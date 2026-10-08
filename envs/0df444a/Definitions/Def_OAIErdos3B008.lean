-- Prove2me | Definitions.Def_OAIErdos3B008
-- name    : OAIErdos3B008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T10:07:08.480934+00:00
-- url     : https://prove2.me/theorems/435f2bb6-343b-4e96-89a2-d2c42a68a221
-- title:
--   OpenAI Erdős-3 split, definitions bundle 9 of 88
-- statement:
--   Definitions bundle 9 of 88 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B007`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 9 available.
--
--   Modules: `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.mem_first_span_of_projection_zero`, `OAI.Erdos3.BohrLattice.MinkowskiSecondBox.span_fin_cons_of_projected_span`, `OAI.Erdos3.CircleFourier.one_le_mul_dist_toAddCircle`, `OAI.Erdos3.CircleFourier.residueCutoff`, `OAI.Erdos3.CircleFourier.residueCutoff_at_grid`, `OAI.Erdos3.CircleFourier.residueCutoff_lipschitz`, `OAI.Erdos3.CircleFourier.residueCutoff_unit_interval`, `OAI.Erdos3.CosetImage`, `OAI.Erdos3.CyclicCrootSisask.crootSisaskSampleSize`, `OAI.Erdos3.CyclicCrootSisask.crootSisaskSampleSize_bound`, `OAI.Erdos3.CyclicCrootSisask.crootSisaskSampleSize_pos`, `OAI.Erdos3.CyclicCrootSisask.samplingMomentCost`, `OAI.Erdos3.CyclicCrootSisask.samplingMomentCost_error`, `OAI.Erdos3.CyclicCrootSisask.samplingMomentCost_nonneg`, `OAI.Erdos3.CyclicMZ.RCLike.marcinkiewicz_zygmund`, `OAI.Erdos3.CyclicMZ.Real.marcinkiewicz_zygmund`, `OAI.Erdos3.CyclicMZ.Real.marcinkiewicz_zygmund'`, `OAI.Erdos3.CyclicMZ.end_step`, `OAI.Erdos3.CyclicMZ.step_eight`, `OAI.Erdos3.CyclicMZ.step_four`, `OAI.Erdos3.CyclicMZ.step_one`, `OAI.Erdos3.CyclicMZ.step_one'`, `OAI.Erdos3.CyclicMZ.step_seven`, `OAI.Erdos3.CyclicMZ.step_six`, `OAI.Erdos3.CyclicMZ.step_three`, `OAI.Erdos3.CyclicMZ.step_two`, `OAI.Erdos3.CyclicMZ.step_two_aux`, `OAI.Erdos3.FixedDensity.AffineForm.eval`, `OAI.Erdos3.FixedDensity.AffineForm.eval_zero`, `OAI.Erdos3.FixedDensity.AffineForm.noConfusion`, `OAI.Erdos3.FreimanModel.variableRoundedGraphCoordinateEquiv`, `OAI.Erdos3.FreimanModel.variableRoundedGraphModuli`, `OAI.Erdos3.FreimanModel.variableRoundedGraphModuli_neZero`, `OAI.Erdos3.MissingAssignment`, `OAI.Erdos3.NilpotentLieFiltration.bch_mem`, `OAI.Erdos3.VectorPolynomial.candidateFrontFactor_massLog_le`, `OAI.Erdos3.VectorPolynomial.candidateFrontFactor_uniform_block_le_power`, `OAI.Erdos3.VectorPolynomial.forecastShortGridEquiv`, `OAI.Erdos3.VectorPolynomial.precenter_native_selection_correlation_budget`, `OAI.Erdos3.VectorPolynomial.precenter_native_selection_mass_budget`, `OAI.Erdos3.VectorPolynomial.precenter_native_selection_model_error_budget`, `OAI.Erdos3.VectorPolynomial.precenter_native_selection_residual_budget`, `OAI.Erdos3.absorb_factored_phases`, `OAI.Erdos3.absorbedSiteTests`, `OAI.Erdos3.absorbedSiteTests_norm`, `OAI.Erdos3.absorbedSiteTests_product`, `OAI.Erdos3.additiveFundamentalDomain_op`, `OAI.Erdos3.affineCoefficientMeasure`, `OAI.Erdos3.affineCoefficientMeasure_probability`, `OAI.Erdos3.affineProbabilityProfile`, `OAI.Erdos3.affineProbabilityProfile_compact`, `OAI.Erdos3.affineProbabilityProfile_contDiff`, `OAI.Erdos3.affineProbabilityProfile_integrable`, `OAI.Erdos3.affineProbabilityProfile_integral`, `OAI.Erdos3.affineProbabilityProfile_le`, `OAI.Erdos3.affineProbabilityProfile_nonneg`, `OAI.Erdos3.affineProbabilityProfile_support`, `OAI.Erdos3.affineProbabilityProfile_zero`, `OAI.Erdos3.affineProbabilityProfile_zero_outside`, `OAI.Erdos3.affineProductProfile`, `OAI.Erdos3.affineProductProfile_contDiff`, `OAI.Erdos3.affineProductProfile_eq`, `OAI.Erdos3.affineProductProfile_nonneg`, `OAI.Erdos3.affineProductProfile_norm_le`, `OAI.Erdos3.affineProductProfile_zero_outside`, `OAI.Erdos3.affineResidueCoordinateEquiv`, `OAI.Erdos3.affineResidueCoordinateEquiv_apply`, `OAI.Erdos3.affineResidueCoordinateEquiv_intCast`, `OAI.Erdos3.ambientReconstructionConstant_le_exp`, `OAI.Erdos3.assignmentSplitEquiv`, `OAI.Erdos3.assignmentSplitMap`, `OAI.Erdos3.assignmentSplitMap_bijective`, `OAI.Erdos3.assignment_product_split`, `OAI.Erdos3.basis_coordinate_matrix_mulVec`, `OAI.Erdos3.basis_image_reconstruct_from_minor`, `OAI.Erdos3.basis_projection_injective_of_minor`, `OAI.Erdos3.blockDegree`, `OAI.Erdos3.blockDegree_add`, `OAI.Erdos3.blockDegree_apply`, `OAI.Erdos3.blockDegree_total`, `OAI.Erdos3.blockDegree_zero`, `OAI.Erdos3.block_quotient_unitriangular`, `OAI.Erdos3.circle_character_triple_cancel`, `OAI.Erdos3.commonKernelRangeEquiv`, `OAI.Erdos3.commonKernelRangeEquiv_apply`, `OAI.Erdos3.commonKernelSubmoduleEquiv`, `OAI.Erdos3.commonKernelSubmoduleEquiv_apply`, `OAI.Erdos3.commonKernelSubmoduleEquiv_symm_apply`, `OAI.Erdos3.comparableBoxPartitions`, `OAI.Erdos3.continuous_integerPeriodicTorusLift`, `OAI.Erdos3.coordinateAdditionInputs`, `OAI.Erdos3.coordinateAdditionInputs_left`, `OAI.Erdos3.coordinateAdditionInputs_right`, `OAI.Erdos3.coordinateAdditionInputs_sum`, `OAI.Erdos3.coordinateAdditionProduct`, `OAI.Erdos3.coordinateConstantInput`, `OAI.Erdos3.coordinatePairInput`, `OAI.Erdos3.coordinatePairInput_left`, `OAI.Erdos3.coordinatePairInput_right`, `OAI.Erdos3.coordinatePairInput_sum`, `OAI.Erdos3.coordinateReindexedFunction`, `OAI.Erdos3.coordinateReindexedSides`, `OAI.Erdos3.coordinateReindexedSides_mem_integerBox`, `OAI.Erdos3.covolume_index_graph_bounds`, `OAI.Erdos3.cyclicInterval_representative_correlation`, `OAI.Erdos3.euclideanHorizontalProjection`, `OAI.Erdos3.euclideanHorizontalProjection_apply`, `OAI.Erdos3.euclidean_closedBall_volume_le`, `OAI.Erdos3.eval_normalizedRealPolynomialChart_substitution`, `OAI.Erdos3.exists_basis_of_surjection`, `OAI.Erdos3.exists_complex_bounded_lipschitz_extension`, `OAI.Erdos3.exists_complex_extension_along_map`, `OAI.Erdos3.exists_complex_extension_from_subset`, `OAI.Erdos3.exists_continuous_image_factor`, `OAI.Erdos3.exists_cyclic_real_character_lift`, `OAI.Erdos3.exists_divisible_character_extension`, `OAI.Erdos3.exists_highest_exceptional_layer`, `OAI.Erdos3.exists_mode_shift_lengths`, `OAI.Erdos3.exists_nested_independent_spanning_sets`, `OAI.Erdos3.exists_normalized_basis_vector`, `OAI.Erdos3.exists_real_lipschitz_extension_interval`, `OAI.Erdos3.exists_rounding_modulus`, `OAI.Erdos3.exists_rounding_modulus_with_recovery`, `OAI.Erdos3.exists_sorted_positive_weights`, `OAI.Erdos3.exists_uniform_parameter_net`, `OAI.Erdos3.exists_unique_cosetImage_reconstruction`, `OAI.Erdos3.exists_unique_observable_reconstruction`, `OAI.Erdos3.exists_unique_quotient_reconstruction`, `OAI.Erdos3.factorial_exp_scalar_integer`, `OAI.Erdos3.factorial_log_scalar_integer`, `OAI.Erdos3.factorsThrough_image_cosets`, `OAI.Erdos3.factorsThrough_target_cosets`, `OAI.Erdos3.finiteCorrelation_image_of_injOn`, `OAI.Erdos3.finiteSumCoordinateInput`, `OAI.Erdos3.finiteSumCoordinateInput_one`, `OAI.Erdos3.finiteTermCoordinateHom`, `OAI.Erdos3.finiteTermCoordinateInput`, `OAI.Erdos3.fourFunctionDifference`, `OAI.Erdos3.four_affine_balanced_invariant`, `OAI.Erdos3.four_refined_affine_identity`, `OAI.Erdos3.generalReconstructionConstant_le_exp`, `OAI.Erdos3.gram_det_basis_change`, `OAI.Erdos3.horizontal_lift_remove`, `OAI.Erdos3.inactivePrincipalCoefficient`, `OAI.Erdos3.inactivePrincipal_large`, `OAI.Erdos3.inactivePrincipal_small`, `OAI.Erdos3.inactiveSideLength`, `OAI.Erdos3.inactiveSideLength_le`, `OAI.Erdos3.inactiveSideLength_pos`, `OAI.Erdos3.inactiveSideLength_power`, `OAI.Erdos3.independent_columns_of_identity_minor`, `OAI.Erdos3.independent_columns_of_nonzero_row_minor`, `OAI.Erdos3.integerBoxCoordinateEquiv`, `OAI.Erdos3.integerBoxCoordinateEquiv_symm_val`, `OAI.Erdos3.integerBoxCoordinateEquiv_val`, `OAI.Erdos3.integerPeriodicTorusLift`, `OAI.Erdos3.integerPeriodicTorusLift_coe`, `OAI.Erdos3.integerPointCoordinateEquiv`, `OAI.Erdos3.integerPointCoordinateEquiv_apply`, `OAI.Erdos3.integerPointCoordinateEquiv_mem_integerBox`, `OAI.Erdos3.integerPointCoordinateEquiv_symm`, `OAI.Erdos3.integerPointCoordinateEquiv_symm_apply`, `OAI.Erdos3.integerResidueLatticeEquiv`, `OAI.Erdos3.integerResidueLatticeEquiv_apply`, `OAI.Erdos3.integerResidueLatticePoint`, `OAI.Erdos3.integerResidueLatticePoint_bijective`, `OAI.Erdos3.integerResidueLatticePoint_cast`, `OAI.Erdos3.integralHyperplaneCorrection`, `OAI.Erdos3.kernelFiberEmbeddingEquiv`, `OAI.Erdos3.kernelGeometryEnvelope`, `OAI.Erdos3.kernelGeometryEnvelope_nonneg`, `OAI.Erdos3.kernelInverseEnvelope`, `OAI.Erdos3.kernelInverseEnvelope_nonneg`, `OAI.Erdos3.kernelOutputEnvelope`, `OAI.Erdos3.kernelOutputEnvelope_nonneg`, `OAI.Erdos3.l1_sampling_via_uniform_surrogate`, `OAI.Erdos3.linear_action_triple`, `OAI.Erdos3.linear_cocycle_triple`, `OAI.Erdos3.linear_derivative_absorb`, `OAI.Erdos3.linear_derivative_remove`, `OAI.Erdos3.linear_lift_remove`, `OAI.Erdos3.lipschitzWith_of_complex_unit_near`, `OAI.Erdos3.lipschitzWith_of_coordinatewise`, `OAI.Erdos3.localizationLengthBudget`, `OAI.Erdos3.localizationLengthBudget_ge_square`, `OAI.Erdos3.localizationMesh`, `OAI.Erdos3.localizationMesh_le_one`, `OAI.Erdos3.localizationMesh_length`, `OAI.Erdos3.localizationMesh_margin`, `OAI.Erdos3.localizationMesh_pos`, `OAI.Erdos3.localizationRadius`, `OAI.Erdos3.localizationRadius_pos`, `OAI.Erdos3.localizationThreshold`, `OAI.Erdos3.localizationThreshold_antitone`, `OAI.Erdos3.localizationThreshold_le_one`, `OAI.Erdos3.localizationThreshold_pos`, `OAI.Erdos3.localizationThreshold_zero`, `OAI.Erdos3.majorRationalLiftInputScale`, `OAI.Erdos3.majorRationalLiftInputScale_bounds`, `OAI.Erdos3.majorRationalLiftInputScale_mass`, `OAI.Erdos3.matrixModuleAction`, `OAI.Erdos3.matrixModuleAction_apply`, `OAI.Erdos3.matrixModuleAction_image_section`, `OAI.Erdos3.matrixModuleAction_mul`, `OAI.Erdos3.mcShaneEnvelope`, `OAI.Erdos3.mcShaneEnvelope_abs_sub_le`, `OAI.Erdos3.mcShaneEnvelope_bddBelow`, `OAI.Erdos3.mcShaneEnvelope_eq`, `OAI.Erdos3.mcShaneEnvelope_le`, `OAI.Erdos3.mcShaneEnvelope_le_add`, `OAI.Erdos3.mcShaneEnvelope_lipschitz`, `OAI.Erdos3.missingAssignment_coordinate`, `OAI.Erdos3.modeShiftLength`, `OAI.Erdos3.modeShiftLength_bounds`, `OAI.Erdos3.multidegree_exists_predecessor`, `OAI.Erdos3.multidegree_exists_predecessor_above`, `OAI.Erdos3.multilinear_coordinate_expansion`, `OAI.Erdos3.multilinear_diagonal_expansion`, `OAI.Erdos3.nativeLocalPivotVertical_inverse_precision_le_exp`, `OAI.Erdos3.normalFunctional`, `OAI.Erdos3.normalFunctional_apply`, `OAI.Erdos3.normalizedRealPolynomialChart`, `OAI.Erdos3.normalizedRealPolynomialChart_eval`, `OAI.Erdos3.normalizedRealPolynomialChart_eval_comp`, `OAI.Erdos3.normalizedRealPolynomialChart_inl`, `OAI.Erdos3.normalizedRealPolynomialChart_inr`, `OAI.Erdos3.optionPiIsometryEquiv`, `OAI.Erdos3.orthogonalBasisChart`, `OAI.Erdos3.orthogonalBasisChart_apply`, `OAI.Erdos3.orthogonalBasisChart_norm_le`, `OAI.Erdos3.orthogonalBasisChart_symm_apply`, `OAI.Erdos3.orthogonalBasisChart_symm_norm_le`, `OAI.Erdos3.orthogonalBasisCoordinates`, `OAI.Erdos3.packTranslationPolynomial`, `OAI.Erdos3.packTranslationPolynomial_C`, `OAI.Erdos3.packTranslationPolynomial_C_X`, `OAI.Erdos3.packTranslationPolynomial_X`, `OAI.Erdos3.packTranslationPolynomial_eval`, `OAI.Erdos3.packTranslationPolynomial_specialize`, `OAI.Erdos3.pathELength_comp_le_mul_of_mfderiv_bound`, `OAI.Erdos3.pathELength_comp_le_of_mfderiv_norm_le`, `OAI.Erdos3.physicalBoxCell`, `OAI.Erdos3.physicalBoxCellEquiv`, `OAI.Erdos3.physicalBoxCell_nonempty`, `OAI.Erdos3.physicalBoxUnitResidueEquiv`, `OAI.Erdos3.piOptionEquivProd_isometry`, `OAI.Erdos3.positiveProjectionAccuracy`, `OAI.Erdos3.preparedModularProductivity_precision`, `OAI.Erdos3.preparedReady_capped_normalized_mass_lower`, `OAI.Erdos3.preparedReady_mass_lower`, `OAI.Erdos3.preparedReady_normalized_mass_lower`, `OAI.Erdos3.primitiveCorrectionRadius`, `OAI.Erdos3.primitiveCorrectionRadius_le_exp`, `OAI.Erdos3.primitiveCorrectionRadius_nonneg`, `OAI.Erdos3.probability_integral_approximation`, `OAI.Erdos3.productCoordinateMix`, `OAI.Erdos3.productCoordinateMix_swap`, `OAI.Erdos3.productCoordinateSwap`, `OAI.Erdos3.profileWidthFactor`, `OAI.Erdos3.profileWidthFactor_pos`, `OAI.Erdos3.projectToCosetImage`, `OAI.Erdos3.projectToCosetImage_surjective`, `OAI.Erdos3.quotient_action_matrix`, `OAI.Erdos3.quotient_basis_representative`, `OAI.Erdos3.quotient_injective_lift_measure`, `OAI.Erdos3.quotient_injective_translates_disjoint`, `OAI.Erdos3.quotient_preimage_image_vadd`, `OAI.Erdos3.rat_nat_div_integer_of_dvd`, `OAI.Erdos3.realDensityMeasure_ae_of_support`, `OAI.Erdos3.realOrderedBasisPrefixProduct`, `OAI.Erdos3.realOrderedBasisPrefixProduct_congr`, `OAI.Erdos3.realOrderedBasisProduct`, `OAI.Erdos3.realOrderedBasisTailProduct`, `OAI.Erdos3.rectangular_det_expansion`, `OAI.Erdos3.recursive_patch_step_rank_bound`, `OAI.Erdos3.relativeReturnedNormalization_denominator_le_exp`, `OAI.Erdos3.relativeReturnedNormalization_denominator_pos`, `OAI.Erdos3.relativeReturnedNormalization_mass_expression_lower`, `OAI.Erdos3.riemannianEDist_le_mul_of_mfderiv_bound`, `OAI.Erdos3.riemannianEDist_le_of_mfderiv_norm_le`, `OAI.Erdos3.rounding_recovery_error_le`, `OAI.Erdos3.scalarThresholdPolynomial`, `OAI.Erdos3.separated_complex_tsum_lipschitz`, `OAI.Erdos3.separated_tsum_lipschitz`, `OAI.Erdos3.spatialStar`, `OAI.Erdos3.spatialStarVertex`, `OAI.Erdos3.spatialStar_unstar`, `OAI.Erdos3.spatialUnstar`, `OAI.Erdos3.spatialUnstar_star`, `OAI.Erdos3.splitRelativePart`, `OAI.Erdos3.splitRelativePart_mul`, `OAI.Erdos3.splitRelativePart_pair_mem`, `OAI.Erdos3.splitRelativePart_projection`, `OAI.Erdos3.splitRelativePart_same_projection`, `OAI.Erdos3.splitSurjectionEquiv`, `OAI.Erdos3.splitSurjectionEquiv_apply`, `OAI.Erdos3.submodule_comap_iSup_of_le_range`, `OAI.Erdos3.sum_split_at_layer`, `OAI.Erdos3.sum_subtype_gt`, `OAI.Erdos3.tangentModelVector`, `OAI.Erdos3.triangularCorrectionSolutions`, `OAI.Erdos3.triangularCorrectionSolutions_last_eq`, `OAI.Erdos3.triangularCorrectionSolutions_last_window`, `OAI.Erdos3.triangularCorrectionSolutions_prefix`, `OAI.Erdos3.triple_phase_cancellation`, `OAI.Erdos3.weightedPolynomialPotential`, `OAI.Erdos3.weightedPolynomialPotential_homogeneous`, `OAI.Erdos3.weightedPolynomialPotential_pderiv`, `OAI.Erdos3.weightedPolynomialPotential_pderiv_formula`, `OAI.Erdos3.weighted_linear_bound_of_unit`, `OAI.Erdos3.zspan_covolume_sq_eq_det_gram`, `OAI.Finset.cast_dens_inter`, `OAI.Finset.cast_dens_sdiff`, `OAI.Finset.dens_product`, `OAI.Finset.dens_sdiff_of_subset`, `OAI.NNRat.cast_sub`, `OAI.Set.conj_indicator_one`, `OAI.Set.conj_indicator_one_apply`, `OAI.Set.indicator_one_apply_eq_zero`, `OAI.Set.indicator_one_apply_ne_zero`, `OAI.Set.indicator_one_apply_nonneg`, `OAI.Set.indicator_one_eq_zero`, `OAI.Set.indicator_one_image`, `OAI.Set.indicator_one_nonneg`, `OAI.Set.indicator_one_pos`, `OAI.Set.support_indicator_one`, `_private.Dynamics.PrecenterNativeSelectionBudget.0.OAI.Erdos3.VectorPolynomial.precenter_exp_add_le_div`, `_private.Estimates.PreparedModularProductivityPrecision.0.OAI.Erdos3.productivity_exp_eight`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B004

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CrootSisaskSampleBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

def samplingMomentCost (m k : ℕ) : ℝ :=
  2 * ((8 * (m : ℝ)) ^ m * (k : ℝ) ^ (m - 1) * k * 2 ^ (2 * m))

theorem samplingMomentCost_nonneg (m k : ℕ) : 0 ≤ samplingMomentCost m k := by
  unfold samplingMomentCost
  positivity

theorem samplingMomentCost_error {m k : ℕ} (hm : 0 < m) {epsilon : ℝ}
    (hsize : 256 * (m : ℝ) ≤ epsilon ^ 2 * k) :
    2 ^ (2 * m) * samplingMomentCost m k ≤ (k : ℝ) ^ (2 * m) * epsilon ^ (2 * m) := by
  have hkpow : (k : ℝ) ^ (m - 1) * k = (k : ℝ) ^ m := pow_sub_one_mul hm.ne' _
  have hcoeff : (2 : ℝ) ^ (2 * m) * 2 ^ (2 * m) * (8 * (m : ℝ)) ^ m =
      (128 * (m : ℝ)) ^ m := by
    rw [pow_mul, ← mul_pow, ← mul_pow]
    congr 1
    ring
  have hidentity : (2 : ℝ) ^ (2 * m) * samplingMomentCost m k =
      2 * (128 * (m : ℝ)) ^ m * (k : ℝ) ^ m := by
    unfold samplingMomentCost
    calc
      _ = 2 * ((2 : ℝ) ^ (2 * m) * 2 ^ (2 * m) * (8 * (m : ℝ)) ^ m) *
          ((k : ℝ) ^ (m - 1) * k) := by ring
      _ = _ := by rw [hcoeff, hkpow]
  have htwo : (2 : ℝ) ≤ 2 ^ m := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show 1 ≤ m by omega)
  have hbase : 2 * (128 * (m : ℝ)) ≤ epsilon ^ 2 * k := by linarith
  have hpower := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * (128 * (m : ℝ))) hbase m
  have hnum : 2 * (128 * (m : ℝ)) ^ m ≤ epsilon ^ (2 * m) * (k : ℝ) ^ m := by
    calc
      _ ≤ 2 ^ m * (128 * (m : ℝ)) ^ m := mul_le_mul_of_nonneg_right htwo (by positivity)
      _ ≤ (epsilon ^ 2 * k) ^ m := by simpa only [mul_pow] using hpower
      _ = _ := by rw [mul_pow, ← pow_mul]
  rw [hidentity]
  calc
    _ ≤ (epsilon ^ (2 * m) * (k : ℝ) ^ m) * (k : ℝ) ^ m :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = _ := by rw [pow_mul]; ring

noncomputable def crootSisaskSampleSize (m : ℕ) (epsilon : ℝ) : ℕ :=
  ⌈256 * (m : ℝ) / epsilon ^ 2⌉₊

theorem crootSisaskSampleSize_pos {m : ℕ} (hm : 0 < m) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < crootSisaskSampleSize m epsilon := by
  apply Nat.ceil_pos.mpr
  positivity

theorem crootSisaskSampleSize_bound (m : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    256 * (m : ℝ) ≤ epsilon ^ 2 * crootSisaskSampleSize m epsilon := by
  have h := Nat.le_ceil (256 * (m : ℝ) / epsilon ^ 2)
  have h' := (div_le_iff₀ (sq_pos_of_pos hepsilon)).mp h
  simpa only [crootSisaskSampleSize, mul_comm] using h'

end Erdos3.CyclicCrootSisask

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeLocalPivotVerticalBudget
namespace OAI

section

namespace Erdos3

theorem nativeLocalPivotVertical_inverse_precision_le_exp
    {pLocal r q : ℝ} (hbudget : pLocal + r + 1 ≤ q) :
    (Real.exp (-pLocal) * Real.exp (-r) / 2)⁻¹ ≤ Real.exp q := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hinv : (Real.exp (-pLocal) * Real.exp (-r) / 2)⁻¹ =
      2 * Real.exp (pLocal + r) := by
    rw [← Real.exp_add, ← neg_add, Real.exp_neg]
    simp [div_eq_mul_inv, mul_comm]
  rw [hinv]
  calc
    2 * Real.exp (pLocal + r) ≤ Real.exp 1 * Real.exp (pLocal + r) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = Real.exp (1 + (pLocal + r)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp q := Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PrecenterNativeSelectionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem precenter_exp_add_le_div (q a : ℝ) (ha : 0 < a)
    (hlog : Real.log a ≤ a) :
    Real.exp (-(q + a)) ≤ Real.exp (-q) / a := by
  calc
    _ ≤ Real.exp (-q - Real.log a) := Real.exp_le_exp.mpr (by linarith only [hlog])
    _ = _ := by rw [Real.exp_sub, Real.exp_log ha]

theorem precenter_native_selection_mass_budget
    {Bin : Type*} [Fintype Bin] [Nonempty Bin] (rank : ℕ)
    {b t d mass : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hrank : (rank : ℝ) ≤ d)
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp b) (hmass : 0 ≤ mass) :
    Real.exp (-(d * (b + t))) * mass ≤
      mass / ((Fintype.card Bin : ℝ) ^ rank * (Real.exp t) ^ rank) := by
  have hcardpos : (0 : ℝ) < Fintype.card Bin := by
    exact_mod_cast Fintype.card_pos
  have hden : 0 < (Fintype.card Bin : ℝ) ^ rank * (Real.exp t) ^ rank := by positivity
  have hbound : (Fintype.card Bin : ℝ) ^ rank * (Real.exp t) ^ rank ≤
      Real.exp (d * (b + t)) := by
    calc
      _ ≤ (Real.exp b) ^ rank * (Real.exp t) ^ rank :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hcardpos.le hcard rank) (by positivity)
      _ = Real.exp ((rank : ℝ) * (b + t)) := by
        rw [← mul_pow, ← Real.exp_add, Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrank (add_nonneg hb ht))
  calc
    _ = mass / Real.exp (d * (b + t)) := by rw [Real.exp_neg]; ring
    _ ≤ _ := div_le_div_of_nonneg_left hmass hden hbound

theorem precenter_native_selection_correlation_budget
    {Bin : Type*} [Fintype Bin] [Nonempty Bin] {rFreq b c : ℝ}
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp b) :
    Real.exp (-(rFreq + b + c + 4)) ≤
      (Real.exp (-rFreq) / (2 * (Fintype.card Bin : ℝ))) / (2 * Real.exp c) := by
  have hcardpos : (0 : ℝ) < Fintype.card Bin := by
    exact_mod_cast Fintype.card_pos
  have hfour : Real.log (4 : ℝ) ≤ 4 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)).trans (by norm_num)
  calc
    _ ≤ Real.exp (-(rFreq + b + c)) / 4 :=
      precenter_exp_add_le_div (rFreq + b + c) 4 (by norm_num) hfour
    _ = (Real.exp (-rFreq) / (2 * Real.exp b)) / (2 * Real.exp c) := by
      rw [show -(rFreq + b + c) = -rFreq - b - c by ring,
        Real.exp_sub, Real.exp_sub]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
        (mul_le_mul_of_nonneg_left hcard (by norm_num))) (by positivity)

theorem precenter_native_selection_residual_budget
    {Bin : Type*} [Fintype Bin] [Nonempty Bin] {pLocal Eres rFreq b : ℝ}
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp b)
    (hres : pLocal + rFreq + b + 4 ≤ Eres) :
    Real.exp (pLocal - Eres) ≤
      (Real.exp (-rFreq) / (2 * (Fintype.card Bin : ℝ))) / 2 := by
  calc
    _ ≤ Real.exp (-(rFreq + b + 0 + 4)) := Real.exp_le_exp.mpr (by linarith only [hres])
    _ ≤ _ := by simpa using (precenter_native_selection_correlation_budget (c := 0) hcard)

theorem precenter_native_selection_model_error_budget (inputLog rFreq : ℝ) :
    Real.exp inputLog * Real.exp (-(inputLog + rFreq + 2)) ≤ Real.exp (-rFreq) / 2 := by
  have htwo : Real.log (2 : ℝ) ≤ 2 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
  calc
    _ = Real.exp (-(rFreq + 2)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := precenter_exp_add_le_div rFreq 2 (by norm_num) htwo

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PrimitiveCorrectionRadiusBudget
namespace OAI

section

namespace Erdos3

def primitiveCorrectionRadius (s u b i : ℕ) (L M : ℝ) : ℝ :=
  (((u + b : ℕ) : ℝ) + 1) ^ s * M * (max 1 ((i : ℝ) * L)) ^ s

theorem primitiveCorrectionRadius_nonneg (s u b i : ℕ) (L : ℝ) {M : ℝ}
    (hM : 0 ≤ M) : 0 ≤ primitiveCorrectionRadius s u b i L M := by
  unfold primitiveCorrectionRadius
  positivity

theorem primitiveCorrectionRadius_le_exp (s u b i : ℕ) {p t L M : ℝ}
    (hp : 0 ≤ p) (ht : 0 ≤ t)
    (hu : (u : ℝ) ≤ p) (hb : (b : ℝ) ≤ p) (hi : (i : ℝ) ≤ p)
    (hM : 0 ≤ M) (hMcap : M ≤ Real.exp t) (hLcap : L ≤ Real.exp t) :
    primitiveCorrectionRadius s u b i L M ≤
      Real.exp ((s : ℝ) * (3 * p + 1) + (s + 1) * t) := by
  have hbase : ((u + b : ℕ) : ℝ) + 1 ≤ Real.exp (2 * p + 1) := by
    rw [Nat.cast_add]
    linarith [Real.add_one_le_exp (2 * p + 1)]
  have hie : (i : ℝ) ≤ Real.exp p :=
    hi.trans (by linarith [Real.add_one_le_exp p])
  have hmax : max 1 ((i : ℝ) * L) ≤ Real.exp (p + t) := by
    apply max_le
    · exact Real.one_le_exp (add_nonneg hp ht)
    · calc
        _ ≤ (i : ℝ) * Real.exp t := mul_le_mul_of_nonneg_left hLcap (Nat.cast_nonneg _)
        _ ≤ Real.exp p * Real.exp t :=
          mul_le_mul_of_nonneg_right hie (Real.exp_nonneg _)
        _ = Real.exp (p + t) := (Real.exp_add _ _).symm
  calc
    primitiveCorrectionRadius s u b i L M ≤
        (Real.exp (2 * p + 1)) ^ s * Real.exp t * (Real.exp (p + t)) ^ s := by
      unfold primitiveCorrectionRadius
      apply mul_le_mul
      · exact mul_le_mul (pow_le_pow_left₀ (by positivity) hbase s) hMcap hM
          (by positivity)
      · exact pow_le_pow_left₀ (by positivity) hmax s
      · positivity
      · positivity
    _ = Real.exp ((s : ℝ) * (3 * p + 1) + (s + 1) * t) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReconstructionConstantBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem ambientReconstructionConstant_le_exp (L K B T ε : ℝ≥0) (r : ℝ) (hr : 1 ≤ r)
    (hL : (L : ℝ) ≤ Real.exp r) (hK : (K : ℝ) ≤ Real.exp r)
    (hB : (B : ℝ) ≤ Real.exp r) (hT : (T : ℝ) ≤ Real.exp r)
    (hε : (ε : ℝ)⁻¹ ≤ Real.exp r) :
    ((2 * max (L * (2 * K)) (2 * B / (min T⁻¹ ε / 2)) : ℝ≥0) : ℝ) ≤ Real.exp (5 * r) := by
  have h2 : (2 : ℝ) ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  let m := min T⁻¹ ε
  have hm : (m : ℝ)⁻¹ ≤ Real.exp r := by
    by_cases h : T⁻¹ ≤ ε
    · simp only [m, min_eq_left h, NNReal.coe_inv, inv_inv]
      exact hT
    · simp only [m, min_eq_right (le_of_not_ge h)]
      exact hε
  have hfirst : (L : ℝ) * (2 * K) ≤ Real.exp (4 * r) := by
    calc
      _ ≤ Real.exp r * (Real.exp r * Real.exp r) := by gcongr
      _ = Real.exp (3 * r) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hsecond : 2 * (B : ℝ) / ((m : ℝ) / 2) ≤ Real.exp (4 * r) := by
    calc
      _ = 2 * 2 * (B : ℝ) * (m : ℝ)⁻¹ := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
      _ ≤ Real.exp r * Real.exp r * Real.exp r * Real.exp r := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  change 2 * max ((L : ℝ) * (2 * K)) (2 * (B : ℝ) / ((m : ℝ) / 2)) ≤ _
  calc
    _ ≤ Real.exp r * Real.exp (4 * r) := mul_le_mul h2 (max_le hfirst hsecond) (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem generalReconstructionConstant_le_exp (L B A N T D Q X Y ε : ℝ≥0) (r : ℝ) (hr : 1 ≤ r)
    (hL : (L : ℝ) ≤ Real.exp r) (hB : (B : ℝ) ≤ Real.exp r)
    (hA : (A : ℝ) ≤ Real.exp r) (hN : (N : ℝ) ≤ Real.exp r)
    (hT : (T : ℝ) ≤ Real.exp r) (hD : (D : ℝ) ≤ Real.exp r)
    (hQ : (Q : ℝ) ≤ Real.exp r) (hX : (X : ℝ) ≤ Real.exp r)
    (hY : (Y : ℝ) ≤ Real.exp r)
    (hε : (ε : ℝ)⁻¹ = (T : ℝ) * Y + D * Q * X * T * Y + 1) :
    ((2 * max (L * (2 * (A * N * T))) (2 * B / (min T⁻¹ ε / 2)) : ℝ≥0) : ℝ) ≤
      Real.exp (40 * r) := by
  have h15 : 1 ≤ Real.exp (5 * r) := Real.one_le_exp (by linarith)
  have hTY : (T : ℝ) * Y ≤ Real.exp (5 * r) := by
    calc
      _ ≤ Real.exp r * Real.exp r := by gcongr
      _ = Real.exp (2 * r) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hprod : (D : ℝ) * Q * X * T * Y ≤ Real.exp (5 * r) := by
    calc
      _ ≤ Real.exp r * Real.exp r * Real.exp r * Real.exp r * Real.exp r := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have heps : (ε : ℝ)⁻¹ ≤ Real.exp (8 * r) := by
    rw [hε]
    calc
      _ ≤ 3 * Real.exp (5 * r) := by linarith
      _ ≤ Real.exp (3 * r) * Real.exp (5 * r) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp (3 * r)]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hK : ((A * N * T : ℝ≥0) : ℝ) ≤ Real.exp (8 * r) := by
    calc
      _ ≤ Real.exp r * Real.exp r * Real.exp r := by simp only [NNReal.coe_mul]; gcongr
      _ = Real.exp (3 * r) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hshift : Real.exp r ≤ Real.exp (8 * r) := Real.exp_le_exp.mpr (by linarith)
  have h := ambientReconstructionConstant_le_exp L (A * N * T) B T ε (8 * r)
    (by linarith) (hL.trans hshift) hK (hB.trans hshift) (hT.trans hshift) heps
  convert h using 1
  congr 1
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RecursivePatchStepBudget
namespace OAI

section

namespace Erdos3

theorem recursive_patch_step_rank_bound {s d₀ d D E detector j : ℕ}
    (hD : D ≤ d) (hE : E ≤ d₀ + s * (d - D))
    (hdetector : detector ≤ j * D) (hj : j ≤ s) :
    detector + E ≤ d₀ + s * d := by
  have hd : detector ≤ s * D := hdetector.trans (Nat.mul_le_mul_right D hj)
  calc
    detector + E ≤ s * D + (d₀ + s * (d - D)) := Nat.add_le_add hd hE
    _ = d₀ + s * ((d - D) + D) := by ring
    _ = d₀ + s * d := by rw [Nat.sub_add_cancel hD]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AbsorbedSiteTests
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators

noncomputable def absorbedSiteTests {A S X : Type*} [Fintype A]
    (χ : A → S → X → ℂ) (test : S → X → ℂ) : S → X → ℂ :=
  fun s x => (∏ a, χ a s x) * test s x

theorem absorbedSiteTests_norm {A S X : Type*} [Fintype A]
    (χ : A → S → X → ℂ) (hχ : ∀ a s x, ‖χ a s x‖ = 1)
    (test : S → X → ℂ) (s : S) (x : X) :
    ‖absorbedSiteTests χ test s x‖ = ‖test s x‖ := by
  simp only [absorbedSiteTests, norm_mul, norm_prod, hχ, Finset.prod_const_one, one_mul]

theorem absorbedSiteTests_product {A S X : Type*} [Fintype A] [Fintype S]
    (χ : A → S → X → ℂ) (test : S → X → ℂ) (value : S → X) :
    (∏ a, ∏ s, χ a s (value s)) * (∏ s, test s (value s)) =
      ∏ s, absorbedSiteTests χ test s (value s) := by
  rw [Finset.prod_comm]
  exact (Finset.prod_mul_distrib).symm

theorem absorb_factored_phases {A S X G : Type*} [Fintype A] [Fintype S]
    (χ : A → S → X → ℂ) (test : S → X → ℂ) (value : G → S → X)
    (high : A → G → ℝ)
    (hfactor : ∀ a g, character (high a g : CircleFourier.Circle) = ∏ s, χ a s (value g s))
    (low : G → ℝ) (g : G) :
    character ((low g + ∑ a, high a g : ℝ) : CircleFourier.Circle) * (∏ s, test s (value g s)) =
      character (low g : CircleFourier.Circle) * (∏ s, absorbedSiteTests χ test s (value g s)) := by
  rw [AddCircle.coe_add, character_add, character_real_sum]
  simp_rw [hfactor]
  rw [mul_assoc, absorbedSiteTests_product]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BSGIndicator
namespace OAI

section

section BSGIndicatorNotation

scoped[Indicator] notation3 "𝟭_[" s ", " R "]" => Set.indicator s fun _ ↦ (1 : R)

open scoped Indicator

scoped[Indicator] notation3 "𝟭_[" s "]" => 𝟭_[s, _]

end BSGIndicatorNotation

section BSGIndicatorAlgebra

open scoped Indicator

variable {F α β M₀ N₀ : Type*}

namespace Set
open scoped _root_.Set
variable [MonoidWithZero M₀] [MonoidWithZero N₀] {s : Set α}

variable (M₀) in
@[simp] lemma indicator_one_image (e : α ≃ β) (s : Set α) (b : β) :
    𝟭_[e '' s, M₀] b = 𝟭_[s] (e.symm b) := by classical simp [_root_.Set.indicator_apply]

variable [Nontrivial M₀] {a : α}

@[simp high] lemma indicator_one_apply_eq_zero : 𝟭_[s, M₀] a = 0 ↔ a ∉ s := by
  classical exact one_ne_zero.ite_eq_right_iff

lemma indicator_one_apply_ne_zero : 𝟭_[s, M₀] a ≠ 0 ↔ a ∈ s := by
  classical exact one_ne_zero.ite_ne_right_iff

@[simp high] lemma indicator_one_eq_zero : 𝟭_[s, M₀] = 0 ↔ s = ∅ := by
  simp [funext_iff, _root_.Set.eq_empty_iff_forall_notMem]

variable (M₀) in
@[simp high] lemma support_indicator_one : 𝟭_[s, M₀].support = s := by
  ext; exact indicator_one_apply_ne_zero

end Set

end BSGIndicatorAlgebra

section BSGIndicatorOrder

open scoped Indicator

namespace Set
open scoped _root_.Set
variable {α M : Type*} [Zero M] [One M]

section Preorder
variable [Preorder M] [ZeroLEOneClass M] {s : Set α}

@[simp] lemma indicator_one_nonneg : 0 ≤ s.indicator (fun _ ↦ (1 : M)) :=
  _root_.Set.indicator_nonneg (by simp)

@[simp] lemma indicator_one_apply_nonneg {a : α} :
    0 ≤ s.indicator (fun _ ↦ (1 : M)) a := indicator_one_nonneg a

end Preorder

section PartialOrder
variable [PartialOrder M] [ZeroLEOneClass M] [NeZero (1 : M)] {s : Set α}

@[simp]
lemma indicator_one_pos [Nontrivial M] : 0 < s.indicator (fun _ ↦ (1 : M)) ↔ s.Nonempty := by
  classical
  simp [_root_.Set.indicator_apply, lt_iff_le_not_ge, Pi.le_def, apply_ite, ite_apply, Set.Nonempty,
    zero_lt_one.not_ge]

end PartialOrder
end Set

end BSGIndicatorOrder

section BSGIndicatorStar

open scoped ComplexConjugate Indicator

namespace Set
open scoped _root_.Set
variable {α R : Type*} [CommSemiring R] [StarRing R]

@[simp] lemma conj_indicator_one_apply (s : Set α) (a : α) : conj (𝟭_[s, R] a) = 𝟭_[s] a := by
  classical simp [_root_.Set.indicator_apply]

@[simp] lemma conj_indicator_one (s : Set α) : conj 𝟭_[s, R] = 𝟭_[s] := by ext; simp

end Set

end BSGIndicatorStar

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BlockQuotientTriangular
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [DecidableEq ι] [DecidableEq κ]

theorem block_quotient_unitriangular (ω : ι → ℕ) (ν : κ → ℕ)
    (D : Matrix κ ι K) (M : Matrix ι ι K) (S : Matrix ι κ K)
    (hD : ∀ k i, ν k ≠ ω i → D k i = 0)
    (hS : ∀ i k, ω i ≠ ν k → S i k = 0)
    (hDS : D * S = 1)
    (hM : ∀ i j, ω i ≤ ω j → M i j = (1 : Matrix ι ι K) i j)
    (a b : κ) (hab : ν a ≤ ν b) :
    (D * M * S) a b = (1 : Matrix κ κ K) a b := by
  have he : (D * M * S) a b = (D * (1 : Matrix ι ι K) * S) a b := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : ω j = ν b
    · apply congrArg (fun x => x * S j b)
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : ν a = ω i
      · rw [hM i j (by omega)]
      · rw [hD a i hi, zero_mul, zero_mul]
    · rw [hS j b hj, mul_zero, mul_zero]
  rw [he, Matrix.mul_one, hDS]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexUnitLocalLipschitz
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem separated_complex_tsum_lipschitz {ι X : Type*} [PseudoMetricSpace X]
    (f : ι → X → ℂ) {K : ℝ≥0} (hf : ∀ i, LipschitzWith K (f i))
    (hsep : ∀ x i j, f i x ≠ 0 → f j x ≠ 0 → i = j) :
    LipschitzWith (2 * K) (fun x => ∑' i, f i x) := by
  have hsingle (x : X) (i : ι) (hi : f i x ≠ 0) : (∑' j, f j x) = f i x := by
    apply tsum_eq_single i
    intro j hji
    by_contra hj
    exact hji (hsep x j i hj hi)
  have hzero (x : X) (hx : ¬∃ i, f i x ≠ 0) : (∑' i, f i x) = 0 := by
    have hz : ∀ i, f i x = 0 := fun i => not_ne_iff.mp (fun hi => hx ⟨i, hi⟩)
    simp only [hz, tsum_zero]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hK : (K : ℝ) * dist x y ≤ (2 * K : ℝ≥0) * dist x y := by
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    nlinarith [K.coe_nonneg, dist_nonneg (x := x) (y := y)]
  by_cases hx : ∃ i, f i x ≠ 0
  · obtain ⟨i, hi⟩ := hx
    rw [hsingle x i hi]
    by_cases hy : ∃ j, f j y ≠ 0
    · obtain ⟨j, hj⟩ := hy
      rw [hsingle y j hj]
      by_cases hij : i = j
      · subst j
        exact ((hf i).dist_le_mul x y).trans hK
      · have hiy : f i y = 0 := by
          by_contra h
          exact hij (hsep y i j h hj)
        have hjx : f j x = 0 := by
          by_contra h
          exact hij (hsep x i j hi h)
        have h1 := (hf i).dist_le_mul x y
        have h2 := (hf j).dist_le_mul x y
        rw [hiy] at h1
        rw [hjx] at h2
        have ht := dist_triangle (f i x) 0 (f j y)
        simp only [NNReal.coe_mul, NNReal.coe_ofNat]
        linarith
    · rw [hzero y hy]
      have hiy : f i y = 0 := not_ne_iff.mp (fun h => hy ⟨i, h⟩)
      simpa only [hiy] using ((hf i).dist_le_mul x y).trans hK
  · rw [hzero x hx]
    by_cases hy : ∃ j, f j y ≠ 0
    · obtain ⟨j, hj⟩ := hy
      rw [hsingle y j hj]
      have hjx : f j x = 0 := not_ne_iff.mp (fun h => hx ⟨j, h⟩)
      simpa only [hjx] using ((hf j).dist_le_mul x y).trans hK
    · rw [hzero y hy, dist_self]
      positivity

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem lipschitzWith_of_complex_unit_near {X : Type*} [PseudoMetricSpace X]
    (f : X → ℂ) (C L : ℝ≥0) (hbound : ∀ x, ‖f x‖ ≤ 1)
    (hnear : ∀ x y, (C : ℝ) * dist x y < 1 →
      ‖f x - f y‖ ≤ (L : ℝ) * dist x y) :
    LipschitzWith (max (2 * C) L) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  by_cases hclose : (C : ℝ) * dist x y < 1
  · exact (hnear x y hclose).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_right (2 * C) L) dist_nonneg)
  · have hxy : ‖f x - f y‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [hbound x, hbound y])
    have hfar : 2 ≤ ((2 * C : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_mul, NNReal.coe_ofNat]
      linarith [le_of_not_gt hclose]
    exact hxy.trans (hfar.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_left (2 * C) L) dist_nonneg))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ContinuousImageFactor
namespace OAI

section

namespace Erdos3

open Topology

theorem exists_continuous_image_factor {X Y Z : Type*}
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace Z] (E : X → Y) (hE : Continuous E) (f : X → Z) (hf : Continuous f)
    (hfactor : ∀ x y, E x = E y → f x = f y) :
    ∃ g : Set.range E → Z, Continuous g ∧ ∀ x, g (Set.rangeFactorization E x) = f x := by
  let e : C(X, Set.range E) := ⟨Set.rangeFactorization E, hE.rangeFactorization⟩
  have hq : IsQuotientMap e :=
    IsQuotientMap.of_surjective_continuous Set.rangeFactorization_surjective hE.rangeFactorization
  have hfac : Function.FactorsThrough (⟨f, hf⟩ : C(X, Z)) e :=
    fun x y hxy => hfactor x y (congrArg Subtype.val hxy)
  let g := hq.lift ⟨f, hf⟩ hfac
  refine ⟨g, g.continuous, ?_⟩
  intro x
  exact DFunLike.congr_fun (hq.lift_comp ⟨f, hf⟩ hfac) x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CovolumeFactorBounds
namespace OAI

section

namespace Erdos3

theorem covolume_index_graph_bounds {a I E C d : ℝ}
    (hd : 0 < d) (ha : 1 / d ≤ a) (hI : 1 ≤ I) (hE : 1 ≤ E)
    (hprod : a * I * E ≤ C) : a ≤ C ∧ I ≤ C * d ∧ E ≤ C * d := by
  have ha0 : 0 ≤ a := (one_div_pos.mpr hd).le.trans ha
  have hI0 : 0 ≤ I := zero_le_one.trans hI
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have haI : a * I ≤ C :=
    (le_mul_of_one_le_right (mul_nonneg ha0 hI0) hE).trans hprod
  have haE : a * E ≤ C := by
    calc
      a * E ≤ (a * I) * E := mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right ha0 hI) hE0
      _ ≤ C := hprod
  refine ⟨(le_mul_of_one_le_right ha0 hI).trans haI, ?_, ?_⟩
  · apply (div_le_iff₀ hd).mp
    calc
      I / d = (1 / d) * I := by ring
      _ ≤ a * I := mul_le_mul_of_nonneg_right ha hI0
      _ ≤ C := haI
  · apply (div_le_iff₀ hd).mp
    calc
      E / d = (1 / d) * E := by ring
      _ ≤ a * E := mul_le_mul_of_nonneg_right ha hE0
      _ ≤ C := haE

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EuclideanBallVolumeBound
namespace OAI

section

namespace Erdos3

open MeasureTheory Module

theorem euclidean_closedBall_volume_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (B : ℝ) (hB : 0 ≤ B) :
    volume.real (Metric.closedBall (0 : E) B) ≤ (2 * B) ^ finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  let e : E ≃ᵐ (Fin (finrank ℝ E) → ℝ) :=
    b.repr.toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 _).symm
  have he : MeasurePreserving e :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).comp b.measurePreserving_repr
  let C : Set (Fin (finrank ℝ E) → ℝ) := Set.Icc (fun _ => -B) (fun _ => B)
  have hsub : Metric.closedBall (0 : E) B ⊆ e ⁻¹' C := by
    intro x hx
    have hxnorm : ‖x‖ ≤ B := mem_closedBall_zero_iff.mp hx
    have hi : ∀ i, |e x i| ≤ B := by
      intro i
      change |b.repr x i| ≤ B
      rw [← Real.norm_eq_abs]
      exact (PiLp.norm_apply_le (b.repr x) i).trans ((b.repr.norm_map x).le.trans hxnorm)
    exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩
  have hmeas : MeasurableSet C := measurableSet_Icc
  have hfinite : volume C ≠ ⊤ := by
    simp only [C, Real.volume_Icc_pi]
    exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)
  have hvolume : volume.real (e ⁻¹' C) = (2 * B) ^ finrank ℝ E := by
    rw [measureReal_def, he.measure_preimage hmeas.nullMeasurableSet]
    have horder : (fun _ : Fin (finrank ℝ E) => -B) ≤ (fun _ => B) := fun _ => by linarith
    simp only [C, Real.volume_Icc_pi_toReal horder, sub_neg_eq_add, ← two_mul,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← hvolume]
  exact measureReal_mono hsub (by rw [he.measure_preimage hmeas.nullMeasurableSet]; exact hfinite)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteAssignmentPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

abbrev MissingAssignment (s : ℕ) := {v : Fin s → Fin s // ¬Function.Surjective v}

def assignmentSplitMap (s : ℕ) : Equiv.Perm (Fin s) ⊕ MissingAssignment s → (Fin s → Fin s)
  | Sum.inl e => e
  | Sum.inr v => v.val

theorem assignmentSplitMap_bijective (s : ℕ) : Function.Bijective (assignmentSplitMap s) := by
  classical
  constructor
  · intro a b h
    rcases a with a | a <;> rcases b with b | b
    · apply congrArg Sum.inl
      exact Equiv.ext (congrFun h)
    · exfalso
      apply b.property
      change (a : Fin s → Fin s) = b.val at h
      exact h ▸ a.surjective
    · exfalso
      apply a.property
      change a.val = (b : Fin s → Fin s) at h
      exact h.symm ▸ b.surjective
    · apply congrArg Sum.inr
      exact Subtype.ext h
  · intro v
    by_cases hv : Function.Surjective v
    · exact ⟨Sum.inl (Equiv.ofBijective v (Finite.surjective_iff_bijective.mp hv)), rfl⟩
    · exact ⟨Sum.inr ⟨v, hv⟩, rfl⟩

noncomputable def assignmentSplitEquiv (s : ℕ) :
    Equiv.Perm (Fin s) ⊕ MissingAssignment s ≃ (Fin s → Fin s) :=
  Equiv.ofBijective (assignmentSplitMap s) (assignmentSplitMap_bijective s)

theorem missingAssignment_coordinate {s : ℕ} (v : MissingAssignment s) :
    ∃ j : Fin s, ∀ i : Fin s, v.val i ≠ j := by
  classical
  have h := v.property
  simpa only [Function.Surjective, not_forall, not_exists] using h

theorem assignment_product_split {s : ℕ} {I M : Type*} [CommMonoid M]
    (F : (Fin s → Fin s) → I → M)
    (a : Equiv.Perm (Fin s) ⊕ MissingAssignment s → I) :
    (∏ v : Fin s → Fin s, F v (a ((assignmentSplitEquiv s).symm v))) =
      (∏ e : Equiv.Perm (Fin s), F e (a (Sum.inl e))) *
        ∏ v : MissingAssignment s, F v.val (a (Sum.inr v)) := by
  classical
  calc
    _ = ∏ r : Equiv.Perm (Fin s) ⊕ MissingAssignment s,
        F (assignmentSplitEquiv s r) (a r) := by
      have h := (assignmentSplitEquiv s).prod_comp
        (fun v => F v (a ((assignmentSplitEquiv s).symm v)))
      simpa only [Equiv.symm_apply_apply] using h.symm
    _ = _ := by rw [Fintype.prod_sum_type]; rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GramCovolume
namespace OAI

section

namespace Erdos3

open Module RealInnerProductSpace

theorem zspan_covolume_sq_eq_det_gram {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {r : ℕ} (b : Basis (Fin r) ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) ^ 2 = (Matrix.gram ℝ b).det := by
  let b₀ : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  have hrank : Module.finrank ℝ E = r := by simpa using Module.finrank_eq_card_basis b
  let e : Fin (Module.finrank ℝ E) ≃ Fin r := Fin.castOrderIso hrank
  let o : OrthonormalBasis (Fin r) ℝ E := b₀.reindex e
  have hoVolume : MeasureTheory.volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [MeasureTheory.measureReal_def]
    have hfd : MeasureTheory.volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
      rw [MeasureTheory.measure_congr
        (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis MeasureTheory.volume)]
      exact o.volume_parallelepiped
    rw [hfd]
    simp
  have hcov : ZLattice.covolume (Submodule.span ℤ (Set.range b)) = |o.toBasis.det b| := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain
      (Submodule.span ℤ (Set.range b)) MeasureTheory.volume
      (ZSpan.isAddFundamentalDomain b MeasureTheory.volume),
      ZSpan.measureReal_fundamentalDomain b MeasureTheory.volume o.toBasis, hoVolume, mul_one]
  rw [hcov, sq_abs, o.toBasis.det_apply]
  rw [Matrix.gram_eq_conjTranspose_mul o b, Matrix.det_mul, Matrix.det_conjTranspose]
  have hm : o.toBasis.toMatrix b = Matrix.of fun i j => o.repr (b j) i := by
    ext i j
    rfl
  rw [hm]
  simp [pow_two]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageCosetReconstruction
namespace OAI

section

namespace Erdos3

variable {H G A : Type*} [Group H] [Group G]

theorem factorsThrough_target_cosets (φ : H →* G) (Γ : Subgroup H) (Λ : Subgroup G)
    (hcover : Λ ≤ Γ.map φ) (f : H → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x) :
    Function.FactorsThrough f (fun x => (QuotientGroup.mk (φ x) : G ⧸ Λ)) := by
  intro x y hxy
  have hmem : (φ x)⁻¹ * φ y ∈ Λ := QuotientGroup.eq.mp hxy
  obtain ⟨γ, hγ, hφγ⟩ := hcover hmem
  let k := y * γ⁻¹ * x⁻¹
  have hk : k ∈ φ.ker := by
    change φ k = 1
    simp only [k, map_mul, map_inv, hφγ, mul_inv_rev, inv_inv]
    group
  have hdecomp : k * (x * γ) = y := by
    dsimp [k]
    group
  calc
    f x = f (x * γ) := (hΓ γ hγ x).symm
    _ = f (k * (x * γ)) := (hker k hk (x * γ)).symm
    _ = f y := congrArg f hdecomp

theorem exists_unique_quotient_reconstruction (φ : H →* G) (hφ : Function.Surjective φ)
    (Γ : Subgroup H) (Λ : Subgroup G) (hcover : Λ ≤ Γ.map φ) (f : H → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x) :
    ∃! F : G ⧸ Λ → A, ∀ x, F (QuotientGroup.mk (φ x)) = f x := by
  let π : H → G ⧸ Λ := fun x => QuotientGroup.mk (φ x)
  have hπ : Function.Surjective π := QuotientGroup.mk_surjective.comp hφ
  have hf := factorsThrough_target_cosets φ Γ Λ hcover f hker hΓ
  let F : G ⧸ Λ → A := fun y => f (Function.surjInv hπ y)
  have hF (x : H) : F (π x) = f x := hf (Function.surjInv_eq hπ (π x))
  refine ⟨F, hF, ?_⟩
  intro F' hF'
  funext y
  obtain ⟨x, rfl⟩ := hπ y
  exact (hF' x).trans (hF x).symm

theorem exists_unique_observable_reconstruction (φ : H →* G) (hφ : Function.Surjective φ)
    (Γ : Subgroup H) (Λ : Subgroup G) (hcover : Λ ≤ Γ.map φ) (f : H ⧸ Γ → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (QuotientGroup.mk (k * x)) = f (QuotientGroup.mk x)) :
    ∃! F : G ⧸ Λ → A, ∀ x, F (QuotientGroup.mk (φ x)) = f (QuotientGroup.mk x) := by
  apply exists_unique_quotient_reconstruction φ hφ Γ Λ hcover (fun x => f (QuotientGroup.mk x)) hker
  intro γ hγ x
  apply congrArg f
  apply QuotientGroup.eq.mpr
  simpa only [mul_inv_rev, inv_mul_cancel_left, inv_mul_cancel_right] using Γ.inv_mem hγ

end Erdos3

end

section

namespace Erdos3

variable {H G A : Type*} [Group H] [Group G]

def CosetImage (φ : H →* G) (Λ : Subgroup G) :=
  Set.range (fun x : H => (QuotientGroup.mk (φ x) : G ⧸ Λ))

def projectToCosetImage (φ : H →* G) (Λ : Subgroup G) (x : H) : CosetImage φ Λ :=
  ⟨QuotientGroup.mk (φ x), ⟨x, rfl⟩⟩

theorem projectToCosetImage_surjective (φ : H →* G) (Λ : Subgroup G) :
    Function.Surjective (projectToCosetImage φ Λ) := by
  rintro ⟨y, x, rfl⟩
  exact ⟨x, rfl⟩

theorem factorsThrough_image_cosets (φ : H →* G) (Γ : Subgroup H) (Λ : Subgroup G)
    (hcover : Λ ⊓ φ.range ≤ Γ.map φ) (f : H → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x) :
    Function.FactorsThrough f (projectToCosetImage φ Λ) := by
  intro x y hxy
  have hmem : (φ x)⁻¹ * φ y ∈ Λ := QuotientGroup.eq.mp (congrArg Subtype.val hxy)
  have hrange : (φ x)⁻¹ * φ y ∈ φ.range := ⟨x⁻¹ * y, by simp only [map_mul, map_inv]⟩
  obtain ⟨γ, hγ, hφγ⟩ := hcover ⟨hmem, hrange⟩
  let k := y * γ⁻¹ * x⁻¹
  have hk : k ∈ φ.ker := by
    change φ k = 1
    simp only [k, map_mul, map_inv, hφγ, mul_inv_rev, inv_inv]
    group
  have hdecomp : k * (x * γ) = y := by dsimp [k]; group
  calc
    f x = f (x * γ) := (hΓ γ hγ x).symm
    _ = f (k * (x * γ)) := (hker k hk (x * γ)).symm
    _ = f y := congrArg f hdecomp

theorem exists_unique_cosetImage_reconstruction (φ : H →* G) (Γ : Subgroup H) (Λ : Subgroup G)
    (hcover : Λ ⊓ φ.range ≤ Γ.map φ) (f : H → A)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x) :
    ∃! F : CosetImage φ Λ → A, ∀ x, F (projectToCosetImage φ Λ x) = f x := by
  let π := projectToCosetImage φ Λ
  have hπ := projectToCosetImage_surjective φ Λ
  have hf := factorsThrough_image_cosets φ Γ Λ hcover f hker hΓ
  let F : CosetImage φ Λ → A := fun y => f (Function.surjInv hπ y)
  have hF (x : H) : F (π x) = f x := hf (Function.surjInv_eq hπ (π x))
  refine ⟨F, hF, ?_⟩
  intro F' hF'
  funext y
  obtain ⟨x, rfl⟩ := hπ y
  exact (hF' x).trans (hF x).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveAxisScale
namespace OAI

section

namespace Erdos3

noncomputable def inactiveSideLength (h K q : ℕ) : ℕ :=
  if 2 * q ≤ K then Nat.nthRoot h (K / q) else 1

def inactivePrincipalCoefficient (K q : ℕ) : ℤ := if 2 * q ≤ K then 1 else 0

theorem inactiveSideLength_pos {h K q : ℕ} (hh : 0 < h) (hq : 0 < q) :
    0 < inactiveSideLength h K q := by
  by_cases hlarge : 2 * q ≤ K
  · have hdiv : 2 ≤ K / q := (Nat.le_div_iff_mul_le hq).mpr hlarge
    have hroot : 1 ≤ Nat.nthRoot h (K / q) :=
      (Nat.le_nthRoot_iff hh.ne').mpr (by simpa only [one_pow] using (by omega : 1 ≤ K / q))
    simpa [inactiveSideLength, hlarge, Nat.succ_le_iff] using hroot
  · simp [inactiveSideLength, hlarge]

theorem inactiveSideLength_power {h K q : ℕ} (hh : 0 < h) (hlarge : 2 * q ≤ K) :
    inactiveSideLength h K q ^ h ≤ K / q := by
  simpa [inactiveSideLength, hlarge] using (Nat.pow_nthRoot_le (.inl hh.ne') : Nat.nthRoot h (K / q) ^ h ≤ K / q)

theorem inactiveSideLength_le {h K q L : ℕ} (hh : 0 < h) (hL : 0 < L)
    (hK : K ≤ L ^ h) : inactiveSideLength h K q ≤ L := by
  by_cases hlarge : 2 * q ≤ K
  · apply (Nat.pow_left_strictMono hh.ne').le_iff_le.mp
    exact (inactiveSideLength_power hh hlarge).trans ((Nat.div_le_self K q).trans hK)
  · simpa [inactiveSideLength, hlarge] using (show 1 ≤ L by omega)

theorem inactivePrincipal_small {K q : ℕ} (hsmall : K < 2 * q) :
    inactivePrincipalCoefficient K q = 0 := by
  simp [inactivePrincipalCoefficient, not_le.mpr hsmall]

theorem inactivePrincipal_large {K q : ℕ} (hlarge : 2 * q ≤ K) :
    inactivePrincipalCoefficient K q = 1 := by
  simp [inactivePrincipalCoefficient, hlarge]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentColumnsMinor
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem independent_columns_of_nonzero_row_minor {K ι : Type*} [Field K] {k : ℕ}
    (Q : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : (Q.submatrix p id).det ≠ 0) :
    LinearIndependent K Q.col := by
  apply Matrix.mulVec_injective_iff.mp
  intro x y hxy
  apply Matrix.mulVec_injective_of_isUnit
    ((Q.submatrix p id).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hp))
  funext i
  exact congrFun hxy (p i)

theorem independent_columns_of_identity_minor {K ι : Type*} [Field K] {k : ℕ}
    (Q : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : Q.submatrix p id = 1) :
    LinearIndependent K Q.col := by
  apply independent_columns_of_nonzero_row_minor Q p
  rw [hp, Matrix.det_one]
  exact one_ne_zero

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IntegralHyperplaneCorrection
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def normalFunctional (ξ : E) : E →ₗ[ℝ] ℝ := (innerSL ℝ ξ).toLinearMap

@[simp]
theorem normalFunctional_apply (ξ x : E) : normalFunctional ξ x = inner ℝ ξ x := rfl

noncomputable def integralHyperplaneCorrection (ξ x : E) : E :=
  x - ((inner ℝ ξ x - (round (inner ℝ ξ x) : ℝ)) / ‖ξ‖ ^ 2) • ξ

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearDerivativeRemoval
namespace OAI

section

namespace Erdos3

variable {R E K : Type*} [Field R] [AddCommGroup E] [Module R E]
  [AddCommGroup K] [Module R K]

theorem linear_action_triple {G : Type*} [Group G] (ρ : G →* (E ≃ₗ[R] E))
    (a b c : G) (x : E) : ρ (a * b * c) x = ρ a (ρ b (ρ c x)) := by
  rw [map_mul, map_mul]
  rfl

theorem linear_cocycle_triple {G : Type*} [Group G] (ρ : G →* (E ≃ₗ[R] E))
    (Y : G → E) (hY : ∀ a b, Y (a * b) = Y a + ρ a (Y b)) (a b c : G) :
    Y (a * b * c) = Y a + ρ a (Y b) + ρ a (ρ b (Y c)) := by
  rw [hY, hY, map_mul]
  rfl

theorem linear_derivative_remove (a b f g : E ≃ₗ[R] E)
    (hcomp : ∀ x, f x = a (g (b x)))
    (y ya yn yb s r z : E)
    (hprod : y = ya + a yn + a (g yb)) (hsystem : y = s + f r + z) :
    yn = a.symm (s - ya) + g (b r - yb) + a.symm z := by
  apply a.injective
  simp only [map_add, map_sub, LinearEquiv.apply_symm_apply]
  calc
    a yn = y - ya - a (g yb) := by rw [hprod]; abel
    _ = _ := by rw [hsystem, hcomp]; abel

theorem linear_lift_remove (a b f g : E ≃ₗ[R] E)
    (hcomp : ∀ x, f x = a (g (b x))) (S T : K →ₗ[R] E)
    (hST : S = f.toLinearMap.comp T) :
    a.symm.toLinearMap.comp S = g.toLinearMap.comp (b.toLinearMap.comp T) := by
  apply LinearMap.ext
  intro x
  change a.symm (S x) = g (b (T x))
  rw [hST]
  change a.symm (f (T x)) = _
  rw [hcomp, LinearEquiv.symm_apply_apply]

theorem linear_derivative_absorb (f : E →ₗ[R] E) (S T : K →ₗ[R] E)
    (hST : S = f.comp T) (y s r : E) (k ks kr : K)
    (hsystem : y = s + f r + S k) :
    y = (s - S ks) + f (r - T kr) + S (k + ks + kr) := by
  rw [hsystem]
  simp only [map_add, map_sub]
  have hkr : S kr = f (T kr) := DFunLike.congr_fun hST kr
  rw [hkr]
  abel

theorem horizontal_lift_remove {H : Type*} [AddCommGroup H] [Module R H]
    (P : E →ₗ[R] H) (a b : E ≃ₗ[R] E)
    (ha : ∀ x, P (a x) = P x) (hb : ∀ x, P (b x) = P x)
    (S T : K →ₗ[R] E) (ι : K →ₗ[R] H)
    (hS : P.comp S = ι) (hT : P.comp T = ι) :
    P.comp (a.symm.toLinearMap.comp S) = ι ∧
      P.comp (b.toLinearMap.comp T) = ι := by
  constructor
  · apply LinearMap.ext
    intro x
    change P (a.symm (S x)) = ι x
    have h := ha (a.symm (S x))
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm.trans (DFunLike.congr_fun hS x)
  · apply LinearMap.ext
    intro x
    change P (b (T x)) = ι x
    rw [hb]
    exact DFunLike.congr_fun hT x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LipschitzExtensionAlongMap
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

theorem exists_real_lipschitz_extension_interval (f : X → ℝ) (S : Set X) (L : ℝ≥0)
    (hf : LipschitzOnWith L f S) (a b : ℝ) (hab : a ≤ b)
    (hbound : ∀ x ∈ S, a ≤ f x ∧ f x ≤ b) :
    ∃ g : X → ℝ, LipschitzWith L g ∧ Set.EqOn f g S ∧ ∀ x, a ≤ g x ∧ g x ≤ b := by
  obtain ⟨g, hg, heq⟩ := hf.extend_real
  refine ⟨fun x => max a (min b (g x)), (hg.const_min b).const_max a, ?_, ?_⟩
  · intro x hx
    change f x = max a (min b (g x))
    rw [← heq hx, min_eq_right (hbound x hx).2, max_eq_right (hbound x hx).1]
  · intro x
    exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem exists_complex_bounded_lipschitz_extension (f : X → ℂ) (S : Set X) (L B : ℝ≥0)
    (hf : LipschitzOnWith L f S) (hbound : ∀ x ∈ S, ‖f x‖ ≤ B) :
    ∃ g : X → ℂ, LipschitzWith (2 * L) g ∧ Set.EqOn f g S ∧ ∀ x, ‖g x‖ ≤ 2 * B := by
  have hre : LipschitzOnWith L (fun x => (f x).re) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change |(f x - f y).re| ≤ L * dist x y
    exact (Complex.abs_re_le_norm _).trans (by simpa only [dist_eq_norm] using hf.dist_le_mul x hx y hy)
  have him : LipschitzOnWith L (fun x => (f x).im) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change |(f x - f y).im| ≤ L * dist x y
    exact (Complex.abs_im_le_norm _).trans (by simpa only [dist_eq_norm] using hf.dist_le_mul x hx y hy)
  obtain ⟨u, hu, heu, hub⟩ := exists_real_lipschitz_extension_interval (fun x => (f x).re) S L hre
    (-B) B (neg_le_self B.coe_nonneg) (fun x hx => abs_le.mp ((Complex.abs_re_le_norm _).trans (hbound x hx)))
  obtain ⟨v, hv, hev, hvb⟩ := exists_real_lipschitz_extension_interval (fun x => (f x).im) S L him
    (-B) B (neg_le_self B.coe_nonneg) (fun x hx => abs_le.mp ((Complex.abs_im_le_norm _).trans (hbound x hx)))
  let g : X → ℂ := fun x => ⟨u x, v x⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hu' := hu.dist_le_mul x y
    have hv' := hv.dist_le_mul x y
    rw [Real.dist_eq] at hu' hv'
    calc
      dist (g x) (g y) = ‖g x - g y‖ := dist_eq_norm _ _
      _ ≤ |(g x - g y).re| + |(g x - g y).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ (L : ℝ) * dist x y + L * dist x y := add_le_add hu' hv'
      _ = ((2 * L : ℝ≥0) : ℝ) * dist x y := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring
  · intro x hx
    exact Complex.ext (heu hx) (hev hx)
  · intro x
    exact (Complex.norm_le_abs_re_add_abs_im (g x)).trans
      (by have h1 := abs_le.mpr (hub x); have h2 := abs_le.mpr (hvb x); change |u x| + |v x| ≤ _; linarith)

theorem exists_complex_extension_from_subset (S : Set X) (f : S → ℂ) (L B : ℝ≥0)
    (hf : LipschitzWith L f) (hbound : ∀ x, ‖f x‖ ≤ B) :
    ∃ g : X → ℂ, LipschitzWith (2 * L) g ∧ (∀ x : S, g x = f x) ∧ ∀ x, ‖g x‖ ≤ 2 * B := by
  classical
  let F : X → ℂ := fun x => if hx : x ∈ S then f ⟨x, hx⟩ else 0
  have hF (x : S) : F x = f x := by simp only [F, dif_pos x.property]
  have hLip : LipschitzOnWith L F S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [F, dif_pos hx, dif_pos hy, Subtype.dist_eq] using hf.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨g, hg, heq, hb⟩ := exists_complex_bounded_lipschitz_extension F S L B hLip
    (fun x hx => (congrArg norm (hF ⟨x, hx⟩)).le.trans (hbound ⟨x, hx⟩))
  exact ⟨g, hg, fun x => (heq x.property).symm.trans (hF x), hb⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_complex_extension_along_map {X Y : Type*} [PseudoMetricSpace Y]
    (f : X → Y) (u : X → ℂ) (K B : ℝ≥0)
    (hdist : ∀ x y, dist (u x) (u y) ≤ K * dist (f x) (f y))
    (hbound : ∀ x, ‖u x‖ ≤ B) :
    ∃ g : Y → ℂ, LipschitzWith (2 * K) g ∧ (∀ x, g (f x) = u x) ∧
      ∀ y, ‖g y‖ ≤ 2 * B := by
  classical
  let S := Set.range f
  let pre (y : S) : X := Classical.choose y.property
  have hpre (y : S) : f (pre y) = y.val := Classical.choose_spec y.property
  let v (y : S) : ℂ := u (pre y)
  have hv : LipschitzWith K v := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [v, hpre, Subtype.dist_eq] using hdist (pre x) (pre y)
  have hvx (x : X) : v ⟨f x, ⟨x, rfl⟩⟩ = u x := by
    apply dist_le_zero.mp
    have h := hdist (pre ⟨f x, ⟨x, rfl⟩⟩) x
    simpa only [hpre, dist_self, mul_zero] using h
  obtain ⟨g, hg, hge, hgb⟩ := exists_complex_extension_from_subset S v K B hv (fun y => hbound (pre y))
  exact ⟨g, hg, fun x => (hge ⟨f x, ⟨x, rfl⟩⟩).trans (hvx x), hgb⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MajorRationalLiftInputScale
namespace OAI

section

namespace Erdos3

def majorRationalLiftInputScale (d : ℕ) (p : ℝ) : ℝ :=
  ((d + 2 : ℕ) : ℝ) * (p + 1) + 8

theorem majorRationalLiftInputScale_bounds (d : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    0 ≤ majorRationalLiftInputScale d p ∧
      p ≤ majorRationalLiftInputScale d p ∧
      2 * p + 8 ≤ majorRationalLiftInputScale d p := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdp : 0 ≤ (d : ℝ) * p := mul_nonneg hd hp
  dsimp [majorRationalLiftInputScale]
  push_cast
  constructor
  · positivity
  constructor <;> nlinarith

theorem majorRationalLiftInputScale_mass (d : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (n m : ℕ) (hnm : ((n + m : ℕ) : ℝ) ≤ p) :
    ((n + m + 1 : ℕ) : ℝ) ^ d ≤ Real.exp (majorRationalLiftInputScale d p) := by
  have hbase : ((n + m + 1 : ℕ) : ℝ) ≤ p + 1 := by
    push_cast at hnm ⊢
    linarith
  have hexp : p + 1 ≤ Real.exp (p + 1) := by
    linarith [Real.add_one_le_exp (p + 1)]
  have hscale : (d : ℝ) * (p + 1) ≤ majorRationalLiftInputScale d p := by
    dsimp [majorRationalLiftInputScale]
    push_cast
    nlinarith
  calc
    _ ≤ Real.exp (p + 1) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hbase.trans hexp) d
    _ = Real.exp ((d : ℝ) * (p + 1)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hscale

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.McShaneEnvelope
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y : Type*} [Nonempty X] [PseudoMetricSpace Y]
  (φ : X → Y) (L : ℝ≥0)

noncomputable def mcShaneEnvelope (f : X → ℝ) (y : Y) : ℝ :=
  ⨅ x, f x + L * dist y (φ x)

omit [Nonempty X] in
theorem mcShaneEnvelope_bddBelow (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (y : Y) :
    BddBelow (Set.range (fun x => f x + L * dist y (φ x))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact add_nonneg (hf x) (mul_nonneg L.coe_nonneg dist_nonneg)

omit [Nonempty X] in
theorem mcShaneEnvelope_le (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (y : Y) (x : X) :
    mcShaneEnvelope φ L f y ≤ f x + L * dist y (φ x) :=
  ciInf_le (mcShaneEnvelope_bddBelow φ L f hf y) x

theorem mcShaneEnvelope_lipschitz (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    LipschitzWith L (mcShaneEnvelope φ L f) := by
  apply LipschitzWith.of_le_add_mul
  intro y z
  rw [← sub_le_iff_le_add]
  apply le_ciInf
  intro x
  rw [sub_le_iff_le_add]
  calc
    mcShaneEnvelope φ L f y ≤ f x + L * dist y (φ x) := mcShaneEnvelope_le φ L f hf y x
    _ ≤ f x + L * dist z (φ x) + L * dist y z := by
      have h := mul_le_mul_of_nonneg_left (dist_triangle y z (φ x)) L.coe_nonneg
      linarith

theorem mcShaneEnvelope_eq (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hLip : ∀ x z, |f x - f z| ≤ L * dist (φ x) (φ z)) (x : X) :
    mcShaneEnvelope φ L f (φ x) = f x := by
  apply le_antisymm
  · simpa only [dist_self, mul_zero, add_zero] using mcShaneEnvelope_le φ L f hf (φ x) x
  · apply le_ciInf
    intro z
    have h := (le_abs_self (f x - f z)).trans (hLip x z)
    linarith

theorem mcShaneEnvelope_le_add (f g : X → ℝ) (hf : ∀ x, 0 ≤ f x) {δ : ℝ}
    (hfg : ∀ x, f x ≤ g x + δ) (y : Y) :
    mcShaneEnvelope φ L f y ≤ mcShaneEnvelope φ L g y + δ := by
  rw [← sub_le_iff_le_add]
  apply le_ciInf
  intro x
  have h := mcShaneEnvelope_le φ L f hf y x
  linarith [hfg x]

theorem mcShaneEnvelope_abs_sub_le (f g : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) {δ : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ δ) (y : Y) :
    |mcShaneEnvelope φ L f y - mcShaneEnvelope φ L g y| ≤ δ := by
  apply abs_le.mpr
  constructor
  · have h := mcShaneEnvelope_le_add φ L g f hg
      (fun x => by have hx := (abs_le.mp (hfg x)).1; linarith) y
    linarith
  · have h := mcShaneEnvelope_le_add φ L f g hf
      (fun x => by have hx := (abs_le.mp (hfg x)).2; linarith) y
    linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModeShiftLengths
namespace OAI

section

namespace Erdos3

noncomputable def modeShiftLength (H T : ℝ) (stride : ℕ) : ℕ :=
  ⌊H / ((stride : ℝ) * T)⌋₊

theorem modeShiftLength_bounds {H T B : ℝ} {stride : ℕ}
    (hs : 0 < stride) (hT : 0 < T) (hB : 1 ≤ B)
    (hsize : (stride : ℝ) * T * (B + 1) ≤ H) :
    B ≤ (modeShiftLength H T stride : ℝ) ∧
      ((stride : ℝ) * T) * (modeShiftLength H T stride : ℝ) ≤ H ∧
      H ≤ (2 * T) * ((stride : ℝ) * (modeShiftLength H T stride : ℝ)) := by
  have hs' : 0 < (stride : ℝ) := by exact_mod_cast hs
  have hd : 0 < (stride : ℝ) * T := mul_pos hs' hT
  have hx : B + 1 ≤ H / ((stride : ℝ) * T) :=
    (le_div_iff₀ hd).mpr (by nlinarith [hsize])
  have hx0 : 0 ≤ H / ((stride : ℝ) * T) := by linarith
  have hf := Nat.lt_floor_add_one (H / ((stride : ℝ) * T))
  have hnb : B < (modeShiftLength H T stride : ℝ) := by
    dsimp [modeShiftLength]
    linarith
  have hu := (le_div_iff₀ hd).mp (Nat.floor_le hx0)
  have hl := (div_lt_iff₀ hd).mp hf
  have hn1 : 1 ≤ (modeShiftLength H T stride : ℝ) := hB.trans hnb.le
  have hprod := mul_le_mul_of_nonneg_left hn1 hd.le
  refine ⟨hnb.le, ?_, ?_⟩
  · change ((stride : ℝ) * T) * (⌊H / ((stride : ℝ) * T)⌋₊ : ℝ) ≤ H
    nlinarith [hu]
  · change H ≤ (2 * T) * ((stride : ℝ) * (⌊H / ((stride : ℝ) * T)⌋₊ : ℝ))
    dsimp [modeShiftLength] at hprod
    nlinarith [hl]

theorem exists_mode_shift_lengths {I K : Type*} (m : ℕ) {D T B ρ r : ℝ}
    (hT : 0 < T) (hB : 1 ≤ B) (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hmove : (m : ℝ) * D ≤ r * ρ * T)
    (H : I → ℝ) (stride : I → ℕ) (hs : ∀ j, 0 < stride j)
    (hsize : ∀ j, (stride j : ℝ) * T * (B + 1) ≤ H j)
    (V : K × I → ℝ) (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    ∃ N : I → ℕ, (∀ j, B ≤ (N j : ℝ)) ∧
      (∀ j, H j ≤ (2 * T) * ((stride j : ℝ) * (N j : ℝ))) ∧
      ∀ z, (m : ℝ) * D * ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z := by
  let N := fun j => modeShiftLength (H j) T (stride j)
  have hn j := modeShiftLength_bounds (hs j) hT hB (hsize j)
  refine ⟨N, (fun j => (hn j).1), (fun j => (hn j).2.2), ?_⟩
  intro z
  have hn0 : 0 ≤ (stride z.2 : ℝ) * (N z.2 : ℝ) := by positivity
  calc
    _ ≤ (r * ρ * T) * ((stride z.2 : ℝ) * (N z.2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hmove hn0
    _ = (r * ρ) * (((stride z.2 : ℝ) * T) * (N z.2 : ℝ)) := by ring
    _ ≤ (r * ρ) * H z.2 := mul_le_mul_of_nonneg_left (hn z.2).2.1 (mul_nonneg hr hρ.le)
    _ = r * (ρ * H z.2) := by ring
    _ ≤ r * V z := mul_le_mul_of_nonneg_left (hwidth z) hr

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
namespace OAI

section

namespace Erdos3
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
namespace NilpotentLieBCHGroup
variable {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

include hnil

namespace NilpotentLieBCHGroup

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3
variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

namespace NilpotentLieFiltration
variable {L} {s : ℕ} (F : NilpotentLieFiltration L s)
include F

theorem bch_mem {i : ℕ} {a b : L} (ha : a ∈ F.layer i) (hb : b ∈ F.layer i) :
    lieBCH s a b ∈ F.layer i :=
  lieBCH_mem (F.layerIdeal i).toLieSubalgebra s ha hb

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

variable [DecidableEq ι] [DecidableEq κ]

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
variable {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarefreeBlockDegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι]

noncomputable def blockDegree (π : ι → σ) (a : ι →₀ ℕ) : σ → ℕ := by
  classical
  exact fun i => ∑ j, if π j = i then a j else 0

theorem blockDegree_apply [DecidableEq σ] (π : ι → σ) (a : ι →₀ ℕ) (i : σ) :
    blockDegree π a i = ∑ j, if π j = i then a j else 0 := by
  classical
  unfold blockDegree
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : π j = i <;> simp only [h, ite_true, ite_false]

@[simp] theorem blockDegree_zero (π : ι → σ) : blockDegree π 0 = 0 := by
  classical
  ext i
  simp only [blockDegree_apply, Finsupp.zero_apply, ite_self, Finset.sum_const_zero, Pi.zero_apply]

theorem blockDegree_add (π : ι → σ) (a b : ι →₀ ℕ) :
    blockDegree π (a + b) = blockDegree π a + blockDegree π b := by
  classical
  ext i
  simp only [blockDegree_apply, Finsupp.add_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [add_zero]

theorem blockDegree_total [Fintype σ] (π : ι → σ) (a : ι →₀ ℕ) :
    ∑ i, blockDegree π a i = ∑ j, a j := by
  classical
  simp only [blockDegree_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultidegreePredecessor
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem multidegree_exists_predecessor {σ : Type*} [Fintype σ] [DecidableEq σ]
    (b : σ → ℕ) (hb : 0 < ∑ i, b i) :
    ∃ a : σ → ℕ, a < b ∧ (∑ i, a i) + 1 = ∑ i, b i := by
  have hne : b ≠ 0 := by intro h; simp only [h, Pi.zero_apply, Finset.sum_const_zero] at hb; omega
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hbi : b i ≠ 0 := by simpa only [Pi.zero_apply] using hi
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hbi
  let a : σ → ℕ := Function.update b i k
  have heq : b = a + Pi.single i 1 := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [a, hk]
    · simp [a, Function.update_of_ne hji, Pi.single_eq_of_ne hji]
  have hle : a ≤ b := by rw [heq]; exact fun j => Nat.le_add_right _ _
  have hnot : ¬b ≤ a := by
    intro h
    have hh := h i
    simp only [a, Function.update_self, hk] at hh
    omega
  refine ⟨a, lt_iff_le_not_ge.mpr ⟨hle, hnot⟩, ?_⟩
  rw [heq]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  congr 1
  simp

theorem multidegree_exists_predecessor_above {σ : Type*} [Fintype σ] [DecidableEq σ]
    (b : σ → ℕ) (n : ℕ) (hb : n + 1 ≤ ∑ i, b i) :
    ∃ a : σ → ℕ, a < b ∧ n ≤ ∑ i, a i := by
  obtain ⟨a, hab, ha⟩ := multidegree_exists_predecessor b (by omega)
  exact ⟨a, hab, by omega⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OrderedLayerSplit
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_subtype_gt {A M : Type*} [Fintype A] [LinearOrder A] [AddCommMonoid M]
    (i : A) (f : A → M) :
    (∑ j : {j : A // i < j}, f j.val) = ∑ j, if i < j then f j else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

theorem sum_split_at_layer {A M : Type*} [Fintype A] [LinearOrder A] [AddCommMonoid M]
    (i : A) (f : A → M) :
    (∑ j, f j) = f i + (∑ j, if j < i then f j else 0) +
      ∑ j : {j : A // i < j}, f j.val := by
  classical
  rw [sum_subtype_gt]
  have he (j : A) : f j =
      (if j = i then f j else 0) + (if j < i then f j else 0) +
        (if i < j then f j else 0) := by
    rcases lt_trichotomy j i with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  conv_lhs => arg 2; ext j; rw [he j]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem exists_highest_exceptional_layer {A : Type*} [Fintype A] [LinearOrder A]
    (good : A → Prop) (hbad : ∃ i, ¬good i) :
    ∃ i, ¬good i ∧ ∀ j, i < j → good j := by
  classical
  let bad := Finset.univ.filter (fun i => ¬good i)
  have hne : bad.Nonempty := by
    obtain ⟨i, hi⟩ := hbad
    exact ⟨i, by simp [bad, hi]⟩
  refine ⟨bad.max' hne, (Finset.mem_filter.mp (Finset.max'_mem bad hne)).2, ?_⟩
  intro j hj
  by_contra hn
  have hm : j ∈ bad := by simp [bad, hn]
  exact (not_le_of_gt hj) (Finset.le_max' bad j hm)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RiemannianLipschitz
namespace OAI

section

namespace Erdos3

open Manifold MeasureTheory _root_.Set
open scoped Manifold ContDiff ENNReal

variable {E F H K M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
  [∀ x : M, ENorm (TangentSpace I x)] [∀ x : N, ENorm (TangentSpace J x)]

theorem pathELength_comp_le_of_mfderiv_norm_le {φ : M → N}
    (hφ : ContMDiff I J 1 φ)
    (hbound : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J φ x v‖ₑ ≤ ‖v‖ₑ)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ) (a b : ℝ) :
    pathELength J (φ ∘ γ) a b ≤ pathELength I γ a b := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_mono
  intro t
  exact (congrArg (fun v : TangentSpace J (φ (γ t)) => ‖v‖ₑ)
    (mfderiv_comp_apply t (hφ.mdifferentiableAt one_ne_zero)
      (hγ.mdifferentiableAt one_ne_zero) 1)).trans_le (hbound (γ t) _)

variable [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
  [∀ x : N, ENormSMulClass ℝ (TangentSpace J x)]

theorem riemannianEDist_le_of_mfderiv_norm_le {φ : M → N}
    (hφ : ContMDiff I J 1 φ)
    (hbound : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J φ x v‖ₑ ≤ ‖v‖ₑ)
    (x y : M) : riemannianEDist J (φ x) (φ y) ≤ riemannianEDist I x y := by
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
  have hends : riemannianEDist J (φ x) (φ y) ≤ pathELength J (φ ∘ γ) 0 1 :=
    riemannianEDist_le_pathELength (hφ.comp hγ).contMDiffOn
      (by simp only [Function.comp_apply, hγ0])
      (by simp only [Function.comp_apply, hγ1]) zero_le_one
  exact (hends.trans (pathELength_comp_le_of_mfderiv_norm_le hφ hbound hγ 0 1)).trans_lt hlen

end Erdos3

end

section

namespace Erdos3

open Manifold MeasureTheory _root_.Set
open scoped Manifold ContDiff ENNReal NNReal Bundle

variable {E F H K M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
  [∀ x : M, ENorm (TangentSpace I x)] [∀ x : N, ENorm (TangentSpace J x)]

theorem pathELength_comp_le_mul_of_mfderiv_bound {φ : M → N} {C : ℝ≥0}
    (hφ : ContMDiff I J 1 φ)
    (hbound : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J φ x v‖ₑ ≤ C * ‖v‖ₑ)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ) (a b : ℝ) :
    pathELength J (φ ∘ γ) a b ≤ C * pathELength I γ a b := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, pathELength_eq_lintegral_mfderiv_Icc,
    ← lintegral_const_mul' (C : ℝ≥0∞) _ (by simp)]
  apply lintegral_mono
  intro t
  exact (congrArg (fun v : TangentSpace J (φ (γ t)) => ‖v‖ₑ)
    (mfderiv_comp_apply t (hφ.mdifferentiableAt one_ne_zero)
      (hγ.mdifferentiableAt one_ne_zero) 1)).trans_le (hbound (γ t) _)

variable [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
  [∀ x : N, ENormSMulClass ℝ (TangentSpace J x)]

theorem riemannianEDist_le_mul_of_mfderiv_bound {φ : M → N} {C : ℝ≥0}
    (hC : 0 < C) (hφ : ContMDiff I J 1 φ)
    (hbound : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J φ x v‖ₑ ≤ C * ‖v‖ₑ)
    (x y : M) : riemannianEDist J (φ x) (φ y) ≤ C * riemannianEDist I x y := by
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  have hCt : (C : ℝ≥0∞) ≠ ⊤ := by simp
  apply le_of_forall_gt
  intro r hr
  have hinput : riemannianEDist I x y < r / C := by
    apply (ENNReal.lt_div_iff_mul_lt (.inl hC0) (.inl hCt)).mpr
    simpa only [mul_comm] using hr
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hinput zero_lt_one
  have hends : riemannianEDist J (φ x) (φ y) ≤ pathELength J (φ ∘ γ) 0 1 :=
    riemannianEDist_le_pathELength (hφ.comp hγ).contMDiffOn
      (by simp only [Function.comp_apply, hγ0])
      (by simp only [Function.comp_apply, hγ1]) zero_le_one
  have hmul : (C : ℝ≥0∞) * pathELength I γ 0 1 < r := by
    simpa only [mul_comm] using
      (ENNReal.lt_div_iff_mul_lt (.inl hC0) (.inl hCt)).mp hlen
  exact (hends.trans (pathELength_comp_le_mul_of_mfderiv_bound hφ hbound hγ 0 1)).trans_lt hmul

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TangentModelVector
namespace OAI

section

namespace Erdos3

open scoped Manifold

def tangentModelVector {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {x : M} (v : TangentSpace I x) : E := v

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RectangularDetExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem rectangular_det_expansion {I J R : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [CommRing R] (A : Matrix I J R) (B : Matrix J I R) :
    (A*B).det = ∑ p : I → J, (A.submatrix id p).det * ∏ i, B (p i) i := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
    Fintype.piFinset_univ, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id_eq]
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialStarCoordinates
namespace OAI

section

namespace Erdos3

def spatialStar {I R : Type*} [Add R] (v : (Unit ⊕ I) → R) : (Unit ⊕ I) → R :=
  Sum.elim (fun _ => v (.inl ())) (fun i => v (.inl ()) + v (.inr i))

def spatialUnstar {I R : Type*} [Sub R] (v : (Unit ⊕ I) → R) : (Unit ⊕ I) → R :=
  Sum.elim (fun _ => v (.inl ())) (fun i => v (.inr i) - v (.inl ()))

theorem spatialUnstar_star {I R : Type*} [AddCommGroup R] (v : (Unit ⊕ I) → R) :
    spatialUnstar (spatialStar v) = v := by
  funext i
  cases i with
  | inl i => cases i; rfl
  | inr i => simp [spatialUnstar, spatialStar]

theorem spatialStar_unstar {I R : Type*} [AddCommGroup R] (v : (Unit ⊕ I) → R) :
    spatialStar (spatialUnstar v) = v := by
  funext i
  cases i with
  | inl i => cases i; rfl
  | inr i => simp [spatialUnstar, spatialStar]

def spatialStarVertex {I : Type*} : (Unit ⊕ I) → Finset I :=
  Sum.elim (fun _ => ∅) (fun i => {i})

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialPotential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

noncomputable def weightedPolynomialPotential (w : σ → ℕ) (d : ℕ)
    (P : σ → MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  (d : ℚ)⁻¹ • ∑ i, w i • (X i * P i)

theorem weightedPolynomialPotential_pderiv_formula (w : σ → ℕ) (d : ℕ)
    (P : σ → MvPolynomial σ ℚ) (i : σ) :
    pderiv i (weightedPolynomialPotential w d P) =
      (d : ℚ)⁻¹ • (w i • P i + ∑ j, w j • (X j * pderiv i (P j))) := by
  classical
  have hterm (j : σ) : pderiv i (w j • (X j * P j)) =
      (if j = i then w i • P i else 0) + w j • (X j * pderiv i (P j)) := by
    by_cases hji : j = i
    · subst j
      simp
      ring
    · simp [pderiv_X_of_ne hji, hji]
  rw [weightedPolynomialPotential, (pderiv i).map_smul, map_sum]
  simp only [hterm, Finset.sum_add_distrib]
  simp

theorem weightedPolynomialPotential_pderiv (w : σ → ℕ) {d : ℕ} (hd : 0 < d)
    (P : σ → MvPolynomial σ ℚ)
    (hweight : ∀ i, w i ≤ d)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i))
    (hclosed : ∀ i j, pderiv i (P j) = pderiv j (P i)) (i : σ) :
    pderiv i (weightedPolynomialPotential w d P) = P i := by
  rw [weightedPolynomialPotential_pderiv_formula]
  simp only [hclosed i]
  rw [(hhom i).sum_weight_X_mul_pderiv, ← add_nsmul, Nat.add_sub_of_le (hweight i)]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd.ne'), one_smul]

theorem weightedPolynomialPotential_homogeneous (w : σ → ℕ) (d : ℕ)
    (P : σ → MvPolynomial σ ℚ)
    (hweight : ∀ i, w i ≤ d)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i)) :
    (weightedPolynomialPotential w d P).IsWeightedHomogeneous w d := by
  change weightedPolynomialPotential w d P ∈ weightedHomogeneousSubmodule ℚ w d
  apply (weightedHomogeneousSubmodule ℚ w d).smul_mem
  apply (weightedHomogeneousSubmodule ℚ w d).sum_mem
  intro i _
  have hprod : (X i * P i).IsWeightedHomogeneous w d := by
    have h := (isWeightedHomogeneous_X (R := ℚ) w i).mul (hhom i)
    simpa only [Nat.add_sub_of_le (hweight i)] using h
  exact (weightedHomogeneousSubmodule ℚ w d).nsmul_mem hprod (w i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NormalizedRealPolynomialChart
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

noncomputable def normalizedRealPolynomialChart (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) : U ⊕ B → MvPolynomial (U ⊕ B) ℝ :=
  Sum.elim (fun i => C ((H i)⁻¹) * X (Sum.inl i))
    (fun j => X (Sum.inr j) - rename Sum.inl (A j))

@[simp] theorem normalizedRealPolynomialChart_inl (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) (i : U) :
    normalizedRealPolynomialChart H A (Sum.inl i) = C ((H i)⁻¹) * X (Sum.inl i) :=
  rfl

@[simp] theorem normalizedRealPolynomialChart_inr (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) (j : B) :
    normalizedRealPolynomialChart H A (Sum.inr j) =
      X (Sum.inr j) - rename Sum.inl (A j) :=
  rfl

@[simp] theorem normalizedRealPolynomialChart_eval (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) (u : U → ℝ) (b : B → ℝ) (j : U ⊕ B) :
    eval (Sum.elim u b) (normalizedRealPolynomialChart H A j) =
      Sum.elim (fun i => u i / H i) (fun i => b i - eval u (A i)) j := by
  cases j <;>
    simp [normalizedRealPolynomialChart, eval_rename, Function.comp_def,
      div_eq_mul_inv, mul_comm]

theorem normalizedRealPolynomialChart_eval_comp (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) (u : U → ℝ) (b : B → ℝ) :
    eval (Sum.elim u b) ∘ normalizedRealPolynomialChart H A =
      Sum.elim (fun i => u i / H i) (fun i => b i - eval u (A i)) := by
  funext j
  exact normalizedRealPolynomialChart_eval H A u b j

theorem eval_normalizedRealPolynomialChart_substitution (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) (u : U → ℝ) (b : B → ℝ)
    (p : MvPolynomial (U ⊕ B) ℝ) :
    eval (Sum.elim u b) (eval₂Hom C (normalizedRealPolynomialChart H A) p) =
      eval (Sum.elim (fun i => u i / H i) (fun i => b i - eval u (A i))) p := by
  rw [coe_eval₂Hom, ← eval_assoc, normalizedRealPolynomialChart_eval_comp]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FactorialIntegerScalars
namespace OAI

section

namespace Erdos3

theorem rat_nat_div_integer_of_dvd {m n : ℕ} (h : n ∣ m) :
    ∃ z : ℤ, (m : ℚ) / n = (z : ℚ) := by
  obtain ⟨d, rfl⟩ := h
  by_cases hn : n = 0
  · exact ⟨0, by simp [hn]⟩
  · exact ⟨d, by push_cast; field_simp⟩

theorem factorial_log_scalar_integer (s k : ℕ) (hk : k ≤ s) :
    ∃ z : ℤ, (s.factorial : ℚ) * ((-1 : ℚ) ^ (k + 1) / k) = (z : ℚ) := by
  by_cases hzero : k = 0
  · exact ⟨0, by simp [hzero]⟩
  obtain ⟨z, hz⟩ := rat_nat_div_integer_of_dvd (Nat.dvd_factorial (Nat.pos_of_ne_zero hzero) hk)
  refine ⟨(-1 : ℤ) ^ (k + 1) * z, ?_⟩
  push_cast
  rw [show (s.factorial : ℚ) * ((-1 : ℚ) ^ (k + 1) / k) =
    (-1 : ℚ) ^ (k + 1) * ((s.factorial : ℚ) / k) by ring, hz]

theorem factorial_exp_scalar_integer (s k : ℕ) (hk : k ≤ s) :
    ∃ z : ℤ, (k.factorial : ℚ)⁻¹ * (s.factorial : ℚ) ^ k = (z : ℚ) := by
  cases k with
  | zero => exact ⟨1, by simp⟩
  | succ k =>
    have hd : (k + 1).factorial ∣ s.factorial ^ (k + 1) := by
      rw [pow_succ']
      exact (Nat.factorial_dvd_factorial hk).trans (Nat.dvd_mul_right _ _)
    obtain ⟨z, hz⟩ := rat_nat_div_integer_of_dvd hd
    exact ⟨z, by simpa only [Nat.cast_pow, div_eq_mul_inv, mul_comm] using hz⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpanningFlagSelection
namespace OAI

section

namespace Erdos3

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_nested_independent_spanning_sets (n : ℕ) :
    ∀ (P : Fin n → Submodule K V) (S : Set V), Antitone P →
      (∀ i, Submodule.span K (S ∩ (P i : Set V)) = P i) →
      ∃ B : Set V, B ⊆ S ∧ LinearIndepOn K id B ∧
        Submodule.span K B = Submodule.span K S ∧
        ∃ T : Fin n → Set V, Antitone T ∧ (∀ i, T i ⊆ B) ∧
          ∀ i, Submodule.span K (T i) = P i := by
  induction n with
  | zero =>
      intro P S _ _
      let h := linearIndepOn_empty K (id : V → V)
      let hsub : (∅ : Set V) ⊆ S := Set.empty_subset S
      refine ⟨h.extend hsub, h.extend_subset hsub, h.linearIndepOn_extend hsub,
        h.span_extend_eq_span hsub, Fin.elim0, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      intro P S hP hspan
      let S₀ := S ∩ (P 0 : Set V)
      let P' : Fin n → Submodule K V := fun i => P i.succ
      have hP' : Antitone P' := fun i j hij => hP (by simpa using hij)
      have hspan' (i : Fin n) : Submodule.span K (S₀ ∩ (P' i : Set V)) = P' i := by
        have heq : S₀ ∩ (P' i : Set V) = S ∩ (P i.succ : Set V) := by
          ext x
          constructor
          · exact fun hx => ⟨hx.1.1, hx.2⟩
          · exact fun hx => ⟨⟨hx.1, hP (Fin.zero_le i.succ) hx.2⟩, hx.2⟩
        rw [heq]
        exact hspan i.succ
      obtain ⟨B₀, hB₀, hiB₀, hspB₀, T₀, hT₀, hTB₀, hspT₀⟩ := ih P' S₀ hP' hspan'
      have hBS : B₀ ⊆ S := fun _ hx => (hB₀ hx).1
      let B := hiB₀.extend hBS
      have hB₀B : B₀ ⊆ B := hiB₀.subset_extend hBS
      let T : Fin (n + 1) → Set V := Fin.cases B₀ T₀
      refine ⟨B, hiB₀.extend_subset hBS, hiB₀.linearIndepOn_extend hBS,
        hiB₀.span_extend_eq_span hBS, T, ?_, ?_, ?_⟩
      · intro i j hij
        obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
        · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
          · exact Set.Subset.rfl
          · exact hTB₀ j
        · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
          · exact False.elim ((not_le_of_gt (Fin.succ_pos i)) hij)
          · exact hT₀ (by simpa using hij)
      · intro i
        exact Fin.cases hB₀B (fun j => (hTB₀ j).trans hB₀B) i
      · intro i
        refine Fin.cases ?_ (fun j => hspT₀ j) i
        exact hspB₀.trans (hspan 0)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SubmoduleSupRestriction
namespace OAI

section

namespace Erdos3

theorem submodule_comap_iSup_of_le_range {R M N : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {I : Sort*} (f : M →ₗ[R] N) (hf : Function.Injective f)
    (P : I → Submodule R N) (hP : ∀ i, P i ≤ LinearMap.range f) :
    (⨆ i, P i).comap f = ⨆ i, (P i).comap f := by
  apply Submodule.map_injective_of_injective hf
  rw [Submodule.map_comap_eq_of_le (iSup_le hP), Submodule.map_iSup]
  exact iSup_congr (fun i => (Submodule.map_comap_eq_of_le (hP i)).symm)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealOrderedBasisProduct
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] {d s : ℕ}
  (e : Basis (Fin d) ℝ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def realOrderedBasisTailProduct (i : ℕ) (t : Fin d → ℝ) :
    NilpotentLieBCHGroup L s hnil :=
  (((List.finRange d).drop i).map fun j => (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil)).prod

noncomputable def realOrderedBasisProduct (t : Fin d → ℝ) : NilpotentLieBCHGroup L s hnil :=
  realOrderedBasisTailProduct e hnil 0 t

noncomputable def realOrderedBasisPrefixProduct (i : ℕ) (t : Fin d → ℝ) :
    NilpotentLieBCHGroup L s hnil :=
  (((List.finRange d).take i).map fun j => (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil)).prod

theorem realOrderedBasisPrefixProduct_congr (i : ℕ) {t u : Fin d → ℝ}
    (h : ∀ j : Fin d, j.val < i → t j = u j) :
    realOrderedBasisPrefixProduct e hnil i t = realOrderedBasisPrefixProduct e hnil i u := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  obtain ⟨k, hk, hkj⟩ := List.mem_take_iff_getElem.mp hj
  have hval : k = j.val := by simpa using congrArg Fin.val hkj
  rw [h j (by omega)]

variable [IsScalarTower ℚ ℝ L]

namespace IsRealCentralLieBasis

variable {e}

end IsRealCentralLieBasis
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultilinearCoordinateExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem multilinear_coordinate_expansion {H I R : Type*} [Fintype H] [Fintype I]
    [DecidableEq H] [DecidableEq I] [CommRing R]
    (F : MultilinearMap R (fun _ : H => I → R) R) (u : H → I → R) :
    F u = ∑ j : H → I, F (fun i => Pi.single (j i) (1 : R)) * ∏ i, u i (j i) := by
  have hu : u = fun h => ∑ i, u h i • Pi.single i (1 : R) := by
    funext h i
    simp [Pi.single_apply]
  calc
    F u = F (fun h => ∑ i, u h i • Pi.single i (1 : R)) := congrArg F hu
    _ = ∑ j : H → I, F (fun h => u h (j h) • Pi.single (j h) (1 : R)) :=
      F.map_sum (fun h i => u h i • Pi.single i (1 : R))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [F.map_smul_univ, smul_eq_mul, mul_comm]

theorem multilinear_diagonal_expansion {H I R : Type*} [Fintype H] [Fintype I]
    [DecidableEq H] [DecidableEq I] [CommRing R]
    (F : MultilinearMap R (fun _ : H => I → R) R) (w : I → R) :
    F (fun _ => w) = ∑ j : H → I, F (fun i => Pi.single (j i) (1 : R)) * ∏ i, w (j i) :=
  multilinear_coordinate_expansion F (fun _ => w)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SeparatedPositiveSum
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem separated_tsum_lipschitz {ι X : Type*} [PseudoMetricSpace X]
    (f : ι → X → ℝ) {K : ℝ≥0} (hf : ∀ i, LipschitzWith K (f i))
    (hpos : ∀ i x, 0 ≤ f i x)
    (hsep : ∀ x i j, f i x ≠ 0 → f j x ≠ 0 → i = j) :
    LipschitzWith K (fun x => ∑' i, f i x) := by
  have hsingle (x : X) (i : ι) (hi : f i x ≠ 0) : (∑' j, f j x) = f i x := by
    apply tsum_eq_single i
    intro j hji
    by_contra hj
    exact hji (hsep x j i hj hi)
  have hdom (x : X) (i : ι) : f i x ≤ ∑' j, f j x := by
    by_cases hi : f i x = 0
    · rw [hi]
      exact tsum_nonneg (fun j => hpos j x)
    · rw [hsingle x i hi]
  have hsub (x y : X) : (∑' i, f i x) - (∑' i, f i y) ≤ K * dist x y := by
    by_cases hx : ∃ i, f i x ≠ 0
    · obtain ⟨i, hi⟩ := hx
      rw [hsingle x i hi]
      have h := (le_abs_self (f i x - f i y)).trans ((hf i).dist_le_mul x y)
      linarith [hdom y i]
    · have hz : ∀ i, f i x = 0 := fun i => not_ne_iff.mp (fun hi => hx ⟨i, hi⟩)
      simp only [hz, tsum_zero, zero_sub]
      exact le_trans (neg_nonpos.mpr (tsum_nonneg (fun i => hpos i y)))
        (mul_nonneg K.coe_nonneg dist_nonneg)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  have hxy := hsub x y
  have hyx := hsub y x
  rw [dist_comm y x] at hyx
  constructor <;> linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixModuleAction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def matrixModuleAction {I J W : Type*} [Fintype J]
    [AddCommGroup W] [Module ℝ W] (A : Matrix I J ℝ) : (J → W) →ₗ[ℝ] (I → W) where
  toFun x i := ∑ j, A i j • x j
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm (A i j) r (x j)

theorem matrixModuleAction_apply {I J W : Type*} [Fintype J]
    [AddCommGroup W] [Module ℝ W] (A : Matrix I J ℝ) (x : J → W) (i : I) :
    matrixModuleAction A x i = ∑ j, A i j • x j := rfl

theorem matrixModuleAction_mul {I J K W : Type*} [Fintype J] [Fintype K]
    [AddCommGroup W] [Module ℝ W] (A : Matrix I J ℝ) (B : Matrix J K ℝ) (x : K → W) :
    matrixModuleAction A (matrixModuleAction B x) = matrixModuleAction (A * B) x := by
  funext i
  simp only [matrixModuleAction_apply, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
  exact Finset.sum_comm

theorem matrixModuleAction_image_section {I J W : Type*} [Fintype I] [Fintype J]
    [AddCommGroup W] [Module ℝ W] (A : Matrix I J ℝ) (S : Matrix J I ℝ)
    (hS : A * S * A = A) (x : J → W) :
    matrixModuleAction A (matrixModuleAction S (matrixModuleAction A x)) = matrixModuleAction A x := by
  rw [matrixModuleAction_mul, matrixModuleAction_mul, hS]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.QuotientActionMatrix
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {K V W ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem quotient_basis_representative (e : Basis ι K V) (f : Basis κ K W)
    (q : V →ₗ[K] W) (D : Matrix κ ι K) (S : Matrix ι κ K)
    (hD : LinearMap.toMatrix e f q = D) (hDS : D * S = 1) (y : κ → K) :
    f.equivFun.symm y = q (e.equivFun.symm (S *ᵥ y)) := by
  apply f.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  change y = f.repr (q (e.equivFun.symm (S *ᵥ y)))
  rw [← LinearMap.toMatrix_mulVec_repr e f q, hD]
  change y = D *ᵥ e.equivFun (e.equivFun.symm (S *ᵥ y))
  rw [LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, hDS, Matrix.one_mulVec]

theorem quotient_action_matrix (e : Basis ι K V) (f : Basis κ K W)
    (q : V →ₗ[K] W) (A : V →ₗ[K] V) (B : W →ₗ[K] W)
    (hAB : ∀ x, q (A x) = B (q x)) (S : Matrix ι κ K)
    (hS : LinearMap.toMatrix e f q * S = 1) :
    LinearMap.toMatrix f f B = LinearMap.toMatrix e f q * LinearMap.toMatrix e e A * S := by
  let L := Matrix.toLin f e S
  have hqL : q.comp L = LinearMap.id := by
    apply (LinearMap.toMatrix f f).injective
    rw [LinearMap.toMatrix_comp f e f, LinearMap.toMatrix_id]
    change LinearMap.toMatrix e f q * LinearMap.toMatrix f e (Matrix.toLin f e S) = 1
    rw [LinearMap.toMatrix_toLin, hS]
  have he : B = q.comp (A.comp L) := by
    ext x
    change B x = q (A (L x))
    rw [hAB, show q (L x) = x from DFunLike.congr_fun hqL x]
  rw [he, LinearMap.toMatrix_comp f e f, LinearMap.toMatrix_comp f e e]
  change LinearMap.toMatrix e f q *
    (LinearMap.toMatrix e e A * LinearMap.toMatrix f e (Matrix.toLin f e S)) = _
  rw [LinearMap.toMatrix_toLin, Matrix.mul_assoc]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CyclicIntervalSampling
namespace OAI

section

namespace Erdos3

theorem finiteCorrelation_image_of_injOn {A B : Type*} [DecidableEq B]
    (Q : Finset A) (φ : A → B) (hφ : Set.InjOn φ (Q : Set A)) (f u : B → ℂ) :
    finiteCorrelation (Q.image φ) f u =
      finiteCorrelation Q (fun x => f (φ x)) (fun x => u (φ x)) := by
  unfold finiteCorrelation
  exact Finset.expect_image hφ

theorem cyclicInterval_representative_correlation {N : ℕ} [NeZero N]
    (a len : ℕ) (hbound : a + len ≤ N) (hshort : 2 * ((len : ℤ) - 1) < N)
    (f : ZMod N → ℂ) (u : ℤ → ℂ) :
    finiteCorrelation (cyclicInterval (a : ZMod N) len) f (fun x => u (x.val : ℤ)) =
      finiteCorrelation (Finset.Ico (a : ℤ) (a + len)) (fun x => f (x : ZMod N)) u := by
  have he := integerInterval_reflectsPairSums N (a : ℤ) (a + len) (by omega)
  rw [← Int.cast_natCast a, ← integerInterval_image_cyclicInterval,
    finiteCorrelation_image_of_injOn _ _ he.injOn]
  unfold finiteCorrelation
  apply Finset.expect_congr rfl
  intro x hx
  have hx' := Finset.mem_Ico.mp hx
  have hrep : (((x : ZMod N).val : ℕ) : ℤ) = x := by
    rw [ZMod.val_intCast, Int.emod_eq_of_lt (by omega) (by omega)]
  change f (x : ZMod N) * star (u (((x : ZMod N).val : ℕ) : ℤ)) = _
  rw [hrep]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LocalizationPolynomialScales
namespace OAI

section

namespace Erdos3

noncomputable def localizationRadius (U ε : ℝ) : ℝ := ε / (8 * U ^ 2)
noncomputable def localizationMesh (U ε : ℝ) : ℝ := ε ^ 2 / (128 * U ^ 5)
noncomputable def localizationLengthBudget (U ε W : ℝ) : ℝ := 256 * U ^ 6 * W / ε ^ 2

theorem localizationRadius_pos {U ε : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) :
    0 < localizationRadius U ε := by unfold localizationRadius; positivity

theorem localizationMesh_pos {U ε : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) :
    0 < localizationMesh U ε := by unfold localizationMesh; positivity

theorem localizationMesh_le_one {U ε : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    localizationMesh U ε ≤ 1 := by
  have hp : 1 ≤ U ^ 5 := one_le_pow₀ hU
  unfold localizationMesh
  apply (div_le_one (by positivity)).mpr
  nlinarith

theorem localizationMesh_length {U ε W : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) :
    localizationMesh U ε * localizationLengthBudget U ε W = 2 * U * W := by
  have hU0 : U ≠ 0 := by linarith
  unfold localizationMesh localizationLengthBudget
  field_simp
  ring

theorem localizationMesh_margin {U ε : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    U * localizationMesh U ε < localizationRadius U ε := by
  have hU0 : 0 < U := by linarith
  have hp : 1 ≤ U ^ 2 := one_le_pow₀ hU
  have he : U * localizationMesh U ε = localizationRadius U ε * (ε / (16 * U ^ 2)) := by
    unfold localizationRadius localizationMesh
    field_simp
    ring
  rw [he]
  apply mul_lt_of_lt_one_right (localizationRadius_pos hU hε)
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem localizationLengthBudget_ge_square {U ε W : ℝ}
    (hU : 1 ≤ U) (hε : 0 < ε) (hε1 : ε ≤ 1) (hW : 1 ≤ W) :
    U ^ 2 ≤ localizationLengthBudget U ε W := by
  have hp : U ^ 2 ≤ U ^ 6 := pow_le_pow_right₀ hU (by decide : 2 ≤ 6)
  have he : ε ^ 2 ≤ 1 := by nlinarith
  have hU6 : 0 ≤ U ^ 6 := by positivity
  have hprod : U ^ 6 ≤ U ^ 6 * W := le_mul_of_one_le_right hU6 hW
  unfold localizationLengthBudget
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  have hsmall := mul_le_of_le_one_right (sq_nonneg U) he
  nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GeometricLocalizationThreshold
namespace OAI

section

namespace Erdos3

noncomputable def localizationThreshold (U ζ : ℝ) (i : ℕ) : ℝ := ζ / (2 * U ^ 2) ^ i

theorem localizationThreshold_pos {U ζ : ℝ} (hU : 1 ≤ U) (hζ : 0 < ζ) (i : ℕ) :
    0 < localizationThreshold U ζ i := by unfold localizationThreshold; positivity

theorem localizationThreshold_zero (U ζ : ℝ) : localizationThreshold U ζ 0 = ζ := by
  simp only [localizationThreshold, pow_zero, div_one]

theorem localizationThreshold_antitone {U ζ : ℝ} (hU : 1 ≤ U) (hζ : 0 ≤ ζ)
    {i j : ℕ} (hij : i ≤ j) : localizationThreshold U ζ j ≤ localizationThreshold U ζ i := by
  have hC : 1 ≤ 2 * U ^ 2 := by nlinarith [one_le_pow₀ hU (n := 2)]
  apply div_le_div_of_nonneg_left hζ (by positivity)
  exact pow_le_pow_right₀ hC hij

theorem localizationThreshold_le_one {U ζ : ℝ} (hU : 1 ≤ U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (i : ℕ) :
    localizationThreshold U ζ i ≤ 1 := by
  have h := localizationThreshold_antitone hU hζ.le (Nat.zero_le i)
  rw [localizationThreshold_zero] at h
  exact h.trans hζ1

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitGroupRelative
namespace OAI

section

namespace Erdos3

variable {G H : Type*} [Group G] [Group H] (q : G →* H) (d : H →* G)

def splitRelativePart (g : G) : G := g * (d (q g))⁻¹

theorem splitRelativePart_projection (hd : ∀ h, q (d h) = h) (g : G) :
    q (splitRelativePart q d g) = 1 := by
  simp only [splitRelativePart, map_mul, map_inv, hd, mul_inv_cancel]

theorem splitRelativePart_mul (g h : G) :
    splitRelativePart q d (g * h) =
      splitRelativePart q d g * (d (q g) * splitRelativePart q d h * (d (q g))⁻¹) := by
  simp only [splitRelativePart, map_mul]
  group

theorem splitRelativePart_same_projection {g h : G} (hproj : q g = q h) :
    splitRelativePart q d g * (splitRelativePart q d h)⁻¹ = g * h⁻¹ := by
  simp only [splitRelativePart, hproj]
  group

theorem splitRelativePart_pair_mem (hd : ∀ h, q (d h) = h) (U : Subgroup G)
    {g h : G} (hg : g ∈ U) (hh : h ∈ U) (hproj : q g = q h) :
    splitRelativePart q d g * (splitRelativePart q d h)⁻¹ ∈ U ⊓ q.ker := by
  constructor
  · rw [splitRelativePart_same_projection q d hproj]
    exact U.mul_mem hg (U.inv_mem hh)
  · change q (splitRelativePart q d g * (splitRelativePart q d h)⁻¹) = 1
    rw [map_mul, map_inv, splitRelativePart_projection q d hd,
      splitRelativePart_projection q d hd, inv_one, mul_one]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SortedPositiveWeights
namespace OAI

section

namespace Erdos3

theorem exists_sorted_positive_weights {d : ℕ} (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i) :
    ∃ (e : Equiv.Perm (Fin d)) (a : ℕ), a ≤ d ∧ Monotone (w ∘ e) ∧
      ∀ i, i.val < a ↔ w (e i) = 1 := by
  classical
  let e := Tuple.sort w
  let a := (Finset.univ.filter (fun i => w (e i) ≤ 1)).card
  have hm : Monotone (w ∘ e) := Tuple.monotone_sort w
  refine ⟨e, a, ?_, hm, ?_⟩
  · exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin d)
  · intro i
    have hi : i.val < a ↔ w (e i) ≤ 1 :=
      Tuple.lt_card_le_iff_apply_le_of_monotone hm
    exact hi.trans ⟨fun h => Nat.le_antisymm h (hw (e i)), fun h => h.le⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonKernelRangeEquiv
namespace OAI

section

namespace Erdos3

variable {K A B C : Type*} [Field K] [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]

noncomputable def commonKernelRangeEquiv (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (h : LinearMap.ker f = LinearMap.ker g) : LinearMap.range f ≃ₗ[K] LinearMap.range g :=
  f.quotKerEquivRange.symm.trans ((Submodule.quotEquivOfEq _ _ h).trans g.quotKerEquivRange)

theorem commonKernelRangeEquiv_apply (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (h : LinearMap.ker f = LinearMap.ker g) (x : A) :
    (commonKernelRangeEquiv f g h ⟨f x, ⟨x, rfl⟩⟩ : C) = g x := by
  dsimp only [commonKernelRangeEquiv, LinearEquiv.trans_apply]
  rw [f.quotKerEquivRange_symm_apply_image x ⟨x, rfl⟩]
  rfl

noncomputable def commonKernelSubmoduleEquiv (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (U : Submodule K B) (V : Submodule K C)
    (h : LinearMap.ker f = LinearMap.ker g)
    (hf : LinearMap.range f = U) (hg : LinearMap.range g = V) : U ≃ₗ[K] V :=
  (LinearEquiv.ofEq U (LinearMap.range f) hf.symm).trans
    ((commonKernelRangeEquiv f g h).trans (LinearEquiv.ofEq (LinearMap.range g) V hg))

theorem commonKernelSubmoduleEquiv_apply (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (U : Submodule K B) (V : Submodule K C)
    (h : LinearMap.ker f = LinearMap.ker g)
    (hf : LinearMap.range f = U) (hg : LinearMap.range g = V)
    (x : A) (hx : f x ∈ U) :
    (commonKernelSubmoduleEquiv f g U V h hf hg ⟨f x, hx⟩ : C) = g x :=
  commonKernelRangeEquiv_apply f g h x

theorem commonKernelSubmoduleEquiv_symm_apply (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (U : Submodule K B) (V : Submodule K C)
    (h : LinearMap.ker f = LinearMap.ker g)
    (hf : LinearMap.range f = U) (hg : LinearMap.range g = V)
    (x : A) (y : V) (hy : g x = y.val) :
    f x = ((commonKernelSubmoduleEquiv f g U V h hf hg).symm y : B) := by
  have hx : f x ∈ U := hf.le ⟨x, rfl⟩
  have he : commonKernelSubmoduleEquiv f g U V h hf hg ⟨f x, hx⟩ = y :=
    Subtype.ext ((commonKernelSubmoduleEquiv_apply f g U V h hf hg x hx).trans hy)
  have hi := congrArg (commonKernelSubmoduleEquiv f g U V h hf hg).symm he
  rw [LinearEquiv.symm_apply_apply] at hi
  exact congrArg Subtype.val hi

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerPeriodicTorusLift
namespace OAI

section

namespace Erdos3

variable {ι : Type*}

noncomputable def integerPeriodicTorusLift (F : (ι → ℝ) → ℂ) (x : UnitAddTorus ι) : ℂ :=
  F (fun i => (AddCircle.equivIoc 1 0 (x i)).val)

theorem integerPeriodicTorusLift_coe (F : (ι → ℝ) → ℂ)
    (hF : ∀ (x : ι → ℝ) (n : ι → ℤ), F (fun i => x i + (n i : ℝ)) = F x)
    (x : ι → ℝ) : integerPeriodicTorusLift F (fun i => (x i : UnitAddCircle)) = F x := by
  classical
  let y : ι → ℝ := fun i => (AddCircle.equivIoc 1 0 (x i : UnitAddCircle)).val
  have hzero (i : ι) : (((y i - x i : ℝ) : UnitAddCircle)) = 0 := by
    simp [y]
  choose n hn using fun i => (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp (hzero i)
  have hy : y = fun i => x i + (n i : ℝ) := by
    funext i
    have hi : (n i : ℝ) = y i - x i := by simpa only [zsmul_eq_mul, mul_one] using hn i
    linarith
  change F y = F x
  rw [hy, hF]

theorem continuous_integerPeriodicTorusLift (F : (ι → ℝ) → ℂ) (hc : Continuous F)
    (hF : ∀ (x : ι → ℝ) (n : ι → ℤ), F (fun i => x i + (n i : ℝ)) = F x) :
    Continuous (integerPeriodicTorusLift F) := by
  have hq : IsOpenQuotientMap (fun x : ι → ℝ => fun i => (x i : UnitAddCircle)) :=
    IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  apply hq.isQuotientMap.continuous_iff.mpr
  convert hc using 1
  funext x
  exact integerPeriodicTorusLift_coe F hF x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.DivisibleCharacterExtension
namespace OAI

section

namespace Erdos3

theorem exists_divisible_character_extension
    {A G Q : Type} [AddCommGroup A] [AddCommGroup G] [AddCommGroup Q]
    [DivisibleBy Q ℤ] (η : A →+ G) (φ : A →+ Q)
    (hker : ∀ x, η x = 0 → φ x = 0) :
    ∃ θ : G →+ Q, ∀ x, θ (η x) = φ x := by
  let : Module.Injective ℤ Q := (Module.Baer.of_divisible Q).injective
  let f := (QuotientAddGroup.kerLift η).toIntLinearMap
  let g := (QuotientAddGroup.lift η.ker φ (fun x hx => hker x hx)).toIntLinearMap
  obtain ⟨θ, hθ⟩ := Module.Injective.out f (QuotientAddGroup.kerLift_injective η) g
  exact ⟨θ.toAddMonoidHom, fun x => hθ (QuotientAddGroup.mk x)⟩

theorem exists_cyclic_real_character_lift
    {A : Type} [AddCommGroup A] {N : ℕ} [NeZero N]
    (η : A →+ ZMod N) (φ : A →+ AddCircle (1 : ℝ))
    (hker : ∀ x, η x = 0 → φ x = 0) :
    ∃ t ∈ Set.Ico (0 : ℝ) 1,
      (∃ k : ℤ, (N : ℝ) * t = (k : ℝ)) ∧
      ∀ (x : A) (n : ℤ), η x = (n : ZMod N) →
        φ x = (((n : ℝ) * t : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨χ, hχ⟩ := exists_divisible_character_extension η φ hker
  obtain ⟨t, ht, he⟩ := AddCircle.eq_coe_Ico (χ 1)
  have hN : N • χ 1 = 0 := by rw [← map_nsmul]; simp [nsmul_eq_mul]
  refine ⟨t, ht, ?_, ?_⟩
  · rw [← he, ← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at hN
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by simpa [nsmul_eq_mul] using hk.symm⟩
  · intro x n hn
    rw [← hχ x, hn]
    have hcast : (n : ZMod N) = n • (1 : ZMod N) := by simp [zsmul_eq_mul]
    rw [hcast, map_zsmul, ← he, ← AddCircle.coe_zsmul]
    congr 1
    simp [zsmul_eq_mul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisImageSection
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem basis_projection_injective_of_minor {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] {k : ℕ}
    (b : Module.Basis (Fin k) K E) (P : E →ₗ[K] (ι → K)) (p : Fin k → ι)
    (hdet : (Matrix.of (fun i j => P (b j) (p i))).det ≠ 0) : Function.Injective P := by
  let B := Matrix.of (fun i j => P (b j) (p i))
  have hB : IsUnit B := B.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet)
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  have hxP : P x = 0 := hx
  have hcoord : B *ᵥ (fun j => b.repr x j) = 0 := by
    funext i
    have hs := congrArg (fun y => P y (p i)) (b.sum_repr x)
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
    change (∑ j, B i j * b.repr x j) = 0
    calc
      _ = P x (p i) := by simpa only [B, Matrix.of_apply, mul_comm] using hs
      _ = 0 := congrFun hxP (p i)
  have hz : (fun j => b.repr x j) = 0 := Matrix.mulVec_injective_of_isUnit hB
    (hcoord.trans (Matrix.mulVec_zero B).symm)
  apply b.repr.injective
  simp only [map_zero]
  exact Finsupp.ext (fun j => congrFun hz j)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem basis_coordinate_matrix_mulVec {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] {k : ℕ}
    (b : Module.Basis (Fin k) K E) (f : E →ₗ[K] (ι → K)) (x : E) :
    Matrix.of (fun i j => f (b j) i) *ᵥ (fun j => b.repr x j) = f x := by
  funext i
  have hs := congrArg (fun y => f y i) (b.sum_repr x)
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
  simpa only [Matrix.mulVec, dotProduct, Matrix.of_apply, mul_comm] using hs

theorem basis_image_reconstruct_from_minor {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] {k : ℕ}
    (b : Module.Basis (Fin k) K E) (f : E →ₗ[K] (ι → K)) (p : Fin k → ι)
    (hp : (Matrix.of (fun i j => f (b j) (p i))).det ≠ 0) (x : E) :
    let F := Matrix.of (fun i j => f (b j) i)
    (F * (F.submatrix p id)⁻¹) *ᵥ (fun j => f x (p j)) = f x := by
  let F := Matrix.of (fun i j => f (b j) i)
  have hF : F *ᵥ (fun j => b.repr x j) = f x := basis_coordinate_matrix_mulVec b f x
  have hsub : (F.submatrix p id) *ᵥ (fun j => b.repr x j) = fun j => f x (p j) := by
    funext i
    exact congrFun hF (p i)
  have hp' : (F.submatrix p id).det ≠ 0 := hp
  change (F * (F.submatrix p id)⁻¹) *ᵥ (fun j => f x (p j)) = f x
  rw [← hsub, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul (F.submatrix p id) (isUnit_iff_ne_zero.mpr hp'), Matrix.mul_one]
  exact hF

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem exists_normalized_basis_vector {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] {k : ℕ}
    (b : Module.Basis (Fin k) K E) (g : E →ₗ[K] (ι → K))
    (B : Matrix ι (Fin k) K) (hB : ∀ i j, B i j = g (b j) i)
    (N : Matrix (Fin k) (Fin k) K) (j : Fin k) :
    ∃ v : E, g v = (B * N).col j := by
  refine ⟨∑ t, N t j • b t, ?_⟩
  funext i
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ t, N t j * g (b t) i) = ∑ t, B i t * N t j
  apply Finset.sum_congr rfl
  intro t _
  rw [hB, mul_comm]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CircleResiduePartition
namespace OAI

section

namespace Erdos3.CircleFourier

open scoped NNReal

theorem one_le_mul_dist_toAddCircle {q : ℕ} [NeZero q] {j k : ZMod q} (hjk : j ≠ k) :
    1 ≤ (q : ℝ) * dist (ZMod.toAddCircle j) (ZMod.toAddCircle k) := by
  let z := j - k
  have hz : z ≠ 0 := sub_ne_zero.mpr hjk
  have hzval : 0 < z.val := Nat.pos_of_ne_zero (fun h => hz ((ZMod.val_eq_zero z).mp h))
  have hzlt := z.val_lt
  have hmin : 1 ≤ min z.val (q - z.val) := le_min hzval (by omega)
  have hdist : dist (ZMod.toAddCircle j) (ZMod.toAddCircle k) =
      ((min z.val (q - z.val) : ℕ) : ℝ) / q := by
    rw [dist_eq_norm, ← map_sub, ZMod.toAddCircle_apply]
    have hn := AddCircle.norm_div_natCast (p := (1 : ℝ)) (m := z.val) (n := q)
    simpa only [mul_one, one_mul, Nat.mod_eq_of_lt z.val_lt] using hn
  rw [hdist, mul_div_cancel₀ _ (show (q : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne q))]
  exact_mod_cast hmin

noncomputable def residueCutoff {q : ℕ} [NeZero q] (j : ZMod q) (x : Circle) : ℝ :=
  max 0 (1 - (q : ℝ) * dist x (ZMod.toAddCircle j))

theorem residueCutoff_unit_interval {q : ℕ} [NeZero q] (j : ZMod q) (x : Circle) :
    0 ≤ residueCutoff j x ∧ residueCutoff j x ≤ 1 := by
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  linarith [mul_nonneg (Nat.cast_nonneg q) (dist_nonneg (x := x) (y := ZMod.toAddCircle j))]

theorem residueCutoff_lipschitz {q : ℕ} [NeZero q] (j : ZMod q) :
    LipschitzWith (q : ℝ≥0) (residueCutoff j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |max 0 (1 - (q : ℝ) * dist x (ZMod.toAddCircle j)) -
    max 0 (1 - (q : ℝ) * dist y (ZMod.toAddCircle j))| ≤ (q : ℝ) * dist x y
  calc
    _ ≤ |(1 - (q : ℝ) * dist x (ZMod.toAddCircle j)) -
        (1 - (q : ℝ) * dist y (ZMod.toAddCircle j))| := by
      rw [max_comm 0 _, max_comm 0 _]
      exact abs_max_sub_max_le_abs _ _ _
    _ = (q : ℝ) * |dist x (ZMod.toAddCircle j) - dist y (ZMod.toAddCircle j)| := by
      rw [show (1 - (q : ℝ) * dist x (ZMod.toAddCircle j)) -
          (1 - (q : ℝ) * dist y (ZMod.toAddCircle j)) =
          -(q : ℝ) * (dist x (ZMod.toAddCircle j) - dist y (ZMod.toAddCircle j)) by ring,
        abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg q)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (abs_dist_sub_le x y (ZMod.toAddCircle j)) (Nat.cast_nonneg q)

theorem residueCutoff_at_grid {q : ℕ} [NeZero q] (j k : ZMod q) :
    residueCutoff j (ZMod.toAddCircle k) = if k = j then 1 else 0 := by
  classical
  by_cases h : k = j
  · subst k
    simp [residueCutoff]
  · simp only [h, ↓reduceIte]
    exact max_eq_left (by linarith [one_le_mul_dist_toAddCircle h])

end Erdos3.CircleFourier

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinatewiseLipschitz
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem lipschitzWith_of_coordinatewise {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, PseudoMetricSpace (X i)] {Y : Type*} [PseudoMetricSpace Y]
    (f : (∀ i, X i) → Y) (C : ι → ℝ≥0)
    (h : ∀ i x, LipschitzWith (C i) (fun a => f (Function.update x i a))) :
    LipschitzWith (∑ i, C i) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let z (S : Finset ι) : ∀ i, X i := fun i => if i ∈ S then x i else y i
  have hbound (S : Finset ι) : dist (f (z S)) (f y) ≤ ∑ i ∈ S, (C i : ℝ) * dist (x i) (y i) := by
    induction S using Finset.induction_on with
    | empty => simp only [z, Finset.notMem_empty, ite_false, Finset.sum_empty, dist_self, le_refl]
    | @insert i S hi ih =>
      have heq : z (insert i S) = Function.update (z S) i (x i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp only [z, Finset.mem_insert_self, ite_true, Function.update_self]
        · simp only [z, Finset.mem_insert, hji, false_or, Function.update_of_ne hji]
      have hold : z S = Function.update (z S) i (y i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp only [z, hi, ite_false, Function.update_self]
        · rw [Function.update_of_ne hji]
      have hstep : dist (f (z (insert i S))) (f (z S)) ≤ (C i : ℝ) * dist (x i) (y i) := by
        calc
          _ = dist (f (Function.update (z S) i (x i))) (f (Function.update (z S) i (y i))) := by
            rw [heq]
            exact congrArg (fun v => dist (f (Function.update (z S) i (x i))) (f v)) hold
          _ ≤ _ := (h i (z S)).dist_le_mul _ _
      have htri : dist (f (z (insert i S))) (f y) ≤
          (C i : ℝ) * dist (x i) (y i) + ∑ j ∈ S, (C j : ℝ) * dist (x j) (y j) :=
        (dist_triangle _ _ _).trans (add_le_add hstep ih)
      simpa only [Finset.sum_insert hi] using htri
  have htotal : dist (f x) (f y) ≤ ∑ i, (C i : ℝ) * dist (x i) (y i) := by
    simpa only [z, Finset.mem_univ, ite_true] using hbound Finset.univ
  calc
    _ ≤ ∑ i, (C i : ℝ) * dist (x i) (y i) := htotal
    _ ≤ ∑ i, (C i : ℝ) * dist x y := Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (C i).coe_nonneg)
    _ = ((∑ i, C i : ℝ≥0) : ℝ) * dist x y := by rw [NNReal.coe_sum, Finset.sum_mul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.GramBasisChange
namespace OAI

section

namespace Erdos3

open Module

theorem gram_det_basis_change {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Basis ι ℝ E) (v : ι → E) :
    (Matrix.gram ℝ v).det = (b.det v) ^ 2 * (Matrix.gram ℝ b).det := by
  classical
  let o : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex
    (Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using finrank_eq_card_basis b))
  have hd (w : ι → E) : (Matrix.gram ℝ w).det = (o.toBasis.toMatrix w).det ^ 2 := by
    rw [Matrix.gram_eq_conjTranspose_mul o w, Matrix.det_mul, Matrix.det_conjTranspose]
    have he : o.toBasis.toMatrix w = Matrix.of (fun i j => o.repr (w j) i) := by
      ext i j
      rfl
    rw [he]
    simp [pow_two]
  rw [hd v, hd b, b.det_apply, ← o.toBasis.toMatrix_mul_toMatrix b v, Matrix.det_mul]
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientTranslatePartition
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem additiveFundamentalDomain_op {E : Type*} [AddCommGroup E] [MeasurableSpace E]
    (Γ : AddSubgroup E) {F : Set E} {μ : Measure E}
    (hF : IsAddFundamentalDomain Γ F μ) : IsAddFundamentalDomain Γ.op F μ := by
  have h := hF.preimage_of_equiv (MeasurePreserving.id μ).quasiMeasurePreserving
    (Γ.equivOp.bijective) (fun g x => ?_)
  · exact h
  · change x + (g : E) = (g : E) + x
    exact add_comm _ _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set
open scoped Pointwise

theorem quotient_preimage_image_vadd {E : Type*} [AddCommGroup E]
    (Γ : AddSubgroup E) (A : Set E) :
    (QuotientAddGroup.mk : E → E ⧸ Γ) ⁻¹'
      ((QuotientAddGroup.mk : E → E ⧸ Γ) '' A) = ⋃ g : Γ, g +ᵥ A := by
  rw [QuotientAddGroup.preimage_image_mk_eq_iUnion_image]
  congr 1
  funext g
  change (fun x : E => x + g.val) '' A = (fun x : E => g.val + x) '' A
  simp only [add_comm]

theorem quotient_injective_translates_disjoint {E : Type*} [AddCommGroup E]
    (Γ : AddSubgroup E) {A : Set E}
    (hA : InjOn (QuotientAddGroup.mk : E → E ⧸ Γ) A) :
    Pairwise (fun g h : Γ => Disjoint (g +ᵥ A) (h +ᵥ A)) := by
  intro g h hgh
  apply Set.disjoint_left.mpr
  rintro x ⟨a, ha, hga⟩ ⟨b, hb, hhb⟩
  change g.val + a = x at hga
  change h.val + b = x at hhb
  have hg0 : QuotientAddGroup.mk' Γ g.val = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr g.property
  have hh0 : QuotientAddGroup.mk' Γ h.val = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr h.property
  have hab : a = b := hA ha hb (by
    have he := congrArg (QuotientAddGroup.mk' Γ) (hga.trans hhb.symm)
    simpa only [map_add, hg0, hh0, zero_add, QuotientAddGroup.mk'_apply] using he)
  subst b
  exact hgh (Subtype.ext (add_right_cancel (hga.trans hhb.symm)))

theorem quotient_injective_lift_measure {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (Γ : AddSubgroup E) [Countable Γ]
    (ν : Measure E) [ν.IsAddLeftInvariant]
    {F A : Set E} (hF : IsAddFundamentalDomain Γ F ν) (hFm : MeasurableSet F)
    (hAm : MeasurableSet A) (hA : InjOn (QuotientAddGroup.mk : E → E ⧸ Γ) A) :
    ν (((QuotientAddGroup.mk : E → E ⧸ Γ) ⁻¹'
      ((QuotientAddGroup.mk : E → E ⧸ Γ) '' A)) ∩ F) = ν A := by
  rw [quotient_preimage_image_vadd, Set.iUnion_inter]
  rw [measure_iUnion]
  · exact (hF.measure_eq_tsum A).symm
  · intro g h hgh
    exact (quotient_injective_translates_disjoint Γ hA hgh).mono inter_subset_left inter_subset_left
  · intro g
    exact (hAm.const_vadd g).inter hFm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.OrthogonalBasisChart
namespace OAI

section

namespace Erdos3

open Module

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def orthogonalBasisCoordinates (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ) :
    E ≃ₗ[ℝ] W × (Fin n → ℝ) where
  toFun x := (W.orthogonalProjectionOnto x, b.equivFun (Wᗮ.orthogonalProjectionOnto x))
  invFun p := p.1.val + (b.equivFun.symm p.2).val
  left_inv x := by
    change W.starProjection x + (b.equivFun.symm (b.equivFun (Wᗮ.orthogonalProjectionOnto x))).val = x
    rw [LinearEquiv.symm_apply_apply]
    exact W.starProjection_add_starProjection_orthogonal x
  right_inv p := by
    apply Prod.ext
    · change W.orthogonalProjectionOnto (p.1.val + (b.equivFun.symm p.2).val) = p.1
      rw [map_add, W.orthogonalProjectionOnto_apply_of_mem_orthogonal
        (b.equivFun.symm p.2).property, add_zero]
      apply Subtype.ext
      exact W.starProjection_eq_self_iff.mpr p.1.property
    · change b.equivFun (Wᗮ.orthogonalProjectionOnto (p.1.val + (b.equivFun.symm p.2).val)) = p.2
      rw [map_add, W.orthogonalProjectionOnto_orthogonal_apply_eq_zero p.1.property, zero_add]
      have he : Wᗮ.orthogonalProjectionOnto (b.equivFun.symm p.2).val = b.equivFun.symm p.2 := by
        apply Subtype.ext
        exact Wᗮ.starProjection_eq_self_iff.mpr (b.equivFun.symm p.2).property
      rw [he, LinearEquiv.apply_symm_apply]
  map_add' x y := by
    apply Prod.ext <;> simp
  map_smul' a x := by
    apply Prod.ext <;> simp

noncomputable def orthogonalBasisChart (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ) :
    E ≃L[ℝ] W × (Fin n → ℝ) := (orthogonalBasisCoordinates W b).toContinuousLinearEquiv

theorem orthogonalBasisChart_apply (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ) (x : E) :
    orthogonalBasisChart W b x =
      (W.orthogonalProjectionOnto x, b.equivFun (Wᗮ.orthogonalProjectionOnto x)) := rfl

theorem orthogonalBasisChart_symm_apply (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ)
    (p : W × (Fin n → ℝ)) :
    (orthogonalBasisChart W b).symm p = p.1.val + (b.equivFun.symm p.2).val := rfl

theorem orthogonalBasisChart_norm_le (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖b.equivFun x‖ ≤ C * ‖x‖) (x : E) :
    ‖orthogonalBasisChart W b x‖ ≤ (1 + C) * ‖x‖ := by
  rw [orthogonalBasisChart_apply, Prod.norm_def]
  apply max_le
  · have h := W.norm_orthogonalProjectionOnto_apply_le x
    nlinarith [norm_nonneg x]
  · calc
      _ ≤ C * ‖Wᗮ.orthogonalProjectionOnto x‖ := hb _
      _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_left (Wᗮ.norm_orthogonalProjectionOnto_apply_le x) hC
      _ ≤ _ := by nlinarith [norm_nonneg x]

theorem orthogonalBasisChart_symm_norm_le (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖b.equivFun.symm x‖ ≤ C * ‖x‖)
    (p : W × (Fin n → ℝ)) :
    ‖(orthogonalBasisChart W b).symm p‖ ≤ (1 + C) * ‖p‖ := by
  rw [orthogonalBasisChart_symm_apply]
  calc
    _ ≤ ‖p.1‖ + ‖b.equivFun.symm p.2‖ := norm_add_le _ _
    _ ≤ ‖p.1‖ + C * ‖p.2‖ := by gcongr; exact hb _
    _ ≤ ‖p‖ + C * ‖p‖ := by gcongr; exact norm_fst_le p; exact norm_snd_le p
    _ = _ := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SplitSurjectionBasis
namespace OAI

section

namespace Erdos3

open Module

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module R F]

def splitSurjectionEquiv (q : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : ∀ x, q (s x) = x) : (LinearMap.ker q × F) ≃ₗ[R] E where
  toFun p := p.1.val + s p.2
  invFun x := (⟨x - s (q x), by rw [LinearMap.mem_ker, map_sub, hs, sub_self]⟩, q x)
  left_inv p := by
    refine Prod.ext (Subtype.ext ?_) ?_
    · change p.1.val + s p.2 - s (q (p.1.val + s p.2)) = p.1.val
      rw [map_add, show q p.1.val = 0 from p.1.property, hs, zero_add, add_sub_cancel_right]
    · change q (p.1.val + s p.2) = p.2
      rw [map_add, show q p.1.val = 0 from p.1.property, hs, zero_add]
  right_inv x := sub_add_cancel x (s (q x))
  map_add' x y := by
    change x.1.val + y.1.val + s (x.2 + y.2) = (x.1.val + s x.2) + (y.1.val + s y.2)
    rw [map_add]
    abel
  map_smul' a x := by
    change a • x.1.val + s (a • x.2) = a • (x.1.val + s x.2)
    rw [map_smul, smul_add]

@[simp] theorem splitSurjectionEquiv_apply (q : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : ∀ x, q (s x) = x) (p : LinearMap.ker q × F) :
    splitSurjectionEquiv q s hs p = p.1.val + s p.2 := rfl

theorem exists_basis_of_surjection [Projective R F] {α β : Type*}
    (q : E →ₗ[R] F) (hq : Function.Surjective q)
    (bK : Basis α R (LinearMap.ker q)) (bI : Basis β R F) :
    ∃ b : Basis (α ⊕ β) R E,
      (∀ i, b (Sum.inl i) = (bK i).val) ∧ (∀ j, q (b (Sum.inr j)) = bI j) := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hret : ∀ x, q (s x) = x := fun x => LinearMap.congr_fun hs x
  let b := (bK.prod bI).map (splitSurjectionEquiv q s hret)
  refine ⟨b, ?_, ?_⟩
  · intro i
    simp [b]
  · intro j
    simp [b, hret]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProjectedBasisSpan
namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open Module Submodule
open scoped BigOperators

theorem mem_first_span_of_projection_zero {n : ℕ}
    (b : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ))
    (q : Basis (Fin n) ℝ (Fin n → ℝ))
    (π : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hzero : π (b 0) = 0) (htail : ∀ j, π (b j.succ) = q j)
    {x : Fin (n + 1) → ℝ} (hx : x ∈ span ℤ (Set.range b)) (hπx : π x = 0) :
    x ∈ span ℤ ({b 0} : Set (Fin (n + 1) → ℝ)) := by
  classical
  rw [mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  have hp : ∑ j : Fin n, c j.succ • q j = 0 := by
    rw [map_sum, Fin.sum_univ_succ] at hπx
    simpa only [map_zsmul, hzero, htail, smul_zero, zero_add] using hπx
  have hc : ∀ j : Fin n, c j.succ = 0 :=
    Fintype.linearIndependent_iff.mp (q.linearIndependent.restrict_scalars' ℤ) _ hp
  rw [Fin.sum_univ_succ]
  simp only [hc, zero_smul, Finset.sum_const_zero, add_zero]
  exact smul_mem _ _ (subset_span (Set.mem_singleton _))

theorem span_fin_cons_of_projected_span {n : ℕ}
    (b : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ))
    (q : Basis (Fin n) ℝ (Fin n → ℝ))
    (π : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hzero : π (b 0) = 0) (htail : ∀ j, π (b j.succ) = q j)
    (w : Fin n → Fin (n + 1) → ℝ)
    (hw : ∀ j, w j ∈ span ℤ (Set.range b))
    (hspan : span ℤ (Set.range (fun j => π (w j))) = span ℤ (Set.range q)) :
    span ℤ (Set.range (Fin.cons (b 0) w)) = span ℤ (Set.range b) := by
  classical
  let L := span ℤ (Set.range b)
  let S := span ℤ (Set.range (Fin.cons (b 0) w))
  have hfirst : b 0 ∈ S := subset_span ⟨0, rfl⟩
  have hwm : ∀ j, w j ∈ S := fun j => subset_span ⟨j.succ, rfl⟩
  have hsmall : span ℤ ({b 0} : Set (Fin (n + 1) → ℝ)) ≤ S := by
    exact span_le.mpr (fun x hx => (Set.mem_singleton_iff.mp hx) ▸ hfirst)
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Fin.cases (subset_span (Set.mem_range_self 0)) hw i
  · apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.cases hfirst (fun k => ?_) i
    change b k.succ ∈ S
    have hk : q k ∈ span ℤ (Set.range (fun j => π (w j))) := by
      rw [hspan]
      exact subset_span (Set.mem_range_self k)
    rw [mem_span_range_iff_exists_fun] at hk
    obtain ⟨c, hc⟩ := hk
    let y := ∑ j, c j • w j
    have hyL : y ∈ L := sum_mem (fun j _ => smul_mem _ _ (hw j))
    have hyS : y ∈ S := sum_mem (fun j _ => smul_mem _ _ (hwm j))
    have hdiff : b k.succ - y ∈ L :=
      sub_mem (subset_span (Set.mem_range_self k.succ)) hyL
    have hπdiff : π (b k.succ - y) = 0 := by
      rw [map_sub, htail]
      change q k - π (∑ j, c j • w j) = 0
      rw [map_sum]
      simp only [map_zsmul, hc, sub_self]
    have hm := mem_first_span_of_projection_zero b q π hzero htail hdiff hπdiff
    have hadd := S.add_mem (hsmall hm) hyS
    simpa only [sub_add_cancel] using hadd

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

noncomputable def affineProbabilityProfile (c w x : ℝ) : ℝ :=
  w⁻¹ * smoothProbabilityProfile ((x - c) / w)

theorem affineProbabilityProfile_nonneg (c : ℝ) {w : ℝ} (hw : 0 < w) (x : ℝ) :
    0 ≤ affineProbabilityProfile c w x :=
  mul_nonneg (inv_nonneg.mpr hw.le) (smoothProbabilityProfile_range _).1

theorem affineProbabilityProfile_le (c : ℝ) {w : ℝ} (hw : 0 < w) (x : ℝ) :
    affineProbabilityProfile c w x ≤ w⁻¹ := by
  exact (mul_le_mul_of_nonneg_left (smoothProbabilityProfile_range _).2
    (inv_nonneg.mpr hw.le)).trans_eq (mul_one _)

theorem affineProbabilityProfile_contDiff (c w : ℝ) :
    ContDiff ℝ ∞ (affineProbabilityProfile c w) := by
  change ContDiff ℝ ∞ (fun x => w⁻¹ * smoothProbabilityProfile ((x-c)/w))
  exact contDiff_const.mul
    (smoothProbabilityProfile_contDiff.comp ((contDiff_id.sub contDiff_const).div_const w))

theorem affineProbabilityProfile_zero (c : ℝ) {w : ℝ} (hw : 0 < w) (x : ℝ)
    (hx : w < |x - c|) : affineProbabilityProfile c w x = 0 := by
  have hnorm : 1 < |(x-c)/w| := by
    rw [abs_div, abs_of_pos hw]
    exact (one_lt_div hw).mpr hx
  rw [affineProbabilityProfile, smoothProbabilityProfile_zero_outside _ hnorm, mul_zero]

theorem affineProbabilityProfile_zero_outside (c : ℝ) {w : ℝ} (hw : 0 < w) (x : ℝ)
    (hx : |c| + w < |x|) : affineProbabilityProfile c w x = 0 := by
  apply affineProbabilityProfile_zero c hw x
  have ht : |x| ≤ |x-c| + |c| := by
    simpa only [sub_add_cancel] using abs_add_le (x-c) c
  linarith

theorem affineProbabilityProfile_compact (c : ℝ) {w : ℝ} (hw : 0 < w) :
    HasCompactSupport (affineProbabilityProfile c w) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) (|c|+w))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  exact le_of_not_gt (fun h => hx (affineProbabilityProfile_zero_outside c hw x h))

theorem affineProbabilityProfile_integrable (c : ℝ) {w : ℝ} (hw : 0 < w) :
    Integrable (affineProbabilityProfile c w) :=
  (affineProbabilityProfile_contDiff c w).continuous.integrable_of_hasCompactSupport
    (affineProbabilityProfile_compact c hw)

theorem affineProbabilityProfile_integral (c : ℝ) {w : ℝ} (hw : 0 < w) :
    (∫ x, affineProbabilityProfile c w x) = 1 := by
  change (∫ x, w⁻¹ * smoothProbabilityProfile ((x-c)/w)) = 1
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun x => smoothProbabilityProfile (x/w)) c,
    Measure.integral_comp_div, smoothProbabilityProfile_integral, smul_eq_mul,
    mul_one, abs_of_pos hw, inv_mul_cancel₀ hw.ne']

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

noncomputable def affineProductProfile {I : Type*} [Fintype I] (c w x : I → ℝ) : ℝ :=
  ∏ i, affineProbabilityProfile (c i) (w i) (x i)

noncomputable def profileWidthFactor {I : Type*} [Fintype I] (w : I → ℝ) : ℝ :=
  ∏ i, (w i)⁻¹

theorem affineProductProfile_eq {I : Type*} [Fintype I] (c w x : I → ℝ) :
    affineProductProfile c w x = profileWidthFactor w *
      smoothProductProfile I (fun i => (x i - c i) / w i) := by
  simp only [affineProductProfile, affineProbabilityProfile, Finset.prod_mul_distrib,
    profileWidthFactor, smoothProductProfile]

theorem profileWidthFactor_pos {I : Type*} [Fintype I] (w : I → ℝ) (hw : ∀ i, 0 < w i) :
    0 < profileWidthFactor w := Finset.prod_pos (fun i _ => inv_pos.mpr (hw i))

theorem affineProductProfile_nonneg {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) (x : I → ℝ) : 0 ≤ affineProductProfile c w x :=
  Finset.prod_nonneg (fun i _ => affineProbabilityProfile_nonneg (c i) (hw i) (x i))

theorem affineProductProfile_norm_le {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) (x : I → ℝ) : ‖affineProductProfile c w x‖ ≤ profileWidthFactor w := by
  rw [Real.norm_eq_abs, abs_of_nonneg (affineProductProfile_nonneg c w hw x)]
  exact Finset.prod_le_prod (fun i _ => affineProbabilityProfile_nonneg (c i) (hw i) (x i))
    (fun i _ => affineProbabilityProfile_le (c i) (hw i) (x i))

theorem affineProductProfile_contDiff {I : Type*} [Fintype I] (c w : I → ℝ) :
    ContDiff ℝ ∞ (affineProductProfile c w) := by
  unfold affineProductProfile
  apply contDiff_prod
  intro i _
  exact (affineProbabilityProfile_contDiff (c i) (w i)).comp
    (ContinuousLinearMap.proj i : (I → ℝ) →L[ℝ] ℝ).contDiff

theorem affineProductProfile_zero_outside {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) {R : ℝ} (hR : 0 ≤ R) (hcw : ∀ i, |c i| + w i ≤ R) :
    ∀ x, R < ‖x‖ → affineProductProfile c w x = 0 := by
  classical
  intro x hx
  by_contra hne
  apply (not_le_of_gt hx)
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  rw [Real.norm_eq_abs]
  by_contra! hi
  exact hne (Finset.prod_eq_zero (Finset.mem_univ i)
    (affineProbabilityProfile_zero_outside (c i) (hw i) (x i) ((hcw i).trans_lt hi)))

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

theorem affineProbabilityProfile_support (c : ℝ) {w : ℝ} (hw : 0 < w) {x : ℝ}
    (hx : affineProbabilityProfile c w x ≠ 0) : |x - c| < 3 * w / 4 := by
  by_contra! h
  have hz : smoothProbabilityProfile ((x-c)/w) = 0 := by
    apply smoothProbabilityProfile_zero
    rw [abs_div, abs_of_pos hw]
    apply (le_div_iff₀ hw).mpr
    linarith
  exact hx (by simp only [affineProbabilityProfile, hz, mul_zero])

theorem realDensityMeasure_ae_of_support {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (P : X → Prop)
    (hP : ∀ x, f x ≠ 0 → P x) : ∀ᵐ x ∂realDensityMeasure μ f, P x := by
  apply (ae_withDensity_iff hf.ennreal_ofReal).mpr
  exact Filter.Eventually.of_forall (fun x hx => hP x (fun hz => hx (by simp [hz])))

noncomputable def affineCoefficientMeasure (c w : ℝ) : Measure ℝ :=
  realDensityMeasure volume (affineProbabilityProfile c w)

theorem affineCoefficientMeasure_probability (c : ℝ) {w : ℝ} (hw : 0 < w) :
    IsProbabilityMeasure (affineCoefficientMeasure c w) :=
  realDensityMeasure_probability volume _ (affineProbabilityProfile_integrable c hw)
    (affineProbabilityProfile_nonneg c hw) (affineProbabilityProfile_integral c hw)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def comparableBoxPartitions {I : Type*} (N H : I → ℕ)
    (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) : ∀ i, FiniteProgressionPartition (N i) :=
  fun i => FiniteProgressionPartition.mergedIntervals (N i) (H i) (hH i) (hHN i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def physicalBoxUnitResidueEquiv (lo : I → ℤ) (N : I → ℕ) :
    translatedIntegerBox lo N ≃ IntegerResidueBox lo (fun i => lo i + N i) (fun _ => 1) (fun _ => 0) where
  toFun x i := ⟨x.val i, Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr ((mem_translatedIntegerBox lo N x.val).mp x.property i), Int.modEq_one⟩⟩
  invFun x := ⟨fun i => (x i).val, (mem_translatedIntegerBox lo N _).mpr
    (fun i => Finset.mem_Ico.mp (Finset.mem_filter.mp (x i).property).1)⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def physicalBoxCell (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (x : translatedIntegerBox lo N) : ∀ i, (P i).Label :=
  boxIntervalResidueCell lo N P (fun _ => 1) (fun _ => 0) (physicalBoxUnitResidueEquiv lo N x)

noncomputable def physicalBoxCellEquiv (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (c : ∀ i, (P i).Label) :
    {x : translatedIntegerBox lo N // physicalBoxCell lo N P x = c} ≃
      IntegerResidueBox (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i))
        (fun _ => 1) (fun _ => 0) := by
  let e : {x : translatedIntegerBox lo N // physicalBoxCell lo N P x = c} ≃
      ↥(partitionCell (boxIntervalResidueCell lo N P (fun _ => 1) (fun _ => 0)) c) :=
    (physicalBoxUnitResidueEquiv lo N).subtypeEquiv (fun x =>
      (mem_partitionCell (boxIntervalResidueCell lo N P (fun _ => 1) (fun _ => 0)) c
        (physicalBoxUnitResidueEquiv lo N x)).symm)
  exact e.trans (boxIntervalResidueCellEquiv lo N P hstep hpos (fun _ => 1) (fun _ => 0) c)

omit [Fintype I] [DecidableEq I] in
theorem physicalBoxCell_nonempty (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (c : ∀ i, (P i).Label) :
    Nonempty (IntegerResidueBox (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i))
      (fun _ => 1) (fun _ => 0)) := by
  refine ⟨fun i => ⟨intervalCellLower (lo i) (P i) (c i), Finset.mem_filter.mpr ⟨?_, Int.modEq_one⟩⟩⟩
  exact Finset.mem_Ico.mpr ⟨le_rfl, lt_add_of_pos_right _ (by exact_mod_cast hpos i (c i))⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductSectionSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [DecidableEq I] {X : I → Type*}

def productCoordinateMix (S : Finset I) (x y : ∀ i, X i) : ∀ i, X i :=
  fun i => if i ∈ S then x i else y i

theorem productCoordinateMix_swap (S : Finset I) (x y : ∀ i, X i) :
    productCoordinateMix S (productCoordinateMix S x y) (productCoordinateMix S y x) = x := by
  funext i
  by_cases hi : i ∈ S <;> simp [productCoordinateMix, hi]

def productCoordinateSwap (S : Finset I) : ((∀ i, X i) × (∀ i, X i)) ≃
    ((∀ i, X i) × (∀ i, X i)) where
  toFun p := (productCoordinateMix S p.1 p.2, productCoordinateMix S p.2 p.1)
  invFun p := (productCoordinateMix S p.1 p.2, productCoordinateMix S p.2 p.1)
  left_inv p := by simp [productCoordinateMix_swap]
  right_inv p := by simp [productCoordinateMix_swap]

variable [Fintype I] [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ProbabilityIntegralApproximation
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem probability_integral_approximation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f g : X → ℂ)
    (hf : Integrable f μ) (hg : Integrable g μ) {η : ℝ}
    (he : ∀ x, ‖f x - g x‖ ≤ η) :
    ‖(∫ x, f x ∂μ) - ∫ x, g x ∂μ‖ ≤ η := by
  rw [← integral_sub hf hg]
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (ae_of_all μ he)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxCoordinateEquiv
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

def coordinateReindexedSides (e : X ≃ Y) (N : X → ℕ) : Y → ℕ :=
  fun y => N (e.symm y)

def coordinateReindexedFunction (e : X ≃ Y) (f : (X → ℤ) → ℝ) : (Y → ℤ) → ℝ :=
  fun y => f (fun x => y (e x))

variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem coordinateReindexedSides_mem_integerBox (e : X ≃ Y) (N : X → ℕ) (y : Y → ℤ) :
    y ∈ integerBox (coordinateReindexedSides e N) ↔
      (fun x => y (e x)) ∈ integerBox N := by
  simp only [mem_integerBox, coordinateReindexedSides]
  constructor
  · intro hy x
    simpa only [e.symm_apply_apply] using hy (e x)
  · intro hy j
    simpa only [e.apply_symm_apply] using hy (e.symm j)

end Erdos3

end

section

namespace Erdos3

variable {X Y : Type*}

def integerPointCoordinateEquiv (e : X ≃ Y) : (X → ℤ) ≃ (Y → ℤ) where
  toFun x y := x (e.symm y)
  invFun y x := y (e x)
  left_inv x := by funext i; simp only [e.symm_apply_apply]
  right_inv y := by funext j; simp only [e.apply_symm_apply]

@[simp] theorem integerPointCoordinateEquiv_apply (e : X ≃ Y) (x : X → ℤ) (y : Y) :
    integerPointCoordinateEquiv e x y = x (e.symm y) := rfl

@[simp] theorem integerPointCoordinateEquiv_symm_apply (e : X ≃ Y) (y : Y → ℤ) (x : X) :
    (integerPointCoordinateEquiv e).symm y x = y (e x) := rfl

@[simp] theorem integerPointCoordinateEquiv_symm (e : X ≃ Y) :
    integerPointCoordinateEquiv e.symm = (integerPointCoordinateEquiv e).symm := rfl

variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

@[simp] theorem integerPointCoordinateEquiv_mem_integerBox (e : X ≃ Y)
    (N : X → ℕ) (x : X → ℤ) :
    integerPointCoordinateEquiv e x ∈ integerBox (coordinateReindexedSides e N) ↔
      x ∈ integerBox N := by
  rw [coordinateReindexedSides_mem_integerBox]
  simp only [integerPointCoordinateEquiv_apply, e.symm_apply_apply]

def integerBoxCoordinateEquiv (e : X ≃ Y) (N : X → ℕ) :
    integerBox N ≃ integerBox (coordinateReindexedSides e N) where
  toFun x := ⟨integerPointCoordinateEquiv e x.val,
    (integerPointCoordinateEquiv_mem_integerBox e N x.val).mpr x.property⟩
  invFun y := ⟨(integerPointCoordinateEquiv e).symm y.val,
    (coordinateReindexedSides_mem_integerBox e N y.val).mp y.property⟩
  left_inv x := by apply Subtype.ext; exact (integerPointCoordinateEquiv e).left_inv x.val
  right_inv y := by apply Subtype.ext; exact (integerPointCoordinateEquiv e).right_inv y.val

@[simp] theorem integerBoxCoordinateEquiv_val (e : X ≃ Y) (N : X → ℕ)
    (x : integerBox N) :
    (integerBoxCoordinateEquiv e N x).val = integerPointCoordinateEquiv e x.val := rfl

@[simp] theorem integerBoxCoordinateEquiv_symm_val (e : X ≃ Y) (N : X → ℕ)
    (y : integerBox (coordinateReindexedSides e N)) :
    ((integerBoxCoordinateEquiv e N).symm y).val =
      (integerPointCoordinateEquiv e).symm y.val := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.OptionProductMetric
namespace OAI

section

namespace Erdos3

theorem piOptionEquivProd_isometry {ι : Type*} [Fintype ι] {X : Option ι → Type*}
    [∀ i, PseudoMetricSpace (X i)] :
    Isometry (Equiv.piOptionEquivProd : (∀ i, X i) → X none × (∀ i, X (some i))) := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (x none, fun i => x (some i)) (y none, fun i => y (some i)) = dist x y
  rw [Prod.dist_eq]
  apply le_antisymm
  · apply max_le (dist_le_pi_dist x y none)
    exact (dist_pi_le_iff dist_nonneg).mpr (fun i => dist_le_pi_dist x y (some i))
  · apply (dist_pi_le_iff (le_trans dist_nonneg (le_max_left _ _))).mpr
    intro i
    cases i with
    | none => exact le_max_left _ _
    | some i => exact (dist_le_pi_dist (fun i => x (some i)) (fun i => y (some i)) i).trans (le_max_right _ _)

noncomputable def optionPiIsometryEquiv {ι : Type*} [Fintype ι] {X : Option ι → Type*}
    [∀ i, PseudoMetricSpace (X i)] : (∀ i, X i) ≃ᵢ X none × (∀ i, X (some i)) where
  toEquiv := Equiv.piOptionEquivProd
  isometry_toFun := piOptionEquivProd_isometry

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularProductivityPrecision
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def positiveProjectionAccuracy (p : ℝ) : ℝ := Real.exp (-(2 * p + 4))

end Erdos3

end

section

namespace Erdos3

theorem productivity_exp_eight : (256 : ℝ) ≤ Real.exp 8 := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h 8
  norm_num [← Real.exp_nat_mul] at hp ⊢
  exact hp

theorem preparedModularProductivity_precision {Pprod Pphysical gainLog gain : ℝ}
    (d : ℕ) (hg : 0 ≤ gainLog)
    (hprod : gainLog + 8 ≤ Pprod)
    (hphysical : gainLog + (d : ℝ) + 8 ≤ Pphysical)
    (hgain : Real.exp (-gainLog) ≤ gain) :
    Real.exp (-Pprod) ≤ gain / 16 ∧
      12 * positiveProjectionAccuracy Pprod +
        2 * (d : ℝ) * Real.exp (-Pphysical) ≤ gain / 8 := by
  have he : 0 < Real.exp (-gainLog) := Real.exp_pos _
  have hshift : Real.exp (-(gainLog + 8)) ≤ Real.exp (-gainLog) / 256 := by
    rw [neg_add, Real.exp_add, Real.exp_neg (8 : ℝ), ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left he.le (by norm_num) productivity_exp_eight
  have hprodExp : Real.exp (-Pprod) ≤ Real.exp (-gainLog) / 256 :=
    (Real.exp_le_exp.mpr (neg_le_neg hprod)).trans hshift
  have haccuracy : positiveProjectionAccuracy Pprod ≤ Real.exp (-Pprod) := by
    apply Real.exp_le_exp.mpr
    linarith only [hg, hprod]
  have hd : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  have hspatial : (d : ℝ) * Real.exp (-Pphysical) ≤ Real.exp (-gainLog) / 256 := by
    calc
      _ ≤ Real.exp d * Real.exp (-(gainLog + (d : ℝ) + 8)) :=
        mul_le_mul hd (Real.exp_le_exp.mpr (neg_le_neg hphysical))
          (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (-(gainLog + 8)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hshift
  constructor
  · linarith
  · linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RoundingRecoveryScale
namespace OAI

section

namespace Erdos3

theorem exists_rounding_modulus (l : ℕ) (hl : 0 < l) {ε : ℝ}
    (hε : 0 < ε) (hsmall : 2 * (l : ℝ) * ε ≤ 1) :
    ∃ M : ℕ, 0 < M ∧ 1 / (2 * (l : ℝ) * ε) ≤ (M : ℝ) ∧
      (M : ℝ) * l * ε ≤ 1 := by
  let u : ℝ := (l : ℝ) * ε
  have hu : 0 < u := mul_pos (by exact_mod_cast hl) hε
  have hu2 : 2 * u ≤ 1 := by simpa only [u, mul_assoc] using hsmall
  have hx : 2 ≤ 1 / u := (le_div_iff₀ hu).mpr hu2
  let M := ⌊1 / u⌋₊
  have hM : 0 < M := Nat.floor_pos.mpr (by linarith)
  have hfloor : (M : ℝ) ≤ 1 / u := Nat.floor_le (by positivity)
  have hlt : 1 / u < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨M, hM, ?_, ?_⟩
  · have heq : 1 / (2 * (l : ℝ) * ε) = (1 / u) / 2 := by
      dsimp only [u]
      ring
    rw [heq]
    linarith
  · have h := (le_div_iff₀ hu).mp hfloor
    simpa only [u, mul_assoc] using h

end Erdos3

end

section

namespace Erdos3

theorem rounding_recovery_error_le (M l : ℕ) [NeZero M] (hl : 0 < l)
    {ε : ℝ} (hε : 0 < ε) (hM : 1 / (2 * (l : ℝ) * ε) ≤ (M : ℝ)) :
    1 / ((M : ℝ) * l) ≤ 2 * ε := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hMR : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hmul := (div_le_iff₀ (by positivity : 0 < 2 * (l : ℝ) * ε)).mp hM
  apply (div_le_iff₀ (mul_pos hMR hlR)).mpr
  nlinarith

theorem exists_rounding_modulus_with_recovery (l : ℕ) (hl : 0 < l) {ε : ℝ}
    (hε : 0 < ε) (hsmall : 2 * (l : ℝ) * ε ≤ 1) :
    ∃ M : ℕ, 0 < M ∧ (M : ℝ) * l * ε ≤ 1 ∧ 1 / ((M : ℝ) * l) ≤ 2 * ε := by
  obtain ⟨M, hM, hlower, hupper⟩ := exists_rounding_modulus l hl hε hsmall
  let _ : NeZero M := ⟨hM.ne'⟩
  exact ⟨M, hM, hupper, rounding_recovery_error_le M l hl hε hlower⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TriangularCorrectionRows
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def triangularCorrectionSolutions {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (B : ℝ) (q : ℕ) :
    Set ((Fin n → ℝ) × (Fin n → ℚ)) :=
  {sr | (∀ i, |sr.1 i| ≤ B) ∧
    (∀ i, ∃ z : ℤ, sr.2 i = (z : ℚ) / q) ∧
    ∀ i, c i = ∑ j, A i j * sr.1 j + (sr.2 i : ℝ)}

theorem triangularCorrectionSolutions_prefix {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {c : Fin (n + 1) → ℝ} {B : ℝ} {q : ℕ}
    {sr : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℚ)}
    (htri : ∀ i j, i < j → A i j = 0)
    (hsr : sr ∈ triangularCorrectionSolutions A c B q) :
    ((fun i : Fin n => sr.1 i.castSucc), (fun i : Fin n => sr.2 i.castSucc)) ∈
      triangularCorrectionSolutions (fun i j => A i.castSucc j.castSucc)
        (fun i => c i.castSucc) B q := by
  refine ⟨fun i => hsr.1 i.castSucc, fun i => hsr.2.1 i.castSucc, ?_⟩
  intro i
  have hi := hsr.2.2 i.castSucc
  rw [Fin.sum_univ_castSucc] at hi
  simpa only [htri i.castSucc (Fin.last n) i.castSucc_lt_last, zero_mul, add_zero]
    using hi

theorem triangularCorrectionSolutions_last_eq {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {c : Fin (n + 1) → ℝ} {B : ℝ} {q : ℕ}
    {sr : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℚ)}
    (hsr : sr ∈ triangularCorrectionSolutions A c B q)
    (hdiag : A (Fin.last n) (Fin.last n) ≠ 0) :
    sr.1 (Fin.last n) =
      (c (Fin.last n) - ∑ j : Fin n, A (Fin.last n) j.castSucc * sr.1 j.castSucc -
        (sr.2 (Fin.last n) : ℝ)) / A (Fin.last n) (Fin.last n) := by
  apply (eq_div_iff hdiag).2
  have hi := hsr.2.2 (Fin.last n)
  rw [Fin.sum_univ_castSucc] at hi
  linarith

theorem triangularCorrectionSolutions_last_window {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {c : Fin (n + 1) → ℝ} {B : ℝ} {q : ℕ}
    {sr : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℚ)}
    (hsr : sr ∈ triangularCorrectionSolutions A c B q)
    (_hB : 0 ≤ B) (hdiag : |A (Fin.last n) (Fin.last n)| ≤ 1) :
    |(sr.2 (Fin.last n) : ℝ) -
      (c (Fin.last n) - ∑ j : Fin n, A (Fin.last n) j.castSucc * sr.1 j.castSucc)| ≤ B := by
  have hi := hsr.2.2 (Fin.last n)
  rw [Fin.sum_univ_castSucc] at hi
  have heq : (sr.2 (Fin.last n) : ℝ) -
      (c (Fin.last n) - ∑ j : Fin n, A (Fin.last n) j.castSucc * sr.1 j.castSucc) =
      -(A (Fin.last n) (Fin.last n) * sr.1 (Fin.last n)) := by linarith
  rw [heq, abs_neg, abs_mul]
  calc
    _ ≤ 1 * |sr.1 (Fin.last n)| :=
      mul_le_mul_of_nonneg_right hdiag (abs_nonneg _)
    _ ≤ B := by simpa only [one_mul] using hsr.1 (Fin.last n)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformParameterNet
namespace OAI

section

namespace Erdos3

theorem exists_uniform_parameter_net {J Ω : Type*} [Fintype J] [Nonempty Ω]
    (f : Ω → J → ℝ) {B : ℝ} (hB : 0 < B) (hf : ∀ x j, |f x j| ≤ B)
    {N : ℕ} (hN : 0 < N) :
    ∃ (code : Ω → J → Fin (N + 1)) (rep : (J → Fin (N + 1)) → Ω),
      ∀ x, dist (f x) (f (rep (code x))) ≤ 4 * B / N := by
  classical
  choose code hcode using fun x => exists_uniformBoxGrid_approx hB hN (f x) (hf x)
  let rep : (J → Fin (N + 1)) → Ω := fun i =>
    if h : ∃ x, code x = i then h.choose else Classical.choice inferInstance
  have hrep (x : Ω) : code (rep (code x)) = code x := by
    have h : ∃ y, code y = code x := ⟨x, rfl⟩
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨code, rep, fun x => ?_⟩
  calc
    dist (f x) (f (rep (code x))) ≤
        dist (f x) (uniformBoxGrid B N (code x)) +
          dist (uniformBoxGrid B N (code x)) (f (rep (code x))) := dist_triangle _ _ _
    _ ≤ 2 * B / N + 2 * B / N := by
      apply add_le_add (hcode x)
      have hr := hcode (rep (code x))
      rw [hrep x] at hr
      exact (dist_comm _ _).trans_le hr
    _ = _ := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedLinearBounds
namespace OAI

section

namespace Erdos3

open Module

theorem weighted_linear_bound_of_unit {E F ι κ : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (e : Basis ι ℝ E) (f : Basis κ ℝ F) (W : ι → ℝ) (V : κ → ℝ)
    (Φ : E →ₗ[ℝ] F) (C : ℝ)
    (hΦ : ∀ x, (∀ i, |e.repr x i| ≤ 1 / W i) → ∀ j, |f.repr (Φ x) j| ≤ C / V j)
    {M : ℝ} (hM : 0 ≤ M) (x : E) (hx : ∀ i, |e.repr x i| ≤ M / W i) :
    ∀ j, |f.repr (Φ x) j| ≤ C * M / V j := by
  by_cases hzero : M = 0
  · have hxi : x = 0 := by
      apply e.repr.injective
      ext i
      have hi : |e.repr x i| ≤ 0 := by simpa only [hzero, zero_div] using hx i
      simpa only [map_zero, Finsupp.zero_apply] using (abs_nonpos_iff.mp hi)
    intro j
    simp only [hxi, map_zero, Finsupp.zero_apply, abs_zero, hzero, mul_zero, zero_div, le_refl]
  · have hpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
    let y : E := M⁻¹ • x
    have hy : ∀ i, |e.repr y i| ≤ 1 / W i := by
      intro i
      change |e.repr (M⁻¹ • x) i| ≤ _
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
      calc
        _ ≤ M⁻¹ * (M / W i) := mul_le_mul_of_nonneg_left (hx i) (inv_pos.mpr hpos).le
        _ = _ := by field_simp
    have hxy : x = M • y := by simp only [y, smul_smul, mul_inv_cancel₀ hzero, one_smul]
    intro j
    rw [hxy, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hpos]
    calc
      _ ≤ M * (C / V j) := mul_le_mul_of_nonneg_left (hΦ y hy j) hM
      _ = _ := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteSumCoordinate
namespace OAI

section

namespace Erdos3

variable {σ : Type*} [DecidableEq σ]

def coordinateAdditionInputs (i : σ) (x : Option σ → ℤ) : Fin 3 → σ → ℤ :=
  ![Function.update (fun j => x (some j)) i (x (some i) + x none),
    fun j => x (some j), Function.update (fun j => x (some j)) i (x none)]

@[simp] theorem coordinateAdditionInputs_sum (i : σ) (x : Option σ → ℤ) :
    coordinateAdditionInputs i x 0 =
      Function.update (fun j => x (some j)) i (x (some i) + x none) := rfl

@[simp] theorem coordinateAdditionInputs_left (i : σ) (x : Option σ → ℤ) :
    coordinateAdditionInputs i x 1 = (fun j => x (some j)) := rfl

@[simp] theorem coordinateAdditionInputs_right (i : σ) (x : Option σ → ℤ) :
    coordinateAdditionInputs i x 2 = Function.update (fun j => x (some j)) i (x none) := rfl

noncomputable def coordinateAdditionProduct {I : Type*} (f : I → (σ → ℤ) → ℂ)
    (a : Fin 3 → I) (i : σ) (x : Option σ → ℤ) : ℂ :=
  f (a 0) (coordinateAdditionInputs i x 0) * star (f (a 1) (coordinateAdditionInputs i x 1)) *
    star (f (a 2) (coordinateAdditionInputs i x 2))

end Erdos3

end

section

namespace Erdos3

variable {σ : Type*} [DecidableEq σ]

def coordinateConstantInput (i : σ) (h n : ℤ) : σ → ℤ :=
  Function.update (fun _ => n) i h

def coordinatePairInput (i : σ) (a b n : ℤ) : Option σ → ℤ
  | none => b
  | some j => coordinateConstantInput i a n j

theorem coordinatePairInput_sum (i : σ) (a b n : ℤ) :
    coordinateAdditionInputs i (coordinatePairInput i a b n) 0 =
      coordinateConstantInput i (a + b) n := by
  simp [coordinateAdditionInputs, coordinatePairInput, coordinateConstantInput]

theorem coordinatePairInput_left (i : σ) (a b n : ℤ) :
    coordinateAdditionInputs i (coordinatePairInput i a b n) 1 = coordinateConstantInput i a n := rfl

theorem coordinatePairInput_right (i : σ) (a b n : ℤ) :
    coordinateAdditionInputs i (coordinatePairInput i a b n) 2 = coordinateConstantInput i b n := by
  simp [coordinateAdditionInputs, coordinatePairInput, coordinateConstantInput]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ] {n : ℕ}

def finiteSumCoordinateInput (i : σ) (x : (σ ⊕ Fin n) → ℤ) : σ → ℤ :=
  Function.update (fun j => x (Sum.inl j)) i (∑ a : Fin n, x (Sum.inr a))

def finiteTermCoordinateInput (i : σ) (a : Fin n) (x : (σ ⊕ Fin n) → ℤ) : σ → ℤ :=
  Function.update (fun j => x (Sum.inl j)) i (x (Sum.inr a))

def finiteTermCoordinateHom (i : σ) (a : Fin n) (j : σ) : (((σ ⊕ Fin n) → ℤ) →+ ℤ) where
  toFun x := finiteTermCoordinateInput i a x j
  map_zero' := by simp [finiteTermCoordinateInput]
  map_add' x y := by
    simp only [finiteTermCoordinateInput, Function.update_apply, Pi.add_apply]
    split_ifs <;> rfl

theorem finiteSumCoordinateInput_one (i : σ) (x : (σ ⊕ Fin 1) → ℤ) :
    finiteSumCoordinateInput i x = finiteTermCoordinateInput i 0 x := by
  simp only [finiteSumCoordinateInput, finiteTermCoordinateInput, Fin.sum_univ_one]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.VariableRoundedGraphCoordinates
namespace OAI

section

namespace Erdos3.FreimanModel

def variableRoundedGraphModuli {I : Type*} (N : ℕ) (M : I → ℕ) : Option I → ℕ
  | none => N
  | some i => M i

def variableRoundedGraphCoordinateEquiv {I : Type*} (N : ℕ) (M : I → ℕ) :
    (ZMod N × (∀ i, ZMod (M i))) ≃+ (∀ i : Option I, ZMod (variableRoundedGraphModuli N M i)) where
  toFun x i := match i with
    | none => x.1
    | some j => x.2 j
  invFun x := (x none, fun i => x (some i))
  left_inv x := rfl
  right_inv x := by funext i; cases i <;> rfl
  map_add' x y := by funext i; cases i <;> rfl

theorem variableRoundedGraphModuli_neZero {I : Type*} (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)] :
    ∀ i : Option I, NeZero (variableRoundedGraphModuli N M i) := by
  intro i
  cases i <;> dsimp [variableRoundedGraphModuli] <;> infer_instance

end Erdos3.FreimanModel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineResidueCoordinateEquiv
namespace OAI

section

namespace Erdos3

noncomputable def affineResidueCoordinateEquiv {σ : Type*} (M q : ℕ) (a : σ → ℤ)
    (hcop : M.Coprime q) : (σ → ZMod q) ≃ (σ → ZMod q) :=
  Equiv.piCongrRight fun j =>
    (ZMod.unitOfCoprime M hcop).mulLeft.trans (Equiv.addLeft (a j : ZMod q))

theorem affineResidueCoordinateEquiv_apply {σ : Type*} (M q : ℕ) (a : σ → ℤ)
    (hcop : M.Coprime q) (x : σ → ZMod q) (j : σ) :
    affineResidueCoordinateEquiv M q a hcop x j = (a j : ZMod q) + (M : ZMod q) * x j := rfl

theorem affineResidueCoordinateEquiv_intCast {σ : Type*} (M q : ℕ) (a : σ → ℤ)
    (hcop : M.Coprime q) (z : σ → ℤ) :
    affineResidueCoordinateEquiv M q a hcop (fun j => (z j : ZMod q)) =
      (fun j => ((a j + (M : ℤ) * z j : ℤ) : ZMod q)) := by
  funext j
  simp only [affineResidueCoordinateEquiv_apply, Int.cast_add, Int.cast_mul, Int.cast_natCast]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FourAffineRefinement
namespace OAI

section

namespace Erdos3

variable {R I E : Type*} {V : I → Type*} [CommRing R]
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
  [AddCommGroup E] [Module R E]

def fourFunctionDifference (f : (∀ i, V i) → E) (v : ∀ i, Fin 4 → V i) : E :=
  f (fun i => v i 0) + f (fun i => v i 1) - f (fun i => v i 2) - f (fun i => v i 3)

theorem four_affine_balanced_invariant (f : (∀ i, V i) → E) (C D : ∀ i, Submodule R (V i))
    (haffine : ∀ x : ∀ i, V i, (∀ i, x i ∈ C i) →
      ∃ A : (∀ i, D i) →ₗ[R] E, ∀ y : ∀ i, D i,
        f (fun i => x i + (y i : V i)) = f x + A y)
    (v z : ∀ i, Fin 4 → V i) (hv : ∀ i, v i ∈ fourCommonModulo (C i) (D i))
    (hz : ∀ i, z i ∈ fourBalancedDependent (D i)) :
    fourFunctionDifference f (fun i k => v i k + z i k) = fourFunctionDifference f v := by
  let x : ∀ i, V i := fun i => v i 0
  obtain ⟨A, hA⟩ := haffine x (fun i => ((mem_fourCommonModulo (C i) (D i) (v i)).mp (hv i)).1 0)
  let y (k : Fin 4) : ∀ i, D i := fun i =>
    ⟨v i k - v i 0, ((mem_fourCommonModulo (C i) (D i) (v i)).mp (hv i)).2 k⟩
  let t (k : Fin 4) : ∀ i, D i := fun i =>
    ⟨z i k, ((mem_fourBalancedDependent (D i) (z i)).mp (hz i)).1 k⟩
  have hbase (k : Fin 4) : f (fun i => v i k) = f x + A (y k) := by
    have heq : (fun i => x i + ((y k) i : V i)) = fun i => v i k := by
      funext i
      dsimp only [x, y]
      abel
    simpa only [heq] using hA (y k)
  have hnew (k : Fin 4) : f (fun i => v i k + z i k) = f x + (A (y k) + A (t k)) := by
    have heq : (fun i => x i + ((y k + t k) i : V i)) = fun i => v i k + z i k := by
      funext i
      change v i 0 + (v i k - v i 0 + z i k) = _
      abel
    simpa only [heq, map_add] using hA (y k + t k)
  have ht : t 0 + t 1 - t 2 - t 3 = 0 := by
    funext i
    apply Subtype.ext
    change z i 0 + z i 1 - z i 2 - z i 3 = 0
    exact ((mem_fourBalancedDependent (D i) (z i)).mp (hz i)).2
  have hAt : A (t 0) + A (t 1) - A (t 2) - A (t 3) = 0 := by
    rw [← map_add, ← map_sub, ← map_sub, ht, map_zero]
  calc
    _ = fourFunctionDifference f v + (A (t 0) + A (t 1) - A (t 2) - A (t 3)) := by
      unfold fourFunctionDifference
      rw [hnew 0, hnew 1, hnew 2, hnew 3, hbase 0, hbase 1, hbase 2, hbase 3]
      abel
    _ = _ := by rw [hAt, add_zero]

theorem four_refined_affine_identity (f : (∀ i, V i) → E) (C D : ∀ i, Submodule R (V i))
    (haffine : ∀ x : ∀ i, V i, (∀ i, x i ∈ C i) →
      ∃ A : (∀ i, D i) →ₗ[R] E, ∀ y : ∀ i, D i,
        f (fun i => x i + (y i : V i)) = f x + A y)
    (K : ∀ i, Submodule R (Fin 4 → V i))
    (hK : ∀ v : ∀ i, Fin 4 → V i, (∀ i, v i ∈ K i) → fourFunctionDifference f v = 0)
    (v : ∀ i, Fin 4 → V i) (hv : ∀ i, v i ∈ fourRefinedRelation (C i) (D i) (K i)) :
    fourFunctionDifference f v = 0 := by
  classical
  have hdecomp (i : I) : ∃ u ∈ K i ⊓ fourCommonModulo (C i) (D i),
      ∃ z ∈ fourBalancedDependent (D i), u + z = v i := Submodule.mem_sup.mp (hv i)
  choose u hu z hz heq using hdecomp
  have hvEq : (fun i k => u i k + z i k) = v := by
    funext i k
    exact congrFun (heq i) k
  rw [← hvEq, four_affine_balanced_invariant f C D haffine u z (fun i => (hu i).2) hz]
  exact hK u (fun i => (hu i).1)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerResidueLatticeSum
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J : Type*} (q : ℕ) [NeZero q]

def integerResidueLatticePoint (r : J → ZMod q) (k : J → ℤ) : J → ℤ :=
  fun j => (r j).val + q * k j

@[simp] theorem integerResidueLatticePoint_cast
    (r : J → ZMod q) (k : J → ℤ) (j : J) :
    (integerResidueLatticePoint q r k j : ZMod q) = r j := by
  exact (ZMod.intCast_eq_iff q _ _).2 ⟨k j, rfl⟩

theorem integerResidueLatticePoint_bijective :
    Function.Bijective (fun p : (J → ZMod q) × (J → ℤ) =>
      integerResidueLatticePoint q p.1 p.2) := by
  constructor
  · rintro ⟨r, k⟩ ⟨r', k'⟩ h
    have hr : r = r' := by
      funext j
      have hj := congrArg (fun x : J → ℤ => (x j : ZMod q)) h
      simpa only [integerResidueLatticePoint_cast] using hj
    subst r'
    have hk : k = k' := by
      funext j
      have hj := congrFun h j
      change (r j).val + (q : ℤ) * k j = (r j).val + (q : ℤ) * k' j at hj
      exact mul_left_cancel₀ (show (q : ℤ) ≠ 0 by exact_mod_cast NeZero.ne q)
        (add_left_cancel hj)
    exact Prod.ext rfl hk
  · intro x
    refine ⟨(fun j => (x j : ZMod q), fun j => x j / q), ?_⟩
    funext j
    change ((x j : ZMod q).val : ℤ) + q * (x j / q) = x j
    rw [ZMod.val_intCast, Int.emod_add_mul_ediv]

noncomputable def integerResidueLatticeEquiv :
    ((J → ZMod q) × (J → ℤ)) ≃ (J → ℤ) :=
  Equiv.ofBijective _ (integerResidueLatticePoint_bijective q)

@[simp] theorem integerResidueLatticeEquiv_apply
    (r : J → ZMod q) (k : J → ℤ) :
    integerResidueLatticeEquiv q (r, k) = integerResidueLatticePoint q r k := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.EuclideanHorizontalProjection
namespace OAI

section

namespace Erdos3

def euclideanHorizontalProjection {σ : Type*} {m : ℕ} (a : ℕ) (ha : a ≤ m) :
    EuclideanSpace ℝ (σ ⊕ Fin m) →ₗ[ℝ] (Fin a → ℝ) where
  toFun x i := x (Sum.inr (Fin.castLE ha i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem euclideanHorizontalProjection_apply {σ : Type*} {m : ℕ}
    (a : ℕ) (ha : a ≤ m) (x : EuclideanSpace ℝ (σ ⊕ Fin m)) (i : Fin a) :
    euclideanHorizontalProjection a ha x i = x (Sum.inr (Fin.castLE ha i)) := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteKernelSumBound
namespace OAI

section

namespace Erdos3

variable {S I : Type*}

def kernelFiberEmbeddingEquiv (r : Setoid S) :
    {a : S → I // Setoid.ker a = r} ≃ (Quotient r ↪ I) where
  toFun a := ⟨Quotient.lift a.1 a.2.symm.le,
    (Setoid.lift_injective_iff_ker_eq_of_le a.2.symm.le).mpr a.2⟩
  invFun b := ⟨fun i => b (Quotient.mk'' i), by
    apply Setoid.ext
    intro i j
    change b (Quotient.mk'' i) = b (Quotient.mk'' j) ↔ r i j
    rw [b.injective.eq_iff, Quotient.eq]⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv b := by
    apply Function.Embedding.ext
    intro i
    induction i using Quotient.inductionOn with
    | h i => rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
  [DecidableEq I] [DecidableEq (Setoid S)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
  [DecidableEq I] [DecidableEq (Setoid S)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScalarEnvelope
namespace OAI

section

namespace Erdos3

def kernelInverseEnvelope {A : Type*} [Semiring A] (D p : A) : A :=
  D + D^2 + D*(D*(D+1)) + D*(D*D+D*(D^2+D+p+2))

def kernelGeometryEnvelope {A : Type*} [Semiring A] (D p : A) : A :=
  p+D+D+D*(D+1)+kernelInverseEnvelope D p

def kernelOutputEnvelope {A : Type*} [Semiring A] (D p : A) : A :=
  D^2+(D+1)*kernelGeometryEnvelope D p+(D+D+(D+1)*p)+
    D*(kernelGeometryEnvelope D p+1)+
    (4*kernelGeometryEnvelope D p+D+D+D*D+2)+1

theorem kernelInverseEnvelope_nonneg {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ kernelInverseEnvelope D p := by
  unfold kernelInverseEnvelope
  positivity

theorem kernelGeometryEnvelope_nonneg {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ kernelGeometryEnvelope D p := by
  have hi := kernelInverseEnvelope_nonneg hD hp
  unfold kernelGeometryEnvelope
  positivity

theorem kernelOutputEnvelope_nonneg {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ kernelOutputEnvelope D p := by
  have hg := kernelGeometryEnvelope_nonneg hD hp
  unfold kernelOutputEnvelope
  positivity

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TriplePhaseCancellation
namespace OAI

section

namespace Erdos3

theorem circle_character_triple_cancel (a b : CircleFourier.Circle) :
    CircleFourier.character (a + b) * star (CircleFourier.character a) *
      star (CircleFourier.character b) = 1 := by
  rw [← CircleFourier.character_neg, ← CircleFourier.character_neg,
    ← CircleFourier.character_add, ← CircleFourier.character_add]
  convert CircleFourier.character_zero using 1
  congr 1
  abel

theorem triple_phase_cancellation (v : Fin 3 → ℂ) (θ : Fin 3 → CircleFourier.Circle)
    (hθ : θ 0 = θ 1 + θ 2) :
    (CircleFourier.character (θ 0) * v 0) * star (CircleFourier.character (θ 1) * v 1) *
      star (CircleFourier.character (θ 2) * v 2) = v 0 * star (v 1) * star (v 2) := by
  rw [star_mul, star_mul]
  calc
    _ = (CircleFourier.character (θ 0) * star (CircleFourier.character (θ 1)) *
        star (CircleFourier.character (θ 2))) * (v 0 * star (v 1) * star (v 2)) := by ring
    _ = _ := by rw [hθ, circle_character_triple_cancel, one_mul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FiniteSamplingMoment
namespace OAI

section

namespace Erdos3.CyclicMZ

open _root_.Finset Fintype Nat

variable {ι : Type*} {A : Finset ι} {m n : ℕ}

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

lemma step_one (hA : A.Nonempty) (f : ι → ℝ) (a : Fin n → ι)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    |∑ i, f (a i)| ^ (m + 1) ≤
      (∑ b ∈ A ^^ n, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / #A ^ n := by
  let B := A ^^ n
  calc
    |∑ i, f (a i)| ^ (m + 1) =
        |∑ i, (f (a i) - (∑ b ∈ B, f (b i)) / #B)| ^ (m + 1) := by
      simp only [B, hf, sub_zero, zero_div]
    _ = |(∑ b ∈ B, ∑ i, (f (a i) - f (b i))) / #B| ^ (m + 1) := by
      simp only [sum_sub_distrib]
      rw [sum_const, sub_div, sum_comm, sum_div, nsmul_eq_mul, card_piFinset, prod_const,
        Finset.card_univ, Fintype.card_fin, Nat.cast_pow, mul_div_cancel_left₀]
      positivity
    _ = |∑ b ∈ B, ∑ i, (f (a i) - f (b i))| ^ (m + 1) / #B ^ (m + 1) := by
      rw [abs_div, div_pow, Nat.abs_cast]
    _ ≤ (∑ b ∈ B, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / #B ^ (m + 1) := by
      gcongr
      exact IsAbsoluteValue.abv_sum _ _ _
    _ = (∑ b ∈ B, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / #B ^ m / #B := by
      rw [div_div, ← _root_.pow_succ]
    _ ≤ (∑ b ∈ B, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / #B := by
      gcongr
      exact pow_sum_div_card_le_sum_pow (fun _ _ ↦ abs_nonneg _) _
    _ = _ := by simp [B]

lemma step_one' (hA : A.Nonempty) (f : ι → ℝ)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) (m : ℕ) (a : Fin n → ι) :
    |∑ i, f (a i)| ^ m ≤
      (∑ b ∈ A ^^ n, |∑ i, (f (a i) - f (b i))| ^ m) / #A ^ n := by
  cases m
  · simp only [_root_.pow_zero, sum_const, prod_const, Nat.smul_one_eq_cast,
      Finset.card_fin, card_piFinset, ← Nat.cast_pow]
    rw [div_self]
    rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
    exact pow_pos (Finset.card_pos.2 hA) _
  exact step_one hA f a hf

lemma step_two_aux (A : Finset ι) (f : ι → ℝ) (ε : Fin n → ℝ)
    (hε : ε ∈ ({-1, 1} : Finset ℝ) ^^ n) (g : (Fin n → ℝ) → ℝ) :
    ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, g (ε * (f ∘ a - f ∘ b)) =
      ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, g (f ∘ a - f ∘ b) := by
  rw [← sum_product', ← sum_product']
  let swapper : (Fin n → ι) × (Fin n → ι) → (Fin n → ι) × (Fin n → ι) := by
    intro xy
    exact (fun i ↦ if ε i = 1 then xy.1 i else xy.2 i,
      fun i ↦ if ε i = 1 then xy.2 i else xy.1 i)
  have h₁ : ∀ a ∈ (A ^^ n) ×ˢ (A ^^ n), swapper a ∈ (A ^^ n) ×ˢ (A ^^ n) := by
    simp only [mem_product, mem_piFinset, ← forall_and, swapper]
    intro a h i
    split_ifs
    · exact h i
    · exact (h i).symm
  have h₂ : ∀ a ∈ (A ^^ n) ×ˢ (A ^^ n), swapper (swapper a) = a := fun a _ ↦ by
    ext <;> simp only [swapper] <;> split_ifs <;> rfl
  refine sum_nbij' swapper swapper h₁ h₁ h₂ h₂ ?_
  rintro ⟨a, b⟩ _
  congr with i : 1
  simp only [mem_piFinset, mem_insert, mem_singleton] at hε
  simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, swapper]
  split_ifs with h
  · simp [h]
  rw [(hε i).resolve_right h]
  ring

lemma step_two (f : ι → ℝ) :
    ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, (∑ i, (f (a i) - f (b i))) ^ (2 * m) =
      2⁻¹ ^ n * ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n,
        ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
          (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) := by
  let B := A ^^ n
  have h : ∀ ε ∈ ({-1, 1} : Finset ℝ) ^^ n,
      ∑ a ∈ B, ∑ b ∈ B, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
        ∑ a ∈ B, ∑ b ∈ B, (∑ i, (f (a i) - f (b i))) ^ (2 * m) :=
    fun ε hε ↦ step_two_aux A f _ hε fun z : Fin n → ℝ ↦ univ.sum z ^ (2 * m)
  rw [Finset.sum_congr rfl h, sum_const, card_piFinset_const, card_pair, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_two, inv_pow, inv_mul_cancel_left₀]
  · positivity
  · norm_num

lemma step_three (f : ι → ℝ) :
    ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n,
      ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
        (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
      ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ (2 * m),
        (multinomial univ k * ∏ t, (f (a t) - f (b t)) ^ k t) *
          ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n, ∏ t, ε t ^ k t := by
  simp only [@sum_comm _ _ (Fin n → ℝ) _ _ (A ^^ n), sum_pow_eq_sum_piAntidiag]
  refine sum_congr rfl fun a _ ↦ ?_
  refine sum_congr rfl fun b _ ↦ ?_
  simp only [mul_pow, prod_mul_distrib, @sum_comm _ _ (Fin n → ℝ), ← mul_sum, ← sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← mul_assoc, mul_right_comm]

lemma step_four {k : Fin n → ℕ} :
    ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n, ∏ t, ε t ^ k t =
      2 ^ n * ite (∀ i, Even (k i)) 1 0 := by
  calc
    _ = ∏ i, ∑ j ∈ ({-1, 1} : Finset ℝ), j ^ k i := by rw [← sum_prod_piFinset]
    _ = ∏ i, if Even (k i) then 2 else 0 := by
      congr with i
      split_ifs <;> simp_all [sum_pair (show (-1 : ℝ) ≠ 1 by norm_num), one_add_one_eq_two]
    _ = _ := by simp [Fintype.prod_ite_zero]

lemma step_six {f : ι → ℝ} {a b : Fin n → ι} :
    ∑ k ∈ piAntidiag univ m,
        (multinomial univ fun a ↦ 2 * k a : ℝ) *
          ∏ i, (f (a i) - f (b i)) ^ (2 * k i) ≤
      m ^ m * (∑ i, (f (a i) - f (b i)) ^ 2) ^ m := by
  rw [sum_pow_eq_sum_piAntidiag, mul_sum]
  refine sum_le_sum fun k hk ↦ ?_
  rw [mem_piAntidiag] at hk
  simp only [← mul_assoc, pow_mul]
  gcongr
  norm_cast
  refine multinomial_two_mul_le_mul_multinomial.trans ?_
  rw [hk.1]

lemma step_seven {f : ι → ℝ} {a b : Fin n → ι} :
    m ^ m * (∑ i, (f (a i) - f (b i)) ^ 2 : ℝ) ^ m ≤
      m ^ m * 2 ^ m * (∑ i, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m := by
  rw [← mul_pow, ← mul_pow, ← mul_pow, mul_assoc, mul_sum _ _ (2 : ℝ)]
  gcongr with i
  exact add_sq_le.trans_eq (by simp)

lemma step_eight {f : ι → ℝ} {a b : Fin n → ι} :
    m ^ m * 2 ^ m * (∑ i, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m ≤
      m ^ m * 2 ^ (m + (m - 1)) *
        ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) := by
  rw [pow_add, ← mul_assoc _ _ (2 ^ _), mul_assoc _ (2 ^ (m - 1)), sum_add_distrib]
  gcongr
  refine add_pow_le ?_ ?_ m <;> positivity

lemma end_step {f : ι → ℝ} (hm : 1 ≤ m) (hA : A.Nonempty) :
    (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ m,
      ↑(multinomial univ fun i ↦ 2 * k i) *
        ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n ≤
      (4 * m) ^ m * ∑ a ∈ A ^^ n, (∑ i, f (a i) ^ 2) ^ m := by
  let B := A ^^ n
  calc
    (∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ piAntidiag univ m,
      (multinomial univ fun i ↦ 2 * k i : ℝ) *
        ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n ≤
      (∑ a ∈ B, ∑ b ∈ B, m ^ m * 2 ^ (m + (m - 1)) *
        ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) : ℝ) / #A ^ n := by
        gcongr
        exact step_six.trans <| step_seven.trans step_eight
    _ = _ := by
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      rw [← mul_add, ← two_mul, ← mul_assoc 2, ← mul_assoc 2, mul_right_comm 2,
        ← _root_.pow_succ', add_assoc, Nat.sub_add_cancel hm, pow_add, ← mul_pow, ← mul_pow,
        card_piFinset, prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow,
        mul_div_cancel_left₀]
      · norm_num
        dsimp [B]
      · positivity

namespace Real

attribute [-instance] decidableForallFin

theorem marcinkiewicz_zygmund' (m : ℕ) (f : ι → ℝ)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    ∑ a ∈ A ^^ n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * ∑ a ∈ A ^^ n, (∑ i, f (a i) ^ 2) ^ m := by
  obtain rfl | hm := m.eq_zero_or_pos
  · simp
  have hm' : 1 ≤ m := by rwa [Nat.succ_le_iff]
  obtain rfl | hA := A.eq_empty_or_nonempty
  · cases n <;> cases m <;> simp
  let B := A ^^ n
  calc
    ∑ a ∈ B, (∑ i, f (a i)) ^ (2 * m) ≤
        ∑ a ∈ A ^^ n,
          (∑ b ∈ B, |∑ i, (f (a i) - f (b i))| ^ (2 * m)) / #A ^ n := by
      gcongr
      simpa [pow_mul, sq_abs] using step_one' hA f hf (2 * m) _
    _ = (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
        ∑ k ∈ piAntidiag univ (2 * m) with ∀ i, 2 ∣ k i,
          multinomial univ (fun i ↦ k i) * ∏ t, (f (a t) - f (b t)) ^ k t) / #A ^ n := by
      rw [← sum_div]
      simp_rw [pow_abs_two_mul]
      rw [step_two, step_three, mul_comm, inv_pow, ← div_eq_mul_inv, div_div]
      simp only [step_four, mul_ite, mul_zero, mul_one, ← sum_filter, ← sum_mul,
        even_iff_two_dvd]
      rw [mul_comm, mul_div_mul_left]
      positivity
    _ = (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
        ∑ k ∈ (piAntidiag univ m).map
          ⟨(2 • ·), fun _ _ h ↦ funext fun i ↦
            mul_right_injective₀ two_ne_zero (congr_fun h i)⟩,
          multinomial univ (fun i ↦ k i) * ∏ t, (f (a t) - f (b t)) ^ k t) / #A ^ n := by
      rw [map_nsmul_piAntidiag_univ m (ι := Fin n) (n := 2) two_ne_zero]
    _ = (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ m,
        multinomial univ (fun i ↦ 2 * k i) *
          ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n := by
      simp
    _ ≤ _ := end_step hm' hA

theorem marcinkiewicz_zygmund (hm : m ≠ 0) (f : ι → ℝ)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    ∑ a ∈ A ^^ n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ A ^^ n, ∑ i, f (a i) ^ (2 * m) := by
  obtain _ | m := m
  · simp at hm
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  calc
    ∑ a ∈ A ^^ n, (∑ i, f (a i)) ^ (2 * (m + 1)) ≤
        (4 * ↑(m + 1)) ^ (m + 1) *
          ∑ a ∈ A ^^ n, (∑ i, f (a i) ^ 2) ^ (m + 1) :=
      marcinkiewicz_zygmund' _ f hf
    _ ≤ (4 * ↑(m + 1)) ^ (m + 1) *
        (∑ a ∈ A ^^ n, n ^ m * ∑ i, f (a i) ^ (2 * (m + 1))) := by
      gcongr with a
      rw [← div_le_iff₀' (by positivity)]
      simpa only [Finset.card_fin, pow_mul] using
        pow_sum_div_card_le_sum_pow (f := fun i ↦ f (a i) ^ 2)
          (s := univ) (fun i _ ↦ by positivity) m
    _ ≤ (4 * ↑(m + 1)) ^ (m + 1) * n ^ m *
        ∑ a ∈ A ^^ n, ∑ i, f (a i) ^ (2 * (m + 1)) := by
      simp_rw [mul_assoc, mul_sum]
      rfl

end Real

namespace RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

theorem marcinkiewicz_zygmund (hm : m ≠ 0) (f : ι → 𝕜)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    ∑ a ∈ A ^^ n, ‖∑ i, f (a i)‖ ^ (2 * m) ≤
      (8 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ A ^^ n, ∑ i, ‖f (a i)‖ ^ (2 * m) := by
  let f₁ x : ℝ := _root_.RCLike.re (f x)
  let f₂ x : ℝ := _root_.RCLike.im (f x)
  let B := A ^^ n
  have hf₁ i : ∑ a ∈ B, f₁ (a i) = 0 := by rw [← map_sum, hf, map_zero]
  have hf₂ i : ∑ a ∈ B, f₂ (a i) = 0 := by rw [← map_sum, hf, map_zero]
  have h₁ := Real.marcinkiewicz_zygmund hm _ hf₁
  have h₂ := Real.marcinkiewicz_zygmund hm _ hf₂
  dsimp [f₁, f₂] at h₁ h₂
  simp only [pow_mul, RCLike.norm_sq_eq_def, ← sq, map_sum, map_sum]
  calc
    ∑ a ∈ B, ((∑ i, _root_.RCLike.re (f (a i))) ^ 2 +
        (∑ i, _root_.RCLike.im (f (a i))) ^ 2) ^ m ≤
        ∑ a ∈ B, 2 ^ (m - 1) *
          (((∑ i, _root_.RCLike.re (f (a i))) ^ 2) ^ m +
            ((∑ i, _root_.RCLike.im (f (a i))) ^ 2) ^ m) := by
      gcongr with a
      apply add_pow_le <;> positivity
    _ = 2 ^ (m - 1) *
        (∑ a ∈ B, (∑ i, _root_.RCLike.re (f (a i))) ^ (2 * m) +
          ∑ a ∈ B, (∑ i, _root_.RCLike.im (f (a i))) ^ (2 * m)) := by
      simp only [← sum_add_distrib, mul_sum, pow_mul]
    _ ≤ 2 ^ (m - 1) *
        ((4 * m) ^ m * n ^ (m - 1) *
            ∑ a ∈ B, ∑ i, _root_.RCLike.re (f (a i)) ^ (2 * m) +
          (4 * m) ^ m * n ^ (m - 1) *
            ∑ a ∈ B, ∑ i, _root_.RCLike.im (f (a i)) ^ (2 * m)) := by
      gcongr
    _ = 2 ^ (m - 1) * ((4 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ B, ∑ i,
          (_root_.RCLike.re (f (a i)) ^ (2 * m) +
            _root_.RCLike.im (f (a i)) ^ (2 * m))) := by
      simp_rw [sum_add_distrib, mul_add]
    _ ≤ 2 ^ (m - 1) * ((4 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ B, ∑ i,
          2 * (_root_.RCLike.re (f (a i)) ^ 2 +
            _root_.RCLike.im (f (a i)) ^ 2) ^ m) := by
      simp_rw [pow_mul]
      gcongr
      apply pow_add_pow_le' <;> positivity
    _ = (8 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ B, ∑ i,
          (_root_.RCLike.re (f (a i)) ^ 2 +
            _root_.RCLike.im (f (a i)) ^ 2) ^ m := by
      simp_rw [← mul_sum, show (8 : ℝ) = 2 * 4 by norm_num, mul_pow,
        ← pow_sub_one_mul hm (2 : ℝ)]
      ring

end RCLike

end Erdos3.CyclicMZ

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarThresholdPolynomial
namespace OAI

section

namespace Erdos3

noncomputable def scalarThresholdPolynomial : Polynomial ℕ :=
  let X := Polynomial.X
  let b := 1024 * (X + 3) ^ 3
  let row := (16 + 4 * X) * X + 16 * X + 48
  let error := X + row + X * (row + 6 * X + 12)
  let coeff := 30 + 2 * X * X + 2 * X + error + X * (5 * X + 11) + 10 * X + 4 * (2 + X)
  let mean := 2 * (b * (X + 2) + 2) + 4 + 2 * X * X + X * (5 * X + 11) + X
  let replacement := 2 * coeff + 2 * mean + (2 * b + 2) * X + 20
  let accuracy := 3 * X + (b * (X + 2) + 1) + 10
  let cell := 65536 * (X + 3) ^ 4 + X * b + accuracy + X + 1
  let mesh := X + 3 * (X + 1) + accuracy + 50
  X + X + 2 * (3 * X + 10) + 2 * replacement + X + X + 4 * mesh + 2 * cell + 2 * X + 100

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationParameterPolynomialPacking
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B R : Type*} [CommSemiring R]

noncomputable def packTranslationPolynomial :
    MvPolynomial B (MvPolynomial U R) ≃ₐ[R] MvPolynomial (U ⊕ B) R :=
  (commAlgEquiv R B U).trans (sumAlgEquiv R U B).symm

@[simp] theorem packTranslationPolynomial_X (i : B) :
    packTranslationPolynomial (R := R) (U := U) (X i) = X (Sum.inr i) := by
  simp [packTranslationPolynomial]

@[simp] theorem packTranslationPolynomial_C_X (i : U) :
    packTranslationPolynomial (R := R) (B := B) (C (X i)) = X (Sum.inl i) := by
  simp only [packTranslationPolynomial, AlgEquiv.trans_apply, commAlgEquiv_C_X,
    sumAlgEquiv_symm_X]

@[simp] theorem packTranslationPolynomial_C (P : MvPolynomial U R) :
    packTranslationPolynomial (B := B) (C P) = rename Sum.inl P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [packTranslationPolynomial]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP, rename_X]
    rw [packTranslationPolynomial_C_X]

theorem packTranslationPolynomial_specialize (u : U → R)
    (Q : MvPolynomial B (MvPolynomial U R)) :
    aeval (Sum.elim (fun i => C (u i)) X) (packTranslationPolynomial Q) =
      MvPolynomial.map (eval u) Q := by
  induction Q using MvPolynomial.induction_on with
  | C P =>
    rw [packTranslationPolynomial_C, map_C]
    induction P using MvPolynomial.induction_on with
    | C c => simp
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | mul_X P i hP => simp only [map_mul, rename_X, aeval_X, Sum.elim_inl, eval_X, hP]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, packTranslationPolynomial_X, aeval_X,
      Sum.elim_inr, map_X, hP]

theorem packTranslationPolynomial_eval (u : U → R) (b : B → R)
    (Q : MvPolynomial B (MvPolynomial U R)) :
    eval (Sum.elim u b) (packTranslationPolynomial Q) =
      eval b (MvPolynomial.map (eval u) Q) := by
  rw [← packTranslationPolynomial_specialize u Q]
  change (aeval (Sum.elim u b)) _ = (aeval b) ((aeval _) _)
  rw [MvPolynomial.comp_aeval_apply]
  congr 2
  funext i
  cases i <;> simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BSGDensity
namespace OAI

section

section BSGCast

namespace NNRat
open scoped _root_.NNRat
variable {K : Type*} [DivisionRing K] [CharZero K]

@[simp] lemma cast_sub {p q : ℚ≥0} (h : p ≤ q) : (↑(q - p) : K) = q - p := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact tsub_add_cancel_of_le h

end NNRat

end BSGCast

section BSGDensity

namespace Finset
open scoped _root_.Finset
variable {K α β : Type*} [DivisionRing K] [CharZero K] [Fintype α] [Fintype β]
  {s t : Finset α} {a : α}

@[simp] lemma dens_product (s : Finset α) (t : Finset β) : (s ×ˢ t).dens = s.dens * t.dens := by
  simp [_root_.Finset.dens, mul_div_mul_comm]

variable [DecidableEq α]

@[grind =]
lemma dens_sdiff_of_subset (h : s ⊆ t) : (t \ s).dens = t.dens - s.dens := by
  suffices (t \ s).dens = (t \ s ∪ s).dens - s.dens by rwa [_root_.Finset.sdiff_union_of_subset h] at this
  rw [_root_.Finset.dens_union_of_disjoint _root_.Finset.sdiff_disjoint, add_tsub_cancel_right]

lemma cast_dens_inter : ((s ∩ t).dens : K) = s.dens + t.dens - (s ∪ t).dens := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact _root_.Finset.dens_inter_add_dens_union ..

lemma cast_dens_sdiff (h : s ⊆ t) : ((t \ s).dens : K) = t.dens - s.dens := by
  rw [dens_sdiff_of_subset h, NNRat.cast_sub (_root_.Finset.dens_mono h)]

end Finset

end BSGDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CandidateFrontFactorMassBlockBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem candidateFrontFactor_uniform_block_le_power (s Ctotal : ℕ)
    {m : ℕ} {p markInput ci : ℝ} (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p)
    (hmark : markInput ≤ ci) (hci : ci ≤ (p + 2) ^ Ctotal) :
    (s : ℝ) * (markInput * m) ≤ (p + 2) ^ (Ctotal + s + 1) := by
  have hbase : 0 ≤ p + 2 := by linarith only [hp]
  have htwo : (s : ℝ) ≤ (2 : ℝ) ^ s := by
    exact_mod_cast (show s < 2 ^ s from Nat.lt_two_pow_self).le
  have hs : (s : ℝ) ≤ (p + 2) ^ s :=
    htwo.trans (pow_le_pow_left₀ (by norm_num) (by linarith only [hp]) s)
  have hcoefficient : (s : ℝ) * m ≤ (p + 2) ^ s * (p + 2) :=
    mul_le_mul hs (by linarith only [hm]) (Nat.cast_nonneg _) (pow_nonneg hbase _)
  calc
    _ = ((s : ℝ) * m) * markInput := by ring
    _ ≤ ((s : ℝ) * m) * (p + 2) ^ Ctotal :=
      mul_le_mul_of_nonneg_left (hmark.trans hci) (by positivity)
    _ ≤ ((p + 2) ^ s * (p + 2)) * (p + 2) ^ Ctotal :=
      mul_le_mul_of_nonneg_right hcoefficient (pow_nonneg hbase _)
    _ = (p + 2) ^ (Ctotal + s + 1) := by
      rw [← pow_succ, ← pow_add]
      congr 1
      omega

theorem candidateFrontFactor_massLog_le
    {v V n p qCommon common mass0 : ℝ}
    (hv0 : 0 ≤ v) (hv : v ≤ V) (hn0 : 0 ≤ n) (hn : n ≤ p)
    (hq0 : 0 ≤ qCommon) (hq : qCommon ≤ common) (hmass : mass0 ≤ p) :
    v * n + ((qCommon + 2) ^ 5 + qCommon) + mass0 ≤
      p + V * p + ((common + 2) ^ 5 + common) := by
  have hproduct : v * n ≤ V * p := mul_le_mul hv hn hn0 (hv0.trans hv)
  have hpower : (qCommon + 2) ^ 5 ≤ (common + 2) ^ 5 :=
    pow_le_pow_left₀ (by linarith only [hq0]) (by linarith only [hq]) 5
  linarith only [hproduct, hpower, hq, hmass]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedReadyNormalizationMassBudget
namespace OAI

section

namespace Erdos3

theorem relativeReturnedNormalization_denominator_pos (D s : ℕ) :
    (0 : ℝ) < ((D + 1) * (s + 1) ^ D : ℕ) := by
  positivity

theorem relativeReturnedNormalization_denominator_le_exp (D s : ℕ)
    {cost : ℝ} (hD : (D : ℝ) ≤ cost) :
    (((D + 1) * (s + 1) ^ D : ℕ) : ℝ) ≤ Real.exp (((s : ℝ) + 1) * cost) := by
  have hD1 : ((D + 1 : ℕ) : ℝ) ≤ Real.exp cost := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith only [hD, Real.add_one_le_exp cost]
  have hs1 : ((s + 1 : ℕ) : ℝ) ≤ Real.exp (s : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.add_one_le_exp (s : ℝ)
  have hpower : (((s + 1) ^ D : ℕ) : ℝ) ≤ Real.exp ((s : ℝ) * cost) := by
    calc
      _ = ((s + 1 : ℕ) : ℝ) ^ D := Nat.cast_pow _ _
      _ ≤ (Real.exp (s : ℝ)) ^ D := pow_le_pow_left₀ (Nat.cast_nonneg _) hs1 D
      _ = Real.exp ((D : ℝ) * s) := (Real.exp_nat_mul (s : ℝ) D).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg s))
  calc
    _ = ((D + 1 : ℕ) : ℝ) * (((s + 1) ^ D : ℕ) : ℝ) := Nat.cast_mul _ _
    _ ≤ Real.exp cost * Real.exp ((s : ℝ) * cost) :=
      mul_le_mul hD1 hpower (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (((s : ℝ) + 1) * cost) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem relativeReturnedNormalization_mass_expression_lower (D s : ℕ)
    {cost massLog normBudget originalMass : ℝ}
    (hD : (D : ℝ) ≤ cost) (hmass : Real.exp (-massLog) ≤ originalMass) :
    Real.exp (-(massLog + ((s : ℝ) + 1) * cost + normBudget)) ≤
      (originalMass / ((D + 1) * (s + 1) ^ D : ℕ)) * Real.exp (-normBudget) := by
  have hden := relativeReturnedNormalization_denominator_pos D s
  have hbound := relativeReturnedNormalization_denominator_le_exp D s hD
  have hdiv : Real.exp (-massLog) / Real.exp (((s : ℝ) + 1) * cost) ≤
      originalMass / ((D + 1) * (s + 1) ^ D : ℕ) :=
    (div_le_div_of_nonneg_left (Real.exp_nonneg _) hden hbound).trans
      (div_le_div_of_nonneg_right hmass hden.le)
  calc
    _ = (Real.exp (-massLog) / Real.exp (((s : ℝ) + 1) * cost)) *
        Real.exp (-normBudget) := by
      rw [← Real.exp_sub, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hdiv (Real.exp_nonneg _)

end Erdos3

end

section

namespace Erdos3

theorem preparedReady_mass_lower {p gain originalMass : ℝ}
    (hgain : Real.exp (-p) ≤ gain) (hmass : gain / 16 < originalMass) :
    Real.exp (-(p + 16)) ≤ originalMass := by
  have h16 : (16 : ℝ) ≤ Real.exp 16 := by
    linarith only [Real.add_one_le_exp (16 : ℝ)]
  have hexp : Real.exp (-(p + 16)) = Real.exp (-p) / Real.exp 16 := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hexp]
  exact ((div_le_div_of_nonneg_left (Real.exp_nonneg (-p)) (by norm_num) h16).trans
    (div_le_div_of_nonneg_right hgain (by norm_num))).trans hmass.le

theorem preparedReady_normalized_mass_lower (D s : ℕ)
    {p gain originalMass childCost normBudget : ℝ}
    (hD : (D : ℝ) ≤ childCost) (hgain : Real.exp (-p) ≤ gain)
    (hmass : gain / 16 < originalMass) :
    Real.exp (-(p + 16 + ((s : ℝ) + 1) * childCost + normBudget)) ≤
      (originalMass / ((D + 1) * (s + 1) ^ D : ℕ)) * Real.exp (-normBudget) :=
  relativeReturnedNormalization_mass_expression_lower D s hD
    (preparedReady_mass_lower hgain hmass)

theorem preparedReady_capped_normalized_mass_lower (rankBound s : ℕ)
    {p gain originalMass childCost normBudget : ℝ} (hcost : 0 ≤ childCost)
    (hgain : Real.exp (-p) ≤ gain) (hmass : gain / 16 < originalMass) :
    let D := min rankBound ⌊childCost⌋₊
    Real.exp (-(p + 16 + ((s : ℝ) + 1) * childCost + normBudget)) ≤
      (originalMass / ((D + 1) * (s + 1) ^ D : ℕ)) * Real.exp (-normBudget) := by
  apply preparedReady_normalized_mass_lower _ _ _ hgain hmass
  exact (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.floor_le hcost)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Results.LinearFormsBasic
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

structure AffineForm (ι R : Type*) [Zero R] where
  constant : R
  coefficient : ι → R

namespace AffineForm

def eval {ι R : Type*} [Fintype ι] [Semiring R]
    (ψ : AffineForm ι R) (x : ι → R) : R :=
  ψ.constant + ∑ i, ψ.coefficient i * x i

@[simp]
theorem eval_zero {ι R : Type*} [Fintype ι] [Semiring R]
    (ψ : AffineForm ι R) :
    ψ.eval (fun _ => 0) = ψ.constant := by
  simp [eval]

end AffineForm

end Erdos3.FixedDensity

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastShortGridEquiv
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def forecastShortGridEquiv (A : Type*) :
    (A → ℤ) ≃ (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) where
  toFun k a _ := k a
  invFun k a := k a ⟨∅, Finset.mem_univ _⟩
  left_inv _ := rfl
  right_inv k := by
    funext a row
    exact congrArg (k a) (Subsingleton.elim _ _)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.L1SamplingSurrogate
namespace OAI

section

namespace Erdos3
open MeasureTheory

theorem l1_sampling_via_uniform_surrogate
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Y → X) (f ideal g : X → ℂ)
    (hf : Integrable f μ) (hi : Integrable ideal μ) (hg : Integrable g μ)
    (hfs : Integrable (fun y => f (s y)) ν)
    (his : Integrable (fun y => ideal (s y)) ν)
    (hgs : Integrable (fun y => g (s y)) ν)
    {E δ ε : ℝ} (happrox : ∀ x, ‖ideal x - g x‖ ≤ δ)
    (hmass : (∫ x, ‖f x - ideal x‖ ∂μ) ≤ E)
    (hsample : (∫ y, ‖f (s y) - g (s y)‖ ∂ν) ≤
      (∫ x, ‖f x - g x‖ ∂μ) + ε) :
    (∫ y, ‖f (s y) - ideal (s y)‖ ∂ν) ≤ E + 2 * δ + ε := by
  have hhaar : (∫ x, ‖f x - g x‖ ∂μ) ≤ E + δ := by
    calc
      _ ≤ ∫ x, ‖f x - ideal x‖ + δ ∂μ :=
        integral_mono (hf.sub hg).norm ((hf.sub hi).norm.add (integrable_const δ))
          (fun x => (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
            (add_le_add le_rfl (happrox x)))
      _ = (∫ x, ‖f x - ideal x‖ ∂μ) + δ := by
        simpa [Pi.sub_apply] using
          (integral_add (hf.sub hi).norm (integrable_const δ))
      _ ≤ E + δ := add_le_add hmass le_rfl
  calc
    _ ≤ ∫ y, ‖f (s y) - g (s y)‖ + δ ∂ν :=
      integral_mono (hfs.sub his).norm ((hfs.sub hgs).norm.add (integrable_const δ))
        (fun y => (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
          (add_le_add le_rfl (by simpa only [norm_sub_rev] using happrox (s y))))
    _ = (∫ y, ‖f (s y) - g (s y)‖ ∂ν) + δ := by
      simpa [Pi.sub_apply] using
        (integral_add (hfs.sub hgs).norm (integrable_const δ))
    _ ≤ ((E + δ) + ε) + δ :=
      add_le_add (hsample.trans (add_le_add hhaar le_rfl)) le_rfl
    _ = _ := by ring

end Erdos3

end

end OAI

end


