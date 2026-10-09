-- Prove2me | Definitions.Def_OAIErdos3B019
-- name    : OAIErdos3B019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T13:34:09.726016+00:00
-- url     : https://prove2.me/theorems/f71232c0-d256-4023-bca5-311d795ddb8e
-- title:
--   OpenAI Erdős-3 split, definitions bundle 20 of 93
-- statement:
--   Definitions bundle 20 of 93 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B018`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 20 available.
--
--   Modules: `OAI.Erdos3.BasisBlockInvariant`, `OAI.Erdos3.BasisBlockInvariant.inf`, `OAI.Erdos3.BasisBlockInvariant.map`, `OAI.Erdos3.HasLayerSamplingRank`, `OAI.Erdos3.HasLayerSamplingRank.div_nat`, `OAI.Erdos3.HasLayerSamplingRank.inv_nat_smul`, `OAI.Erdos3.HasLayerSamplingRank.mono`, `OAI.Erdos3.HasLayerSamplingRank.not_approximation`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeBasis_structure_height`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeDegreeBasis`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeDegreeBasis_height`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeMultidegreeBasis`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeMultidegreeBasis_height`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeSupportedFinBasis`, `OAI.Erdos3.MultidegreeLieFiltration.squarefreeSupportedFinBasis_height`, `OAI.Erdos3.NilpotentLieBCHGroup.PolynomialDerivativeSystem`, `OAI.Erdos3.NilpotentLieBCHGroup.PolynomialDerivativeSystem.real_evaluation`, `OAI.Erdos3.NilpotentLieBCHGroup.PolynomialGroup`, `OAI.Erdos3.NilpotentLieBCHGroup.centralBCHCircleAction`, `OAI.Erdos3.NilpotentLieBCHGroup.centralBCHCircleAction_act_coe`, `OAI.Erdos3.NilpotentLieBCHGroup.centralBCHCircleAction_commutes`, `OAI.Erdos3.NilpotentLieBCHGroup.centralBCHCircleAction_displacement`, `OAI.Erdos3.NilpotentLieBCHGroup.centralBCHFlow_displacement`, `OAI.Erdos3.NilpotentLieBCHGroup.centralBCHFlow_isometry`, `OAI.Erdos3.NilpotentLieBCHGroup.centralBCHFlow_period`, `OAI.Erdos3.NilpotentLieBCHGroup.central_logCharacter_coset_dist_le`, `OAI.Erdos3.NilpotentLieBCHGroup.eval₂_dualAdjoint`, `OAI.Erdos3.NilpotentLieBCHGroup.eval₂_formalLogDerivative`, `OAI.Erdos3.NilpotentLieBCHGroup.exists_uniform_left_lipschitz_exp_bound`, `OAI.Erdos3.NilpotentLieBCHGroup.exists_uniform_quotient_left_lipschitz_exp_bound`, `OAI.Erdos3.NilpotentLieBCHGroup.formalLogDerivative`, `OAI.Erdos3.NilpotentLieBCHGroup.formalLogDerivative_mem_of_invariant`, `OAI.Erdos3.NilpotentLieBCHGroup.formalLogDerivative_one`, `OAI.Erdos3.NilpotentLieBCHGroup.formalLogDerivative_remove`, `OAI.Erdos3.NilpotentLieBCHGroup.formalPolynomialJetHom`, `OAI.Erdos3.NilpotentLieBCHGroup.formalPolynomialJetLie`, `OAI.Erdos3.NilpotentLieBCHGroup.formalPolynomialJet_base`, `OAI.Erdos3.NilpotentLieBCHGroup.formalPolynomialJet_baseHom`, `OAI.Erdos3.NilpotentLieBCHGroup.formalPolynomialJet_tangent`, `OAI.Erdos3.NilpotentLieBCHGroup.logCharacter`, `OAI.Erdos3.NilpotentLieBCHGroup.logCharacter_dist_one_le`, `OAI.Erdos3.NilpotentLieBCHGroup.logCharacter_inv_mul`, `OAI.Erdos3.NilpotentLieBCHGroup.logCharacter_mul`, `OAI.Erdos3.NilpotentLieBCHGroup.logCharacter_norm`, `OAI.Erdos3.NilpotentLieBCHGroup.logCharacter_norm_sub_eq_relative`, `OAI.Erdos3.NilpotentLieBCHGroup.logCharacter_of_integral`, `OAI.Erdos3.NilpotentLieBCHGroup.polynomialFirstJetHom`, `OAI.Erdos3.NilpotentLieBCHGroup.polynomialFirstJet_base`, `OAI.Erdos3.NilpotentLieBCHGroup.polynomialValueHom`, `OAI.Erdos3.NilpotentLieBCHGroup.quotientChartedSpace`, `OAI.Erdos3.NilpotentLieBCHGroup.quotientCoordinateChart`, `OAI.Erdos3.NilpotentLieBCHGroup.quotientCoordinateChart_center_mem`, `OAI.Erdos3.NilpotentLieBCHGroup.quotientCoordinateChart_target`, `OAI.Erdos3.NilpotentLieBCHGroup.quotientMetricSpace_lipschitz_left`, `OAI.Erdos3.NilpotentLieBCHGroup.quotientMetricSpace_lipschitz_orbit`, `OAI.Erdos3.NilpotentLieBCHGroup.realPolynomialChartSubstitution`, `OAI.Erdos3.NilpotentLieBCHGroup.realPolynomialChartSubstitution_coord`, `OAI.Erdos3.NilpotentLieBCHGroup.realPolynomialJet`, `OAI.Erdos3.NilpotentLieBCHGroup.realPolynomialJet_base`, `OAI.Erdos3.NilpotentLieBCHGroup.realPolynomialJet_baseHom`, `OAI.Erdos3.NilpotentLieBCHGroup.realPolynomialJet_tangent`, `OAI.Erdos3.NilpotentLieBCHGroup.realPolynomialValueHom`, `OAI.Erdos3.NilpotentLieBCHGroup.realPolynomialValueHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.exists_bounded_filtered_section`, `OAI.Erdos3.NilpotentLieFiltration.exists_image_lattice_cover`, `OAI.Erdos3.VectorPolynomial.appendRankCutRow`, `OAI.Erdos3.VectorPolynomial.coefficients_realChartSubstitute`, `OAI.Erdos3.VectorPolynomial.coefficients_realChartSubstitute_reindex`, `OAI.Erdos3.VectorPolynomial.coefficients_realCoefficientEquiv`, `OAI.Erdos3.VectorPolynomial.coefficients_realCoefficientEquiv_symm`, `OAI.Erdos3.VectorPolynomial.coefficients_substitute_reindex`, `OAI.Erdos3.VectorPolynomial.coefficients_zero_realChartSubstitute_reindex`, `OAI.Erdos3.VectorPolynomial.directionalDerivative`, `OAI.Erdos3.VectorPolynomial.directionalDerivative_direction_add`, `OAI.Erdos3.VectorPolynomial.directionalDerivative_direction_smul`, `OAI.Erdos3.VectorPolynomial.directionalDerivative_lie`, `OAI.Erdos3.VectorPolynomial.directionalDerivative_tmul`, `OAI.Erdos3.VectorPolynomial.dualEvalLie`, `OAI.Erdos3.VectorPolynomial.dualEvalLie_base`, `OAI.Erdos3.VectorPolynomial.dualEvalLie_tmul`, `OAI.Erdos3.VectorPolynomial.eval_realCoefficientEquiv`, `OAI.Erdos3.VectorPolynomial.eval₂_normalizedRealPolynomialChart`, `OAI.Erdos3.VectorPolynomial.eval₂_realChartSubstitute`, `OAI.Erdos3.VectorPolynomial.eval₂_realCoefficientEquiv_symm`, `OAI.Erdos3.VectorPolynomial.integerRowPolynomial_homogeneousPart`, `OAI.Erdos3.VectorPolynomial.integerRowPolynomial_totalDegree_le`, `OAI.Erdos3.VectorPolynomial.jointRationalSpace`, `OAI.Erdos3.VectorPolynomial.pderiv_lie`, `OAI.Erdos3.VectorPolynomial.realChartSubstitute`, `OAI.Erdos3.VectorPolynomial.realChartSubstituteLie`, `OAI.Erdos3.VectorPolynomial.realChartSubstitute_comp`, `OAI.Erdos3.VectorPolynomial.realChartSubstitute_lie`, `OAI.Erdos3.VectorPolynomial.realCoefficientEquiv`, `OAI.Erdos3.VectorPolynomial.realCoefficientEquiv_monomial`, `OAI.Erdos3.VectorPolynomial.samplingRankProjection`, `OAI.Erdos3.VectorPolynomial.samplingRankProjection_apply`, `OAI.Erdos3.absorbedInitialParameter`, `OAI.Erdos3.absorbedInitialParameter_bounds`, `OAI.Erdos3.absorbedInitialParameter_nonneg`, `OAI.Erdos3.baseChange_matrix_apply`, `OAI.Erdos3.basisBlockInvariant_ker`, `OAI.Erdos3.basisBlockMap_commutes`, `OAI.Erdos3.basis_repr_height_one`, `OAI.Erdos3.bchLogMetricConstant_le_inverse`, `OAI.Erdos3.bchProductBracketCoefficient_height`, `OAI.Erdos3.bchProductCoefficientBase`, `OAI.Erdos3.bchProductCoefficientBase_pos`, `OAI.Erdos3.bchProductCoefficientHeight`, `OAI.Erdos3.bchProductCoefficientHeight_le_exp`, `OAI.Erdos3.bchProductCoordinatePolynomial_height`, `OAI.Erdos3.bchProductDenominator_le_height`, `OAI.Erdos3.bchProductNumeratorBound_le_height`, `OAI.Erdos3.bchProductWordCoefficient_height`, `OAI.Erdos3.bch_bounded_product_box_expression_le_exp`, `OAI.Erdos3.bch_box_expression_le_exp`, `OAI.Erdos3.bch_comap_inner_grid`, `OAI.Erdos3.bch_triple_box_expression_le_exp`, `OAI.Erdos3.blockSpanningFamily`, `OAI.Erdos3.blockSpanningFamily_height`, `OAI.Erdos3.blockSpanningFamily_repr`, `OAI.Erdos3.blockSpanningFamily_span`, `OAI.Erdos3.boxCoverCount_dimension_bound`, `OAI.Erdos3.bracketConstructionBudget`, `OAI.Erdos3.bracketConstructionBudget_nonneg`, `OAI.Erdos3.bracketCorrectionBudget`, `OAI.Erdos3.bracketCorrectionBudget_nonneg`, `OAI.Erdos3.bracket_construction_budget_bounds`, `OAI.Erdos3.bracket_correction_budget_bounds`, `OAI.Erdos3.cocycle_horizontal_normalization`, `OAI.Erdos3.conjugated_subgroup_inner_grid`, `OAI.Erdos3.controlled_real_column_span_separation`, `OAI.Erdos3.controlled_small_vector_separation`, `OAI.Erdos3.coordinateLipschitzBound_power_budget`, `OAI.Erdos3.currentLayerConstructionBudget`, `OAI.Erdos3.currentLayerConstructionBudget_nonneg`, `OAI.Erdos3.currentLayerRemovalBudget`, `OAI.Erdos3.currentLayerRemovalBudget_nonneg`, `OAI.Erdos3.current_layer_construction_budget_bounds`, `OAI.Erdos3.current_layer_coordinate_factor_bound`, `OAI.Erdos3.current_layer_removal_budget_bounds`, `OAI.Erdos3.denominatorGrid_neg`, `OAI.Erdos3.dualScalarEval`, `OAI.Erdos3.dualScalarEval_X`, `OAI.Erdos3.dualScalarEval_fst`, `OAI.Erdos3.exists_bchBoxCover_count_budget`, `OAI.Erdos3.exists_bchLogMetricConstant_exp_bound`, `OAI.Erdos3.exists_bchProductCoordinatePolynomial_exp_budget`, `OAI.Erdos3.exists_bch_conjugation_basis_exp_bound`, `OAI.Erdos3.exists_bch_fixed_product_exp_bound`, `OAI.Erdos3.exists_bch_group_product_exp_bound`, `OAI.Erdos3.exists_bch_product_box_bound`, `OAI.Erdos3.exists_bch_product_coordinate_polynomials_exp_height`, `OAI.Erdos3.exists_bch_triple_product_exp_bound`, `OAI.Erdos3.exists_block_quotient_rows`, `OAI.Erdos3.exists_bounded_block_image_section`, `OAI.Erdos3.exists_bounded_block_quotient_projection`, `OAI.Erdos3.exists_bounded_image_representatives`, `OAI.Erdos3.exists_bounded_layer_spanning`, `OAI.Erdos3.exists_bounded_linear_image_section`, `OAI.Erdos3.exists_bounded_linear_section`, `OAI.Erdos3.exists_bounded_rational_image_section`, `OAI.Erdos3.exists_bounded_realification_factors`, `OAI.Erdos3.exists_bounded_realification_layer_reduction`, `OAI.Erdos3.exists_bounded_realified_linear_section`, `OAI.Erdos3.exists_bracket_uniform_budget`, `OAI.Erdos3.exists_common_correction_budget`, `OAI.Erdos3.exists_conjugation_denominator_exp_bound`, `OAI.Erdos3.exists_controlled_coordinate_leftInverse`, `OAI.Erdos3.exists_controlled_linear_splitting`, `OAI.Erdos3.exists_controlled_sum_coordinates`, `OAI.Erdos3.exists_controlled_weighted_leftInverse`, `OAI.Erdos3.exists_current_layer_uniform_budget`, `OAI.Erdos3.exists_extractedInitialParameter_budget`, `OAI.Erdos3.exists_image_lattice_subgroup`, `OAI.Erdos3.exists_lipschitz_realification_reconstruction`, `OAI.Erdos3.exists_logCharacterMetricConstant_exp_bound`, `OAI.Erdos3.exists_native_horizontal_lift_budget`, `OAI.Erdos3.exists_polynomial_subspace_separation`, `OAI.Erdos3.exists_rationalReconstructionLipschitzBound_exp`, `OAI.Erdos3.exists_rational_sum_coordinates`, `OAI.Erdos3.exists_real_block_span_defining_matrix`, `OAI.Erdos3.exists_real_span_defining_matrix`, `OAI.Erdos3.exists_real_span_integer_defining_matrix`, `OAI.Erdos3.exists_realification_representatives_exp_bound`, `OAI.Erdos3.exists_realified_image_defining_matrix`, `OAI.Erdos3.exists_small_bounded_spanning_family`, `OAI.Erdos3.exists_submodule_block_quotient_projection`, `OAI.Erdos3.exists_uniform_conjugated_inner_grid`, `OAI.Erdos3.exists_vectorPolynomial_subspace_separation`, `OAI.Erdos3.externalNetMesh`, `OAI.Erdos3.externalNetMesh_error`, `OAI.Erdos3.externalNetMesh_inverse_bound`, `OAI.Erdos3.externalNetMesh_pos`, `OAI.Erdos3.extractedInitialParameter`, `OAI.Erdos3.extractedInitialParameter_controls`, `OAI.Erdos3.extractedInitialParameter_products`, `OAI.Erdos3.finiteLieTrees_coordinate_height`, `OAI.Erdos3.hasLayerSamplingRank_homogeneousPart_iff`, `OAI.Erdos3.hasLayerSamplingRank_translate_iff`, `OAI.Erdos3.horizontal_derivative_of_zero_parts`, `OAI.Erdos3.horizontal_parts_separation`, `OAI.Erdos3.horizontal_remove_zero`, `OAI.Erdos3.imageDefiningDenominator_le_exp`, `OAI.Erdos3.imageDefiningHeight`, `OAI.Erdos3.imageDefiningHeight_le_exp`, `OAI.Erdos3.imageDefiningHeight_pos`, `OAI.Erdos3.imageDefiningRow_bound_le_exp`, `OAI.Erdos3.imageSection_bound_le_exp`, `OAI.Erdos3.integerRowPolynomial_coefficientGrid`, `OAI.Erdos3.integerRowPolynomial_homogeneous_approximation_of_decomposition`, `OAI.Erdos3.ker_id_sub_comp_eq_range`, `OAI.Erdos3.layerRoundingBound`, `OAI.Erdos3.layerRoundingBound_le_exp`, `OAI.Erdos3.layerRoundingBound_mono_layer`, `OAI.Erdos3.le_currentLayerConstructionBudget`, `OAI.Erdos3.lieTreeHeight`, `OAI.Erdos3.lieTreeHeight_ge_input`, `OAI.Erdos3.lieTreeHeight_le_coordinateHeight`, `OAI.Erdos3.lieTreeHeight_le_exp`, `OAI.Erdos3.lieTreeHeight_mono`, `OAI.Erdos3.lieTreeHeight_step`, `OAI.Erdos3.lie_basis_bracket_height`, `OAI.Erdos3.linearMap_baseChange_basis`, `OAI.Erdos3.linearMap_baseChange_image_section`, `OAI.Erdos3.linearMap_baseChange_rightInverse`, `OAI.Erdos3.logCharacterMetricConstant`, `OAI.Erdos3.matrixBlockPart`, `OAI.Erdos3.matrixBlockPart_eq`, `OAI.Erdos3.matrixBlockPart_image_section`, `OAI.Erdos3.matrixBlockPart_off_block`, `OAI.Erdos3.matrixDenominator_allowance_le_exp`, `OAI.Erdos3.matrix_blockPart_mul`, `OAI.Erdos3.matrix_mulVec_fine_grid`, `OAI.Erdos3.matrix_mul_blockPart`, `OAI.Erdos3.norm_matrix_mulVec_le`, `OAI.Erdos3.pi_norm_restriction_le`, `OAI.Erdos3.rationalReconstructionLipschitzBound`, `OAI.Erdos3.realBCHPiEquiv`, `OAI.Erdos3.realBCHPiEquiv_mem_lattice`, `OAI.Erdos3.realSpanIntegerRowBound`, `OAI.Erdos3.real_column_span_fromCols`, `OAI.Erdos3.real_column_span_mem_iff`, `OAI.Erdos3.real_image_lattice_lift`, `OAI.Erdos3.real_image_section_denominator_bound`, `OAI.Erdos3.real_image_section_norm_bound`, `OAI.Erdos3.real_image_section_weighted_bound`, `OAI.Erdos3.real_matrix_image_section`, `OAI.Erdos3.real_matrix_image_section_apply`, `OAI.Erdos3.realificationMap_lattice_cover`, `OAI.Erdos3.realificationMap_mem_range_iff`, `OAI.Erdos3.realification_piRight_apply`, `OAI.Erdos3.samplingRank_le_real_column_span_of_decomposition`, `OAI.Erdos3.separationBudget`, `OAI.Erdos3.separationBudget_nonneg`, `OAI.Erdos3.separationBudget_small`, `OAI.Erdos3.shifted_center_power_bound`, `OAI.Erdos3.span_basis_brackets_layer`, `OAI.Erdos3.squarefreeStructureHeight`, `OAI.Erdos3.sum_basisBlockProjection`, `OAI.Erdos3.weightedLinearInverseMask`, `OAI.Erdos3.weightedLinearInverseMask_apply`, `OAI.Erdos3.weightedLinearInverseMask_entry`, `OAI.Erdos3.weightedLinearInverseMask_height`, `OAI.Erdos3.weightedLinearInverseMask_weighted`, `OAI.Erdos3.weighted_matrix_mulVec_bound`, `_private.Polynomial.RealPolynomialChartSubstitution.0.OAI.Erdos3.VectorPolynomial.lieHomOfLinearMap`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B088

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialChartSubstitution
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

variable {σ : Type*}

noncomputable def dualScalarEval (t h : σ → ℚ) : MvPolynomial σ ℚ →ₐ[ℚ] DualNumber ℚ :=
  MvPolynomial.aeval (fun i => algebraMap ℚ (DualNumber ℚ) (t i) + h i • DualNumber.eps)

@[simp] theorem dualScalarEval_X (t h : σ → ℚ) (i : σ) :
    dualScalarEval t h (MvPolynomial.X i) =
      algebraMap ℚ (DualNumber ℚ) (t i) + h i • DualNumber.eps := by
  simp only [dualScalarEval, MvPolynomial.aeval_X]

@[simp] theorem dualScalarEval_fst (t h : σ → ℚ) (p : MvPolynomial σ ℚ) :
    (dualScalarEval t h p).fst = MvPolynomial.aeval t p := by
  have he : (TrivSqZeroExt.fstHom ℚ ℚ ℚ).comp (dualScalarEval t h) = MvPolynomial.aeval t := by
    ext i
    simp [dualScalarEval, TrivSqZeroExt.algebraMap_eq_inl]
  exact congrArg (fun f : MvPolynomial σ ℚ →ₐ[ℚ] ℚ => f p) he

namespace VectorPolynomial

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def dualEvalLie (t h : σ → ℚ) : VectorPolynomial σ ℚ L →ₗ⁅ℚ⁆ DualLieAlgebra L :=
  LieAlgebra.ExtendScalars.map (dualScalarEval t h) (LieHom.id : L →ₗ⁅ℚ⁆ L)

@[simp] theorem dualEvalLie_tmul (t h : σ → ℚ) (p : MvPolynomial σ ℚ) (x : L) :
    dualEvalLie t h (p ⊗ₜ[ℚ] x) = dualScalarEval t h p ⊗ₜ[ℚ] x := rfl

theorem dualEvalLie_base (t h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    dualBaseLinear (dualEvalLie t h p) = eval t p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q x => rw [dualEvalLie_tmul, dualBaseLinear_tmul, dualScalarEval_fst, eval_tmul]
  | add p q hp hq => simp only [map_add, hp, hq]

noncomputable def directionalDerivative [Fintype σ] (h : σ → ℚ) :
    VectorPolynomial σ ℚ L →ₗ[ℚ] VectorPolynomial σ ℚ L :=
  ∑ i, h i • (MvPolynomial.pderiv i).toLinearMap.rTensor L

@[simp] theorem directionalDerivative_tmul [Fintype σ]
    (h : σ → ℚ) (p : MvPolynomial σ ℚ) (x : L) :
    directionalDerivative h (p ⊗ₜ[ℚ] x) =
      ∑ i, h i • (MvPolynomial.pderiv i p ⊗ₜ[ℚ] x) := by
  simp [directionalDerivative]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem pderiv_lie (i : σ) (p q : VectorPolynomial σ ℚ L) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor L ⁅p, q⁆ =
      ⁅(MvPolynomial.pderiv i).toLinearMap.rTensor L p, q⁆ +
        ⁅p, (MvPolynomial.pderiv i).toLinearMap.rTensor L q⁆ := by
  induction p using TensorProduct.induction_on with
  | zero =>
    simp only [zero_lie (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L), map_zero, zero_add]
  | tmul a x =>
    induction q using TensorProduct.induction_on with
    | zero =>
      simp only [lie_zero (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L), map_zero, zero_add]
    | tmul b y =>
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, LinearMap.rTensor_tmul]
      change MvPolynomial.pderiv i (a * b) ⊗ₜ[ℚ] ⁅x, y⁆ =
        (MvPolynomial.pderiv i a * b) ⊗ₜ[ℚ] ⁅x, y⁆ +
          (a * MvPolynomial.pderiv i b) ⊗ₜ[ℚ] ⁅x, y⁆
      rw [MvPolynomial.pderiv_mul, TensorProduct.add_tmul]
    | add q r hq hr =>
      simp only [LieRing.lie_add, map_add, hq, hr]
      abel
  | add p r hp hr =>
    simp only [LieRing.add_lie, map_add, hp, hr]
    abel

theorem directionalDerivative_lie [Fintype σ] (h : σ → ℚ) (p q : VectorPolynomial σ ℚ L) :
    directionalDerivative h ⁅p, q⁆ =
      ⁅directionalDerivative h p, q⁆ + ⁅p, directionalDerivative h q⁆ := by
  simp only [directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply,
    pderiv_lie, smul_add, Finset.sum_add_distrib,
    sum_lie (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L),
    lie_sum (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L),
    smul_lie (R := ℚ) (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L),
    lie_smul (R := ℚ) (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L)]

theorem directionalDerivative_direction_add [Fintype σ]
    (h k : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalDerivative (h + k) p = directionalDerivative h p + directionalDerivative k p := by
  simp only [directionalDerivative, Pi.add_apply, add_smul, Finset.sum_add_distrib,
    LinearMap.add_apply]

theorem directionalDerivative_direction_smul [Fintype σ]
    (r : ℚ) (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalDerivative (r • h) p = r • directionalDerivative h p := by
  simp only [directionalDerivative, Pi.smul_apply, smul_eq_mul, mul_smul,
    ← Finset.smul_sum, LinearMap.smul_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

abbrev PolynomialGroup (σ : Type*) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :=
  NilpotentLieBCHGroup (VectorPolynomial σ ℚ L) s (VectorPolynomial.lowerCentralSeries_eq_bot hnil)

noncomputable def polynomialValueHom (t : σ → ℚ) :
    PolynomialGroup σ hnil →* NilpotentLieBCHGroup L s hnil :=
  NilpotentLieBCHGroup.map (evalLie t)

noncomputable def polynomialFirstJetHom (t h : σ → ℚ) : PolynomialGroup σ hnil →* DualGroup hnil :=
  NilpotentLieBCHGroup.map (dualEvalLie t h)

@[simp] theorem polynomialFirstJet_base (t h : σ → ℚ) (P : PolynomialGroup σ hnil) :
    dualBaseHom (polynomialFirstJetHom t h P) = polynomialValueHom t P := by
  apply ext
  exact dualEvalLie_base t h P.coord

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def formalPolynomialJetLie (i : σ) :
    VectorPolynomial σ ℚ L →ₗ⁅ℚ⁆ DualLieAlgebra (VectorPolynomial σ ℚ L) where
  toLinearMap := dualConstantLie.toLinearMap +
    dualInfinitesimal.comp ((MvPolynomial.pderiv i).toLinearMap.rTensor L)
  map_lie' {P Q} := by
    change dualConstantLie ⁅P, Q⁆ +
      dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L ⁅P, Q⁆) =
      ⁅dualConstantLie P + dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L P),
        dualConstantLie Q + dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L Q)⁆
    apply dual_ext
    · simp only [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal,
        add_zero, dualBaseLinear_lie]
    · simp only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal,
        zero_add, dualTangentLinear_lie, dualBaseLinear_constant,
        dualBaseLinear_infinitesimal, add_zero]
      rw [pderiv_lie]
      exact add_comm _ _

noncomputable def formalPolynomialJetHom (i : σ) :
    PolynomialGroup σ hnil →* DualGroup (VectorPolynomial.lowerCentralSeries_eq_bot (σ := σ) hnil) :=
  NilpotentLieBCHGroup.map (formalPolynomialJetLie i)

@[simp] theorem formalPolynomialJet_base (i : σ) (P : PolynomialGroup σ hnil) :
    dualBaseLinear (formalPolynomialJetHom i P).coord = P.coord := by
  change dualBaseLinear (dualConstantLie P.coord +
    dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord)) = _
  rw [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem formalPolynomialJet_tangent (i : σ) (P : PolynomialGroup σ hnil) :
    dualTangentLinear (formalPolynomialJetHom i P).coord =
      (MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord := by
  change dualTangentLinear (dualConstantLie P.coord +
    dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord)) = _
  rw [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

@[simp] theorem formalPolynomialJet_baseHom (i : σ) (P : PolynomialGroup σ hnil) :
    dualBaseHom (formalPolynomialJetHom i P) = P :=
  NilpotentLieBCHGroup.ext (formalPolynomialJet_base i P)

noncomputable def formalLogDerivative (i : σ) (P : PolynomialGroup σ hnil) :
    VectorPolynomial σ ℚ L := dualLogDerivative (formalPolynomialJetHom i P)

@[simp] theorem formalLogDerivative_one (i : σ) :
    formalLogDerivative i (1 : PolynomialGroup σ hnil) = 0 := by
  simp only [formalLogDerivative, map_one, dualLogDerivative_one]

theorem formalLogDerivative_remove (i : σ) (A P B : PolynomialGroup σ hnil) :
    formalLogDerivative i (A⁻¹ * P * B⁻¹) =
      dualAdjoint A⁻¹ (formalLogDerivative i P - formalLogDerivative i A) -
        dualAdjoint (A⁻¹ * P * B⁻¹) (formalLogDerivative i B) := by
  have h := dualLogDerivative_remove
    (formalPolynomialJetHom i A) (formalPolynomialJetHom i P) (formalPolynomialJetHom i B)
  simpa only [map_mul, map_inv, formalPolynomialJet_baseHom, formalLogDerivative] using h

theorem formalLogDerivative_mem_of_invariant
    (U : LieSubalgebra ℚ (VectorPolynomial σ ℚ L))
    (V : Submodule ℚ (VectorPolynomial σ ℚ L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (i : σ) (P : PolynomialGroup σ hnil) (hP : P.coord ∈ U)
    (hD : (MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord ∈ V) :
    formalLogDerivative i P ∈ V := by
  apply dualLogDerivative_mem_of_invariant U V hUV (formalPolynomialJetHom i P)
  · simpa only [formalPolynomialJet_base] using hP
  · simpa only [formalPolynomialJet_tangent] using hD

def PolynomialDerivativeSystem (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L) : Prop :=
  ∀ i, formalLogDerivative i P = small i + dualAdjoint P (rational i) + extra i

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realPolynomialValueHom (t : σ → ℝ) :
    PolynomialGroup σ hnil →* NilpotentLieBCHGroup L s hnil :=
  NilpotentLieBCHGroup.map (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t)

@[simp] theorem realPolynomialValueHom_coord (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    (realPolynomialValueHom t P).coord = eval₂ t P.coord := rfl

noncomputable def realPolynomialJet (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    DualGroup hnil :=
  ⟨dualConstantLie (eval₂ t P.coord) +
    dualInfinitesimal (eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord))⟩

@[simp] theorem realPolynomialJet_base (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    dualBaseLinear (realPolynomialJet i t P).coord = eval₂ t P.coord := by
  change dualBaseLinear (dualConstantLie _ + dualInfinitesimal _) = _
  rw [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem realPolynomialJet_tangent (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    dualTangentLinear (realPolynomialJet i t P).coord =
      eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord) := by
  change dualTangentLinear (dualConstantLie _ + dualInfinitesimal _) = _
  rw [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

@[simp] theorem realPolynomialJet_baseHom (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    dualBaseHom (realPolynomialJet i t P) = realPolynomialValueHom t P :=
  NilpotentLieBCHGroup.ext (realPolynomialJet_base i t P)

theorem eval₂_formalLogDerivative (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    eval₂ t (formalLogDerivative i P) = dualLogDerivative (realPolynomialJet i t P) := by
  have h := dualLinearLift_logDerivative hnil ⊤ (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t)
    (eval₂ t) (fun a b _ => (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t).map_lie a b)
    (formalPolynomialJetHom i P) (by trivial)
  simp only [dualLinearLift_apply, formalPolynomialJet_base, formalPolynomialJet_tangent,
    eval₂Lie_apply] at h
  exact h

theorem eval₂_dualAdjoint (t : σ → ℝ) (P : PolynomialGroup σ hnil)
    (Q : VectorPolynomial σ ℚ L) :
    eval₂ t (dualAdjoint P Q) = dualAdjoint (realPolynomialValueHom t P) (eval₂ t Q) := by
  have h := map_dualAdjoint (hM := hnil) (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t) P Q
  simp only [eval₂Lie_apply] at h
  exact h

theorem PolynomialDerivativeSystem.real_evaluation (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L)
    (hsystem : PolynomialDerivativeSystem P small rational extra) (i : σ) (t : σ → ℝ) :
    dualLogDerivative (realPolynomialJet i t P) = eval₂ t (small i) +
      dualAdjoint (realPolynomialValueHom t P) (eval₂ t (rational i)) + eval₂ t (extra i) := by
  have h := congrArg (eval₂ t) (hsystem i)
  simpa only [eval₂_formalLogDerivative, map_add, eval₂_dualAdjoint] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ υ V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]

noncomputable def realCoefficientEquiv :
    VectorPolynomial σ ℚ V ≃ₗ[ℚ] VectorPolynomial σ ℝ V :=
  (coefficients (σ := σ) (R := ℚ) (V := V)).trans
    ((coefficients (σ := σ) (R := ℝ) (V := V)).restrictScalars ℚ).symm

@[simp] theorem coefficients_realCoefficientEquiv (p : VectorPolynomial σ ℚ V) :
    coefficients (realCoefficientEquiv p) = coefficients p := by
  simp [realCoefficientEquiv]

@[simp] theorem coefficients_realCoefficientEquiv_symm (p : VectorPolynomial σ ℝ V) :
    coefficients (realCoefficientEquiv.symm p) = coefficients p := by
  simp [realCoefficientEquiv]

@[simp] theorem realCoefficientEquiv_monomial (α : σ →₀ ℕ) (v : V) :
    realCoefficientEquiv (monomial (R := ℚ) α v) = monomial (R := ℝ) α v := by
  apply coefficients.injective
  simp

theorem eval_realCoefficientEquiv (x : σ → ℝ) (p : VectorPolynomial σ ℚ V) :
    eval x (realCoefficientEquiv p) = eval₂ x p := by
  classical
  rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, realCoefficientEquiv_monomial, eval_monomial, eval₂_monomial]

theorem eval₂_realCoefficientEquiv_symm (x : σ → ℝ) (p : VectorPolynomial σ ℝ V) :
    eval₂ x (realCoefficientEquiv.symm p) = eval x p := by
  obtain ⟨q, rfl⟩ := realCoefficientEquiv.surjective p
  rw [LinearEquiv.symm_apply_apply, eval_realCoefficientEquiv]

noncomputable def realChartSubstitute (f : σ → MvPolynomial τ ℝ) :
    VectorPolynomial σ ℚ V →ₗ[ℚ] VectorPolynomial τ ℚ V :=
  realCoefficientEquiv.symm.toLinearMap.comp
    (((substitute f).restrictScalars ℚ).comp realCoefficientEquiv.toLinearMap)

theorem coefficients_realChartSubstitute (f : σ → MvPolynomial τ ℝ)
    (p : VectorPolynomial σ ℚ V) (α : τ →₀ ℕ) :
    coefficients (realChartSubstitute f p) α =
      ∑ β ∈ (coefficients p).support,
        (MvPolynomial.aeval f (MvPolynomial.monomial β (1 : ℝ))).coeff α •
          coefficients p β := by
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, coefficients_realCoefficientEquiv_symm,
    coefficients_substitute, coefficients_realCoefficientEquiv]

theorem eval₂_realChartSubstitute (f : σ → MvPolynomial τ ℝ)
    (x : τ → ℝ) (p : VectorPolynomial σ ℚ V) :
    eval₂ x (realChartSubstitute f p) =
      eval₂ (fun i => MvPolynomial.eval x (f i)) p := by
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, eval₂_realCoefficientEquiv_symm,
    eval_substitute, MvPolynomial.aeval_eq_eval, eval_realCoefficientEquiv]

theorem realChartSubstitute_comp (f : σ → MvPolynomial τ ℝ)
    (g : τ → MvPolynomial υ ℝ) (p : VectorPolynomial σ ℚ V) :
    realChartSubstitute g (realChartSubstitute f p) =
      realChartSubstitute (fun i => MvPolynomial.aeval g (f i)) p := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro x
  rw [map_sub, eval₂_realChartSubstitute, eval₂_realChartSubstitute,
    eval₂_realChartSubstitute]
  apply sub_eq_zero.mpr
  congr 2
  funext i
  change MvPolynomial.aeval (fun j => MvPolynomial.eval x (g j)) (f i) =
    MvPolynomial.aeval x (MvPolynomial.aeval g (f i))
  rw [MvPolynomial.comp_aeval_apply]
  rfl

theorem eval₂_normalizedRealPolynomialChart {U B : Type*}
    (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (u : U → ℝ) (b : B → ℝ) (p : VectorPolynomial (U ⊕ B) ℚ V) :
    eval₂ (Sum.elim u b) (realChartSubstitute (normalizedRealPolynomialChart H A) p) =
      eval₂ (Sum.elim (fun i => u i / H i) (fun j => b j - MvPolynomial.eval u (A j))) p := by
  rw [eval₂_realChartSubstitute]
  simp only [normalizedRealPolynomialChart_eval]

end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]

theorem realChartSubstitute_lie (f : σ → MvPolynomial τ ℝ)
    (p q : VectorPolynomial σ ℚ L) :
    realChartSubstitute f ⁅p, q⁆ = ⁅realChartSubstitute f p, realChartSubstitute f q⁆ := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro x
  rw [map_sub]
  apply sub_eq_zero.mpr
  rw [eval₂_realChartSubstitute]
  change eval₂Lie (R := ℚ) (fun i => MvPolynomial.eval x (f i)) ⁅p, q⁆ =
    eval₂Lie (R := ℚ) x ⁅realChartSubstitute f p, realChartSubstitute f q⁆
  rw [LieHom.map_lie, LieHom.map_lie]
  simp only [eval₂Lie_apply, eval₂_realChartSubstitute]

attribute [local irreducible] realChartSubstitute

def lieHomOfLinearMap {A B : Type*} [LieRing A] [LieAlgebra ℚ A]
    [LieRing B] [LieAlgebra ℚ B] (g : A →ₗ[ℚ] B)
    (hg : ∀ x y, g ⁅x, y⁆ = ⁅g x, g y⁆) : A →ₗ⁅ℚ⁆ B :=
  ⟨g, fun {x y} => hg x y⟩

noncomputable def realChartSubstituteLie (f : σ → MvPolynomial τ ℝ) :
    VectorPolynomial σ ℚ L →ₗ⁅ℚ⁆ VectorPolynomial τ ℚ L :=
  lieHomOfLinearMap (realChartSubstitute f) (realChartSubstitute_lie f)

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ}
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def realPolynomialChartSubstitution (f : σ → MvPolynomial τ ℝ) :
    PolynomialGroup σ hnil →* PolynomialGroup τ hnil :=
  NilpotentLieBCHGroup.map (realChartSubstituteLie f)

@[simp] theorem realPolynomialChartSubstitution_coord (f : σ → MvPolynomial τ ℝ)
    (p : PolynomialGroup σ hnil) :
    (realPolynomialChartSubstitution hnil f p).coord = realChartSubstitute f p.coord := rfl

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedReconstruction
namespace OAI

section

namespace Erdos3

variable {σ τ : Type*}

noncomputable def weightedLinearInverseMask
    (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ)) (v : τ → ℕ) (w : σ → ℕ) :
    (σ → ℚ) →ₗ[ℚ] (τ → ℚ) where
  toFun x j := B (coordinateWeightProjection w (v j) x) j
  map_add' x y := by funext j; simp only [map_add, Pi.add_apply]
  map_smul' r x := by funext j; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

theorem weightedLinearInverseMask_apply [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ))
    (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (hBA : ∀ x, B (A x) = x) (x : τ → ℚ) :
    weightedLinearInverseMask B v w (A x) = x := by
  funext j
  change B (fun i => if w i = v j then A x i else 0) j = x j
  rw [← linearMap_coordinateGradeProjection A v w hweight, hBA]
  simp

theorem weightedLinearInverseMask_entry [DecidableEq σ]
    (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (i : σ) (j : τ) :
    weightedLinearInverseMask B v w (Pi.single i 1) j =
      if w i = v j then B (Pi.single i 1) j else 0 := by
  have hproj : coordinateWeightProjection w (v j) (Pi.single i 1) =
      if w i = v j then Pi.single i 1 else 0 := by
    funext k
    by_cases hk : k = i
    · subst k
      by_cases hij : w i = v j <;> simp [coordinateWeightProjection, hij]
    · by_cases hij : w i = v j <;>
        simp [coordinateWeightProjection, hij, Pi.single_eq_of_ne hk]
  change B (coordinateWeightProjection w (v j) (Pi.single i 1)) j = _
  rw [hproj]
  split_ifs <;> simp

theorem weightedLinearInverseMask_weighted [DecidableEq σ]
    (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (i : σ) (j : τ) (hij : w i ≠ v j) :
    weightedLinearInverseMask B v w (Pi.single i 1) j = 0 := by
  rw [weightedLinearInverseMask_entry, if_neg hij]

theorem weightedLinearInverseMask_height [DecidableEq σ]
    (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    {H : ℕ} (hB : ∀ j i, RationalHeightLE (B (Pi.single i 1) j) H)
    (i : σ) (j : τ) :
    RationalHeightLE (weightedLinearInverseMask B v w (Pi.single i 1) j) H := by
  rw [weightedLinearInverseMask_entry]
  split_ifs
  · exact hB j i
  · exact rationalHeightLE_zero ((B (Pi.single i 1) j).den_pos.trans_le (hB j i).2)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem exists_bounded_linear_section (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (hφ : Function.Surjective φ) {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) :
    ∃ σ : M →ₗ[ℚ] L, Function.RightInverse σ φ ∧
      ∀ i j, RationalHeightLE (e.repr (σ (f j)) i) (rationalSolveHeight (Fintype.card κ) H) := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section (LinearMap.toMatrix e f φ)
    (basisMatrix_surjective e f φ hφ) hH (by
      intro i j
      rw [LinearMap.toMatrix_apply]
      exact hentries i j)
  refine ⟨Matrix.toLin f e S, basisMatrix_section e f φ S hS, ?_⟩
  intro i j
  have heq := LinearMap.toMatrix_apply f e (Matrix.toLin f e S) i j
  rw [LinearMap.toMatrix_toLin] at heq
  rw [← heq]
  exact hSH i j

omit [Fintype ι] [Fintype κ] in

theorem linearMap_baseChange_basis (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (i : κ) (j : ι) :
    (f.baseChange ℝ).repr (φ.baseChange ℝ ((e.baseChange ℝ) j)) i =
      (f.repr (φ (e j)) i : ℝ) := by
  simp only [Basis.baseChange_apply, LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

theorem linearMap_baseChange_rightInverse (φ : L →ₗ[ℚ] M) (σ : M →ₗ[ℚ] L)
    (hσ : Function.RightInverse σ φ) :
    Function.RightInverse (σ.baseChange ℝ) (φ.baseChange ℝ) := by
  have heq : φ.comp σ = LinearMap.id := LinearMap.ext hσ
  have heqR := congrArg (fun T : M →ₗ[ℚ] M => T.baseChange ℝ) heq
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at heqR
  intro x
  exact DFunLike.congr_fun heqR x

theorem exists_bounded_realified_linear_section (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (hφ : Function.Surjective φ) {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) :
    ∃ σ : (ℝ ⊗[ℚ] M) →ₗ[ℝ] (ℝ ⊗[ℚ] L),
      Function.RightInverse σ (φ.baseChange ℝ) ∧
      ∀ i j, |(e.baseChange ℝ).repr (σ ((f.baseChange ℝ) j)) i| ≤
        (rationalSolveHeight (Fintype.card κ) H : ℝ) := by
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_section e f φ hφ hH hentries
  refine ⟨σ.baseChange ℝ, linearMap_baseChange_rightInverse φ σ hσ, ?_⟩
  intro i j
  rw [linearMap_baseChange_basis]
  exact (hσH i j).abs_real_le

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem exists_bounded_rational_image_section {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ S : Matrix κ ι ℚ, A * S * A = A ∧
      ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H) := by
  classical
  obtain ⟨r, hr, rows, _, hsurj, hker⟩ := exists_independent_defining_rows A
  let R := A.submatrix rows id
  let T := (1 : Matrix ι ι ℚ).submatrix rows id
  have hTA : T * A = R := by
    ext i j
    simp [T, R, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply]
  obtain ⟨U, hU, hUH⟩ := exists_bounded_rational_section R hsurj hH (fun i j => hA (rows i) j)
  let S := U * T
  have hpoint (x : κ → ℚ) : A *ᵥ (S *ᵥ (A *ᵥ x)) = A *ᵥ x := by
    have hzero : R *ᵥ (S *ᵥ (A *ᵥ x) - x) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      have hm : R * S * A = R := by
        dsimp [S]
        rw [← Matrix.mul_assoc, hU, Matrix.one_mul, hTA]
      rw [hm, sub_self]
    have hmem : S *ᵥ (A *ᵥ x) - x ∈ LinearMap.ker A.mulVecLin := by
      rw [← hker]
      exact hzero
    change A *ᵥ (S *ᵥ (A *ᵥ x) - x) = 0 at hmem
    rw [Matrix.mulVec_sub, sub_eq_zero] at hmem
    exact hmem
  refine ⟨S, Matrix.ext_iff_mulVec.mpr (fun x => by
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using hpoint x), ?_⟩
  have hT : ∀ i j, RationalHeightLE (T i j) 1 := by
    intro i j
    by_cases hij : rows i = j
    · simpa [T, Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
    · simpa [T, Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
  intro i j
  have hs := rationalHeightLE_matrix_mul U T hUH hT i j
  apply hs.mono
  simp only [Fintype.card_fin, mul_one]
  apply le_trans _ (rationalKernelHeight_mono hH hr)
  unfold rationalKernelHeight
  apply Nat.mul_le_mul (by omega)
  apply pow_le_pow_left₀ (Nat.zero_le _)
  exact le_mul_of_one_le_right (Nat.zero_le _) hH

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem exists_bounded_linear_image_section (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) :
    ∃ σ : M →ₗ[ℚ] L, (φ.comp σ).comp φ = φ ∧
      ∀ i j, RationalHeightLE (e.repr (σ (f j)) i) (rationalKernelHeight (Fintype.card κ) H) := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section (LinearMap.toMatrix e f φ) hH
    (by intro i j; rw [LinearMap.toMatrix_apply]; exact hentries i j)
  refine ⟨Matrix.toLin f e S, ?_, ?_⟩
  · apply (LinearMap.toMatrix e f).injective
    rw [LinearMap.toMatrix_comp e f f, LinearMap.toMatrix_comp f e f, LinearMap.toMatrix_toLin]
    exact hS
  · intro i j
    have heq := LinearMap.toMatrix_apply f e (Matrix.toLin f e S) i j
    rw [LinearMap.toMatrix_toLin] at heq
    rw [← heq]
    exact hSH i j

theorem linearMap_baseChange_image_section (φ : L →ₗ[ℚ] M) (σ : M →ₗ[ℚ] L)
    (hσ : (φ.comp σ).comp φ = φ) :
    ((φ.baseChange ℝ).comp (σ.baseChange ℝ)).comp (φ.baseChange ℝ) = φ.baseChange ℝ := by
  simpa only [LinearMap.baseChange_comp] using
    congrArg (fun T : L →ₗ[ℚ] M => T.baseChange ℝ) hσ

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ}

theorem exists_bounded_filtered_section
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {k | j ≤ τ k}))
    (φ : L →ₗ[ℚ] M)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) :
    ∃ S : M →ₗ[ℚ] L,
      Function.RightInverse S φ ∧
      (∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) ∧
      ∀ i k, RationalHeightLE (b.repr (S (c k)) i)
        (rationalKernelHeight (Fintype.card κ) H) := by
  classical
  have lifts (k : κ) : ∃ x : L,
      x ∈ F.layer (τ k) ∧ φ x = c k ∧
        ∀ i, RationalHeightLE (b.repr x i) (rationalKernelHeight (Fintype.card κ) H) := by
    let P := basisCoordinateProjection b {i | τ k ≤ ω i}
    have hmasked : ∀ a i, RationalHeightLE (c.repr ((φ.comp P) (b i)) a) H := by
      intro a i
      change RationalHeightLE (c.repr (φ (basisCoordinateProjection b {i | τ k ≤ ω i} (b i))) a) H
      rw [basisCoordinateProjection_basis]
      split_ifs
      · exact hentries a i
      · simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
    obtain ⟨T, hT, hTH⟩ := exists_bounded_linear_image_section b c (φ.comp P) hH hmasked
    have hck : c k ∈ G.layer (τ k) := by
      rw [hG]
      exact Submodule.subset_span ⟨k, (show τ k ≤ τ k from le_rfl), rfl⟩
    obtain ⟨y, hy, hφy⟩ := hsurj (τ k) (c k) hck
    have hPy : P y = y := by
      apply basisCoordinateProjection_eq_self
      rwa [← hF]
    have himage : (φ.comp P) y = c k := by
      change φ (P y) = c k
      rw [hPy, hφy]
    have hright : (φ.comp P) (T (c k)) = c k := by
      have ht := congrArg (fun A : L →ₗ[ℚ] M => A y) hT
      change (φ.comp P) (T ((φ.comp P) y)) = (φ.comp P) y at ht
      simpa only [himage] using ht
    refine ⟨P (T (c k)), ?_, hright, ?_⟩
    · rw [hF]
      exact basisCoordinateProjection_mem_span b _ _
    · intro i
      change RationalHeightLE
        (b.repr (basisCoordinateProjection b {i | τ k ≤ ω i} (T (c k))) i) _
      rw [basisCoordinateProjection_repr]
      split_ifs
      · exact hTH i k
      · exact rationalHeightLE_zero (rationalKernelHeight_pos _ hH)
  choose v hmem hright hheight using lifts
  let S := c.constr ℚ v
  have hS (k : κ) : S (c k) = v k := c.constr_basis ℚ v k
  refine ⟨S, ?_, ?_, ?_⟩
  · have hcomp : φ.comp S = LinearMap.id := by
      apply c.ext
      intro k
      change φ (S (c k)) = c k
      rw [hS, hright]
    intro y
    exact congrArg (fun A : M →ₗ[ℚ] M => A y) hcomp
  · intro j y hy
    have hle : G.layer j ≤ (F.layer j).comap S := by
      rw [hG]
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      change S (c k) ∈ F.layer j
      rw [hS]
      exact F.antitone hk (hmem k)
    exact hle hy
  · intro i k
    rw [hS]
    exact hheight k i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped Matrix

variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]

theorem exists_controlled_coordinate_leftInverse
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j i, RationalHeightLE (A (Pi.single j 1) i) H) :
    ∃ B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ), (∀ x, B (A x) = x) ∧
      ∀ i j, RationalHeightLE (B (Pi.single i 1) j)
        (rationalKernelHeight (Fintype.card σ) H) := by
  let D := LinearMap.toMatrix' A
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section D hH
    (fun i j => hentries j i)
  refine ⟨S.mulVecLin, ?_, ?_⟩
  · intro x
    apply hA
    have hx : D *ᵥ (S *ᵥ (D *ᵥ x)) = D *ᵥ x := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hS]
    simpa only [D, LinearMap.toMatrix'_mulVec, Matrix.mulVecLin_apply] using hx
  · intro i j
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using hSH j i

theorem exists_controlled_weighted_leftInverse
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (hA : Function.Injective A) {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j i, RationalHeightLE (A (Pi.single j 1) i) H) :
    ∃ B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ),
      (∀ x, B (A x) = x) ∧
      (∀ i j, w i ≠ v j → B (Pi.single i 1) j = 0) ∧
      (∀ i j, RationalHeightLE (B (Pi.single i 1) j)
        (rationalKernelHeight (Fintype.card σ) H)) := by
  obtain ⟨B, hBA, hBH⟩ := exists_controlled_coordinate_leftInverse A hA hH hentries
  refine ⟨weightedLinearInverseMask B v w, ?_, ?_, ?_⟩
  · exact weightedLinearInverseMask_apply A B v w hweight hBA
  · exact weightedLinearInverseMask_weighted B v w
  · exact weightedLinearInverseMask_height B v w (fun j i => hBH i j)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped NNReal TensorProduct

noncomputable def rationalReconstructionLipschitzBound (s d n H : ℕ) (ℓ B : ℝ≥0) : ℝ≥0 :=
  let C := bchLogMetricConstant s n H 1
  let K := coordinateLipschitzBound d n (rationalSolveHeight n H) * (n + 1) * C
  max (ℓ * (2 * K)) (2 * B / (C⁻¹ / 2))

variable {ι κ L M E : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

open NilpotentLieBCHGroup

theorem realificationMap_lattice_cover (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Λ : Subgroup (NilpotentLieBCHGroup M t hM))
    (hcover : Λ ≤ Γ.map (mapOfSteps φ)) :
    Λ.map realificationHom ≤ (Γ.map realificationHom).map (realificationMap (hnil := hL) (hM := hM) φ) := by
  rintro g ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hxy⟩ := hcover hy
  refine ⟨realificationHom x, ⟨x, hx, rfl⟩, ?_⟩
  rw [realificationMap_realificationHom_ofSteps, hxy]

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] [NormedAddCommGroup E]

theorem exists_lipschitz_realification_reconstruction
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : Function.Surjective φ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Λ : Subgroup (NilpotentLieBCHGroup M t hM))
    (hcover : Λ ≤ Γ.map (mapOfSteps φ))
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (hH : 1 ≤ H)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hΛ : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (hstructure : ∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H)
    (u : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL) ⧸
      Γ.map realificationHom) → E)
    (hker : ∀ k ∈ (realificationMap (hnil := hL) (hM := hM) φ).ker, ∀ x,
      u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x))
    (ℓ B : ℝ≥0)
    (hu : letI := realificationQuotientMetricSpace e Γ l hl hΓ; LipschitzWith ℓ u)
    (hub : ∀ x, ‖u x‖ ≤ B) :
    letI := realificationQuotientMetricSpace f Λ m hm hΛ
    ∃ v : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM) ⧸
      Λ.map realificationHom) → E,
      (∀ x, v (QuotientGroup.mk (realificationMap (hnil := hL) (hM := hM) φ x)) = u (QuotientGroup.mk x)) ∧
      LipschitzWith (rationalReconstructionLipschitzBound t (Fintype.card ι) (Fintype.card κ) H ℓ B) v ∧
      ∀ y, ‖v y‖ ≤ B := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (e.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] M) := (f.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hL) (e.baseChange ℝ)
  let := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := realification_lowerCentralSeries_eq_bot hL) (e.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
  obtain ⟨σ, hσ, hσB⟩ := exists_bounded_realified_linear_section e f φ.toLinearMap hφ hH hentries
  have hsurj : Function.Surjective (realificationMap (hnil := hL) (hM := hM) φ) := by
    intro g
    exact ⟨⟨σ g.coord⟩, ext (hσ g.coord)⟩
  let C := bchLogMetricConstant t (Fintype.card κ) H 1
  let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ)
    (rationalSolveHeight (Fintype.card κ) H) * ((Fintype.card κ : ℝ≥0) + 1) * C
  have hC : 0 < C := bchLogMetricConstant_pos t (Fintype.card κ) H 1
  have hlift := exists_local_metric_lifts_of_section
    (hnil := realification_lowerCentralSeries_eq_bot hL) (hM := realification_lowerCentralSeries_eq_bot hM)
    (e.baseChange ℝ) (f.baseChange ℝ) (realificationLieHom φ) σ hσ
    (rationalSolveHeight (Fintype.card κ) H) hσB (lieStructureConstants f)
    (fun i j k => (realLieBasis_structure f i j k).symm) hstructure
  exact exists_lipschitz_observable_reconstruction (realificationMap (hnil := hL) (hM := hM) φ) hsurj
    (Γ.map realificationHom) (Λ.map realificationHom)
    (realification_subgroup_closed_discrete e Γ l hl hΓ).1
    (realification_subgroup_closed_discrete f Λ m hm hΛ).1
    (realificationMap_lattice_cover φ Γ Λ hcover) u hker ℓ K B C⁻¹ (inv_pos.mpr hC) hu hub hlift

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReconstructionBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_rationalReconstructionLipschitzBound_exp (s : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ (d n H : ℕ) (ℓ B : ℝ≥0) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (n : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (ℓ : ℝ) ≤ Real.exp p → (B : ℝ) ≤ Real.exp p →
      (rationalReconstructionLipschitzBound s d n H ℓ B : ℝ) ≤ Real.exp ((p + N) ^ N) := by
  obtain ⟨D, hD, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s 0
  let N := D + 20
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro d n H ℓ B p hp hd hn hH hℓ hB
  let t := p + N
  let q := t ^ (N - 1)
  have ht : 5 ≤ t := by
    have : (20 : ℝ) ≤ N := by exact_mod_cast (show 20 ≤ N by dsimp [N]; omega)
    dsimp [t]
    linarith
  have hq1 : 1 ≤ q := one_le_pow₀ (by linarith : (1 : ℝ) ≤ t)
  have hpq : p ≤ q := by
    apply (show p ≤ t from le_add_of_nonneg_right (Nat.cast_nonneg N)).trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t)
      (show 1 ≤ N - 1 by dsimp [N]; omega)
  have hpe : Real.exp p ≤ Real.exp q := Real.exp_le_exp.mpr hpq
  have htwo : (2 : ℝ) ≤ Real.exp q := by
    linarith [Real.add_one_le_exp q]
  let C := bchLogMetricConstant s n H 1
  have hC : (C : ℝ) ≤ Real.exp q := by
    have hbc := (bchBoxCoordinateBound_le_bchBoxMetricConstant s n H 1).trans
      (hbox n H 1 p hp hn hH (by simp only [NNReal.coe_one, pow_zero]; exact Real.one_le_exp (by norm_num)))
    change bchBoxCoordinateBound s n H 1 ≤ Real.exp ((p + D) ^ D) at hbc
    have hqt : (p + D) ^ D + 1 ≤ q := by
      calc
        (p + D) ^ D + 1 ≤ t ^ D + t ^ D := by
          gcongr
          · dsimp [t, N]; push_cast; linarith
          · exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ t)
        _ ≤ t * t ^ D := by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ t) D]
        _ = t ^ (D + 1) := (pow_succ' t D).symm
        _ ≤ q := pow_le_pow_right₀ (by linarith) (by dsimp [N]; omega)
    change bchBoxCoordinateBound s n H 1 + 1 ≤ Real.exp q
    calc
      _ ≤ Real.exp ((p + D) ^ D) + Real.exp ((p + D) ^ D) := by
        linarith [Real.one_le_exp (by positivity : 0 ≤ (p + D) ^ D)]
      _ ≤ Real.exp ((p + D) ^ D) * Real.exp 1 := by
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        nlinarith [Real.exp_pos ((p + D) ^ D)]
      _ = Real.exp ((p + D) ^ D + 1) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hqt
  let A := coordinateLipschitzBound d n (rationalSolveHeight n H)
  have hA : (A : ℝ) ≤ Real.exp q := by
    have hpp : p ≤ (p + 2) ^ 5 := le_power_budget hp (by decide)
    have hA' := coordinateLipschitzBound_le_exp d n (rationalSolveHeight n H)
      (by positivity : 0 ≤ (p + 2) ^ 5) (hd.trans hpp) (hn.trans hpp)
      (by exact_mod_cast rationalSolveHeight_le_budget n H hp hn hH)
    apply hA'.trans
    apply Real.exp_le_exp.mpr
    apply (shifted_power_budget_le hp 5 2).trans
    change (p + 2) ^ 14 ≤ q
    calc
      _ ≤ t ^ 14 := pow_le_pow_left₀ (by linarith) (by dsimp [t, N]; push_cast; linarith) 14
      _ ≤ q := pow_le_pow_right₀ (by linarith) (by dsimp [N]; omega)
  have hdim : (n : ℝ) + 1 ≤ Real.exp q :=
    (show (n : ℝ) + 1 ≤ p + 1 by linarith).trans ((Real.add_one_le_exp p).trans hpe)
  have hfirst : (ℓ : ℝ) * (2 * ((A : ℝ) * ((n : ℝ) + 1) * C)) ≤ Real.exp (5 * q) := by
    calc
      _ ≤ Real.exp q * (Real.exp q * (Real.exp q * Real.exp q * Real.exp q)) := by
        gcongr
        · exact hℓ.trans hpe
      _ = Real.exp (5 * q) := by simp only [← Real.exp_add]; congr 1; ring
  have hsecond : 2 * (B : ℝ) / ((C : ℝ)⁻¹ / 2) ≤ Real.exp (5 * q) := by
    calc
      _ = 2 * 2 * (B : ℝ) * C := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
      _ ≤ Real.exp q * Real.exp q * Real.exp q * Real.exp q := by gcongr; exact hB.trans hpe
      _ = Real.exp (4 * q) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (5 * q) := Real.exp_le_exp.mpr (by linarith)
  have hmax : (rationalReconstructionLipschitzBound s d n H ℓ B : ℝ) ≤ Real.exp (5 * q) := by
    change max ((ℓ : ℝ) * (2 * ((A : ℝ) * ((n : ℝ) + 1) * C)))
      (2 * (B : ℝ) / ((C : ℝ)⁻¹ / 2)) ≤ _
    exact max_le hfirst hsecond
  apply hmax.trans
  apply Real.exp_le_exp.mpr
  calc
    5 * q ≤ t * q := mul_le_mul_of_nonneg_right ht (by dsimp [q]; positivity)
    _ = (p + N) ^ N := by dsimp [q, t]; rw [← pow_succ', Nat.sub_add_cancel (by dsimp [N]; omega)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ImageLatticeSubgroup
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix TensorProduct

theorem matrix_mulVec_fine_grid {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix ι κ ℚ) (l : ℕ) :
    scaledIntegerGrid (l * matrixDenominator S) ⊆ S.mulVec ⁻¹' scaledIntegerGrid l := by
  classical
  rintro y ⟨z, rfl⟩
  obtain ⟨w, hw⟩ := integralVector_denominator_mulVec S (fun j => (z j : ℚ)) ⟨z, fun _ => rfl⟩
  refine ⟨w, ?_⟩
  rw [Matrix.mulVec_smul]
  ext i
  have hi := hw i
  change (matrixDenominator S : ℚ) * (S *ᵥ fun j => (z j : ℚ)) i = (w i : ℚ) at hi
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
  rw [mul_assoc, hi]

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem real_image_lattice_lift [DecidableEq ι] [DecidableEq κ]
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M) (σ : M →ₗ[ℚ] L)
    (hσ : (φ.toLinearMap.comp σ).comp φ.toLinearMap = φ.toLinearMap)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Λ : Subgroup (NilpotentLieBCHGroup M s hM)) (l B : ℕ)
    (hΓ : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (hΛ : bchSubgroupCoordinates f Λ ⊆ scaledIntegerGrid B)
    (hdiv : l * matrixDenominator (LinearMap.toMatrix f e σ) ∣ B) :
    Λ.map realificationHom ⊓ (realificationMap (hnil := hL) (hM := hM) φ).range ≤
      (Γ.map realificationHom).map (realificationMap (hnil := hL) (hM := hM) φ) := by
  rintro g ⟨hg, himage⟩
  obtain ⟨γ, hγ, rfl⟩ := hg
  obtain ⟨x, hx⟩ := himage
  have hxcoord := congrArg NilpotentLieBCHGroup.coord hx
  change φ.toLinearMap.baseChange ℝ x.coord = (1 : ℝ) ⊗ₜ[ℚ] γ.coord at hxcoord
  have hsection := DFunLike.congr_fun (linearMap_baseChange_image_section φ.toLinearMap σ hσ) x.coord
  change φ.toLinearMap.baseChange ℝ (σ.baseChange ℝ (φ.toLinearMap.baseChange ℝ x.coord)) =
    φ.toLinearMap.baseChange ℝ x.coord at hsection
  rw [hxcoord] at hsection
  have hpre : φ (σ γ.coord) = γ.coord := by
    apply rationalLieInclusion_injective f
    change (1 : ℝ) ⊗ₜ[ℚ] φ (σ γ.coord) = (1 : ℝ) ⊗ₜ[ℚ] γ.coord
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul] at hsection
    exact hsection
  let a : NilpotentLieBCHGroup L s hL := ⟨σ γ.coord⟩
  have ha : a ∈ Γ := by
    apply (bchSubgroupCoordinates_repr e Γ a).mp
    apply hΓ
    have hy := scaledIntegerGrid_subset_of_dvd hdiv
      (hΛ ((bchSubgroupCoordinates_repr f Λ γ).mpr hγ))
    have hs := matrix_mulVec_fine_grid (LinearMap.toMatrix f e σ) l hy
    change LinearMap.toMatrix f e σ *ᵥ f.equivFun γ.coord ∈ scaledIntegerGrid l at hs
    rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply] at hs
    exact hs
  refine ⟨realificationHom a, ⟨a, ha, rfl⟩, ?_⟩
  rw [realificationMap_realificationHom]
  apply congrArg realificationHom
  exact ext hpre

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem exists_image_lattice_subgroup (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Δ : Subgroup (NilpotentLieBCHGroup M s hM))
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (hH : 1 ≤ H)
    (hΓ : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (hΔ : scaledIntegerGrid m ⊆ bchSubgroupCoordinates f Δ)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H) :
    ∃ (B : ℕ) (Λ : Subgroup (NilpotentLieBCHGroup M s hM)),
      0 < B ∧ m ∣ B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (Fintype.card κ ^ 3) *
        (m * (l * rationalKernelHeight (Fintype.card κ) H ^ (Fintype.card ι * Fintype.card κ))) ∧
      Λ ≤ Δ ∧ bchSubgroupCoordinates f Λ = scaledIntegerGrid B ∧
      Λ.map realificationHom ⊓ (realificationMap (hnil := hL) (hM := hM) φ).range ≤
        (Γ.map realificationHom).map (realificationMap (hnil := hL) (hM := hM) φ) := by
  classical
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_image_section e f φ.toLinearMap hH hentries
  let D := matrixDenominator (LinearMap.toMatrix f e σ)
  have hD : 0 < D := matrixDenominator_pos _
  have hDb : D ≤ rationalKernelHeight (Fintype.card κ) H ^ (Fintype.card ι * Fintype.card κ) := by
    apply matrixDenominator_le
    intro i j
    rw [LinearMap.toMatrix_apply]
    exact hσH i j
  let q := m * (l * D)
  have hq : 0 < q := Nat.mul_pos hm (Nat.mul_pos hl hD)
  have hΔq : scaledIntegerGrid q ⊆ bchSubgroupCoordinates f Δ :=
    (scaledIntegerGrid_subset_of_dvd (dvd_mul_right m (l * D))).trans hΔ
  obtain ⟨B, Λ, hB, hqB, hBb, hΛ, hgrid⟩ := exists_integral_grid_subgroup f hM Δ q hq hc hΔq
  refine ⟨B, Λ, hB, (dvd_mul_right m (l * D)).trans hqB, ?_, hΛ, hgrid, ?_⟩
  · exact hBb.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left m (Nat.mul_le_mul_left l hDb)))
  · apply real_image_lattice_lift e f φ σ hσ Γ Λ l B hΓ
    · exact hgrid.le
    · exact (dvd_mul_left (l * D) m).trans hqB

namespace NilpotentLieFiltration

theorem exists_image_lattice_cover (F : NilpotentLieFiltration M s)
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) (Δ : Subgroup F.Group)
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (hH : 1 ≤ H)
    (hΓ : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (hΔin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates f Δ)
    (hΔout : bchSubgroupCoordinates f Δ ⊆ denominatorGrid m)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H) :
    ∃ (B : ℕ) (Λ : Subgroup F.Group),
      0 < B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (Fintype.card κ ^ 3) *
        (m * (l * rationalKernelHeight (Fintype.card κ) H ^ (Fintype.card ι * Fintype.card κ))) ∧
      Λ ≤ Δ ∧ (Λ.subgroupOf Δ).Characteristic ∧ (Λ.subgroupOf Δ).Normal ∧
      (Λ.subgroupOf Δ).FiniteIndex ∧ Λ.relIndex Δ ≤ (m * B) ^ Fintype.card κ ∧
      scaledIntegerGrid ((m * B) * m) ⊆ bchSubgroupCoordinates f Λ ∧
      bchSubgroupCoordinates f Λ ⊆ denominatorGrid ((m * B) * m) ∧
      Λ.map realificationHom ⊓
        (realificationMap (hnil := hL) (hM := F.lowerCentralSeries_eq_bot) φ).range ≤
        (Γ.map realificationHom).map
          (realificationMap (hnil := hL) (hM := F.lowerCentralSeries_eq_bot) φ) := by
  obtain ⟨B, Λ₀, hB, _, hBb, _, hgrid, hlift⟩ := exists_image_lattice_subgroup e f φ Γ Δ
    l m H hl hm hH hΓ hΔin hentries hc
  obtain ⟨Λ, hΛ₀, hΛ, hchar, hnormal, hfinite, hindex, hin, hout⟩ :=
    F.exists_sharp_normal_cover f Δ Λ₀ m B hm hB hΔin hΔout hgrid.ge
  refine ⟨B, Λ, hB, hBb, hΛ, hchar, hnormal, hfinite, hindex, hin, hout, ?_⟩
  exact le_trans (inf_le_inf_right _ (Subgroup.map_mono hΛ₀)) hlift

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ImageDefiningMatrix
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem ker_id_sub_comp_eq_range {R V W : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (φ : V →ₗ[R] W) (σ : W →ₗ[R] V) (hσ : (φ.comp σ).comp φ = φ) :
    LinearMap.ker (LinearMap.id - φ.comp σ) = LinearMap.range φ := by
  ext y
  change y - φ (σ y) = 0 ↔ ∃ x, φ x = y
  constructor
  · intro h
    exact ⟨σ y, (sub_eq_zero.mp h).symm⟩
  · rintro ⟨x, rfl⟩
    exact sub_eq_zero.mpr (DFunLike.congr_fun hσ x).symm

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem baseChange_matrix_apply [DecidableEq ι] [DecidableEq κ]
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (P : L →ₗ[ℚ] M) (x : ℝ ⊗[ℚ] L) :
    (fun i j => (LinearMap.toMatrix e f P i j : ℝ)) *ᵥ (e.baseChange ℝ).equivFun x =
      (f.baseChange ℝ).equivFun (P.baseChange ℝ x) := by
  have heq : (fun i j => (LinearMap.toMatrix e f P i j : ℝ)) =
      LinearMap.toMatrix (e.baseChange ℝ) (f.baseChange ℝ) (P.baseChange ℝ) := by
    ext i j
    rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, linearMap_baseChange_basis]
  rw [heq]
  simpa only [Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (e.baseChange ℝ) (f.baseChange ℝ) (P.baseChange ℝ) x

open NilpotentLieBCHGroup

variable {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem realificationMap_mem_range_iff (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) s (realification_lowerCentralSeries_eq_bot hM)) :
    g ∈ (realificationMap (hnil := hL) (hM := hM) φ).range ↔
      g.coord ∈ LinearMap.range (φ.toLinearMap.baseChange ℝ) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.coord, congrArg NilpotentLieBCHGroup.coord hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x⟩, ext hx⟩

theorem exists_realified_image_defining_matrix (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) :
    ∃ Q : Matrix κ κ ℚ,
      (∀ i j, RationalHeightLE (Q i j)
        (2 * ((Fintype.card ι + 1) * (H * rationalKernelHeight (Fintype.card κ) H) ^ Fintype.card ι))) ∧
      ∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) s (realification_lowerCentralSeries_eq_bot hM),
        g ∈ (realificationMap (hnil := hL) (hM := hM) φ).range ↔
          (fun i j => (Q i j : ℝ)) *ᵥ (f.baseChange ℝ).equivFun g.coord = 0 := by
  classical
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_image_section e f φ.toLinearMap hH hentries
  let P : M →ₗ[ℚ] M := LinearMap.id - φ.toLinearMap.comp σ
  let Q := LinearMap.toMatrix f f P
  have hQ : Q = 1 - LinearMap.toMatrix e f φ.toLinearMap * LinearMap.toMatrix f e σ := by
    dsimp [Q, P]
    rw [map_sub, LinearMap.toMatrix_id, LinearMap.toMatrix_comp f e f]
  refine ⟨Q, ?_, ?_⟩
  · intro i j
    have hI : RationalHeightLE ((1 : Matrix κ κ ℚ) i j) 1 := by
      by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
    have hprod := rationalHeightLE_matrix_mul (LinearMap.toMatrix e f φ.toLinearMap)
      (LinearMap.toMatrix f e σ)
      (fun i j => by rw [LinearMap.toMatrix_apply]; exact hentries i j)
      (fun i j => by rw [LinearMap.toMatrix_apply]; exact hσH i j) i j
    rw [hQ]
    simpa only [Matrix.sub_apply, mul_one] using hI.sub hprod
  · intro g
    have hσR := linearMap_baseChange_image_section φ.toLinearMap σ hσ
    have hker := ker_id_sub_comp_eq_range (φ.toLinearMap.baseChange ℝ) (σ.baseChange ℝ) hσR
    have hPR : P.baseChange ℝ = LinearMap.id - (φ.toLinearMap.baseChange ℝ).comp (σ.baseChange ℝ) := by
      simp only [P, LinearMap.baseChange_sub, LinearMap.baseChange_id, LinearMap.baseChange_comp]
    rw [realificationMap_mem_range_iff, ← hker, ← hPR]
    change P.baseChange ℝ g.coord = 0 ↔ _
    rw [show (fun i j => (Q i j : ℝ)) *ᵥ (f.baseChange ℝ).equivFun g.coord =
      (f.baseChange ℝ).equivFun (P.baseChange ℝ g.coord) from baseChange_matrix_apply f f P g.coord]
    constructor
    · intro h
      rw [h, map_zero]
    · intro h
      apply (f.baseChange ℝ).equivFun.injective
      simpa only [map_zero] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHUniformQuotientCharts
namespace OAI

section

namespace Erdos3

def bchProductCoefficientBase (s : ℕ) : ℕ :=
  2 * s + 4 + finiteSeriesDenominator s +
    (s + 1) * ((s + 1) * finiteSeriesNumeratorBound s) + finiteSeriesNumeratorBound s

def bchProductCoefficientHeight (s n : ℕ) : ℕ :=
  bchProductCoefficientBase s ^ ((s + 2) * (n + 2))

theorem bchProductCoefficientBase_pos (s : ℕ) : 0 < bchProductCoefficientBase s := by
  unfold bchProductCoefficientBase
  omega

theorem bchProductDenominator_le_height (s n : ℕ) :
    bchProductDenominator s n ≤ bchProductCoefficientHeight s n := by
  let B := bchProductCoefficientBase s
  have hB : 1 ≤ B := bchProductCoefficientBase_pos s
  have hD : finiteSeriesDenominator s ≤ B := by dsimp [B, bchProductCoefficientBase]; omega
  unfold bchProductDenominator bchProductCoefficientHeight
  change finiteSeriesDenominator s * (finiteSeriesDenominator s ^ n) ^ s ≤ B ^ ((s + 2) * (n + 2))
  calc
    _ ≤ B * (B ^ n) ^ s := Nat.mul_le_mul hD (Nat.pow_le_pow_left (Nat.pow_le_pow_left hD _) _)
    _ = B ^ (1 + n * s) := by rw [← pow_mul, ← pow_succ']; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right hB (by nlinarith)

theorem bchProductNumeratorBound_le_height (s n : ℕ) :
    bchProductNumeratorBound s n ≤ bchProductCoefficientHeight s n := by
  let B := bchProductCoefficientBase s
  let A := (s + 1) * ((s + 1) * finiteSeriesNumeratorBound s)
  have hB : 1 ≤ B := bchProductCoefficientBase_pos s
  have hD : finiteSeriesDenominator s ≤ B := by dsimp [B, bchProductCoefficientBase]; omega
  have hA : A ≤ B := by dsimp [A, B, bchProductCoefficientBase]; omega
  have hs : s + 1 ≤ B := by dsimp [B, bchProductCoefficientBase]; omega
  have hU : finiteSeriesNumeratorBound s ≤ B := by dsimp [B, bchProductCoefficientBase]; omega
  have hsum : finiteSeriesDenominator s ^ n + (s + 1) * (A ^ n + finiteSeriesDenominator s ^ n) ≤
      B ^ (n + 1) := by
    calc
      _ ≤ B ^ n + (s + 1) * (B ^ n + B ^ n) :=
        Nat.add_le_add (Nat.pow_le_pow_left hD _)
          (Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.pow_le_pow_left hA _) (Nat.pow_le_pow_left hD _)))
      _ = (2 * s + 3) * B ^ n := by ring
      _ ≤ B * B ^ n := Nat.mul_le_mul_right _ (by dsimp [B, bchProductCoefficientBase]; omega)
      _ = _ := (pow_succ' B n).symm
  unfold bchProductNumeratorBound bchProductCoefficientHeight
  change (s + 1) * finiteSeriesNumeratorBound s *
    (finiteSeriesDenominator s ^ n + (s + 1) * (A ^ n + finiteSeriesDenominator s ^ n)) ^ s ≤
      B ^ ((s + 2) * (n + 2))
  calc
    _ ≤ (B * B) * (B ^ (n + 1)) ^ s :=
      Nat.mul_le_mul (Nat.mul_le_mul hs hU) (Nat.pow_le_pow_left hsum _)
    _ = B ^ (2 + (n + 1) * s) := by rw [← pow_two, ← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right hB (by nlinarith)

variable {X : Type*}

theorem bchProductWordCoefficient_height (s : ℕ) (xs : List X) (w : FreeMonoid X)
    (hw : w.length ≤ s) :
    RationalHeightLE (freeWordCoefficients (bchProductPolynomial s xs) w)
      (bchProductCoefficientHeight s xs.length) := by
  exact ((bchProductPolynomial_coefficient_bound s xs).rationalHeight
    (bchProductDenominator_pos s xs.length) w hw).mono
      (max_le (bchProductDenominator_le_height s xs.length) (bchProductNumeratorBound_le_height s xs.length))

theorem bchProductBracketCoefficient_height (s : ℕ) (xs : List X) {w : FreeSemigroup X}
    (hw : w ∈ bchProductBracketSupport s xs) :
    RationalHeightLE (bchProductBracketCoefficient s xs w)
      (bchProductCoefficientHeight s xs.length * (s + 1)) := by
  have hlen := bchProductBracketSupport_length s xs hw
  have hword := bchProductWordCoefficient_height s xs w.toFreeMonoid
    (by simpa only [freeSemigroup_toFreeMonoid_length] using hlen)
  have hinv : RationalHeightLE ((w.length : ℚ)⁻¹) (s + 1) := by
    have hpos : 0 < w.length := by change 0 < w.tail.length + 1; omega
    have h := rationalHeightLE_fraction (1 : ℤ) (w.length : ℤ)
      (by exact_mod_cast hpos.ne') (H := s + 1) (by simp)
      (by simpa only [Int.natAbs_natCast] using hlen.trans (Nat.le_succ s))
    simpa only [Int.cast_one, Int.cast_natCast, one_div] using h
  rw [bchProductBracketCoefficient, bchProductWordCoefficients_eq, if_pos hlen, div_eq_mul_inv]
  exact hword.mul hinv

variable {ι : Type*} [Fintype ι]

theorem bchProductCoordinatePolynomial_height (c : ι → ι → ι → ℚ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (s : ℕ) (xs : List X) (k : ι) :
    RationalPolynomialHeightLE (bchProductCoordinatePolynomial c s xs k)
      (((bchProductBracketSupport s xs).card + 1) *
        (bchProductCoefficientHeight s xs.length * (s + 1) *
          lieCoordinateHeight (Fintype.card ι) H s) ^ (bchProductBracketSupport s xs).card) := by
  apply RationalPolynomialHeightLE.sum_finset
  intro w hw
  exact RationalPolynomialHeightLE.C_mul (bchProductBracketCoefficient_height s xs hw)
    ((dynkinCoordinatePolynomial_height c hc w k).mono
      (lieCoordinateHeight_mono_length _ _ (bchProductBracketSupport_length s xs hw)))

end Erdos3

end

section

namespace Erdos3

theorem bchProductCoefficientHeight_le_exp (s n C : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hB : bchProductCoefficientBase s ≤ C) (hs : s + 2 ≤ C) :
    (bchProductCoefficientHeight s n : ℝ) ≤ Real.exp ((p + C) ^ 3) := by
  let t : ℝ := p + C
  have hbase : (bchProductCoefficientBase s : ℝ) ≤ t := by
    have h := (Nat.cast_le (α := ℝ)).mpr hB
    dsimp [t]
    linarith
  have hs' : (s : ℝ) + 2 ≤ t := by
    have h : (s : ℝ) + 2 ≤ C := by exact_mod_cast hs
    dsimp [t]
    linarith
  have hn' : (n : ℝ) + 2 ≤ t := by
    have hC : (2 : ℝ) ≤ C := by exact_mod_cast (show 2 ≤ C by omega)
    dsimp [t]
    linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have he : (bchProductCoefficientBase s : ℝ) ≤ Real.exp (bchProductCoefficientBase s) := by
    have h := Real.add_one_le_exp (bchProductCoefficientBase s)
    linarith
  unfold bchProductCoefficientHeight
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (bchProductCoefficientBase s)) ^ ((s + 2) * (n + 2)) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) he _
    _ = Real.exp ((((s + 2) * (n + 2) : ℕ) : ℝ) * bchProductCoefficientBase s) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (t * t * t) := by
      apply Real.exp_le_exp.mpr
      push_cast
      exact mul_le_mul (mul_le_mul hs' hn' (by positivity) ht) hbase (by positivity) (by positivity)
    _ = _ := by congr 1; dsimp [t]; ring

theorem exists_bchProductCoordinatePolynomial_exp_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X ι : Type*} [Fintype X] [Fintype ι]
      (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ) (xs : List X),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (xs.length : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      ∀ k m, (((bchProductCoordinatePolynomial c s xs k).coeff m).num.natAbs : ℝ) ≤
          Real.exp ((p + C) ^ C) ∧
        (((bchProductCoordinatePolynomial c s xs k).coeff m).den : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  let C := bchProductCoefficientBase s + 5 * s + 10
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C, hC, ?_⟩
  intro X ι _ _ c H p xs hp hd hX hn hH hc k m
  let t : ℝ := p + C
  have ht : 2 ≤ t := by
    have h : (2 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [t]
    linarith
  have hshift : p + 2 ≤ t := by
    have h : (2 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [t]
    linarith
  have hs : (s : ℝ) + 1 ≤ t := by
    have h : (s : ℝ) + 1 ≤ C := by exact_mod_cast (show s + 1 ≤ C by dsimp [C]; omega)
    dsimp [t]
    linarith
  have hword : (bchProductCoefficientHeight s xs.length : ℝ) ≤ Real.exp (t ^ (3 * s + 3)) := by
    apply (bchProductCoefficientHeight_le_exp s xs.length C hp hn
      (by dsimp [C]; omega) (by dsimp [C]; omega)).trans
    exact Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith) (by omega))
  have hsbound : ((s + 1 : ℕ) : ℝ) ≤ Real.exp (t ^ (3 * s + 3)) := by
    have h1 : t ≤ t ^ (3 * s + 3) := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t)
        (show 1 ≤ 3 * s + 3 by omega)
    have h2 := Real.add_one_le_exp (t ^ (3 * s + 3))
    push_cast
    linarith
  have hlie : (lieCoordinateHeight (Fintype.card ι) H s : ℝ) ≤ Real.exp (t ^ (3 * s + 3)) := by
    apply (lieCoordinateHeight_le_exp (Fintype.card ι) H s hp hd hH).trans
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (by linarith) hshift _).trans
      (pow_le_pow_right₀ (by linarith) (by omega))
  have hproduct : ((bchProductCoefficientHeight s xs.length * (s + 1) *
        lieCoordinateHeight (Fintype.card ι) H s : ℕ) : ℝ) ≤ Real.exp (t ^ (3 * s + 5)) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    calc
      _ ≤ Real.exp (t ^ (3 * s + 3)) * Real.exp (t ^ (3 * s + 3)) * Real.exp (t ^ (3 * s + 3)) :=
        mul_le_mul (mul_le_mul hword hsbound (by positivity) (by positivity)) hlie
          (by positivity) (by positivity)
      _ = Real.exp (3 * t ^ (3 * s + 3)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [show 3 * s + 5 = (3 * s + 3) + 2 by omega, pow_add t (3 * s + 3) 2]
        have hsq : 3 ≤ t ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ t ^ (3 * s + 3))]
  have hcard : ((bchProductBracketSupport s xs).card : ℝ) ≤ t ^ (s + 1) := by
    have h := (Nat.cast_le (α := ℝ)).mpr (bchProductBracketSupport_card_le s xs)
    push_cast at h
    apply h.trans
    calc
      ((s : ℝ) + 1) * ((Fintype.card X : ℝ) + 1) ^ s ≤ t * t ^ s :=
        mul_le_mul hs (pow_le_pow_left₀ (by positivity) (by linarith) _)
          (by positivity) (by positivity)
      _ = _ := (pow_succ' t s).symm
  have hsum := rational_sum_cost_le_exp (bchProductBracketSupport s xs).card
    (bchProductCoefficientHeight s xs.length * (s + 1) * lieCoordinateHeight (Fintype.card ι) H s)
    (p := t - 2) (by linarith) (3 * s + 5) (s + 1)
    (by simpa only [sub_add_cancel] using hproduct) (by simpa only [sub_add_cancel] using hcard)
  have hfinal : (((bchProductBracketSupport s xs).card + 1) *
      (bchProductCoefficientHeight s xs.length * (s + 1) * lieCoordinateHeight (Fintype.card ι) H s) ^
        (bchProductBracketSupport s xs).card : ℕ) ≤ Real.exp (t ^ C) := by
    apply hsum.trans
    apply Real.exp_le_exp.mpr
    rw [sub_add_cancel]
    exact pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hheight := bchProductCoordinatePolynomial_height c hc s xs k m
  exact ⟨(Nat.cast_le.mpr hheight.1).trans hfinal, (Nat.cast_le.mpr hheight.2).trans hfinal⟩

theorem exists_bch_product_coordinate_polynomials_exp_height (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X ι R L : Type*} [Fintype X] [Fintype ι]
      [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L]
      [IsScalarTower ℚ R L] (e : Module.Basis ι R L) (c : ι → ι → ι → ℚ)
      (H : ℕ) (p : ℝ) (xs : List X),
      (∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k) →
      LieModule.lowerCentralSeries ℚ L L s = ⊥ →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (xs.length : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      ∃ P : ι → MvPolynomial (X × ι) ℚ,
        (∀ (f : X → L) k,
          MvPolynomial.aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (P k) =
            e.repr (lieBCHList s f xs) k) ∧
        (∀ k, (P k).totalDegree ≤ s) ∧
        (∀ k, (P k).support.card ≤ (s + 1) * (Fintype.card X * Fintype.card ι + 1) ^ s) ∧
        ∀ k m, (((P k).coeff m).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          (((P k).coeff m).den : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hbudget⟩ := exists_bchProductCoordinatePolynomial_exp_budget s
  refine ⟨C, hC, ?_⟩
  intro X ι R L _ _ _ _ _ _ _ _ e c H p xs hstructure hnil hp hd hX hn hH hc
  refine ⟨bchProductCoordinatePolynomial c s xs, ?_,
    bchProductCoordinatePolynomial_totalDegree c s xs,
    bchProductCoordinatePolynomial_support_card c s xs, hbudget c H p xs hp hd hX hn hH hc⟩
  intro f k
  exact bchProductCoordinatePolynomial_eval_over e c hstructure s hnil f xs k

end Erdos3

end

section

namespace Erdos3

open Module _root_.MvPolynomial

theorem exists_bch_product_box_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X ι L : Type*} [Fintype X] [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (xs : List X) (f : X → L) (B : ℝ),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      LieModule.lowerCentralSeries ℚ L L s = ⊥ →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (xs.length : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      1 ≤ B → (∀ x i, |e.repr (f x) i| ≤ B) →
      ∀ i, |e.repr (lieBCHList s f xs) i| ≤
        ((s + 1) * (Fintype.card X * Fintype.card ι + 1) ^ s : ℕ) *
          Real.exp ((p + C) ^ C) * B ^ s := by
  obtain ⟨C, hC, hpoly⟩ := exists_bch_product_coordinate_polynomials_exp_height s
  refine ⟨C, hC, ?_⟩
  intro X ι L _ _ _ _ _ _ e c H p xs f B hstructure hnil hp hd hX hn hH hc hB hf i
  obtain ⟨P, heval, hdegree, hcard, hheight⟩ :=
    hpoly e c H p xs hstructure hnil hp hd hX hn hH hc
  rw [← heval f i]
  have hbound := abs_aeval_le_box_bound (P i)
    (fun xi : X × ι => e.repr (f xi.1) xi.2)
    (Real.exp_nonneg _) hB
    (fun m => (rational_abs_real_le_numerator _).trans (hheight i m).1)
    (fun xi => hf xi.1 xi.2) (hdegree i)
  apply hbound.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard i)) (Real.exp_nonneg _))
    (pow_nonneg (by linarith) _)

end Erdos3

end

section

namespace Erdos3

open Module

theorem bch_box_expression_le_exp (s a C n d : ℕ) (hC : 2 ≤ C) {p : ℝ}
    (hp : 0 ≤ p) (hn : n ≤ s) (hd : (d : ℝ) ≤ p) :
    (((s + 1) * (n * d + 1) ^ s : ℕ) : ℝ) *
      Real.exp ((p + s + C) ^ C) * (Real.exp ((p + 2) ^ a)) ^ s ≤
        Real.exp ((p + (C + 3 * s + a + 10)) ^ (C + 3 * s + a + 10)) := by
  let D := C + 3 * s + a + 10
  let t := p + D
  have hD : 3 ≤ D := by dsimp [D]; omega
  have hD' : (3 : ℝ) ≤ D := by exact_mod_cast hD
  have ht : 3 ≤ t := by dsimp [t]; linarith
  have hs : (s : ℝ) + 1 ≤ t := by
    have h : s + 1 ≤ D := by dsimp [D]; omega
    have h' := (Nat.cast_le (α := ℝ)).mpr h
    dsimp [t]
    push_cast at h'
    linarith
  have hp2 : p + 2 ≤ t := by dsimp [t]; linarith
  have hn' : (n : ℝ) ≤ t := (Nat.cast_le.mpr hn).trans (by linarith)
  have hd' : (d : ℝ) ≤ t := hd.trans (by linarith)
  have hbase : ((n * d + 1 : ℕ) : ℝ) ≤ t ^ 3 := by
    have hnd := mul_le_mul hn' hd' (Nat.cast_nonneg d) (by linarith : 0 ≤ t)
    push_cast
    nlinarith [sq_nonneg (t - 1)]
  have hcount : (((s + 1) * (n * d + 1) ^ s : ℕ) : ℝ) ≤ t ^ (3 * s + 1) := by
    push_cast at hbase
    push_cast
    calc
      _ ≤ t * (t ^ 3) ^ s :=
        mul_le_mul hs (pow_le_pow_left₀ (by positivity) hbase s) (by positivity) (by linarith)
      _ = t ^ (3 * s + 1) := by rw [← pow_mul, pow_succ']
  have hcount' : (((s + 1) * (n * d + 1) ^ s : ℕ) : ℝ) ≤ Real.exp (t ^ (D - 1)) := by
    have he : 3 * s + 1 ≤ D - 1 := by dsimp [D]; omega
    apply hcount.trans
    apply (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t) he).trans
    linarith [Real.add_one_le_exp (t ^ (D - 1))]
  have hshift : p + s + C ≤ t := by
    have h : s + C ≤ D := by dsimp [D]; omega
    have h' := (Nat.cast_le (α := ℝ)).mpr h
    dsimp [t]
    push_cast at h'
    linarith
  have hcoef : Real.exp ((p + s + C) ^ C) ≤ Real.exp (t ^ (D - 1)) := by
    apply Real.exp_le_exp.mpr
    apply (pow_le_pow_left₀ (by positivity) hshift C).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [D]; omega)
  have hinput : (Real.exp ((p + 2) ^ a)) ^ s ≤ Real.exp (t ^ (D - 1)) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ t * t ^ a :=
        mul_le_mul (by linarith : (s : ℝ) ≤ t)
          (pow_le_pow_left₀ (by linarith) hp2 a) (by positivity) (by linarith)
      _ = t ^ (a + 1) := (pow_succ' _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by dsimp [D]; omega)
  calc
    _ ≤ Real.exp (t ^ (D - 1)) * Real.exp (t ^ (D - 1)) * Real.exp (t ^ (D - 1)) :=
      mul_le_mul (mul_le_mul hcount' hcoef (by positivity) (by positivity)) hinput
        (by positivity) (by positivity)
    _ = Real.exp (3 * t ^ (D - 1)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (t ^ D) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ t * t ^ (D - 1) := mul_le_mul_of_nonneg_right ht (by positivity)
        _ = t ^ D := by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ D)]
    _ = _ := by simp [t, D]

theorem exists_bch_group_product_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (rs : List (NilpotentLieBCHGroup L s hnil)),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → rs.length ≤ s →
      (H : ℝ) ≤ Real.exp p → (∀ i j k, RationalHeightLE (c i j k) H) →
      (∀ r ∈ rs, ∀ i, |e.repr r.coord i| ≤ Real.exp ((p + 2) ^ a)) →
      ∀ i, |e.repr rs.prod.coord i| ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hbox⟩ := exists_bch_product_box_bound s
  refine ⟨C + 3 * s + a + 10, by omega, ?_⟩
  intro ι L _ _ _ _ _ e c H p hnil rs hstructure hp hd hn hH hc hrs i
  let f : Fin rs.length → L := fun j => (rs.get j).coord
  let xs := List.finRange rs.length
  have hlen : (xs.length : ℝ) ≤ p + s := by
    have hn' : (rs.length : ℝ) ≤ s := by exact_mod_cast hn
    simpa only [xs, List.length_finRange] using hn'.trans (by linarith)
  have hlabels : (Fintype.card (Fin rs.length) : ℝ) ≤ p + s := by
    simpa only [Fintype.card_fin, xs, List.length_finRange] using hlen
  have hbound := hbox e c H (p + s) xs f (Real.exp ((p + 2) ^ a)) hstructure hnil
    (by positivity) (hd.trans (by linarith [Nat.cast_nonneg (α := ℝ) s])) hlabels hlen
    (hH.trans (Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) s]))) hc
    (Real.one_le_exp (by positivity))
    (fun j k => hrs (rs.get j) (List.get_mem _ _) k) i
  have hmap : (xs.map (fun j => (⟨f j⟩ : NilpotentLieBCHGroup L s hnil))) = rs := by
    change (List.finRange rs.length).map rs.get = rs
    exact List.map_get_finRange rs
  have hcoord := lieBCHList_group_prod s hnil f xs
  rw [hmap] at hcoord
  rw [← hcoord, Fintype.card_fin] at hbound
  exact hbound.trans (by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      bch_box_expression_le_exp s a C rs.length (Fintype.card ι) hC hp hn hd)

end Erdos3

end

section

namespace Erdos3

open Module

theorem bch_bounded_product_box_expression_le_exp (s a C n k d : ℕ)
    (hC : 2 ≤ C) (hn : n ≤ k) {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) :
    (((s + 1) * (n * d + 1) ^ s : ℕ) : ℝ) * Real.exp ((p + k + C) ^ C) *
      (Real.exp ((p + 2) ^ a)) ^ s ≤
      Real.exp ((p + (C + 3 * (s + k) + a + 10)) ^ (C + 3 * (s + k) + a + 10)) := by
  have hcount : (s + 1) * (n * d + 1) ^ s ≤ (s + k + 1) * (n * d + 1) ^ (s + k) :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  have hcoef : Real.exp ((p + k + C) ^ C) ≤ Real.exp ((p + (s + k) + C) ^ C) := by
    apply Real.exp_le_exp.mpr
    apply pow_le_pow_left₀ (by positivity)
    linarith [Nat.cast_nonneg (α := ℝ) s]
  have hinput : (Real.exp ((p + 2) ^ a)) ^ s ≤ (Real.exp ((p + 2) ^ a)) ^ (s + k) :=
    pow_le_pow_right₀ (Real.one_le_exp (by positivity)) (by omega)
  apply le_trans (mul_le_mul (mul_le_mul (Nat.cast_le.mpr hcount) hcoef
    (by positivity) (by positivity)) hinput (by positivity) (by positivity))
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    bch_box_expression_le_exp (s + k) a C n d hC hp (by omega) hd

theorem exists_bch_fixed_product_exp_bound (s a k : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (rs : List (NilpotentLieBCHGroup L s hnil)),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → rs.length ≤ k →
      (H : ℝ) ≤ Real.exp p → (∀ i j k, RationalHeightLE (c i j k) H) →
      (∀ r ∈ rs, ∀ i, |e.repr r.coord i| ≤ Real.exp ((p + 2) ^ a)) →
      ∀ i, |e.repr rs.prod.coord i| ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hbox⟩ := exists_bch_product_box_bound s
  refine ⟨C + 3 * (s + k) + a + 10, by omega, ?_⟩
  intro ι L _ _ _ _ _ e c H p hnil rs hstructure hp hd hn hH hc hrs i
  let f : Fin rs.length → L := fun j => (rs.get j).coord
  let xs := List.finRange rs.length
  have hlen : (xs.length : ℝ) ≤ p + k := by
    have hn' : (rs.length : ℝ) ≤ k := by exact_mod_cast hn
    simpa only [xs, List.length_finRange] using hn'.trans (by linarith)
  have hlabels : (Fintype.card (Fin rs.length) : ℝ) ≤ p + k := by
    simpa only [Fintype.card_fin, xs, List.length_finRange] using hlen
  have hbound := hbox e c H (p + k) xs f (Real.exp ((p + 2) ^ a)) hstructure hnil
    (by positivity) (hd.trans (by linarith [Nat.cast_nonneg (α := ℝ) k])) hlabels hlen
    (hH.trans (Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) k]))) hc
    (Real.one_le_exp (by positivity)) (fun j z => hrs (rs.get j) (List.get_mem _ _) z) i
  have hmap : xs.map (fun j => (⟨f j⟩ : NilpotentLieBCHGroup L s hnil)) = rs := by
    change (List.finRange rs.length).map rs.get = rs
    exact List.map_get_finRange rs
  have hcoord := lieBCHList_group_prod s hnil f xs
  rw [hmap] at hcoord
  rw [← hcoord, Fintype.card_fin] at hbound
  exact hbound.trans (by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      bch_bounded_product_box_expression_le_exp s a C rs.length k (Fintype.card ι) hC hn hp hd)

end Erdos3

end

section

namespace Erdos3

open Module

theorem bch_triple_box_expression_le_exp (s a C d : ℕ) (hC : 2 ≤ C) {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) :
    (((s + 1) * (3 * d + 1) ^ s : ℕ) : ℝ) * Real.exp ((p + 3 + C) ^ C) *
      (Real.exp ((p + 2) ^ a)) ^ s ≤
      Real.exp ((p + (C + 3 * (s + 3) + a + 10)) ^ (C + 3 * (s + 3) + a + 10)) := by
  have hcount : (s + 1) * (3 * d + 1) ^ s ≤ (s + 3 + 1) * (3 * d + 1) ^ (s + 3) :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  have hcoef : Real.exp ((p + 3 + C) ^ C) ≤ Real.exp ((p + (s + 3) + C) ^ C) := by
    apply Real.exp_le_exp.mpr
    apply pow_le_pow_left₀ (by positivity)
    linarith [Nat.cast_nonneg (α := ℝ) s]
  have hinput : (Real.exp ((p + 2) ^ a)) ^ s ≤ (Real.exp ((p + 2) ^ a)) ^ (s + 3) :=
    pow_le_pow_right₀ (Real.one_le_exp (by positivity)) (by omega)
  apply le_trans (mul_le_mul (mul_le_mul (Nat.cast_le.mpr hcount) hcoef
    (by positivity) (by positivity)) hinput (by positivity) (by positivity))
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    bch_box_expression_le_exp (s + 3) a C 3 d hC hp (by omega) hd

theorem exists_bch_triple_product_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (u v w : NilpotentLieBCHGroup L s hnil),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      (∀ i, |e.repr u.coord i| ≤ Real.exp ((p + 2) ^ a)) →
      (∀ i, |e.repr v.coord i| ≤ Real.exp ((p + 2) ^ a)) →
      (∀ i, |e.repr w.coord i| ≤ Real.exp ((p + 2) ^ a)) →
      ∀ i, |e.repr (u * v * w).coord i| ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hbox⟩ := exists_bch_product_box_bound s
  refine ⟨C + 3 * (s + 3) + a + 10, by omega, ?_⟩
  intro ι L _ _ _ _ _ e c H p hnil u v w hstructure hp hd hH hc hu hv hw i
  let f : Fin 3 → L := ![u.coord, v.coord, w.coord]
  let xs : List (Fin 3) := [0, 1, 2]
  have hcoords (j : Fin 3) (k : ι) : |e.repr (f j) k| ≤ Real.exp ((p + 2) ^ a) := by
    fin_cases j
    · exact hu k
    · exact hv k
    · exact hw k
  have hbound := hbox e c H (p + 3) xs f (Real.exp ((p + 2) ^ a)) hstructure hnil
    (by linarith) (hd.trans (by linarith))
    (by norm_num only [Fintype.card_fin, Nat.cast_ofNat]; linarith)
    (by simp only [xs, List.length_cons, List.length_nil]; norm_num; linarith)
    (hH.trans (Real.exp_le_exp.mpr (by linarith))) hc
    (Real.one_le_exp (by positivity)) hcoords i
  have heq : lieBCHList s f xs = (u * v * w).coord := by
    simpa [xs, f, mul_assoc] using
      (lieBCHList_group_prod s hnil f xs).symm
  rw [heq, Fintype.card_fin] at hbound
  exact hbound.trans (by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      bch_triple_box_expression_le_exp s a C (Fintype.card ι) hC hp hd)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped NNReal

theorem coordinateLipschitzBound_power_budget (d D : ℕ) (hD : 2 ≤ D) (B : ℝ≥0)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hB : (B : ℝ) ≤ Real.exp ((p + D) ^ D)) :
    (coordinateLipschitzBound d d B : ℝ) ≤
      Real.exp ((p + ((D + 2) * 2 : ℕ)) ^ ((D + 2) * 2)) := by
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hq : 0 ≤ (p + D) ^ D := by positivity
  have hpq : p ≤ (p + D) ^ D := by
    calc
      p ≤ p + D := by linarith
      _ ≤ (p + D) ^ D := by
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + D)
          (by omega : 1 ≤ D)
  apply (coordinateLipschitzBound_le_exp d d B hq (hd.trans hpq) (hd.trans hpq) hB).trans
  apply Real.exp_le_exp.mpr
  have hshift := shifted_power_budget_le (p := p + D - 2) (by linarith) D 2
  rw [show p + D - 2 + 2 = p + D by ring] at hshift
  apply hshift.trans
  apply pow_le_pow_left₀ (by positivity)
  have hDE : D ≤ (D + 2) * 2 := by omega
  exact add_le_add le_rfl (Nat.cast_le.mpr hDE)

theorem exists_bch_conjugation_basis_exp_bound (s r : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (a : NilpotentLieBCHGroup L s hnil),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      (∀ i, |e.repr a.coord i| ≤ Real.exp ((p + 2) ^ r)) →
      ∀ i k, |e.repr (a * (⟨e i⟩ : NilpotentLieBCHGroup L s hnil) * a⁻¹).coord k| ≤
        Real.exp ((p + D) ^ D) := by
  classical
  obtain ⟨D, hD, hprod⟩ := exists_bch_triple_product_exp_bound s r
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ e c H p hnil a hstructure hp hd hH hc ha i k
  apply hprod e c H p hnil a ⟨e i⟩ a⁻¹ hstructure hp hd hH hc ha
  · intro j
    change |e.repr (e i) j| ≤ _
    rw [Basis.repr_self_apply]
    split_ifs
    · simpa only [abs_one] using Real.one_le_exp (by positivity : 0 ≤ (p + 2) ^ r)
    · simpa only [abs_zero] using Real.exp_nonneg ((p + 2) ^ r)
  · intro j
    change |e.repr (-a.coord) j| ≤ _
    simpa only [map_neg, Finsupp.neg_apply, abs_neg] using ha j

namespace NilpotentLieBCHGroup

theorem exists_uniform_left_lipschitz_exp_bound (s r : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      letI := rightMetricSpace (hnil := hnil) e
      ∃ C : ℝ≥0, 0 < C ∧ (C : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∀ a : NilpotentLieBCHGroup L s hnil,
          (∀ i, |e.repr a.coord i| ≤ Real.exp ((p + 2) ^ r)) →
          LipschitzWith C (fun x => a * x) := by
  obtain ⟨D, hD, hbound⟩ := exists_bch_conjugation_basis_exp_bound s r
  refine ⟨(D + 2) * 2, by omega, ?_⟩
  intro ι L _ _ _ _ _ _ _ _ _ e c H p hnil hstructure hp hd hH hc
  let := rightMetricSpace (hnil := hnil) e
  let B : ℝ≥0 := ⟨Real.exp ((p + D) ^ D), Real.exp_nonneg _⟩
  refine ⟨coordinateLipschitzBound (Fintype.card ι) (Fintype.card ι) B,
    coordinateLipschitzBound_pos _ _ _,
    coordinateLipschitzBound_power_budget _ D hD B hp hd le_rfl, ?_⟩
  intro a ha
  exact lipschitz_mul_left_of_basis_bound e a B (hbound e c H p hnil a hstructure hp hd hH hc ha)

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

section Quotient

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))

theorem quotientMetricSpace_lipschitz_left (a : NilpotentLieBCHGroup L s hnil) {C : ℝ≥0}
    (hLip : letI := rightMetricSpace (hnil := hnil) e; LipschitzWith C (fun x => a * x)) :
    letI := quotientMetricSpace e Γ hΓ
    LipschitzWith C (fun x : _ ⧸ Γ => a • x) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  exact lipschitz_quotient_left_smul Γ hΓ a hLip

theorem quotientMetricSpace_lipschitz_orbit (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := quotientMetricSpace e Γ hΓ
    LipschitzWith 1 (fun a : NilpotentLieBCHGroup L s hnil => a • x) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  exact lipschitz_quotient_orbit Γ hΓ x

end Quotient

theorem exists_uniform_quotient_left_lipschitz_exp_bound (s r : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      ∃ C : ℝ≥0, 0 < C ∧ (C : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∀ (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
          (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
          (a : NilpotentLieBCHGroup L s hnil),
          (∀ i, |e.repr a.coord i| ≤ Real.exp ((p + 2) ^ r)) →
          letI := quotientMetricSpace e Γ hΓ
          LipschitzWith C (fun x : _ ⧸ Γ => a • x) := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_left_lipschitz_exp_bound s r
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ _ _ e c H p hnil hstructure hp hd hH hc
  obtain ⟨C, hC, hCp, hLip⟩ := hbound e c H p hnil hstructure hp hd hH hc
  refine ⟨C, hC, hCp, ?_⟩
  intro Γ hΓ a ha
  exact quotientMetricSpace_lipschitz_left e Γ hΓ a (hLip a ha)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))

omit [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L] in
theorem centralBCHFlow_period (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (hperiod : (⟨v⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ) (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    realBCHLine (hnil := hnil) v 1 • x = x := by
  apply central_smul_eq_self_of_mem Γ
  · simpa only [realBCHLine_one] using hperiod
  · exact realBCHLine_commute v hv 1

theorem centralBCHFlow_isometry (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0) (r : ℝ) :
    letI := quotientMetricSpace e Γ hΓ
    Isometry (fun x : NilpotentLieBCHGroup L s hnil ⧸ Γ => realBCHLine (hnil := hnil) v r • x) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  exact isometry_quotient_central_smul Γ hΓ (realBCHLine (hnil := hnil) v r) (realBCHLine_commute v hv r)

theorem centralBCHFlow_displacement (v : L) (r : ℝ) (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    letI := quotientMetricSpace e Γ hΓ
    dist (realBCHLine (hnil := hnil) v r • x) x ≤ coordinateL2Norm (e.equivFun v) * |r| := by
  let := rightMetricSpace (hnil := hnil) e
  let := quotientMetricSpace e Γ hΓ
  have h := (quotientMetricSpace_lipschitz_orbit e Γ hΓ x).dist_le_mul (realBCHLine (hnil := hnil) v r) 1
  have hbound := realBCHLine_dist_one_le (hnil := hnil) e v r
  simp only [one_smul, NNReal.coe_one, one_mul] at h
  exact h.trans (hbound.trans_eq (mul_comm _ _))

noncomputable def centralBCHCircleAction (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (hperiod : (⟨v⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ) :
    letI := quotientMetricSpace e Γ hΓ
    CircleFourier.IsometricCircleAction (NilpotentLieBCHGroup L s hnil ⧸ Γ) := by
  let := quotientMetricSpace e Γ hΓ
  exact CircleFourier.isometricCircleActionOfFlow (fun r x => realBCHLine (hnil := hnil) v r • x)
    (fun x => by rw [realBCHLine_zero, one_smul])
    (fun r t x => by rw [realBCHLine_add, mul_smul])
    (centralBCHFlow_period Γ v hv hperiod)
    (centralBCHFlow_isometry e Γ hΓ v hv)
    ⟨coordinateL2Norm (e.equivFun v), coordinateL2Norm_nonneg _⟩
    (centralBCHFlow_displacement e Γ hΓ v)

theorem centralBCHCircleAction_act_coe (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (hperiod : (⟨v⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ)
    (r : ℝ) (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    letI := quotientMetricSpace e Γ hΓ
    (centralBCHCircleAction e Γ hΓ v hv hperiod).act (r : CircleFourier.Circle) x =
      realBCHLine (hnil := hnil) v r • x := by
  let := quotientMetricSpace e Γ hΓ
  dsimp only [centralBCHCircleAction, CircleFourier.isometricCircleActionOfFlow]
  exact CircleFourier.periodicFlowAct_coe _ _ r x

theorem centralBCHCircleAction_displacement (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (hperiod : (⟨v⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ)
    (t : CircleFourier.Circle) (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    letI := quotientMetricSpace e Γ hΓ
    dist ((centralBCHCircleAction e Γ hΓ v hv hperiod).act t x) x ≤
      coordinateL2Norm (e.equivFun v) * ‖t‖ := by
  let := quotientMetricSpace e Γ hΓ
  dsimp only [centralBCHCircleAction, CircleFourier.isometricCircleActionOfFlow]
  exact CircleFourier.periodicFlowAct_displacement _ _
    ⟨coordinateL2Norm (e.equivFun v), coordinateL2Norm_nonneg _⟩
    (centralBCHFlow_displacement e Γ hΓ v) t x

theorem centralBCHCircleAction_commutes (v w : L)
    (hv : ∀ z : L, ⁅v, z⁆ = 0) (hw : ∀ z : L, ⁅w, z⁆ = 0)
    (hvΓ : (⟨v⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ)
    (hwΓ : (⟨w⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ) :
    letI := quotientMetricSpace e Γ hΓ
    (centralBCHCircleAction e Γ hΓ v hv hvΓ).Commutes (centralBCHCircleAction e Γ hΓ w hw hwΓ) := by
  let := quotientMetricSpace e Γ hΓ
  intro t u x
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective u
  simp only [centralBCHCircleAction_act_coe]
  rw [← mul_smul, ← mul_smul, (realBCHLine_commute v hv r (realBCHLine (hnil := hnil) w q)).eq]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageRepresentatives
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

omit [Fintype ι] in
theorem basis_repr_height_one (e : Basis ι ℚ L) (i j : ι) :
    RationalHeightLE (e.repr (e i) j) 1 := by
  classical
  simp only [Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact rationalHeightLE_one (by omega)
  · exact rationalHeightLE_zero (by omega)

theorem lie_basis_bracket_height (e : Basis ι ℚ L) {H K : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (v : L) (hv : ∀ j, RationalHeightLE (e.repr v j) K) (i k : ι) :
    RationalHeightLE (e.repr ⁅e i, v⁆ k)
      ((Fintype.card ι ^ 2 + 1) * (H * K) ^ (Fintype.card ι ^ 2)) := by
  classical
  rw [lie_coordinate_formula]
  have h := rationalHeightLE_sum
    (fun ab : ι × ι => lieStructureConstants e ab.1 ab.2 k * e.repr (e i) ab.1 * e.repr v ab.2)
    (fun ab => ((hc ab.1 ab.2 k).mul (basis_repr_height_one e i ab.1)).mul (hv ab.2))
  simpa only [Fintype.card_prod, ← pow_two, mul_one] using h

theorem span_basis_brackets_layer (e : Basis ι ℚ L) (v : κ → L) (n : ℕ)
    (hv : Submodule.span ℚ (Set.range v) = (LieModule.lowerCentralSeries ℚ L L n).toSubmodule) :
    Submodule.span ℚ (Set.range (fun ij : ι × κ => ⁅e ij.1, v ij.2⁆)) =
      (LieModule.lowerCentralSeries ℚ L L (n + 1)).toSubmodule := by
  classical
  rw [LieModule.lowerCentralSeries_succ]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    apply LieSubmodule.lie_mem_lie (by simp)
    change v j ∈ (LieModule.lowerCentralSeries ℚ L L n).toSubmodule
    rw [← hv]
    exact Submodule.subset_span ⟨j, rfl⟩
  · rw [LieSubmodule.lieIdeal_oper_eq_linear_span']
    apply Submodule.span_le.mpr
    rintro _ ⟨x, _, y, hy, rfl⟩
    have hy' : y ∈ Submodule.span ℚ (Set.range v) := hv.symm ▸ hy
    obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hy'
    rw [← e.sum_repr x, ← ht]
    simp only [sum_lie, lie_sum, smul_lie, lie_smul]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(j, i), rfl⟩

omit [Fintype κ] in
theorem exists_small_bounded_spanning_family (e : Basis ι ℚ L) (P : Submodule ℚ L)
    (v : κ → L) (hspan : Submodule.span ℚ (Set.range v) = P) {H : ℕ}
    (hv : ∀ i j, RationalHeightLE (e.repr (v i) j) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ w : Fin r → L,
      Submodule.span ℚ (Set.range w) = P ∧
      ∀ i j, RationalHeightLE (e.repr (w i) j) H := by
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan] at hex
  obtain ⟨w, hw, hwspan, _⟩ := hex
  refine ⟨finrank ℚ P, ?_, w, hwspan, ?_⟩
  · simpa only [Module.finrank_eq_card_basis e] using P.finrank_le
  · intro i j
    obtain ⟨a, ha⟩ := hw i
    rw [← ha]
    exact hv a j

theorem exists_bounded_layer_spanning (e : Basis ι ℚ L) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) (n : ℕ) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ v : Fin r → L,
      Submodule.span ℚ (Set.range v) = (LieModule.lowerCentralSeries ℚ L L n).toSubmodule ∧
      ∀ i j, RationalHeightLE (e.repr (v i) j) (lieCoordinateHeight (Fintype.card ι) H n) := by
  induction n with
  | zero =>
    apply exists_small_bounded_spanning_family e _ e
    · simp [e.span_eq]
    · intro i j
      exact (basis_repr_height_one e i j).mono (lieCoordinateHeight_pos _ _ _)
  | succ n ih =>
    obtain ⟨r, _, v, hvspan, hv⟩ := ih
    apply exists_small_bounded_spanning_family e _ (fun ij : ι × Fin r => ⁅e ij.1, v ij.2⁆)
    · exact span_basis_brackets_layer e v n hvspan
    · intro ij k
      exact (lie_basis_bracket_height e hc (v ij.2) (hv ij.2) ij.1 k).mono
        (lieCoordinateHeight_step _ _ _)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

def layerRoundingBound (d H l n : ℕ) : ℕ :=
  d * l * lieCoordinateHeight d H n ^ (d * d + 1)

theorem layerRoundingBound_mono_layer (d H l : ℕ) : Monotone (layerRoundingBound d H l) := by
  intro m n hmn
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (lieCoordinateHeight_mono_length d H hmn) _)

theorem layerRoundingBound_le_exp (d H l n : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    (layerRoundingBound d H l n : ℝ) ≤ Real.exp ((p + 2) ^ (3 * n + 5)) := by
  let t := p + 2
  let a := 3 * n + 2
  have ht : 2 ≤ t := by dsimp [t]; linarith
  have hK := lieCoordinateHeight_le_exp d H n hp hd hH
  have hdim : ((d * d + 1 : ℕ) : ℝ) ≤ t ^ 2 := by
    push_cast
    dsimp [t]
    nlinarith [mul_self_le_mul_self (Nat.cast_nonneg d) hd]
  have hpow : (lieCoordinateHeight d H n : ℝ) ^ (d * d + 1) ≤
      Real.exp (t ^ (a + 2)) := by
    calc
      _ ≤ (Real.exp (t ^ a)) ^ (d * d + 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hK _
      _ = Real.exp (((d * d + 1 : ℕ) : ℝ) * t ^ a) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (t ^ 2 * t ^ a) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdim (by positivity))
      _ = _ := by rw [← pow_add]; congr 2; omega
  have hdp : (d : ℝ) ≤ Real.exp p := hd.trans (by linarith [Real.add_one_le_exp p])
  have hpA : p ≤ t ^ a := le_power_budget hp (by dsimp [a]; omega)
  have htwo : (2 : ℝ) ≤ t ^ 2 := by nlinarith
  have hp2 : 2 * p ≤ t ^ (a + 2) := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_left htwo (by positivity : 0 ≤ t ^ a)]
  unfold layerRoundingBound
  push_cast
  calc
    _ ≤ Real.exp p * Real.exp p * Real.exp (t ^ (a + 2)) :=
      mul_le_mul (mul_le_mul hdp hl (by positivity) (by positivity)) hpow
        (by positivity) (by positivity)
    _ = Real.exp (2 * p + t ^ (a + 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (t ^ (a + 3)) := by
      apply Real.exp_le_exp.mpr
      rw [show a + 3 = (a + 2) + 1 by omega, pow_succ t (a + 2)]
      nlinarith [mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ t ^ (a + 2))]
    _ = _ := by rfl

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

local notation "E" => ℝ ⊗[ℚ] L
local notation "G" => NilpotentLieBCHGroup E s (realification_lowerCentralSeries_eq_bot hnil)

theorem exists_bounded_realification_layer_reduction (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) (n : ℕ) :
    ∃ K : Set G, IsCompact K ∧
      (∀ r ∈ K, ∀ i, |(e.baseChange ℝ).repr r.coord i| ≤
        layerRoundingBound (Fintype.card ι) H l n) ∧
      ∀ g : G, g.coord ∈ LieModule.lowerCentralSeries ℚ E E n →
        ∃ r ∈ K, ∃ w ∈ Γ.map NilpotentLieBCHGroup.realificationHom,
          (r⁻¹ * g * w⁻¹).coord ∈ LieModule.lowerCentralSeries ℚ E E (n + 1) := by
  obtain ⟨r, hr, v, hspan, hv⟩ := exists_bounded_layer_spanning e hc n
  let B := lieCoordinateHeight (Fintype.card ι) H n
  let m := rationalSpanGridStep e v l
  have hB : 1 ≤ B := lieCoordinateHeight_pos _ _ _
  have hm : m ≤ l * B ^ (Fintype.card ι * Fintype.card ι) := by
    apply (rationalSpanGridStep_le e v l (fun i j => hv j i)).trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right hB
    simpa only [Fintype.card_fin] using Nat.mul_le_mul_left (Fintype.card ι) hr
  have hsize : r * m * B ≤ layerRoundingBound (Fintype.card ι) H l n := by
    calc
      _ ≤ Fintype.card ι * (l * B ^ (Fintype.card ι * Fintype.card ι)) * B :=
        Nat.mul_le_mul_right B (Nat.mul_le_mul hr hm)
      _ = _ := by simp [layerRoundingBound, pow_succ, mul_assoc, B]
  refine ⟨(fun x : E => (⟨x⟩ : G)) ''
    boundedSpanCell (fun j => rationalLieInclusion (v j)) (m : ℝ),
    (isCompact_boundedSpanCell _ _).image NilpotentLieBCHGroup.continuous_mk, ?_,
    realification_layer_reduction_in_cell e Γ l hl hinner n v hspan⟩
  rintro _ ⟨x, hx, rfl⟩ i
  have hcoord : ∀ j k, |(e.baseChange ℝ).repr (rationalLieInclusion (v j)) k| ≤ (B : ℝ) := by
    intro j k
    rw [rationalLieInclusion_coordinates]
    exact (hv j k).abs_real_le
  have hb := boundedSpanCell_coordinate_bound (e.baseChange ℝ) _
    (Nat.cast_nonneg m) hcoord hx i
  apply hb.trans
  simpa only [Fintype.card_fin, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hsize

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

local notation "E" => ℝ ⊗[ℚ] L
local notation "G" => NilpotentLieBCHGroup E s (realification_lowerCentralSeries_eq_bot hnil)

theorem exists_bounded_realification_factors (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) :
    ∀ g : G, ∃ rs : List G, rs.length = s ∧
      (∀ r ∈ rs, ∀ i, |(e.baseChange ℝ).repr r.coord i| ≤
        layerRoundingBound (Fintype.card ι) H l s) ∧
      ∃ γ ∈ Γ.map NilpotentLieBCHGroup.realificationHom, g = rs.prod * γ := by
  let J : ℕ → Subgroup G := fun n => NilpotentLieBCHGroup.subgroup
    (show LieIdeal ℚ E from LieModule.lowerCentralSeries ℚ E E n).toLieSubalgebra
  have hzero : J 0 = ⊤ := by
    ext g
    change (g.coord ∈ LieModule.lowerCentralSeries ℚ E E 0) ↔ g ∈ (⊤ : Subgroup G)
    simp
  have hterminal : J s = ⊥ := by
    ext g
    change (g.coord ∈ LieModule.lowerCentralSeries ℚ E E s) ↔ g = 1
    rw [realification_lowerCentralSeries_eq_bot hnil, LieSubmodule.mem_bot]
    exact ⟨fun h => NilpotentLieBCHGroup.ext h, fun h => congrArg NilpotentLieBCHGroup.coord h⟩
  apply exists_representative_factors_of_reductions
    (Γ.map NilpotentLieBCHGroup.realificationHom) J s _ hzero hterminal
  intro i hi g hg
  obtain ⟨K, _, hbound, hreduce⟩ := exists_bounded_realification_layer_reduction e Γ l hl hinner hc i
  obtain ⟨r, hr, w, hw, hrem⟩ := hreduce g hg
  refine ⟨r, ?_, w, hw, hrem⟩
  intro k
  exact (hbound r hr k).trans (Nat.cast_le.mpr (layerRoundingBound_mono_layer _ _ _ hi.le))

end Erdos3

end

section

namespace Erdos3

open Module

def lieTreeHeight (d H n : ℕ) : ℕ := (d ^ 2 + H + 2) ^ ((3 * d ^ 2 + 3) ^ n)

theorem lieTreeHeight_ge_input (d H n : ℕ) : H ≤ lieTreeHeight d H n := by
  unfold lieTreeHeight
  have hE : 1 ≤ (3 * d ^ 2 + 3) ^ n := Nat.one_le_pow _ _ (by omega)
  calc
    H ≤ d ^ 2 + H + 2 := by omega
    _ = (d ^ 2 + H + 2) ^ 1 := (pow_one _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hE

theorem lieTreeHeight_mono (d H : ℕ) : Monotone (lieTreeHeight d H) := by
  intro i j hij
  unfold lieTreeHeight
  exact Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hij)

theorem lieTreeHeight_step (d H n : ℕ) :
    (d ^ 2 + 1) * (H * lieTreeHeight d H n * lieTreeHeight d H n) ^ (d ^ 2) ≤
      lieTreeHeight d H (n + 1) := by
  let A := d ^ 2 + H + 2
  let N := d ^ 2
  let E := (3 * N + 3) ^ n
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hH : H ≤ A := by dsimp [A]; omega
  have hN : N + 1 ≤ A := by dsimp [A, N]; omega
  have hE : 1 ≤ E := Nat.one_le_pow _ _ (by dsimp [N]; omega)
  change (N + 1) * (H * A ^ E * A ^ E) ^ N ≤ A ^ ((3 * N + 3) ^ (n + 1))
  calc
    _ ≤ A * (A * A ^ E * A ^ E) ^ N := by gcongr
    _ = A ^ (1 + (1 + 2 * E) * N) := by
      rw [← pow_succ', ← pow_add, ← pow_mul, ← pow_succ']
      congr 1
      ring
    _ ≤ _ := by
      apply Nat.pow_le_pow_right hA
      rw [pow_succ]
      change 1 + (1 + 2 * E) * N ≤ E * (3 * N + 3)
      nlinarith

theorem lieTreeHeight_le_coordinateHeight (d H n : ℕ) :
    lieTreeHeight d H n ≤ lieCoordinateHeight d H (2 * n) := by
  unfold lieTreeHeight lieCoordinateHeight
  apply Nat.pow_le_pow_right (by omega)
  rw [pow_mul]
  apply Nat.pow_le_pow_left
  nlinarith [sq_nonneg (d : ℤ)]

theorem lieTreeHeight_le_exp (d H n : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (lieTreeHeight d H n : ℝ) ≤ Real.exp ((p + 2) ^ (6 * n + 2)) := by
  have h := lieCoordinateHeight_le_exp d H (2 * n) hp hd hH
  have hle : (lieTreeHeight d H n : ℝ) ≤ lieCoordinateHeight d H (2 * n) := by
    exact_mod_cast lieTreeHeight_le_coordinateHeight d H n
  simpa only [show 3 * (2 * n) + 2 = 6 * n + 2 by omega] using hle.trans h

theorem finiteLieTrees_coordinate_height {I ι L : Type*} [Fintype I] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] (e : Basis ι ℚ L) (v : I → L) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hv : ∀ i j, RationalHeightLE (e.repr (v i) j) H) (n : ℕ)
    (a : FreeMagma I) (ha : a ∈ finiteLieTrees I n) (k : ι) :
    RationalHeightLE (e.repr (lieTreeEval v a) k) (lieTreeHeight (Fintype.card ι) H n) := by
  classical
  induction n generalizing a k with
  | zero => simp only [finiteLieTrees, Finset.notMem_empty] at ha
  | succ n ih =>
    rcases Finset.mem_union.mp ha with h | h
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact (hv i k).mono (lieTreeHeight_ge_input _ _ _)
    · obtain ⟨⟨b, c⟩, hbc, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hb, hc'⟩ := Finset.mem_product.mp hbc
      exact (lie_bracket_coordinate_height e hc (lieTreeEval v b) (lieTreeEval v c)
        (fun j => ih b hb j) (fun j => ih c hc' j) k).mono (lieTreeHeight_step _ _ _)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_realification_representatives_exp_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ),
      0 < l → scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil),
        ∃ r, (∀ i, |(e.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ γ ∈ Γ.map NilpotentLieBCHGroup.realificationHom, g = r * γ := by
  obtain ⟨C, hC, hprod⟩ := exists_bch_group_product_exp_bound s (3 * s + 5)
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ _ _ _ e hnil Γ l H p hl hinner hc hp hd hH hlbound g
  obtain ⟨rs, hlen, hcoords, γ, hγ, heq⟩ := exists_bounded_realification_factors e Γ l hl hinner hc g
  refine ⟨rs.prod, ?_, γ, hγ, heq⟩
  apply hprod (e.baseChange ℝ) (lieStructureConstants e) H p
    (realification_lowerCentralSeries_eq_bot hnil) rs
  · intro i j k
    exact (realLieBasis_structure e i j k).symm
  · exact hp
  · exact hd
  · exact hlen.le
  · exact hH
  · exact hc
  · intro r hr i
    exact (hcoords r hr i).trans (layerRoundingBound_le_exp _ _ _ _ hp hd hH hlbound)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open Module

end Erdos3

end

section

namespace Erdos3

open Module

end Erdos3

end

section

namespace Erdos3

open Module

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix TensorProduct NNReal

theorem matrixDenominator_allowance_le_exp {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (l H : ℕ) (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ((l * matrixDenominator A : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  have hD : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply (Nat.cast_le.mpr (matrixDenominator_le A hA)).trans
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg H) hH _).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [Nat.cast_mul]
    calc
      (Fintype.card ι : ℝ) * Fintype.card κ * p ≤ (p + 2) * (p + 2) * (p + 2) := by
        gcongr <;> linarith
      _ = (p + 2) ^ 3 := by ring
  rw [Nat.cast_mul]
  calc
    (l : ℝ) * matrixDenominator A ≤ Real.exp p * Real.exp ((p + 2) ^ 3) :=
      mul_le_mul hl hD (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (p + (p + 2) ^ 3) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((p + 2) ^ 4) := by
      apply Real.exp_le_exp.mpr
      have hp3 := le_power_budget hp (by decide : 1 ≤ 3)
      nlinarith [mul_nonneg hp (pow_nonneg (by linarith : (0 : ℝ) ≤ p + 2) 3)]

theorem bch_comap_inner_grid {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (Λ : Subgroup (NilpotentLieBCHGroup M s hM)) (l : ℕ)
    (hΛ : scaledIntegerGrid l ⊆ bchSubgroupCoordinates f Λ) :
    scaledIntegerGrid (l * matrixDenominator (LinearMap.toMatrix e f φ.toLinearMap)) ⊆
      bchSubgroupCoordinates e (Λ.comap (map (hnil := hL) φ)) := by
  rw [bchSubgroupCoordinates_comap e f φ Λ]
  intro x hx
  exact hΛ (matrix_mulVec_fine_grid (LinearMap.toMatrix e f φ.toLinearMap) l hx)

theorem exists_bounded_image_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι κ L M : Type*} [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (hM : LieModule.lowerCentralSeries ℚ M M s = ⊥)
      (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
      (Λ : Subgroup (NilpotentLieBCHGroup M s hM)) (l H : ℕ) (p : ℝ),
      0 < l → scaledIntegerGrid l ⊆ bchSubgroupCoordinates f Λ →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∀ y : CosetImage (realificationMap (hnil := hL) (hM := hM) φ) (Λ.map realificationHom),
        ∃ x, projectToCosetImage (realificationMap (hnil := hL) (hM := hM) φ)
            (Λ.map realificationHom) x = y ∧
          ∀ i, |(f.baseChange ℝ).repr (realificationMap (hnil := hL) (hM := hM) φ x).coord i| ≤
            Real.exp ((((p + 2) ^ 4 + C) ^ C) + (p + 2) ^ 2) := by
  obtain ⟨C, hC, hrep⟩ := exists_realification_representatives_exp_bound s
  refine ⟨C, hC, ?_⟩
  intro ι κ L M _ _ _ _ _ _ _ _ _ hL hM e f φ Λ l H p hl hΛ hc hφ hp hι hκ hH hlp y
  classical
  let Γ := Λ.comap (map (hnil := hL) φ)
  let A := LinearMap.toMatrix e f φ.toLinearMap
  let q := l * matrixDenominator A
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    intro i j
    change RationalHeightLE (LinearMap.toMatrix e f φ.toLinearMap i j) H
    rw [LinearMap.toMatrix_apply]
    exact hφ i j
  have hq : 0 < q := Nat.mul_pos hl (matrixDenominator_pos A)
  have hqbound := matrixDenominator_allowance_le_exp A l H hA hp hκ hι hH hlp
  have hp' : p ≤ (p + 2) ^ 4 := le_power_budget hp (by decide)
  obtain ⟨g, hg⟩ := projectToCosetImage_surjective
    (realificationMap (hnil := hL) (hM := hM) φ) (Λ.map realificationHom) y
  obtain ⟨r, hr, γ, hγ, heq⟩ := hrep e hL Γ q H ((p + 2) ^ 4) hq
    (bch_comap_inner_grid e f φ Λ l hΛ) hc (by positivity) (hι.trans hp')
    (hH.trans (Real.exp_le_exp.mpr hp')) hqbound g
  have hγmap : realificationMap (hnil := hL) (hM := hM) φ γ ∈ Λ.map realificationHom :=
    realificationMap_subgroup φ Γ Λ le_rfl hγ
  refine ⟨r, ?_, ?_⟩
  · apply Subtype.ext
    have hgy := congrArg Subtype.val hg
    change (QuotientGroup.mk (realificationMap (hnil := hL) (hM := hM) φ g) :
      _ ⧸ Λ.map realificationHom) = y.val at hgy
    rw [← hgy, heq, map_mul]
    exact (quotient_mk_mul_mem (Λ.map realificationHom)
      (realificationMap (hnil := hL) (hM := hM) φ r) ⟨_, hγmap⟩).symm
  · intro i
    have hnorm : ‖(e.baseChange ℝ).equivFun r.coord‖ ≤ Real.exp (((p + 2) ^ 4 + C) ^ C) := by
      apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr
      intro j
      simpa only [Basis.equivFun_apply, Real.norm_eq_abs] using hr j
    have hbound := abs_matrix_mulVec_le (fun i j => (A i j : ℝ)) (H : ℝ≥0)
      (fun i j => (hA i j).abs_real_le) ((e.baseChange ℝ).equivFun r.coord) i
    dsimp only [A] at hbound
    rw [baseChange_matrix_apply e f φ.toLinearMap] at hbound
    have hfac : ((Fintype.card ι : ℝ) + 1) * ((H : ℝ) + 1) ≤
        (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H : ℝ) := by
      change _ ≤ ((Fintype.card κ : ℝ) + Fintype.card ι + 1) * ((H : ℝ) + 1)
      gcongr
      exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    calc
      _ ≤ ((Fintype.card ι : ℝ) + 1) * ((H : ℝ) + 1) * ‖(e.baseChange ℝ).equivFun r.coord‖ := hbound
      _ ≤ (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H : ℝ) *
          Real.exp (((p + 2) ^ 4 + C) ^ C) := mul_le_mul hfac hnorm (norm_nonneg _) (NNReal.coe_nonneg _)
      _ ≤ Real.exp ((p + 2) ^ 2) * Real.exp (((p + 2) ^ 4 + C) ^ C) :=
        mul_le_mul_of_nonneg_right (coordinateLipschitzBound_le_exp _ _ _ hp hκ hι hH) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeHorizontalLiftBudget
namespace OAI

section

namespace Erdos3

def absorbedInitialParameter (p : ℝ) : ℝ :=
  3 * p + 1 + (p + 2) ^ 36 + (p + 2) ^ 19

theorem absorbedInitialParameter_bounds {p : ℝ} (hp : 0 ≤ p) :
    p ≤ absorbedInitialParameter p ∧
    Real.exp p + Real.exp p * Real.exp ((p + 2) ^ 19) * Real.exp p ≤
      Real.exp (absorbedInitialParameter p) ∧
    Real.exp p * (Real.exp p * (Real.exp p * Real.exp ((p + 2) ^ 36))) ≤
      Real.exp (absorbedInitialParameter p) := by
  have h19 : 0 ≤ (p + 2) ^ 19 := by positivity
  have h36 : 0 ≤ (p + 2) ^ 36 := by positivity
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  refine ⟨by unfold absorbedInitialParameter; linarith, ?_, ?_⟩
  · calc
      _ = Real.exp p + Real.exp (2 * p + (p + 2) ^ 19) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (2 * p + (p + 2) ^ 19) + Real.exp (2 * p + (p + 2) ^ 19) := by
        gcongr
        linarith
      _ = 2 * Real.exp (2 * p + (p + 2) ^ 19) := (two_mul _).symm
      _ ≤ Real.exp 1 * Real.exp (2 * p + (p + 2) ^ 19) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp (1 + (2 * p + (p + 2) ^ 19)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold absorbedInitialParameter; linarith)
  · rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold absorbedInitialParameter
    linarith

theorem absorbedInitialParameter_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ absorbedInitialParameter p := hp.trans (absorbedInitialParameter_bounds hp).1

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

def imageDefiningHeight (d n H : ℕ) : ℕ :=
  2 * ((d + 1) * (H * rationalKernelHeight n H) ^ d)

theorem imageDefiningHeight_le_exp (d n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (imageDefiningHeight d n H : ℝ) ≤ Real.exp ((p + 2) ^ 10) := by
  have hK := rationalKernelHeight_le_budget n H hp hn hH
  have hp7 : p ≤ (p + 2) ^ 7 := le_power_budget hp (by decide)
  have hbase : (H : ℝ) * rationalKernelHeight n H ≤ Real.exp ((p + 2) ^ 8) := by
    calc
      _ ≤ Real.exp p * Real.exp ((p + 2) ^ 7) := mul_le_mul hH hK (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (p + (p + 2) ^ 7) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          p + (p + 2) ^ 7 ≤ 2 * (p + 2) ^ 7 := by linarith
          _ ≤ (p + 2) * (p + 2) ^ 7 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = (p + 2) ^ 8 := by ring
  have hpow : (((H * rationalKernelHeight n H) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
    rw [Nat.cast_pow, Nat.cast_mul]
    apply (pow_le_pow_left₀ (by positivity) hbase d).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      (d : ℝ) * (p + 2) ^ 8 ≤ (p + 2) * (p + 2) ^ 8 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (p + 2) ^ 9 := by ring
  have hfront : 2 * ((d : ℝ) + 1) ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul htwo ((by linarith : (d : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)) (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  change ((2 * ((d + 1) * (H * rationalKernelHeight n H) ^ d) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  calc
    2 * (((d : ℝ) + 1) * (((H * rationalKernelHeight n H) ^ d : ℕ) : ℝ)) =
        (2 * ((d : ℝ) + 1)) * (((H * rationalKernelHeight n H) ^ d : ℕ) : ℝ) := by ring
    _ ≤ Real.exp (p + 1) * Real.exp ((p + 2) ^ 9) := mul_le_mul hfront hpow (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p + 1 + (p + 2) ^ 9) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hp9 : p + 1 ≤ (p + 2) ^ 9 := by
        apply (show p + 1 ≤ p + 2 by linarith).trans
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 2) (by decide : 1 ≤ 9)
      calc
        p + 1 + (p + 2) ^ 9 ≤ 2 * (p + 2) ^ 9 := by linarith
        _ ≤ (p + 2) * (p + 2) ^ 9 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (p + 2) ^ 10 := by ring

theorem imageSection_bound_le_exp (d n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (coordinateLipschitzBound d n (rationalKernelHeight n H) : ℝ) ≤ Real.exp ((p + 2) ^ 18) := by
  have hpp := le_power_budget hp (by decide : 1 ≤ 7)
  have h := coordinateLipschitzBound_le_exp d n (rationalKernelHeight n H)
    (by positivity : 0 ≤ (p + 2) ^ 7) (hd.trans hpp) (hn.trans hpp)
    (by exact_mod_cast rationalKernelHeight_le_budget n H hp hn hH)
  exact h.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 7 2))

theorem imageDefiningDenominator_le_exp {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℚ) (d H m : ℕ)
    (hQ : ∀ i j, RationalHeightLE (Q i j) (imageDefiningHeight d (Fintype.card ι) H))
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p) :
    ((matrixDenominator Q * m : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 48) := by
  have hpp := le_power_budget hp (by decide : 1 ≤ 10)
  have h := matrixDenominator_allowance_le_exp Q m (imageDefiningHeight d (Fintype.card ι) H) hQ
    (by positivity : 0 ≤ (p + 2) ^ 10) (hn.trans hpp) (hn.trans hpp)
    (imageDefiningHeight_le_exp d _ H hp hd hn hH) (hm.trans (Real.exp_le_exp.mpr hpp))
  rw [Nat.mul_comm] at h
  exact h.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 10 4))

theorem imageDefiningRow_bound_le_exp (d n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((n : ℝ) + 1) * ((imageDefiningHeight d n H : ℝ) + 1) ≤ Real.exp ((p + 2) ^ 24) := by
  have hpp := le_power_budget hp (by decide : 1 ≤ 10)
  have h := coordinateLipschitzBound_le_exp n n (imageDefiningHeight d n H)
    (by positivity : 0 ≤ (p + 2) ^ 10) (hn.trans hpp) (hn.trans hpp)
    (by exact_mod_cast imageDefiningHeight_le_exp d n H hp hd hn hH)
  apply le_trans _ (h.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 10 2)))
  change _ ≤ ((n : ℝ) + n + 1) * ((imageDefiningHeight d n H : ℝ) + 1)
  gcongr
  exact le_add_of_nonneg_left (Nat.cast_nonneg n)

theorem exists_bchLogMetricConstant_exp_bound (s : ℕ) :
    ∃ Z : ℕ, 2 ≤ Z ∧ ∀ (n H : ℕ) (p : ℝ), 0 ≤ p → (n : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (bchLogMetricConstant s n H 1 : ℝ) ≤ Real.exp ((p + Z) ^ Z + 1) := by
  obtain ⟨Z, hZ, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s 0
  refine ⟨Z, hZ, ?_⟩
  intro n H p hp hn hH
  have h := (bchBoxCoordinateBound_le_bchBoxMetricConstant s n H 1).trans
    (hbox n H 1 p hp hn hH (by simp only [NNReal.coe_one, pow_zero]; exact Real.one_le_exp (by norm_num)))
  change bchBoxCoordinateBound s n H 1 ≤ Real.exp ((p + Z) ^ Z) at h
  change bchBoxCoordinateBound s n H 1 + 1 ≤ _
  have h1 : 1 ≤ Real.exp ((p + Z) ^ Z) := Real.one_le_exp (by positivity)
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [Real.exp_add]
  nlinarith [Real.exp_pos ((p + Z) ^ Z)]

end Erdos3

end

section

namespace Erdos3

def separationBudget (p : ℝ) : ℝ := (p + 2) ^ 48 + (p + 2) ^ 24 + p + 1

theorem separationBudget_nonneg {p : ℝ} (hp : 0 ≤ p) : 0 ≤ separationBudget p := by
  unfold separationBudget
  positivity

theorem separationBudget_small {p D K r : ℝ}
    (hD : D ≤ Real.exp ((p + 2) ^ 48)) (hK : K ≤ Real.exp ((p + 2) ^ 24))
    (hK0 : 0 ≤ K) (hr0 : 0 ≤ r)
    (hr : r ≤ Real.exp p / Real.exp (separationBudget p)) :
    D * K * r < 1 := by
  calc
    D * K * r ≤ Real.exp ((p + 2) ^ 48) * Real.exp ((p + 2) ^ 24) *
        (Real.exp p / Real.exp (separationBudget p)) :=
      mul_le_mul (mul_le_mul hD hK hK0 (Real.exp_nonneg _)) hr hr0 (by positivity)
    _ = Real.exp (-1) := by
      rw [← Real.exp_sub, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold separationBudget
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr (by norm_num)

end Erdos3

end

section

namespace Erdos3

def extractedInitialParameter (p : ℝ) : ℝ := (p + 2) ^ 3 + 3 * p + 3

theorem extractedInitialParameter_controls {p : ℝ} (hp : 0 ≤ p) :
    p ≤ extractedInitialParameter p ∧ 3 * p ≤ extractedInitialParameter p ∧
      (p + 2) ^ 3 ≤ extractedInitialParameter p := by
  have h : 0 ≤ (p + 2) ^ 3 := by positivity
  unfold extractedInitialParameter
  exact ⟨by linarith, by linarith, by linarith⟩

theorem extractedInitialParameter_products {p B C : ℝ} (hp : 0 ≤ p)
    (hB : 0 ≤ B) (hBp : B ≤ Real.exp p) (hC : 0 ≤ C) (hCp : C ≤ Real.exp p)
    (δ l : ℕ) (hδ : (δ : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ B ^ 2) :
    B * C ≤ Real.exp (extractedInitialParameter p) ∧
      ((δ * l : ℕ) : ℝ) ≤ Real.exp (extractedInitialParameter p) := by
  have hq := (extractedInitialParameter_controls hp).2.1
  constructor
  · calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hBp hCp hC (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * (Real.exp p) ^ 2 := by
        apply mul_le_mul hδ _ (Nat.cast_nonneg _) (Real.exp_nonneg _)
        exact hl.trans (pow_le_pow_left₀ hB hBp 2)
      _ = Real.exp (3 * p) := by rw [pow_two, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hq

theorem exists_extractedInitialParameter_budget (C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      separationBudget (extractedInitialParameter p) ≤ (p + D) ^ D ∧
      absorbedInitialParameter (extractedInitialParameter p) ≤ (p + D) ^ D ∧
      (absorbedInitialParameter (extractedInitialParameter p) + 2) ^ 2 ≤ (p + D) ^ D ∧
      (absorbedInitialParameter (extractedInitialParameter p) + C) ^ C ≤ (p + D) ^ D := by
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ 3 + 3 * Polynomial.X + 3
  let A : Polynomial ℕ := 3 * Q + 1 + (Q + 2) ^ 36 + (Q + 2) ^ 19
  let S : Polynomial ℕ := (Q + 2) ^ 48 + (Q + 2) ^ 24 + Q + 1
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (S + A + (A + 2) ^ 2 + (A + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  have hq : 0 ≤ extractedInitialParameter p := hp.trans (extractedInitialParameter_controls hp).1
  have ha := absorbedInitialParameter_nonneg hq
  have hs := separationBudget_nonneg hq
  have h2 : 0 ≤ (absorbedInitialParameter (extractedInitialParameter p) + 2) ^ 2 := sq_nonneg _
  have hc : 0 ≤ (absorbedInitialParameter (extractedInitialParameter p) + C) ^ C := by positivity
  have hsum : separationBudget (extractedInitialParameter p) +
      absorbedInitialParameter (extractedInitialParameter p) +
      (absorbedInitialParameter (extractedInitialParameter p) + 2) ^ 2 +
      (absorbedInitialParameter (extractedInitialParameter p) + C) ^ C ≤ (p + D) ^ D := by
    simpa [Q, A, S, extractedInitialParameter, absorbedInitialParameter, separationBudget,
      Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_native_horizontal_lift_budget (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let Q := (p + a) ^ a
      let P := (Q + 3) ^ 4
      Q ≤ (p + C) ^ C ∧ separationBudget P ≤ (p + C) ^ C ∧
        (P + 2) ^ 3 + (P + 2) ^ 18 + P ≤ (p + C) ^ C ∧
        Q + s * (P + ((P + 2) ^ 3 + (P + 2) ^ 36)) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  let P := (Q + 3) ^ 4
  let B := (P + 2) ^ 48 + (P + 2) ^ 24 + P + 1
  let E := (P + 2) ^ 3 + (P + 2) ^ 18 + P
  let M := Q + Polynomial.C s * (P + ((P + 2) ^ 3 + (P + 2) ^ 36))
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + B + E + M)
  refine ⟨C, hC, ?_⟩
  intro p hp Q' P'
  have hQ : 0 ≤ Q' := by dsimp only [Q']; positivity
  have hP : 0 ≤ P' := by dsimp only [P']; positivity
  have hB := separationBudget_nonneg hP
  have hE : 0 ≤ (P' + 2) ^ 3 + (P' + 2) ^ 18 + P' := by positivity
  have hM : 0 ≤ Q' + s * (P' + ((P' + 2) ^ 3 + (P' + 2) ^ 36)) := by positivity
  have hsum : Q' + separationBudget P' + ((P' + 2) ^ 3 + (P' + 2) ^ 18 + P') +
      (Q' + s * (P' + ((P' + 2) ^ 3 + (P' + 2) ^ 36))) ≤ (p + C) ^ C := by
    simpa [X, Q, P, B, E, M, Q', P', separationBudget, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hsum, hB, hE, hM],
    by linarith only [hsum, hQ, hE, hM],
    by linarith only [hsum, hQ, hB, hM], by linarith only [hsum, hQ, hB, hE]⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι κ δ : Type*} [Field K] [AddCommGroup V] [Module K V]

def BasisBlockInvariant (b : Basis ι K V) (c : ι → δ) (U : Submodule K V) : Prop :=
  ∀ d x, x ∈ U → basisCoordinateProjection b {i | c i = d} x ∈ U

theorem sum_basisBlockProjection [Fintype ι] [DecidableEq δ]
    (b : Basis ι K V) (c : ι → δ) (x : V) :
    ∑ d ∈ Finset.univ.image c, basisCoordinateProjection b {i | c i = d} x = x := by
  classical
  apply b.repr.injective
  ext i
  have hi : c i ∈ Finset.univ.image c := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  simp only [map_sum, Finsupp.finsetSum_apply, basisCoordinateProjection_repr]
  change (∑ d ∈ Finset.univ.image c, if c i = d then b.repr x i else 0) = b.repr x i
  simp [hi]

noncomputable def blockSpanningFamily (b : Basis ι K V) (c : ι → δ) (v : κ → V) : ι × κ → V :=
  fun z => basisCoordinateProjection b {i | c i = c z.1} (v z.2)

theorem blockSpanningFamily_repr [DecidableEq δ] (b : Basis ι K V) (c : ι → δ) (v : κ → V)
    (z : ι × κ) (i : ι) :
    b.repr (blockSpanningFamily b c v z) i = if c i = c z.1 then b.repr (v z.2) i else 0 := by
  exact basisCoordinateProjection_repr b {i | c i = c z.1} (v z.2) i

theorem blockSpanningFamily_span [Fintype ι] (b : Basis ι K V) (c : ι → δ)
    (U : Submodule K V) (v : κ → V) (hspan : Submodule.span K (Set.range v) = U)
    (hU : BasisBlockInvariant b c U) :
    Submodule.span K (Set.range (blockSpanningFamily b c v)) = U := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    apply hU (c z.1) (v z.2)
    rw [← hspan]
    exact Submodule.subset_span ⟨z.2, rfl⟩
  · rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    rw [← sum_basisBlockProjection b c (v j)]
    apply Submodule.sum_mem
    intro d hd
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
    exact Submodule.subset_span ⟨(i, j), rfl⟩

theorem blockSpanningFamily_height {V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (c : ι → δ) (v : κ → V) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H) :
    ∀ z i, RationalHeightLE (b.repr (blockSpanningFamily b c v z) i) H := by
  classical
  intro z i
  rw [blockSpanningFamily_repr]
  split_ifs
  · exact hv z.2 i
  · exact rationalHeightLE_zero hH

end Erdos3

end

section

namespace Erdos3

open Module

variable {K V W ι κ δ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem basisBlockMap_commutes (e : Basis ι K V) (f : Basis κ K W)
    (c : ι → δ) (d : κ → δ) (T : V →ₗ[K] W)
    (hT : ∀ i j, d j ≠ c i → f.repr (T (e i)) j = 0) (a : δ) (x : V) :
    T (basisCoordinateProjection e {i | c i = a} x) =
      basisCoordinateProjection f {j | d j = a} (T x) := by
  classical
  have he : T.comp (basisCoordinateProjection e {i | c i = a}) =
      (basisCoordinateProjection f {j | d j = a}).comp T := by
    apply e.ext
    intro i
    apply f.repr.injective
    ext j
    by_cases hi : c i = a <;> by_cases hj : d j = a
    · simp [LinearMap.comp_apply, basisCoordinateProjection_basis, basisCoordinateProjection_repr, hi, hj]
    · have hij : d j ≠ c i := fun h => hj (h.trans hi)
      simp [LinearMap.comp_apply, basisCoordinateProjection_basis, basisCoordinateProjection_repr, hi, hj, hT i j hij]
    · have hij : d j ≠ c i := fun h => hi (h.symm.trans hj)
      simp [LinearMap.comp_apply, basisCoordinateProjection_basis, basisCoordinateProjection_repr, hi, hj, hT i j hij]
    · simp [LinearMap.comp_apply, basisCoordinateProjection_basis, basisCoordinateProjection_repr, hi, hj]
  exact DFunLike.congr_fun he x

theorem BasisBlockInvariant.map (e : Basis ι K V) (f : Basis κ K W)
    (c : ι → δ) (d : κ → δ) (T : V →ₗ[K] W)
    (hT : ∀ i j, d j ≠ c i → f.repr (T (e i)) j = 0)
    (U : Submodule K V) (hU : BasisBlockInvariant e c U) :
    BasisBlockInvariant f d (U.map T) := by
  rintro a y ⟨x, hx, rfl⟩
  exact ⟨basisCoordinateProjection e {i | c i = a} x, hU a x hx,
    basisBlockMap_commutes e f c d T hT a x⟩

theorem basisBlockInvariant_ker (e : Basis ι K V) (f : Basis κ K W)
    (c : ι → δ) (d : κ → δ) (T : V →ₗ[K] W)
    (hT : ∀ i j, d j ≠ c i → f.repr (T (e i)) j = 0) :
    BasisBlockInvariant e c (LinearMap.ker T) := by
  intro a x hx
  change T (basisCoordinateProjection e {i | c i = a} x) = 0
  rw [basisBlockMap_commutes e f c d T hT a x, show T x = 0 from hx, map_zero]

theorem BasisBlockInvariant.inf (e : Basis ι K V) (c : ι → δ)
    (U Z : Submodule K V) (hU : BasisBlockInvariant e c U) (hZ : BasisBlockInvariant e c Z) :
    BasisBlockInvariant e c (U ⊓ Z) :=
  fun a x hx => ⟨hU a x hx.1, hZ a x hx.2⟩

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

section Algebra

variable {ι κ μ δ K : Type*} [Semiring K]

noncomputable def matrixBlockPart (r : ι → δ) (c : κ → δ) (A : Matrix ι κ K) : Matrix ι κ K := by
  classical
  exact fun i j => if r i = c j then A i j else 0

theorem matrixBlockPart_eq (r : ι → δ) (c : κ → δ) (A : Matrix ι κ K)
    (hA : ∀ i j, r i ≠ c j → A i j = 0) : matrixBlockPart r c A = A := by
  classical
  ext i j
  by_cases h : r i = c j
  · simp only [matrixBlockPart, h, ↓reduceIte]
  · simp only [matrixBlockPart, h, ↓reduceIte, hA i j h]

theorem matrixBlockPart_off_block (r : ι → δ) (c : κ → δ) (A : Matrix ι κ K)
    (i : ι) (j : κ) (h : r i ≠ c j) : matrixBlockPart r c A i j = 0 := by
  classical
  simp only [matrixBlockPart, h, ↓reduceIte]

theorem matrix_mul_blockPart [Fintype κ] (r : ι → δ) (c : κ → δ) (d : μ → δ)
    (A : Matrix ι κ K) (B : Matrix κ μ K)
    (hA : ∀ i j, r i ≠ c j → A i j = 0) :
    A * matrixBlockPart c d B = matrixBlockPart r d (A * B) := by
  classical
  ext i k
  have hterm (j : κ) :
      A i j * (if c j = d k then B j k else 0) =
        if r i = d k then A i j * B j k else 0 := by
    by_cases hij : r i = c j
    · rw [hij]
      split_ifs <;> simp only [mul_zero]
    · rw [hA i j hij]
      split_ifs <;> simp only [zero_mul]
  simp only [Matrix.mul_apply, matrixBlockPart, hterm]
  by_cases h : r i = d k <;> simp only [h, ↓reduceIte, Finset.sum_const_zero]

theorem matrix_blockPart_mul [Fintype κ] (r : ι → δ) (c : κ → δ) (d : μ → δ)
    (A : Matrix ι κ K) (B : Matrix κ μ K)
    (hB : ∀ j k, c j ≠ d k → B j k = 0) :
    matrixBlockPart r c A * B = matrixBlockPart r d (A * B) := by
  classical
  ext i k
  have hterm (j : κ) :
      (if r i = c j then A i j else 0) * B j k =
        if r i = d k then A i j * B j k else 0 := by
    by_cases hjk : c j = d k
    · rw [hjk]
      split_ifs <;> simp only [zero_mul]
    · rw [hB j k hjk]
      split_ifs <;> simp only [mul_zero]
  simp only [Matrix.mul_apply, matrixBlockPart, hterm]
  by_cases h : r i = d k <;> simp only [h, ↓reduceIte, Finset.sum_const_zero]

theorem matrixBlockPart_image_section [Fintype ι] [Fintype κ]
    (r : ι → δ) (c : κ → δ) (A : Matrix ι κ K) (S : Matrix κ ι K)
    (hA : ∀ i j, r i ≠ c j → A i j = 0) (hS : A * S * A = A) :
    A * matrixBlockPart c r S * A = A := by
  rw [matrix_mul_blockPart r c r A S hA, matrix_blockPart_mul r r c (A * S) A hA,
    hS, matrixBlockPart_eq r c A hA]

end Algebra

theorem exists_bounded_block_image_section {ι κ δ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → δ) (c : κ → δ) (A : Matrix ι κ ℚ)
    (hblock : ∀ i j, r i ≠ c j → A i j = 0) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ S : Matrix κ ι ℚ, A * S * A = A ∧
      (∀ i j, c i ≠ r j → S i j = 0) ∧
      ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H) := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH hA
  refine ⟨matrixBlockPart c r S, matrixBlockPart_image_section r c A S hblock hS,
    matrixBlockPart_off_block c r S, ?_⟩
  intro i j
  by_cases h : c i = r j
  · simpa only [matrixBlockPart, h, ↓reduceIte] using hSH i j
  · simpa only [matrixBlockPart, h, ↓reduceIte] using
      rationalHeightLE_zero (rationalKernelHeight_pos (Fintype.card ι) hH)

end Erdos3

end

section

open scoped Matrix

namespace Erdos3

theorem real_matrix_image_section {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (S : Matrix κ ι ℚ) (hS : A * S * A = A) :
    Matrix.of (fun i j => (A i j : ℝ)) * Matrix.of (fun i j => (S i j : ℝ)) *
      Matrix.of (fun i j => (A i j : ℝ)) = Matrix.of (fun i j => (A i j : ℝ)) := by
  ext i j
  have he := congrArg (fun q : ℚ => (q : ℝ)) (congrFun (congrFun hS i) j)
  simpa only [Matrix.mul_apply, Matrix.of_apply, Rat.cast_sum, Rat.cast_mul] using he

theorem exists_real_span_defining_matrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ Q : Matrix ι ι ℚ,
      (∀ i j, RationalHeightLE (Q i j) (imageDefiningHeight (Fintype.card κ) (Fintype.card ι) H)) ∧
      LinearMap.ker (Matrix.mulVecLin (fun i j => (Q i j : ℝ))) =
        LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH hA
  let Q : Matrix ι ι ℚ := 1 - A * S
  have hSr := real_matrix_image_section A S hS
  have hQr : Matrix.of (fun i j => (Q i j : ℝ)) =
      1 - Matrix.of (fun i j => (A i j : ℝ)) * Matrix.of (fun i j => (S i j : ℝ)) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Q, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, hij]
  refine ⟨Q, ?_, ?_⟩
  · intro i j
    have hI : RationalHeightLE ((1 : Matrix ι ι ℚ) i j) 1 := by
      by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
    have hprod := rationalHeightLE_matrix_mul A S hA hSH i j
    simpa only [Q, Matrix.sub_apply, imageDefiningHeight, mul_one] using hI.sub hprod
  · ext x
    change Matrix.of (fun i j => (Q i j : ℝ)) *ᵥ x = 0 ↔
      ∃ y, Matrix.of (fun i j => (A i j : ℝ)) *ᵥ y = x
    rw [hQr, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    constructor
    · intro hx
      exact ⟨(fun i j => (S i j : ℝ)) *ᵥ x, (sub_eq_zero.mp hx).symm⟩
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hSr, sub_self]

theorem real_column_span_mem_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (x : ι → ℝ) :
    x ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) ↔
      x ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
  have h := congrArg (fun U : Submodule ℝ (ι → ℝ) => x ∈ U)
    (Matrix.range_mulVecLin (Matrix.of (fun i j => (A i j : ℝ))))
  exact (iff_of_eq h).symm

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem imageDefiningHeight_pos (d n H : ℕ) (hH : 1 ≤ H) :
    0 < imageDefiningHeight d n H := by
  have hHp : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hH
  have hK := rationalKernelHeight_pos n hH
  unfold imageDefiningHeight
  positivity

theorem exists_bounded_block_quotient_projection {ι κ δ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → δ) (d : κ → δ) (A : Matrix ι κ ℚ)
    (hblock : ∀ i j, c i ≠ d j → A i j = 0) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ Q : Matrix ι ι ℚ, Q * Q = Q ∧
      LinearMap.ker Q.mulVecLin = LinearMap.range A.mulVecLin ∧
      (∀ i j, c i ≠ c j → Q i j = 0) ∧
      ∀ i j, RationalHeightLE (Q i j) (imageDefiningHeight (Fintype.card κ) (Fintype.card ι) H) := by
  classical
  obtain ⟨S, hS, hSb, hSH⟩ := exists_bounded_block_image_section c d A hblock hH hA
  let Q : Matrix ι ι ℚ := 1 - A * S
  have hId : (A * S) * (A * S) = A * S := by rw [← Matrix.mul_assoc, hS]
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · dsimp only [Q]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hId, sub_self, sub_zero]
  · ext x
    change (1 - A * S) *ᵥ x = 0 ↔ ∃ y, A *ᵥ y = x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    constructor
    · intro hx
      exact ⟨S *ᵥ x, (sub_eq_zero.mp hx).symm⟩
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hS, sub_self]
  · intro i j hij
    have hne : i ≠ j := fun h => hij (congrArg c h)
    have hprod : (A * S) i j = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hik : c i = d k
      · exact (congrArg (fun z : ℚ => A i k * z)
          (hSb k j (fun hkj => hij (hik.trans hkj)))).trans (mul_zero _)
      · exact (congrArg (fun z : ℚ => z * S k j) (hblock i k hik)).trans (zero_mul _)
    simp only [Q, Matrix.sub_apply, Matrix.one_apply, hne, ↓reduceIte, hprod, sub_self]
  · intro i j
    have hI : RationalHeightLE ((1 : Matrix ι ι ℚ) i j) 1 := by
      by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
    have hp := rationalHeightLE_matrix_mul A S hA hSH i j
    simpa only [Q, Matrix.sub_apply, imageDefiningHeight, mul_one] using hI.sub hp

theorem exists_submodule_block_quotient_projection
    {V ι κ δ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ]
    (b : Basis ι ℚ V) (c : ι → δ) (U : Submodule ℚ V) (v : κ → V)
    (hspan : Submodule.span ℚ (Set.range v) = U) (hU : BasisBlockInvariant b c U)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H) :
    ∃ Q : Matrix ι ι ℚ, Q * Q = Q ∧
      LinearMap.ker Q.mulVecLin = U.map b.equivFun.toLinearMap ∧
      (∀ i j, c i ≠ c j → Q i j = 0) ∧
      ∀ i j, RationalHeightLE (Q i j)
        (imageDefiningHeight (Fintype.card ι * Fintype.card κ) (Fintype.card ι) H) := by
  classical
  let v' := blockSpanningFamily b c v
  let A : Matrix ι (ι × κ) ℚ := fun i j => b.repr (v' j) i
  have hA : ∀ i j, RationalHeightLE (A i j) H :=
    fun i j => blockSpanningFamily_height b c v hH hv j i
  have hAb : ∀ i j, c i ≠ c j.1 → A i j = 0 := by
    intro i j hij
    exact (blockSpanningFamily_repr b c v j i).trans (if_neg hij)
  have he := exists_bounded_block_quotient_projection c (fun j : ι × κ => c j.1) A hAb hH hA
  obtain ⟨Q, hQQ, hker, hblock, hQ⟩ := he
  refine ⟨Q, hQQ, hker.trans ?_, hblock, ?_⟩
  · rw [Matrix.range_mulVecLin, ← blockSpanningFamily_span b c U v hspan hU,
      Submodule.map_span, ← Set.range_comp]
    rfl
  · simpa only [Fintype.card_prod] using hQ

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem exists_real_block_span_defining_matrix {ι κ δ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → δ) (c : κ → δ) (A : Matrix ι κ ℚ)
    (hblock : ∀ i j, r i ≠ c j → A i j = 0) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ Q : Matrix ι ι ℚ,
      (∀ i j, RationalHeightLE (Q i j) (imageDefiningHeight (Fintype.card κ) (Fintype.card ι) H)) ∧
      (∀ i j, r i ≠ r j → Q i j = 0) ∧
      LinearMap.ker (Matrix.mulVecLin (fun i j => (Q i j : ℝ))) =
        LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
  classical
  obtain ⟨S, hS, hSb, hSH⟩ := exists_bounded_block_image_section r c A hblock hH hA
  let Q : Matrix ι ι ℚ := 1 - A * S
  have hSr := real_matrix_image_section A S hS
  have hQr : Matrix.of (fun i j => (Q i j : ℝ)) =
      1 - Matrix.of (fun i j => (A i j : ℝ)) * Matrix.of (fun i j => (S i j : ℝ)) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Q, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, hij]
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro i j
    have hI : RationalHeightLE ((1 : Matrix ι ι ℚ) i j) 1 := by
      by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
    have hprod := rationalHeightLE_matrix_mul A S hA hSH i j
    simpa only [Q, Matrix.sub_apply, imageDefiningHeight, mul_one] using hI.sub hprod
  · intro i j hij
    have hne : i ≠ j := fun h => hij (congrArg r h)
    have hprod : (A * S) i j = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hik : r i = c k
      · exact (congrArg (fun x : ℚ => A i k * x)
          (hSb k j (fun hkj => hij (hik.trans hkj)))).trans (mul_zero _)
      · exact (congrArg (fun x : ℚ => x * S k j) (hblock i k hik)).trans (zero_mul _)
    simp only [Q, Matrix.sub_apply, Matrix.one_apply, hne, ↓reduceIte, hprod, sub_self]
  · ext x
    change Matrix.of (fun i j => (Q i j : ℝ)) *ᵥ x = 0 ↔
      ∃ y, Matrix.of (fun i j => (A i j : ℝ)) *ᵥ y = x
    rw [hQr, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    constructor
    · intro hx
      exact ⟨(fun i j => (S i j : ℝ)) *ᵥ x, (sub_eq_zero.mp hx).symm⟩
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hSr, sub_self]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι]
  (b : Basis ι ℚ V) (U : Submodule ℚ V) (Q : Matrix ι ι ℚ)
  (hker : LinearMap.ker Q.mulVecLin = U.map b.equivFun.toLinearMap)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization
namespace OAI

section

open scoped Matrix NNReal

namespace Erdos3

theorem real_matrix_image_section_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (S : Matrix κ ι ℚ) (hS : A * S * A = A)
    (y : ι → ℝ) (hy : y ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ)))) :
    (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ y) = y := by
  obtain ⟨x, rfl⟩ := hy
  change Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
    (Matrix.of (fun i j => (S i j : ℝ)) *ᵥ
      (Matrix.of (fun i j => (A i j : ℝ)) *ᵥ x)) =
    Matrix.of (fun i j => (A i j : ℝ)) *ᵥ x
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, real_matrix_image_section A S hS]

theorem norm_matrix_mulVec_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : Matrix ι κ ℝ) (H : ℝ≥0) (hQ : ∀ i j, |Q i j| ≤ H) (x : κ → ℝ) :
    ‖Q *ᵥ x‖ ≤ ((Fintype.card κ : ℝ) + 1) * (H + 1) * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using abs_matrix_mulVec_le Q H hQ x i

theorem real_image_section_norm_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix κ ι ℚ) (H : ℕ)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) (x : ι → ℝ) :
    ‖(fun i j => (S i j : ℝ)) *ᵥ x‖ ≤ Real.exp ((p + 2) ^ 18) * ‖x‖ := by
  have hnorm := norm_matrix_mulVec_le (fun i j => (S i j : ℝ))
    (rationalKernelHeight (Fintype.card ι) H : ℝ≥0) (fun i j => (hS i j).abs_real_le) x
  have hfac : ((Fintype.card ι : ℝ) + 1) *
      ((rationalKernelHeight (Fintype.card ι) H : ℝ) + 1) ≤
      (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι)
        (rationalKernelHeight (Fintype.card ι) H) : ℝ) := by
    change _ ≤ ((Fintype.card κ : ℝ) + Fintype.card ι + 1) *
      ((rationalKernelHeight (Fintype.card ι) H : ℝ) + 1)
    gcongr
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  exact hnorm.trans (mul_le_mul_of_nonneg_right
    (hfac.trans (imageSection_bound_le_exp (Fintype.card κ) (Fintype.card ι) H hp hκ hι hH))
    (norm_nonneg _))

theorem real_image_section_denominator_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix κ ι ℚ) (H l : ℕ)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((matrixDenominator S * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 36) := by
  have hpq : p ≤ (p + 2) ^ 7 := le_power_budget hp (by decide)
  have h := matrixDenominator_allowance_le_exp S l (rationalKernelHeight (Fintype.card ι) H)
    hS (by positivity : 0 ≤ (p + 2) ^ 7) (hκ.trans hpq) (hι.trans hpq)
    (rationalKernelHeight_le_budget (Fintype.card ι) H hp hι hH)
    (hl.trans (Real.exp_le_exp.mpr hpq))
  rw [Nat.mul_comm] at h
  exact h.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 7 4))

end Erdos3

end

section

open scoped Matrix NNReal

namespace Erdos3

theorem controlled_real_column_span_separation
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    {α : σ →₀ ℕ} (hα : α ≠ 0) (a b : ι → ℝ)
    (ha : ‖a‖ ≤ Real.exp p / monomialScale T α)
    (hb : b ∈ realDenominatorGrid l)
    (hsum : a + b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ)))) :
    a ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) ∧
      b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) := by
  obtain ⟨Q, hQ, hker⟩ := exists_real_span_defining_matrix A hH hA
  have hscale : Real.exp (separationBudget p) ≤ monomialScale T α :=
    le_monomialScale_of_ne_zero T (Real.one_le_exp (separationBudget_nonneg hp)) hT hα
  have hasmall : ‖a‖ ≤ Real.exp p / Real.exp (separationBudget p) :=
    ha.trans (div_le_div_of_nonneg_left (Real.exp_nonneg p) (Real.exp_pos _) hscale)
  have hden := imageDefiningDenominator_le_exp Q (Fintype.card κ) H l hQ hp hκ hι hHp hlp
  have hrow := imageDefiningRow_bound_le_exp (Fintype.card κ) (Fintype.card ι) H hp hκ hι hHp
  have hnear : ((matrixDenominator Q * l : ℕ) : ℝ) *
      (((Fintype.card ι : ℝ) + 1) *
        ((imageDefiningHeight (Fintype.card κ) (Fintype.card ι) H : ℝ) + 1)) *
      dist b (a + b) < 1 := by
    have he : b - (a + b) = -a := by abel
    rw [dist_eq_norm, he, norm_neg]
    exact separationBudget_small hden hrow (by positivity) (norm_nonneg _) hasmall
  have hsumker : (fun i j => (Q i j : ℝ)) *ᵥ (a + b) = 0 := by
    have h := (real_column_span_mem_iff A (a + b)).mp hsum
    rw [← hker] at h
    exact h
  have hbker := rational_matrix_kernel_separation Q
    (imageDefiningHeight (Fintype.card κ) (Fintype.card ι) H : ℝ≥0)
    (fun i j => (hQ i j).abs_real_le) l hl b (a + b) hb hsumker hnear
  have hbrange : b ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
    rw [← hker]
    exact hbker
  have hbspan := (real_column_span_mem_iff A b).mpr hbrange
  refine ⟨?_, hbspan⟩
  simpa only [add_sub_cancel_right] using
    (Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ)))).sub_mem hsum hbspan

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped Matrix BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

theorem weighted_matrix_mulVec_bound {ι κ δ : Type*} [Fintype κ]
    (r : ι → δ) (c : κ → δ) (A : Matrix ι κ ℝ)
    (hblock : ∀ i j, r i ≠ c j → A i j = 0)
    (H : ℝ≥0) (hA : ∀ i j, |A i j| ≤ H)
    (W : δ → ℝ) (hW : ∀ d, 0 < W d) {M : ℝ} (hM : 0 ≤ M)
    (x : κ → ℝ) (hx : ∀ j, |x j| ≤ M / W (c j)) (i : ι) :
    |(A *ᵥ x) i| ≤ ((Fintype.card κ : ℝ) + 1) * (H + 1) * M / W (r i) := by
  classical
  have hdiv : 0 ≤ M / W (r i) := div_nonneg hM (hW _).le
  calc
    _ ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, (H : ℝ) * (M / W (r i)) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : r i = c j
      · rw [abs_mul]
        exact mul_le_mul (hA i j) (by simpa only [h] using hx j) (abs_nonneg _) H.coe_nonneg
      · rw [hblock i j h, zero_mul, abs_zero]
        exact mul_nonneg H.coe_nonneg hdiv
    _ = (Fintype.card κ : ℝ) * H * (M / W (r i)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ ((Fintype.card κ : ℝ) + 1) * (H + 1) * (M / W (r i)) := by
      gcongr <;> linarith
    _ = _ := by ring

theorem real_image_section_weighted_bound {ι κ δ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → δ) (c : κ → δ) (S : Matrix κ ι ℚ) (H : ℕ)
    (hblock : ∀ i j, c i ≠ r j → S i j = 0)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (W : δ → ℝ) (hW : ∀ d, 0 < W d) {M : ℝ} (hM : 0 ≤ M)
    (x : ι → ℝ) (hx : ∀ j, |x j| ≤ M / W (r j)) (i : κ) :
    |((fun i j => (S i j : ℝ)) *ᵥ x) i| ≤
      Real.exp ((p + 2) ^ 18) * M / W (c i) := by
  have hbound := weighted_matrix_mulVec_bound c r (fun i j => (S i j : ℝ))
    (fun i j h => by rw [hblock i j h, Rat.cast_zero])
    (rationalKernelHeight (Fintype.card ι) H : ℝ≥0) (fun i j => (hS i j).abs_real_le)
    W hW hM x hx i
  have hfac : ((Fintype.card ι : ℝ) + 1) *
      ((rationalKernelHeight (Fintype.card ι) H : ℝ) + 1) ≤
      (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι)
        (rationalKernelHeight (Fintype.card ι) H) : ℝ) := by
    change _ ≤ ((Fintype.card κ : ℝ) + Fintype.card ι + 1) *
      ((rationalKernelHeight (Fintype.card ι) H : ℝ) + 1)
    gcongr
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ (hW _).le
  exact mul_le_mul_of_nonneg_right
    (hfac.trans (imageSection_bound_le_exp (Fintype.card κ) (Fintype.card ι) H hp hκ hι hH)) hM

end Erdos3

end

section

open scoped Matrix

namespace Erdos3

theorem exists_controlled_linear_splitting
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ (S : Matrix κ ι ℚ) (m : ℕ), 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (a b : ι → ℝ) (v : κ → ℝ),
      ‖a‖ ≤ Real.exp p / monomialScale T α → b ∈ realDenominatorGrid l →
      (fun i j => (A i j : ℝ)) *ᵥ v = a + b →
      (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ a) = a ∧
      (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ b) = b ∧
      ‖(fun i j => (S i j : ℝ)) *ᵥ a‖ ≤
        Real.exp ((p + 2) ^ 18 + p) / monomialScale T α ∧
      (fun i j => (S i j : ℝ)) *ᵥ b ∈ realDenominatorGrid m ∧
      (fun i j => (A i j : ℝ)) *ᵥ
        (v - (fun i j => (S i j : ℝ)) *ᵥ a - (fun i j => (S i j : ℝ)) *ᵥ b) = 0 := by
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH hA
  refine ⟨S, matrixDenominator S * l, Nat.mul_pos (matrixDenominator_pos S) hl,
    real_image_section_denominator_bound S H l hSH hp hι hκ hHp hlp, ?_⟩
  intro α hα a b v ha hb hv
  have hsum : a + b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) :=
    (real_column_span_mem_iff A (a + b)).mpr ⟨v, hv⟩
  obtain ⟨haspan, hbspan⟩ := controlled_real_column_span_separation A hH hl hA hp hι hκ
    hHp hlp T hT hα a b ha hb hsum
  have hSa := real_matrix_image_section_apply A S hS a ((real_column_span_mem_iff A a).mp haspan)
  have hSb := real_matrix_image_section_apply A S hS b ((real_column_span_mem_iff A b).mp hbspan)
  refine ⟨hSa, hSb, ?_, real_matrix_denominator_grid S l b hb, ?_⟩
  · calc
      _ ≤ Real.exp ((p + 2) ^ 18) * ‖a‖ := real_image_section_norm_bound S H hSH hp hι hκ hHp a
      _ ≤ Real.exp ((p + 2) ^ 18) * (Real.exp p / monomialScale T α) :=
        mul_le_mul_of_nonneg_left ha (Real.exp_nonneg _)
      _ = _ := by rw [← mul_div_assoc, ← Real.exp_add]
  · change Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
      (v - Matrix.of (fun i j => (S i j : ℝ)) *ᵥ a -
        Matrix.of (fun i j => (S i j : ℝ)) *ᵥ b) = 0
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
    exact (congrArg₂ (fun x y : ι → ℝ => x - y)
      (congrArg₂ (fun x y : ι → ℝ => x - y) hv hSa) hSb).trans (by abel)

end Erdos3

end

section

namespace Erdos3

section Algebra

variable {R E H : Type*} [Field R] [AddCommGroup E] [Module R E]
  [AddCommGroup H] [Module R H]

theorem horizontal_remove_zero (P : E →ₗ[R] H) (a b : E ≃ₗ[R] E)
    (ha : ∀ x, P (a x) = P x) (hb : ∀ x, P (b x) = P x)
    (s r ya yb : E) (hya : P ya = P s) (hyb : P yb = P r) :
    P (a.symm (s - ya)) = 0 ∧ P (b r - yb) = 0 := by
  constructor
  · have he := ha (a.symm (s - ya))
    rw [LinearEquiv.apply_symm_apply] at he
    rw [← he, map_sub, hya, sub_self]
  · rw [map_sub, hb, hyb, sub_self]

theorem horizontal_derivative_of_zero_parts (U K : Submodule R H) (P : E →ₗ[R] H)
    (f : E →ₗ[R] E) (hf : P.comp f = P) (S : K →ₗ[R] E)
    (hS : P.comp S = K.subtype) (y s r : E) (k : K)
    (hsystem : y = s + f r + S k) (hs : P s = 0) (hr : P r = 0) (hk : k.val ∈ U) :
    P y = k.val ∧ P y ∈ U ⊓ K := by
  have he : P y = k.val := by
    rw [hsystem, map_add, map_add, hs,
      show P (f r) = P r from DFunLike.congr_fun hf r, hr,
      show P (S k) = k.val from DFunLike.congr_fun hS k, zero_add, zero_add]
  exact ⟨he, he.symm ▸ ⟨hk, k.property⟩⟩

end Algebra

theorem horizontal_parts_separation {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (U K : Submodule ℝ (ι → ℝ)) (A : Matrix ι κ ℚ)
    (hspan : Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) = U ⊔ K)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l) (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    {α : σ →₀ ℕ} (hα : α ≠ 0) (y s r k : ι → ℝ)
    (hsystem : y = s + r + k) (hy : y ∈ U) (hk : k ∈ K)
    (hs : ‖s‖ ≤ Real.exp p / monomialScale T α) (hr : r ∈ realDenominatorGrid l) :
    s ∈ U ⊔ K ∧ r ∈ U ⊔ K := by
  have hsum : s + r ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) := by
    rw [hspan]
    have hmem := (U ⊔ K).sub_mem ((show U ≤ U ⊔ K from le_sup_left) hy)
      ((show K ≤ U ⊔ K from le_sup_right) hk)
    simpa only [hsystem, add_sub_cancel_right] using hmem
  have he := controlled_real_column_span_separation A hH hl hA hp hι hκ hHp hlp T hT hα s r hs hr hsum
  simpa only [hspan] using he

end Erdos3

end

section

namespace Erdos3

theorem controlled_small_vector_separation
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) (a b : ι → ℝ)
    (ha : ‖a‖ ≤ Real.exp p / Real.exp (separationBudget p))
    (hb : b ∈ realDenominatorGrid l)
    (hsum : a + b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ)))) :
    a ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) ∧
      b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) := by
  apply controlled_real_column_span_separation A hH hl hA hp hι hκ hHp hlp
    (fun _ : Unit => Real.exp (separationBudget p)) (fun _ => le_rfl)
    (α := Finsupp.single () 1) (by simp) a b
  · simpa only [monomialScale, Finsupp.prod_single_index, pow_zero, pow_one] using ha
  · exact hb
  · exact hsum

end Erdos3

end

section

namespace Erdos3

variable {σ G E H R : Type*} [Group G] [Field R]
  [AddCommGroup E] [Module R E] [AddCommGroup H] [Module R H]

theorem cocycle_horizontal_normalization
    (ρ : G →* (E ≃ₗ[R] E)) (Y : G → σ → E)
    (hY : ∀ g h i, Y (g * h) i = Y g i + ρ g (Y h i))
    (P : E →ₗ[R] H) (hρ : ∀ g x, P (ρ g x) = P x)
    (U K : Submodule R H) (B a c : G) (S T : K →ₗ[R] E)
    (hST : S = (ρ B).toLinearMap.comp T)
    (hS : P.comp S = K.subtype) (hT : P.comp T = K.subtype)
    (small rational : σ → E) (k : σ → K)
    (hsystem : ∀ i, Y B i = small i + ρ B (rational i) + S (k i))
    (ha : ∀ i, P (Y a i) = P (small i)) (hc : ∀ i, P (Y c i) = P (rational i))
    (hk : ∀ i, (k i).val ∈ U) :
    let B' := a⁻¹ * B * c⁻¹
    let S' := (ρ a).symm.toLinearMap.comp S
    let T' := (ρ c).toLinearMap.comp T
    let small' := fun i => (ρ a).symm (small i - Y a i)
    let rational' := fun i => ρ c (rational i) - Y c i
    a * B' * c = B ∧ S' = (ρ B').toLinearMap.comp T' ∧
      P.comp S' = K.subtype ∧ P.comp T' = K.subtype ∧
      ∀ i, Y B' i = small' i + ρ B' (rational' i) + S' (k i) ∧
        P (small' i) = 0 ∧ P (rational' i) = 0 ∧ P (Y B' i) = (k i).val ∧
        P (Y B' i) ∈ U ⊓ K := by
  let B' := a⁻¹ * B * c⁻¹
  let S' := (ρ a).symm.toLinearMap.comp S
  let T' := (ρ c).toLinearMap.comp T
  let small' := fun i => (ρ a).symm (small i - Y a i)
  let rational' := fun i => ρ c (rational i) - Y c i
  have hprod : a * B' * c = B := by dsimp [B']; group
  have haction (x : E) : ρ B x = ρ a (ρ B' (ρ c x)) := by
    rw [← hprod]
    exact linear_action_triple ρ a B' c x
  have hfac : S' = (ρ B').toLinearMap.comp T' :=
    linear_lift_remove (ρ a) (ρ c) (ρ B) (ρ B') haction S T hST
  have hhor := horizontal_lift_remove P (ρ a) (ρ c) (hρ a) (hρ c) S T K.subtype hS hT
  refine ⟨hprod, hfac, hhor.1, hhor.2, fun i => ?_⟩
  have htriple := linear_cocycle_triple ρ (fun g => Y g i)
    (fun g h => hY g h i) a B' c
  rw [hprod] at htriple
  have hnew : Y B' i = small' i + ρ B' (rational' i) + S' (k i) :=
    linear_derivative_remove (ρ a) (ρ c) (ρ B) (ρ B') haction
      (Y B i) (Y a i) (Y B' i) (Y c i) (small i) (rational i) (S (k i)) htriple (hsystem i)
  have hzero := horizontal_remove_zero P (ρ a) (ρ c) (hρ a) (hρ c)
    (small i) (rational i) (Y a i) (Y c i) (ha i) (hc i)
  have hPB : P.comp (ρ B').toLinearMap = P := by
    ext x
    exact hρ B' x
  have hfinal := horizontal_derivative_of_zero_parts U K P (ρ B').toLinearMap hPB S'
    hhor.1 (Y B' i) (small' i) (rational' i) (k i) hnew hzero.1 hzero.2 (hk i)
  exact ⟨hnew, hzero.1, hzero.2, hfinal.1, hfinal.2⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CommonCorrectionBudget
namespace OAI

section

namespace Erdos3

theorem exists_common_correction_budget (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (p + (s + 2)) ^ (s + 2) * (p + 1) + (p + 2) ^ a + p + 2
      let t := ((q + 2) ^ 10 + 2) ^ 4
      separationBudget t + (t + 2) ^ 36 + ((t + 2) ^ 18 + t) ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) * (Polynomial.X + 1) +
    (Polynomial.X + 2) ^ a + Polynomial.X + 2
  let J : Polynomial ℕ := ((P + 2) ^ 10 + 2) ^ 4
  let B : Polynomial ℕ := (J + 2) ^ 48 + (J + 2) ^ 24 + J + 1 +
    (J + 2) ^ 36 + ((J + 2) ^ 18 + J)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [B, J, P, separationBudget, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ConjugationDenominatorBudget
namespace OAI

section

namespace Erdos3

open Module

theorem exists_conjugation_denominator_exp_bound (s : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) : ℝ) ≤
        Real.exp ((p + K) ^ K) := by
  obtain ⟨C, hC, hcoeff⟩ := exists_bchProductCoordinatePolynomial_exp_budget s
  let K := C + 3 * s + 10
  refine ⟨K, by dsimp [K]; omega, ?_⟩
  intro ι L _ _ _ e H p hp hd hH hc
  let t := p + K
  have hK : (s : ℝ) + 3 ≤ K := by exact_mod_cast (show s + 3 ≤ K by dsimp [K]; omega)
  have ht : 3 ≤ t := by dsimp [t]; linarith
  have hpt : p + 3 ≤ t := by dsimp [t]; linarith
  have hs : (s : ℝ) + 1 ≤ t := by dsimp [t]; linarith
  have hshift : p + 3 + C ≤ t := by
    have h : C + 3 ≤ K := by dsimp [K]; omega
    have h' : (C : ℝ) + 3 ≤ K := by exact_mod_cast h
    dsimp [t]
    linarith
  have hcoeff' : ∀ i m, (((conjugationCoordinatePolynomial e s i).coeff m).den : ℝ) ≤
      Real.exp (t ^ C) := by
    intro i m
    have h := (hcoeff (lieStructureConstants e) H (p + 3) ([0, 1, 2] : List (Fin 3))
      (by positivity) (by linarith) (by simp; linarith) (by simp; linarith)
      (hH.trans (Real.exp_le_exp.mpr (by linarith))) hc i m).2
    exact h.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) hshift C))
  have hcard : ∀ i, ((conjugationCoordinatePolynomial e s i).support.card : ℝ) ≤ t ^ (2 * s + 1) := by
    intro i
    have h := (Nat.cast_le (α := ℝ)).mpr
      (bchProductCoordinatePolynomial_support_card (lieStructureConstants e) s ([0, 1, 2] : List (Fin 3)) i)
    simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h
    have hb : 3 * (Fintype.card ι : ℝ) + 1 ≤ t ^ 2 := by nlinarith [sq_nonneg p]
    apply h.trans
    calc
      _ ≤ t * (t ^ 2) ^ s := mul_le_mul hs (pow_le_pow_left₀ (by positivity) hb s) (by positivity) (by linarith)
      _ = t ^ (2 * s + 1) := by rw [← pow_mul, pow_succ']
  have hD := polynomialFamilyDenominator_exp_bound (conjugationCoordinatePolynomial e s)
    (p := t - 2) (by linarith) C 1 (2 * s + 1)
    (by simpa only [sub_add_cancel] using hcoeff')
    (by simpa only [sub_add_cancel] using hcard)
    (by rw [sub_add_cancel, pow_one]; linarith)
  rw [sub_add_cancel] at hD
  apply hD.trans
  exact Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith) (by dsimp [K]; omega))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ConjugatedLatticeGrids
namespace OAI

section

namespace Erdos3

open Module

theorem denominatorGrid_neg {ι : Type*} (q : ℕ) {x : ι → ℚ}
    (hx : x ∈ denominatorGrid q) : -x ∈ denominatorGrid q := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨-z, ?_⟩
  intro i
  have hi : (q : ℚ) * x i = (z i : ℚ) := hz i
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Int.cast_neg, mul_neg, hi]

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem conjugated_subgroup_inner_grid (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l q : ℕ) (hq : 0 < q)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (z : NilpotentLieBCHGroup L s hnil) (hz : e.equivFun z.coord ∈ denominatorGrid q) :
    scaledIntegerGrid (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * q ^ s) ⊆
      bchSubgroupCoordinates e (Γ.map (MulAut.conj z).toMonoidHom) := by
  intro x hx
  let g : NilpotentLieBCHGroup L s hnil := ⟨e.equivFun.symm x⟩
  have hg : e.equivFun g.coord ∈ scaledIntegerGrid
      (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * q ^ s) := by
    simpa only [g, LinearEquiv.apply_symm_apply] using hx
  have hzinv : e.equivFun (z⁻¹).coord ∈ denominatorGrid q := by
    simpa only [NilpotentLieBCHGroup.coord_inv, map_neg] using denominatorGrid_neg q hz
  have hconj := conjugation_preserves_inner_grid e hnil q l hq z⁻¹ g hzinv hg
  have hmem : z⁻¹ * g * z ∈ Γ := by
    apply (bchSubgroupCoordinates_repr e Γ _).mp
    apply hinner
    simpa only [inv_inv] using hconj
  change g ∈ Γ.map (MulAut.conj z).toMonoidHom
  refine Subgroup.mem_map.mpr ⟨z⁻¹ * g * z, hmem, ?_⟩
  change z * (z⁻¹ * g * z) * z⁻¹ = g
  group

theorem exists_uniform_conjugated_inner_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l q H : ℕ) (p : ℝ),
      0 < l → 0 < q → scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (l : ℝ) ≤ Real.exp p → (q : ℝ) ≤ Real.exp p →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ z : NilpotentLieBCHGroup L s hnil, e.equivFun z.coord ∈ denominatorGrid q →
          scaledIntegerGrid M ⊆ bchSubgroupCoordinates e (Γ.map (MulAut.conj z).toMonoidHom) := by
  obtain ⟨K, hK, hden⟩ := exists_conjugation_denominator_exp_bound s
  refine ⟨K + s + 5, by omega, ?_⟩
  intro ι L _ _ _ e hnil Γ l q H p hl hq hinner hp hd hH hc hlb hqb
  refine ⟨l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * q ^ s,
    Nat.mul_pos (Nat.mul_pos hl (polynomialFamilyDenominator_pos _)) (pow_pos hq _), ?_, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_ofNat] using
      conjugation_grid_allowance_le_exp K s l _ q hp hlb (hden e H p hp hd hH hc) hqb
  · intro z hz
    exact conjugated_subgroup_inner_grid e hnil Γ l q hq hinner z hz

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealifiedBCHFiniteAtlas
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
  (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)

noncomputable def quotientCoordinateChart (z : NilpotentLieBCHGroup L s hnil) :
    OpenPartialHomeomorph (ι → ℝ) (NilpotentLieBCHGroup L s hnil ⧸ Γ) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let f := fun v : ι → ℝ => (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ)
  let U := {v : ι → ℝ | ∀ i, |v i| < bchInjectivityRadius s (Fintype.card ι) H l}
  have hi : Set.InjOn f U := (quotient_coordinate_injOn e c hstructure hc Γ l hl hgrid z).mono
    (fun _ hx i => (hx i).le)
  have hf : Continuous f := QuotientGroup.continuous_mk.comp
    (continuous_const.mul (basisHomeomorph e).symm.continuous)
  have ho : IsOpenMap f := QuotientGroup.isOpenMap_coe.comp
    ((Homeomorph.mulLeft z).isOpenMap.comp (basisHomeomorph e).symm.isOpenMap)
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (continuous_apply i).abs continuous_const)
  exact OpenPartialHomeomorph.ofContinuousOpen (hi.toPartialEquiv f U) hf.continuousOn ho hU

theorem quotientCoordinateChart_target (z : NilpotentLieBCHGroup L s hnil) :
    (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z).target =
      (fun v : ι → ℝ => (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ)) ''
        {v : ι → ℝ | ∀ i, |v i| < bchInjectivityRadius s (Fintype.card ι) H l} := rfl

theorem quotientCoordinateChart_center_mem (z : NilpotentLieBCHGroup L s hnil) :
    (QuotientGroup.mk z : _ ⧸ Γ) ∈ (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z).target := by
  have hzero : (basisHomeomorph (hnil := hnil) e).symm 0 = 1 := by
    apply (basisHomeomorph e).injective
    simp only [Homeomorph.apply_symm_apply, basisHomeomorph_apply, coord_one, map_zero]
  rw [quotientCoordinateChart_target]
  refine ⟨0, ?_, ?_⟩
  · intro i
    simpa only [Pi.zero_apply, abs_zero] using bchInjectivityRadius_pos s (Fintype.card ι) H l
  · simp only [hzero, mul_one]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

namespace NilpotentLieBCHGroup

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set Manifold
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
  (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)

@[instance_reducible]
noncomputable def quotientChartedSpace : ChartedSpace (ι → ℝ) (NilpotentLieBCHGroup L s hnil ⧸ Γ) where
  atlas := Set.range (fun z => (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z).symm)
  chartAt := fun x => (quotientCoordinateChart e c hstructure hc Γ l hl hgrid x.out).symm
  mem_chart_source := fun x => by
    simpa only [OpenPartialHomeomorph.symm_source, QuotientGroup.out_eq'] using
      quotientCoordinateChart_center_mem e c hstructure hc Γ l hl hgrid x.out
  chart_mem_atlas := fun x => ⟨x.out, rfl⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set Manifold
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem shifted_center_power_bound (A B : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ((p + A) + B) ^ B ≤ (p + (A + B + 2 : ℕ)) ^ (A + B + 2) := by
  have hbase : (p + A) + B ≤ p + (A + B + 2 : ℕ) := by push_cast; linarith
  apply (pow_le_pow_left₀ (by positivity) hbase B).trans
  exact pow_le_pow_right₀
    (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) A, Nat.cast_nonneg (α := ℝ) B]) (by omega)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CurrentLayerBudget
namespace OAI

section

namespace Erdos3

def currentLayerConstructionBudget (p : ℝ) : ℝ := 2 * p + 2

def currentLayerRemovalBudget (p : ℝ) : ℝ :=
  2 * (p + 2) ^ 3 + (currentLayerConstructionBudget p + 2) ^ 36 +
    (currentLayerConstructionBudget p + 2) ^ 18 + currentLayerConstructionBudget p + 5 * p + 10

theorem currentLayerConstructionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ currentLayerConstructionBudget p := by unfold currentLayerConstructionBudget; positivity

theorem currentLayerRemovalBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ currentLayerRemovalBudget p := by
  unfold currentLayerRemovalBudget currentLayerConstructionBudget
  positivity

theorem le_currentLayerConstructionBudget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ currentLayerConstructionBudget p := by unfold currentLayerConstructionBudget; linarith

theorem current_layer_construction_budget_bounds {p M : ℝ} (hM : 0 ≤ M)
    (n j l : ℕ) (hn : (n : ℝ) ≤ p) (hj : 1 ≤ j) (hjp : (j : ℝ) ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hMp : M ≤ Real.exp p) :
    ((l * j : ℕ) : ℝ) ≤ Real.exp (currentLayerConstructionBudget p) ∧
      (n : ℝ) / j * M ≤ Real.exp (currentLayerConstructionBudget p) := by
  have hpE : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hexp : Real.exp (2 * p) ≤ Real.exp (currentLayerConstructionBudget p) := by
    apply Real.exp_le_exp.mpr
    unfold currentLayerConstructionBudget
    linarith
  constructor
  · rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hl (hjp.trans hpE) (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hexp
  · have hdiv : (n : ℝ) / j ≤ n := div_le_self (Nat.cast_nonneg _) hjR
    calc
      _ ≤ (n : ℝ) * M := mul_le_mul_of_nonneg_right hdiv hM
      _ ≤ Real.exp p * Real.exp p := mul_le_mul (hn.trans hpE) hMp hM (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hexp

theorem current_layer_coordinate_factor_bound {p : ℝ} (hp : 0 ≤ p)
    (n H : ℕ) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((n : ℝ) + 1) * (H + 1) ≤ Real.exp (2 * p + 1) := by
  have hplus : Real.exp p + 1 ≤ Real.exp (p + 1) := by
    calc
      _ ≤ Real.exp p * 2 := by linarith [Real.one_le_exp hp]
      _ ≤ Real.exp p * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hnplus : (n : ℝ) + 1 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hHplus : (H : ℝ) + 1 ≤ Real.exp (p + 1) := by linarith
  calc
    _ ≤ Real.exp p * Real.exp (p + 1) :=
      mul_le_mul hnplus hHplus (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem current_layer_removal_budget_bounds {p M : ℝ} (hp : 0 ≤ p)
    (a b j J Q l D E : ℕ) (ha : (a : ℝ) ≤ p) (hb : (b : ℝ) ≤ p) (hj : (j : ℝ) ≤ p)
    (hJ : (J : ℝ) ≤ Real.exp p) (hQ : (Q : ℝ) ≤ Real.exp p)
    (hl : (l : ℝ) ≤ Real.exp p) (hM : M ≤ Real.exp p)
    (hD : (D : ℝ) ≤ Real.exp ((p + 2) ^ 3))
    (hE : (E : ℝ) ≤ Real.exp ((p + 2) ^ 3)) :
    p ≤ currentLayerRemovalBudget p ∧
      ((l * D * E : ℕ) : ℝ) * Real.exp ((currentLayerConstructionBudget p + 2) ^ 36) ≤
        Real.exp (currentLayerRemovalBudget p) ∧
      M + j * ((((a : ℝ) + 1) * (Q + 1)) * (((b : ℝ) + 1) * (J + 1)) *
        Real.exp ((currentLayerConstructionBudget p + 2) ^ 18 + currentLayerConstructionBudget p)) ≤
        Real.exp (currentLayerRemovalBudget p) ∧
      Real.exp ((currentLayerConstructionBudget p + 2) ^ 36) ≤ Real.exp (currentLayerRemovalBudget p) ∧
      (((b : ℝ) + 1) * (J + 1)) *
        Real.exp ((currentLayerConstructionBudget p + 2) ^ 18 + currentLayerConstructionBudget p) ≤
        Real.exp (currentLayerRemovalBudget p) ∧
      (E : ℝ) * Real.exp ((currentLayerConstructionBudget p + 2) ^ 36) ≤
        Real.exp (currentLayerRemovalBudget p) := by
  let t := currentLayerConstructionBudget p
  let u := (p + 2) ^ 3
  let r := (t + 2) ^ 36
  let v := (t + 2) ^ 18 + t
  have ht : 0 ≤ t := currentLayerConstructionBudget_nonneg hp
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hq : currentLayerRemovalBudget p = 2 * u + r + v + 5 * p + 10 := by
    dsimp [currentLayerRemovalBudget, u, r, v, t]
    ring
  have hpq : p ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hdenExp : p + u + u + r ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hsizeExp : 5 * p + 2 + v + 1 ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hrq : r ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hcorrExp : 2 * p + 1 + v ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hgridExp : u + r ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hfQ := current_layer_coordinate_factor_bound hp a Q ha hQ
  have hfJ := current_layer_coordinate_factor_bound hp b J hb hJ
  have hpE : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hcorr : (((b : ℝ) + 1) * (J + 1)) * Real.exp v ≤ Real.exp (2 * p + 1 + v) := by
    calc
      _ ≤ Real.exp (2 * p + 1) * Real.exp v := mul_le_mul_of_nonneg_right hfJ (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  refine ⟨hpq, ?_, ?_, Real.exp_le_exp.mpr hrq,
    hcorr.trans (Real.exp_le_exp.mpr hcorrExp), ?_⟩
  · rw [Nat.cast_mul, Nat.cast_mul]
    calc
      _ ≤ (Real.exp p * Real.exp u * Real.exp u) * Real.exp r := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact mul_le_mul (mul_le_mul hl hD (Nat.cast_nonneg _) (Real.exp_nonneg _)) hE
          (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp (p + u + u + r) := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr hdenExp
  · have hproduct : j * ((((a : ℝ) + 1) * (Q + 1)) * (((b : ℝ) + 1) * (J + 1)) * Real.exp v) ≤
        Real.exp (5 * p + 2 + v) := by
      calc
        _ ≤ Real.exp p * ((Real.exp (2 * p + 1) * Real.exp (2 * p + 1)) * Real.exp v) := by
          apply mul_le_mul (hj.trans hpE) _ (by positivity) (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hfQ hfJ (by positivity) (Real.exp_nonneg _)) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hM' : M ≤ Real.exp (5 * p + 2 + v) := hM.trans (Real.exp_le_exp.mpr (by linarith))
    calc
      _ ≤ Real.exp (5 * p + 2 + v) * 2 := by linarith
      _ ≤ Real.exp (5 * p + 2 + v) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = Real.exp (5 * p + 2 + v + 1) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsizeExp
  · calc
      _ ≤ Real.exp u * Real.exp r := mul_le_mul_of_nonneg_right hE (Real.exp_nonneg _)
      _ = Real.exp (u + r) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hgridExp

theorem exists_current_layer_uniform_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      separationBudget (currentLayerConstructionBudget p) +
        separationBudget (currentLayerRemovalBudget p) + currentLayerRemovalBudget p ≤ (p + C) ^ C := by
  let T : Polynomial ℕ := 2 * Polynomial.X + 2
  let Q : Polynomial ℕ := 2 * (Polynomial.X + 2) ^ 3 + (T + 2) ^ 36 + (T + 2) ^ 18 + T + 5 * Polynomial.X + 10
  let B : Polynomial ℕ := ((T + 2) ^ 48 + (T + 2) ^ 24 + T + 1) +
    ((Q + 2) ^ 48 + (Q + 2) ^ 24 + Q + 1) + Q
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [B, Q, T, separationBudget, currentLayerConstructionBudget, currentLayerRemovalBudget,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeParameterCoverBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def externalNetMesh (L : ℝ≥0) (ε : ℝ) : ℝ := ε / (3 * (L + 1))

theorem externalNetMesh_pos (L : ℝ≥0) {ε : ℝ} (hε : 0 < ε) : 0 < externalNetMesh L ε := by
  unfold externalNetMesh
  positivity

theorem externalNetMesh_error (L M : ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε) :
    ε / 3 + M * externalNetMesh M ε + L * externalNetMesh L ε ≤ ε := by
  have hterm (K : ℝ≥0) : K * externalNetMesh K ε ≤ ε / 3 := by
    unfold externalNetMesh
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 3 * (K + 1))]
    nlinarith [K.coe_nonneg]
  linarith [hterm M, hterm L]

theorem externalNetMesh_inverse_bound (L : ℝ≥0) {ε p : ℝ}
    (hε : 0 < ε) (hp : 0 ≤ p) (hL : (L : ℝ) ≤ Real.exp p) (hinv : 1 / ε ≤ Real.exp p) :
    1 / externalNetMesh L ε ≤ Real.exp (2 * p + 7) := by
  have hone : 1 ≤ Real.exp p := Real.one_le_exp hp
  have hseven : (6 : ℝ) ≤ Real.exp 7 := by linarith [Real.add_one_le_exp (7 : ℝ)]
  calc
    1 / externalNetMesh L ε = 3 * (L + 1) * (1 / ε) := by unfold externalNetMesh; field_simp
    _ ≤ 3 * (Real.exp p + Real.exp p) * Real.exp p := by gcongr
    _ = 6 * Real.exp (2 * p) := by rw [two_mul, Real.exp_add]; ring
    _ ≤ Real.exp 7 * Real.exp (2 * p) := mul_le_mul_of_nonneg_right hseven (Real.exp_nonneg _)
    _ = Real.exp (2 * p + 7) := by rw [← Real.exp_add, add_comm]

theorem boxCoverCount_dimension_bound (d : ℕ) (K : ℝ≥0) {B ε p : ℝ}
    (hB0 : 0 ≤ B) (hε : 0 < ε) (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hB : B ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) (hinv : 1 / ε ≤ Real.exp p) :
    (((boxCoverMeshCount B K ε + 1) ^ d : ℕ) : ℝ) ≤ Real.exp (p * (3 * p + 4)) := by
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (3 * p + 4)) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (boxCoverMeshCount_add_one_le_exp K hB0 hε hp hB hK hinv) d
    _ = Real.exp ((d : ℝ) * (3 * p + 4)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd (by positivity))

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_bchBoxCover_count_budget (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d H : ℕ) (B : ℝ≥0) {p ε : ℝ},
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (B : ℝ) ≤ Real.exp ((p + 2) ^ r) → 0 < ε → 1 / ε ≤ Real.exp p →
      (((boxCoverMeshCount B (bchBoxMetricConstant s d H B) ε + 1) ^ d : ℕ) : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  obtain ⟨A, _, hmetric⟩ := exists_bchBoxMetricConstant_exp_bound s r
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 2) ^ r + (X + Polynomial.C A) ^ A
  let P := R * (3 * R + 4)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro d H B p ε hp hd hH hB hε hεinv
  let q := p + (p + 2) ^ r + (p + A) ^ A
  have hr : 0 ≤ (p + 2) ^ r := pow_nonneg (by linarith) _
  have hA : 0 ≤ (p + A) ^ A := pow_nonneg (add_nonneg hp (Nat.cast_nonneg A)) _
  have hpq : p ≤ q := (le_add_of_nonneg_right hr).trans (le_add_of_nonneg_right hA)
  have hrq : (p + 2) ^ r ≤ q := (le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right hA)
  have hAq : (p + A) ^ A ≤ q := le_add_of_nonneg_left (add_nonneg hp hr)
  have hsize := boxCoverCount_dimension_bound d (bchBoxMetricConstant s d H B) B.coe_nonneg hε
    (hp.trans hpq) (hd.trans hpq) (hB.trans (Real.exp_le_exp.mpr hrq))
    ((hmetric d H B p hp hd hH hB).trans (Real.exp_le_exp.mpr hAq))
    (hεinv.trans (Real.exp_le_exp.mpr hpq))
  have hfinal : q * (3 * q + 4) ≤ (p + C) ^ C := by
    simpa [P, R, X, q, Polynomial.eval₂_pow] using hbudget p hp
  exact hsize.trans (Real.exp_le_exp.mpr hfinal)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BlockQuotientRows
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_block_quotient_rows {ι δ : Type*} [Fintype ι]
    (c : ι → δ) (Q : Matrix ι ι ℚ) (hblock : ∀ i j, c i ≠ c j → Q i j = 0)
    {H : ℕ} (hH : 1 ≤ H) (hQ : ∀ i j, RationalHeightLE (Q i j) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ rows : Fin r → ι, Function.Injective rows ∧
      Function.Surjective (Q.submatrix rows id).mulVec ∧
      LinearMap.ker (Q.submatrix rows id).mulVecLin = LinearMap.ker Q.mulVecLin ∧
      ∃ S : Matrix ι (Fin r) ℚ, Q.submatrix rows id * S = 1 ∧
        (∀ i j, c i ≠ c (rows j) → S i j = 0) ∧
        ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight r H) := by
  classical
  obtain ⟨r, hr, rows, hinj, hsurj, hker⟩ := exists_independent_defining_rows Q
  let D := Q.submatrix rows id
  have hD : ∀ i j, c (rows i) ≠ c j → D i j = 0 := fun i j h => hblock (rows i) j h
  obtain ⟨S, hS, hSb, hSH⟩ := exists_bounded_block_image_section (fun i => c (rows i)) c D hD hH
    (fun i j => hQ (rows i) j)
  have hDS : D * S = 1 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    change (D * S) *ᵥ (D *ᵥ x) = 1 *ᵥ (D *ᵥ x)
    rw [Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]
  exact ⟨r, hr, rows, hinj, hsurj, hker, S, hDS, hSb, by simpa only [Fintype.card_fin] using hSH⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledSumCoordinates
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem real_column_span_fromCols {ι κ ν : Type*}
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ) :
    Submodule.span ℝ (Set.range ((Matrix.fromCols A B).map (Rat.castHom ℝ)).col) =
      Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) ⊔
        Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) := by
  rw [Matrix.fromCols_map]
  have hr : Set.range (Matrix.fromCols (A.map (Rat.castHom ℝ)) (B.map (Rat.castHom ℝ))).col =
      Set.range (A.map (Rat.castHom ℝ)).col ∪ Set.range (B.map (Rat.castHom ℝ)).col := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      cases j with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr j => exact Or.inr ⟨j, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr j, rfl⟩
  rw [hr, Submodule.span_union]

theorem exists_rational_sum_coordinates {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hB : ∀ i j, RationalHeightLE (B i j) H) :
    ∃ S : Matrix (κ ⊕ ν) ι ℚ,
      (∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H)) ∧
      ∀ x, x ∈ Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) ⊔
        Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) →
        A.map (Rat.castHom ℝ) *ᵥ ((S.map (Rat.castHom ℝ) *ᵥ x) ∘ Sum.inl) +
          B.map (Rat.castHom ℝ) *ᵥ ((S.map (Rat.castHom ℝ) *ᵥ x) ∘ Sum.inr) = x := by
  let C := Matrix.fromCols A B
  have hC : ∀ i j, RationalHeightLE (C i j) H := by
    intro i j
    cases j with
    | inl j => exact hA i j
    | inr j => exact hB i j
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section C hH hC
  refine ⟨S, hSH, fun x hx => ?_⟩
  have hx' : x ∈ LinearMap.range (C.map (Rat.castHom ℝ)).mulVecLin := by
    apply (real_column_span_mem_iff C x).mp
    change x ∈ Submodule.span ℝ (Set.range ((Matrix.fromCols A B).map (Rat.castHom ℝ)).col)
    rw [real_column_span_fromCols]
    exact hx
  have he := real_matrix_image_section_apply C S hS x hx'
  change C.map (Rat.castHom ℝ) *ᵥ (S.map (Rat.castHom ℝ) *ᵥ x) = x at he
  dsimp only [C] at he
  rw [Matrix.fromCols_map, Matrix.fromCols_mulVec] at he
  exact he

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem pi_norm_restriction_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (f : κ → ι) : ‖x ∘ f‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  exact norm_le_pi_norm x (f i)

theorem exists_controlled_sum_coordinates {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ u : (ι → ℝ) →ₗ[ℝ] (κ → ℝ), ∃ v : (ι → ℝ) →ₗ[ℝ] (ν → ℝ),
        (∀ x, x ∈ Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) ⊔
          Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) →
          A.map (Rat.castHom ℝ) *ᵥ u x + B.map (Rat.castHom ℝ) *ᵥ v x = x) ∧
        (∀ x, ‖u x‖ ≤ Real.exp ((p + 2) ^ 18) * ‖x‖ ∧
          ‖v x‖ ≤ Real.exp ((p + 2) ^ 18) * ‖x‖) ∧
        ∀ x, x ∈ realDenominatorGrid l →
          u x ∈ realDenominatorGrid m ∧ v x ∈ realDenominatorGrid m := by
  classical
  obtain ⟨S, hS, hdecomp⟩ := exists_rational_sum_coordinates A B hH hA hB
  let m := matrixDenominator S * l
  let u : (ι → ℝ) →ₗ[ℝ] (κ → ℝ) :=
    (LinearMap.funLeft ℝ ℝ Sum.inl).comp (S.map (Rat.castHom ℝ)).mulVecLin
  let v : (ι → ℝ) →ₗ[ℝ] (ν → ℝ) :=
    (LinearMap.funLeft ℝ ℝ Sum.inr).comp (S.map (Rat.castHom ℝ)).mulVecLin
  have hnorm (x : ι → ℝ) := real_image_section_norm_bound S H hS hp hι hcols hHp x
  have hgrid (x : ι → ℝ) (hx : x ∈ realDenominatorGrid l) := real_matrix_denominator_grid S l x hx
  refine ⟨m, Nat.mul_pos (matrixDenominator_pos S) hl,
    real_image_section_denominator_bound S H l hS hp hι hcols hHp hlp, u, v, hdecomp, ?_, ?_⟩
  · intro x
    exact ⟨(pi_norm_restriction_le (S.map (Rat.castHom ℝ) *ᵥ x) Sum.inl).trans (hnorm x),
      (pi_norm_restriction_le (S.map (Rat.castHom ℝ) *ᵥ x) Sum.inr).trans (hnorm x)⟩
  · intro x hx
    exact ⟨realDenominatorGrid_comp m _ (hgrid x hx) Sum.inl,
      realDenominatorGrid_comp m _ (hgrid x hx) Sum.inr⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LogCharacterBudget
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open CircleFourier

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def logCharacter (η : L →ₗ[ℝ] ℝ) (g : NilpotentLieBCHGroup L s hnil) : ℂ :=
  character (η g.coord : CircleFourier.Circle)

theorem logCharacter_norm (η : L →ₗ[ℝ] ℝ) (g : NilpotentLieBCHGroup L s hnil) :
    ‖logCharacter η g‖ = 1 := norm_character _

theorem logCharacter_mul (η : L →ₗ[ℝ] ℝ) (g h : NilpotentLieBCHGroup L s hnil)
    (hgh : ⁅g.coord, h.coord⁆ = 0) :
    logCharacter η (g * h) = logCharacter η g * logCharacter η h := by
  simp only [logCharacter, coord_mul, lieBCH_eq_add_of_lie_eq_zero hnil hgh,
    map_add, AddCircle.coe_add, character_add]

theorem logCharacter_inv_mul (η : L →ₗ[ℝ] ℝ) (g : NilpotentLieBCHGroup L s hnil) :
    logCharacter η g⁻¹ * logCharacter η g = 1 := by
  simp only [logCharacter, coord_inv, map_neg, AddCircle.coe_neg, ← character_add,
    neg_add_cancel, character_zero]

theorem logCharacter_of_integral (η : L →ₗ[ℝ] ℝ) (g : NilpotentLieBCHGroup L s hnil)
    (hg : ∃ n : ℤ, η g.coord = n) : logCharacter η g = 1 := by
  obtain ⟨n, hn⟩ := hg
  apply (character_eq_one_iff _).mpr
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn.symm⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem logCharacter_norm_sub_eq_relative (η : L →ₗ[ℝ] ℝ)
    (x y γ : NilpotentLieBCHGroup L s hnil)
    (hx : ∀ v : L, ⁅x.coord, v⁆ = 0) (hy : ∀ v : L, ⁅y.coord, v⁆ = 0)
    (hγ : logCharacter η γ = 1) :
    ‖logCharacter η x - logCharacter η y‖ =
      ‖logCharacter η (y * γ * x⁻¹) - 1‖ := by
  have hzero : ⁅(y * γ).coord, x.coord⁆ = 0 := by rw [← lie_skew, hx, neg_zero]
  have hright : ⁅(y * γ).coord, x⁻¹.coord⁆ = 0 := by
    simp only [coord_inv, lie_neg, hzero, neg_zero]
  have hprod : logCharacter η (y * γ * x⁻¹) * logCharacter η x = logCharacter η y := by
    rw [logCharacter_mul η (y * γ) x⁻¹ hright,
      logCharacter_mul η y γ (hy γ.coord), hγ, mul_one, mul_assoc, logCharacter_inv_mul, mul_one]
  calc
    _ = ‖logCharacter η y - logCharacter η x‖ := norm_sub_rev _ _
    _ = ‖(logCharacter η (y * γ * x⁻¹) - 1) * logCharacter η x‖ := by
      rw [sub_mul, one_mul, hprod]
    _ = _ := by rw [norm_mul, logCharacter_norm, mul_one]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped NNReal

noncomputable def logCharacterMetricConstant (s d H : ℕ) (A : ℝ≥0) : ℝ≥0 :=
  (2 + CircleFourier.characterLipConstant * A) * bchLogMetricConstant s d H 1

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem logCharacter_dist_one_le (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (η : L →ₗ[ℝ] ℝ) (A : ℝ≥0) (hη : ∀ x, |η x| ≤ A * ‖e.equivFun x‖)
    (g : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    ‖logCharacter η g - 1‖ ≤ logCharacterMetricConstant s (Fintype.card ι) H A * dist 1 g := by
  let := rightMetricSpace (hnil := hnil) e
  let C := bchLogMetricConstant s (Fintype.card ι) H 1
  change ‖logCharacter η g - 1‖ ≤
    (2 + (CircleFourier.characterLipConstant : ℝ) * A) * C * dist 1 g
  by_cases hnear : (C : ℝ) * dist 1 g < 1
  · have hcoord := norm_coordinates_le_of_near_one e c hstructure hc 1 le_rfl g hnear
    have hchar := norm_character_real_sub_one_le (η g.coord)
    have hlinear := hη g.coord
    have hscale := mul_le_mul_of_nonneg_left hcoord A.coe_nonneg
    change ‖e.equivFun g.coord‖ ≤ (C : ℝ) * dist 1 g at hcoord
    have hbound : |η g.coord| ≤ A * ((C : ℝ) * dist 1 g) := hlinear.trans hscale
    apply hchar.trans
    have h := mul_le_mul_of_nonneg_left hbound CircleFourier.characterLipConstant.coe_nonneg
    nlinarith [C.coe_nonneg, dist_nonneg (x := (1 : NilpotentLieBCHGroup L s hnil)) (y := g)]
  · have hfar : 1 ≤ (C : ℝ) * dist 1 g := le_of_not_gt hnear
    apply (CircleFourier.norm_character_sub_one_le_two _).trans
    nlinarith [CircleFourier.characterLipConstant.coe_nonneg, A.coe_nonneg,
      C.coe_nonneg, dist_nonneg (x := (1 : NilpotentLieBCHGroup L s hnil)) (y := g),
      mul_nonneg CircleFourier.characterLipConstant.coe_nonneg A.coe_nonneg]

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem bchLogMetricConstant_le_inverse (s d H : ℕ) :
    bchLogMetricConstant s d H 1 ≤ bchInverseBoxConstant s d H 1 := by
  change bchBoxCoordinateBound s d H 1 + 1 ≤
    (bchBoxCoordinateBound s d H 1 + 2 * 1) * (bchBoxCoordinateBound s d H 1 + 1)
  have h := bchBoxCoordinateBound_nonneg s d H (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith

theorem exists_logCharacterMetricConstant_exp_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d H : ℕ) (A : ℝ≥0) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (A : ℝ) ≤ Real.exp p →
      ((2 * logCharacterMetricConstant s d H A : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨a, _, hbound⟩ := exists_bchInverseBoxConstant_exp_bound s 0
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget (X + 11 + (X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro d H A p hp hd hH hA
  have hlog : (bchLogMetricConstant s d H 1 : ℝ) ≤ Real.exp ((p + a) ^ a) :=
    (show (bchLogMetricConstant s d H 1 : ℝ) ≤ bchInverseBoxConstant s d H 1 from
      bchLogMetricConstant_le_inverse s d H).trans
      (hbound d H 1 p hp hd hH (by simp only [NNReal.coe_one, pow_zero]; exact Real.one_le_exp zero_le_one))
  have hfront : 2 + (CircleFourier.characterLipConstant : ℝ) * A ≤ Real.exp (p + 10) := by
    have hpi : (CircleFourier.characterLipConstant : ℝ) ≤ 8 := by
      rw [CircleFourier.coe_characterLipConstant]
      linarith [Real.pi_lt_four]
    have hten : (10 : ℝ) ≤ Real.exp 10 := by linarith [Real.add_one_le_exp (10 : ℝ)]
    have hone := Real.one_le_exp hp
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_right hpi A.coe_nonneg]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsmall : ((2 * logCharacterMetricConstant s d H A : ℝ≥0) : ℝ) ≤
      Real.exp (p + 11 + (p + a) ^ a) := by
    change 2 * ((2 + (CircleFourier.characterLipConstant : ℝ) * A) *
      (bchLogMetricConstant s d H 1 : ℝ)) ≤ _
    calc
      _ ≤ Real.exp 1 * (Real.exp (p + 10) * Real.exp ((p + a) ^ a)) :=
        mul_le_mul htwo (mul_le_mul hfront hlog (by positivity) (Real.exp_pos _).le)
          (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  apply hsmall.trans (Real.exp_le_exp.mpr ?_)
  simpa [X, Polynomial.eval₂_pow] using hpoly p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CentralOrbitMetric
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem central_logCharacter_coset_dist_le (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ T : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (hT : ∀ z ∈ T, ∀ v : L, ⁅z.coord, v⁆ = 0)
    (η : L →ₗ[ℝ] ℝ) (A : ℝ≥0) (hη : ∀ x, |η x| ≤ A * ‖e.equivFun x‖)
    (hint : ∀ γ ∈ Γ, ∃ n : ℤ, η γ.coord = n) (x y : T) :
    letI := quotientMetricSpace e Γ hΓ
    dist (logCharacter η x.val) (logCharacter η y.val) ≤
      logCharacterMetricConstant s (Fintype.card ι) H A *
        dist (QuotientGroup.mk x.val : _ ⧸ Γ) (QuotientGroup.mk y.val) := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  let := quotientMetricSpace e Γ hΓ
  let K := logCharacterMetricConstant s (Fintype.card ι) H A
  have hdist (γ : Γ) : dist (logCharacter η x.val) (logCharacter η y.val) ≤
      K * dist x.val (y.val * γ.val) := by
    rw [dist_eq_norm, logCharacter_norm_sub_eq_relative η x.val y.val γ.val
      (hT x.val x.property) (hT y.val y.property) (logCharacter_of_integral η γ.val (hint γ.val γ.property))]
    have h := logCharacter_dist_one_le e c hstructure hc η A hη (y.val * γ.val * x.val⁻¹)
    have heq : dist (1 : NilpotentLieBCHGroup L s hnil) (y.val * γ.val * x.val⁻¹) =
        dist x.val (y.val * γ.val) := by
      simpa only [mul_inv_cancel] using dist_mul_right x.val (y.val * γ.val) x.val⁻¹
    exact h.trans_eq (congrArg (fun r : ℝ => (K : ℝ) * r) heq)
  have he : edist (logCharacter η x.val) (logCharacter η y.val) ≤
      (K : ℝ≥0∞) * edist (QuotientGroup.mk x.val : _ ⧸ Γ) (QuotientGroup.mk y.val) := by
    rw [quotientMetricSpace_edist_mk, ENNReal.mul_iInf (by simp)]
    apply le_iInf
    intro γ
    simpa only [edist_dist, ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_le_ofReal (hdist γ)
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) he
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg] using h

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeLayerBases
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module
open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*} [∀ a, Fintype (κ a)]
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))

noncomputable def squarefreeSupportedFinBasis (P : SquarefreeIndex ι → Prop) :
    Basis (Fin (finrank ℚ
      ((squarefreeSupportModule P).comap (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap))) ℚ
      ((squarefreeSupportModule P).comap (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap) := by
  classical
  exact (F.squarefreeSupportedBasis π b P).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis (F.squarefreeSupportedBasis π b P)).symm)

theorem squarefreeSupportedFinBasis_height (P : SquarefreeIndex ι → Prop) (j k) :
    RationalHeightLE ((F.squarefreeBasis π b).repr (F.squarefreeSupportedFinBasis π b P j).val k) 1 := by
  classical
  unfold squarefreeSupportedFinBasis
  rw [Basis.reindex_apply, F.squarefreeSupportedBasis_coe]
  exact basis_repr_height_one _ _ _

noncomputable def squarefreeMultidegreeBasis (c : ι → ℕ) :
    Basis (Fin (finrank ℚ (F.squarefreeMultidegreeLayer π c))) ℚ (F.squarefreeMultidegreeLayer π c) :=
  F.squarefreeSupportedFinBasis π b (fun a => c ≤ fun i => a.val i)

theorem squarefreeMultidegreeBasis_height (c : ι → ℕ) (j k) :
    RationalHeightLE ((F.squarefreeBasis π b).repr (F.squarefreeMultidegreeBasis π b c j).val k) 1 :=
  F.squarefreeSupportedFinBasis_height π b _ j k

noncomputable def squarefreeDegreeBasis (n : ℕ) :
    Basis (Fin (finrank ℚ (F.squarefreeDegreeLayer π n))) ℚ (F.squarefreeDegreeLayer π n) :=
  F.squarefreeSupportedFinBasis π b (fun a => n ≤ ∑ i, a.val i)

theorem squarefreeDegreeBasis_height (n : ℕ) (j k) :
    RationalHeightLE ((F.squarefreeBasis π b).repr (F.squarefreeDegreeBasis π b n j).val k) 1 :=
  F.squarefreeSupportedFinBasis_height π b _ j k

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeStructureHeight
namespace OAI

section

namespace Erdos3

open Module

def squarefreeStructureHeight (n H : ℕ) : ℕ :=
  (n + 1) * (rationalSolveHeight n H * squarefreeBracketHeight n H) ^ n

namespace MultidegreeLieFiltration

variable {ι σ ν L : Type*} [Fintype ι] [Fintype σ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*} [∀ a, Fintype (κ a)]
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))
  (e : Basis ν ℚ L) {H : ℕ} (hH : 1 ≤ H)
  (hb : ∀ a j k, RationalHeightLE (e.repr (b a j).val k) H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)

include hH hb hc

theorem squarefreeBasis_structure_height
    (hκ : ∀ a, Fintype.card (κ a) ≤ Fintype.card ν) (x y z : Σ a, κ a) :
    RationalHeightLE (lieStructureConstants (F.squarefreeBasis π b) x y z)
      (squarefreeStructureHeight (Fintype.card ν) H) := by
  change RationalHeightLE ((F.squarefreeBasis π b).repr
    ⁅F.squarefreeBasis π b x, F.squarefreeBasis π b y⁆ z) _
  rw [F.squarefreeBasis_repr]
  have h := submodule_basis_coordinate_height (F.squarefreeCoefficientLayer π z.1) (b z.1) e hH
    (fun i j => hb z.1 j i)
    (F.squarefreeAlgebraEquiv π ⁅F.squarefreeBasis π b x, F.squarefreeBasis π b y⁆ z.1)
    (fun k => F.squarefreeBasis_bracket_coefficient_height π b e hH hb hc x y z.1 k) z.2
  apply h.mono
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.mul_le_mul_right _ (rationalSolveHeight_mono hH (hκ z.1))) _)

end MultidegreeLieFiltration

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealChartReindexCoefficients
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem coefficients_substitute_reindex (e : τ ≃ σ)
    (P : VectorPolynomial σ R V) (α : τ →₀ ℕ) :
    coefficients (substitute (fun i => MvPolynomial.X (e.symm i)) P) α =
      coefficients P (α.mapDomain e) := by
  have hα : (α.mapDomain e).mapDomain e.symm = α := by
    ext i
    simp only [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  induction P using TensorProduct.induction_on with
  | zero => simp
  | tmul p v =>
    simp only [substitute_tmul, coefficients_tmul]
    change (MvPolynomial.aeval (MvPolynomial.X ∘ e.symm) p).coeff α • v = _
    rw [← MvPolynomial.rename_eq_aeval]
    exact congrArg (fun c : R => c • v)
      (by simpa only [hα] using
        MvPolynomial.coeff_rename_mapDomain e.symm e.symm.injective p (α.mapDomain e))
  | add p q hp hq => simp only [map_add, Finsupp.add_apply, hp, hq]

variable [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]

theorem coefficients_realChartSubstitute_reindex (e : τ ≃ σ)
    (P : VectorPolynomial σ ℚ V) (α : τ →₀ ℕ) :
    coefficients (realChartSubstitute (fun i => MvPolynomial.X (e.symm i)) P) α =
      coefficients P (α.mapDomain e) := by
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, coefficients_realCoefficientEquiv_symm,
    coefficients_substitute_reindex, coefficients_realCoefficientEquiv]

@[simp] theorem coefficients_zero_realChartSubstitute_reindex (e : τ ≃ σ)
    (P : VectorPolynomial σ ℚ V) :
    coefficients (realChartSubstitute (fun i => MvPolynomial.X (e.symm i)) P) 0 =
      coefficients P 0 := by
  simp only [coefficients_realChartSubstitute_reindex, Finsupp.mapDomain_zero]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RealSpanIntegerDefiningRows
namespace OAI

section

namespace Erdos3

open scoped Matrix

def realSpanIntegerRowBound (n m H : ℕ) : ℕ :=
  imageDefiningHeight n m H ^ (m * m) * imageDefiningHeight n m H

theorem exists_real_span_integer_defining_matrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ C : Matrix ι ι ℤ,
      (∀ i j, |(C i j : ℝ)| ≤
        (realSpanIntegerRowBound (Fintype.card κ) (Fintype.card ι) H : ℝ)) ∧
      LinearMap.ker (Matrix.mulVecLin (fun i j => (C i j : ℝ))) =
        LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
  classical
  obtain ⟨Q, hQ, hker⟩ := exists_real_span_defining_matrix A hH hA
  have hcast (i j : ι) :
      (clearedMatrix Q i j : ℝ) = (matrixDenominator Q : ℝ) * (Q i j : ℝ) := by
    have h := congrFun (congrFun (clearedMatrix_cast Q) i) j
    change (clearedMatrix Q i j : ℚ) = (matrixDenominator Q : ℚ) * Q i j at h
    exact_mod_cast h
  refine ⟨clearedMatrix Q, ?_, ?_⟩
  · intro i j
    rw [hcast, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have hd := Nat.cast_le (α := ℝ).mpr (matrixDenominator_le Q hQ)
    have hentry := (hQ i j).abs_real_le
    exact (mul_le_mul hd hentry (abs_nonneg _) (Nat.cast_nonneg _)).trans_eq
      (by simp only [realSpanIntegerRowBound, Nat.cast_mul])
  · have hden : (matrixDenominator Q : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (matrixDenominator_pos Q)).ne'
    have hmatrix : Matrix.of (fun i j => (clearedMatrix Q i j : ℝ)) =
        (matrixDenominator Q : ℝ) • Matrix.of (fun i j => (Q i j : ℝ)) := by
      ext i j
      exact hcast i j
    calc
      LinearMap.ker (Matrix.mulVecLin (fun i j => (clearedMatrix Q i j : ℝ))) =
          LinearMap.ker (Matrix.mulVecLin (fun i j => (Q i j : ℝ))) := by
        ext x
        change (Matrix.of (fun i j => (clearedMatrix Q i j : ℝ)) *ᵥ x = 0) ↔
          (Matrix.of (fun i j => (Q i j : ℝ)) *ᵥ x = 0)
        rw [hmatrix, Matrix.smul_mulVec]
        simp [hden]
      _ = _ := hker

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BracketStepBudget
namespace OAI

section

namespace Erdos3

def bracketConstructionBudget (p : ℝ) : ℝ := (p + 2) ^ 3 + 3 * p + 2

def bracketCorrectionBudget (p : ℝ) : ℝ :=
  (bracketConstructionBudget p + 2) ^ 36 + (bracketConstructionBudget p + 2) ^ 18 +
    bracketConstructionBudget p + (p + 2) ^ 3 + 2 * p + 1

theorem bracketConstructionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ bracketConstructionBudget p := by unfold bracketConstructionBudget; positivity

theorem bracketCorrectionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ bracketCorrectionBudget p := by
  have hq := bracketConstructionBudget_nonneg hp
  unfold bracketCorrectionBudget
  positivity

theorem bracket_construction_budget_bounds {p : ℝ} (hp : 0 ≤ p) :
    p ≤ bracketConstructionBudget p ∧ (p + 2) ^ 2 ≤ bracketConstructionBudget p ∧
      (p + 2) ^ 3 + p ≤ bracketConstructionBudget p ∧
      3 * p + 1 ≤ bracketConstructionBudget p := by
  have hc : 0 ≤ (p + 2) ^ 3 := by positivity
  have hpow : (p + 2) ^ 2 ≤ (p + 2) ^ 3 :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 2) (by decide : 2 ≤ 3)
  unfold bracketConstructionBudget
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem bracket_correction_budget_bounds {p : ℝ} (hp : 0 ≤ p)
    (n J D : ℕ) (hn : (n : ℝ) ≤ p) (hJ : (J : ℝ) ≤ Real.exp p)
    (hD : (D : ℝ) ≤ Real.exp ((p + 2) ^ 3)) :
    (((n : ℝ) + 1) * (J + 1)) *
        Real.exp ((bracketConstructionBudget p + 2) ^ 18 + bracketConstructionBudget p) ≤
        Real.exp (bracketCorrectionBudget p) ∧
      (D : ℝ) * Real.exp ((bracketConstructionBudget p + 2) ^ 36) ≤
        Real.exp (bracketCorrectionBudget p) := by
  have hq := bracketConstructionBudget_nonneg hp
  have h36 : 0 ≤ (bracketConstructionBudget p + 2) ^ 36 := by positivity
  have h18 : 0 ≤ (bracketConstructionBudget p + 2) ^ 18 := by positivity
  have h3 : 0 ≤ (p + 2) ^ 3 := by positivity
  constructor
  · calc
      _ ≤ Real.exp (2 * p + 1) *
          Real.exp ((bracketConstructionBudget p + 2) ^ 18 + bracketConstructionBudget p) :=
        mul_le_mul_of_nonneg_right (current_layer_coordinate_factor_bound hp n J hn hJ)
          (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 1 +
          ((bracketConstructionBudget p + 2) ^ 18 + bracketConstructionBudget p)) :=
        (Real.exp_add _ _).symm
      _ ≤ _ := by apply Real.exp_le_exp.mpr; unfold bracketCorrectionBudget; linarith
  · calc
      _ ≤ Real.exp ((p + 2) ^ 3) * Real.exp ((bracketConstructionBudget p + 2) ^ 36) :=
        mul_le_mul_of_nonneg_right hD (Real.exp_nonneg _)
      _ = Real.exp ((p + 2) ^ 3 + (bracketConstructionBudget p + 2) ^ 36) :=
        (Real.exp_add _ _).symm
      _ ≤ _ := by apply Real.exp_le_exp.mpr; unfold bracketCorrectionBudget; linarith

theorem exists_bracket_uniform_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      separationBudget (bracketConstructionBudget p) + bracketCorrectionBudget p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ 3 + 3 * Polynomial.X + 2
  let B : Polynomial ℕ := (Q + 2) ^ 48 + (Q + 2) ^ 24 + Q + 1 +
    ((Q + 2) ^ 36 + (Q + 2) ^ 18 + Q + (Polynomial.X + 2) ^ 3 + 2 * Polynomial.X + 1)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [B, Q, separationBudget, bracketCorrectionBudget, bracketConstructionBudget,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealifiedBCHProductEquiv
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}

theorem realification_piRight_apply (x : ℝ ⊗[ℚ] (∀ i, L i)) (i : ι) :
    TensorProduct.piRight ℚ ℝ ℝ L x i = realificationLieHom (liePiEval i) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

noncomputable def realBCHPiEquiv (F : ∀ i, NilpotentLieFiltration (L i) s) :
    (NilpotentLieFiltration.pi F).realification.Group ≃* (∀ i, (F i).realification.Group) where
  toFun g i := realificationMap (hnil := (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot)
    (hM := (F i).lowerCentralSeries_eq_bot) (liePiEval i) g
  invFun g := ⟨(TensorProduct.piRight ℚ ℝ ℝ L).symm (fun i => (g i).coord)⟩
  left_inv g := by
    apply NilpotentLieBCHGroup.ext
    change (TensorProduct.piRight ℚ ℝ ℝ L).symm
      (fun i => realificationLieHom (liePiEval i) g.coord) = g.coord
    have h : (fun i => realificationLieHom (liePiEval i) g.coord) =
        TensorProduct.piRight ℚ ℝ ℝ L g.coord := funext (fun i => (realification_piRight_apply g.coord i).symm)
    rw [h, LinearEquiv.symm_apply_apply]
  right_inv g := by
    funext i
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom (liePiEval i)
      ((TensorProduct.piRight ℚ ℝ ℝ L).symm (fun i => (g i).coord)) = (g i).coord
    rw [← realification_piRight_apply, LinearEquiv.apply_symm_apply]
  map_mul' g h := by
    funext i
    exact (realificationMap (hnil := (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot)
      (hM := (F i).lowerCentralSeries_eq_bot) (liePiEval i)).map_mul g h

theorem realBCHPiEquiv_mem_lattice (F : ∀ i, NilpotentLieFiltration (L i) s)
    (Γ : ∀ i, Subgroup (F i).Group) (g : (NilpotentLieFiltration.pi F).realification.Group) :
    g ∈ (piBCHSubgroup F Γ).map realificationHom ↔
      ∀ i, realBCHPiEquiv F g i ∈ (Γ i).map realificationHom := by
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    exact ⟨⟨x.coord i⟩, (mem_piBCHSubgroup F Γ x).mp hx i, rfl⟩
  · intro h
    choose x hx heq using h
    let y : (NilpotentLieFiltration.pi F).Group := ⟨fun i => (x i).coord⟩
    refine Subgroup.mem_map.mpr ⟨y, (mem_piBCHSubgroup F Γ y).mpr hx, ?_⟩
    apply (realBCHPiEquiv F).injective
    funext i
    exact heq i

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialSubspaceSeparation
namespace OAI

section

namespace Erdos3

theorem exists_polynomial_subspace_separation (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {ι κ σ : Type*} [Fintype ι] [Fintype κ]
      (A : Matrix ι κ ℚ) (H l : ℕ), 1 ≤ H → 0 < l →
      (∀ i j, RationalHeightLE (A i j) H) →
      ∀ p : ℝ, 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      (Fintype.card κ : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      (H : ℝ) ≤ Real.exp (P.eval₂ (Nat.castRingHom ℝ) p) →
      (l : ℝ) ≤ Real.exp (P.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∀ α : σ →₀ ℕ, α ≠ 0 → ∀ a b : ι → ℝ,
      ‖a‖ ≤ Real.exp (P.eval₂ (Nat.castRingHom ℝ) p) / monomialScale T α →
      b ∈ realDenominatorGrid l →
      a + b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) →
      a ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) ∧
        b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) := by
  let R := (P + 2) ^ 48 + (P + 2) ^ 24 + P + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro ι κ σ _ _ A H l hH hl hA p hp hι hκ hHp hlp T hT α hα a b ha hb hsum
  have hbudget : separationBudget (P.eval₂ (Nat.castRingHom ℝ) p) ≤ (p + C) ^ C := by
    simpa [R, separationBudget, Polynomial.eval₂_pow] using hbound p hp
  exact controlled_real_column_span_separation A hH hl hA (natPolynomial_eval_nonneg P hp)
    hι hκ hHp hlp T (fun i => (Real.exp_le_exp.mpr hbudget).trans (hT i)) hα a b ha hb hsum

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

theorem exists_vectorPolynomial_subspace_separation (budget : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {J I σ : Type*} [Fintype J] [Fintype I]
      (B : Matrix J I ℚ) (H q : ℕ), 1 ≤ H → 0 < q →
      (∀ j i, RationalHeightLE (B j i) H) →
      ∀ p : ℝ, 0 ≤ p →
      (Fintype.card J : ℝ) ≤ budget.eval₂ (Nat.castRingHom ℝ) p →
      (Fintype.card I : ℝ) ≤ budget.eval₂ (Nat.castRingHom ℝ) p →
      (H : ℝ) ≤ Real.exp (budget.eval₂ (Nat.castRingHom ℝ) p) →
      (q : ℝ) ≤ Real.exp (budget.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∀ A E P Q : VectorPolynomial σ ℝ (J → ℝ),
      A = E + P + Q →
      (∀ α, coefficients A α ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) →
      (∀ α, coefficients P α ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) →
      coefficients E 0 = 0 → coefficients Q 0 = 0 →
      (∀ α j, |coefficients E α j| ≤
        Real.exp (budget.eval₂ (Nat.castRingHom ℝ) p) / monomialScale T α) →
      (∀ α, coefficients Q α ∈ realDenominatorGrid q) →
      (∀ α, coefficients E α ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) ∧
      (∀ α, coefficients Q α ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) ∧
      (∀ x, eval x E ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) ∧
      (∀ x, eval x Q ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) := by
  obtain ⟨C, hC, hsep⟩ := exists_polynomial_subspace_separation budget
  refine ⟨C, hC, ?_⟩
  intro J I σ _ _ B H q hH hq hB p hp hJ hI hHp hqp T hT A E P Q
    hdecomp hA hP hE0 hQ0 hE hQ
  let K := Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hcoeff (α : σ →₀ ℕ) : coefficients E α ∈ K ∧ coefficients Q α ∈ K := by
    by_cases hα : α = 0
    · subst α
      rw [hE0, hQ0]
      exact ⟨K.zero_mem, K.zero_mem⟩
    · have hsum : coefficients E α + coefficients Q α ∈ K := by
        have hm := K.sub_mem (hA α) (hP α)
        have heq : coefficients A α - coefficients P α =
            coefficients E α + coefficients Q α := by
          rw [hdecomp]
          simp only [map_add, Finsupp.add_apply]
          abel
        rwa [heq] at hm
      have hnorm : ‖coefficients E α‖ ≤
          Real.exp (budget.eval₂ (Nat.castRingHom ℝ) p) / monomialScale T α := by
        apply (pi_norm_le_iff_of_nonneg (div_nonneg (Real.exp_nonneg _)
          (monomialScale_pos T hTpos α).le)).mpr
        intro j
        simpa only [Real.norm_eq_abs] using hE α j
      exact hsep B H q hH hq hB p hp hJ hI hHp hqp T hT α hα
        (coefficients E α) (coefficients Q α) hnorm (hQ α) hsum
  have hEK : ∀ α, coefficients E α ∈ K := fun α => (hcoeff α).1
  have hQK : ∀ α, coefficients Q α ∈ K := fun α => (hcoeff α).2
  refine ⟨hEK, hQK, ?_, ?_⟩
  · intro x
    rw [← eval_restrictCoefficients K E hEK x]
    exact (eval (V := K) x (restrictCoefficients K E hEK)).property
  · intro x
    rw [← eval_restrictCoefficients K Q hQK x]
    exact (eval (V := K) x (restrictCoefficients K Q hQK)).property

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def HasLayerSamplingRank {I J : Type*} [Fintype J]
    (h : ℕ) (T : I → ℝ) (R : ℝ) (W : Submodule ℝ (J → ℝ))
    (p : VectorPolynomial I ℝ (J → ℝ)) : Prop :=
  ∀ a : J → ℤ, (∀ j, |(a j : ℝ)| ≤ R) →
    (∃ w : W, (∑ j, (a j : ℝ) * w.val j) ≠ 0) →
    ¬ PolynomialRationalApproximation T R
      (MvPolynomial.homogeneousComponent h (VectorPolynomial.integerRowPolynomial a p))

theorem HasLayerSamplingRank.not_approximation {I J : Type*} [Fintype J]
    {h : ℕ} {T : I → ℝ} {R : ℝ} {W : Submodule ℝ (J → ℝ)}
    {p : VectorPolynomial I ℝ (J → ℝ)} (hrank : HasLayerSamplingRank h T R W p)
    (hp : VectorPolynomial.Homogeneous h p) (a : J → ℤ)
    (ha : ∀ j, |(a j : ℝ)| ≤ R) (hw : ∃ w : W, (∑ j, (a j : ℝ) * w.val j) ≠ 0) :
    ¬ PolynomialRationalApproximation T R (VectorPolynomial.integerRowPolynomial a p) := by
  have hn := hrank a ha hw
  rwa [MvPolynomial.homogeneousComponent_eq_self
    (VectorPolynomial.integerRowPolynomial_homogeneous a p hp)] at hn

end Erdos3

end

section

namespace Erdos3

theorem VectorPolynomial.integerRowPolynomial_homogeneousPart {I J : Type*} [Fintype J]
    (a : J → ℤ) (h : ℕ) (p : VectorPolynomial I ℝ (J → ℝ)) :
    VectorPolynomial.integerRowPolynomial a (VectorPolynomial.homogeneousPart h p) =
      MvPolynomial.homogeneousComponent h (VectorPolynomial.integerRowPolynomial a p) :=
  VectorPolynomial.coordinate_homogeneousPart _ h p

theorem hasLayerSamplingRank_homogeneousPart_iff {I J : Type*} [Fintype J]
    (h : ℕ) (T : I → ℝ) (R : ℝ) (W : Submodule ℝ (J → ℝ))
    (p : VectorPolynomial I ℝ (J → ℝ)) :
    HasLayerSamplingRank h T R W (VectorPolynomial.homogeneousPart h p) ↔
      HasLayerSamplingRank h T R W p := by
  unfold HasLayerSamplingRank
  simp only [VectorPolynomial.integerRowPolynomial_homogeneousPart,
    MvPolynomial.homogeneousComponent_eq_self (MvPolynomial.homogeneousComponent_isHomogeneous h _)]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

variable {I J : Type*} [Fintype J]

noncomputable def samplingRankProjection (a : J → ℤ) (e : J → ℝ) :
    (J → ℝ) →ₗ[ℝ] (J → ℝ) :=
  LinearMap.id - (integerRowLinear a).smulRight e

@[simp] theorem samplingRankProjection_apply (a : J → ℤ) (e v : J → ℝ) :
    samplingRankProjection a e v = v - integerRowLinear a v • e := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem HasLayerSamplingRank.mono {I J : Type*} [Fintype J]
    {h : ℕ} {T : I → ℝ} {R S : ℝ} {W : Submodule ℝ (J → ℝ)}
    {P : VectorPolynomial I ℝ (J → ℝ)}
    (hrank : HasLayerSamplingRank h T S W P) (hRS : R ≤ S)
    (hT : ∀ i, 0 < T i) : HasLayerSamplingRank h T R W P := by
  intro a ha hw happ
  exact hrank a (fun j => (ha j).trans hRS) hw (happ.mono hRS hT)

end Erdos3

end

section

namespace Erdos3

theorem HasLayerSamplingRank.inv_nat_smul {I J : Type*} [Fintype J]
    {h : ℕ} {T : I → ℝ} {R : ℝ} (hR : 0 ≤ R)
    {W : Submodule ℝ (J → ℝ)} {p : VectorPolynomial I ℝ (J → ℝ)}
    (q : ℕ) (hq : 0 < q) (hrank : HasLayerSamplingRank h T ((q : ℝ) * R) W p) :
    HasLayerSamplingRank h T R W ((q : ℝ)⁻¹ • p) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  intro a ha hw happ
  have ha' : ∀ j, |(a j : ℝ)| ≤ (q : ℝ) * R := fun j => (ha j).trans (by nlinarith)
  apply hrank a ha' hw
  have hh := happ.nat_smul q hq
  simpa only [VectorPolynomial.integerRowPolynomial_smul, map_smul, smul_smul,
    mul_inv_cancel₀ hq0, one_smul] using hh

theorem HasLayerSamplingRank.div_nat {I J : Type*} [Fintype J]
    {h : ℕ} {T : I → ℝ} {R : ℝ} (hR : 0 ≤ R)
    {W : Submodule ℝ (J → ℝ)} {p : VectorPolynomial I ℝ (J → ℝ)}
    (hrank : HasLayerSamplingRank h T R W p) (q : ℕ) (hq : 0 < q) :
    HasLayerSamplingRank h T (R / q) W ((q : ℝ)⁻¹ • p) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hr : HasLayerSamplingRank h T ((q : ℝ) * (R / q)) W p := by
    simpa only [mul_div_cancel₀ R hq0] using hrank
  exact HasLayerSamplingRank.inv_nat_smul (div_nonneg hR (Nat.cast_nonneg q)) q hq hr

end Erdos3

end

section

namespace Erdos3

theorem hasLayerSamplingRank_translate_iff {X J : Type*} [Fintype J]
    (a : X → ℝ) (n : ℕ) (H : X → ℝ) (R : ℝ) (U : Submodule ℝ (J → ℝ))
    (p : VectorPolynomial X ℝ (J → ℝ)) (hp : VectorPolynomial.DegreeLE (1 : X → ℕ) n p) :
    HasLayerSamplingRank n H R U (VectorPolynomial.translate a p) ↔
      HasLayerSamplingRank n H R U p := by
  rw [← hasLayerSamplingRank_homogeneousPart_iff n H R U (VectorPolynomial.translate a p),
    VectorPolynomial.homogeneousPart_translate a p hp,
    hasLayerSamplingRank_homogeneousPart_iff]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix BigOperators

namespace VectorPolynomial

def jointRationalSpace {ι κ ρ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι κ ℚ) (A : Matrix ρ ι ℚ) : Submodule ℝ (ι → ℝ) :=
  LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin ⊓
    LinearMap.ker (Matrix.of (fun i j => (A i j : ℝ))).mulVecLin

def appendRankCutRow {ι ρ : Type*} (A : Matrix ρ ι ℚ) (a : ι → ℤ) :
    Matrix (Option ρ) ι ℚ :=
  Matrix.of (fun r i => r.elim (a i : ℚ) (fun r => A r i))

open scoped TensorProduct

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped Matrix BigOperators

end Erdos3

end

section

namespace Erdos3

namespace VectorPolynomial

open scoped TensorProduct

theorem integerRowPolynomial_totalDegree_le {I J : Type*} [Fintype J]
    (a : J → ℤ) {p : VectorPolynomial I ℝ (J → ℝ)} {h : ℕ}
    (hp : DegreeLE (fun _ => 1) h p) : (integerRowPolynomial a p).totalDegree ≤ h := by
  have hw : (integerRowPolynomial a p).weightedTotalDegree (1 : I → ℕ) ≤ h := by
    apply (scalar_weightedDegree_le_iff _ _ _).mpr
    intro α hα
    simp only [integerRowPolynomial, coeff_coordinate, hp α hα, map_zero]
  simpa only [MvPolynomial.weightedTotalDegree_one] using hw

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

open VectorPolynomial

theorem integerRowPolynomial_coefficientGrid {σ J : Type*} [Fintype J]
    (a : J → ℤ) (Q : VectorPolynomial σ ℝ (J → ℝ)) (q : ℕ)
    (hQ : ∀ α, coefficients Q α ∈ realDenominatorGrid q) :
    realPolynomialCoefficientGrid q (integerRowPolynomial a Q) := by
  classical
  have hz : ∀ α, ∃ z : J → ℤ, ∀ j, (z j : ℝ) = (q : ℝ) * coefficients Q α j := by
    intro α
    obtain ⟨z, hz⟩ := hQ α
    exact ⟨z, fun j => congrFun hz j⟩
  choose z hz using hz
  refine ⟨fun α => ∑ j, a j * z α j, funext fun α => ?_⟩
  change ((∑ j, a j * z α j : ℤ) : ℝ) = (q : ℝ) * (integerRowPolynomial a Q).coeff α
  simp only [Int.cast_sum, Int.cast_mul, integerRowPolynomial_coeff, Finset.mul_sum, hz]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integerRowPolynomial_homogeneous_approximation_of_decomposition
    {σ J : Type*} [Fintype J] (h : ℕ) (T : σ → ℝ) (R S b : ℝ)
    (a : J → ℤ) (A E P Q : VectorPolynomial σ ℝ (J → ℝ))
    (q : ℕ) (hq : 0 < q) (hqR : (q : ℝ) ≤ R)
    (hT : ∀ i, 0 < T i) (hb : 0 ≤ b)
    (ha : ∀ j, |(a j : ℝ)| ≤ b)
    (hcost : (Fintype.card J : ℝ) * b * S ≤ R)
    (hA : A = E + P + Q)
    (hE : ∀ α j, |coefficients E α j| ≤ S / monomialScale T α)
    (hP : ∀ α, integerRowLinear a (coefficients P α) = 0)
    (hQ : ∀ α, coefficients Q α ∈ realDenominatorGrid q) :
    PolynomialRationalApproximation T R
      (MvPolynomial.homogeneousComponent h (integerRowPolynomial a A)) := by
  classical
  have hgrid := integerRowPolynomial_coefficientGrid a Q q hQ
  obtain ⟨Z, hZ⟩ := (realPolynomialCoefficientGrid_iff q _).mp hgrid
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hZcoeff (α : σ →₀ ℕ) :
      ((Z.coeff α : ℤ) : ℝ) / q = (integerRowPolynomial a Q).coeff α := by
    have hz := congrArg (fun polynomial : MvPolynomial σ ℝ => polynomial.coeff α) hZ
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul] at hz
    change ((Z.coeff α : ℤ) : ℝ) = (q : ℝ) * (integerRowPolynomial a Q).coeff α at hz
    rw [hz, mul_div_cancel_left₀ _ hq0]
  have hR : 0 ≤ R := (Nat.cast_nonneg q).trans hqR
  refine ⟨q, hq, hqR, MvPolynomial.homogeneousComponent h Z, ?_⟩
  intro α
  by_cases hα : α.degree = h
  · simp only [MvPolynomial.coeff_homogeneousComponent, if_pos hα, hZcoeff]
    have heq : (integerRowPolynomial a A).coeff α - (integerRowPolynomial a Q).coeff α =
        ∑ j, (a j : ℝ) * coefficients E α j := by
      rw [hA]
      simp only [integerRowPolynomial_coeff, map_add, Finsupp.add_apply, Pi.add_apply,
        mul_add, Finset.sum_add_distrib]
      have hz := hP α
      rw [integerRowLinear_apply] at hz
      rw [hz]
      ring
    rw [heq]
    calc
      _ ≤ ∑ j, |(a j : ℝ) * coefficients E α j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : J, b * (S / monomialScale T α) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (ha j) (hE α j) (abs_nonneg _) hb
      _ = ((Fintype.card J : ℝ) * b * S) / monomialScale T α := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      _ ≤ R / monomialScale T α :=
        div_le_div_of_nonneg_right hcost (monomialScale_pos T hT α).le
  · simp only [MvPolynomial.coeff_homogeneousComponent, if_neg hα, Int.cast_zero,
      zero_div, sub_zero, abs_zero]
    exact div_nonneg hR (monomialScale_pos T hT α).le

theorem samplingRank_le_real_column_span_of_decomposition
    {σ J L : Type*} [Fintype J] [Fintype L]
    (B : Matrix J L ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hB : ∀ j i, RationalHeightLE (B j i) H)
    (h : ℕ) (T : σ → ℝ) (R S : ℝ) (W : Submodule ℝ (J → ℝ))
    (A E P Q : VectorPolynomial σ ℝ (J → ℝ))
    (q : ℕ) (hq : 0 < q) (hT : ∀ i, 0 < T i)
    (hrank : HasLayerSamplingRank h T R W A)
    (hA : A = E + P + Q)
    (hE : ∀ α j, |coefficients E α j| ≤ S / monomialScale T α)
    (hP : ∀ α, coefficients P α ∈ Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ))))
    (hQ : ∀ α, coefficients Q α ∈ realDenominatorGrid q)
    (hqR : (q : ℝ) ≤ R)
    (hrowR : (realSpanIntegerRowBound (Fintype.card L) (Fintype.card J) H : ℝ) ≤ R)
    (hcost : (Fintype.card J : ℝ) *
      (realSpanIntegerRowBound (Fintype.card L) (Fintype.card J) H : ℝ) * S ≤ R) :
    W ≤ Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ))) := by
  classical
  obtain ⟨C, hC, hker⟩ := exists_real_span_integer_defining_matrix B hH hB
  intro x hx
  apply (real_column_span_mem_iff B x).mpr
  rw [← hker]
  change (fun i j => (C i j : ℝ)) *ᵥ x = 0
  ext i
  by_contra hix
  have hkill (α : σ →₀ ℕ) : integerRowLinear (C i) (coefficients P α) = 0 := by
    have hp : coefficients P α ∈ LinearMap.ker
        (Matrix.mulVecLin (fun i j => (C i j : ℝ))) := by
      rw [hker]
      exact (real_column_span_mem_iff B _).mp (hP α)
    have hh := congrFun hp i
    change (∑ j, (C i j : ℝ) * coefficients P α j) = 0 at hh
    simpa only [integerRowLinear_apply] using hh
  apply hrank (C i) (fun j => (hC i j).trans hrowR) ⟨⟨x, hx⟩, hix⟩
  exact integerRowPolynomial_homogeneous_approximation_of_decomposition h T R S
    (realSpanIntegerRowBound (Fintype.card L) (Fintype.card J) H : ℝ)
    (C i) A E P Q q hq hqR hT (Nat.cast_nonneg _) (hC i) hcost hA hE hkill hQ

end Erdos3

end

end OAI

end


