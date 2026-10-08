-- Prove2me | Definitions.Def_OAIErdos3B007
-- name    : OAIErdos3B007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T10:10:45.361491+00:00
-- url     : https://prove2.me/theorems/366d4944-d67e-4bcb-88c7-6832c71484e0
-- title:
--   OpenAI Erdős-3 split, definitions bundle 8 of 88
-- statement:
--   Definitions bundle 8 of 88 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B006`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 8 available.
--
--   Modules: `OAI.Erdos3.BohrLattice.BoxCertificate.SuccessiveProductCertificate.noConfusion`, `OAI.Erdos3.BohrLattice.BoxCertificate.realBox`, `OAI.Erdos3.BohrLattice.Primitive.IsPrimitive`, `OAI.Erdos3.BohrLattice.Primitive.IsPrimitive.ne_zero`, `OAI.Erdos3.BohrLattice.Primitive.content`, `OAI.Erdos3.BohrLattice.Primitive.content_dvd`, `OAI.Erdos3.BohrLattice.Primitive.content_mul_divideContent`, `OAI.Erdos3.BohrLattice.Primitive.content_ne_zero`, `OAI.Erdos3.BohrLattice.Primitive.divideContent`, `OAI.Erdos3.BohrLattice.Primitive.divideContent_ne_zero`, `OAI.Erdos3.BohrLattice.Primitive.divideContent_primitive`, `OAI.Erdos3.BohrLattice.Primitive.exists_bezout_finset`, `OAI.Erdos3.BohrLattice.Primitive.isPrimitive_of_content_eq_one`, `OAI.Erdos3.BohrLattice.PrimitiveExtension.dotLinear`, `OAI.Erdos3.BohrLattice.PrimitiveExtension.dotLinear_apply`, `OAI.Erdos3.BohrLattice.PrimitiveExtension.exists_basis_zero_eq_of_isPrimitive`, `OAI.Erdos3.BohrLattice.PrimitiveExtension.isPrimitive_of_minimal_gauge`, `OAI.Erdos3.BohrLattice.PrimitiveExtension.shortest_zspan_vector_primitive_and_extends`, `OAI.Erdos3.BohrLattice.PrimitiveExtension.zspanBasis`, `OAI.Erdos3.BohrLattice.PrimitiveExtension.zspanBasis_apply_coe`, `OAI.Erdos3.BohrLattice.PrimitiveExtension.zspanCoordEquiv`, `OAI.Erdos3.BohrLattice.PrimitiveExtension.zspanCoordEquiv_apply`, `OAI.Erdos3.NilpotentLieFiltration.mem_pi_layer`, `OAI.Erdos3.NilpotentLieFiltration.pi`, `OAI.Erdos3.SelectedCoefficientComplement`, `OAI.Erdos3.SpatialKernelRemainder`, `OAI.Erdos3.VectorPolynomial.coefficients_ofCoordinates_pi_apply`, `OAI.Erdos3.VectorPolynomial.finiteFreezing_exp_half_score_le`, `OAI.Erdos3.VectorPolynomial.finiteFreezing_exp_score_surplus`, `OAI.Erdos3.VectorPolynomial.finiteFreezing_exp_weighted_error_le`, `OAI.Erdos3.VectorPolynomial.forecastOriginalSmoothBudget`, `OAI.Erdos3.VectorPolynomial.forecastOriginalSmoothBudget_bounds`, `OAI.Erdos3.VectorPolynomial.linearMap_pi_apply_eq_sum`, `OAI.Erdos3.VectorPolynomial.norm_finset_prod_sub_prod_le_sum`, `OAI.Erdos3.VectorPolynomial.normalizedSiteTwistProduct`, `OAI.Erdos3.VectorPolynomial.normalizedSiteTwistProduct_bounds`, `OAI.Erdos3.VectorPolynomial.sum_projection_C_eq`, `OAI.Erdos3.VectorPolynomial.sum_projection_coordinate_eq`, `OAI.Erdos3.VectorPolynomial.sum_projection_coordinate_sub_C_eq`, `OAI.Erdos3.VectorPolynomial.sum_projection_remainder_eq`, `OAI.Erdos3.additiveBoxDifference_map`, `OAI.Erdos3.affineInterval_normalized_bounds`, `OAI.Erdos3.baseArrayJoin`, `OAI.Erdos3.baseArrayJoin_eta`, `OAI.Erdos3.centralActionBudget`, `OAI.Erdos3.centralActionBudget_nonneg`, `OAI.Erdos3.characterCrossRow`, `OAI.Erdos3.characterCrossRow_derivative`, `OAI.Erdos3.characterCrossRow_derivative_correlation_norm`, `OAI.Erdos3.characterCrossRow_norm`, `OAI.Erdos3.character_real_sub`, `OAI.Erdos3.complex_mixed_polarization`, `OAI.Erdos3.complex_normalization_error`, `OAI.Erdos3.conjugationCoordinatePolynomial`, `OAI.Erdos3.conjugationCoordinatePolynomial_degree`, `OAI.Erdos3.conjugationCoordinatePolynomial_eval`, `OAI.Erdos3.conjugationCoordinatePolynomial_zero`, `OAI.Erdos3.conjugationInput`, `OAI.Erdos3.conjugationInput_mem_denominatorGrid`, `OAI.Erdos3.conjugationInput_sub_mem_scaledGrid`, `OAI.Erdos3.conjugation_preserves_inner_grid`, `OAI.Erdos3.constraintProjectionInput`, `OAI.Erdos3.constraintProjectionInput_grid`, `OAI.Erdos3.constraintProjectionInput_weighted`, `OAI.Erdos3.constraintProjectionMatrix`, `OAI.Erdos3.contDiff_coordinateBCH`, `OAI.Erdos3.contDiff_dynkinWord_coordinates`, `OAI.Erdos3.contDiff_lieBCH_coordinates`, `OAI.Erdos3.contDiff_lie_coordinates`, `OAI.Erdos3.contDiff_rightBracketList_coordinates`, `OAI.Erdos3.dehomogenizingSubstitution`, `OAI.Erdos3.density_mul_integrable`, `OAI.Erdos3.det_eq_one_of_triangular_labels`, `OAI.Erdos3.det_smul_one_sub_posSemidef`, `OAI.Erdos3.divided_basisFun_eq_smul`, `OAI.Erdos3.eigenvalues_le_det_of_sub_one_posSemidef`, `OAI.Erdos3.empirical_step_sq_le`, `OAI.Erdos3.exists_convex_empirical_average`, `OAI.Erdos3.exists_convex_empirical_sum`, `OAI.Erdos3.exists_le_linear_of_mem_convexHull`, `OAI.Erdos3.exists_minimal_row_minor`, `OAI.Erdos3.exists_missing_coordinate_product_factors`, `OAI.Erdos3.exists_nonzero_row_minor`, `OAI.Erdos3.exists_orthogonal_section`, `OAI.Erdos3.exists_preserved_nonzero_row_minor`, `OAI.Erdos3.exists_regular_point_of_monotone`, `OAI.Erdos3.exists_verticalDecompositionBudget_bound`, `OAI.Erdos3.exp_neg_roundedModelLogBudget_le_density`, `OAI.Erdos3.finiteGradedBranchLevel`, `OAI.Erdos3.finiteGradedBranchLevel_all_valid`, `OAI.Erdos3.finiteGradedBranchLevel_card_le_exp_sum`, `OAI.Erdos3.finiteGradedBranchLevel_child_mem`, `OAI.Erdos3.finiteGradedBranchLevel_mem_succ`, `OAI.Erdos3.finiteGradedBranchLevel_mem_zero`, `OAI.Erdos3.finiteGradedBranchVertices`, `OAI.Erdos3.finiteGradedBranchVertices_mem_iff`, `OAI.Erdos3.finiteLatticeBasis`, `OAI.Erdos3.finiteRowChartRadius`, `OAI.Erdos3.finiteRowChartRadius_budget`, `OAI.Erdos3.finiteRowChartRadius_inv_le_exp`, `OAI.Erdos3.finiteRowChartRadius_pos`, `OAI.Erdos3.homogenizingMonomial`, `OAI.Erdos3.homogenizingMonomial_dehomogenize`, `OAI.Erdos3.homogenizingMonomial_homogeneous`, `OAI.Erdos3.integerIco_card`, `OAI.Erdos3.integerIco_intersection`, `OAI.Erdos3.integerIco_subset_range`, `OAI.Erdos3.integerImagePMF`, `OAI.Erdos3.integerRadixHom`, `OAI.Erdos3.integerRadixValue`, `OAI.Erdos3.integerRadixValue_add`, `OAI.Erdos3.integerRadixValue_bounds`, `OAI.Erdos3.integerRadixValue_injective_on_digits`, `OAI.Erdos3.integerRadixValue_zero`, `OAI.Erdos3.inverseScaledBasis`, `OAI.Erdos3.inverseScaledBasis_apply`, `OAI.Erdos3.inverseScaledBasis_bracket`, `OAI.Erdos3.inverseScaledBasis_repr`, `OAI.Erdos3.iteratedBoxDifference_character`, `OAI.Erdos3.le_centralActionBudget`, `OAI.Erdos3.lieAlgebraPi`, `OAI.Erdos3.liePiEval`, `OAI.Erdos3.liePiEval_apply`, `OAI.Erdos3.liePiMap`, `OAI.Erdos3.liePiMap_apply`, `OAI.Erdos3.lieRingPi`, `OAI.Erdos3.lie_coordinate_formula_real`, `OAI.Erdos3.lie_pi_apply`, `OAI.Erdos3.lie_pi_structure_height`, `OAI.Erdos3.linearMap_divided_basis_norm_le`, `OAI.Erdos3.lipschitzWith_of_unit_range_near_nonzero`, `OAI.Erdos3.lipschitzWith_of_unit_range_support_box`, `OAI.Erdos3.lipschitz_reconstruction_of_local_lifts`, `OAI.Erdos3.lower_unitriangular_preserves_minimal_minor`, `OAI.Erdos3.mem_weightedSupportDrop_iff`, `OAI.Erdos3.minimal_row_minor_coordinate_zero`, `OAI.Erdos3.missingCoordinateProduct`, `OAI.Erdos3.missingCoordinateProduct_independent`, `OAI.Erdos3.missingCoordinateProduct_norm`, `OAI.Erdos3.missingCoordinateProduct_prod`, `OAI.Erdos3.momentLinear`, `OAI.Erdos3.momentLinear_lipschitz`, `OAI.Erdos3.momentWeightBound`, `OAI.Erdos3.momentWeightBound_pos`, `OAI.Erdos3.mulVec_constraintProjectionInput`, `OAI.Erdos3.multiaffineBiasBudget`, `OAI.Erdos3.multiaffineBiasBudget_bounds`, `OAI.Erdos3.multiaffineBiasBudget_eq_power`, `OAI.Erdos3.multiaffineBiasBudget_pos`, `OAI.Erdos3.multiaffineExpansion`, `OAI.Erdos3.multiaffineExpansion_box_difference`, `OAI.Erdos3.multilinear_affine_expansion`, `OAI.Erdos3.nativeTwistedSlice_bias_precision`, `OAI.Erdos3.nativeTwistedSlice_freezing_error`, `OAI.Erdos3.nonzero_row_minor_injective`, `OAI.Erdos3.norm_density_integral_le_one`, `OAI.Erdos3.norm_momentLinear_le`, `OAI.Erdos3.norm_momentWeight_le`, `OAI.Erdos3.normalizedSpatialAmplitude_shift_le`, `OAI.Erdos3.normalizedSpatialAmplitude_shift_le_of_norm_le`, `OAI.Erdos3.one_le_det_of_sub_one_posSemidef`, `OAI.Erdos3.one_le_eigenvalues_of_sub_one_posSemidef`, `OAI.Erdos3.piFinset_axis_subset`, `OAI.Erdos3.piFinset_card_ratio_le_axis`, `OAI.Erdos3.pmf_bind_injective_toReal_cap`, `OAI.Erdos3.pmf_bind_point_cap`, `OAI.Erdos3.pmf_map_injective_cap`, `OAI.Erdos3.pmf_map_toReal_indicator`, `OAI.Erdos3.pmf_point_indicator_norm`, `OAI.Erdos3.polarizationPhase`, `OAI.Erdos3.polarizationPhase_norm`, `OAI.Erdos3.polarizationWeight`, `OAI.Erdos3.polarizationWeight_cost`, `OAI.Erdos3.polarizationWeight_norm`, `OAI.Erdos3.polynomialPrimitive`, `OAI.Erdos3.polynomialPrimitive_derivative`, `OAI.Erdos3.polynomialPrimitive_eval_zero`, `OAI.Erdos3.polynomialPrimitive_unique`, `OAI.Erdos3.polynomial_eq_of_derivative_of_eval_zero`, `OAI.Erdos3.pow_mem_powerSubgroup`, `OAI.Erdos3.pow_mem_subgroupPowerCover`, `OAI.Erdos3.powerSubgroup`, `OAI.Erdos3.powerSubgroup_characteristic`, `OAI.Erdos3.powerSubgroup_map_le`, `OAI.Erdos3.quotientRightEDist`, `OAI.Erdos3.quotientRightEDist_comm`, `OAI.Erdos3.quotientRightEDist_mk`, `OAI.Erdos3.quotientRightEDist_mk_le`, `OAI.Erdos3.quotientRightEDist_self`, `OAI.Erdos3.quotientRightEDist_triangle`, `OAI.Erdos3.quotient_mk_mul_mem`, `OAI.Erdos3.realDirectionExtension`, `OAI.Erdos3.realDirectionExtension_apply`, `OAI.Erdos3.realDirectionExtension_rat`, `OAI.Erdos3.realTripleEquiv`, `OAI.Erdos3.realTripleEquiv_left`, `OAI.Erdos3.realTripleEquiv_neutral`, `OAI.Erdos3.realTripleEquiv_right`, `OAI.Erdos3.realTripleEquiv_tmul`, `OAI.Erdos3.reconstruction_norm_le`, `OAI.Erdos3.rectangularLatticePoint_add_displacement`, `OAI.Erdos3.rightCosetEDist`, `OAI.Erdos3.rightCosetEDist_comm`, `OAI.Erdos3.rightCosetEDist_le`, `OAI.Erdos3.rightCosetEDist_mul_left`, `OAI.Erdos3.rightCosetEDist_mul_right`, `OAI.Erdos3.rightCosetEDist_rel`, `OAI.Erdos3.rightCosetEDist_self`, `OAI.Erdos3.rightCosetEDist_triangle`, `OAI.Erdos3.roundedModelLogBudget`, `OAI.Erdos3.roundedModelLogBudget_nonneg`, `OAI.Erdos3.roundedModelScale_le_exp`, `OAI.Erdos3.row_minor_update_det`, `OAI.Erdos3.scalarBadSublevelRamp`, `OAI.Erdos3.scalarBadSublevelRamp_eq_one`, `OAI.Erdos3.scalarBadSublevelRamp_eq_zero`, `OAI.Erdos3.scalarBadSublevelRamp_lipschitz`, `OAI.Erdos3.scalarBadSublevelRamp_range`, `OAI.Erdos3.scalarUnitEquiv`, `OAI.Erdos3.scaledInputPMF`, `OAI.Erdos3.scaledInputWeightSum_pos`, `OAI.Erdos3.scaledIntegerGrid_mem_denominatorGrid`, `OAI.Erdos3.selectedCoefficientComplementFill`, `OAI.Erdos3.selectedCoefficientJoin`, `OAI.Erdos3.selectedCoefficientJoin_complement`, `OAI.Erdos3.selectedCoefficientJoin_selected`, `OAI.Erdos3.spatialTwoBlockEquiv`, `OAI.Erdos3.spatialTwoBlockEquiv_symm_first`, `OAI.Erdos3.spatialTwoBlockEquiv_symm_second`, `OAI.Erdos3.subgroupPowerCover`, `OAI.Erdos3.subgroupPowerCover_characteristic`, `OAI.Erdos3.subgroupPowerCover_le`, `OAI.Erdos3.subgroupPowerCover_le_iff`, `OAI.Erdos3.subgroupPowerCover_normal`, `OAI.Erdos3.subgroupPowerCover_subgroupOf`, `OAI.Erdos3.submoduleQuotientCoordinateBasis`, `OAI.Erdos3.submoduleQuotientCoordinateBasis_matrix`, `OAI.Erdos3.submoduleQuotientCoordinateEquiv`, `OAI.Erdos3.submoduleQuotientCoordinateEquiv_mk`, `OAI.Erdos3.submoduleQuotientCoordinateEquiv_symm`, `OAI.Erdos3.tripleAssemble`, `OAI.Erdos3.tripleAssemble_decompose`, `OAI.Erdos3.tripleAssemble_lie`, `OAI.Erdos3.tripleLeft`, `OAI.Erdos3.tripleLeft_assemble`, `OAI.Erdos3.tripleNeutral`, `OAI.Erdos3.tripleNeutral_assemble`, `OAI.Erdos3.tripleRight`, `OAI.Erdos3.tripleRight_assemble`, `OAI.Erdos3.twoKernelCopies`, `OAI.Erdos3.twoKernelEmbedding`, `OAI.Erdos3.unitIntervalBox_eq_image`, `OAI.Erdos3.unitIntervalBox_expect`, `OAI.Erdos3.verticalDecompositionBudget`, `OAI.Erdos3.verticalDecompositionBudget_nonneg`, `OAI.Erdos3.weightedSupportDrop`, `OAI.Erdos3.weightedSupportDrop_antitone`, `OAI.Erdos3.weightedSupportDrop_eq_zero`, `OAI.Erdos3.weightedSupportDrop_le`, `OAI.Erdos3.weightedSupportDrop_mul`, `OAI.Erdos3.weightedSupportDrop_mul_LE`, `OAI.Erdos3.weightedSupportDrop_one`, `OAI.Erdos3.weightedSupportDrop_rename`, `OAI.Erdos3.weightedSupportDrop_zero`, `OAI.Erdos3.weightedSupportLE_mul_drop`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B005

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MultiaffineBiasBudget
namespace OAI

section

namespace Erdos3

noncomputable def multiaffineBiasBudget (n : ℕ) (ζ : ℝ) : ℝ :=
  denseProductDensityBudget n (ζ^(2^n)/(2*3^n))/ζ^(2^n)

theorem multiaffineBiasBudget_pos (n : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    0 < multiaffineBiasBudget n ζ := by
  have h := denseProductDensityBudget_pos n
    (show 0 < ζ^(2^n)/(2*3^n) by positivity)
  exact div_pos h (pow_pos hζ _)

theorem multiaffineBiasBudget_bounds (n : ℕ) {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    denseProductDensityBudget n (ζ^(2^n)/(2*3^n)) ≤ multiaffineBiasBudget n ζ ∧
    multiaffineBiasBudget n ζ * ζ^(2^n) = denseProductDensityBudget n (ζ^(2^n)/(2*3^n)) := by
  have hp : 0 < ζ^(2^n) := pow_pos hζ _
  have hp1 : ζ^(2^n) ≤ 1 := pow_le_one₀ hζ.le hζ1
  have hL := denseProductDensityBudget_pos n
    (show 0 < ζ^(2^n)/(2*3^n) by positivity)
  constructor
  · apply (le_div_iff₀ hp).mpr
    exact mul_le_of_le_one_right hL.le hp1
  · exact div_mul_cancel₀ _ hp.ne'

theorem multiaffineBiasBudget_eq_power (n : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    multiaffineBiasBudget n ζ =
      ((denseProductDensityConstant n : ℝ)*(2*3^n)^denseProductExponent n) /
        ζ^(2^n*(denseProductExponent n+1)) := by
  unfold multiaffineBiasBudget denseProductDensityBudget
  rw [div_pow, div_div, mul_add, mul_one, pow_add, pow_mul]
  field_simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultiaffineExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def multiaffineExpansion {R : Type*} [CommRing R] {n : ℕ}
    (c : Finset (Fin n) → R) (x : Fin n → R) : R :=
  ∑ S : Finset (Fin n), c S * ∏ i, if i ∈ S then x i else 1

theorem multiaffineExpansion_box_difference {R Z : Type*} [CommRing R]
    (n : ℕ) {X : Fin n → Type*} (c : Finset (Fin n) → Z → R)
    (f : ∀ i, X i → R) (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n
      (fun x t => multiaffineExpansion (fun S => c S t) (fun i => f i (x i))) u v z =
      c Finset.univ z * ∏ i, (f i (u i)-f i (v i)) := by
  unfold multiaffineExpansion
  rw [additiveBoxDifference_sum]
  have hprod (S : Finset (Fin n)) :
      additiveBoxDifference n (fun x t => c S t * ∏ i, if i ∈ S then f i (x i) else 1) u v z =
        c S z * ∏ i, ((if i ∈ S then f i (u i) else 1)-(if i ∈ S then f i (v i) else 1)) :=
    additiveBoxDifference_product n (c S) (fun i x => if i ∈ S then f i x else 1) u v z
  simp_rw [hprod]
  rw [Finset.sum_eq_single (Finset.univ : Finset (Fin n))]
  · simp
  · intro S _ hS
    have hmissing : ∃ i, i ∉ S := by
      by_contra h
      apply hS
      apply Finset.eq_univ_of_forall
      intro i
      by_contra hi
      exact h ⟨i,hi⟩
    obtain ⟨i,hi⟩ := hmissing
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · exact mul_zero _
    · simp only [hi, ite_false, sub_self]
  · simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BoxDifferenceCharacter
namespace OAI

section

namespace Erdos3

open CircleFourier

theorem character_real_sub (a b : ℝ) :
    character ((a-b : ℝ) : CircleFourier.Circle) =
      character (a : CircleFourier.Circle) * star (character (b : CircleFourier.Circle)) := by
  rw [sub_eq_add_neg, AddCircle.coe_add, AddCircle.coe_neg, character_add, character_neg]

theorem iteratedBoxDifference_character (n : ℕ) {X : Fin n → Type*} {Z : Type*}
    (F : (∀ i, X i) → Z → ℝ) (u v : ∀ i, X i) (z : Z) :
    iteratedBoxDifference n (fun x t => character (F x t : CircleFourier.Circle)) u v z =
      character ((additiveBoxDifference n F u v z : ℝ) : CircleFourier.Circle) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iteratedBoxDifference, additiveBoxDifference, ← character_real_sub]
    exact ih _ (Fin.tail u) (Fin.tail v)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MultilinearAffineExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem multilinear_affine_expansion {H R M : Type*} [Fintype H] [DecidableEq H] [CommRing R]
    [AddCommGroup M] [Module R M] (F : MultilinearMap R (fun _ : H => M) R)
    (b w : H → M) (x : H → R) :
    F (fun i => b i + x i • w i) =
      ∑ S : Finset H, F (S.piecewise w b) * ∏ i ∈ S, x i := by
  have he : (fun i => b i + x i • w i) = (fun i => x i • w i) + b := by
    funext i
    exact add_comm _ _
  rw [he, F.map_add_univ]
  apply Finset.sum_congr rfl
  intro S _
  have hs : S.piecewise (fun i => x i • w i) b =
      (fun i => (if i ∈ S then x i else 1) • S.piecewise w b i) := by
    funext i
    by_cases hi : i ∈ S <;> simp [Finset.piecewise, hi]
  rw [hs, F.map_smul_univ, Finset.prod_ite_mem_eq, smul_eq_mul, mul_comm]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxDifferenceSubstitution
namespace OAI

section

namespace Erdos3

theorem additiveBoxDifference_map {X Y Z R : Type*} [AddGroup R] (n : ℕ) :
    ∀ (f : Fin n → X → Y) (F : (Fin n → Y) → Z → R)
      (u v : Fin n → X) (z : Z),
      additiveBoxDifference n (fun x t => F (fun i => f i (x i)) t) u v z =
        additiveBoxDifference n F (fun i => f i (u i)) (fun i => f i (v i)) z := by
  induction n with
  | zero =>
    intro f F u v z
    simp only [additiveBoxDifference]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro f F u v z
    have hcons (a : X) (x : Fin n → X) :
        (fun i => f i ((Fin.cons a x : Fin (n + 1) → X) i)) =
          (Fin.cons (f 0 a) (fun i : Fin n => f i.succ (x i)) : Fin (n + 1) → Y) := by
      funext i
      cases i using Fin.cases <;> rfl
    simp only [additiveBoxDifference]
    simp_rw [hcons]
    exact ih (fun i => f i.succ)
      (fun y t => F (Fin.cons (f 0 (u 0)) y) t - F (Fin.cons (f 0 (v 0)) y) t)
      (Fin.tail u) (Fin.tail v) z

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledInputProbability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem scaledInputWeightSum_pos (f : (J → ℝ) × (I → ℝ) → ℝ) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) (hM : 0 < scaledInputMass f S T) :
    0 < scaledInputWeightSum f S T := by
  have hp : 0 < (∏ i, S i) * (∏ j, T j) :=
    mul_pos (Finset.prod_pos fun i _ => hS i) (Finset.prod_pos fun j _ => hT j)
  have h := mul_pos hM hp
  rwa [scaledInputMass, div_mul_cancel₀ _ hp.ne'] at h

noncomputable def scaledInputPMF (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T) :
    PMF ((I → ℤ) × (J → ℤ)) :=
  realWeightPMF (scaledIntegerWeight f S T) (fun _ => hf0 _)
    (scaledIntegerWeight_summable f S T hS hT hsupport) (scaledInputWeightSum_pos f S T hS hT hM)

noncomputable def integerImagePMF (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T) :
    PMF (I → ℤ) :=
  (scaledInputPMF f hf0 S T hS hT hsupport hM).map (fun p => A *ᵥ p.1 + B *ᵥ p.2)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformSelectedCoefficientProductLaw
namespace OAI

section

namespace Erdos3

open scoped ENNReal Classical

theorem pmf_map_injective_cap {X Y : Type*} (p : PMF X) (f : X → Y)
    (hf : Function.Injective f) {C : ℝ≥0∞} (hp : ∀ x, p x ≤ C) (y : Y) :
    p.map f y ≤ C := by
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    rw [pmf_map_injective_at p f hf]
    exact hp x
  · rw [pmf_map_zero_off_range p f y hy]
    exact bot_le

theorem pmf_bind_point_cap {X Y : Type*} (p : PMF X) (q : X → PMF Y)
    {C : ℝ≥0∞} (y : Y) (hq : ∀ x, q x y ≤ C) : p.bind q y ≤ C := by
  rw [PMF.bind_apply]
  calc
    _ ≤ ∑' x, p x * C := ENNReal.tsum_le_tsum (fun x => by gcongr; exact hq x)
    _ = C := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

theorem pmf_bind_injective_toReal_cap {X Y Z : Type*} (p : PMF X) (q : PMF Y)
    (f : Y → X → Z) (hf : ∀ y, Function.Injective (f y))
    {C : ℝ} (hC : 0 ≤ C) (hp : ∀ x, (p x).toReal ≤ C) (z : Z) :
    ((q.bind (fun y => p.map (f y))) z).toReal ≤ C := by
  have hp' (x : X) : p x ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal (p.apply_ne_top x)]
    exact ENNReal.ofReal_le_ofReal (hp x)
  have h := pmf_bind_point_cap q (fun y => p.map (f y)) z
    (fun y => pmf_map_injective_cap p (f y) (hf y) hp' z)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hC)

theorem pmf_map_toReal_indicator {X Y : Type*} [DecidableEq Y] (p : PMF X) (f : X → Y) (y : Y) :
    (p.map f y).toReal = ∑' x, (p x).toReal * (if f x = y then 1 else 0) := by
  rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro x
    by_cases h : y = f x
    · simp [h]
    · simp [h, Ne.symm h]
  · intro x
    split_ifs <;> first | exact p.apply_ne_top x | exact ENNReal.zero_ne_top

theorem pmf_point_indicator_norm {X Y : Type*} [DecidableEq Y] (p : PMF X) (f : X → Y) (y : Y) :
    ‖∑' x, ((p x).toReal : ℂ) * (if f x = y then 1 else 0)‖ = (p.map f y).toReal := by
  calc
    _ = ‖((∑' x, (p x).toReal * (if f x = y then 1 else 0) : ℝ) : ℂ)‖ := by
      simp only [Complex.ofReal_tsum, Complex.ofReal_mul, apply_ite, Complex.ofReal_one, Complex.ofReal_zero]
    _ = _ := by rw [← pmf_map_toReal_indicator, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def baseArrayJoin {K I X : Type*} (tail : K × I → X) (base : I → X) : Option K × I → X :=
  fun z => match z.1 with | none => base z.2 | some k => tail (k,z.2)

theorem baseArrayJoin_eta {K I X : Type*} (z : Option K × I → X) :
    baseArrayJoin (fun k => z (some k.1,k.2)) (fun i => z (none,i)) = z := by
  funext k
  rcases k with ⟨k,i⟩
  cases k <;> rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

abbrev SelectedCoefficientComplement {A J : Type*} (e : A ↪ J) :=
  {j : J // j ∉ Set.range e}

noncomputable def selectedCoefficientComplementFill {A J X : Type*}
    (e : A ↪ J) (x0 : X) (tail : SelectedCoefficientComplement e → X) : J → X :=
  Function.extend Subtype.val tail (fun _ => x0)

noncomputable def selectedCoefficientJoin {A J X : Type*}
    (e : A ↪ J) (x0 : X) (tail : SelectedCoefficientComplement e → X)
    (selected : A → X) : J → X :=
  Function.extend e selected (selectedCoefficientComplementFill e x0 tail)

@[simp] theorem selectedCoefficientJoin_selected {A J X : Type*}
    (e : A ↪ J) (x0 : X) (tail : SelectedCoefficientComplement e → X)
    (selected : A → X) (a : A) :
    selectedCoefficientJoin e x0 tail selected (e a) = selected a :=
  e.injective.extend_apply _ _ _

@[simp] theorem selectedCoefficientJoin_complement {A J X : Type*}
    (e : A ↪ J) (x0 : X) (tail : SelectedCoefficientComplement e → X)
    (selected : A → X) (k : SelectedCoefficientComplement e) :
    selectedCoefficientJoin e x0 tail selected k.val = tail k := by
  rw [selectedCoefficientJoin, Function.extend_apply' _ _ _ k.property]
  exact Subtype.val_injective.extend_apply _ _ k

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrimitiveExtension
namespace OAI

namespace Erdos3.BohrLattice.Primitive

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def IsPrimitive (z : ι → ℤ) : Prop :=
  ∃ u : ι → ℤ, ∑ i, u i * z i = 1

theorem IsPrimitive.ne_zero {z : ι → ℤ} (hz : IsPrimitive z) : z ≠ 0 := by
  rintro rfl
  simp [IsPrimitive] at hz

def content (z : ι → ℤ) : ℤ := Finset.univ.gcd z

theorem content_dvd (z : ι → ℤ) (i : ι) : content z ∣ z i := by
  exact Finset.gcd_dvd (Finset.mem_univ i)

theorem content_ne_zero {z : ι → ℤ} (hz : z ≠ 0) : content z ≠ 0 := by
  rw [content, Finset.gcd_ne_zero_iff]
  simpa [funext_iff] using hz

def divideContent (z : ι → ℤ) : ι → ℤ := fun i => z i / content z

theorem content_mul_divideContent (z : ι → ℤ) (i : ι) :
    content z * divideContent z i = z i := by
  rw [mul_comm]
  exact Int.ediv_mul_cancel (content_dvd z i)

omit [Fintype ι] in
theorem exists_bezout_finset (s : Finset ι) (z : ι → ℤ) :
    ∃ u : ι → ℤ, ∑ i ∈ s, u i * z i = s.gcd z := by
  classical
  induction s using Finset.induction with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨u, hu⟩ := ih
      let A : ℤ := Int.gcdA (z a) (s.gcd z)
      let B : ℤ := Int.gcdB (z a) (s.gcd z)
      refine ⟨fun i => if i = a then A else B * u i, ?_⟩
      rw [Finset.sum_insert ha, Finset.gcd_insert]
      simp only [if_pos]
      have hsum :
          (∑ i ∈ s, (if i = a then A else B * u i) * z i) =
            B * s.gcd z := by
        calc
          (∑ i ∈ s, (if i = a then A else B * u i) * z i) =
              ∑ i ∈ s, B * (u i * z i) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [if_neg (by intro hia; subst i; exact ha hi)]
                ring
          _ = B * ∑ i ∈ s, u i * z i := by
                rw [Finset.mul_sum]
          _ = B * s.gcd z := by rw [hu]
      rw [hsum]
      dsimp [A, B]
      rw [mul_comm B, mul_comm (Int.gcdA (z a) (s.gcd z))]
      exact (Int.gcd_eq_gcd_ab (z a) (s.gcd z)).symm

theorem isPrimitive_of_content_eq_one {z : ι → ℤ} (hz : content z = 1) :
    IsPrimitive z := by
  obtain ⟨u, hu⟩ := exists_bezout_finset Finset.univ z
  have hu' : ∑ i, u i * z i = content z := by
    simpa [content] using hu
  exact ⟨u, hu'.trans hz⟩

theorem divideContent_primitive {z : ι → ℤ} (hz : z ≠ 0) :
    IsPrimitive (divideContent z) := by
  apply isPrimitive_of_content_eq_one
  rw [content]
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  exact Finset.gcd_div_eq_one (Finset.mem_univ i) hi

theorem divideContent_ne_zero {z : ι → ℤ} (hz : z ≠ 0) :
    divideContent z ≠ 0 := (divideContent_primitive hz).ne_zero

end Erdos3.BohrLattice.Primitive

namespace Erdos3.BohrLattice.PrimitiveExtension

open scoped BigOperators
open Module

noncomputable section

def dotLinear {n : ℕ} (u : Fin n → ℤ) : (Fin n → ℤ) →ₗ[ℤ] ℤ where
  toFun z := ∑ i, u i * z i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_left_comm]

@[simp] theorem dotLinear_apply {n : ℕ} (u z : Fin n → ℤ) :
    dotLinear u z = ∑ i, u i * z i := rfl

theorem isPrimitive_of_minimal_gauge {n : ℕ} (z : Fin n → ℤ)
    (hz : z ≠ 0) (μ : (Fin n → ℤ) → ℝ)
    (hμpos : ∀ x ≠ 0, 0 < μ x)
    (hμhom : ∀ (c : ℤ), 0 < c → ∀ x, μ (c • x) = (c : ℝ) * μ x)
    (hmin : ∀ x ≠ 0, μ z ≤ μ x) :
    Erdos3.BohrLattice.Primitive.IsPrimitive z := by
  let c : ℤ := Erdos3.BohrLattice.Primitive.content z
  have hc0 : 0 ≤ c := by
    have hn := Finset.normalize_gcd (s := Finset.univ) (f := z)
    have habs : |c| = c := by
      rw [Int.abs_eq_normalize]
      exact hn
    rw [← habs]
    exact abs_nonneg c
  have hcne : c ≠ 0 := Erdos3.BohrLattice.Primitive.content_ne_zero hz
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hcne)
  suffices hc : c = 1 by
    apply Erdos3.BohrLattice.Primitive.isPrimitive_of_content_eq_one
    exact hc
  by_contra hc
  have hc2 : (2 : ℤ) ≤ c := by omega
  let z' : Fin n → ℤ := Erdos3.BohrLattice.Primitive.divideContent z
  have hz' : z' ≠ 0 := Erdos3.BohrLattice.Primitive.divideContent_ne_zero hz
  have hz_eq : z = c • z' := by
    funext i
    exact (Erdos3.BohrLattice.Primitive.content_mul_divideContent z i).symm
  have hscale : μ z = (c : ℝ) * μ z' := by
    rw [hz_eq]
    exact hμhom c hcpos z'
  have hle : μ z ≤ μ z' := hmin z' hz'
  have hz'pos : 0 < μ z' := hμpos z' hz'
  have hc2r : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc2
  rw [hscale] at hle
  nlinarith

theorem exists_basis_zero_eq_of_isPrimitive {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℤ) (hz : Erdos3.BohrLattice.Primitive.IsPrimitive z) :
    ∃ b : Basis (Fin n) ℤ (Fin n → ℤ), b ⟨0, hn⟩ = z := by
  obtain ⟨u, hu⟩ := hz
  let f : (Fin n → ℤ) →ₗ[ℤ] ℤ := dotLinear u
  have hfz : f z = 1 := by
    simpa [f, dotLinear] using hu
  let K : Submodule ℤ (Fin n → ℤ) := LinearMap.ker f
  let kb := K.basisOfPid (Pi.basisFun ℤ (Fin n))
  let k : ℕ := kb.1
  let bK : Basis (Fin k) ℤ K := kb.2
  have hli : ∀ (c : ℤ), ∀ x ∈ K, c • z + x = 0 → c = 0 := by
    intro c x hx hzero
    have hx0 : f x = 0 := by
      exact (LinearMap.mem_ker.mp hx)
    have h : f (c • z + x) = f 0 := congr_arg f hzero
    rw [map_add, map_smul, hfz, hx0, map_zero] at h
    simpa using h
  have hsp : ∀ x : Fin n → ℤ, ∃ c : ℤ, x + c • z ∈ K := by
    intro x
    refine ⟨-f x, ?_⟩
    apply LinearMap.mem_ker.mpr
    rw [map_add, map_smul, hfz]
    simp
  let b' : Basis (Fin (k + 1)) ℤ (Fin n → ℤ) :=
    Basis.mkFinCons z bK hli hsp
  have hb'0 : b' 0 = z := by
    simp [b', Basis.coe_mkFinCons]
  have hkn : k + 1 = n := by
    have hc := Fintype.card_congr (b'.indexEquiv (Pi.basisFun ℤ (Fin n)))
    simpa using hc
  let b : Basis (Fin n) ℤ (Fin n → ℤ) := b'.reindex (finCongr hkn)
  refine ⟨b, ?_⟩
  simp only [b, Basis.reindex_apply]
  have hzero : (finCongr hkn).symm ⟨0, hn⟩ = (0 : Fin (k + 1)) := by
    apply Fin.ext
    rfl
  rw [hzero, hb'0]

def zspanCoordEquiv {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (b : Basis (Fin n) ℝ E) :
    Submodule.span ℤ (Set.range b) ≃ₗ[ℤ] (Fin n → ℤ) :=
  (b.restrictScalars ℤ).repr.trans (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n))

def zspanBasis {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (b : Basis (Fin n) ℝ E) :
    Basis (Fin n) ℤ (Submodule.span ℤ (Set.range b)) :=
  b.restrictScalars ℤ

@[simp] theorem zspanBasis_apply_coe {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (b : Basis (Fin n) ℝ E) (i : Fin n) :
    ((zspanBasis b i : Submodule.span ℤ (Set.range b)) : E) = b i := by
  exact b.restrictScalars_apply ℤ i

@[simp] theorem zspanCoordEquiv_apply {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (b : Basis (Fin n) ℝ E)
    (x : Submodule.span ℤ (Set.range b)) (i : Fin n) :
    zspanCoordEquiv b x i = (b.restrictScalars ℤ).repr x i := by
  rfl

theorem shortest_zspan_vector_primitive_and_extends
    {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ} (hn : 0 < n)
    (b : Basis (Fin n) ℝ E)
    (v : Submodule.span ℤ (Set.range b)) (hv : v ≠ 0)
    (μ : Submodule.span ℤ (Set.range b) → ℝ)
    (hμpos : ∀ x ≠ 0, 0 < μ x)
    (hμhom : ∀ (c : ℤ), 0 < c → ∀ x, μ (c • x) = (c : ℝ) * μ x)
    (hmin : ∀ x ≠ 0, μ v ≤ μ x) :
    Erdos3.BohrLattice.Primitive.IsPrimitive (zspanCoordEquiv b v) ∧
      ∃ B : Basis (Fin n) ℤ (Submodule.span ℤ (Set.range b)),
        B ⟨0, hn⟩ = v := by
  let e := zspanCoordEquiv b
  let z : Fin n → ℤ := e v
  have hz : z ≠ 0 := by
    intro hz0
    apply hv
    apply e.injective
    simpa [z] using hz0
  let ν : (Fin n → ℤ) → ℝ := fun x => μ (e.symm x)
  have hνpos : ∀ x ≠ 0, 0 < ν x := by
    intro x hx
    apply hμpos
    simpa using e.symm.injective.ne hx
  have hνhom : ∀ (c : ℤ), 0 < c → ∀ x, ν (c • x) = (c : ℝ) * ν x := by
    intro c hc x
    dsimp [ν]
    rw [map_smul]
    exact hμhom c hc (e.symm x)
  have hνmin : ∀ x ≠ 0, ν z ≤ ν x := by
    intro x hx
    dsimp [ν, z]
    rw [e.symm_apply_apply]
    apply hmin
    simpa using e.symm.injective.ne hx
  have hzprim : Erdos3.BohrLattice.Primitive.IsPrimitive z :=
    isPrimitive_of_minimal_gauge z hz ν hνpos hνhom hνmin
  refine ⟨hzprim, ?_⟩
  obtain ⟨B, hB⟩ := exists_basis_zero_eq_of_isPrimitive hn z hzprim
  refine ⟨B.map e.symm, ?_⟩
  rw [Basis.map_apply, hB]
  exact e.symm_apply_apply v

end

end Erdos3.BohrLattice.PrimitiveExtension

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitRangeLocalLipschitz
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitzWith_of_unit_range_near_nonzero {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (C L : ℝ≥0) (hzero : ∀ x, 0 ≤ f x) (hone : ∀ x, f x ≤ 1)
    (hnear : ∀ x y, f x ≠ 0 → (C : ℝ) * dist x y < 1 →
      |f x - f y| ≤ (L : ℝ) * dist x y) :
    LipschitzWith (max C L) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  by_cases hclose : (C : ℝ) * dist x y < 1
  · have hxy : |f x - f y| ≤ (L : ℝ) * dist x y := by
      by_cases hx : f x = 0
      · by_cases hy : f y = 0
        · rw [hx, hy, sub_self, abs_zero]
          positivity
        · have h := hnear y x hy (by simpa only [dist_comm] using hclose)
          simpa only [abs_sub_comm, dist_comm] using h
      · exact hnear x y hx hclose
    exact hxy.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right C L) dist_nonneg)
  · have hxy : |f x - f y| ≤ 1 := abs_le.mpr ⟨by linarith [hzero x, hone y], by linarith [hone x, hzero y]⟩
    exact hxy.trans ((le_of_not_gt hclose).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left C L) dist_nonneg))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedBoxLipschitz
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitzWith_of_unit_range_support_box {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) (R L : ℝ≥0)
    (hzero : ∀ x, 0 ≤ f x) (hone : ∀ x, f x ≤ 1)
    (hsupport : ∀ x, f x ≠ 0 → ∀ i, |x i| ≤ R)
    (hlip : LipschitzOnWith L f {x | ∀ i, |x i| ≤ (R : ℝ) + 1}) :
    LipschitzWith (max 1 L) f := by
  have hL : (L : ℝ) ≤ (max 1 L : ℝ≥0) := by exact_mod_cast (le_max_right 1 L)
  have hnear (x y : I → ℝ) (hx : f x ≠ 0) (hxy : dist x y < 1) :
      dist (f x) (f y) ≤ L * dist x y := by
    have hxR : ∀ i, |x i| ≤ (R : ℝ) + 1 := fun i => (hsupport x hx i).trans (by linarith)
    have hyR : ∀ i, |y i| ≤ (R : ℝ) + 1 := by
      intro i
      have hi : |y i - x i| ≤ dist x y := by
        calc
          |y i - x i| ≤ dist y x := by simpa only [Real.dist_eq] using dist_le_pi_dist y x i
          _ = dist x y := dist_comm y x
      calc
        |y i| = |(y i - x i) + x i| := by ring_nf
        _ ≤ |y i - x i| + |x i| := abs_add_le _ _
        _ ≤ (R : ℝ) + 1 := by linarith [hsupport x hx i]
    exact hlip.dist_le_mul x hxR y hyR
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hxy : dist x y < 1
  · by_cases hx : f x = 0
    · by_cases hy : f y = 0
      · rw [hx, hy, dist_self]
        positivity
      · have h := hnear y x hy (by simpa only [dist_comm] using hxy)
        rw [dist_comm (f y) (f x), dist_comm y x] at h
        exact h.trans (mul_le_mul_of_nonneg_right hL dist_nonneg)
    · exact (hnear x y hx hxy).trans (mul_le_mul_of_nonneg_right hL dist_nonneg)
  · have hdist : dist (f x) (f y) ≤ 1 := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hzero x, hzero y, hone x, hone y]
    have hlarge : (1 : ℝ) ≤ dist x y := le_of_not_gt hxy
    have hmax : (1 : ℝ) ≤ (max 1 L : ℝ≥0) := by exact_mod_cast (le_max_left 1 L)
    exact hdist.trans (hlarge.trans (by nlinarith [dist_nonneg (x := x) (y := y)]))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LipschitzLocalLifts
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y E : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [NormedAddCommGroup E]

omit [PseudoMetricSpace X] [PseudoMetricSpace Y] in
theorem reconstruction_norm_le (π : X → Y) (hπ : Function.Surjective π)
    (f : X → E) (F : Y → E) (hF : ∀ x, F (π x) = f x) {B : ℝ}
    (hbound : ∀ x, ‖f x‖ ≤ B) : ∀ y, ‖F y‖ ≤ B := by
  intro y
  obtain ⟨x, rfl⟩ := hπ y
  rw [hF]
  exact hbound x

theorem lipschitz_reconstruction_of_local_lifts (π : X → Y) (hπ : Function.Surjective π)
    (f : X → E) (F : Y → E) (hF : ∀ x, F (π x) = f x)
    (L K B δ : ℝ≥0) (hδ : 0 < δ) (hf : LipschitzWith L f) (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlift : ∀ y z : Y, dist y z < δ →
      ∃ x x' : X, π x = y ∧ π x' = z ∧ dist x x' ≤ K * dist y z) :
    LipschitzWith (max (L * K) (2 * B / δ)) F := by
  have hFbound := reconstruction_norm_le π hπ f F hF hbound
  have hδr : (0 : ℝ) < δ := hδ
  apply LipschitzWith.of_dist_le_mul
  intro y z
  by_cases hyz : dist y z < δ
  · obtain ⟨x, x', hx, hx', hdist⟩ := hlift y z hyz
    rw [← hx, ← hx', hF, hF]
    calc
      dist (f x) (f x') ≤ L * dist x x' := hf.dist_le_mul x x'
      _ ≤ (L : ℝ) * (K * dist (π x) (π x')) := by
        rw [hx, hx']
        exact mul_le_mul_of_nonneg_left hdist L.coe_nonneg
      _ = ((L * K : ℝ≥0) : ℝ) * dist (π x) (π x') := by simp only [NNReal.coe_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left (L * K) (2 * B / δ)) dist_nonneg
  · have hdist : (δ : ℝ) ≤ dist y z := le_of_not_gt hyz
    calc
      dist (F y) (F z) ≤ ‖F y‖ + ‖F z‖ := dist_le_norm_add_norm _ _
      _ ≤ (2 : ℝ) * B := by linarith [hFbound y, hFbound z]
      _ = (2 * (B : ℝ) / δ) * δ := (div_mul_cancel₀ _ hδr.ne').symm
      _ ≤ (2 * (B : ℝ) / δ) * dist y z := mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = ((2 * B / δ : ℝ≥0) : ℝ) * dist y z := by simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right (L * K) (2 * B / δ)) dist_nonneg

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RightCosetEDistance
namespace OAI

section

namespace Erdos3

open scoped ENNReal

variable {G : Type*} [Group G] [PseudoEMetricSpace G]

noncomputable def rightCosetEDist (Γ : Subgroup G) (x y : G) : ℝ≥0∞ :=
  ⨅ γ : Γ, edist x (y * γ)

theorem rightCosetEDist_le (Γ : Subgroup G) (x y : G) :
    rightCosetEDist Γ x y ≤ edist x y := by
  unfold rightCosetEDist
  exact iInf_le_of_le (1 : Γ) (by simp)

@[simp] theorem rightCosetEDist_self (Γ : Subgroup G) (x : G) : rightCosetEDist Γ x x = 0 :=
  le_antisymm ((rightCosetEDist_le Γ x x).trans_eq (edist_self x)) bot_le

variable [IsIsometricSMul Gᵐᵒᵖ G]

theorem rightCosetEDist_comm (Γ : Subgroup G) (x y : G) :
    rightCosetEDist Γ x y = rightCosetEDist Γ y x := by
  have h : ∀ a b : G, rightCosetEDist Γ a b ≤ rightCosetEDist Γ b a := by
    intro a b
    apply le_iInf
    intro γ
    apply (iInf_le (fun δ : Γ => edist a (b * δ)) γ⁻¹).trans_eq
    rw [← edist_mul_right a (b * (γ⁻¹ : Γ)) (γ : G)]
    simp only [Subgroup.coe_inv, inv_mul_cancel_right, edist_comm]
  exact le_antisymm (h x y) (h y x)

omit [IsIsometricSMul Gᵐᵒᵖ G] in
theorem rightCosetEDist_mul_right (Γ : Subgroup G) (x y : G) (δ : Γ) :
    rightCosetEDist Γ x (y * δ) = rightCosetEDist Γ x y := by
  apply le_antisymm
  · apply le_iInf
    intro γ
    apply (iInf_le (fun a : Γ => edist x (y * δ * a)) (δ⁻¹ * γ)).trans_eq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left]
  · apply le_iInf
    intro γ
    apply (iInf_le (fun a : Γ => edist x (y * a)) (δ * γ)).trans_eq
    simp only [Subgroup.coe_mul, mul_assoc]

theorem rightCosetEDist_mul_left (Γ : Subgroup G) (x y : G) (δ : Γ) :
    rightCosetEDist Γ (x * δ) y = rightCosetEDist Γ x y := by
  rw [rightCosetEDist_comm, rightCosetEDist_mul_right, rightCosetEDist_comm]

theorem rightCosetEDist_triangle (Γ : Subgroup G) (x y z : G) :
    rightCosetEDist Γ x z ≤ rightCosetEDist Γ x y + rightCosetEDist Γ y z := by
  apply ENNReal.le_iInf_add_iInf
  intro a b
  apply (iInf_le (fun γ : Γ => edist x (z * γ)) (b * a)).trans
  calc
    edist x (z * ↑(b * a)) ≤ edist x (y * a) + edist (y * a) (z * ↑(b * a)) :=
      edist_triangle _ _ _
    _ = edist x (y * a) + edist y (z * b) := by
      simp only [Subgroup.coe_mul, ← mul_assoc, edist_mul_right]

theorem rightCosetEDist_rel (Γ : Subgroup G) {x x' y y' : G}
    (hx : QuotientGroup.leftRel Γ x x') (hy : QuotientGroup.leftRel Γ y y') :
    rightCosetEDist Γ x y = rightCosetEDist Γ x' y' := by
  let a : Γ := ⟨x⁻¹ * x', QuotientGroup.leftRel_apply.mp hx⟩
  let b : Γ := ⟨y⁻¹ * y', QuotientGroup.leftRel_apply.mp hy⟩
  have ha : x * a = x' := by simp only [a, mul_inv_cancel_left]
  have hb : y * b = y' := by simp only [b, mul_inv_cancel_left]
  rw [← ha, ← hb, rightCosetEDist_mul_left, rightCosetEDist_mul_right]

noncomputable def quotientRightEDist (Γ : Subgroup G) : (G ⧸ Γ) → (G ⧸ Γ) → ℝ≥0∞ :=
  Quotient.lift₂ (rightCosetEDist Γ) (fun _ _ _ _ hx hy => rightCosetEDist_rel Γ hx hy)

@[simp] theorem quotientRightEDist_mk (Γ : Subgroup G) (x y : G) :
    quotientRightEDist Γ (QuotientGroup.mk x) (QuotientGroup.mk y) = rightCosetEDist Γ x y := rfl

@[simp] theorem quotientRightEDist_self (Γ : Subgroup G) (x : G ⧸ Γ) :
    quotientRightEDist Γ x x = 0 :=
  Quotient.inductionOn x (rightCosetEDist_self Γ)

theorem quotientRightEDist_comm (Γ : Subgroup G) (x y : G ⧸ Γ) :
    quotientRightEDist Γ x y = quotientRightEDist Γ y x :=
  Quotient.inductionOn₂ x y (rightCosetEDist_comm Γ)

theorem quotientRightEDist_triangle (Γ : Subgroup G) (x y z : G ⧸ Γ) :
    quotientRightEDist Γ x z ≤ quotientRightEDist Γ x y + quotientRightEDist Γ y z :=
  Quotient.inductionOn₃ x y z (rightCosetEDist_triangle Γ)

theorem quotientRightEDist_mk_le (Γ : Subgroup G) (x y : G) :
    quotientRightEDist Γ (QuotientGroup.mk x) (QuotientGroup.mk y) ≤ edist x y :=
  rightCosetEDist_le Γ x y

omit [PseudoEMetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] in
theorem quotient_mk_mul_mem (Γ : Subgroup G) (x : G) (γ : Γ) :
    (QuotientGroup.mk (x * γ) : G ⧸ Γ) = QuotientGroup.mk x := by
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  simpa only [inv_mul_cancel_left] using γ.property

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieCoordinateSmooth
namespace OAI

section

namespace Erdos3

open Module
open scoped ContDiff

variable {ι X E L : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [LieRing L] [LieAlgebra ℝ L] {n : ℕ∞ω}

theorem lie_coordinate_formula_real (e : Basis ι ℝ L) (a b : L) (k : ι) :
    e.repr ⁅a, b⁆ k =
      ∑ i, ∑ j, e.repr a i * e.repr b j * e.repr ⁅e i, e j⁆ k := by
  classical
  conv_lhs => rw [← e.sum_repr a, ← e.sum_repr b]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem contDiff_lie_coordinates (e : Basis ι ℝ L) (f g : E → L)
    (hf : ∀ i, ContDiff ℝ n (fun x => e.repr (f x) i))
    (hg : ∀ i, ContDiff ℝ n (fun x => e.repr (g x) i)) (k : ι) :
    ContDiff ℝ n (fun x => e.repr ⁅f x, g x⁆ k) := by
  have heq : (fun x => e.repr ⁅f x, g x⁆ k) =
      (fun x => ∑ i, ∑ j, e.repr (f x) i * e.repr (g x) j * e.repr ⁅e i, e j⁆ k) :=
    funext (fun x => lie_coordinate_formula_real e (f x) (g x) k)
  rw [heq]
  exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    ((hf i).mul (hg j)).mul contDiff_const))

variable [LieAlgebra ℚ L]

theorem contDiff_rightBracketList_coordinates (e : Basis ι ℝ L) (f : X → E → L)
    (hf : ∀ x i, ContDiff ℝ n (fun y => e.repr (f x y) i)) (xs : List X)
    (a : E → L) (ha : ∀ i, ContDiff ℝ n (fun y => e.repr (a y) i)) (k : ι) :
    ContDiff ℝ n (fun y => e.repr (rightBracketList (fun x => f x y) xs (a y)) k) := by
  induction xs generalizing a with
  | nil => exact ha k
  | cons x xs ih =>
    exact ih (fun y => ⁅a y, f x y⁆) (contDiff_lie_coordinates e a (f x) ha (hf x))

theorem contDiff_dynkinWord_coordinates (e : Basis ι ℝ L) (f : X → E → L)
    (hf : ∀ x i, ContDiff ℝ n (fun y => e.repr (f x y) i))
    (w : FreeSemigroup X) (k : ι) :
    ContDiff ℝ n (fun y => e.repr (dynkinWord (fun x => f x y) w) k) :=
  contDiff_rightBracketList_coordinates e f hf w.tail (f w.head) (hf w.head) k

variable [IsScalarTower ℚ ℝ L]

theorem contDiff_lieBCH_coordinates (e : Basis ι ℝ L) (s : ℕ) (f g : E → L)
    (hf : ∀ i, ContDiff ℝ n (fun x => e.repr (f x) i))
    (hg : ∀ i, ContDiff ℝ n (fun x => e.repr (g x) i)) (k : ι) :
    ContDiff ℝ n (fun x => e.repr (lieBCH s (f x) (g x)) k) := by
  change ContDiff ℝ n (fun x => e.coord k (lieBCH s (f x) (g x)))
  simp only [lieBCH_bracket_formula, map_sum, LinearMap.map_smul_of_tower,
    Algebra.smul_def, Basis.coord_apply]
  apply ContDiff.sum
  intro w _
  apply contDiff_const.mul
  exact contDiff_dynkinWord_coordinates e (fun i x => ![f x, g x] i)
    (by intro i k; fin_cases i; exact hf k; exact hg k) w k

theorem contDiff_coordinateBCH (e : Basis ι ℝ L) (s : ℕ) :
    ContDiff ℝ n (fun z : (ι → ℝ) × (ι → ℝ) =>
      e.equivFun (lieBCH s (e.equivFun.symm z.1) (e.equivFun.symm z.2))) := by
  apply contDiff_pi.mpr
  intro k
  apply contDiff_lieBCH_coordinates e s
  · intro i
    change ContDiff ℝ n (fun z : (ι → ℝ) × (ι → ℝ) =>
      e.equivFun (e.equivFun.symm z.1) i)
    simp only [LinearEquiv.apply_symm_apply]
    exact (contDiff_apply ℝ ℝ i).comp contDiff_fst
  · intro i
    change ContDiff ℝ n (fun z : (ι → ℝ) × (ι → ℝ) =>
      e.equivFun (e.equivFun.symm z.2) i)
    simp only [LinearEquiv.apply_symm_apply]
    exact (contDiff_apply ℝ ℝ i).comp contDiff_snd

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieFiniteProduct
namespace OAI

section

namespace Erdos3

open Module

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]

instance lieRingPi : LieRing (∀ a, M a) where
  bracket x y a := ⁅x a, y a⁆
  add_lie x y z := by funext a; exact add_lie _ _ _
  lie_add x y z := by funext a; exact lie_add _ _ _
  lie_self x := by funext a; exact lie_self _
  leibniz_lie x y z := by funext a; exact leibniz_lie _ _ _

@[simp] theorem lie_pi_apply (x y : ∀ a, M a) (a : α) : ⁅x, y⁆ a = ⁅x a, y a⁆ := rfl

variable {R : Type*} [CommRing R] [∀ a, LieAlgebra R (M a)]

instance lieAlgebraPi : LieAlgebra R (∀ a, M a) where
  lie_smul r x y := by funext a; exact lie_smul _ _ _

def liePiEval (a : α) : (∀ a, M a) →ₗ⁅R⁆ M a where
  toLinearMap := LinearMap.proj a
  map_lie' := rfl

@[simp] theorem liePiEval_apply (a : α) (x : ∀ a, M a) : liePiEval (R := R) a x = x a := rfl

variable {L : Type*} [LieRing L] [LieAlgebra R L]

def liePiMap (φ : ∀ a, L →ₗ⁅R⁆ M a) : L →ₗ⁅R⁆ (∀ a, M a) where
  toLinearMap := LinearMap.pi (fun a => (φ a).toLinearMap)
  map_lie' {x y} := by funext a; exact (φ a).map_lie x y

@[simp] theorem liePiMap_apply (φ : ∀ a, L →ₗ⁅R⁆ M a) (x : L) (a : α) :
    liePiMap φ x a = φ a x := rfl

namespace NilpotentLieFiltration

variable [∀ a, LieAlgebra ℚ (M a)] {s : ℕ}

def pi (F : ∀ a, NilpotentLieFiltration (M a) s) : NilpotentLieFiltration (∀ a, M a) s where
  layer n := Submodule.pi Set.univ (fun a => (F a).layer n)
  antitone _ _ h := Submodule.pi_mono (fun a _ => (F a).antitone h)
  one_eq_top := by simp only [one_eq_top, Submodule.pi_top]
  lie_mem {i j x y} hx hy a ha := (F a).lie_mem (hx a ha) (hy a ha)
  terminal := by simp only [terminal, Submodule.pi_univ_bot]

@[simp] theorem mem_pi_layer (F : ∀ a, NilpotentLieFiltration (M a) s) (n : ℕ) (x : ∀ a, M a) :
    x ∈ (pi F).layer n ↔ ∀ a, x a ∈ (F a).layer n := by simp [pi, Submodule.mem_pi]

end NilpotentLieFiltration

section Coordinates

variable [Fintype α] {κ : α → Type*} [∀ a, Fintype (κ a)]
  [∀ a, LieAlgebra ℚ (M a)]

omit [∀ a, Fintype (κ a)] in

theorem lie_pi_structure_height (f : ∀ a, Basis (κ a) ℚ (M a)) {H : ℕ} (hH : 1 ≤ H)
    (hf : ∀ a i j k, RationalHeightLE (lieStructureConstants (f a) i j k) H) :
    ∀ i j k, RationalHeightLE (lieStructureConstants (Pi.basis f) i j k) H := by
  classical
  rintro ⟨a, i⟩ ⟨b, j⟩ ⟨c, k⟩
  unfold lieStructureConstants
  rw [Pi.basis_repr, lie_pi_apply, Pi.basis_apply, Pi.basis_apply]
  by_cases hac : a = c
  · subst c
    rw [Pi.single_eq_same]
    by_cases hba : b = a
    · subst b
      rw [Pi.single_eq_same]
      exact hf a i j k
    · rw [Pi.single_eq_of_ne (Ne.symm hba), lie_zero, map_zero, Finsupp.zero_apply]
      exact rationalHeightLE_zero hH
  · rw [Pi.single_eq_of_ne (Ne.symm hac), zero_lie, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero hH

variable [LieAlgebra ℚ L] {ι : Type*} [Fintype ι]

end Coordinates
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedSupportDropRename
namespace OAI

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def weightedSupportDrop (w : σ → ℕ) (n r : ℕ) : Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R {a | Finsupp.weight w a + r ≤ n}

theorem mem_weightedSupportDrop_iff (w : σ → ℕ) (n r : ℕ) (P : MvPolynomial σ R) :
    P ∈ weightedSupportDrop w n r ↔ ∀ a ∈ P.support, Finsupp.weight w a + r ≤ n := Iff.rfl

theorem weightedSupportDrop_zero (w : σ → ℕ) (n : ℕ) :
    weightedSupportDrop (R := R) w n 0 = weightedSupportLE w n := by
  ext P
  simp only [mem_weightedSupportDrop_iff, Nat.add_zero]
  rfl

theorem weightedSupportDrop_one (w : σ → ℕ) (n : ℕ) :
    weightedSupportDrop (R := R) w n 1 = weightedSupportLT w n := by
  ext P
  simp only [mem_weightedSupportDrop_iff, Nat.add_one_le_iff]
  rfl

theorem weightedSupportDrop_antitone {w : σ → ℕ} {n r s : ℕ} {P : MvPolynomial σ R}
    (hrs : r ≤ s) (hP : P ∈ weightedSupportDrop w n s) : P ∈ weightedSupportDrop w n r := by
  intro a ha
  change Finsupp.weight w a + r ≤ n
  exact (Nat.add_le_add_left hrs _).trans (hP ha)

theorem weightedSupportDrop_le {w : σ → ℕ} {n r : ℕ} {P : MvPolynomial σ R}
    (hP : P ∈ weightedSupportDrop w n r) : P ∈ weightedSupportLE w n := by
  rw [← weightedSupportDrop_zero]
  exact weightedSupportDrop_antitone (Nat.zero_le _) hP

theorem weightedSupportDrop_eq_zero {w : σ → ℕ} {n r : ℕ} {P : MvPolynomial σ R}
    (hnr : n < r) (hP : P ∈ weightedSupportDrop w n r) : P = 0 := by
  apply MvPolynomial.eq_zero_iff.mpr
  intro a
  by_contra ha
  have h : Finsupp.weight w a + r ≤ n := hP (MvPolynomial.mem_support_iff.mpr ha)
  omega

theorem weightedSupportDrop_mul {w : σ → ℕ} {d e r s : ℕ} {P Q : MvPolynomial σ R}
    (hP : P ∈ weightedSupportDrop w d r) (hQ : Q ∈ weightedSupportDrop w e s) :
    P * Q ∈ weightedSupportDrop w (d + e) (r + s) := by
  classical
  intro a ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q ha)
  have h1 : Finsupp.weight w b + r ≤ d := hP hb
  have h2 : Finsupp.weight w c + s ≤ e := hQ hc
  change Finsupp.weight w (b + c) + (r + s) ≤ d + e
  rw [map_add]
  omega

theorem weightedSupportDrop_mul_LE {w : σ → ℕ} {d e r : ℕ} {P Q : MvPolynomial σ R}
    (hP : P ∈ weightedSupportDrop w d r) (hQ : Q ∈ weightedSupportLE w e) :
    P * Q ∈ weightedSupportDrop w (d + e) r := by
  rw [← weightedSupportDrop_zero] at hQ
  simpa only [Nat.add_zero] using weightedSupportDrop_mul hP hQ

theorem weightedSupportLE_mul_drop {w : σ → ℕ} {d e r : ℕ} {P Q : MvPolynomial σ R}
    (hP : P ∈ weightedSupportLE w d) (hQ : Q ∈ weightedSupportDrop w e r) :
    P * Q ∈ weightedSupportDrop w (d + e) r := by
  rw [mul_comm, Nat.add_comm d e]
  exact weightedSupportDrop_mul_LE hQ hP

end Erdos3

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem weightedSupportDrop_rename {w : σ → ℕ} {v : τ → ℕ}
    (f : σ → τ) (hf : ∀ i, v (f i) = w i)
    {n r : ℕ} {P : MvPolynomial σ R}
    (hP : P ∈ weightedSupportDrop w n r) :
    rename f P ∈ weightedSupportDrop v n r := by
  classical
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
  have hweight : Finsupp.weight v (Finsupp.mapDomain f b) = Finsupp.weight w b := by
    change Finsupp.linearCombination ℕ v (Finsupp.mapDomain f b) =
      Finsupp.linearCombination ℕ w b
    rw [Finsupp.linearCombination_mapDomain]
    congr 2
    exact funext hf
  change Finsupp.weight v (Finsupp.mapDomain f b) + r ≤ n
  rw [hweight]
  exact hP hb

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPrimitive
namespace OAI

section

namespace Erdos3

open Polynomial

variable {A : Type*} [CommRing A] [Algebra ℚ A]

noncomputable def polynomialPrimitive (p : Polynomial A) : Polynomial A :=
  p.sum fun n a => monomial (n + 1) (((n + 1 : ℕ) : ℚ)⁻¹ • a)

@[simp] theorem polynomialPrimitive_derivative (p : Polynomial A) :
    (polynomialPrimitive p).derivative = p := by
  classical
  have hcoef (n : ℕ) (a : A) :
      (((n + 1 : ℕ) : ℚ)⁻¹ • a) * ((n : A) + 1) = a := by
    rw [← Nat.cast_add_one, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
    rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), one_smul]
  simp only [polynomialPrimitive, sum_def, derivative_sum, derivative_monomial_succ, hcoef]
  exact sum_monomial_eq p

@[simp] theorem polynomialPrimitive_eval_zero (p : Polynomial A) :
    (polynomialPrimitive p).eval 0 = 0 := by
  classical
  simp only [polynomialPrimitive, sum_def, eval_finsetSum, eval_monomial]
  simp

omit [Algebra ℚ A] in
theorem polynomial_eq_of_derivative_of_eval_zero [IsAddTorsionFree A]
    {p q : Polynomial A} (hderiv : p.derivative = q.derivative)
    (hzero : p.eval 0 = q.eval 0) : p = q := by
  have hd : (p - q).derivative = 0 := by rw [derivative_sub, hderiv, sub_self]
  have hconst := eq_C_of_derivative_eq_zero hd
  have hz : (p - q).coeff 0 = 0 := by
    simpa only [← coeff_zero_eq_eval_zero, coeff_sub, sub_eq_zero] using hzero
  rw [hz, map_zero] at hconst
  exact sub_eq_zero.mp hconst

theorem polynomialPrimitive_unique [IsAddTorsionFree A]
    {p q : Polynomial A} (hderiv : q.derivative = p) (hzero : q.eval 0 = 0) :
    polynomialPrimitive p = q := by
  apply polynomial_eq_of_derivative_of_eval_zero
  · simpa using hderiv.symm
  · simpa using hzero.symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PowerSubgroup
namespace OAI

section

namespace Erdos3

variable {G : Type*} [Group G]

def powerSubgroup (G : Type*) [Group G] (m : ℕ) : Subgroup G :=
  Subgroup.closure (Set.range (fun g : G => g ^ m))

theorem pow_mem_powerSubgroup (g : G) (m : ℕ) : g ^ m ∈ powerSubgroup G m :=
  Subgroup.subset_closure ⟨g, rfl⟩

theorem powerSubgroup_map_le (f : G →* G) (m : ℕ) :
    (powerSubgroup G m).map f ≤ powerSubgroup G m := by
  rw [Subgroup.map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨g, rfl⟩
  change f (g ^ m) ∈ powerSubgroup G m
  rw [map_pow]
  exact pow_mem_powerSubgroup _ _

instance powerSubgroup_characteristic (m : ℕ) : (powerSubgroup G m).Characteristic :=
  Subgroup.characteristic_iff_map_le.mpr (fun f => powerSubgroup_map_le f.toMonoidHom m)

def subgroupPowerCover (Γ : Subgroup G) (m : ℕ) : Subgroup G :=
  (powerSubgroup Γ m).map Γ.subtype

theorem subgroupPowerCover_le (Γ : Subgroup G) (m : ℕ) : subgroupPowerCover Γ m ≤ Γ := by
  rintro _ ⟨g, _, rfl⟩
  exact g.property

theorem pow_mem_subgroupPowerCover (Γ : Subgroup G) {g : G} (hg : g ∈ Γ) (m : ℕ) :
    g ^ m ∈ subgroupPowerCover Γ m :=
  Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : Γ) ^ m, pow_mem_powerSubgroup _ _, rfl⟩

theorem subgroupPowerCover_le_iff (Γ Λ : Subgroup G) (m : ℕ) :
    subgroupPowerCover Γ m ≤ Λ ↔ ∀ g ∈ Γ, g ^ m ∈ Λ := by
  constructor
  · intro h g hg
    exact h (pow_mem_subgroupPowerCover Γ hg m)
  · intro h
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨g, rfl⟩
    exact h g g.property

theorem subgroupPowerCover_subgroupOf (Γ : Subgroup G) (m : ℕ) :
    (subgroupPowerCover Γ m).subgroupOf Γ = powerSubgroup Γ m := by
  change ((powerSubgroup Γ m).map Γ.subtype).comap Γ.subtype = _
  exact Subgroup.comap_map_eq_self_of_injective (f := Γ.subtype) Subtype.val_injective _

instance subgroupPowerCover_characteristic (Γ : Subgroup G) (m : ℕ) :
    ((subgroupPowerCover Γ m).subgroupOf Γ).Characteristic := by
  rw [subgroupPowerCover_subgroupOf]
  infer_instance

instance subgroupPowerCover_normal (Γ : Subgroup G) (m : ℕ) :
    ((subgroupPowerCover Γ m).subgroupOf Γ).Normal := inferInstance

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ConjugationCoordinates
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

def conjugationInput {ι : Type*} (a b : ι → ℚ) : Fin 3 × ι → ℚ :=
  fun ji => ![a ji.2, b ji.2, -a ji.2] ji.1

theorem conjugationInput_mem_denominatorGrid {ι : Type*} (a b : ι → ℚ) (q : ℕ)
    (ha : a ∈ denominatorGrid q) (hb : b ∈ denominatorGrid q) :
    conjugationInput a b ∈ denominatorGrid q := by
  obtain ⟨za, hza⟩ := ha
  obtain ⟨zb, hzb⟩ := hb
  refine ⟨fun ji => ![za ji.2, zb ji.2, -za ji.2] ji.1, ?_⟩
  rintro ⟨j, i⟩
  have hai : (q : ℚ) * a i = (za i : ℚ) := hza i
  have hbi : (q : ℚ) * b i = (zb i : ℚ) := hzb i
  fin_cases j <;> simp [conjugationInput, Pi.smul_apply, smul_eq_mul, hai, hbi]

theorem scaledIntegerGrid_mem_denominatorGrid {ι : Type*} (m q : ℕ) {b : ι → ℚ}
    (hb : b ∈ scaledIntegerGrid m) : b ∈ denominatorGrid q := by
  obtain ⟨z, rfl⟩ := hb
  refine ⟨fun i => (q : ℤ) * m * z i, ?_⟩
  intro i
  simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem conjugationInput_sub_mem_scaledGrid {ι : Type*} (a b : ι → ℚ) (m : ℕ)
    (hb : b ∈ scaledIntegerGrid m) :
    conjugationInput a b - conjugationInput a 0 ∈ scaledIntegerGrid m := by
  obtain ⟨z, hz⟩ := hb
  refine ⟨fun ji => ![0, z ji.2, 0] ji.1, ?_⟩
  funext ⟨j, i⟩
  have hi := congrFun hz i
  change b i = (m : ℚ) * (z i : ℚ) at hi
  fin_cases j <;> simp [conjugationInput, Pi.smul_apply, smul_eq_mul, hi]

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def conjugationCoordinatePolynomial (e : Basis ι ℚ L) (s : ℕ) (i : ι) :
    MvPolynomial (Fin 3 × ι) ℚ :=
  bchProductCoordinatePolynomial (lieStructureConstants e) s [0, 1, 2] i

theorem conjugationCoordinatePolynomial_degree (e : Basis ι ℚ L) (s : ℕ) (i : ι) :
    (conjugationCoordinatePolynomial e s i).totalDegree ≤ s :=
  bchProductCoordinatePolynomial_totalDegree _ _ _ _

theorem conjugationCoordinatePolynomial_eval (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (z g : NilpotentLieBCHGroup L s hnil) (i : ι) :
    eval (conjugationInput (e.equivFun z.coord) (e.equivFun g.coord))
      (conjugationCoordinatePolynomial e s i) = e.repr (z * g * z⁻¹).coord i := by
  let f : Fin 3 → NilpotentLieBCHGroup L s hnil := ![z, g, z⁻¹]
  have he := bchProductCoordinatePolynomial_eval e s hnil (fun j => (f j).coord) [0, 1, 2] i
  have hp := lieBCHList_group_prod s hnil (fun j => (f j).coord) [0, 1, 2]
  rw [← hp] at he
  have hmap : ([0, 1, 2].map (fun j => (⟨(f j).coord⟩ : NilpotentLieBCHGroup L s hnil))) =
      [z, g, z⁻¹] := by simp [f]; rfl
  rw [hmap] at he
  simp only [List.prod_cons, List.prod_nil, mul_one] at he
  have hi : (fun ji : Fin 3 × ι => e.repr (f ji.1).coord ji.2) =
      conjugationInput (e.equivFun z.coord) (e.equivFun g.coord) := by
    funext ⟨j, k⟩
    fin_cases j <;> simp [f, conjugationInput]
  change eval (fun ji : Fin 3 × ι => e.repr (f ji.1).coord ji.2)
    (conjugationCoordinatePolynomial e s i) = _ at he
  rw [hi] at he
  simpa only [mul_assoc] using he

theorem conjugationCoordinatePolynomial_zero (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (z : NilpotentLieBCHGroup L s hnil) (i : ι) :
    eval (conjugationInput (e.equivFun z.coord) 0) (conjugationCoordinatePolynomial e s i) = 0 := by
  simpa using conjugationCoordinatePolynomial_eval e hnil z 1 i

theorem conjugation_preserves_inner_grid (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (q l : ℕ) (hq : 0 < q)
    (z g : NilpotentLieBCHGroup L s hnil)
    (hz : e.equivFun z.coord ∈ denominatorGrid q)
    (hg : e.equivFun g.coord ∈ scaledIntegerGrid
      (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * q ^ s)) :
    e.equivFun (z * g * z⁻¹).coord ∈ scaledIntegerGrid l := by
  have hb := scaledIntegerGrid_mem_denominatorGrid _ q hg
  have hzero : (0 : ι → ℚ) ∈ denominatorGrid q := ⟨0, by simp⟩
  have h := rational_polynomial_family_eval_sub_mem_grid
    (conjugationCoordinatePolynomial e s) q s l hq (conjugationCoordinatePolynomial_degree e s)
    (conjugationInput (e.equivFun z.coord) (e.equivFun g.coord))
    (conjugationInput (e.equivFun z.coord) 0)
    (conjugationInput_mem_denominatorGrid _ _ q hz hb)
    (conjugationInput_mem_denominatorGrid _ _ q hz hzero)
    (conjugationInput_sub_mem_scaledGrid _ _ _ hg)
  simpa only [conjugationCoordinatePolynomial_eval, conjugationCoordinatePolynomial_zero,
    sub_zero, ← Basis.equivFun_apply] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealifiedTripleCoordinates
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

def tripleNeutral : (L × L × L) →ₗ[ℚ] L where
  toFun x := x.2.1 + x.2.2 - x.1
  map_add' x y := by dsimp; abel
  map_smul' r x := by simp [smul_add, smul_sub]

def tripleLeft : (L × L × L) →ₗ[ℚ] L where
  toFun x := x.1 - x.2.2
  map_add' x y := by dsimp; abel
  map_smul' r x := by simp [smul_sub]

def tripleRight : (L × L × L) →ₗ[ℚ] L where
  toFun x := x.1 - x.2.1
  map_add' x y := by dsimp; abel
  map_smul' r x := by simp [smul_sub]

def tripleAssemble (a b c : L) : L × L × L := (a + b + c, a + b, a + c)

@[simp] theorem tripleNeutral_assemble (a b c : L) : tripleNeutral (tripleAssemble a b c) = a := by
  change a + b + (a + c) - (a + b + c) = a
  abel

@[simp] theorem tripleLeft_assemble (a b c : L) : tripleLeft (tripleAssemble a b c) = b := by
  change a + b + c - (a + c) = b
  abel

@[simp] theorem tripleRight_assemble (a b c : L) : tripleRight (tripleAssemble a b c) = c := by
  change a + b + c - (a + b) = c
  abel

theorem tripleAssemble_decompose (x : L × L × L) :
    tripleAssemble (tripleNeutral x) (tripleLeft x) (tripleRight x) = x := by
  apply Prod.ext
  · change (x.2.1 + x.2.2 - x.1) + (x.1 - x.2.2) + (x.1 - x.2.1) = x.1
    abel
  · apply Prod.ext
    · change (x.2.1 + x.2.2 - x.1) + (x.1 - x.2.2) = x.2.1
      abel
    · change (x.2.1 + x.2.2 - x.1) + (x.1 - x.2.1) = x.2.2
      abel

omit [LieAlgebra ℚ L] in
theorem tripleAssemble_lie (a b c a' b' c' : L)
    (hbb : ⁅b, b'⁆ = 0) (hbc : ⁅b, c'⁆ = 0)
    (hcb : ⁅c, b'⁆ = 0) (hcc : ⁅c, c'⁆ = 0) :
    ⁅tripleAssemble a b c, tripleAssemble a' b' c'⁆ =
      tripleAssemble ⁅a, a'⁆ (⁅a, b'⁆ + ⁅b, a'⁆) (⁅a, c'⁆ + ⁅c, a'⁆) := by
  apply Prod.ext
  · change ⁅a + b + c, a' + b' + c'⁆ = _
    simp only [LieRing.add_lie, LieRing.lie_add, hbb, hbc, hcb, hcc, add_zero]
    change _ = ⁅a, a'⁆ + (⁅a, b'⁆ + ⁅b, a'⁆) + (⁅a, c'⁆ + ⁅c, a'⁆)
    abel
  · apply Prod.ext
    · change ⁅a + b, a' + b'⁆ = ⁅a, a'⁆ + (⁅a, b'⁆ + ⁅b, a'⁆)
      simp only [LieRing.add_lie, LieRing.lie_add, hbb, add_zero]
      abel
    · change ⁅a + c, a' + c'⁆ = ⁅a, a'⁆ + (⁅a, c'⁆ + ⁅c, a'⁆)
      simp only [LieRing.add_lie, LieRing.lie_add, hcc, add_zero]
      abel

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def realTripleEquiv :
    (ℝ ⊗[ℚ] (L × L × L)) ≃ₗ[ℝ] ((ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) :=
  (TensorProduct.prodRight ℚ ℝ ℝ L (L × L)).trans
    ((LinearEquiv.refl ℝ (ℝ ⊗[ℚ] L)).prodCongr (TensorProduct.prodRight ℚ ℝ ℝ L L))

@[simp] theorem realTripleEquiv_tmul (r : ℝ) (x : L × L × L) :
    realTripleEquiv (r ⊗ₜ[ℚ] x) = (r ⊗ₜ[ℚ] x.1, r ⊗ₜ[ℚ] x.2.1, r ⊗ₜ[ℚ] x.2.2) := rfl

theorem realTripleEquiv_neutral (x : ℝ ⊗[ℚ] (L × L × L)) :
    tripleNeutral (realTripleEquiv x) =
      (tripleNeutral : (L × L × L) →ₗ[ℚ] L).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realTripleEquiv_tmul, LinearMap.baseChange_tmul]
    change r ⊗ₜ[ℚ] x.2.1 + r ⊗ₜ[ℚ] x.2.2 - r ⊗ₜ[ℚ] x.1 =
      r ⊗ₜ[ℚ] (x.2.1 + x.2.2 - x.1)
    rw [TensorProduct.tmul_sub, TensorProduct.tmul_add]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realTripleEquiv_left (x : ℝ ⊗[ℚ] (L × L × L)) :
    tripleLeft (realTripleEquiv x) =
      (tripleLeft : (L × L × L) →ₗ[ℚ] L).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realTripleEquiv_tmul, LinearMap.baseChange_tmul]
    change r ⊗ₜ[ℚ] x.1 - r ⊗ₜ[ℚ] x.2.2 = r ⊗ₜ[ℚ] (x.1 - x.2.2)
    rw [TensorProduct.tmul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realTripleEquiv_right (x : ℝ ⊗[ℚ] (L × L × L)) :
    tripleRight (realTripleEquiv x) =
      (tripleRight : (L × L × L) →ₗ[ℚ] L).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realTripleEquiv_tmul, LinearMap.baseChange_tmul]
    change r ⊗ₜ[ℚ] x.1 - r ⊗ₜ[ℚ] x.2.1 = r ⊗ₜ[ℚ] (x.1 - x.2.1)
    rw [TensorProduct.tmul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RescaledLieBasis
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℝ L]

noncomputable def inverseScaledBasis (e : Basis ι ℝ L) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) : Basis ι ℝ L :=
  e.unitsSMul (fun i => (Units.mk0 (d i) (hd i).ne')⁻¹)

theorem inverseScaledBasis_apply (e : Basis ι ℝ L) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (i : ι) :
    inverseScaledBasis e d hd i = (d i)⁻¹ • e i := by
  simp only [inverseScaledBasis, Basis.unitsSMul_apply, Units.smul_def,
    Units.val_inv_eq_inv_val, Units.val_mk0]

theorem inverseScaledBasis_repr (e : Basis ι ℝ L) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (x : L) (i : ι) :
    (inverseScaledBasis e d hd).repr x i = d i * e.repr x i := by
  simp only [inverseScaledBasis, Basis.repr_unitsSMul, inv_inv,
    Units.smul_def, Units.val_mk0, smul_eq_mul]

theorem inverseScaledBasis_bracket (e : Basis ι ℝ L) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i)
    (hcompat : ∀ i j k, e.repr ⁅e i, e j⁆ k ≠ 0 → d k = d i * d j)
    (i j k : ι) :
    (inverseScaledBasis e d hd).repr
      ⁅inverseScaledBasis e d hd i, inverseScaledBasis e d hd j⁆ k =
        e.repr ⁅e i, e j⁆ k := by
  rw [inverseScaledBasis_repr, inverseScaledBasis_apply, inverseScaledBasis_apply]
  simp only [smul_lie, lie_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases h : e.repr ⁅e i, e j⁆ k = 0
  · simp only [h, mul_zero]
  · rw [hcompat i j k h]
    field_simp [(hd i).ne', (hd j).ne']

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.HomogenizingMonomial
namespace OAI

section

namespace Erdos3

noncomputable def homogenizingMonomial {I R : Type*} [CommRing R]
    (h : ℕ) (d : I →₀ ℕ) : MvPolynomial (Option I) R :=
  MvPolynomial.X none ^ (h - d.degree) *
    MvPolynomial.rename some (MvPolynomial.monomial d 1)

noncomputable def dehomogenizingSubstitution {I R : Type*} [CommRing R] : Option I → MvPolynomial I R
  | none => 1
  | some i => MvPolynomial.X i

theorem homogenizingMonomial_homogeneous {I R : Type*} [CommRing R]
    (h : ℕ) (d : I →₀ ℕ) (hd : d.degree ≤ h) :
    (homogenizingMonomial (R := R) h d).IsHomogeneous h := by
  have hh := (MvPolynomial.isHomogeneous_X_pow (R := R) (none : Option I) (h - d.degree)).mul
    ((MvPolynomial.isHomogeneous_monomial (1 : R) (rfl : d.degree = d.degree)).rename_isHomogeneous
      (f := some))
  simpa only [homogenizingMonomial, Nat.sub_add_cancel hd] using hh

theorem homogenizingMonomial_dehomogenize {I R : Type*} [CommRing R]
    (h : ℕ) (d : I →₀ ℕ) :
    MvPolynomial.aeval (dehomogenizingSubstitution (R := R)) (homogenizingMonomial (R := R) h d) =
      MvPolynomial.monomial d (1 : R) := by
  simp only [homogenizingMonomial, map_mul, map_pow, MvPolynomial.aeval_X,
    dehomogenizingSubstitution, one_pow, one_mul, MvPolynomial.aeval_rename]
  exact MvPolynomial.aeval_X_left_apply _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexNormalizationError
namespace OAI

section

namespace Erdos3

theorem complex_normalization_error {M F : ℂ} {Z E ε D : ℝ}
    (hZ : 1 / 2 ≤ Z) (herror : ‖M - F‖ ≤ E)
    (hmass : |Z - 1| ≤ ε) (hcap : ‖F‖ ≤ D) :
    ‖M / (Z : ℂ) - F‖ ≤ 2 * E + 2 * D * ε := by
  have hZpos : 0 < Z := by linarith
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZpos.ne'
  have hE : 0 ≤ E := (norm_nonneg _).trans herror
  have hε : 0 ≤ ε := (abs_nonneg _).trans hmass
  have hD : 0 ≤ D := (norm_nonneg _).trans hcap
  have he : M / (Z : ℂ) - F = ((M - F) + F * (1 - (Z : ℂ))) / (Z : ℂ) := by
    field_simp
    ring
  rw [he, norm_div, Complex.norm_real, Real.norm_of_nonneg hZpos.le]
  have hz : ‖1 - (Z : ℂ)‖ ≤ ε := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [abs_sub_comm] using hmass
  have hn : ‖(M - F) + F * (1 - (Z : ℂ))‖ ≤ E + D * ε :=
    (norm_add_le _ _).trans (add_le_add herror (by
      rw [norm_mul]
      exact mul_le_mul hcap hz (norm_nonneg _) hD))
  calc
    _ ≤ (E + D * ε) / Z := div_le_div_of_nonneg_right hn hZpos.le
    _ ≤ 2 * E + 2 * D * ε := (div_le_iff₀ hZpos).mpr (by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * Z - 1) (by positivity : 0 ≤ E + D * ε)])

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedSpatialAmplitudeShift
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem rectangularLatticePoint_add_displacement {I : Type*} [Fintype I]
    (a S : I → ℝ) (x v : I → ℤ) :
    rectangularLatticePoint a S (x + v) - rectangularLatticePoint a S x =
      rectangularLatticePoint 0 S v := by
  funext i
  simp only [rectangularLatticePoint, Pi.sub_apply, Pi.add_apply, Pi.zero_apply,
    Int.cast_add]
  ring

theorem normalizedSpatialAmplitude_shift_le {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] (F : (I → ℝ) → E) {L : ℝ≥0}
    (hF : LipschitzWith L F) (a S : I → ℝ) (x v : I → ℤ) :
    ‖F (rectangularLatticePoint a S (x + v)) - F (rectangularLatticePoint a S x)‖ ≤
      L * ‖rectangularLatticePoint 0 S v‖ := by
  have h := hF.norm_sub_le (rectangularLatticePoint a S (x + v))
    (rectangularLatticePoint a S x)
  rwa [rectangularLatticePoint_add_displacement] at h

theorem normalizedSpatialAmplitude_shift_le_of_norm_le {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] (F : (I → ℝ) → E) {L : ℝ≥0}
    (hF : LipschitzWith L F) (a S : I → ℝ) (x v : I → ℤ)
    {r : ℝ} (hv : ‖rectangularLatticePoint 0 S v‖ ≤ r) :
    ‖F (rectangularLatticePoint a S (x + v)) - F (rectangularLatticePoint a S x)‖ ≤
      L * r :=
  (normalizedSpatialAmplitude_shift_le F hF a S x v).trans
    (mul_le_mul_of_nonneg_left hv L.coe_nonneg)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerTriangularMinor
namespace OAI

section

namespace Erdos3

theorem exists_nonzero_row_minor {K ι : Type*} [Field K] [Fintype ι] {k : ℕ}
    (A : Matrix ι (Fin k) K) (hA : LinearIndependent K A.col) :
    ∃ p : Fin k → ι, (A.submatrix p id).det ≠ 0 := by
  classical
  have ht : LinearIndependent K A.transpose.row := hA
  have hr : Module.finrank K (Submodule.span K (Set.range A.row)) = k := by
    rw [← A.rank_eq_finrank_span_row, ← Matrix.rank_transpose]
    simpa only [Fintype.card_fin] using ht.rank_matrix
  have hex := Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.row)
  rw [hr] at hex
  obtain ⟨v, hv, _, hli⟩ := hex
  choose p hp using hv
  have he : (A.submatrix p id).row = v := by
    funext i
    exact hp i
  have hind : LinearIndependent K (A.submatrix p id).row := he.symm ▸ hli
  exact ⟨p, ((A.submatrix p id).isUnit_iff_isUnit_det.mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hind)).ne_zero⟩

theorem nonzero_row_minor_injective {K ι : Type*} [Field K] {k : ℕ}
    (A : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : (A.submatrix p id).det ≠ 0) :
    Function.Injective p := by
  have h := Matrix.linearIndependent_rows_of_det_ne_zero hp
  intro i j hij
  apply h.injective
  change A (p i) = A (p j)
  rw [hij]

end Erdos3

end

section

namespace Erdos3

theorem exists_minimal_row_minor {K : Type*} [Field K] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) K) (hA : LinearIndependent K A.col) :
    ∃ p : Fin k → Fin m, (A.submatrix p id).det ≠ 0 ∧
      ∀ q : Fin k → Fin m, (A.submatrix q id).det ≠ 0 →
        (∑ j, (p j).val) ≤ ∑ j, (q j).val := by
  classical
  let S := Finset.univ.filter (fun p : Fin k → Fin m => (A.submatrix p id).det ≠ 0)
  obtain ⟨p, hp⟩ := exists_nonzero_row_minor A hA
  have hS : S.Nonempty := ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
  obtain ⟨q, hq, hmin⟩ := S.exists_min_image (fun p => ∑ j, (p j).val) hS
  exact ⟨q, (Finset.mem_filter.mp hq).2,
    fun p hp => hmin p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)⟩

theorem row_minor_update_det {K ι : Type*} [Field K] {k : ℕ}
    (A : Matrix ι (Fin k) K) (p : Fin k → ι)
    (C : Matrix ι (Fin k) K) (hC : C * A.submatrix p id = A)
    (i : ι) (j : Fin k) :
    (A.submatrix (Function.update p j i) id).det = C i j * (A.submatrix p id).det := by
  have he : A.submatrix (Function.update p j i) id =
      (A.submatrix p id).updateRow j (fun b => A i b) := by
    ext a b
    by_cases h : a = j
    · subst a
      simp only [Matrix.submatrix_apply, Function.update_self, id_eq, Matrix.updateRow_apply,
        ite_true]
    · simp only [Matrix.submatrix_apply, Function.update_of_ne h, id_eq, Matrix.updateRow_apply,
        if_neg h]
  have hr : (fun b => A i b) = ∑ a, C i a • (A.submatrix p id) a := by
    funext b
    simpa only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] using (congrArg (fun M : Matrix ι (Fin k) K => M i b) hC).symm
  rw [he, hr]
  simpa only [smul_eq_mul] using
    Matrix.det_updateRow_sum (A.submatrix p id) j (fun a => C i a)

theorem minimal_row_minor_coordinate_zero {K : Type*} [Field K] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) K) (p : Fin k → Fin m)
    (hp : (A.submatrix p id).det ≠ 0)
    (hmin : ∀ q : Fin k → Fin m, (A.submatrix q id).det ≠ 0 →
      (∑ j, (p j).val) ≤ ∑ j, (q j).val)
    (C : Matrix (Fin m) (Fin k) K) (hC : C * A.submatrix p id = A)
    (i : Fin m) (j : Fin k) (hij : i < p j) : C i j = 0 := by
  classical
  by_contra hne
  have hdet : (A.submatrix (Function.update p j i) id).det ≠ 0 := by
    rw [row_minor_update_det A p C hC i j]
    exact mul_ne_zero hne hp
  have hle := hmin (Function.update p j i) hdet
  have hfun : (fun a => (Function.update p j i a).val) =
      Function.update (fun a => (p a).val) j i.val := by
    funext a
    by_cases h : a = j <;> simp [h]
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ j)] at hle
  have hsum : (∑ a, (p a).val) =
      (p j).val + ∑ a ∈ Finset.univ \ {j}, (p a).val := by
    simpa only [Function.update_eq_self] using
      (Finset.sum_update_of_mem (Finset.mem_univ j) (fun a => (p a).val) (p j).val)
  rw [hsum] at hle
  exact (not_le_of_gt hij) (Nat.le_of_add_le_add_right hle)

end Erdos3

end

section

namespace Erdos3

theorem det_eq_one_of_triangular_labels {K ι α : Type*} [CommRing K]
    [Fintype ι] [DecidableEq ι] [LinearOrder α]
    (B : Matrix ι ι K) (p : ι → α) (hp : Function.Injective p)
    (htri : ∀ i j, p i < p j → B i j = 0) (hdiag : ∀ i, B i i = 1) : B.det = 1 := by
  let : LinearOrder ι := LinearOrder.lift' p hp
  have hB : B.IsLowerTriangular := fun {i j} hij => htri i j hij
  rw [Matrix.det_of_isLowerTriangular B hB]
  simp only [hdiag, Finset.prod_const_one]

theorem lower_unitriangular_preserves_minimal_minor
    {K : Type*} [Field K] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) K) (p : Fin k → Fin m)
    (hp : (A.submatrix p id).det ≠ 0)
    (hmin : ∀ q : Fin k → Fin m, (A.submatrix q id).det ≠ 0 →
      (∑ j, (p j).val) ≤ ∑ j, (q j).val)
    (M : Matrix (Fin m) (Fin m) K)
    (hM : ∀ i j, i < j → M i j = 0) (hdiag : ∀ i, M i i = 1) :
    ((M * A).submatrix p id).det = (A.submatrix p id).det := by
  classical
  let B := A.submatrix p id
  let C := A * B⁻¹
  have hB : IsUnit B.det := isUnit_iff_ne_zero.mpr hp
  have hC : C * B = A := Matrix.nonsing_inv_mul_cancel_right B A hB
  have hCp : C.submatrix p id = 1 := by
    change (A * B⁻¹).submatrix p id = 1
    rw [Matrix.submatrix_mul A B⁻¹ p id id Function.bijective_id, Matrix.submatrix_id_id]
    exact Matrix.mul_nonsing_inv B hB
  have hzero (a : Fin m) (j : Fin k) (haj : a < p j) : C a j = 0 :=
    minimal_row_minor_coordinate_zero A p hp hmin C hC a j haj
  let T := (M * C).submatrix p id
  have hTtri (i j : Fin k) (hij : p i < p j) : T i j = 0 := by
    change ∑ a, M (p i) a * C a j = 0
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : a ≤ p i
    · rw [hzero a j (lt_of_le_of_lt ha hij), mul_zero]
    · rw [hM (p i) a (lt_of_not_ge ha), zero_mul]
  have hTdiag (i : Fin k) : T i i = 1 := by
    change ∑ a, M (p i) a * C a i = 1
    rw [Finset.sum_eq_single (p i)]
    · have hc : C (p i) i = 1 := by
        simpa using congrArg (fun N : Matrix (Fin k) (Fin k) K => N i i) hCp
      rw [hdiag, hc, one_mul]
    · intro a _ hne
      by_cases ha : a < p i
      · rw [hzero a i ha, mul_zero]
      · have hi : p i < a := lt_of_le_of_ne (le_of_not_gt ha) (Ne.symm hne)
        rw [hM (p i) a hi, zero_mul]
    · simp
  have hT : T.det = 1 := det_eq_one_of_triangular_labels T p
    (nonzero_row_minor_injective A p hp) hTtri hTdiag
  have he : (M * A).submatrix p id = T * B := by
    rw [← hC, ← Matrix.mul_assoc]
    exact Matrix.submatrix_mul (M * C) B p id id Function.bijective_id
  rw [he, Matrix.det_mul, hT, one_mul]

theorem exists_preserved_nonzero_row_minor
    {K : Type*} [Field K] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) K) (hA : LinearIndependent K A.col) :
    ∃ p : Fin k → Fin m, Function.Injective p ∧ (A.submatrix p id).det ≠ 0 ∧
      ∀ M : Matrix (Fin m) (Fin m) K,
        (∀ i j, i < j → M i j = 0) → (∀ i, M i i = 1) →
        ((M * A).submatrix p id).det = (A.submatrix p id).det := by
  obtain ⟨p, hp, hmin⟩ := exists_minimal_row_minor A hA
  exact ⟨p, nonzero_row_minor_injective A p hp, hp,
    fun M hM hdiag => lower_unitriangular_preserves_minimal_minor A p hp hmin M hM hdiag⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxCertificate
namespace OAI

section

namespace Erdos3.BohrLattice.BoxCertificate

open scoped BigOperators

def realBox {n : ℕ} (r : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.Icc (-r) r

structure SuccessiveProductCertificate {n : ℕ} (Λ : AddSubgroup (Fin n → ℝ))
    (r : Fin n → ℝ) (B : ℝ) where
  scale : Fin n → ℝ
  point : Fin n → Fin n → ℝ
  scale_nonneg : ∀ i, 0 ≤ scale i
  point_mem : ∀ i, point i ∈ Λ
  independent : LinearIndependent ℝ point
  mem_scaledBox : ∀ i, point i ∈ realBox (scale i • r)
  product_le : ∏ i, scale i ≤ B

end Erdos3.BohrLattice.BoxCertificate

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OrthogonalSection
namespace OAI

section

namespace Erdos3

theorem exists_orthogonal_section
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] (π : E →ₗ[ℝ] F) (hπ : Function.Surjective π) :
    ∃ L : F →ₗ[ℝ] E, (∀ y, π (L y) = y) ∧
      ∀ x, L (π x) = x - (LinearMap.ker π).starProjection x := by
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  have hret : ∀ y, π (s y) = y := fun y => LinearMap.congr_fun hs y
  let K := LinearMap.ker π
  let L : F →ₗ[ℝ] E := (LinearMap.id - K.starProjection.toLinearMap).comp s
  have hL (y : F) : L y = s y - K.starProjection (s y) := rfl
  have hzero (x : E) : π (K.starProjection x) = 0 := K.starProjection_apply_mem x
  have hright (y : F) : π (L y) = y := by rw [hL, map_sub, hret, hzero, sub_zero]
  have horth (y : F) : L y ∈ Kᗮ :=
    Submodule.sub_starProjection_mem_orthogonal (s y)
  refine ⟨L, hright, ?_⟩
  intro x
  let w := x - K.starProjection x
  have hw : w ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hpw : π w = π x := by change π (x - K.starProjection x) = π x; rw [map_sub, hzero, sub_zero]
  have hk : L (π x) - w ∈ K := by
    change π (L (π x) - w) = 0
    rw [map_sub, hright, hpw, sub_self]
  have ho : L (π x) - w ∈ Kᗮ := Kᗮ.sub_mem (horth _) hw
  have hz : inner ℝ (L (π x) - w) (L (π x) - w) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hk ho
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FiniteLatticeBasis
namespace OAI

section

namespace Erdos3

noncomputable def finiteLatticeBasis {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    Module.Basis (Fin (Module.finrank ℝ E)) ℤ Λ :=
  (Module.Free.chooseBasis ℤ Λ).reindex (Fintype.equivOfCardEq
    (by rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ, Fintype.card_fin]))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityIntegralBound
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem density_mul_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (D : X → ℝ) (hD : Integrable D μ) (f : X → ℂ)
    (hf : AEStronglyMeasurable f μ) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    Integrable (fun x => (D x : ℂ) * f x) μ :=
  hD.ofReal.mul_bdd hf (ae_of_all μ hbound)

theorem norm_density_integral_le_one {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (D : X → ℝ) (hD : Integrable D μ) (hD0 : ∀ x, 0 ≤ D x)
    (hDmass : (∫ x, D x ∂μ) = 1) (f : X → ℂ) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    ‖∫ x, (D x : ℂ) * f x ∂μ‖ ≤ 1 := by
  rw [← hDmass]
  apply norm_integral_le_of_norm_le hD
  apply ae_of_all
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hD0 x)]
  exact mul_le_of_le_one_right (hD0 x) (hbound x)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConvexEmpiricalApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_le_linear_of_mem_convexHull
    {E : Type*} [AddCommMonoid E] [Module ℝ E] {S : Set E} {z : E}
    (hz : z ∈ convexHull ℝ S) (f : E →ₗ[ℝ] ℝ) :
    ∃ q ∈ S, f q ≤ f z := by
  by_contra h
  push Not at h
  have hz' := (convexHull_min h (convex_halfSpace_gt f.isLinear (f z))) hz
  exact (lt_irrefl (f z)) hz'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem empirical_step_sq_le (u z q : E) {R : ℝ}
    (hchoice : inner ℝ (u - z) q ≤ inner ℝ (u - z) z) (hq : ‖q‖ ≤ R) :
    ‖u + (q - z)‖ ^ 2 ≤ ‖u‖ ^ 2 + R ^ 2 := by
  have hqsq := pow_le_pow_left₀ (norm_nonneg q) hq 2
  simp only [inner_sub_left, real_inner_self_eq_norm_sq] at hchoice
  rw [← real_inner_comm z q] at hchoice
  rw [norm_add_sq_real, norm_sub_sq_real, inner_sub_right]
  nlinarith only [hchoice, hqsq, sq_nonneg ‖z‖]

theorem exists_convex_empirical_sum {S : Set E} {z : E}
    (hz : z ∈ convexHull ℝ S) {R : ℝ} (hS : ∀ q ∈ S, ‖q‖ ≤ R) (n : ℕ) :
    ∃ q : Fin n → E, (∀ i, q i ∈ S) ∧
      ‖(∑ i, q i) - (n : ℝ) • z‖ ^ 2 ≤ (n : ℝ) * R ^ 2 := by
  induction n with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | succ n ih =>
    obtain ⟨q, hq, hsum⟩ := ih
    let u := (∑ i, q i) - (n : ℝ) • z
    obtain ⟨x, hx, hchoice⟩ := exists_le_linear_of_mem_convexHull hz
      (innerSL ℝ (u - z)).toLinearMap
    refine ⟨Fin.cons x q, ?_, ?_⟩
    · exact Fin.forall_fin_succ.mpr ⟨hx, hq⟩
    · have hid : (∑ i : Fin (n + 1), Fin.cons x q i) - ((n + 1 : ℕ) : ℝ) • z =
          u + (x - z) := by
        simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Nat.cast_add,
          Nat.cast_one, add_smul, one_smul]
        dsimp only [u]
        abel
      rw [hid]
      have hstep := empirical_step_sq_le u z x hchoice (hS x hx)
      change ‖u‖ ^ 2 ≤ (n : ℝ) * R ^ 2 at hsum
      push_cast
      nlinarith only [hsum, hstep]

theorem exists_convex_empirical_average {S : Set E} {z : E}
    (hz : z ∈ convexHull ℝ S) {R : ℝ} (hS : ∀ q ∈ S, ‖q‖ ≤ R)
    (n : ℕ) (hn : 0 < n) :
    ∃ q : Fin n → E, (∀ i, q i ∈ S) ∧
      ‖(n : ℝ)⁻¹ • (∑ i, q i) - z‖ ^ 2 ≤ R ^ 2 / n := by
  obtain ⟨q, hq, hsum⟩ := exists_convex_empirical_sum hz hS n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨q, hq, ?_⟩
  have hid : (n : ℝ)⁻¹ • ((∑ i, q i) - (n : ℝ) • z) =
      (n : ℝ)⁻¹ • (∑ i, q i) - z := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hnR.ne', one_smul]
  rw [← hid, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnR.le), mul_pow]
  apply (mul_le_mul_of_nonneg_left hsum (sq_nonneg ((n : ℝ)⁻¹))).trans_eq
  field_simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ProductSliceAxisDensity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem piFinset_axis_subset {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
    (A B : ∀ i, Finset (X i)) (hA : ∀ i, (A i).Nonempty)
    (hsub : Fintype.piFinset A ⊆ Fintype.piFinset B) (i : I) : A i ⊆ B i := by
  have hi := Finset.image_subset_image (f := fun x : ∀ i, X i => x i) hsub
  rw [Fintype.eval_image_piFinset A i (fun j _ => hA j)] at hi
  exact hi.trans (Fintype.eval_image_piFinset_subset B i)

theorem piFinset_card_ratio_le_axis {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
    (A B : ∀ i, Finset (X i)) (hA : ∀ i, (A i).Nonempty) (hB : ∀ i, (B i).Nonempty)
    (hsub : Fintype.piFinset A ⊆ Fintype.piFinset B) (i : I) :
    ((Fintype.piFinset A).card : ℝ) / (Fintype.piFinset B).card ≤
      ((A i).card : ℝ) / (B i).card := by
  let r : I → ℝ := fun j => ((A j).card : ℝ) / (B j).card
  have hr (j : I) : 0 ≤ r j ∧ r j ≤ 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
    apply (div_le_one (by exact_mod_cast (hB j).card_pos : (0 : ℝ) < (B j).card)).mpr
    exact_mod_cast Finset.card_le_card (piFinset_axis_subset A B hA hsub j)
  have he : ((Fintype.piFinset A).card : ℝ) / (Fintype.piFinset B).card = ∏ j, r j := by
    simp only [Fintype.card_piFinset, Nat.cast_prod, Finset.prod_div_distrib, r]
  rw [he, ← Finset.mul_prod_erase Finset.univ r (Finset.mem_univ i)]
  exact mul_le_of_le_one_right (hr i).1 (Finset.prod_le_one (fun j _ => (hr j).1) (fun j _ => (hr j).2))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealDirectionExtension
namespace OAI

section

namespace Erdos3

variable {σ E : Type*} [Fintype σ] [AddCommGroup E] [Module ℚ E] [Module ℝ E]

noncomputable def realDirectionExtension (f : (σ → ℚ) →ₗ[ℚ] E) : (σ → ℝ) →ₗ[ℝ] E := by
  classical
  exact ∑ i, (LinearMap.proj i).smulRight (f (Pi.single i 1))

open scoped Classical in
theorem realDirectionExtension_apply (f : (σ → ℚ) →ₗ[ℚ] E) (h : σ → ℝ) :
    realDirectionExtension f h = ∑ i, h i • f (Pi.single i 1) := by
  classical
  simp only [realDirectionExtension, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply]

theorem realDirectionExtension_rat (f : (σ → ℚ) →ₗ[ℚ] E) (h : σ → ℚ) :
    realDirectionExtension f (fun i => (h i : ℝ)) = f h := by
  classical
  rw [realDirectionExtension_apply]
  have he : h = ∑ i, h i • Pi.single i (1 : ℚ) := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  exact ratCast_smul_eq ℝ ℚ (h i) _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SubmoduleQuotientCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ V : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ]
  (b : Basis ι ℚ V) (U : Submodule ℚ V) (D : Matrix κ ι ℚ)
  (hker : LinearMap.ker D.mulVecLin = U.map b.equivFun.toLinearMap)
  (hsurj : Function.Surjective D.mulVec)

noncomputable def submoduleQuotientCoordinateEquiv : (V ⧸ U) ≃ₗ[ℚ] (κ → ℚ) :=
  (Submodule.Quotient.equiv U (U.map b.equivFun.toLinearMap) b.equivFun rfl).trans
    (rationalQuotientEquiv D _ hker hsurj)

omit [Fintype κ] in
theorem submoduleQuotientCoordinateEquiv_mk (x : V) :
    submoduleQuotientCoordinateEquiv b U D hker hsurj (U.mkQ x) = D *ᵥ b.equivFun x :=
  rationalQuotientEquiv_apply_mk D _ hker hsurj _

noncomputable def submoduleQuotientCoordinateBasis : Basis κ ℚ (V ⧸ U) :=
  Basis.ofEquivFun (submoduleQuotientCoordinateEquiv b U D hker hsurj)

theorem submoduleQuotientCoordinateBasis_matrix [DecidableEq ι] [DecidableEq κ] :
    LinearMap.toMatrix b (submoduleQuotientCoordinateBasis b U D hker hsurj) U.mkQ = D := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply, submoduleQuotientCoordinateBasis, Basis.ofEquivFun_repr_apply]
  change (submoduleQuotientCoordinateEquiv b U D hker hsurj (U.mkQ (b j))) i = _
  rw [submoduleQuotientCoordinateEquiv_mk]
  simp [Basis.equivFun_self, Matrix.mulVec, dotProduct]

theorem submoduleQuotientCoordinateEquiv_symm [DecidableEq κ]
    (S : Matrix ι κ ℚ) (hS : D * S = 1) (y : κ → ℚ) :
    (submoduleQuotientCoordinateEquiv b U D hker hsurj).symm y = U.mkQ (b.equivFun.symm (S *ᵥ y)) := by
  apply (submoduleQuotientCoordinateEquiv b U D hker hsurj).injective
  rw [LinearEquiv.apply_symm_apply, submoduleQuotientCoordinateEquiv_mk,
    LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MonotoneRegularPoint
namespace OAI

section

namespace Erdos3

open _root_.Finset
open scoped BigOperators

theorem exists_regular_point_of_monotone
    (f : ℝ → ℝ) (hf : Monotone f)
    (hgrowth : f (5 / 4) - f (1 / 4) < 5) :
    ∃ x ∈ Set.Icc (1 / 2 : ℝ) 1,
      ∀ y ∈ Set.Icc (1 / 4 : ℝ) (5 / 4),
        |f y - f x| ≤ 60 * |y - x| := by
  classical
  by_contra! hregular
  let Bad : Set (ℝ × ℝ) := {p |
    1 / 4 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 5 / 4 ∧
      60 * (p.2 - p.1) < f p.2 - f p.1}
  let center : (ℝ × ℝ) → ℝ := fun p ↦ (p.1 + p.2) / 2
  let radius : (ℝ × ℝ) → ℝ := fun p ↦ (p.2 - p.1) / 2
  have hradius_pos {p : ℝ × ℝ} (hp : p ∈ Bad) : 0 < radius p := by
    dsimp [Bad] at hp
    dsimp [radius]
    linarith
  have hradius_le (p : ℝ × ℝ) (hp : p ∈ Bad) : radius p ≤ 1 / 2 := by
    dsimp [Bad] at hp
    dsimp [radius]
    linarith
  obtain ⟨u, huBad, huDisjoint, huCover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
      Bad center radius (1 / 2) hradius_le 5 (by norm_num)
  have hcentralCover : Set.Icc (1 / 2 : ℝ) 1 ⊆
      ⋃ b : ↥u, Metric.ball (center b.1) (6 * radius b.1) := by
    intro x hx
    obtain ⟨y, hybuf, hxy⟩ := hregular x hx
    let p : ℝ × ℝ := (min x y, max x y)
    have hpbuf : p ∈ Bad := by
      dsimp [Bad, p]
      have hxbuf : x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4) := by
        constructor <;> linarith [hx.1, hx.2]
      rcases le_total x y with hle | hle
      · simp only [min_eq_left hle, max_eq_right hle]
        have habs : |f y - f x| = f y - f x :=
          abs_of_nonneg (sub_nonneg.mpr (hf hle))
        have hdist : |y - x| = y - x := abs_of_nonneg (sub_nonneg.mpr hle)
        rw [habs, hdist] at hxy
        exact ⟨hxbuf.1, lt_of_not_ge (fun heq ↦ by
          have : y = x := le_antisymm heq hle
          subst y
          norm_num at hxy), hybuf.2, hxy⟩
      · simp only [min_eq_right hle, max_eq_left hle]
        have habs : |f y - f x| = f x - f y := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (sub_nonneg.mpr (hf hle))
        have hdist : |y - x| = x - y := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (sub_nonneg.mpr hle)
        rw [habs, hdist] at hxy
        exact ⟨hybuf.1, lt_of_not_ge (fun heq ↦ by
          have : x = y := le_antisymm heq hle
          subst y
          norm_num at hxy), hxbuf.2, hxy⟩
    obtain ⟨b, hbu, hsub⟩ := huCover p hpbuf
    have hxp : x ∈ Metric.closedBall (center p) (radius p) := by
      rw [Real.closedBall_eq_Icc]
      dsimp [center, radius, p]
      constructor <;> rcases le_total x y with hle | hle <;>
        simp [hle] <;> linarith
    have hxb : x ∈ Metric.closedBall (center b) (5 * radius b) := hsub hxp
    rw [Metric.mem_closedBall] at hxb
    rw [Set.mem_iUnion]
    refine ⟨⟨b, hbu⟩, ?_⟩
    rw [Metric.mem_ball]
    have hbr : 0 < radius b := hradius_pos (huBad hbu)
    linarith
  obtain ⟨v, hvCover⟩ := isCompact_Icc.elim_finite_subcover
    (fun b : ↥u ↦ Metric.ball (center b.1) (6 * radius b.1))
    (fun _ ↦ Metric.isOpen_ball) hcentralCover
  have hv_nonempty : v.Nonempty := by
    by_contra hv
    rw [Finset.not_nonempty_iff_eq_empty] at hv
    simpa [hv] using hvCover (show (1 / 2 : ℝ) ∈ Set.Icc (1 / 2) 1 by norm_num)
  have hvolume : (1 / 2 : ℝ) ≤ 6 * ∑ b ∈ v, (b.1.2 - b.1.1) := by
    have hm : MeasureTheory.volume (Set.Icc (1 / 2 : ℝ) 1) ≤
        MeasureTheory.volume (⋃ b ∈ v,
          Metric.ball (center b.1) (6 * radius b.1)) :=
      MeasureTheory.measure_mono hvCover
    have hright : 0 ≤ 6 * ∑ b ∈ v, (b.1.2 - b.1.1) := by
      apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro b hb
      have := hradius_pos (huBad b.2)
      dsimp [radius] at this
      linarith
    rw [← ENNReal.ofReal_le_ofReal_iff hright]
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) =
        MeasureTheory.volume (Set.Icc (1 / 2 : ℝ) 1) := by
      rw [Real.volume_Icc]
      norm_num
    rw [hhalf]
    calc
      MeasureTheory.volume (Set.Icc (1 / 2 : ℝ) 1) ≤
          MeasureTheory.volume (⋃ b ∈ v,
            Metric.ball (center b.1) (6 * radius b.1)) := hm
      _ ≤ ∑ b ∈ v, MeasureTheory.volume
          (Metric.ball (center b.1) (6 * radius b.1)) :=
        MeasureTheory.measure_biUnion_finset_le v _
      _ = ENNReal.ofReal (6 * ∑ b ∈ v, (b.1.2 - b.1.1)) := by
        simp only [Real.volume_ball]
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          simp only [radius]
          calc
            ∑ b ∈ v, 2 * (6 * ((b.1.2 - b.1.1) / 2)) =
                ∑ b ∈ v, 6 * (b.1.2 - b.1.1) := by
              apply Finset.sum_congr rfl
              intro b hb
              ring
            _ = 6 * ∑ b ∈ v, (b.1.2 - b.1.1) := by
              rw [Finset.mul_sum]
        · intro b hb
          have := hradius_pos (huBad b.2)
          dsimp [radius] at this
          positivity
      _ = ENNReal.ofReal (6 * ∑ b ∈ v, (b.1.2 - b.1.1)) := rfl
  let e : ↥u ↪ (ℝ × ℝ) := ⟨Subtype.val, Subtype.val_injective⟩
  let F : Finset (ℝ × ℝ) := v.map e
  have hball (p : ℝ × ℝ) :
      Metric.closedBall (center p) (radius p) = Set.Icc p.1 p.2 := by
    rw [Real.closedBall_eq_Icc]
    dsimp [center, radius]
    congr <;> ring
  have hF_bounds : ∀ ⦃z⦄, z ∈ F →
      (1 / 4 : ℝ) ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ 5 / 4 := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hz
    have hbad := huBad b.2
    dsimp [Bad] at hbad
    exact ⟨hbad.1, hbad.2.1.le, hbad.2.2.1⟩
  have hF_disjoint : (SetLike.coe F).PairwiseDisjoint
      (fun z ↦ Set.Icc z.1 z.2) := by
    intro z hz w hw hzw
    obtain ⟨bz, hbz, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨bw, hbw, rfl⟩ := Finset.mem_map.mp hw
    have hne : (bz : ℝ × ℝ) ≠ bw := by
      simpa [e] using hzw
    have hd := huDisjoint bz.2 bw.2 hne
    change Disjoint (Metric.closedBall (center bz) (radius bz))
      (Metric.closedBall (center bw) (radius bw)) at hd
    rw [hball, hball] at hd
    simpa [e] using hd
  have hsum_le : ∑ z ∈ F, (f z.2 - f z.1) ≤ f (5 / 4) - f (1 / 4) := by
    have htel := F.sum_intervalGapsWithin_add_sum_eq_sub rfl
      (a := (1 / 4 : ℝ)) (b := (5 / 4 : ℝ)) f
    calc
      ∑ z ∈ F, (f z.2 - f z.1) ≤ _ := by
        rw [le_add_iff_nonneg_left]
        apply Finset.sum_nonneg
        intro i hi
        apply sub_nonneg.mpr
        apply hf
        exact F.intervalGapsWithin_fst_le_snd rfl _ (by norm_num)
          hF_bounds hF_disjoint
      _ = f (5 / 4) - f (1 / 4) := htel
  have hbad_sum : 60 * ∑ b ∈ v, (b.1.2 - b.1.1) <
      ∑ z ∈ F, (f z.2 - f z.1) := by
    rw [Finset.sum_map]
    simp only [e, Function.Embedding.coeFn_mk]
    rw [Finset.mul_sum]
    exact Finset.sum_lt_sum_of_nonempty hv_nonempty
      (fun b hb ↦ (huBad b.2).2.2.2)
  linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AugmentedMatrixSection
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {ι κ μ R : Type*} [CommRing R]

def constraintProjectionMatrix (Q : Matrix ι κ R) (P : Matrix μ κ R) :
    Matrix (ι ⊕ μ) κ R := fun i j => Sum.elim (fun k => Q k j) (fun k => P k j) i

def constraintProjectionInput (y : μ → R) : (ι ⊕ μ) → R := Sum.elim (fun _ => 0) y

theorem mulVec_constraintProjectionInput [Fintype ι] [Fintype μ]
    (S : Matrix κ (ι ⊕ μ) R) (y : μ → R) :
    S *ᵥ constraintProjectionInput (ι := ι) y = (fun i j => S i (Sum.inr j)) *ᵥ y := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, constraintProjectionInput]

theorem constraintProjectionInput_grid [Fintype ι] [Fintype μ]
    (l : ℕ) (y : μ → ℝ) (hy : y ∈ realDenominatorGrid l) :
    constraintProjectionInput (ι := ι) y ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hy
  refine ⟨Sum.elim (fun _ => (0 : ℤ)) z, ?_⟩
  funext i
  cases i with
  | inl i => simp [constraintProjectionInput]
  | inr i => exact congrFun hz i

theorem constraintProjectionInput_weighted {δ : Type*}
    (r : ι → δ) (c : μ → δ) (W : δ → ℝ) (hW : ∀ d, 0 < W d)
    {M : ℝ} (hM : 0 ≤ M) (y : μ → ℝ) (hy : ∀ i, |y i| ≤ M / W (c i)) :
    ∀ i, |constraintProjectionInput (ι := ι) y i| ≤ M / W (Sum.elim r c i) := by
  intro i
  cases i with
  | inl i =>
    change |(0 : ℝ)| ≤ M / W (r i)
    rw [abs_zero]
    exact div_nonneg hM (hW _).le
  | inr i => exact hy i

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MomentEvaluationBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

def momentWeightBound (m : ℕ) : ℕ := (m + 1) * (m * m + 1) ^ m

theorem momentWeightBound_pos (m : ℕ) : 0 < momentWeightBound m := by
  unfold momentWeightBound
  positivity

theorem norm_momentWeight_le {m : ℕ} (z : Fin (m * m + 1)) (j : Fin m) :
    ‖(z.val : ℂ) ^ j.val‖ ≤ ((m * m + 1) ^ m : ℕ) := by
  rw [norm_pow, Complex.norm_natCast]
  have hz : (z.val : ℝ) ≤ (m * m + 1 : ℕ) := by exact_mod_cast (Nat.le_of_lt z.isLt)
  calc
    _ ≤ ((m * m + 1 : ℕ) : ℝ) ^ j.val := pow_le_pow_left₀ (Nat.cast_nonneg _) hz _
    _ ≤ ((m * m + 1 : ℕ) : ℝ) ^ m :=
      pow_le_pow_right₀ (by exact_mod_cast (Nat.le_add_left 1 (m * m))) (Nat.le_of_lt j.isLt)
    _ = _ := by norm_cast

noncomputable def momentLinear {m : ℕ} (v : Fin m → ℂ) (z : Fin (m * m + 1)) : ℂ :=
  ∑ j, v j * (z.val : ℂ) ^ j.val

theorem norm_momentLinear_le {m : ℕ} (v : Fin m → ℂ) (z : Fin (m * m + 1))
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ j, ‖v j‖ ≤ M) :
    ‖momentLinear v z‖ ≤ (momentWeightBound m : ℝ) * M := by
  calc
    _ ≤ ∑ j, ‖v j‖ * ‖(z.val : ℂ) ^ j.val‖ := by
      simpa only [momentLinear, norm_mul] using norm_sum_le (s := Finset.univ)
        (f := fun j => v j * (z.val : ℂ) ^ j.val)
    _ ≤ ∑ _j : Fin m, M * (((m * m + 1) ^ m : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul (hv j) (norm_momentWeight_le z j) (norm_nonneg _) hM)
    _ ≤ (momentWeightBound m : ℝ) * M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, momentWeightBound]
      push_cast
      nlinarith [mul_nonneg hM (pow_nonneg (by positivity : (0 : ℝ) ≤ m * m + 1) m)]

theorem momentLinear_lipschitz {m : ℕ} {X : Type*} [PseudoMetricSpace X]
    (f : Fin m → X → ℂ) {K : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j))
    (z : Fin (m * m + 1)) :
    LipschitzWith ((momentWeightBound m : ℝ≥0) * K) (fun x => momentLinear (fun j => f j x) z) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have heq : momentLinear (fun j => f j x) z - momentLinear (fun j => f j y) z =
      momentLinear (fun j => f j x - f j y) z := by
    simp only [momentLinear, Finset.sum_sub_distrib, sub_mul]
  rw [heq]
  calc
    _ ≤ (momentWeightBound m : ℝ) * ((K : ℝ) * dist x y) :=
      norm_momentLinear_le _ z (by positivity)
        (fun j => by simpa only [dist_eq_norm] using (hf j).dist_le_mul x y)
    _ = _ := by push_cast; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.VerticalDecompositionBudget
namespace OAI

section

namespace Erdos3

def centralActionBudget (p : ℝ) : ℝ := (p + 3) ^ 9 + 2 * p + 2

def verticalDecompositionBudget (p : ℝ) : ℝ :=
  let q := centralActionBudget p
  2 * q * (2 * q + 2) ^ 4 + ((2 * q + 2) ^ 4 + q + (p + 3) ^ 5 + 2) ^ 4

theorem centralActionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) : 0 ≤ centralActionBudget p := by
  unfold centralActionBudget
  positivity

theorem le_centralActionBudget {p : ℝ} (hp : 0 ≤ p) : p ≤ centralActionBudget p := by
  have h : 0 ≤ (p + 3) ^ 9 := by positivity
  unfold centralActionBudget
  linarith

theorem verticalDecompositionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ verticalDecompositionBudget p := by
  unfold verticalDecompositionBudget
  have := centralActionBudget_nonneg hp
  positivity

theorem exists_verticalDecompositionBudget_bound :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → verticalDecompositionBudget p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := (Polynomial.X + 3) ^ 9 + 2 * Polynomial.X + 2
  let P : Polynomial ℕ :=
    2 * Q * (2 * Q + 2) ^ 4 + ((2 * Q + 2) ^ 4 + Q + (Polynomial.X + 3) ^ 5 + 2) ^ 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [P, Q, verticalDecompositionBudget, centralActionBudget,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ExpandingGramSpectrum
namespace OAI

section

namespace Erdos3

open Matrix
open scoped ComplexOrder

theorem one_le_eigenvalues_of_sub_one_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (h : (M - 1).PosSemidef) (i : ι) :
    1 ≤ hM.eigenvalues i := by
  let v := hM.eigenvectorBasis i
  have hv : star (⇑v) ⬝ᵥ ⇑v = (1 : ℝ) := by
    rw [dotProduct_comm]
    change inner ℝ v v = 1
    rw [real_inner_self_eq_norm_sq, hM.eigenvectorBasis.orthonormal.1 i, one_pow]
  have he : star (⇑v) ⬝ᵥ (M *ᵥ ⇑v) = hM.eigenvalues i := by
    simpa only [RCLike.re_to_real] using (hM.eigenvalues_eq i).symm
  have hp := h.dotProduct_mulVec_nonneg (⇑v)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, he, hv] at hp
  linarith

theorem one_le_det_of_sub_one_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (h : (M - 1).PosSemidef) :
    1 ≤ M.det := by
  rw [hM.det_eq_prod_eigenvalues]
  exact Finset.one_le_prod (fun i _ => one_le_eigenvalues_of_sub_one_posSemidef hM h i)

theorem eigenvalues_le_det_of_sub_one_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (h : (M - 1).PosSemidef) (i : ι) :
    hM.eigenvalues i ≤ M.det := by
  rw [hM.det_eq_prod_eigenvalues]
  have heigen := one_le_eigenvalues_of_sub_one_posSemidef hM h
  have hp := Finset.prod_le_prod_of_subset_of_one_le
    (f := hM.eigenvalues) (Finset.subset_univ ({i} : Finset ι))
    (fun j _ => zero_le_one.trans (heigen j)) (fun j _ _ => heigen j)
  simpa only [Finset.prod_singleton, RCLike.ofReal_real_eq_id, id_eq] using hp

theorem det_smul_one_sub_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (h : (M - 1).PosSemidef) :
    (M.det • (1 : Matrix ι ι ℝ) - M).PosSemidef := by
  let U : Matrix ι ι ℝ := hM.eigenvectorUnitary
  have hdiag : (Matrix.diagonal (fun i => M.det - hM.eigenvalues i)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun i =>
      sub_nonneg.mpr (eigenvalues_le_det_of_sub_one_posSemidef hM h i))
  have hd : Matrix.diagonal (fun i => M.det - hM.eigenvalues i) =
      M.det • (1 : Matrix ι ι ℝ) - Matrix.diagonal hM.eigenvalues := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hs : M = U * Matrix.diagonal hM.eigenvalues * U.conjTranspose := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_real_eq_id,
      id_eq, Matrix.star_eq_conjTranspose] using
      hM.spectral_theorem
  have hU : U * U.conjTranspose = 1 := Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hp := hdiag.mul_mul_conjTranspose_same U
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, hU, ← hs] at hp
  exact hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ScaledBasisNorm
namespace OAI

section

namespace Erdos3

theorem divided_basisFun_eq_smul {σ : Type*} [Fintype σ] [DecidableEq σ]
    (T : σ → ℝ) (i : σ) :
    (fun j => (Pi.basisFun ℝ σ i) j / T j) = (1 / T i) • Pi.basisFun ℝ σ i := by
  funext j
  by_cases hij : i = j
  · subst j
    simp
  · simp [Pi.basisFun_apply, Ne.symm hij]

theorem linearMap_divided_basis_norm_le {E σ : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype σ] [DecidableEq σ]
    (G : (σ → ℝ) →ₗ[ℝ] E) (T : σ → ℝ) (i : σ) (hTi : 0 < T i)
    (B : ℝ) (hB : ‖G (Pi.basisFun ℝ σ i)‖ ≤ B) :
    ‖G (fun j => (Pi.basisFun ℝ σ i) j / T j)‖ ≤ B / T i := by
  rw [divided_basisFun_eq_smul, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hTi)]
  calc
    _ ≤ (1 / T i) * B := mul_le_mul_of_nonneg_left hB (one_div_pos.mpr hTi).le
    _ = B / T i := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitIntervalBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def scalarUnitEquiv (A : Type*) : A ≃ (Unit → A) where
  toFun a _ := a
  invFun f := f ()
  left_inv _ := rfl
  right_inv f := by
    funext u
    cases u
    rfl

theorem unitIntervalBox_eq_image (a : ℤ) (len : ℕ) :
    translatedIntegerBox (fun _ : Unit => a) (fun _ => len) =
      (Finset.Ico a (a + len)).image (scalarUnitEquiv ℤ) := by
  ext x
  rw [mem_translatedIntegerBox, Finset.mem_image]
  constructor
  · intro hx
    exact ⟨x (), Finset.mem_Ico.mpr (hx ()), (scalarUnitEquiv ℤ).apply_symm_apply x⟩
  · rintro ⟨n, hn, rfl⟩ u
    exact Finset.mem_Ico.mp hn

theorem unitIntervalBox_expect (a : ℤ) (len : ℕ) (f : (Unit → ℤ) → ℂ) :
    (𝔼 x ∈ translatedIntegerBox (fun _ : Unit => a) (fun _ => len), f x) =
      𝔼 n ∈ Finset.Ico a (a + len), f (fun _ => n) := by
  rw [unitIntervalBox_eq_image]
  exact Finset.expect_image (scalarUnitEquiv ℤ).injective.injOn

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerIntervalOverlap
namespace OAI

section

namespace Erdos3

theorem integerIco_card (c len : ℕ) :
    (Finset.Ico (c : ℤ) (c + len)).card = len := by
  simp

theorem integerIco_subset_range (c len N : ℕ) (hN : c + len ≤ N) :
    Finset.Ico (c : ℤ) (c + len) ⊆ Finset.Ico (0 : ℤ) N := by
  intro x hx
  obtain ⟨hx₀, hx₁⟩ := Finset.mem_Ico.mp hx
  exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

theorem integerIco_intersection (c₁ l₁ c₂ l₂ N : ℕ)
    (hN₁ : c₁ + l₁ ≤ N) (hN₂ : c₂ + l₂ ≤ N)
    (hne : (Finset.Ico (c₁ : ℤ) (c₁ + l₁) ∩ Finset.Ico (c₂ : ℤ) (c₂ + l₂)).Nonempty) :
    ∃ c len : ℕ, 0 < len ∧ c + len ≤ N ∧ len ≤ l₁ ∧ len ≤ l₂ ∧
      Finset.Ico (c₁ : ℤ) (c₁ + l₁) ∩ Finset.Ico (c₂ : ℤ) (c₂ + l₂) =
        Finset.Ico (c : ℤ) (c + len) := by
  let c := max c₁ c₂
  let e := min (c₁ + l₁) (c₂ + l₂)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨hx₁, hx₂⟩ := Finset.mem_inter.mp hx
  obtain ⟨hx₁₀, hx₁₁⟩ := Finset.mem_Ico.mp hx₁
  obtain ⟨hx₂₀, hx₂₁⟩ := Finset.mem_Ico.mp hx₂
  have hce : c < e := by dsimp [c, e]; omega
  have heq : c + (e - c) = e := by omega
  refine ⟨c, e - c, by omega, ?_, ?_, ?_, ?_⟩
  · dsimp [e] at heq
    omega
  · dsimp [c, e]
    omega
  · dsimp [c, e]
    omega
  · ext y
    simp only [Finset.mem_inter, Finset.mem_Ico]
    dsimp [c, e] at *
    omega

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexPolarization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def polarizationPhase : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]

noncomputable def polarizationWeight (k : Fin 4) : ℂ := polarizationPhase k / 4

theorem polarizationPhase_norm (k : Fin 4) : ‖polarizationPhase k‖ = 1 := by
  fin_cases k <;> norm_num [polarizationPhase]

theorem polarizationWeight_norm (k : Fin 4) : ‖polarizationWeight k‖ = (1 : ℝ) / 4 := by
  simp only [polarizationWeight, norm_div, polarizationPhase_norm]
  norm_num

theorem polarizationWeight_cost : (∑ k, ‖polarizationWeight k‖) = 1 := by
  simp only [polarizationWeight_norm, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem complex_mixed_polarization (a b c d : ℂ) :
    a * star d = ∑ k, polarizationWeight k *
      ((a + polarizationPhase k * b) * star (c + polarizationPhase k * d)) := by
  norm_num [Fin.sum_univ_succ, polarizationWeight, polarizationPhase,
    star_add, star_mul, Complex.star_def]
  ring_nf
  norm_num [Complex.I_sq]
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RoundedModelDensityBudget
namespace OAI

section

namespace Erdos3

noncomputable def roundedModelLogBudget (P : ℝ) (d : ℕ) : ℝ :=
  736 + 96 * max P 0 + 1504 * d

theorem roundedModelLogBudget_nonneg (P : ℝ) (d : ℕ) : 0 ≤ roundedModelLogBudget P d := by
  unfold roundedModelLogBudget
  positivity

theorem roundedModelScale_le_exp (P : ℝ) (d : ℕ) :
    (2 ^ 14 : ℝ) * (Real.exp (P + 13 * d)) ^ 6 * 16 ^ (d + 1) ≤
      Real.exp (44 + 6 * max P 0 + 94 * d) := by
  have h2 : (2 ^ 14 : ℝ) ≤ Real.exp 28 := by
    calc
      (2 ^ 14 : ℝ) ≤ (Real.exp 2) ^ 14 :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (2 : ℝ)]) _
      _ = Real.exp 28 := by rw [← Real.exp_nat_mul]; norm_num
  have h16 : (16 : ℝ) ^ (d + 1) ≤ Real.exp (16 * ((d : ℝ) + 1)) := by
    calc
      (16 : ℝ) ^ (d + 1) ≤ (Real.exp 16) ^ (d + 1) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (16 : ℝ)]) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc
    (2 ^ 14 : ℝ) * (Real.exp (P + 13 * d)) ^ 6 * 16 ^ (d + 1) ≤
        Real.exp 28 * (Real.exp (P + 13 * d)) ^ 6 * Real.exp (16 * ((d : ℝ) + 1)) := by
      gcongr
    _ = Real.exp (44 + 6 * P + 94 * d) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      norm_num
      ring
    _ ≤ Real.exp (44 + 6 * max P 0 + 94 * d) := by
      apply Real.exp_le_exp.mpr
      nlinarith [le_max_left P 0]

theorem exp_neg_roundedModelLogBudget_le_density (P : ℝ) (d : ℕ) :
    Real.exp (-roundedModelLogBudget P d) ≤
      (32 * ((2 ^ 14 : ℝ) * (Real.exp (P + 13 * d)) ^ 6 * 16 ^ (d + 1)) ^ 16)⁻¹ := by
  let C := (2 ^ 14 : ℝ) * (Real.exp (P + 13 * d)) ^ 6 * 16 ^ (d + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : 32 * C ^ 16 ≤ Real.exp (roundedModelLogBudget P d) := by
    calc
      32 * C ^ 16 ≤ Real.exp 32 * (Real.exp (44 + 6 * max P 0 + 94 * d)) ^ 16 := by
        gcongr
        · linarith [Real.add_one_le_exp (32 : ℝ)]
        · exact roundedModelScale_le_exp P d
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        unfold roundedModelLogBudget
        norm_num
        ring
  rw [Real.exp_neg]
  exact inv_le_inv₀ (Real.exp_pos _) (by positivity) |>.mpr hbound

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MissingCoordinateProducts
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def missingCoordinateProduct {I K α : Type*} [Fintype I]
    (coordinate : I → K) (f : I → (K → α) → ℂ) (k : K) (x : K → α) : ℂ := by
  classical
  exact ∏ i ∈ Finset.univ with coordinate i = k, f i x

theorem missingCoordinateProduct_prod {I K α : Type*} [Fintype I] [Fintype K]
    (coordinate : I → K) (f : I → (K → α) → ℂ) (x : K → α) :
    (∏ k, missingCoordinateProduct coordinate f k x) = ∏ i, f i x := by
  classical
  exact Finset.prod_fiberwise Finset.univ coordinate (fun i => f i x)

theorem missingCoordinateProduct_norm {I K α : Type*} [Fintype I]
    (coordinate : I → K) (f : I → (K → α) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1)
    (k : K) (x : K → α) : ‖missingCoordinateProduct coordinate f k x‖ ≤ 1 := by
  classical
  unfold missingCoordinateProduct
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hf i x)

theorem missingCoordinateProduct_independent {I K α : Type*} [Fintype I]
    (coordinate : I → K) (f : I → (K → α) → ℂ)
    (hf : ∀ i x y, (∀ k, k ≠ coordinate i → x k = y k) → f i x = f i y)
    (k : K) (x y : K → α) (hxy : ∀ l, l ≠ k → x l = y l) :
    missingCoordinateProduct coordinate f k x = missingCoordinateProduct coordinate f k y := by
  classical
  apply Finset.prod_congr rfl
  intro i hi
  have heq : coordinate i = k := (Finset.mem_filter.mp hi).2
  apply hf i x y
  simpa only [heq] using hxy

theorem exists_missing_coordinate_product_factors {I K α : Type*} [Fintype I] [Fintype K]
    (f : I → (K → α) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1)
    (hind : ∀ i, ∃ k, ∀ x y, (∀ l, l ≠ k → x l = y l) → f i x = f i y) :
    ∃ A : K → (K → α) → ℂ,
      (∀ k x, ‖A k x‖ ≤ 1) ∧
      (∀ k x y, (∀ l, l ≠ k → x l = y l) → A k x = A k y) ∧
      ∀ x, (∏ k, A k x) = ∏ i, f i x := by
  classical
  choose coordinate homit using hind
  exact ⟨missingCoordinateProduct coordinate f, missingCoordinateProduct_norm coordinate f hf,
    missingCoordinateProduct_independent coordinate f homit, missingCoordinateProduct_prod coordinate f⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CrossRowCharacterDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def characterCrossRow (f g : G → ℂ) (χ : G → AddChar G ℂ) (h n : G) : ℂ :=
  (f n * star (g (n + h))) * star (χ h n)

theorem characterCrossRow_norm (f g : G → ℂ) (χ : G → AddChar G ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (h n : G) :
    ‖characterCrossRow f g χ h n‖ ≤ 1 := by
  simp only [characterCrossRow, norm_mul, norm_star, AddChar.norm_apply, mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (hg (n + h))

theorem characterCrossRow_derivative (f g : G → ℂ) (χ : G → AddChar G ℂ) (h k n : G) :
    multiplicativeDerivative (characterCrossRow f g χ h) k n =
      (multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h))) * χ h k := by
  have hcancel : χ h n * star (χ h n) = 1 := by
    change χ h n * (starRingEnd ℂ) (χ h n) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, AddChar.norm_apply]
    norm_num
  have hshift : n + k + h = n + h + k := by abel
  simp only [characterCrossRow, multiplicativeDerivative, star_mul, star_star,
    (χ h).map_add_eq_mul, hshift]
  calc
    _ = (((f n * star (f (n + k))) * (star (g (n + h)) * g (n + h + k))) * χ h k) *
        (χ h n * star (χ h n)) := by ring
    _ = _ := by rw [hcancel, mul_one]; ring

theorem characterCrossRow_derivative_correlation_norm (f g : G → ℂ)
    (χ : G → AddChar G ℂ) (h k : G) (K : G → ℂ) :
    ‖𝔼 n, multiplicativeDerivative (characterCrossRow f g χ h) k n * star (K n)‖ =
      ‖𝔼 n, (multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h))) *
        star (K n)‖ := by
  have heq : (𝔼 n, multiplicativeDerivative (characterCrossRow f g χ h) k n * star (K n)) =
      χ h k * (𝔼 n, (multiplicativeDerivative f k n *
        star (multiplicativeDerivative g k (n + h))) * star (K n)) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro n _
    rw [characterCrossRow_derivative]
    ring
  rw [heq, norm_mul, AddChar.norm_apply, one_mul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRadixCoding
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerRadixValue : {n : ℕ} → (Fin n → ℕ) → (Fin n → ℤ) → ℤ
  | 0, _, _ => 0
  | n + 1, R, x => x 0 + (R 0 : ℤ) * integerRadixValue (fun i : Fin n => R i.succ) (fun i => x i.succ)

theorem integerRadixValue_zero {n : ℕ} (R : Fin n → ℕ) :
    integerRadixValue R 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (0 : ℤ) + (R 0 : ℤ) * integerRadixValue (fun i : Fin n => R i.succ) 0 = 0
      rw [ih, mul_zero, add_zero]

theorem integerRadixValue_add {n : ℕ} (R : Fin n → ℕ) (x y : Fin n → ℤ) :
    integerRadixValue R (x + y) = integerRadixValue R x + integerRadixValue R y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [integerRadixValue, Pi.add_apply]
      rw [show (fun i : Fin n => x i.succ + y i.succ) =
        (fun i => x i.succ) + (fun i => y i.succ) from rfl, ih]
      ring

def integerRadixHom {n : ℕ} (R : Fin n → ℕ) : (Fin n → ℤ) →+ ℤ where
  toFun := integerRadixValue R
  map_zero' := integerRadixValue_zero R
  map_add' := integerRadixValue_add R

theorem integerRadixValue_bounds {n : ℕ} (R : Fin n → ℕ) (x : Fin n → ℤ)
    (hx : ∀ i, 0 ≤ x i ∧ x i < (R i : ℤ)) :
    0 ≤ integerRadixValue R x ∧ integerRadixValue R x < ((∏ i, R i : ℕ) : ℤ) := by
  induction n with
  | zero => simp [integerRadixValue]
  | succ n ih =>
      have h0 := hx 0
      have ht := ih (fun i => R i.succ) (fun i => x i.succ) (fun i => hx i.succ)
      have hm := mul_le_mul_of_nonneg_left
        (show integerRadixValue (fun i : Fin n => R i.succ) (fun i => x i.succ) ≤
          ((∏ i : Fin n, R i.succ : ℕ) : ℤ) - 1 by omega)
        (Nat.cast_nonneg (R 0) : (0 : ℤ) ≤ R 0)
      rw [integerRadixValue, Fin.prod_univ_succ, Nat.cast_mul]
      constructor
      · exact add_nonneg h0.1 (mul_nonneg (Nat.cast_nonneg _) ht.1)
      · nlinarith

theorem integerRadixValue_injective_on_digits {n : ℕ} (R : Fin n → ℕ)
    (x y : Fin n → ℤ) (hx : ∀ i, 0 ≤ x i ∧ x i < (R i : ℤ))
    (hy : ∀ i, 0 ≤ y i ∧ y i < (R i : ℤ))
    (he : integerRadixValue R x = integerRadixValue R y) : x = y := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
      have hx0 := hx 0
      have hy0 := hy 0
      have hR : (R 0 : ℤ) ≠ 0 := ne_of_gt (lt_of_le_of_lt hx0.1 hx0.2)
      have h0 : x 0 = y 0 := by
        have h := congrArg (fun z : ℤ => z % (R 0 : ℤ)) he
        simpa only [integerRadixValue, Int.add_emod, Int.mul_emod, Int.emod_self,
          zero_mul, Int.zero_emod, add_zero, Int.emod_eq_of_lt hx0.1 hx0.2,
          Int.emod_eq_of_lt hy0.1 hy0.2] using h
      have ht : integerRadixValue (fun i : Fin n => R i.succ) (fun i => x i.succ) =
          integerRadixValue (fun i : Fin n => R i.succ) (fun i => y i.succ) := by
        apply mul_left_cancel₀ hR
        simpa only [integerRadixValue, h0, add_left_cancel_iff] using he
      have hh := ih (fun i => R i.succ) (fun i => x i.succ) (fun i => y i.succ)
        (fun i => hx i.succ) (fun i => hy i.succ) ht
      funext i
      exact Fin.cases h0 (fun j => congrFun hh j) i

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeTwistedSliceBudget
namespace OAI

section

namespace Erdos3

theorem nativeTwistedSlice_freezing_error {p L mass : ℝ}
    (hp : 0 ≤ p) (_hL : 0 ≤ L) (hLp : L ≤ Real.exp p)
    (hmass : 0 ≤ mass) (hmass1 : mass ≤ 1) :
    Real.exp p * (2 * L * (Real.exp (-(2 * (2 * p + 2))) / 4) * mass) ≤
      Real.exp (-p) / 4 := by
  have h2 : (2 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp 4
    linarith
  have hsmall : 2 * Real.exp (-4) ≤ 1 := by
    rw [Real.exp_neg]
    exact (mul_inv_le_iff₀ (Real.exp_pos 4)).mpr (by simpa using h2)
  calc
    _ ≤ Real.exp p * (2 * Real.exp p * (Real.exp (-(2 * (2 * p + 2))) / 4) * 1) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLp (by norm_num)) (by positivity)
      · exact hmass1
      · exact hmass
      · positivity
    _ = 2 * Real.exp (-4) * Real.exp (-2 * p) / 4 := by
      rw [mul_one]
      have he : Real.exp p * Real.exp p * Real.exp (-(2 * (2 * p + 2))) =
          Real.exp (-4) * Real.exp (-2 * p) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = 2 * (Real.exp p * Real.exp p * Real.exp (-(2 * (2 * p + 2)))) / 4 := by ring
        _ = _ := by rw [he]; ring
    _ ≤ Real.exp (-p) / 4 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      calc
        _ ≤ 1 * Real.exp (-2 * p) := mul_le_mul_of_nonneg_right hsmall (Real.exp_nonneg _)
        _ ≤ Real.exp (-p) := by rw [one_mul]; exact Real.exp_le_exp.mpr (by linarith)

theorem nativeTwistedSlice_bias_precision (p : ℝ) :
    Real.exp (-(p + 2)) ≤ Real.exp (-p) / 4 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; norm_num at this ⊢; exact this
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 2
    norm_num only [pow_two, mul_comm, ← Real.exp_add] at h
    exact h
  rw [show -(p + 2) = -p - 2 by ring, Real.exp_sub]
  exact div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) hfour

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteRowChartRadiusBudget
namespace OAI

section

namespace Erdos3

noncomputable def finiteRowChartRadius (rows dim : ℕ) (C T : ℝ) : ℝ :=
  1 / (4 * ((rows : ℝ) + 1) * (C + 1) * ((dim : ℝ) + 1) * (T + 1))

theorem finiteRowChartRadius_pos (rows dim : ℕ) {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T) :
    0 < finiteRowChartRadius rows dim C T := by
  unfold finiteRowChartRadius
  positivity

theorem finiteRowChartRadius_budget (rows dim : ℕ) {C T R : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hsmall : R ≤ finiteRowChartRadius rows dim C T) :
    (rows : ℝ) * (C * (((dim : ℝ) + 1) * (T * R))) ≤ 1 / 4 := by
  have hd : 0 < 4 * ((rows : ℝ) + 1) * (C + 1) * ((dim : ℝ) + 1) * (T + 1) := by positivity
  have hr := (le_div_iff₀ hd).mp hsmall
  have hb : (rows : ℝ) * C * ((dim : ℝ) + 1) * T ≤
      ((rows : ℝ) + 1) * (C + 1) * ((dim : ℝ) + 1) * (T + 1) := by gcongr <;> linarith
  have hm := mul_le_mul_of_nonneg_right hb hR
  nlinarith only [hr, hm]

end Erdos3

end

section

namespace Erdos3

theorem finiteRowChartRadius_inv_le_exp (rows dim : ℕ) {C T P : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hP : 0 ≤ P)
    (hr : (rows : ℝ) ≤ Real.exp P) (hd : (dim : ℝ) ≤ Real.exp P)
    (hCP : C ≤ Real.exp P) (hTP : T ≤ Real.exp P) :
    (finiteRowChartRadius rows dim C T)⁻¹ ≤ Real.exp (4 * P + 6) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hunit : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hadd {a : ℝ} (ha : a ≤ Real.exp P) : a + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ 2 * Real.exp P := by linarith
      _ ≤ Real.exp P * Real.exp 1 := by nlinarith [Real.exp_pos P]
      _ = _ := (Real.exp_add _ _).symm
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) htwo 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  simp only [finiteRowChartRadius, one_div, inv_inv]
  calc
    _ ≤ Real.exp 2 * Real.exp (P + 1) * Real.exp (P + 1) * Real.exp (P + 1) * Real.exp (P + 1) := by
      gcongr
      · exact hadd hr
      · exact hadd hCP
      · exact hadd hd
      · exact hadd hTP
    _ = _ := by simp only [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedNormalizedSiteTwist
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.Set
open scoped BigOperators Classical NNReal

def normalizedSiteTwistProduct {X Y : Type*} (f : X → ℂ) (g : Y → ℂ) (v : X × Y) : ℂ :=
  f v.1 * g v.2

theorem normalizedSiteTwistProduct_bounds {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → ℂ) (g : Y → ℂ) {Lf Lg : ℝ≥0}
    (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g)
    (hnf : ∀ x, ‖f x‖ ≤ 1) (hng : ∀ y, ‖g y‖ ≤ 1) :
    (∀ v, ‖normalizedSiteTwistProduct f g v‖ ≤ 1) ∧
      LipschitzWith (Lf + Lg) (normalizedSiteTwistProduct f g) := by
  have h1 : LipschitzWith Lf (fun v : X × Y => f v.1) := by
    simpa only [mul_one, Function.comp_def] using hf.comp LipschitzWith.prod_fst
  have h2 : LipschitzWith Lg (fun v : X × Y => g v.2) := by
    simpa only [mul_one, Function.comp_def] using hg.comp LipschitzWith.prod_snd
  refine ⟨?_, ?_⟩
  · intro v
    rw [normalizedSiteTwistProduct, norm_mul]
    exact (mul_le_mul (hnf _) (hng _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · have h := lipschitz_mul_of_bounds _ _ h1 h2 (Bf := 1) (Bg := 1)
      (fun v => hnf v.1) (fun v => hng v.2)
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa only [normalizedSiteTwistProduct, one_mul, add_comm] using h.dist_le_mul v w

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {A α : Type*}
  [Fintype A]
  [Fintype α]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (r : ℝ≥0)
  (hr : 0 < r)
  (s : Finset α)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d]
variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j a, coefficients (p j) a ∈ U j) (u : X → ℤ)

local notation "single" => (fun _ : Fin m => Unit)

variable {Ksp : Type*} [Fintype Ksp]
variable (root : Ksp → ℤ) (spatialD : Matrix α Ksp ℤ) (spatialBase : X → ℤ)
variable [Fintype X] (spatialResidue : Option Ksp × X → ℤ) (q : X → ℕ)
variable (box : ℝ) (mesh : ℝ≥0) (H N : X → ℝ) {spatialModulus : ℕ}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteGradedBranchPrefixLog
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def finiteGradedBranchLevel {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1))) :
    ∀ n, Finset (State n)
  | 0 => {initial}
  | n + 1 => (finiteGradedBranchLevel initial children n).biUnion (children n)

@[simp] theorem finiteGradedBranchLevel_mem_zero {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1))) (x : State 0) :
    x ∈ finiteGradedBranchLevel initial children 0 ↔ x = initial := by
  exact Finset.mem_singleton

theorem finiteGradedBranchLevel_mem_succ {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (n : ℕ) (x : State (n + 1)) :
    x ∈ finiteGradedBranchLevel initial children (n + 1) ↔
      ∃ y ∈ finiteGradedBranchLevel initial children n, x ∈ children n y :=
  Finset.mem_biUnion

theorem finiteGradedBranchLevel_child_mem {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    {n : ℕ} {y : State n} {x : State (n + 1)}
    (hy : y ∈ finiteGradedBranchLevel initial children n) (hx : x ∈ children n y) :
    x ∈ finiteGradedBranchLevel initial children (n + 1) :=
  (finiteGradedBranchLevel_mem_succ initial children n x).mpr ⟨y, hy, hx⟩

theorem finiteGradedBranchLevel_all_valid {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (depth : ℕ) (valid : ∀ n, State n → Prop) (hinit : valid 0 initial)
    (hstep : ∀ n, n < depth → ∀ x ∈ finiteGradedBranchLevel initial children n,
      valid n x → ∀ y ∈ children n x, valid (n + 1) y) :
    ∀ n, n ≤ depth → ∀ x ∈ finiteGradedBranchLevel initial children n, valid n x := by
  intro n
  induction n with
  | zero =>
    intro _ x hx
    have he := (finiteGradedBranchLevel_mem_zero initial children x).mp hx
    simpa only [he] using hinit
  | succ n ih =>
    intro hn x hx
    obtain ⟨y, hy, hxy⟩ := (finiteGradedBranchLevel_mem_succ initial children n x).mp hx
    exact hstep n (Nat.lt_of_succ_le hn) y hy (ih (Nat.le_of_succ_le hn) y hy) x hxy

noncomputable def finiteGradedBranchVertices {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1))) (depth : ℕ) :
    Finset (Σ n : Fin (depth + 1), State n.val) :=
  Finset.univ.sigma (fun n => finiteGradedBranchLevel initial children n.val)

@[simp] theorem finiteGradedBranchVertices_mem_iff {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (depth : ℕ) (v : Σ n : Fin (depth + 1), State n.val) :
    v ∈ finiteGradedBranchVertices initial children depth ↔
      v.2 ∈ finiteGradedBranchLevel initial children v.1.val := by
  change v ∈ Finset.univ.sigma (fun n : Fin (depth + 1) =>
    finiteGradedBranchLevel initial children n.val) ↔ _
  simp only [Finset.mem_sigma, Finset.mem_univ, true_and]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem finiteGradedBranchLevel_card_le_exp_sum {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (depth : ℕ) (logCap : ℕ → ℝ)
    (hcard : ∀ n, n < depth → ∀ x ∈ finiteGradedBranchLevel initial children n,
      ((children n x).card : ℝ) ≤ Real.exp (logCap n)) :
    ∀ n, n ≤ depth → ((finiteGradedBranchLevel initial children n).card : ℝ) ≤
      Real.exp (∑ j ∈ Finset.range n, logCap j) := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [finiteGradedBranchLevel]
  | succ n ih =>
    intro hn
    have hnd : n < depth := Nat.lt_of_succ_le hn
    change (((finiteGradedBranchLevel initial children n).biUnion (children n)).card : ℝ) ≤ _
    calc
      _ ≤ ((∑ x ∈ finiteGradedBranchLevel initial children n, (children n x).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ = ∑ x ∈ finiteGradedBranchLevel initial children n, ((children n x).card : ℝ) := by
        simp only [Nat.cast_sum]
      _ ≤ ∑ _x ∈ finiteGradedBranchLevel initial children n, Real.exp (logCap n) :=
        Finset.sum_le_sum (fun x hx => hcard n hnd x hx)
      _ = ((finiteGradedBranchLevel initial children n).card : ℝ) * Real.exp (logCap n) := by
        simp [nsmul_eq_mul]
      _ ≤ Real.exp (∑ j ∈ Finset.range n, logCap j) * Real.exp (logCap n) :=
        mul_le_mul_of_nonneg_right (ih (Nat.le_of_lt hnd)) (Real.exp_nonneg _)
      _ = Real.exp (∑ j ∈ Finset.range (n + 1), logCap j) := by
        rw [Finset.sum_range_succ, Real.exp_add]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarBadSublevelRamp
namespace OAI

section

namespace Erdos3
open scoped NNReal

noncomputable def scalarBadSublevelRamp (κ t : ℝ) : ℝ :=
  max 0 (min 1 (2 - 2 * |t| / κ))

theorem scalarBadSublevelRamp_range (κ t : ℝ) :
    scalarBadSublevelRamp κ t ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem scalarBadSublevelRamp_eq_one {κ t : ℝ} (hκ : 0 < κ) (ht : |t| ≤ κ / 2) :
    scalarBadSublevelRamp κ t = 1 := by
  have hr : 2 * |t| / κ ≤ 1 := (div_le_one hκ).mpr (by linarith)
  rw [scalarBadSublevelRamp, min_eq_left (by linarith), max_eq_right zero_le_one]

theorem scalarBadSublevelRamp_eq_zero {κ t : ℝ} (hκ : 0 < κ) (ht : κ ≤ |t|) :
    scalarBadSublevelRamp κ t = 0 := by
  have hr : 2 ≤ 2 * |t| / κ := (le_div_iff₀ hκ).mpr (by linarith)
  rw [scalarBadSublevelRamp, min_eq_right (by linarith), max_eq_left (by linarith)]

theorem scalarBadSublevelRamp_lipschitz {κ : ℝ} (hκ : 0 < κ) :
    LipschitzWith ⟨2 / κ, by positivity⟩ (scalarBadSublevelRamp κ) := by
  have hraw : LipschitzWith ⟨2 / κ, by positivity⟩ (fun t : ℝ => 2 - 2 * |t| / κ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq]
    have he : (2 - 2 * |x| / κ) - (2 - 2 * |y| / κ) = -(2 / κ) * (|x| - |y|) := by ring
    rw [he, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 / κ)]
    exact mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub x y) (by positivity)
  exact (hraw.const_min 1).const_max 0

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitBoundProductDifference
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem norm_finset_prod_sub_prod_le_sum {ι A : Type*}
    [NormedCommRing A] [NormOneClass A]
    (s : Finset ι) (f g : ι → A)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfs : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, ‖g i‖ ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hprod : ‖∏ i ∈ s, f i‖ ≤ 1 :=
      (s.norm_prod_le f).trans (Finset.prod_le_one (fun i _ => norm_nonneg (f i)) hfs)
    have hga : ‖g a‖ ≤ 1 := hg a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      ‖f a * (∏ i ∈ s, f i) - g a * (∏ i ∈ s, g i)‖ =
          ‖(f a - g a) * (∏ i ∈ s, f i) +
            g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ := by congr 1; ring
      _ ≤ ‖(f a - g a) * (∏ i ∈ s, f i)‖ +
          ‖g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ := norm_add_le _ _
      _ ≤ ‖f a - g a‖ * ‖∏ i ∈ s, f i‖ +
          ‖g a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖f a - g a‖ * 1 + 1 * (∑ i ∈ s, ‖f i - g i‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
          (mul_le_mul hga (ih hfs hgs) (norm_nonneg _) (by norm_num))
      _ = ‖f a - g a‖ + ∑ i ∈ s, ‖f i - g i‖ := by simp

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialTwoBlockEquiv
namespace OAI

section

namespace Erdos3
open scoped Classical

def twoKernelCopies (X : Type*) : X ⊕ X ≃ Fin 2 × X where
  toFun := Sum.elim (fun x => (0, x)) (fun x => (1, x))
  invFun z := if z.1 = 0 then Sum.inl z.2 else Sum.inr z.2
  left_inv := by intro z; cases z <;> simp
  right_inv := by rintro ⟨i, x⟩; fin_cases i <;> simp

def twoKernelEmbedding {X G : Type*} (blocks : Fin 2 × X ↪ G) : X ⊕ X ↪ G :=
  (twoKernelCopies X).toEmbedding.trans blocks

abbrev SpatialKernelRemainder {X G : Type*} (blocks : Fin 2 × X ↪ G) :=
  {g : G // g ∉ Set.range (twoKernelEmbedding blocks)}

noncomputable def spatialTwoBlockEquiv {X G : Type*} (blocks : Fin 2 × X ↪ G) :
    G ≃ X ⊕ (X ⊕ SpatialKernelRemainder blocks) :=
  ((Equiv.sumCongr (Equiv.ofInjective (twoKernelEmbedding blocks)
      (twoKernelEmbedding blocks).injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range (twoKernelEmbedding blocks)))).symm.trans
      (Equiv.sumAssoc X X (SpatialKernelRemainder blocks))

@[simp] theorem spatialTwoBlockEquiv_symm_first {X G : Type*}
    (blocks : Fin 2 × X ↪ G) (x : X) :
    (spatialTwoBlockEquiv blocks).symm (Sum.inl x) = blocks (0, x) := rfl

@[simp] theorem spatialTwoBlockEquiv_symm_second {X G : Type*}
    (blocks : Fin 2 × X ↪ G) (x : X) :
    (spatialTwoBlockEquiv blocks).symm (Sum.inr (Sum.inl x)) = blocks (1, x) := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineIntervalNormalizedBounds
namespace OAI

section

namespace Erdos3

theorem affineInterval_normalized_bounds
    {L H step : ℕ} {start : ℤ}
    (hL : 0 < L) (hH : 2 ≤ H) (hstep : 0 < step)
    (hinside : ∀ t : Fin H, 0 ≤ start + step * (t.val : ℤ) ∧
      start + step * (t.val : ℤ) < L) :
    0 ≤ (start : ℝ) / L ∧
      0 < (step : ℝ) * ((H - 1 : ℕ) : ℝ) / L ∧
      (start : ℝ) / L + (step : ℝ) * ((H - 1 : ℕ) : ℝ) / L < 1 ∧
      (step : ℝ) * ((H - 1 : ℕ) : ℝ) / L ≤ 1 := by
  have hHpos : 0 < H := by omega
  have hlast : H - 1 < H := Nat.sub_lt hHpos (by norm_num)
  have hstartZ : 0 ≤ start := by
    simpa only [Nat.cast_zero, mul_zero, add_zero] using (hinside ⟨0, hHpos⟩).1
  have hendZ := (hinside ⟨H - 1, hlast⟩).2
  have hstart : (0 : ℝ) ≤ start := by exact_mod_cast hstartZ
  have hend : (start : ℝ) + (step : ℝ) * ((H - 1 : ℕ) : ℝ) < L := by
    exact_mod_cast hendZ
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hstepreal : (0 : ℝ) < step := by exact_mod_cast hstep
  have hHreal : (0 : ℝ) < ((H - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < H - 1 by omega)
  have hlower := div_nonneg hstart hLreal.le
  have hwidth := div_pos (mul_pos hstepreal hHreal) hLreal
  have hsum : (start : ℝ) / L + (step : ℝ) * ((H - 1 : ℕ) : ℝ) / L < 1 := by
    rw [← add_div]
    exact (div_lt_one hLreal).mpr hend
  exact ⟨hlower, hwidth, hsum, by linarith⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PiCoordinatePolynomialCoefficients
namespace OAI

section

namespace Erdos3.VectorPolynomial

@[simp] theorem coefficients_ofCoordinates_pi_apply {X K : Type*} [Fintype K]
    (p : K → MvPolynomial X ℝ) (α : X →₀ ℕ) (i : K) :
    coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ K) p) α i =
      (p i).coeff α := by
  have h := congrArg (fun polynomial : MvPolynomial X ℝ => polynomial.coeff α)
    (coordinate_ofCoordinates (R := ℝ) (Pi.basisFun ℝ K) p i)
  rw [coeff_coordinate] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FullTaggedProjectionPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {X J : Type*} [Fintype J]

theorem linearMap_pi_apply_eq_sum
    (P : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (x : J → ℝ) (i : J) :
    P x i = ∑ a : J, P (Pi.single a 1) i * x a := by
  have hsum : ∑ a : J, x a • Pi.single a (1 : ℝ) = x := by
    ext a
    simp [Pi.smul_apply, Pi.single_apply]
  conv_lhs => rw [← hsum, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem sum_projection_coordinate_eq
    (P : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (U : Submodule ℝ (J → ℝ))
    (hP : ∀ x, x ∈ U → P x = x)
    (poly : VectorPolynomial X ℝ (J → ℝ))
    (hm : ∀ α, coefficients poly α ∈ U) (i : J) :
    (∑ a : J, P (Pi.single a 1) i •
      coordinate (LinearMap.proj a : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly) =
      coordinate (LinearMap.proj i : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly := by
  ext α
  simp only [coeff_sum, coeff_smul, coeff_coordinate, LinearMap.toAddMonoidHom_coe,
    LinearMap.proj_apply, smul_eq_mul]
  rw [← linearMap_pi_apply_eq_sum, hP _ (hm α)]

theorem sum_projection_C_eq
    (P : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (U : Submodule ℝ (J → ℝ))
    (hP : ∀ x, x ∈ U → P x = x) (c : J → ℝ) (hc : c ∈ U) (i : J) :
    (∑ a : J, P (Pi.single a 1) i • C (c a) : MvPolynomial X ℝ) = C (c i) := by
  simp only [smul_eq_C_mul, ← C_mul, ← map_sum]
  rw [← linearMap_pi_apply_eq_sum, hP _ hc]

theorem sum_projection_coordinate_sub_C_eq
    (P : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (U : Submodule ℝ (J → ℝ))
    (hP : ∀ x, x ∈ U → P x = x)
    (poly : VectorPolynomial X ℝ (J → ℝ))
    (hm : ∀ α, coefficients poly α ∈ U)
    (c : J → ℝ) (hc : c ∈ U) (i : J) :
    (∑ a : J, P (Pi.single a 1) i •
      (coordinate (LinearMap.proj a : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly - C (c a))) =
      coordinate (LinearMap.proj i : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly - C (c i) := by
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [sum_projection_coordinate_eq P U hP poly hm i, sum_projection_C_eq P U hP c hc i]

theorem sum_projection_remainder_eq
    {K : Type*}
    (P : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (U : Submodule ℝ (J → ℝ))
    (hP : ∀ x, x ∈ U → P x = x)
    (poly : VectorPolynomial X ℝ (J → ℝ))
    (hm : ∀ α, coefficients poly α ∈ U)
    (c : J → ℝ) (hc : c ∈ U)
    (spatial : X → MvPolynomial K ℝ) (tag error : J → MvPolynomial K ℝ)
    (heq : ∀ a, aeval spatial
      (coordinate (LinearMap.proj a : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly) - C (c a) =
        error a + tag a) (i : J) :
    (∑ a : J, P (Pi.single a 1) i • tag a) -
        aeval spatial
          (coordinate (LinearMap.proj i : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly - C (c i)) =
      -(∑ a : J, P (Pi.single a 1) i • error a) := by
  have hcenter := congrArg (aeval spatial)
    (sum_projection_coordinate_sub_C_eq P U hP poly hm c hc i)
  simp only [map_sum, map_smul, map_sub, aeval_C, MvPolynomial.algebraMap_eq] at hcenter
  simp_rw [heq, smul_add] at hcenter
  rw [Finset.sum_add_distrib] at hcenter
  rw [map_sub, aeval_C, MvPolynomial.algebraMap_eq, heq i, ← hcenter]
  abel

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateFreezingScoreBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem finiteFreezing_exp_weighted_error_le
    {B C b q e : ℝ} (hC : 0 ≤ C)
    (hBbound : B ≤ Real.exp b) (hCbound : C ≤ Real.exp b)
    (he : 2 * b + q + Real.log 8 ≤ e) :
    B * (C * Real.exp (-e)) ≤ Real.exp (-q) / 8 := by
  have hprod : B * C ≤ Real.exp b * Real.exp b :=
    mul_le_mul hBbound hCbound hC (Real.exp_nonneg _)
  calc
    B * (C * Real.exp (-e)) = (B * C) * Real.exp (-e) := (mul_assoc _ _ _).symm
    _ ≤ (Real.exp b * Real.exp b) * Real.exp (-e) :=
      mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg _)
    _ = Real.exp (2 * b - e) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-q - Real.log 8) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-q) / 8 := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 8)]

theorem finiteFreezing_exp_score_surplus
    {Bweight Bobs Lip b q e t scoreThreshold : ℝ}
    (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip)
    (hweight : Bweight ≤ Real.exp b) (hobs : Bobs ≤ Real.exp b)
    (hlip : Lip ≤ Real.exp b)
    (he : 2 * b + q + Real.log 8 ≤ e)
    (ht : 2 * b + q + Real.log 8 ≤ t)
    (hscore : Real.exp (-q) ≤ scoreThreshold) :
    Real.exp (-q) / 2 + Bweight * (Lip * Real.exp (-e)) +
      (Bweight * Bobs) * Real.exp (-t) < scoreThreshold := by
  have herror := finiteFreezing_exp_weighted_error_le hLip hweight hlip he
  have hdiscard := finiteFreezing_exp_weighted_error_le hBobs hweight hobs ht
  rw [← mul_assoc] at hdiscard
  have hpos := Real.exp_pos (-q)
  linarith

theorem finiteFreezing_exp_half_score_le {q recursionParameter : ℝ}
    (hparameter : q + Real.log 2 ≤ recursionParameter) :
    Real.exp (-recursionParameter) ≤ Real.exp (-q) / 2 := by
  calc
    _ ≤ Real.exp (-q - Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastOriginalSampleUniformBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

def forecastOriginalSmoothBudget (m : ℕ) (P : ℝ) : ℝ :=
  (10 * (m : ℝ) + 30) * (P + 1) ^ 2

theorem forecastOriginalSmoothBudget_bounds (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    let Q := ((m : ℝ) + 2) * P + 4 * m + 8
    0 ≤ forecastOriginalSmoothBudget m P ∧
      P * (2 * P + 1) + P * (Q + 1) + 1 ≤ forecastOriginalSmoothBudget m P ∧
      2 * P * (2 * P + 1) + 2 * P * (Q + 1) + 2 * P + (4 * P + 2) +
        2 * Q + 2 ≤ forecastOriginalSmoothBudget m P := by
  intro Q
  refine ⟨?_, ?_, ?_⟩
  · unfold forecastOriginalSmoothBudget
    positivity
  · apply sub_nonneg.mp
    have he : forecastOriginalSmoothBudget m P -
        (P * (2 * P + 1) + P * (Q + 1) + 1) =
        (9 * (m : ℝ) + 26) * P ^ 2 + (16 * m + 50) * P + (10 * m + 29) := by
      unfold forecastOriginalSmoothBudget Q
      ring
    rw [he]
    positivity
  · apply sub_nonneg.mp
    have he : forecastOriginalSmoothBudget m P -
        (2 * P * (2 * P + 1) + 2 * P * (Q + 1) + 2 * P + (4 * P + 2) + 2 * Q + 2) =
        (8 * (m : ℝ) + 22) * P ^ 2 + (10 * m + 30) * P + (2 * m + 10) := by
      unfold forecastOriginalSmoothBudget Q
      ring
    rw [he]
    positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

end OAI

end


