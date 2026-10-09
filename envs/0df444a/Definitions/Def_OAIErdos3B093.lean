-- Prove2me | Definitions.Def_OAIErdos3B093
-- name    : OAIErdos3B093
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T17:49:23.407914+00:00
-- url     : https://prove2.me/theorems/c87aeaea-1840-4fa5-9b8c-46b754e5440e
-- title:
--   OpenAI Erdős-3 split, definitions bundle 94 of 106
-- statement:
--   Definitions bundle 94 of 106 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B092`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 94 available.
--
--   Modules: `OAI.Erdos3.MultidegreeLieFiltration.BoxedDegreeIndex`, `OAI.Erdos3.MultidegreeLieFiltration.boxedDegreeMonomial`, `OAI.Erdos3.MultidegreeLieFiltration.boxedDegreeMonomial_apply`, `OAI.Erdos3.MultidegreeLieFiltration.boxedDegreeMonomial_injective`, `OAI.Erdos3.MultidegreeLieFiltration.boxedDegreeMonomial_le`, `OAI.Erdos3.MultidegreeLieFiltration.boxedPolynomial`, `OAI.Erdos3.MultidegreeLieFiltration.boxedPolynomial_coefficient`, `OAI.Erdos3.MultidegreeLieFiltration.boxedPolynomial_coefficient_outside`, `OAI.Erdos3.MultidegreeLieFiltration.boxedPolynomial_positive`, `OAI.Erdos3.MultidegreeLieFiltration.exists_boxedDegreeMonomial`, `OAI.Erdos3.MultidegreeLieFiltration.exists_positivePolynomial_orbit`, `OAI.Erdos3.MultidegreeLieFiltration.mem_positiveCoefficientLayer`, `OAI.Erdos3.MultidegreeLieFiltration.mem_positivePolynomialAlgebra`, `OAI.Erdos3.MultidegreeLieFiltration.positiveCoefficientLayer`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialAlgebra`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialBasis`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialBasis_bracket_coefficient_height`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialBasis_coefficient_ne`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialBasis_coefficient_self`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialBasis_evaluation`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialBasis_monomial`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialBasis_repr`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialBasis_structure_height`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialCoefficientEquiv`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialCoefficientEquiv_apply`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialComponent`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialComponent_eq_zero`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialComponent_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialCoordinates`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialCoordinates_injective`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDegreeBasis`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDegreeBasis_height`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDegreeFiltration`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDegreeLayer`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDegreeLayer_antitone`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDegreeLayer_eq`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDegreeLayer_lie`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDegreeLayer_one`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDegreeLayer_terminal`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDiagonal`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDiagonal_adapted`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDiagonal_coefficient`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDiagonal_constant`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDiagonal_eval`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDiagonal_projection`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDownsetBasis`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDownsetBasis_repr`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDownsetDegreeBasis`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDownsetDegreeBasis_height`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDownsetIdeal_eq_span`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDownsetIdeal_eq_support`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDownsetMultidegreeBasis`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDownsetMultidegreeBasis_height`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDownsetQuotient`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDownsetQuotient_terminal`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDownset_degree_span`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDownset_multidegree_span`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialEvaluation`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialEvaluation_apply`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialEvaluation_component`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialFiniteDimensional`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialLayer_le_outsideDownset`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialMultidegree`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialMultidegreeBasis`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialMultidegreeBasis_height`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialMultidegreeLayer`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialMultidegreeLayer_antitone`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialMultidegreeLayer_lie`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialMultidegreeLayer_terminal`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialMultidegreeLayer_zero`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialQuotientProduct`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialQuotientProductLattice`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialQuotientProductMap`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialQuotientProductRealMap`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialQuotientProductRealMap_component`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialQuotientProductRealMap_injective`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialQuotientProduct_lattice_cover`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialQuotientProduct_lattice_detect`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialSupport`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialSupport_eq_span`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialSupportedBasis`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialSupportedBasis_coe`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialSupportedFinBasis`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialSupportedFinBasis_height`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomial_constant`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomial_finrank_le`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomial_finrank_le_total`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomial_quotient_family_basis_cover`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomial_support_of_layers`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialEvaluation_commute`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialMap`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialMap_adapted`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialMap_coefficient_tmul`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialMap_constant`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialTensor`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialTensor_injective`, `OAI.Erdos3.MultidegreeLieFiltration.realQuotientMultidegreeMap`, `OAI.Erdos3.MultidegreeLieFiltration.realQuotientMultidegreeOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.realQuotientMultidegreeOrbit_eval`, `OAI.Erdos3.MultidegreeLieFiltration.realQuotientMultidegree_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.sum_positivePolynomialComponent`, `OAI.Erdos3.NilpotentLieBCHGroup.coord_mem_realificationKernel_iff`, `OAI.Erdos3.NilpotentLieBCHGroup.mem_realificationSubgroup_ker_iff`, `OAI.Erdos3.NilpotentLieBCHGroup.mem_realification_integral_lattice_iff`, `OAI.Erdos3.NilpotentLieFiltration.RealSymbolGradeQuotientGroup`, `OAI.Erdos3.NilpotentLieFiltration.adjoint_correction_sub_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.adjoint_sub_mem_invariant_next_layer`, `OAI.Erdos3.NilpotentLieFiltration.correction_adjoint_sub_current_bracket_mem`, `OAI.Erdos3.NilpotentLieFiltration.correction_inverse_adjoint_sub_current_bracket_mem`, `OAI.Erdos3.NilpotentLieFiltration.correction_removal_coord_sub_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.correction_removal_preserves_lower_layers`, `OAI.Erdos3.NilpotentLieFiltration.current_layer_derivative_system`, `OAI.Erdos3.NilpotentLieFiltration.current_layer_normalization`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_symbol_reset`, `OAI.Erdos3.NilpotentLieFiltration.exists_symbol_reset_bounds`, `OAI.Erdos3.NilpotentLieFiltration.filteredPolynomialSymbolMap_basis_height`, `OAI.Erdos3.NilpotentLieFiltration.filteredPolynomialSymbolMap_basis_repr`, `OAI.Erdos3.NilpotentLieFiltration.filteredPolynomialSymbolMap_monomial_blocks`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousAssociatedGradedEquiv`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousAssociatedGradedEquiv_basis`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousAssociatedGradedEquiv_repr`, `OAI.Erdos3.NilpotentLieFiltration.lie_mem_invariant_sup_layer_of_degree`, `OAI.Erdos3.NilpotentLieFiltration.logDerivative_current_layer_of_lower_brackets`, `OAI.Erdos3.NilpotentLieFiltration.polynomial_bchRemove_grades`, `OAI.Erdos3.NilpotentLieFiltration.polynomial_lift_matching_remainder`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopPolynomialMap`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopSymbolMap`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopSymbolMap_surjective`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopSymbolMap_symbol`, `OAI.Erdos3.NilpotentLieFiltration.realGradeProjection_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.realGradeProjection_mem_of_mem_sup_next`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_eval₂_gradeProjection`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_gradeProjection`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_gradeProjection_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_gradeProjection_homogeneous`, `OAI.Erdos3.NilpotentLieFiltration.realQuotientFamily_joint_injective`, `OAI.Erdos3.NilpotentLieFiltration.realQuotientFamily_lattice_detect`, `OAI.Erdos3.NilpotentLieFiltration.realQuotientStep_integral_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeEvaluation`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeEvaluation_apply`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeEvaluation_correction_below`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeEvaluation_current_correction`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeEvaluation_eq_projection`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeEvaluation_homogeneous`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeQuotientHom`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeQuotient_mem_of_grade_values`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeQuotient_mem_of_restricted_path`, `OAI.Erdos3.NilpotentLieFiltration.real_corrected_middle_mem_next_layer`, `OAI.Erdos3.NilpotentLieFiltration.real_correction_current_grade`, `OAI.Erdos3.NilpotentLieFiltration.real_correction_preserves_grades_below`, `OAI.Erdos3.NilpotentLieFiltration.real_current_bracket_remainder`, `OAI.Erdos3.NilpotentLieFiltration.real_matching_grade_remainder`, `OAI.Erdos3.NilpotentLieFiltration.real_mem_of_homogeneous_mem_sup_next`, `OAI.Erdos3.NilpotentLieFiltration.real_quotient_mem_subgroup_iff`, `OAI.Erdos3.NilpotentLieFiltration.real_sub_grade_mem_sup_next`, `OAI.Erdos3.NilpotentLieFiltration.real_subalgebra_layer_eq_span`, `OAI.Erdos3.NilpotentLieFiltration.real_subalgebra_layer_mem_iff_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.removal_adjoint_relation`, `OAI.Erdos3.NilpotentLieFiltration.reset_real_splitting`, `OAI.Erdos3.NilpotentLieFiltration.reset_real_symbol_splitting`, `OAI.Erdos3.NilpotentLieFiltration.simultaneous_real_grade_correction`, `OAI.Erdos3.NilpotentLieFiltration.squareDiagonalLie`, `OAI.Erdos3.NilpotentLieFiltration.squareDiagonalPolynomialMap`, `OAI.Erdos3.NilpotentLieFiltration.squareDiagonalPolynomialMap_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.squareDiagonalSymbolMap`, `OAI.Erdos3.NilpotentLieFiltration.squareDiagonalSymbolMap_symbol`, `OAI.Erdos3.NilpotentLieFiltration.squareFstPolynomialMap`, `OAI.Erdos3.NilpotentLieFiltration.squareFstPolynomialMap_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.squareFstPolynomialMap_diagonal`, `OAI.Erdos3.NilpotentLieFiltration.squareFstPolynomialMap_relative`, `OAI.Erdos3.NilpotentLieFiltration.squareSndPolynomialMap`, `OAI.Erdos3.NilpotentLieFiltration.squareSndPolynomialMap_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.squareSndPolynomialMap_diagonal`, `OAI.Erdos3.NilpotentLieFiltration.squareSndPolynomialMap_relative`, `OAI.Erdos3.NilpotentLieFiltration.square_polynomial_ext`, `OAI.Erdos3.NilpotentLieFiltration.truncateRealSymbol_mem_of_grade_values`, `OAI.Erdos3.PolynomialTranslationLie.weightedAssociatedGradedEquiv`, `OAI.Erdos3.PolynomialTranslationLie.weightedAssociatedGradedEquiv_repr`, `OAI.Erdos3.VectorPolynomial.bchRemove`, `OAI.Erdos3.VectorPolynomial.bchRemove_coefficients_mem`, `OAI.Erdos3.VectorPolynomial.bchRemove_constant`, `OAI.Erdos3.VectorPolynomial.bchRemove_factorization`, `OAI.Erdos3.VectorPolynomial.eval₂_bchRemove`, `OAI.Erdos3.basisBelowProjection_succ`, `OAI.Erdos3.exists_block_subspace_corrections`, `OAI.Erdos3.exists_block_subspace_defining_matrix`, `OAI.Erdos3.exists_controlled_block_subspace_lift`, `OAI.Erdos3.exists_controlled_constraint_section`, `OAI.Erdos3.exists_controlled_linear_subspace_lift`, `OAI.Erdos3.exists_controlled_weighted_linear_splitting`, `OAI.Erdos3.exists_joint_weighted_corrections`, `OAI.Erdos3.exists_uniformPolynomialBCHPeriod_exp_bound`, `OAI.Erdos3.jointMatrixImages`, `OAI.Erdos3.jointMatrixImages_equation`, `OAI.Erdos3.jointMatrixImages_grid`, `OAI.Erdos3.mem_realificationLieKernel_iff`, `OAI.Erdos3.polynomialBCHMap_uniform_coset_eq`, `OAI.Erdos3.polynomialBCHMap_uniform_inverse_coset_eq`, `OAI.Erdos3.polynomialBCHPeriod_dvd_uniform`, `OAI.Erdos3.polynomialDenominator_dvd_power`, `OAI.Erdos3.polynomialFamilyDenominator_dvd_power`, `OAI.Erdos3.polynomial_period_cost_le_exp`, `OAI.Erdos3.realPolynomialBCHMap_uniform_cosets`, `OAI.Erdos3.reset_splitting_in_quotient`, `OAI.Erdos3.subalgebraLayerFamily`, `OAI.Erdos3.subalgebraLayerFamily_height`, `OAI.Erdos3.uniformPolynomialBCHPeriod`, `OAI.Erdos3.uniformPolynomialBCHPeriod_le_exp`, `OAI.Erdos3.uniformPolynomialBCHPeriod_pos`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090
import Definitions.Def_OAIErdos3B095

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CurrentLayerPreservation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem lie_mem_invariant_sup_layer_of_degree
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) {i j : ℕ}
    {u v : L} (hu : u ∈ U) (hui : u ∈ F.layer i) (hv : v ∈ V ⊔ F.layer j) :
    ⁅u, v⁆ ∈ V ⊔ F.layer (i + j) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  rw [lie_add]
  exact (V ⊔ F.layer (i + j)).add_mem
    (Submodule.mem_sup_left (hUV _ hu _ hx))
    (Submodule.mem_sup_right (F.lie_mem hui hy))

theorem correction_adjoint_sub_current_bracket_mem (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) {j : ℕ} (hj : 2 ≤ j)
    (a : F.Group) (haU : a.coord ∈ U) (ha : a.coord ∈ F.layer (j - 1))
    (x k : L) (hx : x - k ∈ V ⊔ F.layer 2) :
    dualAdjoint a x - (x + ⁅a.coord, k⁆) ∈ V ⊔ F.layer (j + 1) := by
  have hx1 : x ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hrem := F.dualAdjoint_sub_first_bracket_mem_layer hs a ha x hx1
  have hrem' : dualAdjoint a x - (x + ⁅a.coord, x⁆) ∈ F.layer (j + 1) :=
    F.antitone (by omega) hrem
  have hbr : ⁅a.coord, x - k⁆ ∈ V ⊔ F.layer (j + 1) := by
    have h := F.lie_mem_invariant_sup_layer_of_degree U V hUV haU ha hx
    have he : j - 1 + 2 = j + 1 := by omega
    simpa only [he] using h
  have h := (V ⊔ F.layer (j + 1)).add_mem (Submodule.mem_sup_right hrem') hbr
  rw [lie_sub] at h
  convert h using 1; abel

theorem correction_inverse_adjoint_sub_current_bracket_mem (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) {j : ℕ} (hj : 2 ≤ j)
    (a : F.Group) (haU : a.coord ∈ U) (ha : a.coord ∈ F.layer (j - 1))
    (x k : L) (hx : x - k ∈ V ⊔ F.layer 2) :
    dualAdjoint a⁻¹ x - (x - ⁅a.coord, k⁆) ∈ V ⊔ F.layer (j + 1) := by
  have h := F.correction_adjoint_sub_current_bracket_mem hs U V hUV hj a⁻¹
    (U.neg_mem haU) ((F.layer (j - 1)).neg_mem ha) x k hx
  simpa only [coord_inv, neg_lie, ← sub_eq_add_neg] using h

theorem correction_removal_coord_sub_mem_layer {j : ℕ}
    (a g c : F.Group) (ha : a.coord ∈ F.layer (j - 1))
    (hc : c.coord ∈ F.layer (j - 1)) (hj : 1 ≤ j) :
    (a⁻¹ * g * c⁻¹).coord - (g.coord - a.coord - c.coord) ∈ F.layer j := by
  have hg1 : g.coord ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hag1 : (a⁻¹ * g).coord ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have ha' : -a.coord ∈ F.layer (j - 1) := (F.layer (j - 1)).neg_mem ha
  have hc' : -c.coord ∈ F.layer (j - 1) := (F.layer (j - 1)).neg_mem hc
  have hleft : ⁅-a.coord, g.coord⁆ ∈ F.layer j := by
    simpa only [Nat.sub_add_cancel hj] using F.lie_mem ha' hg1
  have hright : ⁅(a⁻¹ * g).coord, -c.coord⁆ ∈ F.layer j := by
    have he : 1 + (j - 1) = j := by omega
    simpa only [he] using F.lie_mem hag1 hc'
  have h1 := lieBCH_sub_add_mem F.lowerCentralSeries_eq_bot (F.layerIdeal j)
    (-a.coord) g.coord hleft
  have h2 := lieBCH_sub_add_mem F.lowerCentralSeries_eq_bot (F.layerIdeal j)
    (a⁻¹ * g).coord (-c.coord) hright
  change (a⁻¹ * g).coord - (-a.coord + g.coord) ∈ F.layer j at h1
  change (a⁻¹ * g * c⁻¹).coord - ((a⁻¹ * g).coord + -c.coord) ∈ F.layer j at h2
  convert (F.layer j).add_mem h2 h1 using 1; abel

theorem correction_removal_preserves_lower_layers {j : ℕ}
    (a g c : F.Group) (ha : a.coord ∈ F.layer (j - 1))
    (hc : c.coord ∈ F.layer (j - 1)) (hj : 1 ≤ j) :
    (a⁻¹ * g * c⁻¹).coord - g.coord ∈ F.layer (j - 1) := by
  have h := F.antitone (by omega : j - 1 ≤ j)
    (F.correction_removal_coord_sub_mem_layer a g c ha hc hj)
  have hneg := (F.layer (j - 1)).neg_mem ((F.layer (j - 1)).add_mem ha hc)
  convert (F.layer (j - 1)).add_mem h hneg using 1; abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem removal_adjoint_relation (a g c : F.Group) (x y : L)
    (hxy : x = dualAdjoint g y) :
    dualAdjoint a⁻¹ x = dualAdjoint (a⁻¹ * g * c⁻¹) (dualAdjoint c y) := by
  rw [dualAdjoint_mul, dualAdjoint_mul, dualAdjoint_inv_cancel, hxy]

theorem current_layer_normalization {κ : Type*} (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) {j : ℕ} (hj : 2 ≤ j)
    (g a c : F.Group) (hg : g.coord ∈ U) (haU : a.coord ∈ U) (hcU : c.coord ∈ U)
    (ha : a.coord ∈ F.layer (j - 1)) (hc : c.coord ∈ F.layer (j - 1))
    (S R k : κ → L) (p : L) (hp : p ∈ F.layer (j - 1))
    (hSR : ∀ b, S b = dualAdjoint g (R b))
    (hR : ∀ b, R b - k b ∈ V ⊔ F.layer j)
    (hlower : ∀ b, ⁅g.coord - p, k b⁆ ∈ V ⊔ F.layer (j + 1))
    (hleft : ∀ b, S b - k b - ⁅a.coord, k b⁆ ∈ V ⊔ F.layer (j + 1))
    (hright : ∀ b, R b - k b + ⁅c.coord, k b⁆ ∈ V ⊔ F.layer (j + 1)) :
    let g' := a⁻¹ * g * c⁻¹
    let S' := fun b => dualAdjoint a⁻¹ (S b)
    let R' := fun b => dualAdjoint c (R b)
    let p' := p - a.coord - c.coord
    a * g' * c = g ∧ g'.coord ∈ U ∧ p' ∈ F.layer (j - 1) ∧
      g'.coord - (g.coord - a.coord - c.coord) ∈ F.layer j ∧
      (∀ b, S' b = dualAdjoint g' (R' b)) ∧
      ∀ b, S' b - k b ∈ V ⊔ F.layer (j + 1) ∧
        R' b - k b ∈ V ⊔ F.layer (j + 1) ∧
        ⁅p', k b⁆ ∈ V ⊔ F.layer (j + 1) := by
  intro g' S' R' p'
  have hj1 : 1 ≤ j := by omega
  have hdown : V ⊔ F.layer j ≤ V ⊔ F.layer 2 :=
    sup_le le_sup_left ((F.antitone hj).trans le_sup_right)
  have hR2 (b : κ) : R b - k b ∈ V ⊔ F.layer 2 := hdown (hR b)
  have hS2 (b : κ) : S b - k b ∈ V ⊔ F.layer 2 := by
    have hx : R b ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
    have h := F.dualAdjoint_sub_mem_next_layer 1 g (R b) hx
    rw [hSR b]
    convert (V ⊔ F.layer 2).add_mem (Submodule.mem_sup_right h) (hR2 b) using 1
    abel
  refine ⟨?_, ?_, (F.layer (j - 1)).sub_mem ((F.layer (j - 1)).sub_mem hp ha) hc,
    F.correction_removal_coord_sub_mem_layer a g c ha hc hj1,
    fun b => F.removal_adjoint_relation a g c (S b) (R b) (hSR b), ?_⟩
  · dsimp [g']
    group
  · exact lieBCH_mem U s (lieBCH_mem U s (U.neg_mem haU) hg) (U.neg_mem hcU)
  · intro b
    have hSa := F.correction_inverse_adjoint_sub_current_bracket_mem hs U V hUV hj
      a haU ha (S b) (k b) (hS2 b)
    have hRc := F.correction_adjoint_sub_current_bracket_mem hs U V hUV hj
      c hcU hc (R b) (k b) (hR2 b)
    have hk1 : k b ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
    have hbr := F.adjoint_current_layer_relation U V hUV hs hj1 g hg (R b) (k b)
      p hp hk1 (hR b) (hlower b)
    rw [← hSR b] at hbr
    refine ⟨?_, ?_, ?_⟩
    · convert (V ⊔ F.layer (j + 1)).add_mem hSa (hleft b) using 1; dsimp [S']; abel
    · convert (V ⊔ F.layer (j + 1)).add_mem hRc (hright b) using 1; dsimp [R']; abel
    · have h := (V ⊔ F.layer (j + 1)).sub_mem
        ((V ⊔ F.layer (j + 1)).add_mem hbr (hleft b)) (hright b)
      dsimp [p']
      rw [sub_lie, sub_lie]
      convert h using 1; abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem logDerivative_current_layer_of_lower_brackets (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (z : DualGroup F.lowerCentralSeries_eq_bot) (hz : dualBaseLinear z.coord ∈ U)
    (k : L) (ht : dualTangentLinear z.coord - k ∈ V ⊔ F.layer j)
    (hk : ⁅dualBaseLinear z.coord, k⁆ ∈ V ⊔ F.layer (j + 1)) :
    dualLogDerivative z - dualTangentLinear z.coord ∈ V ⊔ F.layer (j + 1) := by
  apply F.logDerivative_current_layer_relation hs U V hUV j z hz
  have h := (V ⊔ F.layer (j + 1)).add_mem
    (F.lie_mem_invariant_sup_next_layer U V hUV j hz ht) hk
  simpa only [lie_sub, sub_add_cancel] using h

theorem adjoint_sub_mem_invariant_next_layer (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (g : F.Group) (hg : g.coord ∈ U) (r : L) (hr : r ∈ V ⊔ F.layer j) :
    dualAdjoint g r - r ∈ V ⊔ F.layer (j + 1) := by
  have hbr := F.lie_mem_invariant_sup_next_layer U V hUV j hg hr
  have hW := F.invariant_sup_layer U V hUV (j + 1)
  have hrem := dualAdjoint_sub_first_bracket_mem hs U (V ⊔ F.layer (j + 1))
    hW g hg r (hW _ hg _ hbr)
  convert (V ⊔ F.layer (j + 1)).add_mem hrem hbr using 1; abel

theorem current_layer_derivative_system (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (z : DualGroup F.lowerCentralSeries_eq_bot) (hz : dualBaseLinear z.coord ∈ U)
    (k small rational extra : L)
    (ht : dualTangentLinear z.coord - k ∈ V ⊔ F.layer j)
    (hk : ⁅dualBaseLinear z.coord, k⁆ ∈ V ⊔ F.layer (j + 1))
    (hr : rational ∈ V ⊔ F.layer j) (he : extra - k ∈ V ⊔ F.layer (j + 1))
    (hsystem : dualLogDerivative z = small + dualAdjoint (dualBaseHom z) rational + extra) :
    dualTangentLinear z.coord - k - (small + rational) ∈ V ⊔ F.layer (j + 1) := by
  have hY := F.logDerivative_current_layer_of_lower_brackets (by omega) U V hUV j z hz k ht hk
  have hA := F.adjoint_sub_mem_invariant_next_layer hs U V hUV j (dualBaseHom z) hz rational hr
  rw [hsystem] at hY
  convert (V ⊔ F.layer (j + 1)).add_mem
    ((V ⊔ F.layer (j + 1)).neg_mem hY) ((V ⊔ F.layer (j + 1)).add_mem hA he) using 1
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem realGradeProjection_mem_layer (k : ℕ) (x : ℝ ⊗[ℚ] L) :
    basisGradeProjection (b.baseChange ℝ) w k x ∈ F.realification.layer k := by
  change basisGradeProjection (b.baseChange ℝ) w k x ∈ (F.realLayer k).toSubmodule
  rw [F.realLayer_eq_span_basis b k _ (hlayers k)]
  apply Submodule.span_mono (Set.image_mono ?_)
    (basisCoordinateProjection_mem_span (b.baseChange ℝ) {i | w i = k} x)
  intro i hi
  exact (show w i = k from hi).ge

include hlayers in

theorem real_corrected_middle_mem_next_layer
    (U : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U) (k : ℕ)
    (Y A D : F.realification.Group)
    (hY : Y.coord ∈ U ⊔ (F.realLayer k).toSubmodule)
    (hA : A.coord ∈ F.realification.layer k)
    (hD : D.coord ∈ F.realification.layer k)
    (hgrade : basisGradeProjection (b.baseChange ℝ) w k Y.coord -
      basisGradeProjection (b.baseChange ℝ) w k A.coord -
      basisGradeProjection (b.baseChange ℝ) w k D.coord ∈ U) :
    (A⁻¹ * Y * D⁻¹).coord ∈ U ⊔ (F.realLayer (k + 1)).toSubmodule := by
  let P := A⁻¹ * Y * D⁻¹
  have hAn : -A.coord ∈ F.realification.layer k := (F.realification.layer k).neg_mem hA
  have hDn : -D.coord ∈ F.realification.layer k := (F.realification.layer k).neg_mem hD
  have hrem : P.coord - (-A.coord + Y.coord + -D.coord) ∈
      F.realification.layer (k + 1) :=
    F.realification.bch_triple_sub_sum_mem_next_layer k _ _ _ hAn hDn
  have hsum : -A.coord + Y.coord + -D.coord ∈ U ⊔ (F.realLayer k).toSubmodule :=
    (U ⊔ (F.realLayer k).toSubmodule).add_mem
      ((U ⊔ (F.realLayer k).toSubmodule).add_mem (Submodule.mem_sup_right hAn) hY)
      (Submodule.mem_sup_right hDn)
  have hP : P.coord ∈ U ⊔ (F.realLayer k).toSubmodule := by
    have hsmall : P.coord - (-A.coord + Y.coord + -D.coord) ∈ (F.realLayer k).toSubmodule :=
      F.realification.antitone (Nat.le_succ k) hrem
    have h := (U ⊔ (F.realLayer k).toSubmodule).add_mem (Submodule.mem_sup_right hsmall) hsum
    simpa only [sub_add_cancel] using h
  have hPg : basisGradeProjection (b.baseChange ℝ) w k P.coord ∈ U := by
    have h := F.realGradeProjection_bch_triple b w hlayers k (-A.coord) Y.coord (-D.coord) hAn hDn
    change basisGradeProjection (b.baseChange ℝ) w k P.coord = _ at h
    rw [h, map_neg, map_neg]
    convert hgrade using 1
    abel
  rw [F.realLayer_eq_span_basis b k _ (hlayers k)] at hP
  change P.coord ∈ U ⊔ (F.realLayer (k + 1)).toSubmodule
  rw [F.realLayer_eq_span_basis b (k + 1) _ (hlayers (k + 1))]
  exact hU.mem_sup_higher_of_grade (b.baseChange ℝ) w U k P.coord hP hPg

theorem real_quotient_mem_subgroup_iff (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (k : ℕ) (g : F.realification.Group) :
    NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) g ∈
      (NilpotentLieBCHGroup.realLieSubgroup
        (hnil := F.realification.lowerCentralSeries_eq_bot) U).map
        (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot)
          (F.realification.layerIdeal k)) ↔
      g.coord ∈ U.toSubmodule ⊔ (F.realLayer k).toSubmodule := by
  rw [NilpotentLieBCHGroup.realLieSubgroup,
    NilpotentLieBCHGroup.quotient_mem_map_subgroup_iff]
  change g.coord ∈ U.toSubmodule.restrictScalars ℚ ⊔
    (F.realLayer k).toSubmodule.restrictScalars ℚ ↔ _
  rw [← Submodule.restrictScalars_sup]
  rfl

include hlayers in

theorem simultaneous_real_grade_correction {η : Type*}
    (U : η → LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (hU : ∀ i, BasisGradedSubmodule (b.baseChange ℝ) w (U i).toSubmodule)
    (k : ℕ) (X E₀ R₀ A D : F.realification.Group)
    (hY : ∀ i, (E₀⁻¹ * X * R₀⁻¹).coord ∈ (U i).toSubmodule ⊔ (F.realLayer k).toSubmodule)
    (hA : A.coord ∈ F.realification.layer k)
    (hD : D.coord ∈ F.realification.layer k)
    (hgrade : ∀ i, basisGradeProjection (b.baseChange ℝ) w k (E₀⁻¹ * X * R₀⁻¹).coord -
      basisGradeProjection (b.baseChange ℝ) w k A.coord -
      basisGradeProjection (b.baseChange ℝ) w k D.coord ∈ U i) :
    (E₀ * A) * (A⁻¹ * (E₀⁻¹ * X * R₀⁻¹) * D⁻¹) * (D * R₀) = X ∧
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) (E₀ * A) =
        NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) E₀ ∧
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) (D * R₀) =
        NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) R₀ ∧
      ∀ i, (A⁻¹ * (E₀⁻¹ * X * R₀⁻¹) * D⁻¹).coord ∈
        (U i).toSubmodule ⊔ (F.realLayer (k + 1)).toSubmodule := by
  have hqA : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) A = 1 := by
    apply NilpotentLieBCHGroup.ext
    exact (lieQuotientMap_eq_zero (F.realification.layerIdeal k) _).mpr hA
  have hqD : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) D = 1 := by
    apply NilpotentLieBCHGroup.ext
    exact (lieQuotientMap_eq_zero (F.realification.layerIdeal k) _).mpr hD
  refine ⟨by group, ?_, ?_, ?_⟩
  · rw [map_mul, hqA, mul_one]
  · rw [map_mul, hqD, one_mul]
  · intro i
    exact F.real_corrected_middle_mem_next_layer b w hlayers (U i).toSubmodule (hU i) k
      (E₀⁻¹ * X * R₀⁻¹) A D (hY i) hA hD (hgrade i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

theorem basisBelowProjection_succ {K L ι : Type*} [Field K] [AddCommGroup L] [Module K L]
    (b : Basis ι K L) (w : ι → ℕ) (j : ℕ) (x : L) :
    basisBelowProjection b w (j + 1) x =
      basisBelowProjection b w j x + basisGradeProjection b w j x := by
  rw [basisBelowProjection_eq_sum_grades, Finset.sum_range_succ,
    ← basisBelowProjection_eq_sum_grades]

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem real_current_bracket_remainder (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (j : ℕ)
    (x k : ℝ ⊗[ℚ] L) (hk : k ∈ F.realification.layer 1)
    (hlower : ∀ d < j, ⁅basisGradeProjection (b.baseChange ℝ) w d x, k⁆ ∈ V) :
    ⁅x - basisGradeProjection (b.baseChange ℝ) w j x, k⁆ ∈
      V ⊔ (F.realLayer (j + 2)).toSubmodule := by
  have hlow : ⁅basisBelowProjection (b.baseChange ℝ) w j x, k⁆ ∈ V := by
    rw [basisBelowProjection_eq_sum_grades, sum_lie]
    exact V.sum_mem (fun d hd => hlower d (Finset.mem_range.mp hd))
  have hhigh : ⁅x - basisBelowProjection (b.baseChange ℝ) w (j + 1) x, k⁆ ∈
      F.realification.layer (j + 2) := by
    have h := F.realification.lie_mem (i := j + 1) (j := 1)
      (F.sub_realGradeTruncation_mem b w hlayers (j + 1) x) hk
    simpa only [Nat.add_assoc] using h
  have h := (V ⊔ (F.realLayer (j + 2)).toSubmodule).add_mem
    (Submodule.mem_sup_right hhigh) (Submodule.mem_sup_left hlow)
  rw [basisBelowProjection_succ, sub_lie, add_lie] at h
  convert h using 1
  rw [sub_lie]
  abel

include hlayers in
theorem realGradeProjection_mem_of_mem_sup_next
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (j : ℕ) (x : ℝ ⊗[ℚ] L) (hx : x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    basisGradeProjection (b.baseChange ℝ) w j x ∈ V := by
  obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers j z hz, add_zero]
  exact hV j v hv

include hlayers in
theorem real_mem_of_homogeneous_mem_sup_next
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (j : ℕ) (x : ℝ ⊗[ℚ] L) (hgrade : basisGradeProjection (b.baseChange ℝ) w j x = x)
    (hx : x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule) : x ∈ V := by
  have h := F.realGradeProjection_mem_of_mem_sup_next b w hlayers V hV j x hx
  rwa [hgrade] at h

include hlayers in
theorem real_correction_preserves_grades_below (j : ℕ) (a g c : F.realification.Group)
    (ha : a.coord ∈ F.realification.layer j) (hc : c.coord ∈ F.realification.layer j) :
    ∀ d < j, basisGradeProjection (b.baseChange ℝ) w d (a⁻¹ * g * c⁻¹).coord =
      basisGradeProjection (b.baseChange ℝ) w d g.coord := by
  have hdiff : (a⁻¹ * g * c⁻¹).coord - g.coord ∈ F.realification.layer j := by
    have h := F.realification.correction_removal_preserves_lower_layers (j := j + 1)
      a g c (by simpa using ha) (by simpa using hc) (by omega)
    simpa only [Nat.add_sub_cancel] using h
  intro d hd
  have hz := F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers d _
    (F.realification.antitone (Nat.succ_le_of_lt hd) hdiff)
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

include hlayers in
theorem real_correction_current_grade (j : ℕ) (a g c : F.realification.Group)
    (ha : a.coord ∈ F.realification.layer j) (hc : c.coord ∈ F.realification.layer j) :
    basisGradeProjection (b.baseChange ℝ) w j (a⁻¹ * g * c⁻¹).coord =
      basisGradeProjection (b.baseChange ℝ) w j g.coord -
        basisGradeProjection (b.baseChange ℝ) w j a.coord -
        basisGradeProjection (b.baseChange ℝ) w j c.coord := by
  have h := F.realGradeProjection_bch_triple b w hlayers j (-a.coord) g.coord (-c.coord)
    ((F.realification.layer j).neg_mem ha) ((F.realification.layer j).neg_mem hc)
  change basisGradeProjection (b.baseChange ℝ) w j (a⁻¹ * g * c⁻¹).coord = _ at h
  rw [h, map_neg, map_neg]
  abel

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

section Rational

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adjoint_correction_sub_mem_layer (hs : 2 ≤ s) (j : ℕ)
    (a : F.Group) (ha : a.coord ∈ F.layer j) (x : L) :
    dualAdjoint a x - x ∈ F.layer (j + 1) := by
  have hx : x ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hrem := F.dualAdjoint_sub_first_bracket_mem_layer hs a ha x hx
  have hsmall : dualAdjoint a x - (x + ⁅a.coord, x⁆) ∈ F.layer (j + 1) :=
    F.antitone (by omega) hrem
  have hbr : ⁅a.coord, x⁆ ∈ F.layer (j + 1) := F.lie_mem ha hx
  convert (F.layer (j + 1)).add_mem hsmall hbr using 1
  abel

end Rational

section Real

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

end Real
end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolGradeEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realGradedSymbolPolynomial_gradeProjection_coefficient
    (d : ℕ) (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (F.realGradedSymbolPolynomial b ω hlayers w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
        (fun z => ω z.val.2) d x)) α =
      basisGradeProjection ((F.associatedGradedBasis b ω hlayers).baseChange ℝ) ω d
        (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) := by
  apply ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr.injective
  ext i
  rw [basisGradeProjection_repr]
  by_cases h : Finsupp.weight w α = ω i
  · rw [F.realGradedSymbolPolynomial_coordinate b ω hlayers w _ ⟨(α, i), h⟩,
      basisGradeProjection_repr,
      F.realGradedSymbolPolynomial_coordinate b ω hlayers w x ⟨(α, i), h⟩]
  · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w _ α i h,
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w x α i h]
    simp

theorem realGradedSymbolPolynomial_gradeProjection
    (d : ℕ) (x : F.RealPolynomialSymbol w) :
    F.realGradedSymbolPolynomial b ω hlayers w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
        (fun z => ω z.val.2) d x) =
      VectorPolynomial.map
        ((basisGradeProjection ((F.associatedGradedBasis b ω hlayers).baseChange ℝ)
          ω d).restrictScalars ℚ)
        (F.realGradedSymbolPolynomial b ω hlayers w x) := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  exact F.realGradedSymbolPolynomial_gradeProjection_coefficient b ω hlayers w d x α

theorem realGradedSymbolPolynomial_gradeProjection_homogeneous
    (d : ℕ) (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ)
    (hα : Finsupp.weight w α ≠ d) :
    coefficients (F.realGradedSymbolPolynomial b ω hlayers w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
        (fun z => ω z.val.2) d x)) α = 0 := by
  rw [F.realGradedSymbolPolynomial_gradeProjection_coefficient]
  apply ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr.injective
  ext i
  simp only [basisGradeProjection_repr, map_zero, Finsupp.zero_apply]
  split_ifs with hi
  · exact F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w x α i
      (fun h => hα (h.trans hi))
  · rfl

theorem realGradedSymbolPolynomial_eval₂_gradeProjection
    (d : ℕ) (x : F.RealPolynomialSymbol w) (t : σ → ℝ) :
    eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
        (fun z => ω z.val.2) d x)) =
      basisGradeProjection ((F.associatedGradedBasis b ω hlayers).baseChange ℝ) ω d
        (eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x)) := by
  rw [F.realGradedSymbolPolynomial_gradeProjection, eval₂_map]

noncomputable def realSymbolGradeEvaluation (d : ℕ) (t : σ → ℝ) :
    F.RealPolynomialSymbol w →ₗ[ℚ] (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  (eval₂ t).comp ((F.realGradedSymbolPolynomial b ω hlayers w).toLinearMap.comp
    ((basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
      (fun z => ω z.val.2) d).restrictScalars ℚ))

@[simp] theorem realSymbolGradeEvaluation_apply (d : ℕ) (t : σ → ℝ)
    (x : F.RealPolynomialSymbol w) :
    F.realSymbolGradeEvaluation b ω hlayers w d t x =
      eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
        (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
          (fun z => ω z.val.2) d x)) := rfl

theorem realSymbolGradeEvaluation_eq_projection (d : ℕ) (t : σ → ℝ)
    (x : F.RealPolynomialSymbol w) :
    F.realSymbolGradeEvaluation b ω hlayers w d t x =
      basisGradeProjection ((F.associatedGradedBasis b ω hlayers).baseChange ℝ) ω d
        (eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x)) :=
  F.realGradedSymbolPolynomial_eval₂_gradeProjection b ω hlayers w d x t

theorem realSymbolGradeEvaluation_homogeneous (d : ℕ) (t : σ → ℝ)
    (x : F.RealPolynomialSymbol w) :
    basisGradeProjection ((F.associatedGradedBasis b ω hlayers).baseChange ℝ) ω d
      (F.realSymbolGradeEvaluation b ω hlayers w d t x) =
        F.realSymbolGradeEvaluation b ω hlayers w d t x := by
  simp only [F.realSymbolGradeEvaluation_eq_projection]
  exact basisCoordinateProjection_idempotent
    ((F.associatedGradedBasis b ω hlayers).baseChange ℝ) {i | ω i = d} _

theorem realSymbolGradeEvaluation_current_correction (d : ℕ) (t : σ → ℝ)
    (a g c : F.RealPolynomialSymbolGroup w)
    (ha : a.coord ∈ (F.polynomialSymbolFiltration w).realification.layer d)
    (hc : c.coord ∈ (F.polynomialSymbolFiltration w).realification.layer d) :
    F.realSymbolGradeEvaluation b ω hlayers w d t (a⁻¹ * g * c⁻¹).coord =
      F.realSymbolGradeEvaluation b ω hlayers w d t g.coord -
        F.realSymbolGradeEvaluation b ω hlayers w d t a.coord -
        F.realSymbolGradeEvaluation b ω hlayers w d t c.coord := by
  have h := (F.polynomialSymbolFiltration w).real_correction_current_grade
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) d a g c ha hc
  have he := congrArg (fun x => eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x)) h
  simpa only [realSymbolGradeEvaluation_apply, map_sub] using he

theorem realSymbolGradeEvaluation_correction_below (d : ℕ) (t : σ → ℝ)
    (a g c : F.RealPolynomialSymbolGroup w)
    (ha : a.coord ∈ (F.polynomialSymbolFiltration w).realification.layer d)
    (hc : c.coord ∈ (F.polynomialSymbolFiltration w).realification.layer d)
    (j : ℕ) (hj : j < d) :
    F.realSymbolGradeEvaluation b ω hlayers w j t (a⁻¹ * g * c⁻¹).coord =
      F.realSymbolGradeEvaluation b ω hlayers w j t g.coord := by
  have h := (F.polynomialSymbolFiltration w).real_correction_preserves_grades_below
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) d a g c ha hc j hj
  exact congrArg (fun x => eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x)) h

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RestrictedGradePathMembership
namespace OAI

section

namespace Erdos3

theorem reset_splitting_in_quotient {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) (H : Subgroup G) (E P R E₀ R₀ A D : G)
    (hP : P ∈ H) (hA : A ∈ H) (hD : D ∈ H)
    (hAq : φ A = φ (E₀⁻¹ * E)) (hDq : φ D = φ (R * R₀⁻¹)) :
    (E * A⁻¹) * (A * P * D) * (D⁻¹ * R) = E * P * R ∧
      A * P * D ∈ H ∧ φ (E * A⁻¹) = φ E₀ ∧ φ (D⁻¹ * R) = φ R₀ := by
  refine ⟨?_, H.mul_mem (H.mul_mem hA hP) hD, ?_, ?_⟩
  · group
  · rw [map_mul, map_inv, hAq, map_mul, map_inv]
    group
  · rw [map_mul, map_inv, hDq, map_mul, map_inv]
    group

namespace NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem reset_real_splitting (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule)
    (j : ℕ) (E P R E₀ R₀ : F.realification.Group)
    (hP : P.coord ∈ U)
    (hleft : NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) (E₀⁻¹ * E) ∈
      (NilpotentLieBCHGroup.realLieSubgroup (hnil := F.realification.lowerCentralSeries_eq_bot) U).map
        (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j)))
    (hright : NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) (R * R₀⁻¹) ∈
      (NilpotentLieBCHGroup.realLieSubgroup (hnil := F.realification.lowerCentralSeries_eq_bot) U).map
        (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j))) :
    let A := F.truncateRealGrades b w j (E₀⁻¹ * E)
    let D := F.truncateRealGrades b w j (R * R₀⁻¹)
    (E * A⁻¹) * (A * P * D) * (D⁻¹ * R) = E * P * R ∧
      (A * P * D).coord ∈ U ∧
      NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) (E * A⁻¹) =
        NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) E₀ ∧
      NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) (D⁻¹ * R) =
        NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) R₀ := by
  exact reset_splitting_in_quotient
    (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j))
    (NilpotentLieBCHGroup.realLieSubgroup (hnil := F.realification.lowerCentralSeries_eq_bot) U) E P R E₀ R₀
    (F.truncateRealGrades b w j (E₀⁻¹ * E)) (F.truncateRealGrades b w j (R * R₀⁻¹)) hP
    (F.truncateRealGrades_mem_of_quotient_mem b w hlayers U hU j _ hleft)
    (F.truncateRealGrades_mem_of_quotient_mem b w hlayers U hU j _ hright)
    (F.truncateRealGrades_quotient b w hlayers j _) (F.truncateRealGrades_quotient b w hlayers j _)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_symbol_reset_bounds (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ E E₀ R R₀ : F.RealPolynomialSymbolGroup w,
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E₀ →
          F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l R₀ →
        ∀ j : ℕ,
          let A := F.truncateRealSymbol b ω hlayers w j (E₀⁻¹ * E)
          let D := F.truncateRealSymbol b ω hlayers w j (R * R₀⁻¹)
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) (E * A⁻¹) ∧
            F.SymbolRationalGrid b ω hlayers w m (D⁻¹ * R) := by
  obtain ⟨c₁, _, hslow₁⟩ := exists_symbol_slow_product_bound s a 2
  obtain ⟨c₂, _, hslow₂⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨cr, _, hrat⟩ := exists_symbol_rational_product_bound s 2
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ a + (Polynomial.X + Polynomial.C c₁) ^ c₁ +
    (Polynomial.X + Polynomial.C cr) ^ cr + Polynomial.X + 2
  let B : Polynomial ℕ := (Q + Polynomial.C c₂) ^ c₂ + (Q + Polynomial.C cr) ^ cr
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H l p hH hl hp hι hσ hHp hlp hb T hT
  let q : ℝ := (p + 2) ^ a + (p + c₁) ^ c₁ + (p + cr) ^ cr + p + 2
  have ha0 : 0 ≤ (p + 2) ^ a := by positivity
  have hs0 : 0 ≤ (p + c₁) ^ c₁ := by positivity
  have hr0 : 0 ≤ (p + cr) ^ cr := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have haq : (p + 2) ^ a ≤ q + 2 := by dsimp [q]; linarith
  have hsq : (p + c₁) ^ c₁ ≤ q + 2 := by dsimp [q]; linarith
  have hrq : (p + cr) ^ cr ≤ q := by dsimp [q]; linarith
  have hboth : (q + c₂) ^ c₂ + (q + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hbound p hp
  have hsfinal : (q + c₂) ^ c₂ ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hboth
  have hrfinal : (q + cr) ^ cr ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hboth
  obtain ⟨m₁, hm₁, hm₁p, hlm₁, hproducts₁⟩ := hrat F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  obtain ⟨m₂, hm₂, hm₂p, hm₁m₂, hproducts₂⟩ := hrat F b ω hlayers w hw H q hH hq
    (hι.trans hpq) (hσ.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq)) hb m₁ hm₁
    (hm₁p.trans (Real.exp_le_exp.mpr hrq))
  refine ⟨m₂, hm₂, hm₂p.trans (Real.exp_le_exp.mpr hrfinal), hlm₁.trans hm₁m₂, ?_⟩
  intro E E₀ R R₀ hE hE₀ hR hR₀
  have hA : F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + c₁) ^ c₁)) (E₀⁻¹ * E) := by
    have hi : ∀ g ∈ [E₀⁻¹, E], F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact (F.symbolSlowBound_inv_iff b ω hlayers w T _ E₀).mpr hE₀
      · exact hE
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hslow₁ F b ω hlayers w hw H p hH hp hι hσ hHp hb T hT [E₀⁻¹, E] (by simp) hi
  have hD : F.SymbolRationalGrid b ω hlayers w m₁ (R * R₀⁻¹) := by
    have hi : ∀ g ∈ [R, R₀⁻¹], F.SymbolRationalGrid b ω hlayers w l g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hR
      · exact F.symbolRationalGrid_inv b ω hlayers w l hR₀
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts₁ [R, R₀⁻¹] (by simp) hi
  intro j
  dsimp only
  constructor
  · have hi : ∀ g ∈ [E, (F.truncateRealSymbol b ω hlayers w j (E₀⁻¹ * E))⁻¹],
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((q + 2) ^ 1)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact F.symbolSlowBound_mono b ω hlayers w T hT (Real.exp_le_exp.mpr (by simpa using haq)) _ hE
      · apply (F.symbolSlowBound_inv_iff b ω hlayers w T _ _).mpr
        exact F.symbolSlowBound_mono b ω hlayers w T hT (Real.exp_le_exp.mpr (by simpa using hsq)) _
          (F.truncateRealSymbol_slow b ω hlayers w j _ T _ hA)
    have hnew := hslow₂ F b ω hlayers w hw H q hH hq (hι.trans hpq) (hσ.trans hpq)
      (hHp.trans (Real.exp_le_exp.mpr hpq)) hb T hT
      [E, (F.truncateRealSymbol b ω hlayers w j (E₀⁻¹ * E))⁻¹] (by simp) hi
    simp only [List.prod_cons, List.prod_nil, mul_one] at hnew
    exact F.symbolSlowBound_mono b ω hlayers w T hT (Real.exp_le_exp.mpr hsfinal) _ hnew
  · have hi : ∀ g ∈ [(F.truncateRealSymbol b ω hlayers w j (R * R₀⁻¹))⁻¹, R],
        F.SymbolRationalGrid b ω hlayers w m₁ g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact F.symbolRationalGrid_inv b ω hlayers w m₁
          (F.truncateRealSymbol_rational b ω hlayers w j _ m₁ hD)
      · exact F.symbolRationalGrid_mono b ω hlayers w hl hlm₁ _ hR
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hproducts₂ [(F.truncateRealSymbol b ω hlayers w j (R * R₀⁻¹))⁻¹, R] (by simp) hi

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

abbrev RealSymbolGradeQuotientGroup (j : ℕ) :=
  NilpotentLieBCHGroup
    (F.RealPolynomialSymbol w ⧸ (F.polynomialSymbolFiltration w).realification.layerIdeal j) s
    (lie_quotient_lowerCentralSeries_eq_bot
      (realification_lowerCentralSeries_eq_bot (F.polynomialSymbol_lowerCentralSeries_eq_bot w))
      ((F.polynomialSymbolFiltration w).realification.layerIdeal j))

noncomputable def realSymbolGradeQuotientHom (j : ℕ) :
    F.RealPolynomialSymbolGroup w →* F.RealSymbolGradeQuotientGroup w j :=
  NilpotentLieBCHGroup.quotientHom ((F.polynomialSymbolFiltration w).realification.layerIdeal j)

theorem reset_real_symbol_splitting (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.PolynomialSymbol w))
    (hU : BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w)
      (fun z => ω z.val.2) U.toSubmodule)
    (j : ℕ) (E P R E₀ R₀ : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hleft : F.realSymbolGradeQuotientHom w j (E₀⁻¹ * E) ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w j))
    (hright : F.realSymbolGradeQuotientHom w j (R * R₀⁻¹) ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w j)) :
    let A := F.truncateRealSymbol b ω hlayers w j (E₀⁻¹ * E)
    let D := F.truncateRealSymbol b ω hlayers w j (R * R₀⁻¹)
    (E * A⁻¹) * (A * P * D) * (D⁻¹ * R) = E * P * R ∧
      (A * P * D).coord ∈ realificationLieSubalgebra U ∧
      F.realSymbolGradeQuotientHom w j (E * A⁻¹) = F.realSymbolGradeQuotientHom w j E₀ ∧
      F.realSymbolGradeQuotientHom w j (D⁻¹ * R) = F.realSymbolGradeQuotientHom w j R₀ := by
  have hUreal : BasisGradedSubmodule ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
      (fun z => ω z.val.2) (realificationLieSubalgebra U).toSubmodule :=
    hU.baseChange (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2) U.toSubmodule
  exact (F.polynomialSymbolFiltration w).reset_real_splitting
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) (realificationLieSubalgebra U) hUreal
    j E P R E₀ R₀ hP hleft hright

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_controlled_symbol_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ U : LieSubalgebra ℚ (F.PolynomialSymbol w),
        BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2) U.toSubmodule →
        ∀ (j : ℕ) (E P R E₀ R₀ : F.RealPolynomialSymbolGroup w),
        P.coord ∈ realificationLieSubalgebra U →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E₀ →
        F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l R₀ →
        F.realSymbolGradeQuotientHom w j (E₀⁻¹ * E) ∈
          (NilpotentLieBCHGroup.realificationSubgroup
            (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w j) →
        F.realSymbolGradeQuotientHom w j (R * R₀⁻¹) ∈
          (NilpotentLieBCHGroup.realificationSubgroup
            (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w j) →
        let A := F.truncateRealSymbol b ω hlayers w j (E₀⁻¹ * E)
        let D := F.truncateRealSymbol b ω hlayers w j (R * R₀⁻¹)
        (E * A⁻¹) * (A * P * D) * (D⁻¹ * R) = E * P * R ∧
          (A * P * D).coord ∈ realificationLieSubalgebra U ∧
          F.realSymbolGradeQuotientHom w j (E * A⁻¹) = F.realSymbolGradeQuotientHom w j E₀ ∧
          F.realSymbolGradeQuotientHom w j (D⁻¹ * R) = F.realSymbolGradeQuotientHom w j R₀ ∧
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) (E * A⁻¹) ∧
          F.SymbolRationalGrid b ω hlayers w m (D⁻¹ * R) := by
  obtain ⟨C, hC, hbound⟩ := exists_symbol_reset_bounds s a
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H l p hH hl hp hι hσ hHp hlp hb T hT
  obtain ⟨m, hm, hmp, hlm, hreset⟩ := hbound F b ω hlayers w hw H l p hH hl hp hι hσ hHp hlp hb T hT
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro U hU j E P R E₀ R₀ hP hE hE₀ hR hR₀ hleft hright
  obtain ⟨hprod, hmid, hEeq, hReq⟩ := F.reset_real_symbol_splitting w b ω hlayers U hU j E P R E₀ R₀ hP hleft hright
  obtain ⟨hslow, hgrid⟩ := hreset E E₀ R R₀ hE hE₀ hR hR₀ j
  exact ⟨hprod, hmid, hEeq, hReq, hslow, hgrid⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3
open Module VectorPolynomial
open scoped TensorProduct BigOperators

namespace VectorPolynomial

end VectorPolynomial

namespace NilpotentLieFiltration
variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem truncateRealSymbol_mem_of_grade_values
    (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.RealPolynomialSymbolGroup w) (k : ℕ)
    (hx : ∀ t : σ → ℝ, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t x.coord ∈ realificationLieSubalgebra U) :
    (F.truncateRealSymbol b ω hF w k x).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) := by
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w U _).mpr
  intro t
  rw [F.truncateRealSymbol_coord, basisBelowProjection_eq_sum_grades]
  simp only [map_sum]
  apply (realificationLieSubalgebra U).toSubmodule.sum_mem
  intro j hj
  exact hx t j (Finset.mem_range.mp hj)

theorem realSymbolGradeQuotient_mem_of_grade_values
    (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.RealPolynomialSymbolGroup w) (k : ℕ)
    (hx : ∀ t : σ → ℝ, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t x.coord ∈ realificationLieSubalgebra U) :
    F.realSymbolGradeQuotientHom w k x ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
        (F.symbolPointwiseSubalgebra b ω hF w U)).map (F.realSymbolGradeQuotientHom w k) := by
  apply Subgroup.mem_map.mpr
  refine ⟨F.truncateRealSymbol b ω hF w k x,
    F.truncateRealSymbol_mem_of_grade_values b ω hF w U x k hx, ?_⟩
  exact F.truncateRealSymbol_quotient b ω hF w k x

theorem realSymbolGradeQuotient_mem_of_restricted_path
    (w : σ → ℕ) (v : τ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (K : Set (σ → ℝ)) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ u : τ → ℝ, (fun i => MvPolynomial.eval u (β i)) ∈ K)
    (x : F.RealPolynomialSymbol w) (y : F.RealPolynomialSymbolGroup v) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t x ∈ realificationLieSubalgebra U)
    (hy : ∀ u : τ → ℝ, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF v j u y.coord =
        F.realSymbolGradeEvaluation b ω hF w j
          (fun i => MvPolynomial.eval u (β i)) x) :
    F.realSymbolGradeQuotientHom v k y ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot v)
        (F.symbolPointwiseSubalgebra b ω hF v U)).map (F.realSymbolGradeQuotientHom v k) := by
  apply F.realSymbolGradeQuotient_mem_of_grade_values b ω hF v U y k
  intro u j hj
  rw [hy u j hj]
  exact hx _ (hβ u) j hj

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledLinearSubspaceLift
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem exists_block_subspace_defining_matrix
    {ι κ δ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (b : Basis ι ℚ L) (c : ι → δ) (U : Submodule ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U) (hU : BasisBlockInvariant b c U)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H) :
    ∃ Q : Matrix ι ι ℚ,
      (∀ i j, RationalHeightLE (Q i j)
        (imageDefiningHeight (Fintype.card ι * Fintype.card κ) (Fintype.card ι) H)) ∧
      (∀ i j, c i ≠ c j → Q i j = 0) ∧
      ∀ x : ℝ ⊗[ℚ] L,
        (fun i j => (Q i j : ℝ)) *ᵥ (b.baseChange ℝ).equivFun x = 0 ↔ x ∈ U.baseChange ℝ := by
  classical
  let v' := blockSpanningFamily b c v
  let A : Matrix ι (ι × κ) ℚ := fun i z => b.repr (v' z) i
  have hA : ∀ i z, RationalHeightLE (A i z) H :=
    fun i z => blockSpanningFamily_height b c v hH hv z i
  have hAb : ∀ i z, c i ≠ c z.1 → A i z = 0 := by
    intro i z hz
    change b.repr (blockSpanningFamily b c v z) i = 0
    rw [blockSpanningFamily_repr, if_neg hz]
  obtain ⟨Q, hQ, hQb, hker⟩ := exists_real_block_span_defining_matrix c (fun z : ι × κ => c z.1) A hAb hH hA
  refine ⟨Q, ?_, hQb, ?_⟩
  · simpa only [Fintype.card_prod] using hQ
  · intro x
    have hsp := blockSpanningFamily_span b c U v hspan hU
    rw [← real_span_rational_family U v' hsp, real_span_family_mem_iff_coordinates b v' x,
      real_column_span_mem_iff A]
    change (b.baseChange ℝ).equivFun x ∈ LinearMap.ker (Matrix.mulVecLin (fun i j => (Q i j : ℝ))) ↔ _
    rw [hker]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem exists_controlled_weighted_linear_splitting
    {ι κ δ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → δ) (c : κ → δ) (A : Matrix ι κ ℚ)
    (hblock : ∀ i j, r i ≠ c j → A i j = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (S : Matrix κ ι ℚ) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧ l ∣ m ∧
      (∀ i j, c i ≠ r j → S i j = 0) ∧
      ∀ (W : δ → ℝ), (∀ d, 0 < W d) → (∀ i, Real.exp (separationBudget p) ≤ W (r i)) →
      ∀ (a b : ι → ℝ) (v : κ → ℝ),
      (∀ i, |a i| ≤ Real.exp p / W (r i)) → b ∈ realDenominatorGrid l →
      (fun i j => (A i j : ℝ)) *ᵥ v = a + b →
      (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ a) = a ∧
      (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ b) = b ∧
      (∀ i, |((fun i j => (S i j : ℝ)) *ᵥ a) i| ≤
        Real.exp ((p + 2) ^ 18 + p) / W (c i)) ∧
      (fun i j => (S i j : ℝ)) *ᵥ b ∈ realDenominatorGrid m ∧
      (fun i j => (A i j : ℝ)) *ᵥ
        (v - (fun i j => (S i j : ℝ)) *ᵥ a - (fun i j => (S i j : ℝ)) *ᵥ b) = 0 := by
  obtain ⟨S, hS, hSb, hSH⟩ := exists_bounded_block_image_section r c A hblock hH hA
  refine ⟨S, matrixDenominator S * l, Nat.mul_pos (matrixDenominator_pos S) hl,
    real_image_section_denominator_bound S H l hSH hp hι hκ hHp hlp,
    ⟨matrixDenominator S, Nat.mul_comm _ _⟩, hSb, ?_⟩
  intro W hW hWmin a b v ha hb hv
  have hanorm : ‖a‖ ≤ Real.exp p / Real.exp (separationBudget p) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    apply (show ‖a i‖ ≤ Real.exp p / W (r i) by simpa only [Real.norm_eq_abs] using ha i).trans
    exact div_le_div_of_nonneg_left (Real.exp_nonneg p) (Real.exp_pos _) (hWmin i)
  have hsum : a + b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) :=
    (real_column_span_mem_iff A (a + b)).mpr ⟨v, hv⟩
  obtain ⟨haspan, hbspan⟩ := controlled_small_vector_separation A hH hl hA hp hι hκ hHp hlp a b hanorm hb hsum
  have hSa := real_matrix_image_section_apply A S hS a ((real_column_span_mem_iff A a).mp haspan)
  have hSb' := real_matrix_image_section_apply A S hS b ((real_column_span_mem_iff A b).mp hbspan)
  refine ⟨hSa, hSb', ?_, real_matrix_denominator_grid S l b hb, ?_⟩
  · intro i
    simpa only [← Real.exp_add] using
      real_image_section_weighted_bound r c S H hSb hSH hp hι hκ hHp W hW (Real.exp_nonneg p) a ha i
  · change Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
      (v - Matrix.of (fun i j => (S i j : ℝ)) *ᵥ a - Matrix.of (fun i j => (S i j : ℝ)) *ᵥ b) = 0
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
    exact (congrArg₂ (fun x y : ι → ℝ => x - y)
      (congrArg₂ (fun x y : ι → ℝ => x - y) hv hSa) hSb').trans (by abel)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem exists_controlled_constraint_section
    {ι κ μ δ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (r : ι → δ) (c : κ → δ) (t : μ → δ)
    (Q : Matrix ι κ ℚ) (P : Matrix μ κ ℚ)
    (hQblock : ∀ i j, r i ≠ c j → Q i j = 0)
    (hPblock : ∀ i j, t i ≠ c j → P i j = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hQ : ∀ i j, RationalHeightLE (Q i j) H)
    (hP : ∀ i j, RationalHeightLE (P i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (ι ⊕ μ) : ℝ) ≤ p)
    (hcols : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (T : Matrix κ μ ℚ) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧ l ∣ m ∧
      (∀ i j, c i ≠ t j → T i j = 0) ∧
      (∀ i j, RationalHeightLE (T i j) (rationalKernelHeight (Fintype.card (ι ⊕ μ)) H)) ∧
      (∀ y : μ → ℝ,
        (∃ x : κ → ℝ, (fun i j => (Q i j : ℝ)) *ᵥ x = 0 ∧
          (fun i j => (P i j : ℝ)) *ᵥ x = y) →
        (fun i j => (Q i j : ℝ)) *ᵥ ((fun i j => (T i j : ℝ)) *ᵥ y) = 0 ∧
          (fun i j => (P i j : ℝ)) *ᵥ ((fun i j => (T i j : ℝ)) *ᵥ y) = y) ∧
      (∀ (W : δ → ℝ), (∀ d, 0 < W d) → ∀ (M : ℝ), 0 ≤ M →
        ∀ y : μ → ℝ, (∀ i, |y i| ≤ M / W (t i)) →
          ∀ i, |((fun i j => (T i j : ℝ)) *ᵥ y) i| ≤
            Real.exp ((p + 2) ^ 18) * M / W (c i)) ∧
      (∀ y : μ → ℝ, y ∈ realDenominatorGrid l →
        (fun i j => (T i j : ℝ)) *ᵥ y ∈ realDenominatorGrid m) := by
  let A := constraintProjectionMatrix Q P
  have hAblock : ∀ i j, Sum.elim r t i ≠ c j → A i j = 0 := by
    intro i j hij
    cases i with
    | inl i => exact hQblock i j hij
    | inr i => exact hPblock i j hij
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    intro i j
    cases i with
    | inl i => exact hQ i j
    | inr i => exact hP i j
  obtain ⟨S, hS, hSblock, hSH⟩ :=
    exists_bounded_block_image_section (Sum.elim r t) c A hAblock hH hA
  let T : Matrix κ μ ℚ := fun i j => S i (Sum.inr j)
  have hTS (y : μ → ℝ) :
      (fun i j => (S i j : ℝ)) *ᵥ constraintProjectionInput (ι := ι) y =
        (fun i j => (T i j : ℝ)) *ᵥ y :=
    mulVec_constraintProjectionInput _ y
  refine ⟨T, matrixDenominator S * l, Nat.mul_pos (matrixDenominator_pos S) hl,
    real_image_section_denominator_bound S H l hSH hp hrows hcols hHp hlp,
    ⟨matrixDenominator S, Nat.mul_comm _ _⟩,
    (fun i j hij => hSblock i (Sum.inr j) hij), (fun i j => hSH i (Sum.inr j)), ?_, ?_, ?_⟩
  · intro y hy
    have hAy : constraintProjectionInput (ι := ι) y ∈
        LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
      obtain ⟨x, hxQ, hxP⟩ := hy
      refine ⟨x, ?_⟩
      funext i
      cases i with
      | inl i => exact congrFun hxQ i
      | inr i => exact congrFun hxP i
    have he := real_matrix_image_section_apply A S hS _ hAy
    rw [hTS] at he
    constructor
    · funext i
      exact congrFun he (Sum.inl i)
    · funext i
      exact congrFun he (Sum.inr i)
  · intro W hW M hM y hy i
    have hh := real_image_section_weighted_bound (Sum.elim r t) c S H hSblock hSH
      hp hrows hcols hHp W hW hM (constraintProjectionInput (ι := ι) y)
      (constraintProjectionInput_weighted r t W hW hM y hy) i
    rwa [hTS] at hh
  · intro y hy
    have hh := real_matrix_denominator_grid S l (constraintProjectionInput (ι := ι) y)
      (constraintProjectionInput_grid l y hy)
    rwa [hTS] at hh

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

variable {η ι δ : Type*} [Fintype ι]

noncomputable def jointMatrixImages (Q : η → Matrix ι ι ℚ) (x : η → ι → ℝ) : (Σ _ : η, ι) → ℝ :=
  fun bi => ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ x bi.1) bi.2

theorem jointMatrixImages_grid [Fintype η] (Q : η → Matrix ι ι ℚ) (l : ℕ)
    (x : η → ι → ℝ) (hx : ∀ b, x b ∈ realDenominatorGrid l) :
    jointMatrixImages Q x ∈ realDenominatorGrid (matrixDenominator (jointMatrix Q) * l) := by
  classical
  choose z hz using hx
  let A := jointMatrix Q
  have hcoef (bi : Σ _ : η, ι) (j : ι) :
      ((clearedMatrix A bi j : ℤ) : ℝ) = (matrixDenominator A : ℝ) * (Q bi.1 bi.2 j : ℝ) := by
    have h := congrFun (congrFun (clearedMatrix_cast A) bi) j
    change ((clearedMatrix A bi j : ℤ) : ℚ) = (matrixDenominator A : ℚ) * Q bi.1 bi.2 j at h
    exact_mod_cast h
  refine ⟨fun bi => ∑ j, clearedMatrix A bi j * z bi.1 j, ?_⟩
  funext bi
  change ((∑ j, clearedMatrix A bi j * z bi.1 j : ℤ) : ℝ) =
    ((matrixDenominator A * l : ℕ) : ℝ) * ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ x bi.1) bi.2
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (z bi.1 j : ℝ) = (l : ℝ) * x bi.1 j := congrFun (hz bi.1) j
  rw [hcoef, hj]
  ring

theorem jointMatrixImages_equation (Q : η → Matrix ι ι ℚ) (e r : η → ι → ℝ) (v : ι → ℝ)
    (h : ∀ b, (fun i j => (Q b i j : ℝ)) *ᵥ (v - e b - r b) = 0) :
    (fun bi j => (jointMatrix Q bi j : ℝ)) *ᵥ v = jointMatrixImages Q e + jointMatrixImages Q r := by
  funext bi
  have hb := h bi.1
  change Matrix.of (fun i j => (Q bi.1 i j : ℝ)) *ᵥ (v - e bi.1 - r bi.1) = 0 at hb
  rw [Matrix.mulVec_sub, Matrix.mulVec_sub] at hb
  have hb' := congrFun hb bi.2
  change ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ v) bi.2 -
    ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ e bi.1) bi.2 -
    ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ r bi.1) bi.2 = 0 at hb'
  change ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ v) bi.2 =
    ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ e bi.1) bi.2 +
    ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ r bi.1) bi.2
  linarith

theorem exists_joint_weighted_corrections [Fintype η]
    (c : ι → δ) (Q : η → Matrix ι ι ℚ)
    (hblock : ∀ b i j, c i ≠ c j → Q b i j = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hQ : ∀ b i j, RationalHeightLE (Q b i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hrows : (Fintype.card (Σ _ : η, ι) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (((p + 2) ^ 4 + 2) ^ 36) ∧ l ∣ m ∧
      ∀ (W : δ → ℝ), (∀ d, 0 < W d) →
      (∀ i, Real.exp (separationBudget ((p + 2) ^ 4)) ≤ W (c i)) →
      ∀ (e r : η → ι → ℝ) (v : ι → ℝ),
      (∀ b i, |e b i| ≤ Real.exp p / W (c i)) →
      (∀ b, r b ∈ realDenominatorGrid l) →
      (∀ b, (fun i j => (Q b i j : ℝ)) *ᵥ (v - e b - r b) = 0) →
      ∃ u d : ι → ℝ,
        (∀ i, |u i| ≤ Real.exp (((p + 2) ^ 4 + 2) ^ 18 + (p + 2) ^ 4) / W (c i)) ∧
        d ∈ realDenominatorGrid m ∧
        ∀ b, (fun i j => (Q b i j : ℝ)) *ᵥ (v - u - d) = 0 := by
  let A := jointMatrix Q
  let q : ℝ := (p + 2) ^ 4
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by decide : 1 ≤ 4)
  have hAh : ∀ bi j, RationalHeightLE (A bi j) H := fun bi j => hQ bi.1 bi.2 j
  have hAb : ∀ bi j, c bi.2 ≠ c j → A bi j = 0 := fun bi j h => hblock bi.1 bi.2 j h
  have hDen : ((matrixDenominator A * l : ℕ) : ℝ) ≤ Real.exp q := by
    simpa only [Nat.mul_comm] using matrixDenominator_allowance_le_exp A l H hAh hp hrows hι hHp hlp
  obtain ⟨S, m, hm, hmp, hdm, _, hsplit⟩ := exists_controlled_weighted_linear_splitting
    (fun bi : Σ _ : η, ι => c bi.2) c A hAb hH
    (Nat.mul_pos (matrixDenominator_pos A) hl) hAh hq (hrows.trans hpq) (hι.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) hDen
  refine ⟨m, hm, hmp, dvd_trans ⟨matrixDenominator A, Nat.mul_comm _ _⟩ hdm, ?_⟩
  intro W hW hWmin e r v he hr hres
  have hfac : ((Fintype.card ι : ℝ) + 1) * ((H : ℝ) + 1) ≤ Real.exp ((p + 2) ^ 2) := by
    apply le_trans _ (coordinateLipschitzBound_le_exp (Fintype.card ι) (Fintype.card ι)
      (H : ℝ≥0) hp hι hι hHp)
    change _ ≤ ((Fintype.card ι : ℝ) + Fintype.card ι + 1) * ((H : ℝ) + 1)
    gcongr
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hcost : (p + 2) ^ 2 + p ≤ q := by
    have hp2 : p ≤ (p + 2) ^ 2 := le_power_budget hp (by decide : 1 ≤ 2)
    calc
      _ ≤ 2 * (p + 2) ^ 2 := by linarith
      _ ≤ (p + 2) ^ 2 * (p + 2) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg p]
      _ = q := by dsimp [q]; ring
  have hslow : ∀ bi, |jointMatrixImages Q e bi| ≤ Real.exp q / W (c bi.2) := by
    intro bi
    have h := weighted_matrix_mulVec_bound c c (fun i j => (Q bi.1 i j : ℝ))
      (fun i j hij => by rw [hblock bi.1 i j hij, Rat.cast_zero])
      (H : ℝ≥0) (fun i j => (hQ bi.1 i j).abs_real_le) W hW (Real.exp_nonneg p) (e bi.1) (he bi.1) bi.2
    apply h.trans
    apply div_le_div_of_nonneg_right _ (hW _).le
    calc
      _ ≤ Real.exp ((p + 2) ^ 2) * Real.exp p := mul_le_mul_of_nonneg_right hfac (Real.exp_nonneg p)
      _ = Real.exp ((p + 2) ^ 2 + p) := (Real.exp_add _ _).symm
      _ ≤ Real.exp q := Real.exp_le_exp.mpr hcost
  obtain ⟨_, _, hu, hd, hker⟩ := hsplit W hW (fun bi => hWmin bi.2)
    (jointMatrixImages Q e) (jointMatrixImages Q r) v hslow (jointMatrixImages_grid Q l r hr)
    (jointMatrixImages_equation Q e r v hres)
  refine ⟨(fun i j => (S i j : ℝ)) *ᵥ jointMatrixImages Q e,
    (fun i j => (S i j : ℝ)) *ᵥ jointMatrixImages Q r, hu, hd, ?_⟩
  intro b
  funext i
  exact congrFun hker ⟨b, i⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem exists_controlled_block_subspace_lift
    {ι κ μ δ L : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    [LieRing L] [LieAlgebra ℚ L]
    (b : Basis ι ℚ L) (c : ι → δ) (r : μ → δ) (U : Submodule ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U) (hU : BasisBlockInvariant b c U)
    (P : Matrix μ ι ℚ) (hPblock : ∀ i j, r i ≠ c j → P i j = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H)
    (hP : ∀ i j, RationalHeightLE (P i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (ι ⊕ μ) : ℝ) ≤ p)
    (hcols : ((Fintype.card ι * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := (p + 2) ^ 10
    ∃ (T : Matrix ι μ ℚ) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((q + 2) ^ 36) ∧ l ∣ m ∧
      (∀ i j, c i ≠ r j → T i j = 0) ∧
      (∀ y : μ → ℝ,
        (∃ x ∈ U.baseChange ℝ, (fun i j => (P i j : ℝ)) *ᵥ (b.baseChange ℝ).equivFun x = y) →
        (b.baseChange ℝ).equivFun.symm ((fun i j => (T i j : ℝ)) *ᵥ y) ∈ U.baseChange ℝ ∧
          (fun i j => (P i j : ℝ)) *ᵥ ((fun i j => (T i j : ℝ)) *ᵥ y) = y) ∧
      (∀ (W : δ → ℝ), (∀ d, 0 < W d) → ∀ (M : ℝ), 0 ≤ M →
        ∀ y : μ → ℝ, (∀ i, |y i| ≤ M / W (r i)) →
          ∀ i, |((fun i j => (T i j : ℝ)) *ᵥ y) i| ≤
            Real.exp ((q + 2) ^ 18) * M / W (c i)) ∧
      (∀ y : μ → ℝ, y ∈ realDenominatorGrid l →
        (fun i j => (T i j : ℝ)) *ᵥ y ∈ realDenominatorGrid m) := by
  let q : ℝ := (p + 2) ^ 10
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by decide : 1 ≤ 10)
  have hι : (Fintype.card ι : ℝ) ≤ p := by
    have hsum : (Fintype.card ι : ℝ) + Fintype.card μ ≤ p := by
      simpa only [Fintype.card_sum, Nat.cast_add] using hrows
    exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hsum
  let H' := max (imageDefiningHeight (Fintype.card ι * Fintype.card κ) (Fintype.card ι) H) H
  have hH' : 1 ≤ H' := hH.trans (Nat.le_max_right _ _)
  have hH'q : (H' : ℝ) ≤ Real.exp q := by
    dsimp only [H']
    rw [Nat.cast_max]
    exact max_le (imageDefiningHeight_le_exp _ _ _ hp hcols hι hHp)
      (hHp.trans (Real.exp_le_exp.mpr hpq))
  obtain ⟨Q, hQ, hQblock, hQker⟩ :=
    exists_block_subspace_defining_matrix b c U v hspan hU hH hv
  obtain ⟨T, m, hm, hmp, hlm, hTblock, _, hsolve, hslow, hgrid⟩ :=
    exists_controlled_constraint_section c c r Q P hQblock hPblock hH' hl
      (fun i j => (hQ i j).mono (Nat.le_max_left _ _))
      (fun i j => (hP i j).mono (Nat.le_max_right _ _))
      hq (hrows.trans hpq) (hι.trans hpq) hH'q (hlp.trans (Real.exp_le_exp.mpr hpq))
  refine ⟨T, m, hm, hmp, hlm, hTblock, ?_, hslow, hgrid⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hy
  obtain ⟨hzero, hright⟩ := hsolve y
    ⟨(b.baseChange ℝ).equivFun x, (hQker x).mpr hx, hxy⟩
  refine ⟨(hQker _).mp ?_, hright⟩
  simpa only [LinearEquiv.apply_symm_apply] using hzero

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem exists_block_subspace_corrections
    {η ι κ δ L : Type*} [Fintype η] [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L]
    (b : Basis ι ℚ L) (c : ι → δ) (U : η → Submodule ℚ L) (v : η → κ → L)
    (hspan : ∀ j, Submodule.span ℚ (Set.range (v j)) = U j)
    (hU : ∀ j, BasisBlockInvariant b c (U j))
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ j z i, RationalHeightLE (b.repr (v j z) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : ((Fintype.card ι * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hrows : (Fintype.card (Σ _ : η, ι) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := (p + 2) ^ 10
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (((q + 2) ^ 4 + 2) ^ 36) ∧ l ∣ m ∧
      ∀ (W : δ → ℝ), (∀ d, 0 < W d) →
      (∀ i, Real.exp (separationBudget ((q + 2) ^ 4)) ≤ W (c i)) →
      ∀ (e r : η → ℝ ⊗[ℚ] L) (x : ℝ ⊗[ℚ] L),
      (∀ j i, |(b.baseChange ℝ).equivFun (e j) i| ≤ Real.exp p / W (c i)) →
      (∀ j, (b.baseChange ℝ).equivFun (r j) ∈ realDenominatorGrid l) →
      (∀ j, x - e j - r j ∈ (U j).baseChange ℝ) →
      ∃ u d : ℝ ⊗[ℚ] L,
        (∀ i, |(b.baseChange ℝ).equivFun u i| ≤ Real.exp (((q + 2) ^ 4 + 2) ^ 18 + (q + 2) ^ 4) / W (c i)) ∧
        (b.baseChange ℝ).equivFun d ∈ realDenominatorGrid m ∧
        ∀ j, x - u - d ∈ (U j).baseChange ℝ := by
  classical
  let H' := imageDefiningHeight (Fintype.card ι * Fintype.card κ) (Fintype.card ι) H
  let q : ℝ := (p + 2) ^ 10
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by decide : 1 ≤ 10)
  have hH' : 1 ≤ H' := by
    have hk := rationalKernelHeight_pos (Fintype.card ι) hH
    have hHpos : 0 < H := hH
    have hpos : 0 < H' := by
      dsimp [H', imageDefiningHeight]
      positivity
    exact hpos
  have hH'p : (H' : ℝ) ≤ Real.exp q := imageDefiningHeight_le_exp _ _ _ hp hcols hι hHp
  choose Q hQ hQb hQker using fun j =>
    exists_block_subspace_defining_matrix b c (U j) (v j) (hspan j) (hU j) hH (hv j)
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_joint_weighted_corrections c Q hQb hH' hl hQ hq
    (hι.trans hpq) (hrows.trans hpq) hH'p (hlp.trans (Real.exp_le_exp.mpr hpq))
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro W hW hWmin e r x he hr hres
  have he' : ∀ j i, |(b.baseChange ℝ).equivFun (e j) i| ≤ Real.exp q / W (c i) := by
    intro j i
    exact (he j i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hpq) (hW _).le)
  have hsys : ∀ j, (fun i k => (Q j i k : ℝ)) *ᵥ
      ((b.baseChange ℝ).equivFun x - (b.baseChange ℝ).equivFun (e j) - (b.baseChange ℝ).equivFun (r j)) = 0 := by
    intro j
    simpa only [map_sub] using (hQker j (x - e j - r j)).mpr (hres j)
  obtain ⟨u, d, hu, hd, hker⟩ := hsolve W hW hWmin
    (fun j => (b.baseChange ℝ).equivFun (e j)) (fun j => (b.baseChange ℝ).equivFun (r j))
    ((b.baseChange ℝ).equivFun x) he' hr hsys
  refine ⟨(b.baseChange ℝ).equivFun.symm u, (b.baseChange ℝ).equivFun.symm d, ?_, ?_, ?_⟩
  · simpa only [LinearEquiv.apply_symm_apply] using hu
  · simpa only [LinearEquiv.apply_symm_apply] using hd
  · intro j
    apply (hQker j _).mp
    simpa only [map_sub, LinearEquiv.apply_symm_apply] using hker j

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem exists_controlled_linear_subspace_lift
    {ι κ μ δ L M : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (e : Basis ι ℚ L) (f : Basis μ ℚ M) (c : ι → δ) (r : μ → δ)
    (U : Submodule ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U) (hU : BasisBlockInvariant e c U)
    (φ : L →ₗ[ℚ] M) (hblock : ∀ i j, r i ≠ c j → f.repr (φ (e j)) i = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ j i, RationalHeightLE (e.repr (v j) i) H)
    (hφ : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (ι ⊕ μ) : ℝ) ≤ p)
    (hcols : ((Fintype.card ι * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := (p + 2) ^ 10
    ∃ (σ : M →ₗ[ℚ] L) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((q + 2) ^ 36) ∧ l ∣ m ∧
      (∀ i j, c i ≠ r j → e.repr (σ (f j)) i = 0) ∧
      (∀ y ∈ (U.map φ).baseChange ℝ,
        σ.baseChange ℝ y ∈ U.baseChange ℝ ∧ φ.baseChange ℝ (σ.baseChange ℝ y) = y) ∧
      (∀ (W : δ → ℝ), (∀ d, 0 < W d) → ∀ (B : ℝ), 0 ≤ B →
        ∀ y : ℝ ⊗[ℚ] M, (∀ i, |(f.baseChange ℝ).equivFun y i| ≤ B / W (r i)) →
          ∀ i, |(e.baseChange ℝ).equivFun (σ.baseChange ℝ y) i| ≤
            Real.exp ((q + 2) ^ 18) * B / W (c i)) ∧
      (∀ y : ℝ ⊗[ℚ] M, (f.baseChange ℝ).equivFun y ∈ realDenominatorGrid l →
        (e.baseChange ℝ).equivFun (σ.baseChange ℝ y) ∈ realDenominatorGrid m) := by
  classical
  let P := LinearMap.toMatrix e f φ
  obtain ⟨T, m, hm, hmp, hlm, hTblock, hsolve, hslow, hgrid⟩ :=
    exists_controlled_block_subspace_lift e c r U v hspan hU P
      (by intro i j hij; simpa only [P, LinearMap.toMatrix_apply] using hblock i j hij) hH hl hv
      (by intro i j; simpa only [P, LinearMap.toMatrix_apply] using hφ i j) hp hrows hcols hHp hlp
  let σ := Matrix.toLin f e T
  have hcoord (y : ℝ ⊗[ℚ] M) :
      (e.baseChange ℝ).equivFun (σ.baseChange ℝ y) =
        (fun i j => (T i j : ℝ)) *ᵥ (f.baseChange ℝ).equivFun y :=
    toLin_baseChange_coordinates e f T y
  have hlift (y : ℝ ⊗[ℚ] M) : σ.baseChange ℝ y =
      (e.baseChange ℝ).equivFun.symm ((fun i j => (T i j : ℝ)) *ᵥ (f.baseChange ℝ).equivFun y) := by
    apply (e.baseChange ℝ).equivFun.injective
    rw [hcoord, LinearEquiv.apply_symm_apply]
  refine ⟨σ, m, hm, hmp, hlm, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have he := LinearMap.toMatrix_apply f e σ i j
    rw [LinearMap.toMatrix_toLin] at he
    exact he.symm.trans (hTblock i j hij)
  · intro y hy
    rw [realification_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    obtain ⟨hmem, hright⟩ := hsolve ((f.baseChange ℝ).equivFun y)
      ⟨x, hx, (baseChange_matrix_apply e f φ x).trans (congrArg (f.baseChange ℝ).equivFun hxy)⟩
    constructor
    · rwa [hlift]
    · apply (f.baseChange ℝ).equivFun.injective
      rw [← baseChange_matrix_apply e f φ, hcoord]
      exact hright
  · intro W hW B hB y hy i
    rw [hcoord]
    exact hslow W hW B hB ((f.baseChange ℝ).equivFun y) hy i
  · intro y hy
    rw [hcoord]
    exact hgrid ((f.baseChange ℝ).equivFun y) hy

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientTopSymbol
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def quotientTopPolynomialMap : F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆
    F.quotientTop.adaptedLieSubalgebra w :=
  F.filteredPolynomialMap F.quotientTop (lieQuotientMap (F.layerIdeal (s + 1)))
    (fun _ _ hx => F.quotientLie_mem _ le_rfl hx) w

noncomputable def quotientTopSymbolMap : F.PolynomialSymbol w →ₗ⁅ℚ⁆
    F.quotientTop.PolynomialSymbol w :=
  F.filteredPolynomialSymbolMap F.quotientTop (lieQuotientMap (F.layerIdeal (s + 1)))
    (fun _ _ hx => F.quotientLie_mem _ le_rfl hx) w

@[simp] theorem quotientTopSymbolMap_symbol (p : F.adaptedLieSubalgebra w) :
    F.quotientTopSymbolMap w (F.polynomialSymbolMap w p) =
      F.quotientTop.polynomialSymbolMap w (F.quotientTopPolynomialMap w p) := rfl

theorem quotientTopSymbolMap_surjective : Function.Surjective (F.quotientTopSymbolMap w) :=
  F.filteredPolynomialSymbolMap_surjective _ _ _ w (fun _ _ hy => hy)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealMultidegreeQuotientOrbit
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (I : LieIdeal ℚ L)

theorem realQuotientMultidegree_mem_layer (a : σ → ℕ) {x : ℝ ⊗[ℚ] L}
    (hx : x ∈ F.realification.layer a) :
    realificationLieHom (lieQuotientMap I) x ∈ (F.quotientMultidegree I).realification.layer a := by
  change realificationLieHom (lieQuotientMap I) x ∈
    ((F.layer a).map (lieQuotientMap I).toLinearMap).baseChange ℝ
  rw [realification_map]
  exact ⟨x, hx, rfl⟩

noncomputable def realQuotientMultidegreeMap :
    F.realification.Group →* (F.quotientMultidegree I).realification.Group :=
  realificationMap (hnil := F.ordinary.lowerCentralSeries_eq_bot)
    (hM := (F.quotientMultidegree I).ordinary.lowerCentralSeries_eq_bot) (lieQuotientMap I)

noncomputable def realQuotientMultidegreeOrbit (g : F.realification.PolynomialOrbit) :
    (F.quotientMultidegree I).realification.PolynomialOrbit :=
  (F.quotientMultidegree I).realification.polynomialOrbitOfLog
    (VectorPolynomial.map (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap
      (PolynomialOrbit.log F.realification g)) (by
        intro a
        rw [coefficients_map]
        exact F.realQuotientMultidegree_mem_layer I (fun i => a i)
          (PolynomialOrbit.adapted F.realification g a))

theorem realQuotientMultidegreeOrbit_eval (g : F.realification.PolynomialOrbit) (x : σ → ℤ) :
    (F.quotientMultidegree I).realification.polynomialOrbitEval x (F.realQuotientMultidegreeOrbit I g) =
      F.realQuotientMultidegreeMap I (F.realification.polynomialOrbitEval x g) := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => (x i : ℚ))
    (VectorPolynomial.map (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap
      (PolynomialOrbit.log F.realification g)) = _
  rw [eval_map]
  rfl

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationAssociatedGraded
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def homogeneousAssociatedGradedEquiv
    (hb : BasisHomogeneousBrackets b ω) : F.AssociatedGraded ≃ₗ⁅ℚ⁆ L :=
  { (F.associatedGradedBasis b ω hF).repr.trans b.repr.symm with
    map_lie' {x y} := by
      let f := (F.associatedGradedBasis b ω hF).repr.trans b.repr.symm
      change f ⁅x, y⁆ = ⁅f x, f y⁆
      apply linear_map_lie_of_basis (F.associatedGradedBasis b ω hF) f.toLinearMap
      intro i j
      apply b.repr.injective
      ext k
      have hf (z : F.AssociatedGraded) : b.repr (f z) =
          (F.associatedGradedBasis b ω hF).repr z := b.repr.apply_symm_apply _
      have hbi (a : ι) : f (F.associatedGradedBasis b ω hF a) = b a := by
        apply b.repr.injective
        rw [hf]
        simp only [Basis.repr_self]
      change b.repr (f ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆) k =
        b.repr ⁅f (F.associatedGradedBasis b ω hF i), f (F.associatedGradedBasis b ω hF j)⁆ k
      rw [hf, hbi, hbi, F.associatedGradedBasis_bracket]
      by_cases h : ω i + ω j = ω k
      · simp only [h, ite_true]
      · rw [if_neg h, hb i j k (Ne.symm h)] }

@[simp] theorem homogeneousAssociatedGradedEquiv_repr
    (hb : BasisHomogeneousBrackets b ω) (x : F.AssociatedGraded) (i : ι) :
    b.repr (F.homogeneousAssociatedGradedEquiv b ω hF hb x) i =
      (F.associatedGradedBasis b ω hF).repr x i := by
  exact congrArg (fun z : ι →₀ ℚ => z i) (b.repr.apply_symm_apply _)

@[simp] theorem homogeneousAssociatedGradedEquiv_basis
    (hb : BasisHomogeneousBrackets b ω) (i : ι) :
    F.homogeneousAssociatedGradedEquiv b ω hF hb (F.associatedGradedBasis b ω hF i) = b i := by
  apply b.repr.injective
  ext k
  rw [homogeneousAssociatedGradedEquiv_repr]
  simp only [Basis.repr_self]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.PolynomialTranslationLie
open Module
variable {σ : Type*} [Fintype σ]

noncomputable def weightedAssociatedGradedEquiv (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) :
    (weightedFiltration w d hwd).AssociatedGraded ≃ₗ⁅ℚ⁆ weightedSubalgebra w d :=
  (weightedFiltration w d hwd).homogeneousAssociatedGradedEquiv
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw)

@[simp] theorem weightedAssociatedGradedEquiv_repr (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : (weightedFiltration w d hwd).AssociatedGraded) (i : WeightedBasisIndex w d) :
    (weightedBasis w d hw).repr (weightedAssociatedGradedEquiv w d hw hwd x) i =
      ((weightedFiltration w d hwd).associatedGradedBasis (weightedBasis w d hw)
        (weightedBasisGrade w d) (weightedFiltration_layer_eq_span w d hw hwd)).repr x i :=
  (weightedFiltration w d hwd).homogeneousAssociatedGradedEquiv_repr _ _ _ _ x i

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FilteredSubalgebraCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def subalgebraLayerFamily (e : Basis ι ℚ L) (v : κ → L)
    (ω : ι → ℕ) (j : ℕ) : κ ⊕ ι → L :=
  Sum.elim v (fun i => if j ≤ ω i then e i else 0)

omit [Fintype ι] in
theorem subalgebraLayerFamily_height (e : Basis ι ℚ L) (v : κ → L)
    (ω : ι → ℕ) (j : ℕ) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ z i, RationalHeightLE (e.repr (v z) i) H) (z : κ ⊕ ι) (i : ι) :
    RationalHeightLE (e.repr (subalgebraLayerFamily e v ω j z) i) H := by
  classical
  cases z with
  | inl z => exact hv z i
  | inr z =>
    by_cases h : j ≤ ω z
    · by_cases he : z = i
      · subst i
        simpa [subalgebraLayerFamily, h] using rationalHeightLE_one hH
      · simpa [subalgebraLayerFamily, h, he] using rationalHeightLE_zero hH
    · simpa [subalgebraLayerFamily, h] using rationalHeightLE_zero hH

namespace NilpotentLieFiltration

variable {s : ℕ} (F : NilpotentLieFiltration L s)

omit [Fintype ι] in
theorem real_subalgebra_layer_eq_span (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hv : Submodule.span ℚ (Set.range v) = U.toSubmodule) (j : ℕ) :
    (realificationLieSubalgebra U).toSubmodule ⊔ (F.realLayer j).toSubmodule =
      Submodule.span ℝ (Set.range (fun z => rationalLieInclusion (subalgebraLayerFamily e v ω j z))) := by
  have hlayer : Submodule.span ℚ (Set.range (fun i => if j ≤ ω i then e i else 0)) = F.layer j :=
    (span_conditional_basis e {i | j ≤ ω i}).trans (hlayers j).symm
  rw [subalgebraLayerFamily, real_span_sum_family,
    real_span_rational_family U.toSubmodule v hv,
    real_span_rational_family (F.layer j) _ hlayer]
  rfl

theorem real_subalgebra_layer_mem_iff_coordinates (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hv : Submodule.span ℚ (Set.range v) = U.toSubmodule) (j : ℕ) (x : ℝ ⊗[ℚ] L) :
    x ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer j ↔
      (e.baseChange ℝ).equivFun x ∈ Submodule.span ℝ
        (Set.range (fun z i => (e.repr (subalgebraLayerFamily e v ω j z) i : ℝ))) := by
  change x ∈ (realificationLieSubalgebra U).toSubmodule.restrictScalars ℚ ⊔
    (F.realLayer j).toSubmodule.restrictScalars ℚ ↔ _
  rw [← Submodule.restrictScalars_sup]
  change x ∈ (realificationLieSubalgebra U).toSubmodule ⊔ (F.realLayer j).toSubmodule ↔ _
  rw [F.real_subalgebra_layer_eq_span e ω hlayers U v hv j]
  exact real_span_family_mem_iff_coordinates e _ x

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FilteredSymbolMapCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

theorem filteredPolynomialSymbolMap_basis_repr [DecidableEq σ]
    (a : SymbolBasisIndex w ω) (b : SymbolBasisIndex w ν) :
    (G.polynomialSymbolBasis f ν hG w).repr
      (F.filteredPolynomialSymbolMap G φ hφ w (F.polynomialSymbolBasis e ω hF w a)) b =
      if a.val.1 = b.val.1 then f.repr (φ (e a.val.2)) b.val.2 else 0 := by
  rw [F.polynomialSymbolBasis_apply, F.filteredPolynomialSymbolMap_symbol,
    G.polynomialSymbolBasis_repr_map, F.filteredPolynomialMap_coefficient,
    F.adaptedMonomialBasis_coe, coefficients_monomial]
  by_cases hab : a.val.1 = b.val.1
  · simp only [hab, Finsupp.single_eq_same, ite_true]
  · rw [Finsupp.single_eq_of_ne (Ne.symm hab), map_zero, map_zero, Finsupp.zero_apply,
      if_neg hab]

theorem filteredPolynomialSymbolMap_monomial_blocks
    (a : SymbolBasisIndex w ω) (b : SymbolBasisIndex w ν) (hab : b.val.1 ≠ a.val.1) :
    (G.polynomialSymbolBasis f ν hG w).repr
      (F.filteredPolynomialSymbolMap G φ hφ w (F.polynomialSymbolBasis e ω hF w a)) b = 0 := by
  classical
  rw [F.filteredPolynomialSymbolMap_basis_repr G e ω hF f ν hG φ hφ w a b,
    if_neg (Ne.symm hab)]

theorem filteredPolynomialSymbolMap_basis_height {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (a : SymbolBasisIndex w ω) (b : SymbolBasisIndex w ν) :
    RationalHeightLE ((G.polynomialSymbolBasis f ν hG w).repr
      (F.filteredPolynomialSymbolMap G φ hφ w (F.polynomialSymbolBasis e ω hF w a)) b) H := by
  classical
  rw [F.filteredPolynomialSymbolMap_basis_repr G e ω hF f ν hG φ hφ w a b]
  split_ifs
  · exact hentries b.val.2 a.val.2
  · exact rationalHeightLE_zero hH

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SupportedQuotientLatticeFaithful
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem mem_realification_integral_lattice_iff (b : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (N : ℕ)
    (hgrid : bchSubgroupCoordinates b Γ = scaledIntegerGrid N)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :
    g ∈ Γ.map realificationHom ↔
      ∃ z : ι → ℤ, ∀ i, (b.baseChange ℝ).repr g.coord i = (N : ℝ) * (z i : ℝ) := by
  constructor
  · intro hg
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
    have hc := (bchSubgroupCoordinates_repr b Γ a).mpr ha
    rw [hgrid] at hc
    obtain ⟨z, hz⟩ := hc
    refine ⟨z, fun i => ?_⟩
    rw [← Basis.equivFun_apply, realificationHom_coordinates]
    have hi := congrFun hz i
    change b.repr a.coord i = (N : ℚ) * (z i : ℚ) at hi
    change (b.repr a.coord i : ℝ) = _
    rw [hi]
    push_cast
    rfl
  · rintro ⟨z, hz⟩
    let a : NilpotentLieBCHGroup L s hnil :=
      ⟨b.equivFun.symm (fun i => (N : ℚ) * (z i : ℚ))⟩
    have ha : a ∈ Γ := by
      apply (bchSubgroupCoordinates_repr b Γ a).mp
      rw [hgrid]
      change b.equivFun (b.equivFun.symm _) ∈ scaledIntegerGrid N
      rw [LinearEquiv.apply_symm_apply]
      exact ⟨z, rfl⟩
    refine Subgroup.mem_map.mpr ⟨a, ha, ?_⟩
    apply NilpotentLieBCHGroup.ext
    apply (b.baseChange ℝ).equivFun.injective
    rw [realificationHom_coordinates]
    funext i
    change (b.equivFun (b.equivFun.symm _) i : ℝ) = _
    rw [LinearEquiv.apply_symm_apply]
    push_cast
    exact (hz i).symm

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t u : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

include hspan in
theorem realQuotientStep_integral_coordinates (Γ : Subgroup F.Group) (N : ℕ)
    (hgrid : bchSubgroupCoordinates b Γ = scaledIntegerGrid N)
    (g : F.realification.Group)
    (hg : F.realQuotientStepHom I hI g ∈
      (Γ.map (F.quotientStepHom I hI)).map realificationHom) :
    ∃ z : {i // i ∉ S} → ℤ, ∀ i : {i // i ∉ S},
      (b.baseChange ℝ).repr g.coord i = (N : ℝ) * (z i : ℝ) := by
  let bq : Basis {i // i ∉ S} ℚ (L ⧸ I) := supportedQuotientBasis b I.toSubmodule S hspan
  have hq : bchSubgroupCoordinates bq (Γ.map (F.quotientStepHom I hI)) = scaledIntegerGrid N :=
    F.quotientStep_exact_grid_supported b I hI S hspan Γ N hgrid
  obtain ⟨z, hz⟩ := (mem_realification_integral_lattice_iff (L := L ⧸ I)
    (hnil := (F.quotientLie I hI).lowerCentralSeries_eq_bot) bq
    (Γ.map (F.quotientStepHom I hI)) N hq (F.realQuotientStepHom I hI g)).mp hg
  refine ⟨z, fun i => ?_⟩
  have hi := hz i
  change ((supportedQuotientBasis b I.toSubmodule S hspan).baseChange ℝ).repr
    (I.toSubmodule.mkQ.baseChange ℝ g.coord) i = _ at hi
  rwa [realSupportedQuotientBasis_repr_mk] at hi

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedQuotientFamilyFaithful
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {α ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)

theorem realQuotientFamily_lattice_detect
    (I : α → LieIdeal ℚ L) (hI : ∀ a, F.layer (t + 1) ≤ (I a).toSubmodule)
    (S : α → Set ι) (hspan : ∀ a, (I a).toSubmodule = Submodule.span ℚ (b '' S a))
    (hcover : ∀ i, ∃ a, i ∉ S a)
    (Γ : Subgroup F.Group) (N : ℕ) (hgrid : bchSubgroupCoordinates b Γ = scaledIntegerGrid N)
    (g : F.realification.Group)
    (hg : ∀ a, F.realQuotientStepHom (I a) (hI a) g ∈
      (Γ.map (F.quotientStepHom (I a) (hI a))).map realificationHom) :
    g ∈ Γ.map realificationHom := by
  classical
  have hcoords (a : α) := F.realQuotientStep_integral_coordinates b (I a) (hI a)
    (S a) (hspan a) Γ N hgrid g (hg a)
  choose z hz using hcoords
  choose a ha using hcover
  apply (mem_realification_integral_lattice_iff b Γ N hgrid g).mpr
  exact ⟨fun i => z (a i) ⟨i, ha i⟩, fun i => hz (a i) ⟨i, ha i⟩⟩

omit [Fintype ι] in
theorem realQuotientFamily_joint_injective
    (I : α → LieIdeal ℚ L) (hI : ∀ a, F.layer (t + 1) ≤ (I a).toSubmodule)
    (S : α → Set ι) (hspan : ∀ a, (I a).toSubmodule = Submodule.span ℚ (b '' S a))
    (hcover : ∀ i, ∃ a, i ∉ S a) :
    Function.Injective (fun g : F.realification.Group => fun a => F.realQuotientStepHom (I a) (hI a) g) := by
  intro g h heq
  apply NilpotentLieBCHGroup.ext
  apply (b.baseChange ℝ).repr.injective
  ext i
  obtain ⟨a, ha⟩ := hcover i
  have hc := congrArg (fun v : (F.quotientLie (I a) (hI a)).realification.Group =>
    ((supportedQuotientBasis b (I a).toSubmodule (S a) (hspan a)).baseChange ℝ).repr
      v.coord ⟨i, ha⟩) (congrFun heq a)
  change ((supportedQuotientBasis b (I a).toSubmodule (S a) (hspan a)).baseChange ℝ).repr
    ((I a).toSubmodule.mkQ.baseChange ℝ g.coord) ⟨i, ha⟩ =
    ((supportedQuotientBasis b (I a).toSubmodule (S a) (hspan a)).baseChange ℝ).repr
      ((I a).toSubmodule.mkQ.baseChange ℝ h.coord) ⟨i, ha⟩ at hc
  simpa only [realSupportedQuotientBasis_repr_mk] using hc

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LieKernelRealificationMark
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem mem_realificationLieKernel_iff (φ : L →ₗ⁅ℚ⁆ M) (x : ℝ ⊗[ℚ] L) :
    x ∈ (LinearMap.ker φ.toLinearMap).baseChange ℝ ↔ realificationLieHom φ x = 0 := by
  rw [real_baseChange_ker]
  rfl

namespace NilpotentLieBCHGroup

variable {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem coord_mem_realificationKernel_iff (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :
    g.coord ∈ (LinearMap.ker φ.toLinearMap).baseChange ℝ ↔
      realificationMap (hnil := hnil) (hM := hM) φ g = 1 := by
  rw [mem_realificationLieKernel_iff]
  constructor
  · intro h
    exact ext h
  · intro h
    exact congrArg coord h

theorem mem_realificationSubgroup_ker_iff (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :
    g ∈ realificationSubgroup (hnil := hnil) φ.ker.toLieSubalgebra ↔
      realificationMap (hnil := hnil) (hM := hM) φ g = 1 := by
  change g.coord ∈ (LinearMap.ker φ.toLinearMap).baseChange ℝ ↔ _
  exact coord_mem_realificationKernel_iff φ g

end NilpotentLieBCHGroup
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolynomialBCHRemoval
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def bchRemove (s : ℕ) (A P B : VectorPolynomial σ ℚ L) :
    VectorPolynomial σ ℚ L := lieBCH s (lieBCH s (-A) P) (-B)

theorem bchRemove_factorization {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (A P B : VectorPolynomial σ ℚ L) :
    lieBCH s (lieBCH s A (bchRemove s A P B)) B = P := by
  let a : NilpotentLieBCHGroup.PolynomialGroup σ hnil := ⟨A⟩
  let g : NilpotentLieBCHGroup.PolynomialGroup σ hnil := ⟨P⟩
  let c : NilpotentLieBCHGroup.PolynomialGroup σ hnil := ⟨B⟩
  have h : a * (a⁻¹ * g * c⁻¹) * c = g := by group
  exact congrArg NilpotentLieBCHGroup.coord h

theorem eval₂_bchRemove [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
    (s : ℕ) (A P B : VectorPolynomial σ ℚ L) (t : σ → ℝ) :
    eval₂ t (bchRemove s A P B) = lieBCH s (lieBCH s (-eval₂ t A) (eval₂ t P)) (-eval₂ t B) := by
  have h₁ := map_lieBCH (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t) s (lieBCH s (-A) P) (-B)
  have h₂ := map_lieBCH (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t) s (-A) P
  rw [h₂] at h₁
  simp only [map_neg, eval₂Lie_apply] at h₁
  exact h₁

theorem bchRemove_constant {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (A P B : VectorPolynomial σ ℚ L) (hA : coefficients A 0 = 0) (hB : coefficients B 0 = 0) :
    coefficients (bchRemove s A P B) 0 = coefficients P 0 := by
  have h₁ := eval_lieBCH (fun _ : σ => (0 : ℚ)) s (lieBCH s (-A) P) (-B)
  have h₂ := eval_lieBCH (fun _ : σ => (0 : ℚ)) s (-A) P
  rw [h₂] at h₁
  simp only [map_neg, eval_zero_eq_coefficient, hA, hB, neg_zero] at h₁
  apply h₁.trans
  change ((1 : NilpotentLieBCHGroup L s hnil) * ⟨coefficients P 0⟩ * 1).coord = _
  simp only [one_mul, mul_one]

theorem bchRemove_coefficients_mem (U : LieSubalgebra ℚ L) (s : ℕ)
    (A P B : VectorPolynomial σ ℚ L)
    (hA : ∀ α, coefficients A α ∈ U) (hP : ∀ α, coefficients P α ∈ U)
    (hB : ∀ α, coefficients B α ∈ U) :
    ∀ α, coefficients (bchRemove s A P B) α ∈ U := by
  let W := coefficientLieSubalgebra (σ := σ) U
  have ha : A ∈ W := hA
  have hp : P ∈ W := hP
  have hb : B ∈ W := hB
  exact lieBCH_mem W s (lieBCH_mem W s (W.neg_mem ha) hp) (W.neg_mem hb)

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem polynomial_bchRemove_grades (E : Submodule ℝ (ℝ ⊗[ℚ] L)) (j : ℕ)
    (hE : ∀ x ∈ E, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (A P B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hA : ∀ α, coefficients A α ∈ E) (hB : ∀ α, coefficients B α ∈ E) :
    map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (bchRemove s A P B) =
      map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P - A - B ∧
      ∀ d < j, map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) (bchRemove s A P B) =
        map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P := by
  have heq (X Y : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
      (h : ∀ t : σ → ℝ, eval₂ t X = eval₂ t Y) : X = Y := by
    apply sub_eq_zero.mp
    apply eq_zero_of_eval₂_zero (K := ℝ)
    intro t
    rw [map_sub, h t, sub_self]
  have hvalues (t : σ → ℝ) :
      basisGradeProjection (b.baseChange ℝ) w j
          (lieBCH s (lieBCH s (-eval₂ t A) (eval₂ t P)) (-eval₂ t B)) =
        basisGradeProjection (b.baseChange ℝ) w j (eval₂ t P) - eval₂ t A - eval₂ t B ∧
      ∀ d < j, basisGradeProjection (b.baseChange ℝ) w d
          (lieBCH s (lieBCH s (-eval₂ t A) (eval₂ t P)) (-eval₂ t B)) =
        basisGradeProjection (b.baseChange ℝ) w d (eval₂ t P) := by
    have ha := hE _ ((eval₂_mem_iff_coefficients E A).mpr hA t)
    have hc := hE _ ((eval₂_mem_iff_coefficients E B).mpr hB t)
    have hal : eval₂ t A ∈ F.realification.layer j := by
      simpa only [ha] using F.realGradeProjection_mem_layer b w hlayers j (eval₂ t A)
    have hcl : eval₂ t B ∈ F.realification.layer j := by
      simpa only [hc] using F.realGradeProjection_mem_layer b w hlayers j (eval₂ t B)
    have hcurrent := F.real_correction_current_grade b w hlayers j
      ⟨eval₂ t A⟩ ⟨eval₂ t P⟩ ⟨eval₂ t B⟩ hal hcl
    have hbelow := F.real_correction_preserves_grades_below b w hlayers j
      ⟨eval₂ t A⟩ ⟨eval₂ t P⟩ ⟨eval₂ t B⟩ hal hcl
    change basisGradeProjection (b.baseChange ℝ) w j
      (lieBCH s (lieBCH s (-eval₂ t A) (eval₂ t P)) (-eval₂ t B)) = _ at hcurrent
    rw [ha, hc] at hcurrent
    exact ⟨hcurrent, hbelow⟩
  constructor
  · apply heq
    intro t
    simp only [eval₂_map, eval₂_bchRemove, map_sub]
    exact (hvalues t).1
  · intro d hd
    apply heq
    intro t
    simp only [eval₂_map, eval₂_bchRemove]
    exact (hvalues t).2 d hd

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialLiftMatching
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem real_sub_grade_mem_sup_next (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) (j : ℕ) (x : ℝ ⊗[ℚ] L)
    (hx : x ∈ V ⊔ (F.realLayer j).toSubmodule) :
    x - basisGradeProjection (b.baseChange ℝ) w j x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  have ht : basisBelowProjection (b.baseChange ℝ) w j z = 0 := by
    have hz' : z - 0 ∈ F.realification.layer j := by rw [sub_zero]; exact hz
    have h := (F.realGradeTruncation_eq_iff b w hlayers j z 0).mpr hz'
    simpa only [map_zero] using h
  have hhigh := F.sub_realGradeTruncation_mem b w hlayers (j + 1) z
  rw [basisBelowProjection_succ, ht, zero_add] at hhigh
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem
    (Submodule.mem_sup_left (V.sub_mem hv (hV j v hv))) (Submodule.mem_sup_right hhigh)
  simpa only [map_add, add_sub_add_comm] using h

include hlayers in
theorem real_matching_grade_remainder (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) (j : ℕ) (x y : ℝ ⊗[ℚ] L)
    (hx : x ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hmatch : basisGradeProjection (b.baseChange ℝ) w j x - y ∈ V) :
    x - y ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem
    (F.real_sub_grade_mem_sup_next b w hlayers V hV j x hx) (Submodule.mem_sup_left hmatch)
  simpa only [sub_add_sub_cancel] using h

include hlayers in
theorem polynomial_lift_matching_remainder (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) (j : ℕ)
    (X Y : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hX : ∀ α, coefficients X α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hmatch : ∀ α, coefficients
      (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) X - Y) α ∈ V) :
    ∀ α, coefficients (X - Y) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro α
  rw [map_sub, Finsupp.sub_apply]
  apply F.real_matching_grade_remainder b w hlayers V hV j _ _ (hX α)
  have h := hmatch α
  simpa only [map_sub, Finsupp.sub_apply, coefficients_map, LinearMap.restrictScalars_apply] using h

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarePolynomialCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

def squareDiagonalLie : L →ₗ⁅ℚ⁆ F.squareLieSubalgebra where
  toFun x := ⟨(x, x), (F.mem_squareLieSubalgebra _).mpr (by simp)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  map_lie' := Subtype.ext rfl

noncomputable def squareFstPolynomialMap :
    F.squareFiltration.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.adaptedLieSubalgebra w :=
  F.squareFiltration.filteredPolynomialMap F F.squareFst (fun _ _ hx => hx.1) w

noncomputable def squareSndPolynomialMap :
    F.squareFiltration.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.adaptedLieSubalgebra w :=
  F.squareFiltration.filteredPolynomialMap F F.squareSnd (fun _ _ hx => hx.2.1) w

noncomputable def squareDiagonalPolynomialMap :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.squareFiltration.adaptedLieSubalgebra w :=
  F.filteredPolynomialMap F.squareFiltration F.squareDiagonalLie
    (fun j x hx => ⟨hx, hx, by change x - x ∈ F.layer (j + 1); simp⟩) w

theorem squareFstPolynomialMap_coefficient (r : F.squareFiltration.adaptedLieSubalgebra w)
    (α : σ →₀ ℕ) : coefficients (F.squareFstPolynomialMap w r).val α =
      (coefficients r.val α).val.1 := by
  change coefficients (VectorPolynomial.map F.squareFst.toLinearMap r.val) α = _
  rw [coefficients_map]
  rfl

theorem squareSndPolynomialMap_coefficient (r : F.squareFiltration.adaptedLieSubalgebra w)
    (α : σ →₀ ℕ) : coefficients (F.squareSndPolynomialMap w r).val α =
      (coefficients r.val α).val.2 := by
  change coefficients (VectorPolynomial.map F.squareSnd.toLinearMap r.val) α = _
  rw [coefficients_map]
  rfl

theorem squareDiagonalPolynomialMap_coefficient (p : F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    (coefficients (F.squareDiagonalPolynomialMap w p).val α).val =
      (coefficients p.val α, coefficients p.val α) := by
  change (coefficients (VectorPolynomial.map F.squareDiagonalLie.toLinearMap p.val) α).val = _
  rw [coefficients_map]
  rfl

theorem square_polynomial_ext {r q : F.squareFiltration.adaptedLieSubalgebra w}
    (hf : F.squareFstPolynomialMap w r = F.squareFstPolynomialMap w q)
    (hs : F.squareSndPolynomialMap w r = F.squareSndPolynomialMap w q) : r = q := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  apply Subtype.ext
  apply Prod.ext
  · have he := congrArg (fun p : F.adaptedLieSubalgebra w => coefficients p.val α) hf
    simpa only [F.squareFstPolynomialMap_coefficient] using he
  · have he := congrArg (fun p : F.adaptedLieSubalgebra w => coefficients p.val α) hs
    simpa only [F.squareSndPolynomialMap_coefficient] using he

@[simp] theorem squareFstPolynomialMap_diagonal (p : F.adaptedLieSubalgebra w) :
    F.squareFstPolynomialMap w (F.squareDiagonalPolynomialMap w p) = p := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.squareFstPolynomialMap_coefficient, F.squareDiagonalPolynomialMap_coefficient]

@[simp] theorem squareSndPolynomialMap_diagonal (p : F.adaptedLieSubalgebra w) :
    F.squareSndPolynomialMap w (F.squareDiagonalPolynomialMap w p) = p := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.squareSndPolynomialMap_coefficient, F.squareDiagonalPolynomialMap_coefficient]

@[simp] theorem squareFstPolynomialMap_relative (hw : ∀ i, 0 < w i)
    (p : F.normalizedRelativeSubmodule w) :
    F.squareFstPolynomialMap w (F.relativeSquareLift w hw p) = p.val := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.squareFstPolynomialMap_coefficient]
  change (coefficients (F.relativeSquarePolynomial w hw p) α).val.1 = _
  rw [F.relativeSquarePolynomial_coefficient]

@[simp] theorem squareSndPolynomialMap_relative (hw : ∀ i, 0 < w i)
    (p : F.normalizedRelativeSubmodule w) :
    F.squareSndPolynomialMap w (F.relativeSquareLift w hw p) = 0 := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.squareSndPolynomialMap_coefficient]
  change (coefficients (F.relativeSquarePolynomial w hw p) α).val.2 = coefficients 0 α
  rw [F.relativeSquarePolynomial_coefficient, map_zero, Finsupp.zero_apply]

noncomputable def squareDiagonalSymbolMap :
    F.PolynomialSymbol w →ₗ⁅ℚ⁆ F.squareFiltration.PolynomialSymbol w :=
  F.filteredPolynomialSymbolMap F.squareFiltration F.squareDiagonalLie
    (fun j x hx => ⟨hx, hx, by change x - x ∈ F.layer (j + 1); simp⟩) w

@[simp] theorem squareDiagonalSymbolMap_symbol (p : F.adaptedLieSubalgebra w) :
    F.squareDiagonalSymbolMap w (F.polynomialSymbolMap w p) =
      F.squareFiltration.polynomialSymbolMap w (F.squareDiagonalPolynomialMap w p) := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPositivePolynomialEvaluation
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialAlgebra : LieSubalgebra ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | F.Adapted p ∧ coefficients p 0 = 0}
  zero_mem' := by constructor <;> simp [Adapted]
  add_mem' hp hq := ⟨F.adaptedSubmodule.add_mem hp.1 hq.1, by simp [hp.2, hq.2]⟩
  smul_mem' c p hp := ⟨F.adaptedSubmodule.smul_mem c hp.1, by simp [hp.2]⟩
  lie_mem' hp hq := by
    refine ⟨F.lie_mem_adaptedSubmodule hp.1 hq.1, ?_⟩
    rw [← eval_zero_eq_coefficient]
    change evalLie (fun _ : σ => (0 : ℚ)) ⁅_, _⁆ = 0
    rw [LieHom.map_lie]
    simp only [evalLie_apply, eval_zero_eq_coefficient, hp.2, zero_lie]

@[simp] theorem mem_positivePolynomialAlgebra (p : VectorPolynomial σ ℚ L) :
    p ∈ F.positivePolynomialAlgebra ↔ F.Adapted p ∧ coefficients p 0 = 0 := Iff.rfl

@[simp] theorem positivePolynomial_constant (p : F.positivePolynomialAlgebra) :
    coefficients p.val 0 = 0 := p.property.2

noncomputable def positivePolynomialEvaluation : F.positivePolynomialAlgebra →ₗ⁅ℚ⁆ L :=
  (evalLie (fun _ : σ => (1 : ℚ))).comp F.positivePolynomialAlgebra.incl

theorem positivePolynomialEvaluation_apply (p : F.positivePolynomialAlgebra) :
    F.positivePolynomialEvaluation p = eval (fun _ : σ => (1 : ℚ)) p.val := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialComponent (a : σ →₀ ℕ) :
    F.positivePolynomialAlgebra →ₗ[ℚ] F.positivePolynomialAlgebra where
  toFun p := ⟨monomial a (coefficients p.val a),
    F.monomial_mem_adaptedSubmodule a (p.property.1 a), by
      classical
      by_cases ha : a = 0
      · subst a
        simp only [coefficients_monomial, Finsupp.single_eq_same, F.positivePolynomial_constant]
      · simp [ha]⟩
  map_add' p q := by
    apply Subtype.ext
    change monomial a (coefficients (p.val + q.val) a) =
      monomial a (coefficients p.val a) + monomial a (coefficients q.val a)
    simp [monomial, TensorProduct.tmul_add]
  map_smul' c p := by
    apply Subtype.ext
    change monomial a (coefficients (c • p.val) a) = c • monomial a (coefficients p.val a)
    simp [monomial]

theorem sum_positivePolynomialComponent (p : F.positivePolynomialAlgebra) :
    ∑ a ∈ (coefficients p.val).support, F.positivePolynomialComponent a p = p := by
  classical
  apply Subtype.ext
  change F.positivePolynomialAlgebra.incl
    (∑ a ∈ (coefficients p.val).support, F.positivePolynomialComponent a p) = p.val
  rw [map_sum]
  exact sum_monomial_coefficients p.val

theorem positivePolynomialEvaluation_component (a : σ →₀ ℕ) (p : F.positivePolynomialAlgebra) :
    F.positivePolynomialEvaluation (F.positivePolynomialComponent a p) = coefficients p.val a := by
  change eval (fun _ : σ => (1 : ℚ)) (monomial a (coefficients p.val a)) = _
  simp [eval_monomial, Finsupp.prod]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialDegreeLayer (n : ℕ) :
    Submodule ℚ F.positivePolynomialAlgebra :=
  (coefficientSupport {a : σ →₀ ℕ | n ≤ ∑ i, a i}).comap
    F.positivePolynomialAlgebra.incl.toLinearMap

theorem positivePolynomialDegreeLayer_antitone : Antitone F.positivePolynomialDegreeLayer := by
  intro n m hnm p hp a ha
  exact hp a (fun hm => ha (hnm.trans hm))

theorem positivePolynomialDegreeLayer_one : F.positivePolynomialDegreeLayer 1 = ⊤ := by
  classical
  apply top_unique
  intro p _ a ha
  change ¬1 ≤ ∑ i, a i at ha
  have hs : (∑ i, a i) = 0 := by omega
  have hz : a = 0 := by
    ext i
    have hi : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
    simpa only [hs, Nat.le_zero_eq, Finsupp.zero_apply] using hi
  subst a
  exact p.property.2

theorem positivePolynomialDegreeLayer_lie {n m : ℕ} {p q : F.positivePolynomialAlgebra}
    (hp : p ∈ F.positivePolynomialDegreeLayer n) (hq : q ∈ F.positivePolynomialDegreeLayer m) :
    ⁅p, q⁆ ∈ F.positivePolynomialDegreeLayer (n + m) := by
  change ⁅p.val, q.val⁆ ∈ coefficientSupport _
  apply coefficientSupport_lie (S := {a : σ →₀ ℕ | n ≤ ∑ i, a i})
    (T := {a : σ →₀ ℕ | m ≤ ∑ i, a i}) _ hp hq
  intro a ha b hb
  change n + m ≤ ∑ i, (a + b) i
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib] using add_le_add ha hb

theorem positivePolynomialDegreeLayer_terminal :
    F.positivePolynomialDegreeLayer ((∑ i, bound i) + 1) = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply Subtype.ext
  apply coefficients.injective
  ext a
  change coefficients p.val a = 0
  by_cases ha : (fun i => a i) ≤ bound
  · apply hp a
    have hsum : (∑ i, a i) ≤ ∑ i, bound i := Finset.sum_le_sum (fun i _ => ha i)
    change ¬(∑ i, bound i) + 1 ≤ ∑ i, a i
    omega
  · simpa only [F.terminal _ ha, Submodule.mem_bot] using p.property.1 a

noncomputable def positivePolynomialDegreeFiltration :
    NilpotentLieFiltration F.positivePolynomialAlgebra (∑ i, bound i) where
  layer := F.positivePolynomialDegreeLayer
  antitone := F.positivePolynomialDegreeLayer_antitone
  one_eq_top := F.positivePolynomialDegreeLayer_one
  lie_mem := F.positivePolynomialDegreeLayer_lie
  terminal := F.positivePolynomialDegreeLayer_terminal

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ}

abbrev BoxedDegreeIndex (bound : σ → ℕ) := ∀ i, Fin (bound i + 1)

noncomputable def boxedDegreeMonomial (a : BoxedDegreeIndex bound) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i).val)

@[simp] theorem boxedDegreeMonomial_apply (a : BoxedDegreeIndex bound) (i : σ) :
    boxedDegreeMonomial a i = (a i).val := by
  classical
  exact congrFun (Finsupp.equivFunOnFinite.apply_symm_apply (fun i => (a i).val)) i

variable (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialCoordinates :
    F.positivePolynomialAlgebra →ₗ[ℚ] (BoxedDegreeIndex bound → L) where
  toFun p a := coefficients p.val (boxedDegreeMonomial a)
  map_add' p q := by ext a; simp
  map_smul' c p := by ext a; simp

theorem positivePolynomialCoordinates_injective : Function.Injective F.positivePolynomialCoordinates := by
  classical
  intro p q hpq
  apply Subtype.ext
  apply coefficients.injective
  ext a
  by_cases ha : (fun i => a i) ≤ bound
  · let b : BoxedDegreeIndex bound := fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩
    have hb : boxedDegreeMonomial b = a := by ext i; simp [b]
    have h := congrFun hpq b
    change coefficients p.val (boxedDegreeMonomial b) = coefficients q.val (boxedDegreeMonomial b) at h
    simpa only [hb] using h
  · have hp : coefficients p.val a = 0 := by
      simpa only [F.terminal _ ha, Submodule.mem_bot] using p.property.1 a
    have hq : coefficients q.val a = 0 := by
      simpa only [F.terminal _ ha, Submodule.mem_bot] using q.property.1 a
    rw [hp, hq]

instance positivePolynomialFiniteDimensional [FiniteDimensional ℚ L] :
    FiniteDimensional ℚ F.positivePolynomialAlgebra :=
  FiniteDimensional.of_injective F.positivePolynomialCoordinates F.positivePolynomialCoordinates_injective

theorem positivePolynomial_finrank_le [FiniteDimensional ℚ L] :
    finrank ℚ F.positivePolynomialAlgebra ≤ (∏ i, (bound i + 1)) * finrank ℚ L := by
  classical
  calc
    _ ≤ finrank ℚ (BoxedDegreeIndex bound → L) :=
      LinearMap.finrank_le_finrank_of_injective F.positivePolynomialCoordinates_injective
    _ = ∑ _ : BoxedDegreeIndex bound, finrank ℚ L := Module.finrank_pi_fintype ℚ
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_pi, Fintype.card_fin, Nat.cast_id]

theorem positivePolynomial_finrank_le_total [FiniteDimensional ℚ L] :
    finrank ℚ F.positivePolynomialAlgebra ≤ 2 ^ (∑ i, bound i) * finrank ℚ L := by
  classical
  have h : (∏ i, (bound i + 1)) ≤ 2 ^ (∑ i, bound i) := by
    calc
      _ ≤ ∏ i, 2 ^ bound i := Finset.prod_le_prod' (fun i _ => Nat.succ_le_of_lt (Nat.lt_two_pow_self))
      _ = _ := by rw [Finset.prod_pow_eq_pow_sum]
  exact F.positivePolynomial_finrank_le.trans (Nat.mul_le_mul_right _ h)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realPositivePolynomialMap :
    (ℝ ⊗[ℚ] F.positivePolynomialAlgebra) →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  VectorPolynomial.realificationLieEquiv.toLieHom.comp
    (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) F.positivePolynomialAlgebra.incl)

theorem realPositivePolynomialMap_coefficient_tmul
    (r : ℝ) (p : F.positivePolynomialAlgebra) (a : σ →₀ ℕ) :
    coefficients (F.realPositivePolynomialMap (r ⊗ₜ[ℚ] p)) a = r ⊗ₜ[ℚ] coefficients p.val a := by
  change coefficients (VectorPolynomial.realificationLieEquiv (r ⊗ₜ[ℚ] p.val)) a = _
  exact coefficients_realificationLieEquiv_tmul r p.val a

theorem realPositivePolynomialMap_adapted (x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra) :
    F.realification.Adapted (F.realPositivePolynomialMap x) := by
  intro a
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r p =>
    rw [F.realPositivePolynomialMap_coefficient_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem r (p.property.1 a)
  | add x y hx hy =>
    rw [map_add, map_add, Finsupp.add_apply]
    exact Submodule.add_mem _ hx hy

theorem realPositivePolynomialMap_constant (x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra) :
    coefficients (F.realPositivePolynomialMap x) 0 = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r p =>
    rw [F.realPositivePolynomialMap_coefficient_tmul, p.property.2, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]

noncomputable def realPositivePolynomialTensor :
    (ℝ ⊗[ℚ] F.positivePolynomialAlgebra) →ₗ⁅ℚ⁆ F.realification.positivePolynomialAlgebra where
  toLinearMap := F.realPositivePolynomialMap.toLinearMap.codRestrict
    F.realification.positivePolynomialAlgebra.toSubmodule
    (fun x => ⟨F.realPositivePolynomialMap_adapted x, F.realPositivePolynomialMap_constant x⟩)
  map_lie' {x y} := by
    apply Subtype.ext
    exact F.realPositivePolynomialMap.map_lie x y

theorem realPositivePolynomialTensor_injective : Function.Injective F.realPositivePolynomialTensor := by
  intro x y h
  apply realification_subtype_injective F.positivePolynomialAlgebra.toSubmodule
  apply VectorPolynomial.realificationLieEquiv.injective
  exact congrArg Subtype.val h

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialMultidegreeLayer (a : σ → ℕ) :
    Submodule ℚ F.positivePolynomialAlgebra :=
  (coefficientSupport {b : σ →₀ ℕ | a ≤ fun i => b i}).comap
    F.positivePolynomialAlgebra.incl.toLinearMap

theorem positivePolynomialMultidegreeLayer_antitone :
    Antitone F.positivePolynomialMultidegreeLayer := by
  intro a b hab p hp c hc
  exact hp c (fun hbc => hc (hab.trans hbc))

theorem positivePolynomialMultidegreeLayer_zero : F.positivePolynomialMultidegreeLayer 0 = ⊤ := by
  apply top_unique
  intro p _ a ha
  exact False.elim (ha (fun i => Nat.zero_le (a i)))

theorem positivePolynomialMultidegreeLayer_lie {a b : σ → ℕ} {p q : F.positivePolynomialAlgebra}
    (hp : p ∈ F.positivePolynomialMultidegreeLayer a)
    (hq : q ∈ F.positivePolynomialMultidegreeLayer b) :
    ⁅p, q⁆ ∈ F.positivePolynomialMultidegreeLayer (a + b) := by
  change ⁅p.val, q.val⁆ ∈ coefficientSupport _
  apply coefficientSupport_lie (S := {c : σ →₀ ℕ | a ≤ fun i => c i})
    (T := {c : σ →₀ ℕ | b ≤ fun i => c i}) _ hp hq
  intro c hc d hd i
  exact add_le_add (hc i) (hd i)

theorem positivePolynomialMultidegreeLayer_terminal (a : σ → ℕ) (ha : ¬a ≤ bound) :
    F.positivePolynomialMultidegreeLayer a = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply Subtype.ext
  apply coefficients.injective
  ext b
  change coefficients p.val b = 0
  by_cases hab : a ≤ fun i => b i
  · have hb : ¬(fun i => b i) ≤ bound := fun hb => ha (hab.trans hb)
    simpa only [F.terminal _ hb, Submodule.mem_bot] using p.property.1 b
  · exact hp b hab

theorem positivePolynomialComponent_mem_layer (a : σ →₀ ℕ) (p : F.positivePolynomialAlgebra) :
    F.positivePolynomialComponent a p ∈ F.positivePolynomialMultidegreeLayer (fun i => a i) := by
  change monomial a (coefficients p.val a) ∈
    coefficientSupport {b : σ →₀ ℕ | (fun i => a i) ≤ fun i => b i}
  apply monomial_mem_coefficientSupport
  exact fun i => le_rfl

theorem positivePolynomialDegreeLayer_eq (n : ℕ) :
    F.positivePolynomialDegreeLayer n =
      ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), F.positivePolynomialMultidegreeLayer a := by
  classical
  apply le_antisymm
  · intro p hp
    rw [← F.sum_positivePolynomialComponent p]
    apply Submodule.sum_mem
    intro a ha
    have hn : n ≤ ∑ i, a i := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp ha) (hp a hn)
    have hle : F.positivePolynomialMultidegreeLayer (fun i => a i) ≤
        ⨆ (b : σ → ℕ) (_hb : n ≤ ∑ i, b i), F.positivePolynomialMultidegreeLayer b :=
      le_iSup_of_le (fun i => a i) (le_iSup_of_le hn le_rfl)
    exact hle (F.positivePolynomialComponent_mem_layer a p)
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha p hp b hb
    apply hp b
    intro hab
    exact hb (ha.trans (Finset.sum_le_sum (fun i _ => hab i)))

noncomputable def positivePolynomialMultidegree :
    MultidegreeLieFiltration σ F.positivePolynomialAlgebra (∑ i, bound i) bound where
  ordinary := F.positivePolynomialDegreeFiltration
  layer := F.positivePolynomialMultidegreeLayer
  antitone := F.positivePolynomialMultidegreeLayer_antitone
  zero_eq_top := F.positivePolynomialMultidegreeLayer_zero
  lie_mem := F.positivePolynomialMultidegreeLayer_lie
  terminal := F.positivePolynomialMultidegreeLayer_terminal
  degree_eq := F.positivePolynomialDegreeLayer_eq

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {bound : σ → ℕ}

theorem boxedDegreeMonomial_injective : Function.Injective (@boxedDegreeMonomial σ _ bound) := by
  intro a b h
  funext i
  apply Fin.ext
  simpa only [boxedDegreeMonomial_apply] using congrArg (fun c : σ →₀ ℕ => c i) h

theorem boxedDegreeMonomial_le (a : BoxedDegreeIndex bound) :
    (fun i => boxedDegreeMonomial a i) ≤ bound := by
  intro i
  change boxedDegreeMonomial a i ≤ bound i
  rw [boxedDegreeMonomial_apply]
  exact Nat.le_of_lt_succ (a i).isLt

theorem exists_boxedDegreeMonomial (a : σ →₀ ℕ) (ha : (fun i => a i) ≤ bound) :
    ∃ b : BoxedDegreeIndex bound, boxedDegreeMonomial b = a := by
  refine ⟨fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩, ?_⟩
  ext i
  exact boxedDegreeMonomial_apply _ i

noncomputable def boxedPolynomial (f : BoxedDegreeIndex bound → L) : VectorPolynomial σ ℚ L := by
  classical
  exact ∑ a, monomial (boxedDegreeMonomial a) (f a)

theorem boxedPolynomial_coefficient (f : BoxedDegreeIndex bound → L) (a : BoxedDegreeIndex bound) :
    coefficients (boxedPolynomial f) (boxedDegreeMonomial a) = f a := by
  classical
  simp [boxedPolynomial, Finsupp.single_apply, boxedDegreeMonomial_injective.eq_iff]

theorem boxedPolynomial_coefficient_outside (f : BoxedDegreeIndex bound → L) (a : σ →₀ ℕ)
    (ha : ¬(fun i => a i) ≤ bound) : coefficients (boxedPolynomial f) a = 0 := by
  classical
  have hne (b : BoxedDegreeIndex bound) : boxedDegreeMonomial b ≠ a := by
    intro h
    apply ha
    simpa only [h] using boxedDegreeMonomial_le b
  simp [boxedPolynomial, hne]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem positivePolynomialComponent_eq_zero (a : σ →₀ ℕ) (p : F.positivePolynomialAlgebra) :
    F.positivePolynomialComponent a p = 0 ↔ coefficients p.val a = 0 := by
  constructor
  · intro h
    have he := congrArg (fun q : F.positivePolynomialAlgebra => coefficients q.val a) h
    change coefficients (monomial a (coefficients p.val a)) a =
      coefficients (0 : VectorPolynomial σ ℚ L) a at he
    simpa only [coefficients_monomial,
      Finsupp.single_eq_same, map_zero, Finsupp.zero_apply] using he
  · intro h
    apply Subtype.ext
    change monomial a (coefficients p.val a) = 0
    simp [h, monomial]

noncomputable def positivePolynomialDiagonal (p : F.positivePolynomialAlgebra) :
    VectorPolynomial σ ℚ F.positivePolynomialAlgebra :=
  (coefficients p.val).sum (fun a _ => monomial a (F.positivePolynomialComponent a p))

theorem positivePolynomialDiagonal_coefficient (p : F.positivePolynomialAlgebra) (a : σ →₀ ℕ) :
    coefficients (F.positivePolynomialDiagonal p) a = F.positivePolynomialComponent a p := by
  classical
  by_cases ha : a ∈ (coefficients p.val).support
  · simp [positivePolynomialDiagonal, Finsupp.sum, Finsupp.single_apply, ha]
  · have hz : F.positivePolynomialComponent a p = 0 :=
      (F.positivePolynomialComponent_eq_zero a p).mpr (Finsupp.notMem_support_iff.mp ha)
    simp [positivePolynomialDiagonal, Finsupp.sum, Finsupp.single_apply, ha, hz]

theorem positivePolynomialDiagonal_adapted (p : F.positivePolynomialAlgebra) :
    F.positivePolynomialMultidegree.Adapted (F.positivePolynomialDiagonal p) := by
  intro a
  rw [F.positivePolynomialDiagonal_coefficient]
  exact F.positivePolynomialComponent_mem_layer a p

theorem positivePolynomialDiagonal_constant (p : F.positivePolynomialAlgebra) :
    coefficients (F.positivePolynomialDiagonal p) 0 = 0 := by
  rw [F.positivePolynomialDiagonal_coefficient, F.positivePolynomialComponent_eq_zero]
  exact p.property.2

theorem positivePolynomialDiagonal_projection (p : F.positivePolynomialAlgebra) :
    VectorPolynomial.map F.positivePolynomialEvaluation.toLinearMap
      (F.positivePolynomialDiagonal p) = p.val := by
  apply coefficients.injective
  ext a
  rw [coefficients_map, F.positivePolynomialDiagonal_coefficient]
  exact F.positivePolynomialEvaluation_component a p

theorem positivePolynomialDiagonal_eval (p : F.positivePolynomialAlgebra) (x : σ → ℚ) :
    F.positivePolynomialEvaluation (eval x (F.positivePolynomialDiagonal p)) = eval x p.val := by
  change F.positivePolynomialEvaluation.toLinearMap (eval x (F.positivePolynomialDiagonal p)) = _
  rw [← eval_map, F.positivePolynomialDiagonal_projection]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem positivePolynomial_support_of_layers (S : Set (σ →₀ ℕ))
    (hS : ∀ a, a ≠ 0 → a ∉ S → F.layer (fun i => a i) = ⊥)
    (p : F.positivePolynomialAlgebra) : p.val ∈ coefficientSupport S := by
  intro a ha
  by_cases hz : a = 0
  · subst a
    exact p.property.2
  · simpa only [hS a hz ha, Submodule.mem_bot] using p.property.1 a

theorem positivePolynomialLayer_le_outsideDownset
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) (a : σ →₀ ℕ) (ha : a ∉ J) :
    F.positivePolynomialMultidegreeLayer (fun i => a i) ≤
      (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ).toSubmodule := by
  intro p hp
  apply (mem_restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ p).mpr
  intro b hb
  apply hp b
  intro hab
  exact ha (hJ hab hb)

noncomputable def positivePolynomialDownsetQuotient
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) :=
  F.positivePolynomialMultidegree.quotientMultidegree
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ)

theorem positivePolynomialDownsetQuotient_terminal
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) (a : σ →₀ ℕ) (ha : a ∉ J) :
    (F.positivePolynomialDownsetQuotient J hJ).layer (fun i => a i) = ⊥ :=
  F.positivePolynomialMultidegree.quotientMultidegree_layer_eq_bot _ _
    (F.positivePolynomialLayer_le_outsideDownset J hJ a ha)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem exists_positivePolynomial_orbit (g : F.PolynomialOrbit)
    (hg : F.polynomialOrbitEval 0 g = 1) :
    ∃ h : F.positivePolynomialMultidegree.PolynomialOrbit,
      F.positivePolynomialMultidegree.polynomialOrbitEval 0 h = 1 ∧
      ∀ x, NilpotentLieBCHGroup.mapOfSteps F.positivePolynomialEvaluation
          (F.positivePolynomialMultidegree.polynomialOrbitEval x h) =
        F.polynomialOrbitEval x g := by
  have hzero : coefficients (PolynomialOrbit.log F g) 0 = 0 := by
    have hcoord := congrArg NilpotentLieBCHGroup.coord hg
    change eval (fun i => ((0 : σ → ℤ) i : ℚ)) (PolynomialOrbit.log F g) = 0 at hcoord
    simpa only [Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using hcoord
  let p : F.positivePolynomialAlgebra := ⟨PolynomialOrbit.log F g, PolynomialOrbit.adapted F g, hzero⟩
  let h := F.positivePolynomialMultidegree.polynomialOrbitOfLog
    (F.positivePolynomialDiagonal p) (F.positivePolynomialDiagonal_adapted p)
  refine ⟨h, ?_, ?_⟩
  · apply NilpotentLieBCHGroup.ext
    change eval (fun i => ((0 : σ → ℤ) i : ℚ)) (F.positivePolynomialDiagonal p) = 0
    simpa only [Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using
      F.positivePolynomialDiagonal_constant p
  · intro x
    apply NilpotentLieBCHGroup.ext
    exact F.positivePolynomialDiagonal_eval p (fun i => (x i : ℚ))

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realPositivePolynomialEvaluation_commute (x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra) :
    F.realification.positivePolynomialEvaluation (F.realPositivePolynomialTensor x) =
      realificationLieHom F.positivePolynomialEvaluation x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r p =>
    change eval (fun _ : σ => (1 : ℚ))
      (VectorPolynomial.realificationLieEquiv (r ⊗ₜ[ℚ] p.val)) =
        r ⊗ₜ[ℚ] eval (fun _ : σ => (1 : ℚ)) p.val
    exact eval_realificationLieEquiv_tmul r p.val _
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PositivePolynomialLayerBases
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positiveCoefficientLayer (a : BoxedDegreeIndex bound) : Submodule ℚ L := by
  classical
  exact if boxedDegreeMonomial a = 0 then ⊥ else F.layer (fun i => (a i).val)

theorem mem_positiveCoefficientLayer (a : BoxedDegreeIndex bound) (x : L) :
    x ∈ F.positiveCoefficientLayer a ↔
      x ∈ F.layer (fun i => (a i).val) ∧ (boxedDegreeMonomial a = 0 → x = 0) := by
  classical
  by_cases ha : boxedDegreeMonomial a = 0
  · have hzero : (fun i => (a i).val) = 0 := by
      funext i
      have h := congrArg (fun b : σ →₀ ℕ => b i) ha
      simpa only [boxedDegreeMonomial_apply, Finsupp.zero_apply, Pi.zero_apply] using h
    simp [positiveCoefficientLayer, ha, hzero, F.zero_eq_top]
  · simp [positiveCoefficientLayer, ha]

theorem boxedPolynomial_positive (f : ∀ a : BoxedDegreeIndex bound, F.positiveCoefficientLayer a) :
    boxedPolynomial (fun a => (f a).val) ∈ F.positivePolynomialAlgebra := by
  constructor
  · intro a
    by_cases ha : (fun i => a i) ≤ bound
    · obtain ⟨b, rfl⟩ := exists_boxedDegreeMonomial a ha
      rw [boxedPolynomial_coefficient]
      simpa only [boxedDegreeMonomial_apply] using
        ((F.mem_positiveCoefficientLayer b (f b).val).mp (f b).property).1
    · rw [boxedPolynomial_coefficient_outside _ a ha]
      exact Submodule.zero_mem _
  · obtain ⟨b, hb⟩ := exists_boxedDegreeMonomial (bound := bound) 0 (fun i => Nat.zero_le _)
    rw [← hb, boxedPolynomial_coefficient]
    exact ((F.mem_positiveCoefficientLayer b (f b).val).mp (f b).property).2 hb

noncomputable def positivePolynomialCoefficientEquiv :
    F.positivePolynomialAlgebra ≃ₗ[ℚ] (∀ a : BoxedDegreeIndex bound, F.positiveCoefficientLayer a) where
  toFun p a := ⟨coefficients p.val (boxedDegreeMonomial a),
    (F.mem_positiveCoefficientLayer a _).mpr ⟨by
      simpa only [boxedDegreeMonomial_apply] using p.property.1 (boxedDegreeMonomial a),
      fun ha => by rw [ha]; exact p.property.2⟩⟩
  invFun f := ⟨boxedPolynomial (fun a => (f a).val), F.boxedPolynomial_positive f⟩
  left_inv p := by
    apply F.positivePolynomialCoordinates_injective
    funext a
    exact boxedPolynomial_coefficient _ a
  right_inv f := by
    funext a
    apply Subtype.ext
    exact boxedPolynomial_coefficient _ a
  map_add' p q := by ext a; simp
  map_smul' c p := by ext a; simp

theorem positivePolynomialCoefficientEquiv_apply
    (p : F.positivePolynomialAlgebra) (a : BoxedDegreeIndex bound) :
    (F.positivePolynomialCoefficientEquiv p a).val = coefficients p.val (boxedDegreeMonomial a) := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))

noncomputable def positivePolynomialBasis : Basis (Σ a, κ a) ℚ F.positivePolynomialAlgebra := by
  classical
  exact (Pi.basis b).map F.positivePolynomialCoefficientEquiv.symm

theorem positivePolynomialBasis_repr (p : F.positivePolynomialAlgebra) (j : Σ a, κ a) :
    (F.positivePolynomialBasis b).repr p j =
      (b j.1).repr (F.positivePolynomialCoefficientEquiv p j.1) j.2 := by
  classical
  rfl

theorem positivePolynomialBasis_coefficient_self (a : BoxedDegreeIndex bound) (j : κ a) :
    coefficients (F.positivePolynomialBasis b ⟨a, j⟩).val (boxedDegreeMonomial a) = (b a j).val := by
  classical
  change (F.positivePolynomialCoefficientEquiv (F.positivePolynomialBasis b ⟨a, j⟩) a).val = _
  simp only [positivePolynomialBasis, Basis.map_apply, LinearEquiv.apply_symm_apply,
    Pi.basis_apply, Pi.single_eq_same]

theorem positivePolynomialBasis_coefficient_ne (a c : BoxedDegreeIndex bound)
    (h : a ≠ c) (j : κ a) :
    coefficients (F.positivePolynomialBasis b ⟨a, j⟩).val (boxedDegreeMonomial c) = 0 := by
  classical
  change (F.positivePolynomialCoefficientEquiv (F.positivePolynomialBasis b ⟨a, j⟩) c).val = _
  simp only [positivePolynomialBasis, Basis.map_apply, LinearEquiv.apply_symm_apply,
    Pi.basis_apply, Pi.single_eq_of_ne (Ne.symm h), ZeroMemClass.coe_zero]

theorem positivePolynomialBasis_monomial (j : Σ a, κ a) :
    (F.positivePolynomialBasis b j).val = monomial (boxedDegreeMonomial j.1) (b j.1 j.2).val := by
  classical
  apply coefficients.injective
  ext a
  by_cases ha : (fun i => a i) ≤ bound
  · obtain ⟨c, rfl⟩ := exists_boxedDegreeMonomial a ha
    by_cases hc : j.1 = c
    · subst c
      rw [F.positivePolynomialBasis_coefficient_self, coefficients_monomial, Finsupp.single_eq_same]
    · rw [F.positivePolynomialBasis_coefficient_ne b _ _ hc]
      simp [boxedDegreeMonomial_injective.ne hc]
  · have hp : coefficients (F.positivePolynomialBasis b j).val a = 0 := by
      simpa only [F.terminal _ ha, Submodule.mem_bot] using
        (F.positivePolynomialBasis b j).property.1 a
    have hne : boxedDegreeMonomial j.1 ≠ a := by
      intro h
      apply ha
      simpa only [h] using boxedDegreeMonomial_le j.1
    simp [hp, hne]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))

noncomputable def positivePolynomialSupport (S : Set (σ →₀ ℕ)) : Submodule ℚ F.positivePolynomialAlgebra :=
  (coefficientSupport S).comap F.positivePolynomialAlgebra.incl.toLinearMap

theorem positivePolynomialSupport_eq_span (S : Set (σ →₀ ℕ)) :
    F.positivePolynomialSupport S =
      Submodule.span ℚ (F.positivePolynomialBasis b '' {j | boxedDegreeMonomial j.1 ∈ S}) := by
  ext p
  rw [basis_mem_span_image_iff]
  constructor
  · intro hp j hj
    have hz : F.positivePolynomialCoefficientEquiv p j.1 = 0 := Subtype.ext (hp _ hj)
    rw [F.positivePolynomialBasis_repr, hz, map_zero, Finsupp.zero_apply]
  · intro hp a ha
    change coefficients p.val a = 0
    by_cases hbox : (fun i => a i) ≤ bound
    · obtain ⟨c, rfl⟩ := exists_boxedDegreeMonomial a hbox
      have hz : F.positivePolynomialCoefficientEquiv p c = 0 := by
        apply (b c).repr.injective
        ext j
        simpa only [F.positivePolynomialBasis_repr, map_zero, Finsupp.zero_apply] using hp ⟨c, j⟩ ha
      exact congrArg Subtype.val hz
    · simpa only [F.terminal _ hbox, Submodule.mem_bot] using p.property.1 a

noncomputable def positivePolynomialSupportedBasis (S : Set (σ →₀ ℕ)) :
    Basis {j : Σ a, κ a // boxedDegreeMonomial j.1 ∈ S} ℚ (F.positivePolynomialSupport S) :=
  supportedSubmoduleBasis (F.positivePolynomialBasis b) _ _ (F.positivePolynomialSupport_eq_span b S)

theorem positivePolynomialSupportedBasis_coe (S : Set (σ →₀ ℕ))
    (j : {j : Σ a, κ a // boxedDegreeMonomial j.1 ∈ S}) :
    (F.positivePolynomialSupportedBasis b S j).val = F.positivePolynomialBasis b j.val :=
  supportedSubmoduleBasis_coe _ _ _ _ j

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial

variable {σ ν L : Type*} [Fintype σ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))
  (e : Basis ν ℚ L) {H : ℕ} (hH : 1 ≤ H)
  (hb : ∀ a j k, RationalHeightLE (e.repr (b a j).val k) H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)

include hH hb hc in
theorem positivePolynomialBasis_bracket_coefficient_height
    (x y : Σ a, κ a) (a : BoxedDegreeIndex bound) (k : ν) :
    RationalHeightLE (e.repr
      (F.positivePolynomialCoefficientEquiv ⁅F.positivePolynomialBasis b x,
        F.positivePolynomialBasis b y⁆ a).val k)
      (squarefreeBracketHeight (Fintype.card ν) H) := by
  classical
  rw [F.positivePolynomialCoefficientEquiv_apply]
  change RationalHeightLE (e.repr (coefficients
    ⁅(F.positivePolynomialBasis b x).val, (F.positivePolynomialBasis b y).val⁆
    (boxedDegreeMonomial a)) k) _
  rw [F.positivePolynomialBasis_monomial, F.positivePolynomialBasis_monomial, lie_monomial]
  by_cases ha : boxedDegreeMonomial x.1 + boxedDegreeMonomial y.1 = boxedDegreeMonomial a
  · rw [ha, coefficients_monomial, Finsupp.single_eq_same]
    exact lie_bracket_coordinate_height e hc _ _ (hb x.1 x.2) (hb y.1 y.2) k
  · simp only [coefficients_monomial, Finsupp.single_apply, ha, ite_false, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (squarefreeBracketHeight_pos _ hH)

include hH hb hc in
theorem positivePolynomialBasis_structure_height [∀ a, Fintype (κ a)]
    (hκ : ∀ a, Fintype.card (κ a) ≤ Fintype.card ν) (x y z : Σ a, κ a) :
    RationalHeightLE (lieStructureConstants (F.positivePolynomialBasis b) x y z)
      (squarefreeStructureHeight (Fintype.card ν) H) := by
  change RationalHeightLE ((F.positivePolynomialBasis b).repr
    ⁅F.positivePolynomialBasis b x, F.positivePolynomialBasis b y⁆ z) _
  rw [F.positivePolynomialBasis_repr]
  have h := submodule_basis_coordinate_height (F.positiveCoefficientLayer z.1) (b z.1) e hH
    (fun i j => hb z.1 j i)
    (F.positivePolynomialCoefficientEquiv ⁅F.positivePolynomialBasis b x,
      F.positivePolynomialBasis b y⁆ z.1)
    (fun k => F.positivePolynomialBasis_bracket_coefficient_height b e hH hb hc x y z.1 k) z.2
  apply h.mono
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.mul_le_mul_right _ (rationalSolveHeight_mono hH (hκ z.1))) _)

theorem positivePolynomialBasis_evaluation (j : Σ a, κ a) :
    F.positivePolynomialEvaluation (F.positivePolynomialBasis b j) = (b j.1 j.2).val := by
  rw [F.positivePolynomialEvaluation_apply, F.positivePolynomialBasis_monomial]
  simp [eval_monomial, Finsupp.prod]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))
  (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J)

theorem positivePolynomialDownsetIdeal_eq_support :
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ).toSubmodule =
      F.positivePolynomialSupport Jᶜ := rfl

theorem positivePolynomialDownsetIdeal_eq_span :
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ).toSubmodule =
      Submodule.span ℚ (F.positivePolynomialBasis b '' {j | boxedDegreeMonomial j.1 ∉ J}) :=
  (F.positivePolynomialDownsetIdeal_eq_support J hJ).trans
    (F.positivePolynomialSupport_eq_span b Jᶜ)

noncomputable def positivePolynomialDownsetBasis :
    Basis {j : Σ a, κ a // j ∉ {k | boxedDegreeMonomial k.1 ∉ J}} ℚ
      (F.positivePolynomialAlgebra ⧸ restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ) :=
  supportedQuotientBasis (F.positivePolynomialBasis b) _ _
    (F.positivePolynomialDownsetIdeal_eq_span b J hJ)

theorem positivePolynomialDownsetBasis_repr (x : F.positivePolynomialAlgebra) (j) :
    (F.positivePolynomialDownsetBasis b J hJ).repr
      (lieQuotientMap (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ) x) j =
        (F.positivePolynomialBasis b).repr x j.val :=
  supportedQuotientBasis_repr_mk _ _ _ _ x j

theorem positivePolynomialDownset_multidegree_span (a : σ → ℕ) :
    (F.positivePolynomialDownsetQuotient J hJ).layer a =
      Submodule.span ℚ (F.positivePolynomialDownsetBasis b J hJ ''
        {j | a ≤ fun i => boxedDegreeMonomial j.val.1 i}) := by
  change (F.positivePolynomialSupport {c : σ →₀ ℕ | a ≤ fun i => c i}).map
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ).toSubmodule.mkQ = _
  rw [F.positivePolynomialSupport_eq_span b]
  exact supportedQuotientBasis_map_span _ _ _ _ _

theorem positivePolynomialDownset_degree_span (n : ℕ) :
    (F.positivePolynomialDownsetQuotient J hJ).ordinary.layer n =
      Submodule.span ℚ (F.positivePolynomialDownsetBasis b J hJ ''
        {j | n ≤ ∑ i, boxedDegreeMonomial j.val.1 i}) := by
  change (F.positivePolynomialSupport {c : σ →₀ ℕ | n ≤ ∑ i, c i}).map
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ).toSubmodule.mkQ = _
  rw [F.positivePolynomialSupport_eq_span b]
  exact supportedQuotientBasis_map_span _ _ _ _ _

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))

variable [DecidableEq σ] [∀ a, Fintype (κ a)]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators

variable {α σ L : Type*} [Fintype α] [DecidableEq α] [Fintype σ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ} {bound : σ → ℕ}
  (F : MultidegreeLieFiltration σ L s bound)
  (J : α → Set (σ →₀ ℕ)) (hJ : ∀ a, IsLowerSet (J a))

noncomputable def positivePolynomialQuotientProduct :=
  NilpotentLieFiltration.pi (fun a => (F.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary)

noncomputable def positivePolynomialQuotientProductMap :
    F.positivePolynomialAlgebra →ₗ⁅ℚ⁆
      (∀ a, F.positivePolynomialAlgebra ⧸ restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a)) :=
  liePiMap (fun a => lieQuotientMap (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a)))

noncomputable def positivePolynomialQuotientProductRealMap :
    F.positivePolynomialMultidegree.ordinary.realification.Group →*
      (F.positivePolynomialQuotientProduct J hJ).realification.Group :=
  realificationMap (hnil := F.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
    (hM := (F.positivePolynomialQuotientProduct J hJ).lowerCentralSeries_eq_bot)
    (F.positivePolynomialQuotientProductMap J hJ)

noncomputable def positivePolynomialQuotientProductLattice
    (Γ : Subgroup F.positivePolynomialMultidegree.ordinary.Group) :
    Subgroup (F.positivePolynomialQuotientProduct J hJ).Group :=
  piBCHSubgroup (fun a => (F.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary)
    (fun a => Γ.map (F.positivePolynomialMultidegree.ordinary.quotientStepHom
      (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a))
      (by rw [F.positivePolynomialMultidegree.ordinary.terminal]; exact bot_le)))

theorem positivePolynomialQuotientProductRealMap_component
    (g : F.positivePolynomialMultidegree.ordinary.realification.Group) (a : α) :
    realBCHPiEquiv (fun a => (F.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary)
      (F.positivePolynomialQuotientProductRealMap J hJ g) a =
        F.positivePolynomialMultidegree.ordinary.realQuotientStepHom
          (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a))
          (by rw [F.positivePolynomialMultidegree.ordinary.terminal]; exact bot_le) g := by
  apply NilpotentLieBCHGroup.ext
  exact realification_liePiEval_liePiMap _ g.coord a

variable {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ c, Basis (κ c) ℚ (F.positiveCoefficientLayer c))

omit [Fintype α] [DecidableEq α] in
include b in
theorem positivePolynomial_quotient_family_basis_cover
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → F.layer (fun i => c i) = ⊥)
    (j : Σ c, κ c) : ∃ a, boxedDegreeMonomial j.1 ∈ J a := by
  classical
  rcases j with ⟨c, j⟩
  by_contra hnone
  have hs : ∀ c, c ≠ 0 → c ∉ ⋃ a, J a → F.layer (fun i => c i) = ⊥ := by
    intro c hc hnot
    exact hcover c hc (fun a ha => hnot (Set.mem_iUnion.mpr ⟨a, ha⟩))
  have hz := F.positivePolynomial_support_of_layers (⋃ a, J a) hs
    (F.positivePolynomialBasis b ⟨c, j⟩) (boxedDegreeMonomial c)
    (fun h => hnone (Set.mem_iUnion.mp h))
  change coefficients (F.positivePolynomialBasis b ⟨c, j⟩).val (boxedDegreeMonomial c) = 0 at hz
  rw [F.positivePolynomialBasis_coefficient_self] at hz
  exact (b c).ne_zero j (Subtype.ext hz)

variable [DecidableEq σ] [∀ c, Fintype (κ c)]

omit [DecidableEq σ] [∀ c, Fintype (κ c)] in
include b in
theorem positivePolynomialQuotientProductRealMap_injective
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → F.layer (fun i => c i) = ⊥) :
    Function.Injective (F.positivePolynomialQuotientProductRealMap J hJ) := by
  classical
  have hcov (j : Σ c, κ c) : ∃ a, j ∉ {k | boxedDegreeMonomial k.1 ∉ J a} := by
    simpa only [Set.mem_ofPred_eq, not_not] using F.positivePolynomial_quotient_family_basis_cover J b hcover j
  intro g h heq
  apply F.positivePolynomialMultidegree.ordinary.realQuotientFamily_joint_injective
    (t := ∑ i, bound i)
    (F.positivePolynomialBasis b)
    (fun a => restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a))
    (fun a => by rw [F.positivePolynomialMultidegree.ordinary.terminal]; exact bot_le)
    (fun a => {k | boxedDegreeMonomial k.1 ∉ J a})
    (fun a => F.positivePolynomialDownsetIdeal_eq_span b (J a) (hJ a)) hcov
  funext a
  simpa only [F.positivePolynomialQuotientProductRealMap_component] using
    congrArg (fun x => realBCHPiEquiv
      (fun a => (F.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary) x a) heq

theorem positivePolynomialQuotientProduct_lattice_detect
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → F.layer (fun i => c i) = ⊥)
    (Γ : Subgroup F.positivePolynomialMultidegree.ordinary.Group) (B : ℕ)
    (hgrid : bchSubgroupCoordinates (F.positivePolynomialBasis b) Γ = scaledIntegerGrid B)
    (g : F.positivePolynomialMultidegree.ordinary.realification.Group)
    (hg : F.positivePolynomialQuotientProductRealMap J hJ g ∈
      (F.positivePolynomialQuotientProductLattice J hJ Γ).map realificationHom) :
    g ∈ Γ.map realificationHom := by
  classical
  apply F.positivePolynomialMultidegree.ordinary.realQuotientFamily_lattice_detect
    (t := ∑ i, bound i)
    (F.positivePolynomialBasis b)
    (fun a => restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a))
    (fun a => by rw [F.positivePolynomialMultidegree.ordinary.terminal]; exact bot_le)
    (fun a => {k | boxedDegreeMonomial k.1 ∉ J a})
    (fun a => F.positivePolynomialDownsetIdeal_eq_span b (J a) (hJ a))
    (fun j => by simpa only [Set.mem_ofPred_eq, not_not] using
      F.positivePolynomial_quotient_family_basis_cover J b hcover j) Γ B hgrid g
  intro a
  have ha := (realBCHPiEquiv_mem_lattice
    (fun a => (F.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary) _ _).mp hg a
  simpa only [F.positivePolynomialQuotientProductRealMap_component] using ha

theorem positivePolynomialQuotientProduct_lattice_cover
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → F.layer (fun i => c i) = ⊥)
    (Γ : Subgroup F.positivePolynomialMultidegree.ordinary.Group) (B : ℕ)
    (hgrid : bchSubgroupCoordinates (F.positivePolynomialBasis b) Γ = scaledIntegerGrid B) :
    (F.positivePolynomialQuotientProductLattice J hJ Γ).map realificationHom ⊓
      (F.positivePolynomialQuotientProductRealMap J hJ).range ≤
        (Γ.map realificationHom).map (F.positivePolynomialQuotientProductRealMap J hJ) := by
  rintro y ⟨hy, g, rfl⟩
  exact Subgroup.mem_map.mpr ⟨g,
    F.positivePolynomialQuotientProduct_lattice_detect J hJ b hcover Γ B hgrid g hy, rfl⟩

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*} [∀ a, Fintype (κ a)]
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))
  (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J)

noncomputable def positivePolynomialDownsetMultidegreeBasis (a : σ → ℕ) :
    Basis (Fin (finrank ℚ ((F.positivePolynomialDownsetQuotient J hJ).layer a))) ℚ
      ((F.positivePolynomialDownsetQuotient J hJ).layer a) := by
  classical
  let c := supportedSubmoduleBasis (F.positivePolynomialDownsetBasis b J hJ) _ _
    (F.positivePolynomialDownset_multidegree_span b J hJ a)
  exact c.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis c).symm)

theorem positivePolynomialDownsetMultidegreeBasis_height (a : σ → ℕ) (j k) :
    RationalHeightLE ((F.positivePolynomialDownsetBasis b J hJ).repr
      (F.positivePolynomialDownsetMultidegreeBasis b J hJ a j).val k) 1 := by
  classical
  unfold positivePolynomialDownsetMultidegreeBasis
  rw [Basis.reindex_apply, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one _ _ _

noncomputable def positivePolynomialDownsetDegreeBasis (n : ℕ) :
    Basis (Fin (finrank ℚ ((F.positivePolynomialDownsetQuotient J hJ).ordinary.layer n))) ℚ
      ((F.positivePolynomialDownsetQuotient J hJ).ordinary.layer n) := by
  classical
  let c := supportedSubmoduleBasis (F.positivePolynomialDownsetBasis b J hJ) _ _
    (F.positivePolynomialDownset_degree_span b J hJ n)
  exact c.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis c).symm)

theorem positivePolynomialDownsetDegreeBasis_height (n : ℕ) (j k) :
    RationalHeightLE ((F.positivePolynomialDownsetBasis b J hJ).repr
      (F.positivePolynomialDownsetDegreeBasis b J hJ n j).val k) 1 := by
  classical
  unfold positivePolynomialDownsetDegreeBasis
  rw [Basis.reindex_apply, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one _ _ _

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*} [∀ a, Fintype (κ a)]
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))

noncomputable def positivePolynomialSupportedFinBasis (S : Set (σ →₀ ℕ)) :
    Basis (Fin (finrank ℚ (F.positivePolynomialSupport S))) ℚ (F.positivePolynomialSupport S) := by
  classical
  exact (F.positivePolynomialSupportedBasis b S).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis (F.positivePolynomialSupportedBasis b S)).symm)

theorem positivePolynomialSupportedFinBasis_height (S : Set (σ →₀ ℕ)) (j k) :
    RationalHeightLE ((F.positivePolynomialBasis b).repr
      (F.positivePolynomialSupportedFinBasis b S j).val k) 1 := by
  classical
  unfold positivePolynomialSupportedFinBasis
  rw [Basis.reindex_apply, F.positivePolynomialSupportedBasis_coe]
  exact basis_repr_height_one _ _ _

noncomputable def positivePolynomialMultidegreeBasis (a : σ → ℕ) :
    Basis (Fin (finrank ℚ (F.positivePolynomialMultidegreeLayer a))) ℚ
      (F.positivePolynomialMultidegreeLayer a) :=
  F.positivePolynomialSupportedFinBasis b {c : σ →₀ ℕ | a ≤ fun i => c i}

theorem positivePolynomialMultidegreeBasis_height (a : σ → ℕ) (j k) :
    RationalHeightLE ((F.positivePolynomialBasis b).repr
      (F.positivePolynomialMultidegreeBasis b a j).val k) 1 :=
  F.positivePolynomialSupportedFinBasis_height b _ j k

noncomputable def positivePolynomialDegreeBasis (n : ℕ) :
    Basis (Fin (finrank ℚ (F.positivePolynomialDegreeLayer n))) ℚ
      (F.positivePolynomialDegreeLayer n) :=
  F.positivePolynomialSupportedFinBasis b {c : σ →₀ ℕ | n ≤ ∑ i, c i}

theorem positivePolynomialDegreeBasis_height (n : ℕ) (j k) :
    RationalHeightLE ((F.positivePolynomialBasis b).repr
      (F.positivePolynomialDegreeBasis b n j).val k) 1 :=
  F.positivePolynomialSupportedFinBasis_height b _ j k

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.UniformPolynomialPeriodBudget
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

theorem polynomial_period_cost_le_exp (K r s l D Q : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hD : (D : ℝ) ≤ Real.exp ((p + K) ^ K))
    (hQ : (Q : ℝ) ≤ Real.exp ((p + (r + 3)) ^ (r + 3))) :
    (((l * D * Q ^ s) * Q : ℕ) : ℝ) ≤
      Real.exp ((p + (K + r + s + 10)) ^ (K + r + s + 10)) := by
  let C := K + r + s + 10
  let t := p + C
  have ht : 3 ≤ t := by
    dsimp [t, C]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) s]
  have hC : 1 ≤ C := by dsimp [C]; omega
  have hpT : p ≤ t ^ (C - 1) := by
    apply (show p ≤ t by dsimp [t]; have := Nat.cast_nonneg (α := ℝ) C; linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t) (show 1 ≤ C - 1 by dsimp [C]; omega)
  have hDT : (p + K) ^ K ≤ t ^ (C - 1) := by
    apply (pow_le_pow_left₀ (by positivity : 0 ≤ p + K) (show p + K ≤ t by
      dsimp [t, C]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) s]) K).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hQT : ((s : ℝ) + 1) * (p + (r + 3)) ^ (r + 3) ≤ t ^ (C - 1) := by
    have hs : (s : ℝ) + 1 ≤ t := by
      dsimp [t, C]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) r]
    have hr : p + (r + 3) ≤ t := by
      dsimp [t, C]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) s]
    calc
      _ ≤ t * t ^ (r + 3) := mul_le_mul hs (pow_le_pow_left₀ (by positivity) hr _) (by positivity) (by linarith)
      _ = t ^ (r + 4) := (pow_succ' _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hQpow : (Q : ℝ) ^ (s + 1) ≤ Real.exp (((s : ℝ) + 1) * (p + (r + 3)) ^ (r + 3)) := by
    simpa only [← Real.exp_nat_mul, Nat.cast_add, Nat.cast_one] using
      pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ (s + 1)
  push_cast
  calc
    _ = (l : ℝ) * D * (Q : ℝ) ^ (s + 1) := by rw [pow_succ]; ring
    _ ≤ Real.exp p * Real.exp ((p + K) ^ K) *
        Real.exp (((s : ℝ) + 1) * (p + (r + 3)) ^ (r + 3)) :=
      mul_le_mul (mul_le_mul hl hD (by positivity) (by positivity)) hQpow (by positivity) (by positivity)
    _ = Real.exp (p + (p + K) ^ K + ((s : ℝ) + 1) * (p + (r + 3)) ^ (r + 3)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (t ^ C) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ 3 * t ^ (C - 1) := by linarith
        _ ≤ t * t ^ (C - 1) := mul_le_mul_of_nonneg_right ht (by positivity)
        _ = _ := by rw [← pow_succ', Nat.sub_add_cancel hC]
    _ = _ := by simp [t, C]

end Erdos3

end

section

namespace Erdos3

open Module _root_.MvPolynomial

end Erdos3

end

section

namespace Erdos3

open Module _root_.MvPolynomial

theorem polynomialDenominator_dvd_power {σ : Type*} (P : MvPolynomial σ ℚ)
    (q N : ℕ) (hden : ∀ α, (P.coeff α).den ∣ q) (hcard : P.support.card ≤ N) :
    polynomialDenominator P ∣ q ^ N := by
  classical
  have h : polynomialDenominator P ∣ q ^ P.support.card := by
    unfold polynomialDenominator arrayDenominator
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_coe] using
      Finset.prod_dvd_prod_of_dvd (s := Finset.univ) (fun α : P.support => (P.coeff α.val).den)
        (fun _ : P.support => q) (fun α _ => hden α.val)
  exact h.trans (pow_dvd_pow q hcard)

theorem polynomialFamilyDenominator_dvd_power {ι σ : Type*} [Fintype ι]
    (P : ι → MvPolynomial σ ℚ) (q N : ℕ)
    (hden : ∀ i α, ((P i).coeff α).den ∣ q) (hcard : ∀ i, (P i).support.card ≤ N) :
    polynomialFamilyDenominator P ∣ q ^ (N * Fintype.card ι) := by
  classical
  unfold polynomialFamilyDenominator
  simpa only [Finset.prod_const, Finset.card_univ, ← pow_mul] using
    Finset.prod_dvd_prod_of_dvd (s := Finset.univ) (fun i => polynomialDenominator (P i))
      (fun _ : ι => q ^ N) (fun i _ => polynomialDenominator_dvd_power (P i) q N (hden i) (hcard i))

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def uniformPolynomialBCHPeriod (e : Basis ι ℚ L) (s r l q : ℕ) : ℕ :=
  let Q := q ^ (((r + 1) * (Fintype.card σ + 1) ^ r) * Fintype.card ι)
  (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * Q ^ s) * Q

theorem uniformPolynomialBCHPeriod_pos (e : Basis ι ℚ L) (s r l q : ℕ)
    (hl : 0 < l) (hq : 0 < q) : 0 < uniformPolynomialBCHPeriod (σ := σ) e s r l q := by
  unfold uniformPolynomialBCHPeriod
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hl (polynomialFamilyDenominator_pos _))
    (pow_pos (pow_pos hq _) _)) (pow_pos hq _)

theorem polynomialBCHPeriod_dvd_uniform (e : Basis ι ℚ L) (s r l q : ℕ)
    (P : ι → MvPolynomial σ ℚ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (hden : ∀ i α, ((P i).coeff α).den ∣ q) :
    polynomialBCHPeriod e s l P ∣ uniformPolynomialBCHPeriod (σ := σ) e s r l q := by
  have h := polynomialFamilyDenominator_dvd_power P q ((r + 1) * (Fintype.card σ + 1) ^ r)
    hden (fun i => polynomial_support_card_le (P i) (hdegree i))
  exact mul_dvd_mul (mul_dvd_mul_left _ (pow_dvd_pow_of_dvd h s)) h

theorem polynomialBCHMap_uniform_coset_eq (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (r l q : ℕ)
    (P : ι → MvPolynomial σ ℚ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (hden : ∀ i α, ((P i).coeff α).den ∣ q)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (x y : σ → ℤ) (hxy : ∀ j, (uniformPolynomialBCHPeriod (σ := σ) e s r l q : ℤ) ∣ x j - y j) :
    (QuotientGroup.mk (polynomialBCHMap e hnil P x) : _ ⧸ Γ) =
      QuotientGroup.mk (polynomialBCHMap e hnil P y) := by
  apply polynomialBCHMap_coset_eq e hnil Γ l r P hdegree hinner x y
  intro j
  exact (Int.natCast_dvd_natCast.mpr (polynomialBCHPeriod_dvd_uniform e s r l q P hdegree hden)).trans (hxy j)

theorem polynomialBCHMap_uniform_inverse_coset_eq (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (r l q : ℕ)
    (P : ι → MvPolynomial σ ℚ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (hden : ∀ i α, ((P i).coeff α).den ∣ q)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (x y : σ → ℤ) (hxy : ∀ j, (uniformPolynomialBCHPeriod (σ := σ) e s r l q : ℤ) ∣ x j - y j) :
    (QuotientGroup.mk (polynomialBCHMap e hnil P x)⁻¹ : _ ⧸ Γ) =
      QuotientGroup.mk (polynomialBCHMap e hnil P y)⁻¹ := by
  have hinv (z : σ → ℤ) : polynomialBCHMap e hnil (fun i => -(P i)) z =
      (polynomialBCHMap e hnil P z)⁻¹ := by
    apply NilpotentLieBCHGroup.ext
    change e.equivFun.symm (fun i => eval (fun j => (z j : ℚ)) (-(P i))) =
      -(e.equivFun.symm (fun i => eval (fun j => (z j : ℚ)) (P i)))
    simp only [map_neg, ← Pi.neg_def]
  have h := polynomialBCHMap_uniform_coset_eq e hnil Γ r l q (fun i => -(P i))
    (fun i => by simpa only [totalDegree_neg] using hdegree i)
    (fun i α => by simpa only [coeff_neg, Rat.neg_den] using hden i α)
    hinner x y hxy
  simpa only [hinv] using h

end Erdos3

end

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped TensorProduct

theorem uniformPolynomialBCHPeriod_le_exp {ι σ L : Type*} [Fintype ι] [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] (e : Basis ι ℚ L) (K s r l q : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hn : (Fintype.card σ : ℝ) ≤ p) (hl : (l : ℝ) ≤ Real.exp p) (hq : (q : ℝ) ≤ Real.exp p)
    (hD : (polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) : ℝ) ≤
      Real.exp ((p + K) ^ K)) :
    (uniformPolynomialBCHPeriod (σ := σ) e s r l q : ℝ) ≤
      Real.exp ((p + (K + r + s + 10)) ^ (K + r + s + 10)) := by
  let N := ((r + 1) * (Fintype.card σ + 1) ^ r) * Fintype.card ι
  let Q := q ^ N
  let t : ℝ := p + (r + 3)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right (by positivity)
  have hdt : (Fintype.card ι : ℝ) ≤ t := hd.trans hpt
  have hnt : (Fintype.card σ : ℝ) + 1 ≤ t := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) r]
  have hrt : (r : ℝ) + 1 ≤ t := by dsimp [t]; linarith
  have hlength : (N : ℝ) * p ≤ t ^ (r + 3) := by
    dsimp only [N]
    push_cast
    calc
      _ ≤ t * t ^ r * t * t := by gcongr
      _ = _ := by rw [pow_add]; ring
  have hQ : (Q : ℝ) ≤ Real.exp ((p + (r + 3)) ^ (r + 3)) := by
    dsimp only [Q]
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hq N).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr hlength
  exact polynomial_period_cost_le_exp K r s l _ Q hp hl hD hQ

theorem exists_uniformPolynomialBCHPeriod_exp_bound (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι σ L : Type*} [Fintype ι] [Fintype σ]
      [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (l H q : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p → (q : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (uniformPolynomialBCHPeriod (σ := σ) e s r l q : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  obtain ⟨K, hK, hden⟩ := exists_conjugation_denominator_exp_bound s
  refine ⟨K + r + s + 10, by omega, ?_⟩
  intro ι σ L _ _ _ _ e l H q p hp hd hn hH hlb hqb hc
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    uniformPolynomialBCHPeriod_le_exp (σ := σ) e K s r l q hp hd hn hlb hqb
    (hden e H p hp hd hH hc)

theorem realPolynomialBCHMap_uniform_cosets {ι σ L : Type*} [Fintype ι] [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (r l q : ℕ)
    (P : ι → MvPolynomial σ ℚ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (hP : ∀ i α, ((P i).coeff α).den ∣ q)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (x y : σ → ℤ)
    (hxy : ∀ j, (uniformPolynomialBCHPeriod (σ := σ) e s r l q : ℤ) ∣ x j - y j) :
    let f := fun z : σ → ℤ => realPolynomialBCHMap
      (hnil := realification_lowerCentralSeries_eq_bot hnil) (e.baseChange ℝ) P
      (fun j => (z j : ℝ))
    ((QuotientGroup.mk (f x) : _ ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) =
      QuotientGroup.mk (f y)) ∧
    ((QuotientGroup.mk (f x)⁻¹ : _ ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) =
      QuotientGroup.mk (f y)⁻¹) := by
  dsimp only
  constructor
  · rw [realPolynomialBCHMap_integer, realPolynomialBCHMap_integer]
    exact realification_coset_eq Γ _ _
      (polynomialBCHMap_uniform_coset_eq e hnil Γ r l q P hdegree hP hinner x y hxy)
  · rw [realPolynomialBCHMap_integer, realPolynomialBCHMap_integer,
      ← map_inv, ← map_inv]
    exact realification_coset_eq Γ _ _
      (polynomialBCHMap_uniform_inverse_coset_eq e hnil Γ r l q P hdegree hP hinner x y hxy)

end Erdos3

end

end OAI

end


