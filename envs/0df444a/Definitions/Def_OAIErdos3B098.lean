-- Prove2me | Definitions.Def_OAIErdos3B098
-- name    : OAIErdos3B098
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T18:20:54.670033+00:00
-- url     : https://prove2.me/theorems/3d79b0c9-2ec8-468b-b87b-530ac6a5733a
-- title:
--   OpenAI Erdős-3 split, definitions bundle 99 of 106
-- statement:
--   Definitions bundle 99 of 106 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B097`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 99 available.
--
--   Modules: `OAI.Erdos3.DegreeRankLieFiltration.ambientHorizontalCoordinates`, `OAI.Erdos3.DegreeRankLieFiltration.fourAmbientCoordinates`, `OAI.Erdos3.DegreeRankLieFiltration.fourAmbientCoordinates_height`, `OAI.Erdos3.DegreeRankLieFiltration.fourHorizontalCoordinates`, `OAI.Erdos3.DegreeRankLieFiltration.fourHorizontalCoordinates_map`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalCoordinates`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalCoordinates_injective`, `OAI.Erdos3.DegreeRankLieFiltration.horizontalImageOfSubmodule`, `OAI.Erdos3.DegreeRankLieFiltration.horizontalImage_coordinates`, `OAI.Erdos3.DegreeRankLieFiltration.layerHorizontalImage`, `OAI.Erdos3.DegreeRankLieFiltration.layerHorizontalImage_eq_of_submodule`, `OAI.Erdos3.DegreeRankLieFiltration.layerHorizontalImage_frequency`, `OAI.Erdos3.DegreeRankLieFiltration.layerHorizontalMap`, `OAI.Erdos3.DegreeRankLieFiltration.mem_layerHorizontalImage`, `OAI.Erdos3.DegreeRankLieFiltration.projectedComponentSymbolMap`, `OAI.Erdos3.DegreeRankLieFiltration.projectedComponent_mem_layer`, `OAI.Erdos3.DegreeRankLieFiltration.projectedHorizontalSymbolCoefficient`, `OAI.Erdos3.DegreeRankLieFiltration.projectedHorizontalSymbolCoefficient_lie`, `OAI.Erdos3.DegreeRankLieFiltration.projectedHorizontalSymbolCoefficient_symbol`, `OAI.Erdos3.DegreeRankLieFiltration.projectedLayerCoefficient`, `OAI.Erdos3.DegreeRankLieFiltration.projectedLayerCoefficient_coe`, `OAI.Erdos3.DegreeRankLieFiltration.projectedLayerCoefficient_horizontal`, `OAI.Erdos3.DegreeRankLieFiltration.projectedLayerCoefficient_tensor_coe`, `OAI.Erdos3.DegreeRankLieFiltration.projectedLayerCoefficient_tensor_horizontal`, `OAI.Erdos3.DegreeRankLieFiltration.realFourAmbientCoordinates`, `OAI.Erdos3.DegreeRankLieFiltration.realFourAmbientCoordinates_bound`, `OAI.Erdos3.DegreeRankLieFiltration.realFourAmbientCoordinates_component`, `OAI.Erdos3.DegreeRankLieFiltration.realFourAmbientCoordinates_grid`, `OAI.Erdos3.DegreeRankLieFiltration.realFourCoordinateEquiv`, `OAI.Erdos3.DegreeRankLieFiltration.realFourHorizontalCoordinates`, `OAI.Erdos3.DegreeRankLieFiltration.realFourHorizontalCoordinates_component`, `OAI.Erdos3.DegreeRankLieFiltration.realFourHorizontalCoordinates_image`, `OAI.Erdos3.DegreeRankLieFiltration.realFourHorizontalCoordinates_map`, `OAI.Erdos3.DegreeRankLieFiltration.realFourHorizontalCoordinates_tensor_map`, `OAI.Erdos3.DegreeRankLieFiltration.realFourHorizontalMap`, `OAI.Erdos3.DegreeRankLieFiltration.realFourHorizontalMap_baseChange`, `OAI.Erdos3.DegreeRankLieFiltration.realHigherHorizontalCoordinates`, `OAI.Erdos3.DegreeRankLieFiltration.realHigherHorizontalCoordinates_component`, `OAI.Erdos3.DegreeRankLieFiltration.realHigherHorizontalCoordinates_image`, `OAI.Erdos3.DegreeRankLieFiltration.realHigherHorizontalCoordinates_injective`, `OAI.Erdos3.DegreeRankLieFiltration.realProjectedHorizontalSymbolHom`, `OAI.Erdos3.DegreeRankLieFiltration.realProjectedHorizontalSymbolHom_apply`, `OAI.Erdos3.DegreeRankLieFiltration.real_projectedCoefficient_horizontal`, `OAI.Erdos3.DegreeRankLieFiltration.real_projectedCoefficient_mem`, `OAI.Erdos3.DegreeRankLieFiltration.real_projectedHorizontalSymbolCoefficient_component`, `OAI.Erdos3.NilpotentLieBCHGroup.PolynomialDerivativeSystemMod`, `OAI.Erdos3.NilpotentLieBCHGroup.PolynomialDerivativeSystemMod.exact_system`, `OAI.Erdos3.NilpotentLieBCHGroup.PolynomialDerivativeSystemMod.remove`, `OAI.Erdos3.NilpotentLieBCHGroup.PolynomialLiftSystem`, `OAI.Erdos3.NilpotentLieBCHGroup.PolynomialLiftSystemMod`, `OAI.Erdos3.NilpotentLieBCHGroup.PolynomialLiftSystemMod.exact_left`, `OAI.Erdos3.NilpotentLieBCHGroup.PolynomialLiftSystemMod.remove`, `OAI.Erdos3.NilpotentLieFiltration.current_derivative_defect_preserved`, `OAI.Erdos3.NilpotentLieFiltration.current_derivative_removal_projection`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbit_log_mul_mem_graded`, `OAI.Erdos3.NilpotentLieFiltration.polynomialRationalGrid_symbol`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_symbol`, `OAI.Erdos3.NilpotentLieFiltration.polynomial_grade_adjoint_eq`, `OAI.Erdos3.NilpotentLieFiltration.polynomial_grade_eq_of_sub_mem_next`, `OAI.Erdos3.NilpotentLieFiltration.polynomial_grade_logDerivative_eq`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialOrbit_log_mul_mem_graded`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolHom_eq_of_quotient_eq`, `OAI.Erdos3.NilpotentLieFiltration.real_current_layer_polynomial_derivative_equation`, `OAI.Erdos3.NilpotentLieFiltration.real_polynomial_derivative_lower_layers`, `OAI.Erdos3.NilpotentLieFiltration.real_sub_horizontal_mem_of_lower_grades`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasisIndex_card_le`, `OAI.Erdos3.PolynomialTranslationLie.weightedIndexOrder`, `OAI.Erdos3.PolynomialTranslationLie.weightedLayerBasis`, `OAI.Erdos3.PolynomialTranslationLie.weightedLayerBasis_height`, `OAI.Erdos3.PolynomialTranslationLie.weightedLayerFinBasis`, `OAI.Erdos3.PolynomialTranslationLie.weightedLayerFinBasis_height`, `OAI.Erdos3.PolynomialTranslationLie.weightedLayerIndexEquiv`, `OAI.Erdos3.PolynomialTranslationLie.weightedOrderedBasis`, `OAI.Erdos3.PolynomialTranslationLie.weightedOrderedBasis_layers`, `OAI.Erdos3.PolynomialTranslationLie.weightedOrderedBasis_repr`, `OAI.Erdos3.PolynomialTranslationLie.weightedOrderedBasis_structure_height`, `OAI.Erdos3.PolynomialTranslationLie.weightedOrderedGrade`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeGridRightDictionary.labeling`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeGridRightDictionary.recOn`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.affinePullback`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.affinePullback_complexityLE`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.conjugate`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.conjugate_complexityLE`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.coordinateEquiv`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.coordinateEquiv_complexityLE`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.coordinateEquiv_lipBound`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.coordinateEquiv_normBound`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.coordinateEquiv_observable`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.eval_affinePullback`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.eval_conjugate`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.eval_coordinateEquiv`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.eval_coordinateEquiv_symm`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.eval_substitute`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.eval_translate`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.exists_nested_box_restriction`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.linearPullbackHom`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.linearPullbackHom_complexityLE`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.mean_translate_box`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.scalarAffinePullback`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.scalarAffinePullback_complexityLE`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.scalarAffinePullback_eval_integer`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.substitute`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.substitute_complexityLE`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.symbol`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.symbol_translate`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.translate`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.translate_complexityLE`, `OAI.Erdos3.RationalFilteredNilmanifold.centralRationalCircle`, `OAI.Erdos3.RationalFilteredNilmanifold.centralRationalCircle_act_coe`, `OAI.Erdos3.RationalFilteredNilmanifold.centralRationalCircle_commutes`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_bounded_native_grid_enumeration`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_grid_right_dictionary`, `OAI.Erdos3.RationalFilteredNilmanifold.periodicRealDirection`, `OAI.Erdos3.RationalFilteredNilmanifold.periodicRealDirection_central`, `OAI.Erdos3.RationalFilteredNilmanifold.periodicRealDirection_eq`, `OAI.Erdos3.RationalFilteredNilmanifold.periodicRealDirection_mem_lattice`, `OAI.Erdos3.RationalFilteredNilmanifold.periodicRealDirection_mem_top`, `OAI.Erdos3.RationalFilteredNilmanifold.periodicRealDirection_span`, `OAI.Erdos3.RationalFilteredNilmanifold.piFrequency_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.piFrequency_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.pi_layer_span`, `OAI.Erdos3.RationalFilteredNilmanifold.productBasisWeight`, `OAI.Erdos3.RationalFilteredNilmanifold.productFinBasis_repr`, `OAI.Erdos3.RationalFilteredNilmanifold.rationalDirectionPeriod`, `OAI.Erdos3.RationalFilteredNilmanifold.rationalDirectionPeriod_mem_lattice`, `OAI.Erdos3.RationalFilteredNilmanifold.rationalDirectionPeriod_pos`, `OAI.Erdos3.RationalFilteredNilmanifold.triple_product_basis_logHeight`, `OAI.Erdos3.VectorPolynomial.coefficientSubmodule_sup`, `OAI.Erdos3.VectorPolynomial.coefficients_lie_constant`, `OAI.Erdos3.VectorPolynomial.mem_coefficient_sup_polynomialLayer`, `OAI.Erdos3.VectorPolynomial.pderiv_map`, `OAI.Erdos3.VectorPolynomial.pderiv_mem_submodule`, `OAI.Erdos3.VectorPolynomial.polynomialLayer_eq_coefficientSubmodule`, `OAI.Erdos3.VectorPolynomial.substitute_scalarAffinePolynomial`, `OAI.Erdos3.basisGradeProjection_other`, `OAI.Erdos3.bchRemove_mem_gradedPolynomialSubmodule`, `OAI.Erdos3.bracketSystemLift_injective`, `OAI.Erdos3.coefficientSubmodule_invariant`, `OAI.Erdos3.dualAdjoint_mem_coefficientSubmodule`, `OAI.Erdos3.dualAdjoint_mem_shiftedGradedPolynomialSubmodule`, `OAI.Erdos3.exists_subspace_basis_coordinates`, `OAI.Erdos3.exists_subspace_coordinate_polynomial`, `OAI.Erdos3.finite_card_real_grid_box`, `OAI.Erdos3.formalLogDerivative_mem_coefficientSubmodule`, `OAI.Erdos3.formalLogDerivative_mem_shiftedGradedPolynomialSubmodule`, `OAI.Erdos3.gradedPolynomialSubalgebra`, `OAI.Erdos3.gradedPolynomialSubmodule`, `OAI.Erdos3.gradedPolynomialSubmodule_projection_homogeneous`, `OAI.Erdos3.homogeneous_mem_gradedPolynomialSubmodule`, `OAI.Erdos3.lieTreeEval_hom`, `OAI.Erdos3.monomial_mem_gradedPolynomialSubmodule`, `OAI.Erdos3.monomial_mem_shiftedGradedPolynomialSubmodule`, `OAI.Erdos3.pderiv_mem_shiftedGradedPolynomialSubmodule`, `OAI.Erdos3.piFrequency`, `OAI.Erdos3.piFrequency_apply`, `OAI.Erdos3.piFrequency_single`, `OAI.Erdos3.polynomial_derivative_removal_preserves_coefficients`, `OAI.Erdos3.polynomial_derivative_removal_preserves_shifted_grading`, `OAI.Erdos3.quotientCoordinateMatrix`, `OAI.Erdos3.realCoordinate_projection`, `OAI.Erdos3.realFourCoordinateEquiv_tmul`, `OAI.Erdos3.realFourCoordinateSpan`, `OAI.Erdos3.realFourCoordinateSpan_span`, `OAI.Erdos3.realQuotientCoordinateMap`, `OAI.Erdos3.realQuotientCoordinateMap_apply`, `OAI.Erdos3.realQuotientCoordinateMap_eq_matrix`, `OAI.Erdos3.realQuotientCoordinateMap_eq_zero_iff`, `OAI.Erdos3.realQuotientCoordinateMap_grid`, `OAI.Erdos3.realQuotientCoordinateMap_norm_bound`, `OAI.Erdos3.realQuotientCoordinateMap_tmul_one`, `OAI.Erdos3.realRationalCoordinateEquiv`, `OAI.Erdos3.realRationalCoordinateEquiv_tmul`, `OAI.Erdos3.realRationalCoordinateSpan`, `OAI.Erdos3.realRationalCoordinateSpan_eq_image`, `OAI.Erdos3.realRationalCoordinateSpan_span`, `OAI.Erdos3.real_pi_projection_coordinates`, `OAI.Erdos3.realify_piFrequency`, `OAI.Erdos3.scalarAffinePolynomial`, `OAI.Erdos3.scalarAffinePolynomial_support`, `OAI.Erdos3.shiftedGradedPolynomialSubmodule`, `OAI.Erdos3.shiftedGradedPolynomialSubmodule_invariant`, `OAI.Erdos3.shiftedGradedPolynomialSubmodule_projection_homogeneous`, `OAI.Erdos3.shifted_one_projection_homogeneous`, `OAI.Erdos3.subspaceQuotientMatrix`, `OAI.Erdos3.subspaceQuotientMatrix_height`, `OAI.Erdos3.subspaceQuotientMatrix_real_apply`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B029

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalCentralCircle
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)

noncomputable def rationalDirectionPeriod (v : L) : ℕ :=
  D.grid * arrayDenominator (D.basis.equivFun v)

theorem rationalDirectionPeriod_pos (v : L) : 0 < D.rationalDirectionPeriod v :=
  Nat.mul_pos D.grid_pos (arrayDenominator_pos _)

theorem rationalDirectionPeriod_mem_lattice (v : L) :
    (⟨(D.rationalDirectionPeriod v : ℚ) • v⟩ : D.filtration.Group) ∈ D.lattice := by
  have hc : D.basis.equivFun ((D.rationalDirectionPeriod v : ℚ) • v) ∈
      scaledIntegerGrid D.grid := by
    refine ⟨clearedArray (D.basis.equivFun v), ?_⟩
    rw [map_smul]
    ext i
    change (D.rationalDirectionPeriod v : ℚ) * D.basis.equivFun v i =
      (D.grid : ℚ) * (clearedArray (D.basis.equivFun v) i : ℚ)
    rw [clearedArray_cast]
    simp only [rationalDirectionPeriod, Nat.cast_mul, mul_assoc]
  have h := D.inner_grid hc
  change (⟨D.basis.equivFun.symm (D.basis.equivFun
    ((D.rationalDirectionPeriod v : ℚ) • v))⟩ : D.filtration.Group) ∈ D.lattice at h
  simpa only [LinearEquiv.symm_apply_apply] using h

noncomputable def periodicRealDirection (v : L) : ℝ ⊗[ℚ] L :=
  rationalLieInclusion ((D.rationalDirectionPeriod v : ℚ) • v)

theorem periodicRealDirection_eq (v : L) :
    D.periodicRealDirection v = (D.rationalDirectionPeriod v : ℝ) • rationalLieInclusion v := by
  simp only [periodicRealDirection, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem periodicRealDirection_mem_lattice (v : L) :
    (⟨D.periodicRealDirection v⟩ : D.RealGroup) ∈ D.realLattice := by
  exact Subgroup.mem_map.mpr ⟨⟨(D.rationalDirectionPeriod v : ℚ) • v⟩,
    D.rationalDirectionPeriod_mem_lattice v, rfl⟩

theorem periodicRealDirection_central (v : L) (hv : v ∈ D.filtration.layer s)
    (w : ℝ ⊗[ℚ] L) : ⁅D.periodicRealDirection v, w⁆ = 0 := by
  rw [D.periodicRealDirection_eq, smul_lie,
    rationalLieInclusion_central v (D.filtration.top_layer_central hv), smul_zero]

theorem periodicRealDirection_mem_top (v : L) (hv : v ∈ D.filtration.layer s) :
    (⟨D.periodicRealDirection v⟩ : D.RealGroup) ∈ D.filtration.realification.subgroup s := by
  change (1 : ℝ) ⊗ₜ[ℚ] ((D.rationalDirectionPeriod v : ℚ) • v) ∈
    (D.filtration.layer s).baseChange ℝ
  exact Submodule.tmul_mem_baseChange_of_mem 1 ((D.filtration.layer s).smul_mem _ hv)

theorem periodicRealDirection_span {ι : Type*} (v : ι → L) :
    Submodule.span ℝ (Set.range (fun i => D.periodicRealDirection (v i))) =
      Submodule.span ℝ (Set.range (fun i => rationalLieInclusion (v i))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change D.periodicRealDirection (v i) ∈ _
    rw [D.periodicRealDirection_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have h := Submodule.smul_mem
      (Submodule.span ℝ (Set.range (fun i => D.periodicRealDirection (v i))))
      (D.rationalDirectionPeriod (v i) : ℝ)⁻¹ (Submodule.subset_span ⟨i, rfl⟩)
    change (D.rationalDirectionPeriod (v i) : ℝ)⁻¹ • D.periodicRealDirection (v i) ∈ _ at h
    rw [D.periodicRealDirection_eq, smul_smul, inv_mul_cancel₀, one_smul] at h
    · exact h
    · exact_mod_cast (D.rationalDirectionPeriod_pos (v i)).ne'

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

noncomputable def centralRationalCircle (v : L) (hv : v ∈ D.filtration.layer s) :
    let := D.metricSpace
    IsometricCircleAction D.Space := by
  let := D.metricSpace
  exact centralBCHCircleAction (D.basis.baseChange ℝ) D.realLattice
    D.realLattice_closed_discrete.1 (D.periodicRealDirection v)
    (D.periodicRealDirection_central v hv) (D.periodicRealDirection_mem_lattice v)

theorem centralRationalCircle_act_coe (v : L) (hv : v ∈ D.filtration.layer s)
    (r : ℝ) (x : D.Space) :
    let := D.metricSpace
    (D.centralRationalCircle v hv).act (r : CircleFourier.Circle) x =
      realBCHLine (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.periodicRealDirection v) r • x := by
  let := D.metricSpace
  exact centralBCHCircleAction_act_coe (D.basis.baseChange ℝ) D.realLattice
    D.realLattice_closed_discrete.1 (D.periodicRealDirection v)
    (D.periodicRealDirection_central v hv) (D.periodicRealDirection_mem_lattice v) r x

theorem centralRationalCircle_commutes (v w : L)
    (hv : v ∈ D.filtration.layer s) (hw : w ∈ D.filtration.layer s) :
    let := D.metricSpace
    (D.centralRationalCircle v hv).Commutes (D.centralRationalCircle w hw) := by
  let := D.metricSpace
  exact centralBCHCircleAction_commutes (D.basis.baseChange ℝ) D.realLattice
    D.realLattice_closed_discrete.1 (D.periodicRealDirection v) (D.periodicRealDirection w)
    (D.periodicRealDirection_central v hv) (D.periodicRealDirection_central w hw)
    (D.periodicRealDirection_mem_lattice v) (D.periodicRealDirection_mem_lattice w)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealProjectedCoefficientLift
namespace OAI

section

namespace Erdos3

theorem lieTreeEval_hom {I L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] (φ : L →ₗ⁅ℚ⁆ M) (v : I → L) (a : FreeMagma I) :
    lieTreeEval (fun i => φ (v i)) a = φ (lieTreeEval v a) := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    simp only [lieTreeEval, ha, hb, LieHom.map_lie]

namespace DegreeRankLieFiltration

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s r : ℕ} (F : DegreeRankLieFiltration L s r) (P : DegreeRankLieFiltration M s r)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ P.layer d 1 → ∀ k, φ x k ∈ F.layer d 1)

end DegreeRankLieFiltration

end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s r : ℕ} (F : DegreeRankLieFiltration L s r) (A : ℕ → Submodule ℚ M)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ A d → ∀ k, φ x k ∈ F.layer d 1)

def layerHorizontalMap (d : ℕ) : A d →ₗ[ℚ] (Fin 4 → F.HigherHorizontal d) :=
  (F.fourHorizontalMap d).comp
    (((φ : M →ₗ[ℚ] (Fin 4 → L)).comp (A d).subtype).codRestrict
      (F.fourHorizontalLayer d)
      (fun x => (F.mem_fourHorizontalLayer d (φ x.val)).mpr (hφ d x.val x.property)))

def layerHorizontalImage (d : ℕ) : Submodule ℚ (Fin 4 → F.HigherHorizontal d) :=
  LinearMap.range (F.layerHorizontalMap A φ hφ d)

theorem mem_layerHorizontalImage (d : ℕ) (v : Fin 4 → F.HigherHorizontal d) :
    v ∈ F.layerHorizontalImage A φ hφ d ↔
      ∃ w : A d, F.layerHorizontalMap A φ hφ d w = v := Iff.rfl

theorem layerHorizontalImage_frequency {E : Type*} [AddCommGroup E] [Module ℚ E]
    (η : L →ₗ[ℚ] E) (d : I → ℕ) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hker : ∀ u : I → M, (∀ i, u i ∈ A (d i)) →
      η (φ (lieTreeEval u a) 0) + η (φ (lieTreeEval u a) 1) -
        η (φ (lieTreeEval u a) 2) - η (φ (lieTreeEval u a) 3) = 0)
    (v : ∀ i, Fin 4 → F.HigherHorizontal (d i))
    (hv : ∀ i, v i ∈ F.layerHorizontalImage A φ hφ (d i)) :
    η (F.horizontalTreeValue d a (fun i => v i 0)) +
      η (F.horizontalTreeValue d a (fun i => v i 1)) -
      η (F.horizontalTreeValue d a (fun i => v i 2)) -
      η (F.horizontalTreeValue d a (fun i => v i 3)) = 0 := by
  classical
  have hlift (i : I) := (F.mem_layerHorizontalImage A φ hφ (d i) (v i)).mp (hv i)
  choose w hw using hlift
  let u (i : I) : M := (w i).val
  let lifted (k : Fin 4) (i : I) : F.layer (d i) 1 :=
    ⟨φ (u i) k, hφ (d i) (u i) (w i).property k⟩
  have hmap (k : Fin 4) :
      (fun i => F.higherHorizontalMk (d i) (lifted k i)) = (fun i => v i k) := by
    funext i
    exact congrFun (hw i) k
  have hvalue (k : Fin 4) : F.horizontalTreeValue d a (fun i => v i k) = φ (lieTreeEval u a) k := by
    rw [← hmap k]
    calc
      _ = lieTreeEval (fun i => φ (u i) k) a := F.horizontalTreeValue_mk d a hd hr (lifted k)
      _ = lieTreeEval (fun i => φ (u i)) a k := (lieTreeEval_pi _ a k).symm
      _ = _ := congrFun (lieTreeEval_hom φ u a) k
  rw [hvalue 0, hvalue 1, hvalue 2, hvalue 3]
  exact hker u (fun i => (w i).property)

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L M E : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [AddCommGroup E] [Module ℚ E] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (P : DegreeRankLieFiltration M s r)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ P.layer d 1 → ∀ k, φ x k ∈ F.layer d 1)

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L M E : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [AddCommGroup E] [Module ℚ E] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (A : ℕ → Submodule ℚ M)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ A d → ∀ k, φ x k ∈ F.layer d 1)

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

include hφ in
theorem projectedComponent_mem_layer (k : Fin 4) (d : ℕ) (x : M) (hx : x ∈ F.layer d) :
    ((liePiEval k).comp φ) x ∈ G.associatedDegree.layer d := by
  change φ x k ∈ G.layer d 0
  rw [G.rank_zero_eq_one]
  exact hφ d x hx k

noncomputable def projectedComponentSymbolMap (w : σ → ℕ) (k : Fin 4) :
    F.PolynomialSymbol w →ₗ⁅ℚ⁆ G.associatedDegree.PolynomialSymbol w :=
  F.filteredPolynomialSymbolMap G.associatedDegree ((liePiEval k).comp φ)
    (G.projectedComponent_mem_layer F φ hφ k) w

noncomputable def projectedHorizontalSymbolCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.PolynomialSymbol w →ₗ[ℚ] (Fin 4 → G.HigherHorizontal (Finsupp.weight w α)) :=
  LinearMap.pi (fun k => (G.higherHorizontalSymbolCoefficient w α).comp
    (G.projectedComponentSymbolMap F φ hφ w k).toLinearMap)

theorem projectedHorizontalSymbolCoefficient_symbol (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.adaptedLieSubalgebra w) :
    G.projectedHorizontalSymbolCoefficient F φ hφ w α (F.polynomialSymbolMap w p) =
      G.layerHorizontalMap F.layer φ hφ (Finsupp.weight w α)
        ⟨coefficients p.val α, p.property α⟩ := by
  funext k
  change G.higherHorizontalSymbolCoefficient w α
    (F.filteredPolynomialSymbolMap G.associatedDegree ((liePiEval k).comp φ)
      (G.projectedComponent_mem_layer F φ hφ k) w (F.polynomialSymbolMap w p)) = _
  rw [F.filteredPolynomialSymbolMap_symbol, G.higherHorizontalSymbolCoefficient_map]
  apply congrArg (G.higherHorizontalMk (Finsupp.weight w α))
  apply Subtype.ext
  exact F.filteredPolynomialMap_coefficient G.associatedDegree ((liePiEval k).comp φ)
    (G.projectedComponent_mem_layer F φ hφ k) w p α

theorem projectedHorizontalSymbolCoefficient_lie (w : σ → ℕ) (α : σ →₀ ℕ)
    (x y : F.PolynomialSymbol w) :
    G.projectedHorizontalSymbolCoefficient F φ hφ w α ⁅x, y⁆ = 0 := by
  funext k
  change G.higherHorizontalSymbolCoefficient w α
    ((G.projectedComponentSymbolMap F φ hφ w k) ⁅x, y⁆) = 0
  rw [LieHom.map_lie]
  exact G.higherHorizontalSymbolCoefficient_lie w α _ _

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

noncomputable def realProjectedHorizontalSymbolHom (ht : 1 ≤ t) (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.RealPolynomialSymbolGroup w →*
      Multiplicative (ℝ ⊗[ℚ] (Fin 4 → G.HigherHorizontal (Finsupp.weight w α))) where
  toFun X := Multiplicative.ofAdd
    ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ X.coord)
  map_one' := by
    change Multiplicative.ofAdd ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ 0) = 1
    rw [map_zero]
    rfl
  map_mul' X Y := by
    change Multiplicative.ofAdd ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
      (lieBCH t X.coord Y.coord)) = Multiplicative.ofAdd
        ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ X.coord +
          (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ Y.coord)
    exact congrArg Multiplicative.ofAdd (linearMap_baseChange_lieBCH_eq_add
      (G.projectedHorizontalSymbolCoefficient F φ hφ w α)
      (G.projectedHorizontalSymbolCoefficient_lie F φ hφ w α) ht X.coord Y.coord)

@[simp] theorem realProjectedHorizontalSymbolHom_apply (ht : 1 ≤ t) (w : σ → ℕ) (α : σ →₀ ℕ)
    (X : F.RealPolynomialSymbolGroup w) :
    Multiplicative.toAdd (G.realProjectedHorizontalSymbolHom F φ hφ ht w α X) =
      (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ X.coord := rfl

theorem real_projectedHorizontalSymbolCoefficient_component (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.PolynomialSymbol w) (k : Fin 4) :
    (LinearMap.proj k : (Fin 4 → G.HigherHorizontal (Finsupp.weight w α)) →ₗ[ℚ]
      G.HigherHorizontal (Finsupp.weight w α)).baseChange ℝ
        ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ x) =
      (G.higherHorizontalSymbolCoefficient w α).baseChange ℝ
        ((G.projectedComponentSymbolMap F φ hφ w k).toLinearMap.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp only [LinearMap.baseChange_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r)

noncomputable def realFourHorizontalMap (d : ℕ) :
    (G.fourHorizontalLayer d).baseChange ℝ →ₗ[ℝ]
      ℝ ⊗[ℚ] (Fin 4 → G.HigherHorizontal d) :=
  ((G.fourHorizontalMap d).baseChange ℝ).comp
    (realificationSubmoduleEquiv (G.fourHorizontalLayer d)).symm.toLinearMap

@[simp] theorem realFourHorizontalMap_baseChange (d : ℕ)
    (v : ℝ ⊗[ℚ] G.fourHorizontalLayer d) :
    G.realFourHorizontalMap d (realificationSubmoduleEquiv (G.fourHorizontalLayer d) v) =
      (G.fourHorizontalMap d).baseChange ℝ v := by
  exact congrArg ((G.fourHorizontalMap d).baseChange ℝ)
    ((realificationSubmoduleEquiv (G.fourHorizontalLayer d)).symm_apply_apply v)

variable (F : NilpotentLieFiltration M t) (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

noncomputable def projectedLayerCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.adaptedLieSubalgebra w →ₗ[ℚ] G.fourHorizontalLayer (Finsupp.weight w α) :=
  (φ.toLinearMap.comp (F.adaptedCoefficientMap w α)).codRestrict
    (G.fourHorizontalLayer (Finsupp.weight w α))
    (fun p => (G.mem_fourHorizontalLayer _ _).mpr (hφ _ _ (p.property α)))

@[simp] theorem projectedLayerCoefficient_coe (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.adaptedLieSubalgebra w) :
    (G.projectedLayerCoefficient F φ hφ w α p : Fin 4 → L) = φ (coefficients p.val α) := rfl

theorem projectedLayerCoefficient_horizontal (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.adaptedLieSubalgebra w) :
    G.fourHorizontalMap (Finsupp.weight w α) (G.projectedLayerCoefficient F φ hφ w α p) =
      G.projectedHorizontalSymbolCoefficient F φ hφ w α (F.polynomialSymbolMap w p) := by
  rw [G.projectedHorizontalSymbolCoefficient_symbol]
  rfl

theorem projectedLayerCoefficient_tensor_coe (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    (G.fourHorizontalLayer (Finsupp.weight w α)).subtype.baseChange ℝ
        ((G.projectedLayerCoefficient F φ hφ w α).baseChange ℝ x) =
      φ.toLinearMap.baseChange ℝ (coefficients (F.realAdaptedPolynomialMap w x) α) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    simp only [LinearMap.baseChange_tmul, G.projectedLayerCoefficient_coe,
      F.realAdaptedPolynomialMap_coefficient_tmul, Submodule.subtype_apply]
    rfl
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem projectedLayerCoefficient_tensor_horizontal (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    (G.fourHorizontalMap (Finsupp.weight w α)).baseChange ℝ
        ((G.projectedLayerCoefficient F φ hφ w α).baseChange ℝ x) =
      (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
        (F.realExtendedSymbolMap w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    change (G.fourHorizontalMap (Finsupp.weight w α)).baseChange ℝ
      ((G.projectedLayerCoefficient F φ hφ w α).baseChange ℝ (a ⊗ₜ[ℚ] p)) =
        (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
          (a ⊗ₜ[ℚ] F.polynomialSymbolMap w p)
    simp only [LinearMap.baseChange_tmul, G.projectedLayerCoefficient_horizontal]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (b : Basis ι ℚ M) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hφ hF in
theorem real_projectedCoefficient_mem (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.realification.adaptedLieSubalgebra w) :
    φ.toLinearMap.baseChange ℝ (coefficients p.val α) ∈
      (G.fourHorizontalLayer (Finsupp.weight w α)).baseChange ℝ := by
  obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p
  rw [F.realAdaptedPolynomialTensor_coe, ← G.projectedLayerCoefficient_tensor_coe F φ hφ]
  exact (realificationSubmoduleEquiv (G.fourHorizontalLayer (Finsupp.weight w α))
    ((G.projectedLayerCoefficient F φ hφ w α).baseChange ℝ x)).property

theorem real_projectedCoefficient_horizontal (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.realification.adaptedLieSubalgebra w)
    (v : (G.fourHorizontalLayer (Finsupp.weight w α)).baseChange ℝ)
    (hv : v.val = φ.toLinearMap.baseChange ℝ (coefficients p.val α)) :
    G.realFourHorizontalMap (Finsupp.weight w α) v =
      (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
        (F.realPolynomialSymbolMap b ω hF w p) := by
  obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p
  have heq : v = realificationSubmoduleEquiv (G.fourHorizontalLayer (Finsupp.weight w α))
      ((G.projectedLayerCoefficient F φ hφ w α).baseChange ℝ x) := by
    apply Subtype.ext
    exact hv.trans (G.projectedLayerCoefficient_tensor_coe F φ hφ w α x).symm
  rw [heq, G.realFourHorizontalMap_baseChange, G.projectedLayerCoefficient_tensor_horizontal]
  change _ = (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
    (F.realSymbolOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w x))
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap]

end Erdos3.DegreeRankLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ProductFrequencyKernel
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

noncomputable def piFrequency (eta : ∀ i, L i →ₗ[ℚ] ℚ) : (∀ i, L i) →ₗ[ℚ] ℚ :=
  ∑ i, (eta i).comp (liePiEval i).toLinearMap

theorem piFrequency_apply (eta : ∀ i, L i →ₗ[ℚ] ℚ) (x : ∀ i, L i) :
    piFrequency eta x = ∑ i, eta i (x i) := by
  simp only [piFrequency, LinearMap.sum_apply, LinearMap.comp_apply, LieHom.coe_toLinearMap,
    liePiEval_apply]

theorem piFrequency_single (eta : ∀ i, L i →ₗ[ℚ] ℚ) (i : ι) (x : L i) :
    letI := Classical.decEq ι
    piFrequency eta (Pi.single i x) = eta i x := by
  classical
  rw [piFrequency_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

theorem realify_piFrequency (eta : ∀ i, L i →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] (∀ i, L i)) :
    realifyFunctional (piFrequency eta) x =
      ∑ i, realifyFunctional (eta i) (realificationLieHom (liePiEval i) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realifyFunctional_tmul, piFrequency_apply, Rat.cast_sum,
      realificationLieHom_tmul, liePiEval_apply, Finset.mul_sum]
  | add x y hx hy => simp only [map_add, hx, hy, Finset.sum_add_distrib]

namespace RationalFilteredNilmanifold

variable {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem piFrequency_basis (eta : ∀ i, L i →ₗ[ℚ] ℚ)
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
    piFrequency eta ((pi D).basis k) = eta z.1 ((D z.1).basis z.2) := by
  classical
  change piFrequency eta (productFinBasis D k) = _
  rw [productFinBasis, Basis.reindex_apply]
  generalize hz : (Fintype.equivFin (Σ i, Fin (d i))).symm k = z
  rcases z with ⟨i, j⟩
  rw [Pi.basis_apply, piFrequency_single]

theorem piFrequency_logHeight (eta : ∀ i, L i →ₗ[ℚ] ℚ) {p : ℝ}
    (hheight : ∀ i j, rationalLogHeight (eta i ((D i).basis j)) ≤ p)
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    rationalLogHeight (piFrequency eta ((pi D).basis k)) ≤ p := by
  rw [piFrequency_basis D]
  exact hheight _ _

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s r : ℕ} (F : DegreeRankLieFiltration L s r)

def horizontalImageOfSubmodule (B : Submodule ℚ (Fin 4 → L)) (d : ℕ) :
    Submodule ℚ (Fin 4 → F.HigherHorizontal d) :=
  (B.comap (F.fourHorizontalLayer d).subtype).map (F.fourHorizontalMap d)

theorem layerHorizontalImage_eq_of_submodule (A : ℕ → Submodule ℚ M)
    (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
    (hφ : ∀ d x, x ∈ A d → ∀ k, φ x k ∈ F.layer d 1) (d : ℕ) :
    F.layerHorizontalImage A φ hφ d =
      F.horizontalImageOfSubmodule ((A d).map φ.toLinearMap) d := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨φ x.val, (F.mem_fourHorizontalLayer d _).mpr (hφ d x.val x.property)⟩, ?_, rfl⟩
    exact ⟨x.val, x.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply congrArg (F.fourHorizontalMap d)
    exact Subtype.ext hxy

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module

variable {ι μ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

noncomputable def higherHorizontalCoordinates : F.HigherHorizontal d →ₗ[ℚ] (ι → ℚ) :=
  f.equivFun.toLinearMap.comp (F.higherHorizontalAmbient d)

noncomputable def ambientHorizontalCoordinates : L →ₗ[ℚ] (ι → ℚ) :=
  f.equivFun.toLinearMap.comp (F.layer d 2).mkQ

theorem higherHorizontalCoordinates_injective : Function.Injective (F.higherHorizontalCoordinates d f) :=
  f.equivFun.injective.comp (F.higherHorizontalAmbient_injective d)

noncomputable def fourHorizontalCoordinates :
    (Fin 4 → F.HigherHorizontal d) →ₗ[ℚ] (Fin 4 → ι → ℚ) :=
  LinearMap.pi (fun k => (F.higherHorizontalCoordinates d f).comp (LinearMap.proj k))

noncomputable def fourAmbientCoordinates : (Fin 4 → L) →ₗ[ℚ] (Fin 4 → ι → ℚ) :=
  LinearMap.pi (fun k => (F.ambientHorizontalCoordinates d f).comp (LinearMap.proj k))

theorem fourHorizontalCoordinates_map (x : F.fourHorizontalLayer d) :
    F.fourHorizontalCoordinates d f (F.fourHorizontalMap d x) =
      F.fourAmbientCoordinates d f x.val := by
  ext k i
  rfl

theorem horizontalImage_coordinates (B : Submodule ℚ (Fin 4 → L))
    (hB : B ≤ F.fourHorizontalLayer d) :
    (F.horizontalImageOfSubmodule B d).map (F.fourHorizontalCoordinates d f) =
      B.map (F.fourAmbientCoordinates d f) := by
  ext v
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x.val, hx, (F.fourHorizontalCoordinates_map d f x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    let y : F.fourHorizontalLayer d := ⟨x, hB hx⟩
    exact ⟨F.fourHorizontalMap d y, ⟨y, hx, rfl⟩, F.fourHorizontalCoordinates_map d f y⟩

theorem fourAmbientCoordinates_height [Fintype μ] (b : Basis μ ℚ L) {H K : ℕ}
    (hf : ∀ i j, RationalHeightLE (f.repr ((F.layer d 2).mkQ (b j)) i) H)
    (x : Fin 4 → L) (hx : ∀ k j, RationalHeightLE (b.repr (x k) j) K)
    (k : Fin 4) (i : ι) :
    RationalHeightLE (F.fourAmbientCoordinates d f x k i)
      ((Fintype.card μ + 1) * (K * H) ^ Fintype.card μ) :=
  linearMap_coordinate_height b f (F.layer d 2).mkQ (fun j i => hf i j) (x k) (hx k) i

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

noncomputable def realFourCoordinateEquiv :
    (ℝ ⊗[ℚ] (Fin 4 → ι → ℚ)) ≃ₗ[ℝ] ((Σ _ : Fin 4, ι) → ℝ) :=
  ((Pi.basis (fun _ : Fin 4 => Pi.basisFun ℚ ι)).baseChange ℝ).equivFun

noncomputable def realFourHorizontalCoordinates :
    (ℝ ⊗[ℚ] (Fin 4 → F.HigherHorizontal d)) →ₗ[ℝ] ((Σ _ : Fin 4, ι) → ℝ) :=
  (realFourCoordinateEquiv (ι := ι)).toLinearMap.comp
    ((F.fourHorizontalCoordinates d f).baseChange ℝ)

noncomputable def realFourAmbientCoordinates :
    (ℝ ⊗[ℚ] (Fin 4 → L)) →ₗ[ℝ] ((Σ _ : Fin 4, ι) → ℝ) :=
  (realFourCoordinateEquiv (ι := ι)).toLinearMap.comp
    ((F.fourAmbientCoordinates d f).baseChange ℝ)

theorem realFourHorizontalCoordinates_tensor_map (x : ℝ ⊗[ℚ] F.fourHorizontalLayer d) :
    F.realFourHorizontalCoordinates d f ((F.fourHorizontalMap d).baseChange ℝ x) =
      F.realFourAmbientCoordinates d f ((F.fourHorizontalLayer d).subtype.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change realFourCoordinateEquiv
      ((F.fourHorizontalCoordinates d f).baseChange ℝ ((F.fourHorizontalMap d).baseChange ℝ (a ⊗ₜ[ℚ] x))) =
        realFourCoordinateEquiv
          ((F.fourAmbientCoordinates d f).baseChange ℝ
            ((F.fourHorizontalLayer d).subtype.baseChange ℝ (a ⊗ₜ[ℚ] x)))
    simp only [LinearMap.baseChange_tmul, F.fourHorizontalCoordinates_map]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realFourHorizontalCoordinates_map (x : (F.fourHorizontalLayer d).baseChange ℝ) :
    F.realFourHorizontalCoordinates d f (F.realFourHorizontalMap d x) =
      F.realFourAmbientCoordinates d f x.val := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv (F.fourHorizontalLayer d)).surjective x
  rw [F.realFourHorizontalMap_baseChange]
  exact F.realFourHorizontalCoordinates_tensor_map d f v

theorem realFourHorizontalCoordinates_image (J : Submodule ℚ (Fin 4 → F.HigherHorizontal d)) :
    (J.baseChange ℝ).map (F.realFourHorizontalCoordinates d f) =
      ((J.map (F.fourHorizontalCoordinates d f)).baseChange ℝ).map
        (realFourCoordinateEquiv (ι := ι)).toLinearMap := by
  rw [realification_map]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(F.fourHorizontalCoordinates d f).baseChange ℝ x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem realFourAmbientCoordinates_component (x : ℝ ⊗[ℚ] (Fin 4 → L)) (k : Fin 4) (i : ι) :
    F.realFourAmbientCoordinates d f x ⟨k, i⟩ =
      (f.baseChange ℝ).repr ((F.layer d 2).mkQ.baseChange ℝ ((LinearMap.proj k).baseChange ℝ x)) i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change ((Pi.basis (fun _ : Fin 4 => Pi.basisFun ℚ ι)).baseChange ℝ).repr
      (a ⊗ₜ[ℚ] F.fourAmbientCoordinates d f x) ⟨k, i⟩ =
        (f.baseChange ℝ).repr (a ⊗ₜ[ℚ] (F.layer d 2).mkQ (x k)) i
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul, Pi.basis_repr]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, Finsupp.add_apply, hx, hy]

theorem realFourHorizontalCoordinates_component
    (x : ℝ ⊗[ℚ] (Fin 4 → F.HigherHorizontal d)) (k : Fin 4) (i : ι) :
    F.realFourHorizontalCoordinates d f x ⟨k, i⟩ =
      (f.baseChange ℝ).repr
        ((F.higherHorizontalAmbient d).baseChange ℝ ((LinearMap.proj k).baseChange ℝ x)) i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change ((Pi.basis (fun _ : Fin 4 => Pi.basisFun ℚ ι)).baseChange ℝ).repr
      (a ⊗ₜ[ℚ] F.fourHorizontalCoordinates d f x) ⟨k, i⟩ =
        (f.baseChange ℝ).repr (a ⊗ₜ[ℚ] F.higherHorizontalAmbient d (x k)) i
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul, Pi.basis_repr]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, Finsupp.add_apply, hx, hy]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ : Type*} [Fintype ι]

noncomputable def realRationalCoordinateEquiv : (ℝ ⊗[ℚ] (ι → ℚ)) ≃ₗ[ℝ] (ι → ℝ) :=
  ((Pi.basisFun ℚ ι).baseChange ℝ).equivFun

theorem realRationalCoordinateEquiv_tmul (a : ℝ) (x : ι → ℚ) (i : ι) :
    realRationalCoordinateEquiv (a ⊗ₜ[ℚ] x) i = a * (x i : ℝ) := by
  change ((Pi.basisFun ℚ ι).baseChange ℝ).repr (a ⊗ₜ[ℚ] x) i = _
  rw [Basis.baseChange_repr_tmul]
  change (x i) • a = _
  simp only [Rat.smul_def, mul_comm]

theorem realFourCoordinateEquiv_tmul (a : ℝ) (x : Fin 4 → ι → ℚ) (j : Σ _ : Fin 4, ι) :
    DegreeRankLieFiltration.realFourCoordinateEquiv (a ⊗ₜ[ℚ] x) j = a * (x j.1 j.2 : ℝ) := by
  change ((Pi.basis (fun _ : Fin 4 => Pi.basisFun ℚ ι)).baseChange ℝ).repr
    (a ⊗ₜ[ℚ] x) j = _
  rw [Basis.baseChange_repr_tmul, Pi.basis_repr]
  change (x j.1 j.2) • a = _
  simp only [Rat.smul_def, mul_comm]

noncomputable def realRationalCoordinateSpan (U : Submodule ℚ (ι → ℚ)) : Submodule ℝ (ι → ℝ) :=
  (U.baseChange ℝ).map realRationalCoordinateEquiv.toLinearMap

noncomputable def realFourCoordinateSpan (J : Submodule ℚ (Fin 4 → ι → ℚ)) :
    Submodule ℝ ((Σ _ : Fin 4, ι) → ℝ) :=
  (J.baseChange ℝ).map DegreeRankLieFiltration.realFourCoordinateEquiv.toLinearMap

theorem realCoordinate_projection (x : ℝ ⊗[ℚ] (Fin 4 → ι → ℚ)) (k : Fin 4) (i : ι) :
    realRationalCoordinateEquiv ((LinearMap.proj k).baseChange ℝ x) i =
      DegreeRankLieFiltration.realFourCoordinateEquiv x ⟨k, i⟩ := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, realRationalCoordinateEquiv_tmul, realFourCoordinateEquiv_tmul]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem realFourCoordinateSpan_span (v : κ → Fin 4 → ι → ℚ) :
    realFourCoordinateSpan (Submodule.span ℚ (Set.range v)) =
      Submodule.span ℝ (Set.range (fun a (j : Σ _ : Fin 4, ι) => (v a j.1 j.2 : ℝ))) := by
  unfold realFourCoordinateSpan
  rw [Submodule.baseChange_span, Submodule.map_span, Set.image_image]
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    refine ⟨a, ?_⟩
    funext j
    change (v a j.1 j.2 : ℝ) =
      DegreeRankLieFiltration.realFourCoordinateEquiv (1 ⊗ₜ[ℚ] v a) j
    simpa only [one_mul] using (realFourCoordinateEquiv_tmul (1 : ℝ) (v a) j).symm
  · rintro ⟨a, rfl⟩
    refine ⟨v a, ⟨a, rfl⟩, ?_⟩
    funext j
    change DegreeRankLieFiltration.realFourCoordinateEquiv (1 ⊗ₜ[ℚ] v a) j =
      (v a j.1 j.2 : ℝ)
    simpa only [one_mul] using realFourCoordinateEquiv_tmul (1 : ℝ) (v a) j

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L ι μ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  {E V : Submodule ℚ L}

noncomputable def realQuotientCoordinateMap (f : Basis ι ℚ (L ⧸ V)) :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi (fun i => ((f.baseChange ℝ).coord i).comp (V.mkQ.baseChange ℝ))

@[simp] theorem realQuotientCoordinateMap_apply (f : Basis ι ℚ (L ⧸ V))
    (x : ℝ ⊗[ℚ] L) (i : ι) :
    realQuotientCoordinateMap f x i = (f.baseChange ℝ).repr (V.mkQ.baseChange ℝ x) i := rfl

theorem realQuotientCoordinateMap_tmul_one (f : Basis ι ℚ (L ⧸ V)) (x : L) (i : ι) :
    realQuotientCoordinateMap f ((1 : ℝ) ⊗ₜ[ℚ] x) i = (f.repr (V.mkQ x) i : ℝ) := by
  rw [realQuotientCoordinateMap_apply, LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

theorem realQuotientCoordinateMap_eq_zero_iff (f : Basis ι ℚ (L ⧸ V)) (x : ℝ ⊗[ℚ] L) :
    realQuotientCoordinateMap f x = 0 ↔ x ∈ V.baseChange ℝ := by
  rw [← realification_mkQ_eq_zero_iff]
  constructor
  · intro h
    apply (f.baseChange ℝ).repr.injective
    ext i
    simpa only [realQuotientCoordinateMap_apply, map_zero, Finsupp.zero_apply, Pi.zero_apply]
      using congrFun h i
  · intro h
    funext i
    simp only [realQuotientCoordinateMap_apply, h, map_zero, Finsupp.zero_apply, Pi.zero_apply]

noncomputable def subspaceQuotientMatrix (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) :
    Matrix ι ν ℚ := fun i n => f.repr (V.mkQ (e n : L)) i

theorem subspaceQuotientMatrix_real_apply [Fintype ν]
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (x : ν → ℝ) :
    (fun i n => (subspaceQuotientMatrix e f i n : ℝ)) *ᵥ x =
      realQuotientCoordinateMap f (bracketSystemLift e x) := by
  classical
  have h : Matrix.mulVecLin (fun i n => (subspaceQuotientMatrix e f i n : ℝ)) =
      (realQuotientCoordinateMap f).comp (bracketSystemLift e) := by
    apply (Pi.basisFun ℝ ν).ext
    intro n
    change Matrix.of (fun i t => (subspaceQuotientMatrix e f i t : ℝ)) *ᵥ Pi.single n 1 =
      realQuotientCoordinateMap f (bracketSystemLift e (Pi.single n 1))
    rw [Matrix.mulVec_single_one, bracketSystemLift_single]
    funext i
    exact (realQuotientCoordinateMap_tmul_one f (e n : L) i).symm
  exact DFunLike.congr_fun h x

theorem exists_subspace_basis_coordinates [Fintype ν] (e : Basis ν ℚ E)
    (x : ℝ ⊗[ℚ] L) (hx : x ∈ E.baseChange ℝ) :
    ∃ v : ν → ℝ, bracketSystemLift e v = x := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(e.baseChange ℝ).equivFun y, ?_⟩
  simp only [bracketSystemLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

theorem subspaceQuotientMatrix_height [Fintype μ] (b : Basis μ ℚ L)
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) {H J : ℕ}
    (hq : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b i)) n) H)
    (he : ∀ n i, RationalHeightLE (b.repr (e n : L) i) J) (i : ι) (n : ν) :
    RationalHeightLE (subspaceQuotientMatrix e f i n)
      ((Fintype.card μ + 1) * (J * H) ^ Fintype.card μ) :=
  linearMap_coordinate_height b f V.mkQ hq (e n : L) (he n) i

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {ι κ : Type*} [Fintype ι]

theorem realRationalCoordinateSpan_span (v : κ → ι → ℚ) :
    realRationalCoordinateSpan (Submodule.span ℚ (Set.range v)) =
      Submodule.span ℝ (Set.range (fun a i => (v a i : ℝ))) := by
  unfold realRationalCoordinateSpan
  rw [Submodule.baseChange_span, Submodule.map_span, Set.image_image]
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    refine ⟨a, ?_⟩
    funext i
    change (v a i : ℝ) = realRationalCoordinateEquiv (1 ⊗ₜ[ℚ] v a) i
    simpa only [one_mul] using (realRationalCoordinateEquiv_tmul (1 : ℝ) (v a) i).symm
  · rintro ⟨a, rfl⟩
    refine ⟨v a, ⟨a, rfl⟩, ?_⟩
    funext i
    change realRationalCoordinateEquiv (1 ⊗ₜ[ℚ] v a) i = (v a i : ℝ)
    simpa only [one_mul] using realRationalCoordinateEquiv_tmul (1 : ℝ) (v a) i

theorem realRationalCoordinateSpan_eq_image [Fintype κ]
    (U : Submodule ℚ (ι → ℚ)) (v : κ → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) = U) :
    realRationalCoordinateSpan U =
      LinearMap.range (Matrix.mulVecLin (fun i a => (v a i : ℝ))) := by
  rw [← hv, realRationalCoordinateSpan_span]
  ext x
  exact real_column_span_mem_iff (fun i a => v a i) x

end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

noncomputable def realHigherHorizontalCoordinates : (ℝ ⊗[ℚ] F.HigherHorizontal d) →ₗ[ℝ] (ι → ℝ) :=
  realRationalCoordinateEquiv.toLinearMap.comp ((F.higherHorizontalCoordinates d f).baseChange ℝ)

theorem realHigherHorizontalCoordinates_component (x : ℝ ⊗[ℚ] F.HigherHorizontal d) (i : ι) :
    F.realHigherHorizontalCoordinates d f x i =
      (f.baseChange ℝ).repr ((F.higherHorizontalAmbient d).baseChange ℝ x) i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change ((Pi.basisFun ℚ ι).baseChange ℝ).repr
      (a ⊗ₜ[ℚ] F.higherHorizontalCoordinates d f x) i =
        (f.baseChange ℝ).repr (a ⊗ₜ[ℚ] F.higherHorizontalAmbient d x) i
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, Finsupp.add_apply, hx, hy]

theorem realHigherHorizontalCoordinates_injective :
    Function.Injective (F.realHigherHorizontalCoordinates d f) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact realRationalCoordinateEquiv.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ)
      (F.higherHorizontalCoordinates d f) (F.higherHorizontalCoordinates_injective d f))

theorem realHigherHorizontalCoordinates_image (U : Submodule ℚ (F.HigherHorizontal d)) :
    (U.baseChange ℝ).map (F.realHigherHorizontalCoordinates d f) =
      realRationalCoordinateSpan (U.map (F.higherHorizontalCoordinates d f)) := by
  unfold realRationalCoordinateSpan
  rw [realification_map]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(F.higherHorizontalCoordinates d f).baseChange ℝ x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L ι μ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype ι] [Fintype μ] {V : Submodule ℚ L}

noncomputable def quotientCoordinateMatrix (b : Basis μ ℚ L) (f : Basis ι ℚ (L ⧸ V)) :
    Matrix ι μ ℚ := fun i j => f.repr (V.mkQ (b j)) i

omit [Fintype ι] in
theorem realQuotientCoordinateMap_eq_matrix (b : Basis μ ℚ L) (f : Basis ι ℚ (L ⧸ V))
    (x : ℝ ⊗[ℚ] L) :
    realQuotientCoordinateMap f x =
      (fun i j => (quotientCoordinateMatrix b f i j : ℝ)) *ᵥ (b.baseChange ℝ).equivFun x := by
  classical
  have h : (realQuotientCoordinateMap f).comp
      (b.baseChange ℝ).equivFun.symm.toLinearMap =
        Matrix.mulVecLin (fun i j => (quotientCoordinateMatrix b f i j : ℝ)) := by
    apply (Pi.basisFun ℝ μ).ext
    intro j
    change realQuotientCoordinateMap f ((b.baseChange ℝ).equivFun.symm (Pi.single j 1)) =
      Matrix.of (fun i n => (quotientCoordinateMatrix b f i n : ℝ)) *ᵥ Pi.single j 1
    rw [Basis.equivFun_symm_single, Matrix.mulVec_single_one, Basis.baseChange_apply]
    funext i
    exact realQuotientCoordinateMap_tmul_one f (b j) i
  have hx := DFunLike.congr_fun h ((b.baseChange ℝ).equivFun x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hx
  exact hx.trans (Matrix.mulVecLin_apply _ _)

theorem realQuotientCoordinateMap_norm_bound (b : Basis μ ℚ L) (f : Basis ι ℚ (L ⧸ V))
    {H : ℕ} (hf : ∀ i j, RationalHeightLE (f.repr (V.mkQ (b j)) i) H)
    (x : ℝ ⊗[ℚ] L) :
    ‖realQuotientCoordinateMap f x‖ ≤
      ((Fintype.card μ : ℝ) + 1) * (H + 1) * ‖(b.baseChange ℝ).equivFun x‖ := by
  rw [realQuotientCoordinateMap_eq_matrix b f x]
  exact norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hf i j).abs_real_le) _

theorem realQuotientCoordinateMap_grid (b : Basis μ ℚ L) (f : Basis ι ℚ (L ⧸ V))
    (l : ℕ) (x : ℝ ⊗[ℚ] L) (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    realQuotientCoordinateMap f x ∈
      realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix b f) * l) := by
  rw [realQuotientCoordinateMap_eq_matrix b f x]
  exact real_matrix_denominator_grid (quotientCoordinateMatrix b f) l _ hx

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem real_pi_projection_coordinates {μ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (b : Basis μ ℚ L) (x : ℝ ⊗[ℚ] (Fin 4 → L)) (k : Fin 4) (i : μ) :
    (b.baseChange ℝ).repr ((LinearMap.proj k).baseChange ℝ x) i =
      ((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).repr x ⟨k, i⟩ :=
  (realification_pi_basis_repr (fun _ : Fin 4 => b) x k i).symm

namespace DegreeRankLieFiltration

variable {ι μ L : Type*} [Fintype ι] [Fintype μ] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))
  (b : Basis μ ℚ L)

theorem realFourAmbientCoordinates_bound {H : ℕ}
    (hf : ∀ i j, RationalHeightLE (f.repr ((F.layer d 2).mkQ (b j)) i) H)
    (x : ℝ ⊗[ℚ] (Fin 4 → L)) {B : ℝ} (hB : 0 ≤ B)
    (hx : ∀ j, |((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).repr x j| ≤ B)
    (k : Fin 4) (i : ι) :
    |F.realFourAmbientCoordinates d f x ⟨k, i⟩| ≤
      ((Fintype.card μ : ℝ) + 1) * (H + 1) * B := by
  let y := (LinearMap.proj k).baseChange ℝ x
  have hy : ‖(b.baseChange ℝ).equivFun y‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro j
    rw [Real.norm_eq_abs]
    change |(b.baseChange ℝ).repr ((LinearMap.proj k).baseChange ℝ x) j| ≤ B
    rw [real_pi_projection_coordinates]
    exact hx ⟨k, j⟩
  rw [F.realFourAmbientCoordinates_component]
  calc
    _ = ‖realQuotientCoordinateMap f y i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖realQuotientCoordinateMap f y‖ := norm_le_pi_norm _ i
    _ ≤ ((Fintype.card μ : ℝ) + 1) * (H + 1) * ‖(b.baseChange ℝ).equivFun y‖ :=
      realQuotientCoordinateMap_norm_bound b f hf y
    _ ≤ _ := mul_le_mul_of_nonneg_left hy (by positivity)

theorem realFourAmbientCoordinates_grid (l : ℕ) (x : ℝ ⊗[ℚ] (Fin 4 → L))
    (hx : (fun j => ((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).repr x j) ∈ realDenominatorGrid l) :
    F.realFourAmbientCoordinates d f x ∈
      realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix b f) * l) := by
  obtain ⟨z, hz⟩ := hx
  have hsource (k : Fin 4) :
      (b.baseChange ℝ).equivFun ((LinearMap.proj k).baseChange ℝ x) ∈ realDenominatorGrid l := by
    refine ⟨fun i => z ⟨k, i⟩, ?_⟩
    funext i
    exact (congrFun hz ⟨k, i⟩).trans
      (congrArg (fun y : ℝ => (l : ℝ) * y) (real_pi_projection_coordinates b x k i).symm)
  choose a ha using fun k => realQuotientCoordinateMap_grid b f l
    ((LinearMap.proj k).baseChange ℝ x) (hsource k)
  refine ⟨fun j => a j.1 j.2, ?_⟩
  funext j
  exact (congrFun (ha j.1) j.2).trans
    (congrArg (fun y : ℝ => ((matrixDenominator (quotientCoordinateMatrix b f) * l : ℕ) : ℝ) * y)
      (F.realFourAmbientCoordinates_component d f x j.1 j.2).symm)

end DegreeRankLieFiltration

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.TripleProductBasisBounds
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def productBasisWeight (weight : ∀ i, Fin (d i) → ℕ)
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) : ℕ :=
  let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
  weight z.1 z.2

theorem productFinBasis_repr (x : ∀ i, L i) (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
    (pi D).basis.repr x k = (D z.1).basis.repr (x z.1) z.2 := by
  change (productFinBasis D).repr x k = _
  rw [productFinBasis, Basis.repr_reindex_apply, Pi.basis_repr]

theorem pi_layer_span (weight : ∀ i, Fin (d i) → ℕ)
    (hF : ∀ i n, (D i).filtration.layer n =
      Submodule.span ℚ ((D i).basis '' {k | n ≤ weight i k})) (n : ℕ) :
    (pi D).filtration.layer n =
      Submodule.span ℚ ((pi D).basis '' {k | n ≤ productBasisWeight weight k}) := by
  classical
  ext x
  change x ∈ (NilpotentLieFiltration.pi (fun i => (D i).filtration)).layer n ↔ _
  rw [NilpotentLieFiltration.mem_pi_layer]
  constructor
  · intro hx
    apply (pi D).basis.mem_span_image.mpr
    intro k hk
    have hcoeff : (pi D).basis.repr x k ≠ 0 := Finsupp.mem_support_iff.mp hk
    rw [productFinBasis_repr D] at hcoeff
    let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
    have hm := hx z.1
    rw [hF z.1 n] at hm
    exact (D z.1).basis.mem_span_image.mp hm (Finsupp.mem_support_iff.mpr hcoeff)
  · intro hx i
    rw [hF i n]
    apply (D i).basis.mem_span_image.mpr
    intro k hk
    let q := (Fintype.equivFin (Σ i, Fin (d i))) ⟨i, k⟩
    have hq : (Fintype.equivFin (Σ i, Fin (d i))).symm q = ⟨i, k⟩ :=
      Equiv.symm_apply_apply _ _
    have hrepr : (pi D).basis.repr x q = (D i).basis.repr (x i) k :=
      (productFinBasis_repr D x q).trans
        (congrArg (fun z : Σ i, Fin (d i) => (D z.1).basis.repr (x z.1) z.2) hq)
    have hcoeff : (pi D).basis.repr x q ≠ 0 := by
      rw [hrepr]
      exact Finsupp.mem_support_iff.mp hk
    have hw := (pi D).basis.mem_span_image.mp hx (Finsupp.mem_support_iff.mpr hcoeff)
    change n ≤ productBasisWeight weight q at hw
    have hweight : productBasisWeight weight q = weight i k :=
      congrArg (fun z : Σ i, Fin (d i) => weight z.1 z.2) hq
    exact hw.trans_eq hweight

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem triple_product_basis_logHeight (x : L × L × L) {p : ℝ}
    (hx : ∀ k, rationalLogHeight (D.basis.repr x.1 k) ≤ p ∧
      rationalLogHeight (D.basis.repr x.2.1 k) ≤ p ∧
      rationalLogHeight (D.basis.repr x.2.2 k) ≤ p)
    (k : Fin (Fintype.card (Σ _ : Fin 3, Fin d))) :
    rationalLogHeight ((pi (fun _ : Fin 3 => D)).basis.repr (tripleToPi x) k) ≤ p := by
  have h (j : Fin 3) (l : Fin d) :
      rationalLogHeight (D.basis.repr (tripleToPi x j) l) ≤ p := by
    fin_cases j
    · exact (hx l).1
    · exact (hx l).2.1
    · exact (hx l).2.2
  rw [productFinBasis_repr]
  exact h _ _

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationOrderedBasis
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ)
  (hw : ∀ i, 0 < w i) [Fintype (WeightedBasisIndex w d)]

noncomputable def weightedIndexOrder :
    WeightedBasisIndex w d ≃ Fin (Fintype.card (WeightedBasisIndex w d)) :=
  let ρ := Fintype.equivFin (WeightedBasisIndex w d)
  let u := fun j => weightedBasisGrade w d (ρ.symm j)
  ρ.trans (Tuple.sort u).symm

noncomputable def weightedOrderedBasis :
    Basis (Fin (Fintype.card (WeightedBasisIndex w d))) ℚ (weightedSubalgebra w d) :=
  (weightedBasis w d hw).reindex (weightedIndexOrder w d)

noncomputable def weightedOrderedGrade (j : Fin (Fintype.card (WeightedBasisIndex w d))) : ℕ :=
  weightedBasisGrade w d ((weightedIndexOrder w d).symm j)

theorem weightedOrderedBasis_layers (hwd : ∀ i, w i ≤ d) (r : ℕ) :
    (weightedFiltration w d hwd).layer r = Submodule.span ℚ
      (weightedOrderedBasis w d hw '' {j | r ≤ weightedOrderedGrade w d j}) := by
  change (weightedFiltration w d hwd).layer r = Submodule.span ℚ
    (((weightedBasis w d hw).reindex (weightedIndexOrder w d)) ''
      {j | r ≤ weightedBasisGrade w d ((weightedIndexOrder w d).symm j)})
  rw [basis_reindex_span_weights, ← weightedFiltration_layer_eq_span w d hw hwd r]

noncomputable def weightedLayerBasis (hwd : ∀ i, w i ≤ d) (r : ℕ) :
    Basis {j : Fin (Fintype.card (WeightedBasisIndex w d)) // r ≤ weightedOrderedGrade w d j}
      ℚ ((weightedFiltration w d hwd).layer r) :=
  supportedSubmoduleBasis (weightedOrderedBasis w d hw) ((weightedFiltration w d hwd).layer r)
    {j | r ≤ weightedOrderedGrade w d j} (weightedOrderedBasis_layers w d hw hwd r)

theorem weightedLayerBasis_height (hwd : ∀ i, w i ≤ d) (r : ℕ)
    (i : {j : Fin (Fintype.card (WeightedBasisIndex w d)) // r ≤ weightedOrderedGrade w d j}) (j) :
    RationalHeightLE ((weightedOrderedBasis w d hw).repr
      (weightedLayerBasis w d hw hwd r i).val j) 1 := by
  rw [weightedLayerBasis, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one (weightedOrderedBasis w d hw) _ _

noncomputable def weightedLayerIndexEquiv (hwd : ∀ i, w i ≤ d) (r : ℕ) :
    {j : Fin (Fintype.card (WeightedBasisIndex w d)) // r ≤ weightedOrderedGrade w d j} ≃
      Fin (finrank ℚ ((weightedFiltration w d hwd).layer r)) := by
  classical
  exact Fintype.equivFinOfCardEq (finrank_eq_card_basis (weightedLayerBasis w d hw hwd r)).symm

noncomputable def weightedLayerFinBasis (hwd : ∀ i, w i ≤ d) (r : ℕ) :
    Basis (Fin (finrank ℚ ((weightedFiltration w d hwd).layer r)))
      ℚ ((weightedFiltration w d hwd).layer r) :=
  (weightedLayerBasis w d hw hwd r).reindex (weightedLayerIndexEquiv w d hw hwd r)

theorem weightedLayerFinBasis_height (hwd : ∀ i, w i ≤ d) (r : ℕ) (i j) :
    RationalHeightLE ((weightedOrderedBasis w d hw).repr
      (weightedLayerFinBasis w d hw hwd r i).val j) 1 := by
  rw [weightedLayerFinBasis, Basis.reindex_apply]
  exact weightedLayerBasis_height w d hw hwd r _ _

include hw in
theorem weightedBasisIndex_card_le :
    Fintype.card (WeightedBasisIndex w d) ≤ Fintype.card σ + (Fintype.card σ + 1)^d := by
  rw [← finrank_eq_card_basis (weightedBasis w d hw)]
  exact weightedSubalgebra_finrank_le w d hw

@[simp] theorem weightedOrderedBasis_repr (x : weightedSubalgebra w d)
    (i : Fin (Fintype.card (WeightedBasisIndex w d))) :
    (weightedOrderedBasis w d hw).repr x i =
      (weightedBasis w d hw).repr x ((weightedIndexOrder w d).symm i) :=
  Basis.repr_reindex_apply _ _ _ _

theorem weightedOrderedBasis_structure_height (a b c) :
    RationalHeightLE (lieStructureConstants (weightedOrderedBasis w d hw) a b c) (2 * d + 1) := by
  rw [weightedOrderedBasis, lieStructureConstants_reindex]
  exact weightedBasis_structure_height w d hw _ _ _

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeNilsequenceExpansion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def conjugate (T : D.Niltest w) : D.Niltest w where
  orbit := T.orbit
  observable := fun x => star (T.observable x)
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le x := by simpa only [norm_star] using T.norm_le x
  lipschitz := by
    let := D.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← star_sub, norm_star] using T.lipschitz.dist_le_mul x y

@[simp] theorem eval_conjugate (T : D.Niltest w) (x : σ → ℤ) :
    T.conjugate.eval x = star (T.eval x) := rfl

@[simp] theorem conjugate_complexityLE (T : D.Niltest w) (p : ℝ) :
    T.conjugate.ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace NativeNilsequenceExpansion

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}

end NativeNilsequenceExpansion

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem polynomialSlowBound_symbol (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) :
    F.SymbolSlowBound b ω hlayers w T M (F.realPolynomialSymbolHom b ω hlayers w g) := by
  intro z
  change |((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
    (F.realSymbolOfPolynomial b ω hlayers w g.coord) z| ≤ _
  rw [F.realSymbolOfPolynomial_coordinate]
  exact hg z.val.1 z.val.2

theorem polynomialRationalGrid_symbol (m : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w m g) :
    F.SymbolRationalGrid b ω hlayers w m (F.realPolynomialSymbolHom b ω hlayers w g) := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => a z.val, ?_⟩
  funext z
  change (a z.val : ℝ) = (m : ℝ) *
    ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
      (F.realSymbolOfPolynomial b ω hlayers w g.coord) z
  rw [F.realSymbolOfPolynomial_coordinate]
  exact congrFun ha z.val

theorem realPolynomialSymbolHom_eq_of_quotient_eq
    (g h : (F.realification.adaptedPolynomialFiltration w).Group)
    (hgh : F.realification.polynomialSymbolHom w g = F.realification.polynomialSymbolHom w h) :
    F.realPolynomialSymbolHom b ω hlayers w g = F.realPolynomialSymbolHom b ω hlayers w h := by
  apply NilpotentLieBCHGroup.ext
  exact (F.realSymbolOfPolynomial_eq_iff_symbolMap_eq b ω hlayers w g.coord h.coord).mpr
    (congrArg NilpotentLieBCHGroup.coord hgh)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

noncomputable def substitute (T : D.Niltest w) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) : D.Niltest v :=
  { T with orbit := D.filtration.realification.polynomialOrbitSubstitute f hf T.orbit }

theorem eval_substitute (T : D.Niltest w) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) (x : τ → ℤ) (y : σ → ℤ)
    (hxy : ∀ i, MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (f i) = (y i : ℚ)) :
    (T.substitute f hf).eval x = T.eval y := by
  exact congrArg (fun z : D.RealGroup => T.observable (QuotientGroup.mk z))
    (D.filtration.realification.polynomialOrbitSubstitute_eval f hf T.orbit x y hxy)

@[simp] theorem substitute_complexityLE (T : D.Niltest w) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) (p : ℝ) :
    (T.substitute f hf).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

noncomputable def affinePullback [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (A : σ → τ → ℤ) (b : σ → ℤ) : D.Niltest (fun _ : τ => 1) :=
  T.substitute (integerAffinePolynomial A b) (integerAffinePolynomial_support A b)

theorem eval_affinePullback [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (A : σ → τ → ℤ) (b : σ → ℤ) (x : τ → ℤ) :
    (T.affinePullback A b).eval x = T.eval (integerAffineMap A b x) :=
  T.eval_substitute (integerAffinePolynomial A b) (integerAffinePolynomial_support A b)
    x (integerAffineMap A b x) (integerAffinePolynomial_eval A b x)

@[simp] theorem affinePullback_complexityLE [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (A : σ → τ → ℤ) (b : σ → ℤ) (p : ℝ) :
    (T.affinePullback A b).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

noncomputable def linearPullbackHom [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (f : σ → ((τ → ℤ) →+ ℤ)) : D.Niltest (fun _ : τ => 1) := by
  classical
  exact T.affinePullback (fun i j => f i (Pi.single j 1)) 0

theorem eval_linearPullbackHom [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (f : σ → ((τ → ℤ) →+ ℤ)) (x : τ → ℤ) :
    (T.linearPullbackHom f).eval x = T.eval (fun i => f i x) := by
  classical
  change (T.affinePullback (fun i j => f i (Pi.single j 1)) 0).eval x = _
  rw [eval_affinePullback]
  congr 1
  funext i
  simpa only [integerAffineMap, Pi.zero_apply, zero_add] using (integerLinearForm_eq_sum (f i) x).symm

@[simp] theorem linearPullbackHom_complexityLE [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (f : σ → ((τ → ℤ) →+ ℤ)) (p : ℝ) :
    (T.linearPullbackHom f).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def translate (T : D.Niltest w) (hw : ∀ i, 0 < w i) (h : σ → ℤ) : D.Niltest w :=
  { T with
    orbit := NilpotentLieFiltration.polynomialOrbitOfLog
      (VectorPolynomial.translate (fun i => (h i : ℚ)) T.orbit.log)
      (D.filtration.realification.adapted_translate w hw (fun i => (h i : ℚ)) T.orbit.adapted) }

@[simp] theorem eval_translate (T : D.Niltest w) (hw : ∀ i, 0 < w i) (h x : σ → ℤ) :
    (T.translate hw h).eval x = T.eval (x + h) := by
  apply congrArg T.observable
  apply congrArg QuotientGroup.mk
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.eval (fun i => (x i : ℚ))
      (VectorPolynomial.translate (fun i => (h i : ℚ)) T.orbit.log) =
    VectorPolynomial.eval (fun i => ((x + h) i : ℚ)) T.orbit.log
  rw [VectorPolynomial.eval_translate]
  simp only [Pi.add_apply, Int.cast_add]

@[simp] theorem translate_complexityLE (T : D.Niltest w) (hw : ∀ i, 0 < w i)
    (h : σ → ℤ) (p : ℝ) : (T.translate hw h).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {I L : Type*} [Fintype I] [DecidableEq I] [LieRing L] [LieAlgebra ℚ L] {s dim : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s dim}

theorem exists_nested_box_restriction (T : D.Niltest (fun _ : I => 1))
    (c b : I → ℤ) {m d : ℕ} (hm : 0 < m) (hd : 0 < d)
    (H K : I → ℕ) (hK : ∀ i, 0 < K i)
    (hsub : commonStrideBox b d K ⊆ commonStrideBox c m H) :
    ∃ U : D.Niltest (fun _ : I => 1),
      (∀ p, U.ComplexityLE p ↔ T.ComplexityLE p) ∧
      ∀ x ∈ integerBox K, U.eval x = T.eval (commonStrideIndex c m (commonStridePoint b d x)) := by
  obtain ⟨A, a, hA⟩ := exists_nested_box_affine c b hm hd H K hK hsub
  refine ⟨T.affinePullback A a, fun p => affinePullback_complexityLE T A a p, ?_⟩
  intro x hx
  rw [eval_affinePullback, (hA x hx).2, commonStrideIndex_point c hm]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {K K' L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

noncomputable def coordinateEquiv (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K') :
    D.Niltest (fun _ : K' => 1) :=
  T.substitute (fun i => MvPolynomial.X (e i))
    (fun i => weightedSupportLE_X (fun _ : K' => 1) (e i))

@[simp] theorem eval_coordinateEquiv (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K')
    (x : K' → ℤ) :
    (T.coordinateEquiv e).eval x = T.eval (fun i => x (e i)) := by
  exact T.eval_substitute (fun i => MvPolynomial.X (e i))
    (fun i => weightedSupportLE_X (fun _ : K' => 1) (e i))
    x (fun i => x (e i)) (fun _ => by simp)

@[simp] theorem eval_coordinateEquiv_symm (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K')
    (x : K → ℤ) :
    (T.coordinateEquiv e).eval (fun j => x (e.symm j)) = T.eval x := by
  simp only [eval_coordinateEquiv, Equiv.symm_apply_apply]

@[simp] theorem coordinateEquiv_observable (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K') :
    (T.coordinateEquiv e).observable = T.observable := rfl

@[simp] theorem coordinateEquiv_normBound (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K') :
    (T.coordinateEquiv e).normBound = T.normBound := rfl

@[simp] theorem coordinateEquiv_lipBound (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K') :
    (T.coordinateEquiv e).lipBound = T.lipBound := rfl

@[simp] theorem coordinateEquiv_complexityLE (T : D.Niltest (fun _ : K => 1))
    (e : K ≃ K') (p : ℝ) :
    (T.coordinateEquiv e).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

open scoped TensorProduct BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct BigOperators

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def symbol (T : D.Niltest w) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) :
    D.filtration.RealPolynomialSymbolGroup w :=
  D.filtration.realPolynomialSymbolHom b ω hF w ⟨⟨T.orbit.log, T.orbit.property⟩⟩

theorem symbol_translate (T : D.Niltest w) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hw : ∀ i, 0 < w i) (h : σ → ℤ) :
    (T.translate hw h).symbol b ω hF = T.symbol b ω hF := by
  apply D.filtration.realPolynomialSymbolHom_eq_of_quotient_eq b ω hF w
  apply NilpotentLieBCHGroup.ext
  exact D.filtration.realification.polynomialSymbolMap_translate w hw
    (fun i => (h i : ℚ)) ⟨T.orbit.log, T.orbit.property⟩

theorem mean_translate_box [Fintype σ] [DecidableEq σ]
    (T : D.Niltest w) (hw : ∀ i, 0 < w i) (a : σ → ℤ) (N : σ → ℕ) :
    (𝔼 x ∈ integerBox N, (T.translate hw a).eval x) =
      𝔼 x ∈ translatedIntegerBox a N, T.eval x := by
  rw [translatedIntegerBox, translateSupport,
    Finset.expect_image (add_right_injective a).injOn]
  apply Finset.expect_congr rfl
  intro x _
  rw [T.eval_translate, add_comm]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

noncomputable def scalarAffinePolynomial {σ : Type*} (r : ℚ) (shift : σ → ℚ) (i : σ) :
    MvPolynomial σ ℚ := MvPolynomial.C (shift i) + MvPolynomial.C r * MvPolynomial.X i

theorem scalarAffinePolynomial_support {σ : Type*} (r : ℚ) (shift : σ → ℚ) (i : σ) :
    scalarAffinePolynomial r shift i ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
  apply Submodule.add_mem
  · exact weightedSupportLE_C _ 1 (shift i)
  · simpa only [zero_add] using
      weightedSupportLE_mul (weightedSupportLE_C (fun _ : σ => 1) 0 r)
        (weightedSupportLE_X (fun _ : σ => 1) i)

namespace VectorPolynomial

theorem substitute_scalarAffinePolynomial {σ V : Type*} [AddCommGroup V] [Module ℚ V]
    (r : ℚ) (shift : σ → ℚ) (p : VectorPolynomial σ ℚ V) :
    substitute (scalarAffinePolynomial r shift) p =
      weightedDilation (fun _ => 1) r (translate shift p) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_zero
  intro x
  rw [map_sub, eval_substitute, eval_weightedDilation, eval_translate]
  simp [scalarAffinePolynomial, add_comm]

end VectorPolynomial

namespace RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

noncomputable def scalarAffinePullback (T : D.Niltest (fun _ : σ => 1))
    (r : ℚ) (shift : σ → ℚ) : D.Niltest (fun _ : σ => 1) :=
  T.substitute (scalarAffinePolynomial r shift) (scalarAffinePolynomial_support r shift)

@[simp] theorem scalarAffinePullback_complexityLE (T : D.Niltest (fun _ : σ => 1))
    (r : ℚ) (shift : σ → ℚ) (p : ℝ) :
    (T.scalarAffinePullback r shift).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

theorem scalarAffinePullback_eval_integer (T : D.Niltest (fun _ : σ => 1))
    (a : ℤ) (shift x : σ → ℤ) :
    (T.scalarAffinePullback a (fun i => (shift i : ℚ))).eval x =
      T.eval (fun i => a * x i + shift i) := by
  apply T.eval_substitute (scalarAffinePolynomial (a : ℚ) (fun i => (shift i : ℚ)))
    (scalarAffinePolynomial_support _ _) x (fun i => a * x i + shift i)
  intro i
  simp [scalarAffinePolynomial, add_comm]

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FormalPolynomialCorrectionStep
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace VectorPolynomial

theorem pderiv_map {σ V W : Type*} [LieRing V] [LieAlgebra ℚ V]
    [LieRing W] [LieAlgebra ℚ W] (i : σ) (f : V →ₗ[ℚ] W) (P : VectorPolynomial σ ℚ V) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor W (map f P) =
      map f ((MvPolynomial.pderiv i).toLinearMap.rTensor V P) := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  simp only [coefficients_pderiv, coefficients_map, map_smul]

theorem pderiv_mem_submodule {σ V : Type*} [LieRing V] [LieAlgebra ℚ V]
    (W : Submodule ℚ V) (P : VectorPolynomial σ ℚ V)
    (hP : ∀ α, coefficients P α ∈ W) (i : σ) (α : σ →₀ ℕ) :
    coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor V P) α ∈ W := by
  rw [coefficients_pderiv]
  exact W.smul_mem _ (hP _)

end VectorPolynomial

theorem basisGradeProjection_other {R L ι : Type*} [Field R] [AddCommGroup L] [Module R L]
    (b : Basis ι R L) (w : ι → ℕ) {i j : ℕ} (hij : i ≠ j) (x : L) :
    basisGradeProjection b w i (basisGradeProjection b w j x) = 0 := by
  apply b.repr.injective
  apply Finsupp.ext
  intro k
  simp only [basisGradeProjection_repr, map_zero, Finsupp.zero_apply]
  by_cases hi : w k = i
  · rw [if_pos hi, if_neg (fun hj => hij (hi.symm.trans hj))]
  · rw [if_neg hi]

namespace NilpotentLieFiltration

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem real_sub_horizontal_mem_of_lower_grades (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    {j : ℕ} (hj : 2 ≤ j) (x : ℝ ⊗[ℚ] L)
    (hlower : ∀ d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d x ∈ V) :
    x - basisGradeProjection (b.baseChange ℝ) w 1 x ∈ V ⊔ (F.realLayer j).toSubmodule := by
  classical
  have hzero : basisGradeProjection (b.baseChange ℝ) w 0 x = 0 :=
    F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers 0 x
      (by rw [show 0 + 1 = 1 from rfl, F.realification.one_eq_top]; trivial)
  have hlow : basisBelowProjection (b.baseChange ℝ) w j x -
      basisGradeProjection (b.baseChange ℝ) w 1 x ∈ V := by
    rw [basisBelowProjection_eq_sum_grades,
      ← Finset.sum_erase_add (Finset.range j) (fun d => basisGradeProjection (b.baseChange ℝ) w d x)
        (by simp only [Finset.mem_range]; omega : 1 ∈ Finset.range j), add_sub_cancel_right]
    apply V.sum_mem
    intro d hd
    obtain ⟨hd1, hdj⟩ := Finset.mem_erase.mp hd
    by_cases hd0 : d = 0
    · subst d
      rw [hzero]
      exact V.zero_mem
    · exact hlower d (by omega) (Finset.mem_range.mp hdj)
  have hhigh := F.sub_realGradeTruncation_mem b w hlayers j x
  have h := (V ⊔ (F.realLayer j).toSubmodule).add_mem
    (Submodule.mem_sup_right hhigh) (Submodule.mem_sup_left hlow)
  convert h using 1
  abel

include hlayers in
theorem real_polynomial_derivative_lower_layers (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    {j : ℕ} (hj : 2 ≤ j) (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d (coefficients P α) ∈ V)
    (i : σ) (t : σ → ℝ) :
    let D := eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P)
    D - basisGradeProjection (b.baseChange ℝ) w 1 D ∈ V ⊔ (F.realLayer j).toSubmodule ∧
      basisGradeProjection (b.baseChange ℝ) w 1 D ∈ K := by
  intro D
  let π := basisGradeProjection (b.baseChange ℝ) w 1
  let q := LinearMap.id - π
  let W := V ⊔ (F.realLayer j).toSubmodule
  have hq : ∀ α, coefficients (map (q.restrictScalars ℚ) P) α ∈ W := by
    intro α
    rw [coefficients_map]
    exact F.real_sub_horizontal_mem_of_lower_grades b w hlayers V hj _ (hlower α)
  have hπ : ∀ α, coefficients (map (π.restrictScalars ℚ) P) α ∈ K := by
    intro α
    rw [coefficients_map]
    exact hK α
  have hDq := (eval₂_mem_iff_coefficients W
    ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) (map (q.restrictScalars ℚ) P))).mpr
      (pderiv_mem_submodule (W.restrictScalars ℚ) _ hq i) t
  have hDπ := (eval₂_mem_iff_coefficients K
    ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) (map (π.restrictScalars ℚ) P))).mpr
      (pderiv_mem_submodule (K.restrictScalars ℚ) _ hπ i) t
  rw [pderiv_map, eval₂_map] at hDq hDπ
  exact ⟨hDq, hDπ⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem real_current_layer_polynomial_derivative_equation (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) {j : ℕ} (hj : 2 ≤ j)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hU : ∀ t : σ → ℝ, eval₂ t P ∈ U)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P α) ∈ V)
    (hbracket : ∀ (t : σ → ℝ) k, k ∈ K →
      ⁅eval₂ t P, k⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (extra : σ → (σ → ℝ) → ℝ ⊗[ℚ] L)
    (z : σ → (σ → ℝ) → DualGroup F.realification.lowerCentralSeries_eq_bot)
    (hbase : ∀ i t, dualBaseLinear (z i t).coord = eval₂ t P)
    (htangent : ∀ i t, dualTangentLinear (z i t).coord =
      eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P))
    (hextra : ∀ i t, extra i t - basisGradeProjection (b.baseChange ℝ) w 1
      (eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P)) ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hsystem : ∀ i t, dualLogDerivative (z i t) = eval₂ t (small i) +
      dualAdjoint (dualBaseHom (z i t)) (eval₂ t (rational i)) + extra i t) :
    ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
          (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P) -
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i) -
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α ∈ V := by
  have hW (d : ℕ) (x : ℝ ⊗[ℚ] L) :
      x ∈ V.restrictScalars ℚ ⊔ F.realification.layer d ↔
        x ∈ V ⊔ (F.realLayer d).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer d).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  intro i
  apply (eval₂_mem_iff_coefficients V _).mp
  intro t
  let D := eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P)
  let k := basisGradeProjection (b.baseChange ℝ) w 1 D
  have hlow := F.real_polynomial_derivative_lower_layers b w hlayers V K hj P hK hlower i t
  have hzU : dualBaseLinear (z i t).coord ∈ U := by rw [hbase]; exact hU t
  have hzlow : dualTangentLinear (z i t).coord - k ∈ V.restrictScalars ℚ ⊔ F.realification.layer j := by
    rw [htangent]
    exact (hW j _).mpr hlow.1
  have hzbracket : ⁅dualBaseLinear (z i t).coord, k⁆ ∈
      V.restrictScalars ℚ ⊔ F.realification.layer (j + 1) := by
    rw [hbase]
    exact (hW (j + 1) _).mpr (hbracket t k hlow.2)
  have hr : eval₂ t (rational i) ∈ V.restrictScalars ℚ ⊔ F.realification.layer j :=
    (hW j _).mpr ((eval₂_mem_iff_coefficients _ _).mpr (hrational i) t)
  have he := (hW (j + 1) _).mpr (hextra i t)
  have hcurrent := F.realification.current_layer_derivative_system hs U (V.restrictScalars ℚ)
    hUV j (z i t) hzU k (eval₂ t (small i)) (eval₂ t (rational i)) (extra i t)
    hzlow hzbracket hr he (hsystem i t)
  have hproj := F.realGradeProjection_mem_of_mem_sup_next b w hlayers V hV j _
    ((hW (j + 1) _).mp hcurrent)
  have hkzero : basisGradeProjection (b.baseChange ℝ) w j k = 0 :=
    basisGradeProjection_other (b.baseChange ℝ) w (by omega : j ≠ 1) D
  rw [htangent, map_sub, map_sub, map_add, hkzero, sub_zero] at hproj
  simp only [map_sub, pderiv_map, eval₂_map]
  convert hproj using 1
  change _ = (basisGradeProjection (b.baseChange ℝ) w j D -
    (basisGradeProjection (b.baseChange ℝ) w j (eval₂ t (small i)) +
      basisGradeProjection (b.baseChange ℝ) w j (eval₂ t (rational i))))
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem coefficientSubmodule_invariant (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (P Q : VectorPolynomial σ ℚ L)
    (hP : P ∈ coefficientLieSubalgebra U) (hQ : Q ∈ coefficientSubmodule V) :
    ⁅P, Q⁆ ∈ coefficientSubmodule V := by
  classical
  rw [← sum_monomial_coefficients P, ← sum_monomial_coefficients Q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients P).support (coefficients Q).support
    (fun α => monomial (R := ℚ) α (coefficients P α))
    (fun β => monomial (R := ℚ) β (coefficients Q β))]
  apply (coefficientSubmodule V).sum_mem
  intro α _
  apply (coefficientSubmodule V).sum_mem
  intro β _
  rw [lie_monomial]
  exact monomial_mem_coefficientSubmodule V _ (hUV _ (hP α) _ (hQ β))

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem formalLogDerivative_mem_coefficientSubmodule
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (i : σ) (P : PolynomialGroup σ hnil)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hPV : ∀ α, coefficients P.coord α ∈ V) :
    ∀ α, coefficients (formalLogDerivative i P) α ∈ V :=
  formalLogDerivative_mem_of_invariant (coefficientLieSubalgebra U) (coefficientSubmodule V)
    (fun A hA B hB => coefficientSubmodule_invariant U V hUV A B hA hB)
    i P hPU (pderiv_mem_submodule V P.coord hPV i)

theorem dualAdjoint_mem_coefficientSubmodule
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (P : PolynomialGroup σ hnil) (Q : VectorPolynomial σ ℚ L)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hQV : ∀ α, coefficients Q α ∈ V) :
    ∀ α, coefficients (dualAdjoint P Q) α ∈ V :=
  dualAdjoint_mem_of_invariant (coefficientLieSubalgebra U) (coefficientSubmodule V)
    (fun A hA B hB => coefficientSubmodule_invariant U V hUV A B hA hB) P hPU Q hQV

theorem polynomial_derivative_removal_preserves_coefficients
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (i : σ) (A B : PolynomialGroup σ hnil) (small rational : VectorPolynomial σ ℚ L)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hAV : ∀ α, coefficients A.coord α ∈ V) (hBV : ∀ α, coefficients B.coord α ∈ V)
    (hsmall : ∀ α, coefficients small α ∈ V)
    (hrational : ∀ α, coefficients rational α ∈ V) :
    (∀ α, coefficients (dualAdjoint A⁻¹ (small - formalLogDerivative i A)) α ∈ V) ∧
      ∀ α, coefficients (dualAdjoint B rational - formalLogDerivative i B) α ∈ V := by
  have hYA := formalLogDerivative_mem_coefficientSubmodule U V hUV i A hAU hAV
  have hYB := formalLogDerivative_mem_coefficientSubmodule U V hUV i B hBU hBV
  have hAinv : ∀ α, coefficients A⁻¹.coord α ∈ U := by
    intro α
    change coefficients (-A.coord) α ∈ U
    rw [map_neg, Finsupp.neg_apply]
    exact U.neg_mem (hAU α)
  constructor
  · exact dualAdjoint_mem_coefficientSubmodule U V hUV A⁻¹ _ hAinv
      ((coefficientSubmodule V).sub_mem hsmall hYA)
  · exact (coefficientSubmodule V).sub_mem
      (dualAdjoint_mem_coefficientSubmodule U V hUV B rational hBU hrational) hYB

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]

noncomputable def gradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ) (v : σ → ℕ) :
    Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {P | ∀ α,
    (basisGradeProjection b w (Finsupp.weight v α)).restrictScalars ℚ (coefficients P α) = coefficients P α}
  zero_mem' := by intro α; simp only [map_zero, Finsupp.zero_apply]
  add_mem' := by
    intro P Q hP hQ α
    simp only [map_add, Finsupp.add_apply, hP α, hQ α]
  smul_mem' := by
    intro a P hP α
    simp only [map_smul, Finsupp.smul_apply, hP α]

theorem monomial_mem_gradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ) (v : σ → ℕ)
    (α : σ →₀ ℕ) (x : L) (hx : basisGradeProjection b w (Finsupp.weight v α) x = x) :
    monomial (R := ℚ) α x ∈ gradedPolynomialSubmodule b w v := by
  intro β
  rw [coefficients_monomial]
  by_cases h : α = β
  · subst β
    simpa only [Finsupp.single_eq_same, LinearMap.restrictScalars_apply] using hx
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), map_zero]

noncomputable def gradedPolynomialSubalgebra (b : Basis ι ℝ L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) (v : σ → ℕ) : LieSubalgebra ℚ (VectorPolynomial σ ℚ L) :=
  { gradedPolynomialSubmodule b w v with
    lie_mem' := by
      intro P Q hP hQ
      classical
      rw [← sum_monomial_coefficients P, ← sum_monomial_coefficients Q]
      simp only [Finsupp.sum]
      rw [sum_lie_sum (coefficients P).support (coefficients Q).support
        (fun α => monomial (R := ℚ) α (coefficients P α))
        (fun β => monomial (R := ℚ) β (coefficients Q β))]
      apply (gradedPolynomialSubmodule b w v).sum_mem
      intro α _
      apply (gradedPolynomialSubmodule b w v).sum_mem
      intro β _
      rw [lie_monomial]
      apply monomial_mem_gradedPolynomialSubmodule
      rw [map_add]
      exact hb.projection_lie b w (hP α) (hQ β) }

theorem homogeneous_mem_gradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ) (v : σ → ℕ)
    (j : ℕ) (P : VectorPolynomial σ ℚ L)
    (hhom : ∀ α, Finsupp.weight v α ≠ j → coefficients P α = 0)
    (hgrade : ∀ α, basisGradeProjection b w j (coefficients P α) = coefficients P α) :
    P ∈ gradedPolynomialSubmodule b w v := by
  intro α
  by_cases hα : Finsupp.weight v α = j
  · simpa only [hα, LinearMap.restrictScalars_apply] using hgrade α
  · rw [hhom α hα, map_zero]

theorem gradedPolynomialSubmodule_projection_homogeneous (b : Basis ι ℝ L) (w : ι → ℕ)
    (v : σ → ℕ) (P : VectorPolynomial σ ℚ L) (hP : P ∈ gradedPolynomialSubmodule b w v)
    (j : ℕ) (α : σ →₀ ℕ) (hα : Finsupp.weight v α ≠ j) :
    coefficients (map ((basisGradeProjection b w j).restrictScalars ℚ) P) α = 0 := by
  rw [coefficients_map]
  change basisGradeProjection b w j (coefficients P α) = 0
  have he : basisGradeProjection b w (Finsupp.weight v α) (coefficients P α) = coefficients P α := hP α
  rw [← he]
  exact basisGradeProjection_other b w (Ne.symm hα) _

theorem bchRemove_mem_gradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) (v : σ → ℕ) (s : ℕ)
    (A P B : VectorPolynomial σ ℚ L)
    (hA : A ∈ gradedPolynomialSubmodule b w v) (hP : P ∈ gradedPolynomialSubmodule b w v)
    (hB : B ∈ gradedPolynomialSubmodule b w v) :
    bchRemove s A P B ∈ gradedPolynomialSubmodule b w v := by
  let U := gradedPolynomialSubalgebra b w hb v
  exact lieBCH_mem U s (lieBCH_mem U s (U.neg_mem hA) hP) (U.neg_mem hB)

namespace NilpotentLieFiltration

theorem realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule
    {M κ : Type*} [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration M s) (b : Basis κ ℚ M) (w : κ → ℕ)
    (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (v : σ → ℕ) (x : F.RealPolynomialSymbol v) :
    F.realGradedSymbolPolynomial b w hF v x ∈
      gradedPolynomialSubmodule ((F.associatedGradedBasis b w hF).baseChange ℝ) w v := by
  intro α
  change basisGradeProjection ((F.associatedGradedBasis b w hF).baseChange ℝ) w
    (Finsupp.weight v α) (coefficients (F.realGradedSymbolPolynomial b w hF v x) α) = _
  apply ((F.associatedGradedBasis b w hF).baseChange ℝ).repr.injective
  apply Finsupp.ext
  intro i
  rw [basisGradeProjection_repr]
  by_cases hi : w i = Finsupp.weight v α
  · rw [if_pos hi]
  · rw [if_neg hi]
    exact (F.realGradedSymbolPolynomial_coordinate_of_ne b w hF v x α i (Ne.symm hi)).symm

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem coefficientSubmodule_sup (V W : Submodule ℚ L) :
    coefficientSubmodule (σ := σ) (V ⊔ W) = coefficientSubmodule V ⊔ coefficientSubmodule W := by
  classical
  apply le_antisymm
  · intro P hP
    rw [← sum_monomial_coefficients P]
    change ∑ α ∈ (coefficients P).support, monomial α (coefficients P α) ∈ _
    apply Submodule.sum_mem
    intro α _
    obtain ⟨v, hv, w, hw, he⟩ := Submodule.mem_sup.mp (hP α)
    rw [← he]
    have hmono : monomial (R := ℚ) α (v + w) = monomial α v + monomial α w :=
      TensorProduct.tmul_add _ _ _
    rw [hmono]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (monomial_mem_coefficientSubmodule V α hv))
      (Submodule.mem_sup_right (monomial_mem_coefficientSubmodule W α hw))
  · apply sup_le
    · intro P hP α
      exact Submodule.mem_sup_left (hP α)
    · intro P hP α
      exact Submodule.mem_sup_right (hP α)

theorem coefficients_lie_constant (P : VectorPolynomial σ ℚ L) (x : L) (α : σ →₀ ℕ) :
    coefficients ⁅P, monomial (R := ℚ) 0 x⁆ α = ⁅coefficients P α, x⁆ := by
  induction P using TensorProduct.induction_on with
  | zero =>
    rw [zero_lie (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L)]
    simp
  | tmul q y =>
    simp only [monomial, LieAlgebra.ExtendScalars.bracket_tmul,
      MvPolynomial.monomial_zero', MvPolynomial.C_1, mul_one,
      coefficients_tmul, coefficients_tmul, smul_lie]
  | add P Q hP hQ =>
    rw [LieRing.add_lie P Q, map_add, Finsupp.add_apply, hP, hQ,
      map_add, Finsupp.add_apply, LieRing.add_lie]

theorem polynomialLayer_eq_coefficientSubmodule {s : ℕ} (F : NilpotentLieFiltration L s) (j : ℕ) :
    (F.polynomialFiltration (σ := σ)).layer j = coefficientSubmodule (F.layer j) := by
  ext P
  rfl

theorem mem_coefficient_sup_polynomialLayer {s : ℕ} (F : NilpotentLieFiltration L s)
    (V : Submodule ℚ L) (j : ℕ) (P : VectorPolynomial σ ℚ L) :
    P ∈ coefficientSubmodule V ⊔ F.polynomialFiltration.layer j ↔
      ∀ α, coefficients P α ∈ V ⊔ F.layer j := by
  rw [polynomialLayer_eq_coefficientSubmodule, ← coefficientSubmodule_sup]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

section RealBasis

variable {L ι σ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} (F : NilpotentLieFiltration L s)
  (b : Basis ι ℝ L) (ω : ι → ℕ) (v : σ → ℕ)

theorem polynomialOrbit_log_mul_mem_graded (hb : BasisHomogeneousBrackets b ω)
    (p q : F.PolynomialOrbit v)
    (hp : p.log ∈ gradedPolynomialSubmodule b ω v)
    (hq : q.log ∈ gradedPolynomialSubmodule b ω v) :
    (p * q).log ∈ gradedPolynomialSubmodule b ω v :=
  lieBCH_mem (gradedPolynomialSubalgebra b ω hb v) s hp hq

end RealBasis

section RationalBasis

variable {L ι σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ) (v : σ → ℕ)

theorem realPolynomialOrbit_log_mul_mem_graded (hb : BasisHomogeneousBrackets b ω)
    (p q : F.realification.PolynomialOrbit v)
    (hp : p.log ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v)
    (hq : q.log ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v) :
    (p * q).log ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v :=
  F.realification.polynomialOrbit_log_mul_mem_graded (b.baseChange ℝ) ω v
    (hb.baseChange b ω) p q hp hq

end RationalBasis

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]

noncomputable def shiftedGradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (v : σ → ℕ) (r : ℕ) : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {P | ∀ α,
    (basisGradeProjection b w (Finsupp.weight v α + r)).restrictScalars ℚ
      (coefficients P α) = coefficients P α}
  zero_mem' := by intro α; simp only [map_zero, Finsupp.zero_apply]
  add_mem' := by
    intro P Q hP hQ α
    simp only [map_add, Finsupp.add_apply, hP α, hQ α]
  smul_mem' := by
    intro a P hP α
    simp only [map_smul, Finsupp.smul_apply, hP α]

theorem monomial_mem_shiftedGradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (v : σ → ℕ) (r : ℕ) (α : σ →₀ ℕ) (x : L)
    (hx : basisGradeProjection b w (Finsupp.weight v α + r) x = x) :
    monomial (R := ℚ) α x ∈ shiftedGradedPolynomialSubmodule b w v r := by
  intro β
  rw [coefficients_monomial]
  by_cases h : α = β
  · subst β
    simpa only [Finsupp.single_eq_same, LinearMap.restrictScalars_apply] using hx
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), map_zero]

theorem shiftedGradedPolynomialSubmodule_invariant (b : Basis ι ℝ L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) (v : σ → ℕ) (r : ℕ)
    (P Q : VectorPolynomial σ ℚ L)
    (hP : P ∈ gradedPolynomialSubmodule b w v)
    (hQ : Q ∈ shiftedGradedPolynomialSubmodule b w v r) :
    ⁅P, Q⁆ ∈ shiftedGradedPolynomialSubmodule b w v r := by
  classical
  rw [← sum_monomial_coefficients P, ← sum_monomial_coefficients Q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients P).support (coefficients Q).support
    (fun α => monomial (R := ℚ) α (coefficients P α))
    (fun β => monomial (R := ℚ) β (coefficients Q β))]
  apply (shiftedGradedPolynomialSubmodule b w v r).sum_mem
  intro α _
  apply (shiftedGradedPolynomialSubmodule b w v r).sum_mem
  intro β _
  rw [lie_monomial]
  apply monomial_mem_shiftedGradedPolynomialSubmodule
  rw [map_add, Nat.add_assoc]
  exact hb.projection_lie b w (hP α) (hQ β)

theorem pderiv_mem_shiftedGradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (P : VectorPolynomial σ ℚ L)
    (hP : P ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1)) (i : σ) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor L P ∈
      shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1 := by
  intro α
  rw [coefficients_pderiv, map_smul]
  have h := congrArg (fun x => (α i + 1 : ℚ) • x) (hP (α + Finsupp.single i 1))
  simpa only [map_add, Finsupp.weight_single, one_smul] using h

theorem shiftedGradedPolynomialSubmodule_projection_homogeneous (b : Basis ι ℝ L) (w : ι → ℕ)
    (v : σ → ℕ) (r : ℕ) (P : VectorPolynomial σ ℚ L)
    (hP : P ∈ shiftedGradedPolynomialSubmodule b w v r)
    (j : ℕ) (α : σ →₀ ℕ) (hα : Finsupp.weight v α + r ≠ j) :
    coefficients (VectorPolynomial.map ((basisGradeProjection b w j).restrictScalars ℚ) P) α = 0 := by
  rw [coefficients_map]
  change basisGradeProjection b w j (coefficients P α) = 0
  have he : basisGradeProjection b w (Finsupp.weight v α + r) (coefficients P α) =
      coefficients P α := hP α
  rw [← he]
  exact basisGradeProjection_other b w (Ne.symm hα) _

theorem shifted_one_projection_homogeneous (b : Basis ι ℝ L) (w : ι → ℕ)
    (P : VectorPolynomial σ ℚ L)
    (hP : P ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1)
    {j : ℕ} (hj : 0 < j) (α : σ →₀ ℕ)
    (hα : Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1) :
    coefficients (VectorPolynomial.map ((basisGradeProjection b w j).restrictScalars ℚ) P) α = 0 := by
  apply shiftedGradedPolynomialSubmodule_projection_homogeneous b w (fun _ => 1) 1 P hP j α
  omega

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_mem_shiftedGradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) (v : σ → ℕ) (r : ℕ)
    (P : PolynomialGroup σ hnil) (Q : VectorPolynomial σ ℚ L)
    (hP : P.coord ∈ gradedPolynomialSubmodule b w v)
    (hQ : Q ∈ shiftedGradedPolynomialSubmodule b w v r) :
    dualAdjoint P Q ∈ shiftedGradedPolynomialSubmodule b w v r :=
  dualAdjoint_mem_of_invariant (gradedPolynomialSubalgebra b w hb v)
    (shiftedGradedPolynomialSubmodule b w v r)
    (fun A hA B hB => shiftedGradedPolynomialSubmodule_invariant b w hb v r A B hA hB)
    P hP Q hQ

theorem formalLogDerivative_mem_shiftedGradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) (i : σ) (P : PolynomialGroup σ hnil)
    (hP : P.coord ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1)) :
    formalLogDerivative i P ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1 :=
  formalLogDerivative_mem_of_invariant (gradedPolynomialSubalgebra b w hb (fun _ : σ => 1))
    (shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1)
    (fun A hA B hB => shiftedGradedPolynomialSubmodule_invariant b w hb _ 1 A B hA hB)
    i P hP (pderiv_mem_shiftedGradedPolynomialSubmodule b w P.coord hP i)

theorem polynomial_derivative_removal_preserves_shifted_grading
    (b : Basis ι ℝ L) (w : ι → ℕ) (hb : BasisHomogeneousBrackets b w)
    (i : σ) (A B : PolynomialGroup σ hnil) (small rational : VectorPolynomial σ ℚ L)
    (hA : A.coord ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1))
    (hB : B.coord ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1))
    (hsmall : small ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1)
    (hrational : rational ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1) :
    dualAdjoint A⁻¹ (small - formalLogDerivative i A) ∈
        shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1 ∧
      dualAdjoint B rational - formalLogDerivative i B ∈
        shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1 := by
  let W := shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1
  have hYA := formalLogDerivative_mem_shiftedGradedPolynomialSubmodule b w hb i A hA
  have hYB := formalLogDerivative_mem_shiftedGradedPolynomialSubmodule b w hb i B hB
  constructor
  · exact dualAdjoint_mem_shiftedGradedPolynomialSubmodule b w hb _ 1 A⁻¹ _
      ((gradedPolynomialSubmodule b w _).neg_mem hA) (W.sub_mem hsmall hYA)
  · exact W.sub_mem
      (dualAdjoint_mem_shiftedGradedPolynomialSubmodule b w hb _ 1 B rational hB hrational) hYB

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CurrentPolynomialDerivativeRemoval
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def PolynomialLiftSystem (P : PolynomialGroup σ hnil)
    (S R : κ → VectorPolynomial σ ℚ L) : Prop :=
  ∀ k, S k = dualAdjoint P (R k)

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def PolynomialLiftSystemMod (V : Submodule ℚ L) (P : PolynomialGroup σ hnil)
    (S R : κ → VectorPolynomial σ ℚ L) : Prop :=
  ∀ k, S k - dualAdjoint P (R k) ∈ coefficientSubmodule V

def PolynomialDerivativeSystemMod (V : Submodule ℚ L) (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L) : Prop :=
  ∀ i, formalLogDerivative i P - (small i + dualAdjoint P (rational i) + extra i) ∈ coefficientSubmodule V

theorem PolynomialLiftSystemMod.exact_left (V : Submodule ℚ L) (P : PolynomialGroup σ hnil)
    (S R : κ → VectorPolynomial σ ℚ L) (h : PolynomialLiftSystemMod V P S R) :
    ∃ S₀ : κ → VectorPolynomial σ ℚ L,
      PolynomialLiftSystem P S₀ R ∧ ∀ k, S k - S₀ k ∈ coefficientSubmodule V :=
  ⟨fun k => dualAdjoint P (R k), fun _ => rfl, h⟩

theorem PolynomialDerivativeSystemMod.exact_system (V : Submodule ℚ L) (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L)
    (h : PolynomialDerivativeSystemMod V P small rational extra) :
    ∃ error : σ → VectorPolynomial σ ℚ L,
      (∀ i, error i ∈ coefficientSubmodule V) ∧
      PolynomialDerivativeSystem P small rational (fun i => extra i + error i) := by
  refine ⟨fun i => formalLogDerivative i P - (small i + dualAdjoint P (rational i) + extra i), h, ?_⟩
  intro i
  change formalLogDerivative i P = small i + dualAdjoint P (rational i) +
    (extra i + (formalLogDerivative i P - (small i + dualAdjoint P (rational i) + extra i)))
  abel

theorem PolynomialLiftSystemMod.remove (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (P A B : PolynomialGroup σ hnil) (hA : ∀ α, coefficients A.coord α ∈ U)
    (S R : κ → VectorPolynomial σ ℚ L) (h : PolynomialLiftSystemMod V P S R) :
    PolynomialLiftSystemMod V (A⁻¹ * P * B⁻¹)
      (fun k => dualAdjoint A⁻¹ (S k)) (fun k => dualAdjoint B (R k)) := by
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ U := (coefficientLieSubalgebra U).neg_mem hA
  intro k
  change dualAdjoint A⁻¹ (S k) - dualAdjoint (A⁻¹ * P * B⁻¹) (dualAdjoint B (R k)) ∈ _
  rw [dualAdjoint_mul, dualAdjoint_mul, dualAdjoint_inv_cancel, ← dualAdjoint_sub]
  exact dualAdjoint_mem_coefficientSubmodule U V hUV A⁻¹ _ hAi (h k)

theorem PolynomialDerivativeSystemMod.remove (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (P A B : PolynomialGroup σ hnil) (hA : ∀ α, coefficients A.coord α ∈ U)
    (small rational extra : σ → VectorPolynomial σ ℚ L)
    (h : PolynomialDerivativeSystemMod V P small rational extra) :
    PolynomialDerivativeSystemMod V (A⁻¹ * P * B⁻¹)
      (fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A))
      (fun i => dualAdjoint B (rational i) - formalLogDerivative i B)
      (fun i => dualAdjoint A⁻¹ (extra i)) := by
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ U := (coefficientLieSubalgebra U).neg_mem hA
  intro i
  have herr := dualAdjoint_mem_coefficientSubmodule U V hUV A⁻¹
    (formalLogDerivative i P - (small i + dualAdjoint P (rational i) + extra i)) hAi (h i)
  have hmem : dualAdjoint A⁻¹
      (formalLogDerivative i P - (small i + dualAdjoint P (rational i) + extra i)) ∈
      coefficientSubmodule V := herr
  change formalLogDerivative i (A⁻¹ * P * B⁻¹) -
    (dualAdjoint A⁻¹ (small i - formalLogDerivative i A) +
      dualAdjoint (A⁻¹ * P * B⁻¹) (dualAdjoint B (rational i) - formalLogDerivative i B) +
      dualAdjoint A⁻¹ (extra i)) ∈ coefficientSubmodule V
  convert hmem using 1
  rw [formalLogDerivative_remove]
  simp only [dualAdjoint_mul, dualAdjoint_add, dualAdjoint_sub, dualAdjoint_inv_cancel]
  abel

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem polynomial_grade_eq_of_sub_mem_next (j : ℕ)
    (X Y : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hXY : ∀ α, coefficients (X - Y) α ∈ F.realification.layer (j + 1)) :
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) X =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) Y := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [coefficients_map, coefficients_map]
  have h := F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers j _ (hXY α)
  simp only [map_sub, Finsupp.sub_apply] at h
  exact sub_eq_zero.mp h

include hlayers in
theorem polynomial_grade_adjoint_eq (hs : 2 ≤ s) (j : ℕ)
    (A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (X : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (dualAdjoint A X) =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) X := by
  apply F.polynomial_grade_eq_of_sub_mem_next b w hlayers j
  exact F.realification.polynomialFiltration.adjoint_correction_sub_mem_layer hs j A hA X

include hlayers in
theorem polynomial_grade_logDerivative_eq (hs : 1 ≤ s) {j : ℕ} (hj : 0 < j)
    (i : σ) (A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients A.coord α) = coefficients A.coord α) :
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (formalLogDerivative i A) =
      (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) A.coord := by
  have hAlayer : ∀ α, coefficients A.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hA α]
    exact F.realGradeProjection_mem_layer b w hlayers j _
  have hDlayer := pderiv_mem_submodule (F.realification.layer j) A.coord hAlayer i
  have hrem := F.realification.polynomialFiltration.dualLogDerivative_sub_tangent_mem_layer hs
    (i := j) (j := j) (formalPolynomialJetHom i A)
    (by rw [formalPolynomialJet_base]; exact hAlayer)
    (by rw [formalPolynomialJet_tangent]; exact hDlayer)
  rw [formalPolynomialJet_tangent] at hrem
  have hnext : ∀ α, coefficients (formalLogDerivative i A -
      (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) A.coord) α ∈ F.realification.layer (j + 1) := by
    intro α
    exact F.realification.antitone (by omega : j + 1 ≤ j + j) (hrem α)
  have hgrade := F.polynomial_grade_eq_of_sub_mem_next b w hlayers j _ _ hnext
  have hfix : VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) A.coord = A.coord := by
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map]
    exact hA α
  rw [← pderiv_map, hfix] at hgrade
  exact hgrade

include hlayers in
theorem current_derivative_removal_projection (hs : 2 ≤ s) {j : ℕ} (hj : 0 < j)
    (i : σ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients B.coord α) = coefficients B.coord α)
    (small rational : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (dualAdjoint A⁻¹ (small - formalLogDerivative i A)) =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) small -
        (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) A.coord ∧
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (dualAdjoint B rational - formalLogDerivative i B) =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) rational -
        (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) B.coord := by
  have hAlayer : ∀ α, coefficients A.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hA α]
    exact F.realGradeProjection_mem_layer b w hlayers j _
  have hBlayer : ∀ α, coefficients B.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hB α]
    exact F.realGradeProjection_mem_layer b w hlayers j _
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ F.realification.layer j :=
    (coefficientSubmodule (F.realification.layer j)).neg_mem hAlayer
  constructor
  · rw [F.polynomial_grade_adjoint_eq b w hlayers hs j A⁻¹ hAi, map_sub,
      F.polynomial_grade_logDerivative_eq b w hlayers (by omega) hj i A hA]
  · rw [map_sub, F.polynomial_grade_adjoint_eq b w hlayers hs j B hBlayer,
      F.polynomial_grade_logDerivative_eq b w hlayers (by omega) hj i B hB]

include hlayers in
theorem current_derivative_defect_preserved (hs : 2 ≤ s) {j : ℕ} (hj : 0 < j)
    (i : σ) (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients B.coord α) = coefficients B.coord α)
    (small rational : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    let π := VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
    let D := (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
    D (π (A⁻¹ * P * B⁻¹).coord) - π (dualAdjoint A⁻¹ (small - formalLogDerivative i A)) -
        π (dualAdjoint B rational - formalLogDerivative i B) =
      D (π P.coord) - π small - π rational := by
  dsimp only
  let E := LinearMap.ker (basisGradeProjection (b.baseChange ℝ) w j - LinearMap.id)
  have hE : ∀ x ∈ E, basisGradeProjection (b.baseChange ℝ) w j x = x := by
    intro x hx
    exact sub_eq_zero.mp hx
  have hgrades := F.polynomial_bchRemove_grades b w hlayers E j hE A.coord P.coord B.coord
    (fun α => sub_eq_zero.mpr (hA α)) (fun α => sub_eq_zero.mpr (hB α))
  have hP : VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
      (A⁻¹ * P * B⁻¹).coord =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P.coord - A.coord - B.coord :=
    hgrades.1
  have hparts := F.current_derivative_removal_projection b w hlayers hs hj i A B hA hB small rational
  rw [hP, hparts.1, hparts.2, map_sub, map_sub]
  abel

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SubspacePolynomialCoordinates
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {L ν σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ν] {E : Submodule ℚ L}

theorem bracketSystemLift_injective (e : Basis ν ℚ E) : Function.Injective (bracketSystemLift e) := by
  intro x y h
  apply (e.baseChange ℝ).equivFun.symm.injective
  exact realification_subtype_injective E h

theorem exists_subspace_coordinate_polynomial (e : Basis ν ℚ E)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hP : ∀ α, coefficients P α ∈ E.baseChange ℝ) :
    ∃ Q : VectorPolynomial σ ℚ (ν → ℝ),
      map ((bracketSystemLift e).restrictScalars ℚ) Q = P ∧
        ∀ α, coefficients P α = 0 → coefficients Q α = 0 := by
  classical
  choose v hv using fun α : σ →₀ ℕ => exists_subspace_basis_coordinates e (coefficients P α) (hP α)
  have hzero (α : σ →₀ ℕ) (hα : coefficients P α = 0) : v α = 0 := by
    apply bracketSystemLift_injective e
    rw [hv, hα, map_zero]
  let C : (σ →₀ ℕ) →₀ (ν → ℝ) := {
    support := (coefficients P).support
    toFun := v
    mem_support_toFun := by
      intro α
      rw [Finsupp.mem_support_iff]
      constructor
      · intro h hα
        apply h
        rw [← hv α, hα, map_zero]
      · intro h hα
        exact h (hzero α hα) }
  let Q : VectorPolynomial σ ℚ (ν → ℝ) := coefficients.symm C
  have hcoeff (α : σ →₀ ℕ) : coefficients Q α = v α := by
    change coefficients (coefficients.symm C) α = v α
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hmap : map ((bracketSystemLift e).restrictScalars ℚ) Q = P := by
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map]
    change bracketSystemLift e (coefficients Q α) = _
    rw [hcoeff]
    exact hv α
  refine ⟨Q, hmap, ?_⟩
  intro α hα
  rw [hcoeff]
  exact hzero α hα

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NativeGridRightDictionary
namespace OAI

section

namespace Erdos3

theorem finite_card_real_grid_box {ι : Type*} [Fintype ι]
    (S : Set (ι → ℝ)) (l N : ℕ) (hl : 0 < l) {B : ℝ}
    (hgrid : S ⊆ realDenominatorGrid l)
    (hbound : ∀ x ∈ S, ∀ i, |x i| ≤ B)
    (hN : (l : ℝ) * B ≤ N) :
    S.Finite ∧ S.ncard ≤ (2 * N + 1) ^ Fintype.card ι := by
  classical
  let z : S → ι → ℤ := fun x => Classical.choose (hgrid x.property)
  have hz (x : S) (i : ι) : (z x i : ℝ) = (l : ℝ) * x.val i :=
    congrFun (Classical.choose_spec (hgrid x.property)) i
  have hzi (x : S) (i : ι) : z x i ∈ Set.Icc (-(N : ℤ)) N := by
    have hb : |(z x i : ℝ)| ≤ (N : ℝ) := by
      rw [hz, abs_mul, abs_of_nonneg (Nat.cast_nonneg l)]
      exact (mul_le_mul_of_nonneg_left (hbound x x.property i) (Nat.cast_nonneg l)).trans hN
    apply abs_le.mp
    exact_mod_cast hb
  let f : S → (ι → Set.Icc (-(N : ℤ)) N) := fun x i => ⟨z x i, hzi x i⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hi : z x i = z y i := congrArg Subtype.val (congrFun hxy i)
    apply mul_left_cancel₀ (show (l : ℝ) ≠ 0 by exact_mod_cast hl.ne')
    rw [← hz, ← hz, hi]
  let : Finite S := Finite.of_injective f hf
  have hcardI : Fintype.card (Set.Icc (-(N : ℤ)) N) = 2 * N + 1 := by
    have h := Int.card_fintype_Icc_of_le (-(N : ℤ)) N (show -(N : ℤ) ≤ N + 1 by omega)
    omega
  refine ⟨Set.toFinite S, ?_⟩
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_fun, hcardI] using hc

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_bounded_native_grid_enumeration
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (m : ℕ) (hm : 0 < m)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (2 * ⌈(m : ℝ) * B⌉₊ + 1) ^ d ∧
      ∃ rep : Fin n → D.RealGroup,
        (∀ j, (∀ i, |(D.basis.baseChange ℝ).repr (rep j).coord i| ≤ B) ∧
          (D.basis.baseChange ℝ).equivFun (rep j).coord ∈ realDenominatorGrid m) ∧
        ∀ g : D.RealGroup,
          (∀ i, |(D.basis.baseChange ℝ).repr g.coord i| ≤ B) →
          (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid m →
          ∃ j, g = rep j := by
  classical
  let A : Set (Fin d → ℝ) :=
    {x | (∀ i, |x i| ≤ B) ∧ x ∈ realDenominatorGrid m}
  obtain ⟨hAfin, hAcard⟩ := finite_card_real_grid_box A m ⌈(m : ℝ) * B⌉₊ hm
    (fun _ hx => hx.2) (fun _ hx => hx.1) (Nat.le_ceil _)
  let S : Set D.RealGroup :=
    {g | (∀ i, |(D.basis.baseChange ℝ).repr g.coord i| ≤ B) ∧
      (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid m}
  let f : D.RealGroup → (Fin d → ℝ) :=
    fun g => (D.basis.baseChange ℝ).equivFun g.coord
  have hf : Function.Injective f := by
    intro g h hgh
    apply NilpotentLieBCHGroup.ext
    exact (D.basis.baseChange ℝ).equivFun.injective hgh
  have hmaps : Set.MapsTo f S A := by
    intro g hg
    exact ⟨by simpa only [f, Basis.equivFun_apply] using hg.1, hg.2⟩
  have hSfin : S.Finite := Set.Finite.of_injOn hmaps hf.injOn hAfin
  have hScard : S.ncard ≤ (2 * ⌈(m : ℝ) * B⌉₊ + 1) ^ d := by
    exact (Set.ncard_le_ncard_of_injOn f hmaps hf.injOn hAfin).trans
      (by simpa only [Fintype.card_fin] using hAcard)
  let : Fintype S := hSfin.fintype
  have hone : (1 : D.RealGroup) ∈ S := by
    constructor
    · simpa only [coord_one, map_zero, Finsupp.zero_apply, abs_zero] using
        fun _ : Fin d => hB
    · change (D.basis.baseChange ℝ).equivFun (0 : ℝ ⊗[ℚ] L) ∈ _
      rw [map_zero]
      exact ⟨0, by ext i; simp⟩
  let : Nonempty S := ⟨⟨1, hone⟩⟩
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, Fintype.card_pos, ?_, fun j => (e.symm j).val,
    fun j => (e.symm j).property, ?_⟩
  · simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hScard
  · intro g hbound hgrid
    let x : S := ⟨g, hbound, hgrid⟩
    exact ⟨e x, (congrArg Subtype.val (e.symm_apply_apply x)).symm⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

structure NativeGridRightDictionary
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (inputDenominator : ℕ) (B : ℝ) where
  denominator : ℕ
  count : ℕ
  denominator_pos : 0 < denominator
  count_pos : 0 < count
  denominator_bound : (denominator : ℝ) ≤ B
  count_bound : (count : ℝ) ≤ B
  representative : Fin count → D.RealGroup
  representative_bounds : ∀ j,
    (∀ i, |(D.basis.baseChange ℝ).repr (representative j).coord i| ≤ B) ∧
    (D.basis.baseChange ℝ).equivFun (representative j).coord ∈
      realDenominatorGrid denominator
  cover : ∀ g : D.RealGroup,
    (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid inputDenominator →
    ∃ j : Fin count, ∃ γ ∈ D.realLattice, g = representative j * γ

namespace NativeGridRightDictionary

theorem labeling
    {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d m : ℕ} {B : ℝ}
    {D : RationalFilteredNilmanifold L s d}
    (dictionary : NativeGridRightDictionary D m B) (rightAt : X → D.RealGroup)
    (hgrid : ∀ x, (D.basis.baseChange ℝ).equivFun (rightAt x).coord ∈
      realDenominatorGrid m) :
    ∃ label : X → Fin dictionary.count, ∀ x,
      (∃ γ ∈ D.realLattice, rightAt x = dictionary.representative (label x) * γ) ∧
      ∀ g : D.RealGroup,
        (QuotientGroup.mk (g * rightAt x) : D.Space) =
          QuotientGroup.mk (g * dictionary.representative (label x)) := by
  classical
  choose label γ hγ heq using fun x => dictionary.cover (rightAt x) (hgrid x)
  refine ⟨label, fun x => ⟨⟨γ x, hγ x, heq x⟩, ?_⟩⟩
  intro g
  rw [heq x, ← mul_assoc]
  exact QuotientGroup.mk_mul_of_mem _ (hγ x)

end NativeGridRightDictionary

theorem exists_native_grid_right_dictionary (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp p →
      Nonempty (NativeGridRightDictionary D m (Real.exp ((p + C) ^ C))) := by
  obtain ⟨a, _, hrep⟩ := exists_native_rational_representatives s
  let P : Polynomial ℕ :=
    (Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a + 7) ^ 7
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD m hm hmp
  obtain ⟨q, hq, hqp, hreps⟩ := hrep D p hp hD m hm hmp
  let t := p + (p + a) ^ a
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by
    dsimp [t]
    exact le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hat : (p + a) ^ a ≤ t := by dsimp [t]; linarith
  have htbox : t ≤ (t + 2) ^ 2 := le_power_budget ht (by decide)
  have hboxcount : (t + 2) ^ 2 ≤ (t + 7) ^ 7 :=
    (pow_le_pow_left₀ (by linarith) (by linarith : t + 2 ≤ t + 7) 2).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ t + 7) (by decide : 2 ≤ 7))
  have hcountC : (t + 7) ^ 7 ≤ (p + C) ^ C := by
    simpa [P, t, Polynomial.eval₂_pow] using hbudget p hp
  have hboxC := hboxcount.trans hcountC
  have haC := hat.trans (htbox.trans hboxC)
  obtain ⟨n, hn, hncount, rep, hrepbounds, hcover⟩ :=
    exists_bounded_native_grid_enumeration D q hq (Real.exp_pos ((t + 2) ^ 2)).le
  have hnexp : (n : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    apply (Nat.cast_le.mpr hncount).trans
    have hcount := grid_box_count_le_exp 2 d q (by decide) ht (hD.1.trans hpt)
      (hqp.trans (Real.exp_le_exp.mpr hat))
    norm_num at hcount
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      using hcount.trans (Real.exp_le_exp.mpr hcountC)
  refine ⟨{
    denominator := q
    count := n
    denominator_pos := hq
    count_pos := hn
    denominator_bound := hqp.trans (Real.exp_le_exp.mpr haC)
    count_bound := hnexp
    representative := rep
    representative_bounds := fun j =>
      ⟨fun i => ((hrepbounds j).1 i).trans (Real.exp_le_exp.mpr hboxC), (hrepbounds j).2⟩
    cover := ?_
  }⟩
  intro g hg
  obtain ⟨r, hr, hrgrid, γ, hγ, heq⟩ := (hreps g hg).1
  obtain ⟨j, hj⟩ := hcover r
    (fun i => (hr i).trans (Real.exp_le_exp.mpr (hat.trans htbox))) hrgrid
  exact ⟨j, γ, hγ, by simpa only [hj] using heq⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end


