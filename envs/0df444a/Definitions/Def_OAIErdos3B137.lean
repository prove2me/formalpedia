-- Prove2me | Definitions.Def_OAIErdos3B137
-- name    : OAIErdos3B137
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T16:23:13.159108+00:00
-- url     : https://prove2.me/theorems/74c46a85-0d95-4653-b3a1-9beb82158ba7
-- title:
--   OpenAI Erdős-3 split, definitions bundle 138 of 149
-- statement:
--   Definitions bundle 138 of 149 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B136`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 138 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.coeff_scalarSymbolPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.exists_bounded_fast_graded_relative_kernel_generators`, `OAI.Erdos3.NilpotentLieFiltration.exists_bounded_full_fast_relative_generators`, `OAI.Erdos3.NilpotentLieFiltration.exists_full_fast_relative_generators_exp`, `OAI.Erdos3.NilpotentLieFiltration.exists_marked_polynomial_kernel_slow_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_symbol_of_gradedPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousPullback_quotient_mem_of_restricted_grade_values`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousPullback_residual_quotient_mem`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousQuotientGradedPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousQuotientGradedPolynomial_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousQuotientGradedPolynomial_coefficientBound`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousQuotientGradedPolynomial_coefficientGrid`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousQuotientGradedPolynomial_eval`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousQuotientGradedPolynomial_graded`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousQuotientSymbolLift`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousQuotientSymbolLift_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousQuotientSymbolLift_eval`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousQuotientSymbolLift_pure`, `OAI.Erdos3.NilpotentLieFiltration.nativeFast_derivativeSystem_to_formal`, `OAI.Erdos3.NilpotentLieFiltration.nativeFast_liftSystem_to_formal`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_filteredRealPolynomialSection`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_filteredRealPolynomialSection_exp`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialHom_bound`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialHom_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialHom_correction`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialHom_grid`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialLie_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialLie_constant`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialLie_fullFast_mem`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialLie_graded`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialLie_horizontal_mem`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialLie_linear`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedShiftedGradedPolynomial_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficient_relative_iff_polynomial`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientGradedPolynomial_basisLift`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomialHom`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomialHom_injective`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomialHom_native`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_gradeProjection_eq_weightedHomogeneousPart`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_homogeneousPullback`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_homogeneousQuotientSymbolLift`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_ofGradedPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_rational_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_slow_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolHom_homogeneousChart`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeEvaluation_homogeneousPullback`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeEvaluation_quotientLift`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeEvaluation_zero`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeQuotientPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeQuotientPolynomial_eval`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeQuotientPolynomial_homogeneous`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolHomogeneousPullback`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolHomogeneousPullbackHom`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolHomogeneousPullbackHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolHomogeneousPullbackLie`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfGradedPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfGradedPolynomial_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfPolynomial_homogeneousChart`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedSndMap_basis_height`, `OAI.Erdos3.NilpotentLieFiltration.restrictedMajorCorrection`, `OAI.Erdos3.NilpotentLieFiltration.restrictedMajorOuterFactors`, `OAI.Erdos3.NilpotentLieFiltration.restricted_symbol_grade_matching`, `OAI.Erdos3.NilpotentLieFiltration.restricted_symbol_grade_terminal`, `OAI.Erdos3.NilpotentLieFiltration.restricted_symbol_major_grade_step`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial_approximation_of_factorization`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial_eq_zero_of_fast`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial_exists_coefficient_grid`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial_homogeneous_normalized_splitting`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial_mul`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial_rational_coefficients`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial_slow_coefficients`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial_slow_coefficients_of_height`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial_weightedComponent_normalized_splitting`, `OAI.Erdos3.NilpotentLieFiltration.symbolRationalGrid_homogeneousPullback_of_coefficientGrid`, `OAI.Erdos3.NilpotentLieFiltration.symbolRationalGrid_integerTopPullback_of_coefficientGrid`, `OAI.Erdos3.NilpotentLieFiltration.symbolRationalGrid_of_gradedPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.symbolSlowBound_of_gradedPolynomial`, `OAI.Erdos3.VectorPolynomial.CoefficientGrid.realChartSubstitute_integral`, `OAI.Erdos3.VectorPolynomial.allocatedCanonicalProjectionLog`, `OAI.Erdos3.VectorPolynomial.allocatedSelectedGridExtension`, `OAI.Erdos3.VectorPolynomial.canonicalProjectionRowCost`, `OAI.Erdos3.VectorPolynomial.coefficientGrid_iff_coordinate`, `OAI.Erdos3.VectorPolynomial.coefficients_weightedHomogeneousPart`, `OAI.Erdos3.VectorPolynomial.coordinate_realChartSubstitute_for_grid`, `OAI.Erdos3.VectorPolynomial.coordinate_weightedHomogeneousPart`, `OAI.Erdos3.VectorPolynomial.eval₂_weightedHomogeneousPart`, `OAI.Erdos3.VectorPolynomial.eval₂_weightedHomogeneousPart_decomposition_on`, `OAI.Erdos3.VectorPolynomial.eval₂_weightedHomogeneousPart_eq_on`, `OAI.Erdos3.VectorPolynomial.eval₂_weightedHomogeneousPart_eq_zero_on`, `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalProjection_budget`, `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalProjection_composed_budget`, `OAI.Erdos3.VectorPolynomial.exists_allocated_positive_fourier_data`, `OAI.Erdos3.VectorPolynomial.exists_preparedBadProductFinalBudget`, `OAI.Erdos3.VectorPolynomial.exists_preparedBadProductSourceBudget`, `OAI.Erdos3.VectorPolynomial.exists_preparedBadProductSpatialBudget`, `OAI.Erdos3.VectorPolynomial.exists_preparedModularCanonicalDetectorAllocationBudget`, `OAI.Erdos3.VectorPolynomial.preparedBadProductCoefficientExponent`, `OAI.Erdos3.VectorPolynomial.preparedBadProductSpatialExponent`, `OAI.Erdos3.VectorPolynomial.weightedHomogeneousPart`, `OAI.Erdos3.VectorPolynomial.weightedHomogeneousPart_coordinateBound`, `OAI.Erdos3.VectorPolynomial.weightedHomogeneousPart_coordinateGrid`, `OAI.Erdos3.VectorPolynomial.weightedHomogeneousPart_eq_self`, `OAI.Erdos3.VectorPolynomial.weightedHomogeneousPart_homogeneous`, `OAI.Erdos3.VectorPolynomial.weightedHomogeneousPart_monomial`, `OAI.Erdos3.VectorPolynomial.weightedHomogeneousPart_tmul`, `OAI.Erdos3.VectorPolynomial.weightedRadialPolynomial`, `OAI.Erdos3.VectorPolynomial.weightedRadialPolynomial_coefficient`, `OAI.Erdos3.VectorPolynomial.weightedRadialPolynomial_eq_zero`, `OAI.Erdos3.VectorPolynomial.weightedRadialPolynomial_eval`, `OAI.Erdos3.linearMap_abs_repr_le`, `OAI.Erdos3.realChartSubstitute_mem_gradedPolynomialSubmodule`, `OAI.Erdos3.real_graded_quotient_section_residual`, `OAI.Erdos3.real_quotient_section_residual`, `OAI.Erdos3.realifyFunctional_eq_sum_basis`, `_private.Polynomial.MarkedPolynomialSectionSlow.0.OAI.Erdos3.NilpotentLieFiltration.section_exponential_budget`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B050
import Definitions.Def_OAIErdos3B135

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.GradedPolynomialSymbolInverse
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

section General

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedShiftedGradedPolynomial_coefficient (k : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.realAdaptedShiftedGradedPolynomial e ω hF w k x) α =
      (F.gradedPieceProjection e ω hF (Finsupp.weight w α + k)).baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap w x) α) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
    rw [F.realAdaptedShiftedGradedPolynomial_tensor, LinearMap.baseChange_tmul,
      realificationRealLinearEquiv_apply, coefficients_realificationLinearEquiv_tmul,
      F.adaptedShiftedGradedPolynomial_apply, F.shiftedGradedPolynomial_coefficient,
      F.realAdaptedPolynomialMap_coefficient_tmul, LinearMap.baseChange_tmul]

theorem realAdaptedGradedPolynomialLie_coefficient
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.realAdaptedGradedPolynomialLie e ω hF w x) α =
      (F.gradedPieceProjection e ω hF (Finsupp.weight w α)).baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap w x) α) := by
  rw [F.realAdaptedGradedPolynomialLie_apply, F.realAdaptedShiftedGradedPolynomial_coefficient]
  simp only [Nat.add_zero]

theorem realAdaptedGradedPolynomialLie_graded (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realAdaptedGradedPolynomialLie e ω hF w x ∈
      gradedPolynomialSubmodule ((F.associatedGradedBasis e ω hF).baseChange ℝ) ω w := by
  rw [F.realAdaptedGradedPolynomialLie_symbol]
  exact F.realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule e ω hF w _

theorem realAdaptedGradedPolynomialLie_constant (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    coefficients (F.realAdaptedGradedPolynomialLie e ω hF w x) 0 = 0 := by
  rw [F.realAdaptedGradedPolynomialLie_symbol]
  apply ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr.injective
  ext i
  have hi : Finsupp.weight w (0 : σ →₀ ℕ) ≠ ω i := by
    rw [map_zero]
    exact Nat.ne_of_lt (F.adaptedBasis_weight_pos e ω hF i)
  simpa only [map_zero, Finsupp.zero_apply] using
    F.realGradedSymbolPolynomial_coordinate_of_ne e ω hF w
      (realificationLieHom (F.polynomialSymbolMap w) x) 0 i hi

omit w in
theorem realAdaptedGradedPolynomialLie_linear
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) (i : σ) :
    coefficients (F.realAdaptedGradedPolynomialLie e ω hF (fun _ : σ => 1) x)
        (Finsupp.single i 1) =
      (F.layerOneGradedMap e ω hF).baseChange ℝ ((F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) x) (Finsupp.single i 1))) := by
  rw [F.realAdaptedGradedPolynomialLie_coefficient, F.realLayerOneGradedMap_mk]
  simp only [Finsupp.weight_single, one_smul]

omit w in
theorem realAdaptedGradedPolynomialLie_horizontal_mem
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (K : Submodule ℝ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hK : ∀ i, (F.layerOneGradedMap e ω hF).baseChange ℝ ((F.layer 2).mkQ.baseChange ℝ
      (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) x) (Finsupp.single i 1))) ∈ K)
    (α : σ →₀ ℕ) :
    basisGradeProjection ((F.associatedGradedBasis e ω hF).baseChange ℝ) ω 1
      (coefficients (F.realAdaptedGradedPolynomialLie e ω hF (fun _ : σ => 1) x) α) ∈ K := by
  have hgraded := F.realAdaptedGradedPolynomialLie_graded e ω hF (fun _ : σ => 1) x
  by_cases hα : Finsupp.weight (fun _ : σ => (1 : ℕ)) α = 1
  · obtain hz | ⟨i, rfl⟩ := exponent_of_weight_le_one α hα.le
    · subst α
      simp only [map_zero] at hα
      omega
    · have hg := hgraded (Finsupp.single i 1)
      simp only [Finsupp.weight_single, one_smul, LinearMap.restrictScalars_apply] at hg
      rw [hg, F.realAdaptedGradedPolynomialLie_linear]
      exact hK i
  · have hz := gradedPolynomialSubmodule_projection_homogeneous
      ((F.associatedGradedBasis e ω hF).baseChange ℝ) ω (fun _ : σ => 1) _ hgraded 1 α hα
    simp only [coefficients_map, LinearMap.restrictScalars_apply] at hz
    rw [hz]
    exact K.zero_mem

end General

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem realAdaptedGradedPolynomialLie_fullFast_mem
    (hW : BasisGradedSubmodule
      (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis e ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF))
      (fun i => squareBasisWeight ω i.val) W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W))
    (α : σ →₀ ℕ) :
    coefficients (F.realAdaptedGradedPolynomialLie e ω hF (fun _ : σ => 1) g.val.coord) α ∈
      realificationLieSubalgebra (F.fullFastGradedDiagonal W) := by
  have hg : g.val ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ : σ => 1)
      (F.fullFastGradedDiagonal W) := by
    rw [F.fullFastPointwise_subgroup_eq e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) W hW]
    exact g.property
  have hs := (F.mem_realPointwisePolynomialSubgroup e ω hF (fun _ => 1)
    (F.fullFastGradedDiagonal W) g.val).mp hg
  have hc := (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ => 1)
    (F.fullFastGradedDiagonal W) _).mp hs α
  rw [F.realAdaptedGradedPolynomialLie_symbol]
  exact hc

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

section General

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedGradedPolynomialHom_coordinate
    (g : F.RealAdaptedPolynomialGroup w) (α : σ →₀ ℕ) (i : ι) :
    ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr
      (coefficients (F.realAdaptedGradedPolynomialHom e ω hF w g).coord α) i =
        if ω i = Finsupp.weight w α then
          (e.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap w g.coord) α) i else 0 := by
  change ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr
    (coefficients (F.realAdaptedGradedPolynomialLie e ω hF w g.coord) α) i = _
  rw [F.realAdaptedGradedPolynomialLie_coefficient, F.real_gradedPieceProjection_coordinate]

theorem realAdaptedGradedPolynomialHom_bound
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealAdaptedPolynomialGroup w) (hg : F.RealAdaptedCoefficientBound e ω hF w T M g.coord) :
    CoefficientBound ((F.associatedGradedBasis e ω hF).baseChange ℝ) T M
      (F.realAdaptedGradedPolynomialHom e ω hF w g).coord := by
  have hfull := (F.realAdaptedCoefficientBound_iff_formal e ω hF w T hT hM g.coord).mp hg
  intro α i
  rw [F.realAdaptedGradedPolynomialHom_coordinate]
  split_ifs
  · exact hfull α i
  · rw [abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem realAdaptedGradedPolynomialHom_grid (l : ℕ)
    (g : F.RealAdaptedPolynomialGroup w) (hg : F.RealAdaptedCoefficientGrid e ω hF w l g.coord) :
    CoefficientGrid ((F.associatedGradedBasis e ω hF).baseChange ℝ) l
      (F.realAdaptedGradedPolynomialHom e ω hF w g).coord := by
  classical
  intro α
  obtain ⟨a, ha⟩ := (F.realAdaptedCoefficientGrid_iff_formal e ω hF w l g.coord).mp hg α
  refine ⟨fun i => if ω i = Finsupp.weight w α then a i else 0, ?_⟩
  funext i
  change ((if ω i = Finsupp.weight w α then a i else 0 : ℤ) : ℝ) =
    (l : ℝ) * ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr
      (coefficients (F.realAdaptedGradedPolynomialHom e ω hF w g).coord α) i
  rw [F.realAdaptedGradedPolynomialHom_coordinate]
  split_ifs
  · exact congrFun ha i
  · simp only [Int.cast_zero, mul_zero]

end General

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem realAdaptedGradedPolynomialHom_correction
    (hW : BasisGradedSubmodule
      (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis e ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF))
      (fun i => squareBasisWeight ω i.val) W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W)) :
    F.associatedGradedFiltration.FormalCorrectionProperty (F.associatedGradedBasis e ω hF) ω
      (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
      (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val) :=
  ⟨F.realAdaptedGradedPolynomialLie_fullFast_mem e ω hF W hW g,
    F.realAdaptedGradedPolynomialLie_graded e ω hF (fun _ : σ => 1) g.val.coord,
    F.realAdaptedGradedPolynomialLie_constant e ω hF (fun _ : σ => 1) g.val.coord⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realSymbolOfGradedPolynomial
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) : F.RealPolynomialSymbol w :=
  ((F.polynomialSymbolBasis e ω hF w).baseChange ℝ).repr.symm
    (supportedCoordinates ((F.associatedGradedBasis e ω hF).baseChange ℝ)
      {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2} P)

theorem realSymbolOfGradedPolynomial_coordinate
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) (z : SymbolBasisIndex w ω) :
    ((F.polynomialSymbolBasis e ω hF w).baseChange ℝ).repr
      (F.realSymbolOfGradedPolynomial e ω hF w P) z =
      ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr (coefficients P z.val.1) z.val.2 := by
  rw [realSymbolOfGradedPolynomial, LinearEquiv.apply_symm_apply]
  rfl

theorem realGradedSymbolPolynomial_ofGradedPolynomial
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hP : P ∈ gradedPolynomialSubmodule ((F.associatedGradedBasis e ω hF).baseChange ℝ) ω w) :
    F.realGradedSymbolPolynomial e ω hF w (F.realSymbolOfGradedPolynomial e ω hF w P) = P := by
  apply coefficients.injective
  ext α
  apply ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr.injective
  ext i
  by_cases h : Finsupp.weight w α = ω i
  · exact (F.realGradedSymbolPolynomial_coordinate e ω hF w _ ⟨(α, i), h⟩).trans
      (F.realSymbolOfGradedPolynomial_coordinate e ω hF w P ⟨(α, i), h⟩)
  · rw [F.realGradedSymbolPolynomial_coordinate_of_ne e ω hF w _ α i h]
    have hi := congrArg (fun v => ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr v i) (hP α)
    simp only [LinearMap.restrictScalars_apply] at hi
    rw [basisGradeProjection_repr, if_neg (Ne.symm h)] at hi
    exact hi

noncomputable def realGradedSymbolPolynomialHom :
    F.RealPolynomialSymbolGroup w →*
      PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.realGradedSymbolPolynomial e ω hF w)

theorem realGradedSymbolPolynomialHom_injective :
    Function.Injective (F.realGradedSymbolPolynomialHom e ω hF w) := by
  intro x y h
  apply NilpotentLieBCHGroup.ext
  apply F.realGradedSymbolPolynomial_injective e ω hF w
  exact congrArg NilpotentLieBCHGroup.coord h

theorem exists_symbol_of_gradedPolynomial
    (P : PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot)
    (hP : P.coord ∈ gradedPolynomialSubmodule ((F.associatedGradedBasis e ω hF).baseChange ℝ) ω w) :
    ∃ x : F.RealPolynomialSymbolGroup w, F.realGradedSymbolPolynomialHom e ω hF w x = P := by
  refine ⟨⟨F.realSymbolOfGradedPolynomial e ω hF w P.coord⟩, ?_⟩
  apply NilpotentLieBCHGroup.ext
  exact F.realGradedSymbolPolynomial_ofGradedPolynomial e ω hF w P.coord hP

theorem realGradedSymbolPolynomialHom_native (g : F.RealAdaptedPolynomialGroup w) :
    F.realGradedSymbolPolynomialHom e ω hF w
      (F.realPolynomialSymbolHom e ω hF w (F.realAdaptedPolynomialGroupHom w g)) =
      F.realAdaptedGradedPolynomialHom e ω hF w g := by
  apply NilpotentLieBCHGroup.ext
  change F.realGradedSymbolPolynomial e ω hF w
    (F.realSymbolOfPolynomial e ω hF w (F.realAdaptedPolynomialMap w g.coord)) = _
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap]
  exact (F.realAdaptedGradedPolynomialLie_symbol e ω hF w g.coord).symm

theorem symbolSlowBound_of_gradedPolynomial (T : σ → ℝ) (M : ℝ) (x : F.RealPolynomialSymbolGroup w)
    (hx : CoefficientBound ((F.associatedGradedBasis e ω hF).baseChange ℝ) T M
      (F.realGradedSymbolPolynomialHom e ω hF w x).coord) : F.SymbolSlowBound e ω hF w T M x := by
  intro z
  rw [← F.realGradedSymbolPolynomial_coordinate e ω hF w x.coord z]
  exact hx z.val.1 z.val.2

theorem symbolRationalGrid_of_gradedPolynomial (l : ℕ) (x : F.RealPolynomialSymbolGroup w)
    (hx : CoefficientGrid ((F.associatedGradedBasis e ω hF).baseChange ℝ) l
      (F.realGradedSymbolPolynomialHom e ω hF w x).coord) : F.SymbolRationalGrid e ω hF w l x := by
  choose a ha using hx
  refine ⟨fun z => a z.val.1 z.val.2, ?_⟩
  funext z
  have hz := congrFun (ha z.val.1) z.val.2
  change (a z.val.1 z.val.2 : ℝ) = (l : ℝ) *
    ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial e ω hF w x.coord) z.val.1) z.val.2 at hz
  rw [F.realGradedSymbolPolynomial_coordinate e ω hF w x.coord z] at hz
  exact hz

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeFormalPolynomialSystems
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Kf" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf)
local notation "φ" => F.realFirstCoefficientGradedPolynomial e ω hF (fun _ : σ => 1)
local notation "Vg" => Submodule.restrictScalars ℚ (Submodule.baseChange ℝ (F.fullFastGradedRelative e ω hF W))

theorem realFastCoefficient_relative_iff_polynomial
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (x : F.RealFirstCoefficientModule (fun _ : σ => 1)) :
    x ∈ Kf ↔ φ x ∈ coefficientSubmodule Vg := by
  rw [F.realFirstCoefficientFastSubmodule_relative]
  exact F.realFirstCoefficientFastSubmodule_iff_graded e ω hF (fun _ : σ => 1) W
    (fun _ => Nat.zero_lt_one) hW x

theorem nativeFast_liftSystem_to_formal
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf)
    (S R : κ → F.RealFirstCoefficientModule (fun _ : σ => 1))
    (h : ∀ z, (Kf).mkQ (S z) =
      F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf g ((Kf).mkQ (R z))) :
    PolynomialLiftSystemMod Vg (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val)
      (fun z => φ (S z)) (fun z => φ (R z)) := by
  intro z
  have hz := h z
  rw [F.realFastCoefficientAction_mk] at hz
  have hq : (Kf).mkQ (S z - F.realFirstCoefficientAdjoint (fun _ : σ => 1) g.val (R z)) = 0 := by
    rw [map_sub, hz, sub_self]
  have hm : S z - F.realFirstCoefficientAdjoint (fun _ : σ => 1) g.val (R z) ∈ Kf :=
    (Submodule.Quotient.mk_eq_zero _).mp hq
  have hp := (F.realFastCoefficient_relative_iff_polynomial e ω hF W hW _).mp hm
  simpa only [map_sub, F.realFirstCoefficientGradedPolynomial_adjoint] using hp

theorem realFirstCoefficientGradedPolynomial_basisLift {K : Type*}
    [AddCommGroup K] [Module ℝ K] (b : Basis κ ℝ K)
    (S : K →ₗ[ℝ] F.RealFirstCoefficientModule (fun _ : σ => 1)) (x : K) :
    φ (S x) = basisPolynomialLift b (fun z => φ (S (b z))) x := by
  have he : (φ).comp S = basisPolynomialLift b (fun z => φ (S (b z))) := by
    apply b.ext
    intro z
    simp only [LinearMap.comp_apply, basisPolynomialLift_basis]
  exact LinearMap.congr_fun he x

variable [Fintype σ] [DecidableEq σ]

theorem nativeFast_derivativeSystem_to_formal
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf)
    (small rational extra : σ → F.RealFirstCoefficientModule (fun _ : σ => 1))
    (h : ∀ i, F.realFastCoefficientDirectionMap Wf g.val (Pi.single i 1) =
      (Kf).mkQ (small i) +
        F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf g ((Kf).mkQ (rational i)) +
          (Kf).mkQ (extra i)) :
    PolynomialDerivativeSystemMod Vg (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val)
      (fun i => φ (small i)) (fun i => φ (rational i)) (fun i => φ (extra i)) := by
  intro i
  have hi := h i
  rw [F.realFastCoefficientAction_mk] at hi
  change (Kf).mkQ (F.realFirstCoefficientDirectionMap g.val.coord (Pi.single i 1)) = _ at hi
  have hq : (Kf).mkQ (F.realFirstCoefficientDirectionMap g.val.coord (Pi.single i 1) -
      (small i + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g.val (rational i) + extra i)) = 0 := by
    rw [map_sub, map_add, map_add]
    exact sub_eq_zero.mpr hi
  have hm : F.realFirstCoefficientDirectionMap g.val.coord (Pi.single i 1) -
      (small i + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g.val (rational i) + extra i) ∈ Kf :=
    (Submodule.Quotient.mk_eq_zero _).mp hq
  have hp := (F.realFastCoefficient_relative_iff_polynomial e ω hF W hW
    (F.realFirstCoefficientDirectionMap g.val.coord (Pi.single i 1) -
      (small i + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g.val (rational i) + extra i))).mp hm
  simpa only [map_sub, map_add, F.realFirstCoefficientGradedPolynomial_direction,
    F.realFirstCoefficientGradedPolynomial_adjoint] using hp

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FullFastRelativeSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "ωQ" => (fun a : QuotientTopBasisIndex s ω => ω (Subtype.val a))
local notation "bQ" => F.quotientTop.associatedGradedBasis
  (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)

theorem reducedSquareGradedSndMap_basis_height (a : ReducedSquareBasisIndex s ω)
    (i : QuotientTopBasisIndex s ω) :
    RationalHeightLE ((bQ).repr (F.reducedSquareGradedSndMap (bW a)) i) 1 := by
  rw [F.reducedSquareGradedSndMap_coordinate e ω hF]
  exact basis_repr_height_one bW a _

variable [Fintype ι] [Fintype κ]

theorem exists_bounded_fast_graded_relative_kernel_generators
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H) :
    ∃ r : ℕ, r ≤ Fintype.card (QuotientTopBasisIndex s ω) ∧
      ∃ z : κ → F.squareFiltration.quotientTop.AssociatedGraded,
        Submodule.span ℚ (Set.range z) = F.fastGradedRelativeKernel W ∧
        ∀ j i, RationalHeightLE ((bW).repr (z j) i)
          (fastKernelGeneratorHeight (Fintype.card (ReducedSquareBasisIndex s ω))
            (Fintype.card κ) r H) := by
  have hPv (j : κ) (i : QuotientTopBasisIndex s ω) :
      RationalHeightLE ((bQ).repr (F.reducedSquareGradedSndMap (v j)) i)
        ((Fintype.card (ReducedSquareBasisIndex s ω) + 1) *
          H ^ Fintype.card (ReducedSquareBasisIndex s ω)) := by
    simpa only [mul_one, LieHom.coe_toLinearMap] using linearMap_coordinate_height
      bW bQ F.reducedSquareGradedSndMap.toLinearMap
      (F.reducedSquareGradedSndMap_basis_height e ω hF) (v j) (hv j) i
  have hB : 1 ≤ (Fintype.card (ReducedSquareBasisIndex s ω) + 1) *
      H ^ Fintype.card (ReducedSquareBasisIndex s ω) := by
    have hHp : 0 < H := hH
    exact Nat.succ_le_of_lt (by positivity)
  have he := exists_bounded_span_kernel_generators bW bQ
    F.reducedSquareGradedSndMap.toLinearMap v hB hv hPv
  simpa only [hspan, fastKernelGeneratorHeight, fastGradedRelativeKernel,
    LieHom.ker_toSubmodule] using he

theorem exists_bounded_full_fast_relative_generators
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H) :
    ∃ r : ℕ, r ≤ Fintype.card (QuotientTopBasisIndex s ω) ∧
      ∃ z : κ → F.AssociatedGraded,
        Submodule.span ℚ (Set.range z) = F.fullFastGradedRelative e ω hF W ∧
        ∀ j i, RationalHeightLE ((F.associatedGradedBasis e ω hF).repr (z j) i)
          (fastCoefficientGeneratorHeight (Fintype.card (ReducedSquareBasisIndex s ω))
            (Fintype.card κ) r H) := by
  obtain ⟨r, hr, z, hz, hzh⟩ :=
    F.exists_bounded_fast_graded_relative_kernel_generators e ω hF W v hspan hH hv
  refine ⟨r, hr, (F.reducedSquareGradedDifference e ω hF) ∘ z, ?_, fun j i => ?_⟩
  · rw [fullFastGradedRelative, ← hz, Submodule.map_span, ← Set.range_comp]
  · simpa only [Function.comp_apply, mul_one, fastCoefficientGeneratorHeight] using
      linearMap_coordinate_height bW (F.associatedGradedBasis e ω hF)
        (F.reducedSquareGradedDifference e ω hF)
        (F.reducedSquareGradedDifference_basis_height e ω hF) (z j) (hzh j) i

theorem exists_full_fast_relative_generators_exp
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopBasisIndex s ω) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 40) ∧
      ∃ z : κ → F.AssociatedGraded,
        Submodule.span ℚ (Set.range z) = F.fullFastGradedRelative e ω hF W ∧
        ∀ j i, RationalHeightLE ((F.associatedGradedBasis e ω hF).repr (z j) i) H' := by
  obtain ⟨r, hr, z, hz, hzh⟩ :=
    F.exists_bounded_full_fast_relative_generators e ω hF W v hspan hH hv
  exact ⟨_, fastCoefficientGeneratorHeight_pos _ _ _ _ hH,
    fastCoefficientGeneratorHeight_le_exp _ _ _ _ hp hn hm
      ((Nat.cast_le.mpr hr).trans hq) hHp, z, hz, hzh⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedPositiveFourierData
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)

include hC hV in
theorem exists_allocated_positive_fourier_data (q : ℕ)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {p : ℝ} (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp p) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp p)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp p) (hLP : (S.value : ℝ) ≤ Real.exp p)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp p) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp p) :
    let Q := positiveComparisonDataBudget m q p
    let b := allocatedFourierLogBudget m (2 * p + 4)
    ((allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) ≤ Real.exp b) ∧
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ) (coeff : F → ℂ),
      (∀ t j d, d.degree ≤ j.val + 1 → ∀ i, |(frequency t j d i : ℝ)| ≤ Real.exp Q) ∧
      (∑ t, ‖coeff t‖) ≤ Real.exp Q ∧
      ∀ z, ‖(allocatedCoefficientDensity B U basis hb o hR hσ S z : ℂ) -
        coefficientTorusFourierSum U frequency coeff z‖ ≤ positiveProjectionAccuracy p := by
  let P := 2 * p + 4
  have hP : 0 ≤ P := by dsimp [P]; linarith
  have hpP : p ≤ P := by dsimp [P]; linarith
  have hE := Real.exp_le_exp.mpr hpP
  have hdata := allocatedCoefficient_fourier_input_budget B (J := J) R σ S.value S.positive C V
    hP (hm.trans hpP) (hK.trans hpP) hR hσ
    (fun j => (hRP j).trans hE) (fun j => (hσP j).trans hE)
    (fun j => (hcount j).trans hpP) (fun j => (hI j).trans hpP) (fun j => (hn j).trans hpP)
    (fun j => (hJ j).trans hpP) (hAP.trans hE) (hLP.trans hE)
    (fun j => (hCP j).trans hE) (fun j => (hVP j).trans hE)
  refine ⟨hdata.2.2.1, ?_⟩
  obtain ⟨F, inst, frequency, coeff, _, hfreq, hcoeff, happ⟩ :=
    exists_allocated_coefficient_uniform_fourier B U basis hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall hP (hm.trans hpP) (hK.trans hpP)
      (fun j => (hRP j).trans hE) (fun j => (hσP j).trans hE)
      (fun j => (hcount j).trans hpP) (fun j => (hI j).trans hpP) (fun j => (hn j).trans hpP)
      (fun j => (hJ j).trans hpP) (hAP.trans hE) (hLP.trans hE)
      (fun j => (hCP j).trans hE) (fun j => (hVP j).trans hE)
      (show 0 < positiveProjectionAccuracy p from Real.exp_pos _)
      (by simp only [positiveProjectionAccuracy, Real.exp_neg, inv_inv]; exact le_rfl)
  let _ := inst
  have hQ := (positiveComparisonDataBudget_bounds m q hp).2.2.2.1
  have hF := allocatedFourierOutputBudget_dominates m hP
  refine ⟨F, inst, frequency, coeff, ?_, ?_, happ⟩
  · exact fun t j d hd i => (hfreq t j d hd i).trans (Real.exp_le_exp.mpr (hF.2.1.trans hQ))
  · exact hcoeff.trans (Real.exp_le_exp.mpr (hF.2.2.trans hQ))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousQuotientSymbolLiftBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ R S V W : Type*} [CommRing R] [CommRing S]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

noncomputable def weightedHomogeneousPart (w : σ → ℕ) (d : ℕ) :
    VectorPolynomial σ R V →ₗ[R] VectorPolynomial σ R V :=
  (MvPolynomial.weightedHomogeneousComponent w d).rTensor V

theorem weightedHomogeneousPart_tmul (w : σ → ℕ) (d : ℕ)
    (P : MvPolynomial σ R) (v : V) :
    weightedHomogeneousPart w d (P ⊗ₜ[R] v) =
      MvPolynomial.weightedHomogeneousComponent w d P ⊗ₜ[R] v := rfl

theorem coefficients_weightedHomogeneousPart (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    coefficients (weightedHomogeneousPart w d p) α =
      if Finsupp.weight w α = d then coefficients p α else 0 := by
  classical
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial vector =>
    rw [weightedHomogeneousPart_tmul, coefficients_tmul,
      MvPolynomial.coeff_weightedHomogeneousComponent, coefficients_tmul]
    split <;> simp_all
  | add first second hfirst hsecond =>
    simp only [map_add, Finsupp.add_apply, hfirst, hsecond]
    split <;> simp

theorem weightedHomogeneousPart_monomial (w : σ → ℕ) (d : ℕ)
    (α : σ →₀ ℕ) (v : V) :
    weightedHomogeneousPart w d (monomial (R := R) α v) =
      if Finsupp.weight w α = d then monomial α v else 0 := by
  classical
  apply coefficients.injective
  ext β
  split <;> rename_i hd
  all_goals rw [coefficients_weightedHomogeneousPart]
  by_cases h : α = β
  · subst β
    simp [hd]
  · simp [Ne.symm h]
  by_cases h : α = β
  · subst β
    simp [hd]
  · simp [Ne.symm h]

theorem weightedHomogeneousPart_homogeneous (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) (hα : Finsupp.weight w α ≠ d) :
    coefficients (weightedHomogeneousPart w d p) α = 0 := by
  rw [coefficients_weightedHomogeneousPart, if_neg hα]

theorem weightedHomogeneousPart_eq_self {w : σ → ℕ} {d : ℕ}
    {p : VectorPolynomial σ R V}
    (hp : ∀ α, Finsupp.weight w α ≠ d → coefficients p α = 0) :
    weightedHomogeneousPart w d p = p := by
  apply coefficients.injective
  ext α
  rw [coefficients_weightedHomogeneousPart]
  split
  · rfl
  · exact (hp α ‹_›).symm

theorem coordinate_weightedHomogeneousPart (f : V →+ S) (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) :
    coordinate f (weightedHomogeneousPart w d p) =
      MvPolynomial.weightedHomogeneousComponent w d (coordinate f p) := by
  classical
  ext α
  simp only [coeff_coordinate, coefficients_weightedHomogeneousPart,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  split <;> simp

theorem eval₂_weightedHomogeneousPart [Algebra R S] [Module S V] [IsScalarTower R S V]
    (w : σ → ℕ) (d : ℕ) (x : σ → S) (p : VectorPolynomial σ R V) :
    eval₂ x (weightedHomogeneousPart w d p) =
      ∑ α ∈ (coefficients p).support,
        if Finsupp.weight w α = d then
          (α.prod fun i n => x i ^ n) • coefficients p α else 0 := by
  classical
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, weightedHomogeneousPart_monomial]
  apply Finset.sum_congr rfl
  intro α _
  split <;> simp [eval₂_monomial]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]

noncomputable def weightedRadialPolynomial (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (x : σ → ℝ) : VectorPolynomial Unit ℚ V :=
  ∑ α ∈ (coefficients p).support,
    monomial (Finsupp.single () (Finsupp.weight w α))
      ((α.prod fun i n => x i ^ n) • coefficients p α)

theorem weightedRadialPolynomial_eval (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (x : σ → ℝ) (r : ℚ) :
    eval (fun _ : Unit => r) (weightedRadialPolynomial w p x) =
      eval₂ (fun i => (r : ℝ) ^ w i * x i) p := by
  classical
  unfold weightedRadialPolynomial
  conv_rhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, eval_monomial, eval₂_monomial]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finsupp.prod_single_index (by simp), weighted_monomial_dilation]
  rw [mul_smul, ← Rat.cast_pow, ← IsScalarTower.algebraMap_smul ℝ (r ^ Finsupp.weight w α)]
  rfl

omit [IsScalarTower ℚ ℝ V] in
theorem weightedRadialPolynomial_coefficient (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (x : σ → ℝ) (d : ℕ) :
    coefficients (weightedRadialPolynomial w p x) (Finsupp.single () d) =
      ∑ α ∈ (coefficients p).support,
        if Finsupp.weight w α = d then
          (α.prod fun i n => x i ^ n) • coefficients p α else 0 := by
  classical
  simp only [weightedRadialPolynomial, map_sum, Finsupp.finsetSum_apply,
    coefficients_monomial, Finsupp.single_apply, (Finsupp.single_injective ()).eq_iff]

theorem weightedRadialPolynomial_eq_zero (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (x : σ → ℝ)
    (hp : ∀ r : ℚ, eval₂ (fun i => (r : ℝ) ^ w i * x i) p = 0) :
    weightedRadialPolynomial w p x = 0 := by
  apply eq_zero_of_eval_zero
  intro r
  have hr : r = fun _ : Unit => r () := by funext i; cases i; rfl
  rw [hr, weightedRadialPolynomial_eval]
  exact hp (r ())

theorem eval₂_weightedHomogeneousPart_eq_zero_on (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (K : Set (σ → ℝ))
    (hK : ∀ x ∈ K, ∀ r : ℚ, (fun i => (r : ℝ) ^ w i * x i) ∈ K)
    (hp : ∀ x ∈ K, eval₂ x p = 0) (d : ℕ) (x : σ → ℝ) (hx : x ∈ K) :
    eval₂ x (weightedHomogeneousPart w d p) = 0 := by
  have hz := weightedRadialPolynomial_eq_zero w p x (fun r => hp _ (hK x hx r))
  have hc := congrArg (fun q : VectorPolynomial Unit ℚ V =>
    coefficients q (Finsupp.single () d)) hz
  rw [eval₂_weightedHomogeneousPart]
  simpa only [weightedRadialPolynomial_coefficient, map_zero, Finsupp.zero_apply] using hc

theorem eval₂_weightedHomogeneousPart_eq_on (w : σ → ℕ)
    (p q : VectorPolynomial σ ℚ V) (K : Set (σ → ℝ))
    (hK : ∀ x ∈ K, ∀ r : ℚ, (fun i => (r : ℝ) ^ w i * x i) ∈ K)
    (hpq : ∀ x ∈ K, eval₂ x p = eval₂ x q)
    (d : ℕ) (x : σ → ℝ) (hx : x ∈ K) :
    eval₂ x (weightedHomogeneousPart w d p) =
      eval₂ x (weightedHomogeneousPart w d q) := by
  have hzero : ∀ y ∈ K, eval₂ y (p - q) = 0 := by
    intro y hy
    rw [map_sub, hpq y hy, sub_self]
  have h := eval₂_weightedHomogeneousPart_eq_zero_on w (p - q) K hK hzero d x hx
  exact sub_eq_zero.mp (by simpa only [map_sub] using h)

theorem eval₂_weightedHomogeneousPart_decomposition_on (w : σ → ℕ)
    (p a c : VectorPolynomial σ ℚ V) (K : Set (σ → ℝ))
    (hK : ∀ x ∈ K, ∀ r : ℚ, (fun i => (r : ℝ) ^ w i * x i) ∈ K)
    (d : ℕ) (hp : ∀ α, Finsupp.weight w α ≠ d → coefficients p α = 0)
    (hdecomp : ∀ x ∈ K, eval₂ x p = eval₂ x a + eval₂ x c)
    (x : σ → ℝ) (hx : x ∈ K) :
    eval₂ x p = eval₂ x (weightedHomogeneousPart w d a) +
      eval₂ x (weightedHomogeneousPart w d c) := by
  have heq : ∀ y ∈ K, eval₂ y p = eval₂ y (a + c) := by
    intro y hy
    simpa only [map_add] using hdecomp y hy
  have h := eval₂_weightedHomogeneousPart_eq_on w p (a + c) K hK heq d x hx
  simpa only [weightedHomogeneousPart_eq_self hp, map_add] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L Q : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  [AddCommGroup Q] [Module ℚ Q] [Module ℝ Q] [IsScalarTower ℚ ℝ Q]
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def homogeneousQuotientGradedPolynomial (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  map (((basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k).comp S).restrictScalars ℚ) p

theorem homogeneousQuotientGradedPolynomial_coefficient (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (α : σ →₀ ℕ) :
    coefficients (F.homogeneousQuotientGradedPolynomial b ω hF k S p) α =
      basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
        (S (coefficients p α)) := by
  rw [homogeneousQuotientGradedPolynomial, coefficients_map]
  rfl

theorem homogeneousQuotientGradedPolynomial_eval (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (t : σ → ℝ) :
    eval₂ t (F.homogeneousQuotientGradedPolynomial b ω hF k S p) =
      basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
        (S (eval₂ t p)) := by
  exact eval₂_map _ t p

theorem homogeneousQuotientGradedPolynomial_graded (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (hhom : ∀ α, Finsupp.weight w α ≠ k → coefficients p α = 0) :
    F.homogeneousQuotientGradedPolynomial b ω hF k S p ∈
      gradedPolynomialSubmodule ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w := by
  apply homogeneous_mem_gradedPolynomialSubmodule _ _ _ k
  · intro α hα
    rw [F.homogeneousQuotientGradedPolynomial_coefficient, hhom α hα, map_zero, map_zero]
  · intro α
    rw [F.homogeneousQuotientGradedPolynomial_coefficient]
    exact basisCoordinateProjection_idempotent _ _ _

noncomputable def homogeneousQuotientSymbolLift (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q) :
    F.RealPolynomialSymbol w :=
  F.realSymbolOfGradedPolynomial b ω hF w
    (F.homogeneousQuotientGradedPolynomial b ω hF k S p)

theorem homogeneousQuotientSymbolLift_coordinate (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (z : SymbolBasisIndex w ω) :
    ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
      (F.homogeneousQuotientSymbolLift b ω hF w k S p) z =
      if ω z.val.2 = k then
        ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
          (S (coefficients p z.val.1)) z.val.2 else 0 := by
  rw [homogeneousQuotientSymbolLift, F.realSymbolOfGradedPolynomial_coordinate,
    F.homogeneousQuotientGradedPolynomial_coefficient, basisGradeProjection_repr]

theorem realGradedSymbolPolynomial_homogeneousQuotientSymbolLift (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (hhom : ∀ α, Finsupp.weight w α ≠ k → coefficients p α = 0) :
    F.realGradedSymbolPolynomial b ω hF w
        (F.homogeneousQuotientSymbolLift b ω hF w k S p) =
      F.homogeneousQuotientGradedPolynomial b ω hF k S p := by
  exact F.realGradedSymbolPolynomial_ofGradedPolynomial b ω hF w _
    (F.homogeneousQuotientGradedPolynomial_graded b ω hF w k S p hhom)

theorem homogeneousQuotientSymbolLift_eval (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (hhom : ∀ α, Finsupp.weight w α ≠ k → coefficients p α = 0) (t : σ → ℝ) :
    eval₂ t (F.realGradedSymbolPolynomial b ω hF w
      (F.homogeneousQuotientSymbolLift b ω hF w k S p)) =
      basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
        (S (eval₂ t p)) := by
  rw [F.realGradedSymbolPolynomial_homogeneousQuotientSymbolLift b ω hF w k S p hhom]
  exact F.homogeneousQuotientGradedPolynomial_eval b ω hF k S p t

theorem homogeneousQuotientSymbolLift_pure (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q) :
    basisGradeProjection ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ)
      (fun z => ω z.val.2) k (F.homogeneousQuotientSymbolLift b ω hF w k S p) =
      F.homogeneousQuotientSymbolLift b ω hF w k S p := by
  apply ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr.injective
  ext z
  rw [basisGradeProjection_repr, F.homogeneousQuotientSymbolLift_coordinate]
  split_ifs <;> rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators TensorProduct

theorem linearMap_abs_repr_le {V W ι κ : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] [Fintype ι]
    (b : Basis ι ℝ V) (c : Basis κ ℝ W) (S : V →ₗ[ℝ] W)
    {A B : ℝ} (hA : 0 ≤ A)
    (hS : ∀ i j, |c.repr (S (b j)) i| ≤ B)
    (x : V) (hx : ∀ j, |b.repr x j| ≤ A) (i : κ) :
    |c.repr (S x) i| ≤ (Fintype.card ι : ℝ) * B * A := by
  classical
  have he : c.repr (S x) i = ∑ j, b.repr x j * c.repr (S (b j)) i := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [he]
  calc
    |∑ j, b.repr x j * c.repr (S (b j)) i| ≤
        ∑ j, |b.repr x j * c.repr (S (b j)) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : ι, A * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hx j) (hS i j) (abs_nonneg _) hA
    _ = _ := by simp; ring

namespace VectorPolynomial

theorem weightedHomogeneousPart_coordinateBound {σ ι V : Type*}
    [AddCommGroup V] [Module ℚ V] [Module ℝ V]
    (b : Basis ι ℝ V) (T : σ → ℝ) (hT : ∀ j, 0 < T j)
    {M : ℝ} (hM : 0 ≤ M) (p : VectorPolynomial σ ℚ V)
    (hp : ∀ α i, |b.repr (coefficients p α) i| ≤ M / monomialScale T α)
    (w : σ → ℕ) (k : ℕ) :
    ∀ α i, |b.repr (coefficients (weightedHomogeneousPart w k p) α) i| ≤
      M / monomialScale T α := by
  intro α i
  rw [coefficients_weightedHomogeneousPart]
  split_ifs
  · exact hp α i
  · simpa using div_nonneg hM (monomialScale_pos T hT α).le

theorem weightedHomogeneousPart_coordinateGrid {σ ι V : Type*}
    [AddCommGroup V] [Module ℚ V] [Module ℝ V]
    (b : Basis ι ℝ V) (p : VectorPolynomial σ ℚ V) (q : ℕ)
    (hp : ∀ α, (fun i => b.repr (coefficients p α) i) ∈ realDenominatorGrid q)
    (w : σ → ℕ) (k : ℕ) :
    ∀ α, (fun i => b.repr (coefficients (weightedHomogeneousPart w k p) α) i) ∈
      realDenominatorGrid q := by
  intro α
  rw [coefficients_weightedHomogeneousPart]
  split_ifs
  · exact hp α
  · refine ⟨0, ?_⟩
    ext i
    simp

variable {σ ι κ V W : Type*} [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V]
  [LieRing W] [LieAlgebra ℚ W] [LieAlgebra ℝ W]

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ ι κ L Q : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  [AddCommGroup Q] [Module ℚ Q] [Module ℝ Q] [IsScalarTower ℚ ℝ Q]
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem homogeneousQuotientGradedPolynomial_coefficientBound [Fintype κ]
    (eQ : Basis κ ℝ Q) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded))
    (p : VectorPolynomial σ ℚ Q) (T : σ → ℝ) (hT : ∀ j, 0 < T j)
    {M B : ℝ} (hM : 0 ≤ M)
    (hS : ∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (S (eQ j)) i| ≤ B)
    (hp : ∀ α j, |eQ.repr (coefficients p α) j| ≤ M / monomialScale T α) :
    CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T
      ((Fintype.card κ : ℝ) * B * M)
      (F.homogeneousQuotientGradedPolynomial b ω hF k S p) := by
  intro α i
  rw [F.homogeneousQuotientGradedPolynomial_coefficient]
  apply (basisCoordinateProjection_abs_repr_le
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) {i | ω i = k}
    (S (coefficients p α)) i).trans
  exact (linearMap_abs_repr_le eQ _ S
    (div_nonneg hM (monomialScale_pos T hT α).le) hS
    (coefficients p α) (hp α) i).trans_eq (by ring)

theorem homogeneousQuotientGradedPolynomial_coefficientGrid [Fintype κ] [Fintype ι]
    (eQ : Basis κ ℝ Q) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded))
    (p : VectorPolynomial σ ℚ Q) (qS qP : ℕ)
    (hS : ∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (S (eQ j)) i) ∈ realDenominatorGrid qS)
    (hp : ∀ α, (fun j => eQ.repr (coefficients p α) j) ∈ realDenominatorGrid qP) :
    CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) (qS * qP)
      (F.homogeneousQuotientGradedPolynomial b ω hF k S p) := by
  intro α
  rw [F.homogeneousQuotientGradedPolynomial_coefficient]
  apply basisCoordinateProjection_real_grid _ {i | ω i = k}
  have h := linear_lift_grid_of_coefficients
    ((((F.associatedGradedBasis b ω hF).baseChange ℝ).equivFun.toLinearMap).comp S)
    eQ (fun j => eQ.repr (coefficients p α) j) qP qS (hp α) hS
  simpa only [Basis.sum_repr, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Basis.equivFun_apply] using h

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace VectorPolynomial

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ ι η L Q : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    [AddCommGroup Q] [Module ℚ Q] [Module ℝ Q] [IsScalarTower ℚ ℝ Q]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolGradeQuotientSplitting
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem realifyFunctional_eq_sum_basis {V ι : Type*} [AddCommGroup V] [Module ℚ V]
    [Fintype ι] (b : Basis ι ℚ V) (θ : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional θ x = ∑ i, (b.baseChange ℝ).repr x i * (θ (b i) : ℝ) := by
  classical
  calc
    realifyFunctional θ x = realifyFunctional θ
        (∑ i, (b.baseChange ℝ).repr x i • (b.baseChange ℝ) i) :=
      congrArg (realifyFunctional θ) ((b.baseChange ℝ).sum_repr x).symm
    _ = _ := by
      simp only [map_sum, map_smul, Basis.baseChange_apply, realifyFunctional_tmul,
        one_mul, smul_eq_mul]

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def scalarSymbolPolynomial (θ : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (g : F.RealPolynomialSymbolGroup w) : MvPolynomial σ ℝ :=
  coordinate (realifyFunctional θ).toAddMonoidHom
    (F.realGradedSymbolPolynomial b ω hF w g.coord)

@[simp] theorem coeff_scalarSymbolPolynomial (θ : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (g : F.RealPolynomialSymbolGroup w) (α : σ →₀ ℕ) :
    (F.scalarSymbolPolynomial b ω hF w θ g).coeff α =
      realifyFunctional θ
        (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) := by
  simp only [scalarSymbolPolynomial, coeff_coordinate, LinearMap.toAddMonoidHom_coe]

theorem realGradedSymbolPolynomial_slow_coordinates (T : σ → ℝ)
    (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hF w T M g)
    (α : σ →₀ ℕ) (i : ι) :
    |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) i| ≤
      M / monomialScale T α := by
  by_cases h : Finsupp.weight w α = ω i
  · have hc := F.realGradedSymbolPolynomial_coordinate b ω hF w g.coord ⟨(α, i), h⟩
    exact (congrArg abs hc).le.trans (hg ⟨(α, i), h⟩)
  · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w g.coord α i h, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem scalarSymbolPolynomial_slow_coefficients [Fintype ι]
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M H : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hθ : ∀ i, |(θ (F.associatedGradedBasis b ω hF i) : ℝ)| ≤ H)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hF w T M g)
    (α : σ →₀ ℕ) :
    |(F.scalarSymbolPolynomial b ω hF w θ g).coeff α| ≤
      (Fintype.card ι : ℝ) * H * M / monomialScale T α := by
  classical
  rw [F.coeff_scalarSymbolPolynomial, realifyFunctional_eq_sum_basis (F.associatedGradedBasis b ω hF)]
  calc
    _ ≤ ∑ i, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) i *
          (θ (F.associatedGradedBasis b ω hF i) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, (M / monomialScale T α) * H := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hθ i) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right
          (F.realGradedSymbolPolynomial_slow_coordinates b ω hF w T hT hM g hg α i) hH)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem realGradedSymbolPolynomial_rational_coordinates [Fintype ι] (m : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w m g)
    (α : σ →₀ ℕ) :
    ((F.associatedGradedBasis b ω hF).baseChange ℝ).equivFun
      (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α)
        ∈ realDenominatorGrid m := by
  classical
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun i => if h : Finsupp.weight w α = ω i then a ⟨(α, i), h⟩ else 0, ?_⟩
  funext i
  change ((if h : Finsupp.weight w α = ω i then a ⟨(α, i), h⟩ else 0 : ℤ) : ℝ) =
    (m : ℝ) * ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) i
  by_cases h : Finsupp.weight w α = ω i
  · rw [dif_pos h, F.realGradedSymbolPolynomial_coordinate b ω hF w g.coord ⟨(α, i), h⟩]
    exact congrFun ha ⟨(α, i), h⟩
  · rw [dif_neg h, Int.cast_zero,
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w g.coord α i h, mul_zero]

theorem scalarSymbolPolynomial_rational_coefficients [Fintype ι]
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (m : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w m g) :
    realPolynomialCoefficientGrid
      (matrixDenominator (fun (_ : Unit) i => θ (F.associatedGradedBasis b ω hF i)) * m)
      (F.scalarSymbolPolynomial b ω hF w θ g) := by
  classical
  have h : ∀ α, ∃ z : ℤ,
      ((matrixDenominator (fun (_ : Unit) i => θ (F.associatedGradedBasis b ω hF i)) * m : ℕ) : ℝ) *
        (F.scalarSymbolPolynomial b ω hF w θ g).coeff α = (z : ℝ) := by
    intro α
    rw [F.coeff_scalarSymbolPolynomial]
    exact realifyFunctional_denominator_grid (F.associatedGradedBasis b ω hF) θ m _
      (F.realGradedSymbolPolynomial_rational_coordinates b ω hF w m g hg α)
  choose z hz using h
  exact ⟨z, funext (fun α => (hz α).symm)⟩

theorem scalarSymbolPolynomial_slow_coefficients_of_height [Fintype ι]
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) {H : ℕ}
    (hθ : ∀ i, RationalHeightLE (θ (F.associatedGradedBasis b ω hF i)) H)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hF w T M g)
    (α : σ →₀ ℕ) :
    |(F.scalarSymbolPolynomial b ω hF w θ g).coeff α| ≤
      (Fintype.card ι : ℝ) * H * M / monomialScale T α :=
  F.scalarSymbolPolynomial_slow_coefficients b ω hF w θ T hT hM (Nat.cast_nonneg H)
    (fun i => (hθ i).abs_real_le) g hg α

theorem scalarSymbolPolynomial_exists_coefficient_grid [Fintype ι]
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) {H : ℕ}
    (hθ : ∀ i, RationalHeightLE (θ (F.associatedGradedBasis b ω hF i)) H)
    (m : ℕ) (hm : 0 < m) (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolRationalGrid b ω hF w m g) :
    ∃ q : ℕ, 0 < q ∧ q ≤ H ^ Fintype.card ι * m ∧
      realPolynomialCoefficientGrid q (F.scalarSymbolPolynomial b ω hF w θ g) := by
  refine ⟨_, Nat.mul_pos (scalarFunctionalDenominator_pos (F.associatedGradedBasis b ω hF) θ) hm,
    Nat.mul_le_mul_right m (scalarFunctionalDenominator_le (F.associatedGradedBasis b ω hF) θ hθ), ?_⟩
  exact F.scalarSymbolPolynomial_rational_coefficients b ω hF w θ m g hg

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem scalarSymbolPolynomial_mul (θ : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (hθ : ∀ x y : F.AssociatedGraded, θ ⁅x, y⁆ = 0) (hs : 1 ≤ s)
    (x y : F.RealPolynomialSymbolGroup w) :
    F.scalarSymbolPolynomial b ω hF w θ (x * y) =
      F.scalarSymbolPolynomial b ω hF w θ x + F.scalarSymbolPolynomial b ω hF w θ y := by
  apply MvPolynomial.funext
  intro u
  simp only [scalarSymbolPolynomial, MvPolynomial.eval_add, ← coordinate_eval₂,
    NilpotentLieBCHGroup.coord_mul, map_lieBCH]
  have he := map_lieBCH (eval₂Lie (R := ℚ) (S := ℝ) u) s
    (F.realGradedSymbolPolynomial b ω hF w x.coord)
    (F.realGradedSymbolPolynomial b ω hF w y.coord)
  rw [eval₂Lie_apply] at he
  rw [he]
  exact realifyFunctional_lieBCH θ hθ hs _ _

theorem scalarSymbolPolynomial_eq_zero_of_fast
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hθ : ∀ x ∈ W, θ x = 0) (P : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W)) :
    F.scalarSymbolPolynomial b ω hF w θ P = 0 := by
  have hle : W.toSubmodule ≤ LinearMap.ker θ := hθ
  ext α
  rw [F.coeff_scalarSymbolPolynomial, MvPolynomial.coeff_zero]
  apply (mem_realified_frequency_kernel_iff θ _).mp
  apply Submodule.baseChange_mono ℝ hle
  exact (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients b ω hF w W P.coord).mp hP α

theorem scalarSymbolPolynomial_approximation_of_factorization [Fintype ι]
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (hθlie : ∀ x y : F.AssociatedGraded, θ ⁅x, y⁆ = 0) (hs : 1 ≤ s)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (R M : ℝ) (hM : 0 ≤ M)
    {H m : ℕ} (hm : 0 < m)
    (hθH : ∀ i, RationalHeightLE (θ (F.associatedGradedBasis b ω hF i)) H)
    (hden : ((H ^ Fintype.card ι * m : ℕ) : ℝ) ≤ R)
    (hslow : (Fintype.card ι : ℝ) * H * M ≤ R)
    (E P Q X : F.RealPolynomialSymbolGroup w) (hprod : E * P * Q = X)
    (hE : F.SymbolSlowBound b ω hF w T M E)
    (hQ : F.SymbolRationalGrid b ω hF w m Q)
    (W : LieSubalgebra ℚ F.AssociatedGraded) (hθW : ∀ x ∈ W, θ x = 0)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W)) :
    PolynomialRationalApproximation T R (F.scalarSymbolPolynomial b ω hF w θ X) := by
  have hsplit : F.scalarSymbolPolynomial b ω hF w θ X =
      F.scalarSymbolPolynomial b ω hF w θ E + F.scalarSymbolPolynomial b ω hF w θ Q := by
    rw [← hprod, F.scalarSymbolPolynomial_mul b ω hF w θ hθlie hs,
      F.scalarSymbolPolynomial_mul b ω hF w θ hθlie hs,
      F.scalarSymbolPolynomial_eq_zero_of_fast b ω hF w θ W hθW P hP, add_zero]
  obtain ⟨q, hq, hqbound, hgrid⟩ :=
    F.scalarSymbolPolynomial_exists_coefficient_grid b ω hF w θ hθH m hm Q hQ
  obtain ⟨Z, hZ⟩ := (realPolynomialCoefficientGrid_iff q _).mp hgrid
  refine ⟨q, hq, (Nat.cast_le.mpr hqbound).trans hden, Z, ?_⟩
  intro α
  have hz := congrArg (fun polynomial => polynomial.coeff α) hZ
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul] at hz
  change ((Z.coeff α : ℤ) : ℝ) = (q : ℝ) * (F.scalarSymbolPolynomial b ω hF w θ Q).coeff α at hz
  rw [hsplit, MvPolynomial.coeff_add, hz,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hq.ne'), add_sub_cancel_right]
  exact (F.scalarSymbolPolynomial_slow_coefficients_of_height b ω hF w θ T hT hM
    hθH E hE α).trans (div_le_div_of_nonneg_right hslow (monomialScale_pos T hT α).le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem real_quotient_section_residual
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (U : Submodule ℚ V) (S : (V ⧸ U) →ₗ[ℚ] V)
    (hS : ∀ y, U.mkQ (S y) = y)
    (x : ℝ ⊗[ℚ] V) (a c : ℝ ⊗[ℚ] (V ⧸ U))
    (hquot : U.mkQ.baseChange ℝ x = a + c) :
    x - S.baseChange ℝ a - S.baseChange ℝ c ∈ U.baseChange ℝ := by
  have hcomp : U.mkQ.comp S = LinearMap.id := LinearMap.ext hS
  have hSr (y : ℝ ⊗[ℚ] (V ⧸ U)) :
      U.mkQ.baseChange ℝ (S.baseChange ℝ y) = y := by
    have h := congrArg (fun f => LinearMap.baseChange ℝ f) hcomp
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at h
    exact LinearMap.congr_fun h y
  have hker : U.baseChange ℝ = LinearMap.ker (U.mkQ.baseChange ℝ) := by
    simpa only [Submodule.ker_mkQ] using real_baseChange_ker U.mkQ
  rw [hker]
  change U.mkQ.baseChange ℝ (x - S.baseChange ℝ a - S.baseChange ℝ c) = 0
  rw [map_sub, map_sub, hSr, hSr, hquot]
  abel

theorem real_graded_quotient_section_residual
    {V ι : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (ω : ι → ℕ) (U : Submodule ℚ V)
    (hU : BasisGradedSubmodule b ω U)
    (S : (V ⧸ U) →ₗ[ℚ] V) (hS : ∀ y, U.mkQ (S y) = y)
    (k : ℕ) (x : ℝ ⊗[ℚ] V) (a c : ℝ ⊗[ℚ] (V ⧸ U))
    (hx : basisGradeProjection (b.baseChange ℝ) ω k x = x)
    (hquot : U.mkQ.baseChange ℝ x = a + c) :
    x - basisGradeProjection (b.baseChange ℝ) ω k (S.baseChange ℝ a) -
      basisGradeProjection (b.baseChange ℝ) ω k (S.baseChange ℝ c) ∈ U.baseChange ℝ := by
  have h := hU.baseChange b ω U k _ (real_quotient_section_residual U S hS x a c hquot)
  simpa only [map_sub, hx] using h

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realSymbolGradeEvaluation_quotientLift
    {Q : Type*} [AddCommGroup Q] [Module ℚ Q] [Module ℝ Q] [IsScalarTower ℚ ℝ Q]
    (k : ℕ) (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded))
    (p : VectorPolynomial σ ℚ Q)
    (hp : ∀ α, Finsupp.weight w α ≠ k → coefficients p α = 0) (t : σ → ℝ) :
    F.realSymbolGradeEvaluation b ω hF w k t
      (F.homogeneousQuotientSymbolLift b ω hF w k S p) =
        basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
          (S (eval₂ t p)) := by
  rw [F.realSymbolGradeEvaluation_apply, F.homogeneousQuotientSymbolLift_pure]
  exact F.homogeneousQuotientSymbolLift_eval b ω hF w k S p hp t

theorem restricted_symbol_grade_terminal
    (U : Submodule ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U)
    (x : F.RealPolynomialSymbol w) (t : σ → ℝ) :
    eval₂ t (F.realGradedSymbolPolynomial b ω hF w x) ∈ U.baseChange ℝ ↔
      ∀ j ≤ s, F.realSymbolGradeEvaluation b ω hF w j t x ∈ U.baseChange ℝ := by
  constructor
  · intro hx j _
    rw [F.realSymbolGradeEvaluation_eq_projection]
    exact hU.baseChange (F.associatedGradedBasis b ω hF) ω U j _ hx
  · intro hx
    let y := eval₂ t (F.realGradedSymbolPolynomial b ω hF w x)
    have hfull : basisBelowProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ)
        ω (s + 1) y = y := by
      apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
      ext i
      rw [basisBelowProjection_repr, if_pos (Nat.lt_succ_of_le
        (F.adaptedBasis_weight_le_step b ω hF i))]
    change y ∈ U.baseChange ℝ
    rw [← hfull, basisBelowProjection_eq_sum_grades]
    apply Submodule.sum_mem
    intro j hj
    have h := hx j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    rwa [F.realSymbolGradeEvaluation_eq_projection] at h

theorem restricted_symbol_grade_matching
    (U : Submodule ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U)
    (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)
    (hS : ∀ y, U.mkQ (S y) = y)
    (k : ℕ) (Z E R : F.RealPolynomialSymbolGroup w)
    (K₀ K : Set (σ → ℝ)) (hK : K ⊆ K₀)
    (pS pR : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
    (hpS : ∀ α, Finsupp.weight w α ≠ k → coefficients pS α = 0)
    (hpR : ∀ α, Finsupp.weight w α ≠ k → coefficients pR α = 0)
    (hlower : ∀ t ∈ K₀, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord ∈ U.baseChange ℝ)
    (hquot : ∀ t ∈ K,
      U.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation b ω hF w k t (E⁻¹ * Z * R⁻¹).coord) =
          eval₂ t pS + eval₂ t pR) :
    ∃ A D : F.RealPolynomialSymbolGroup w,
      A.coord = F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ) pS ∧
      D.coord = F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ) pR ∧
      A.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
      D.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
      (E * A) * ((E * A)⁻¹ * Z * (D * R)⁻¹) * (D * R) = Z ∧
      (∀ t, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF w j t ((E * A)⁻¹ * Z * (D * R)⁻¹).coord =
          F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord) ∧
      ∀ t ∈ K, ∀ j ≤ k,
        F.realSymbolGradeEvaluation b ω hF w j t ((E * A)⁻¹ * Z * (D * R)⁻¹).coord ∈
          U.baseChange ℝ := by
  let A : F.RealPolynomialSymbolGroup w :=
    ⟨F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ) pS⟩
  let D : F.RealPolynomialSymbolGroup w :=
    ⟨F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ) pR⟩
  have hlift (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
      F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ) p ∈
        (F.polynomialSymbolFiltration w).realification.layer k := by
    rw [← F.homogeneousQuotientSymbolLift_pure b ω hF w k (S.baseChange ℝ) p]
    exact (F.polynomialSymbolFiltration w).realGradeProjection_mem_layer
      (F.polynomialSymbolBasis b ω hF w) (fun z => ω z.val.2)
      (F.polynomialSymbolFiltration_layer b ω hF w) k _
  have hA : A.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k := hlift pS
  have hD : D.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k := hlift pR
  have hmiddle : (E * A)⁻¹ * Z * (D * R)⁻¹ = A⁻¹ * (E⁻¹ * Z * R⁻¹) * D⁻¹ := by group
  have hbelow (t : σ → ℝ) (j : ℕ) (hj : j < k) :
      F.realSymbolGradeEvaluation b ω hF w j t ((E * A)⁻¹ * Z * (D * R)⁻¹).coord =
        F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord := by
    rw [hmiddle]
    exact F.realSymbolGradeEvaluation_correction_below b ω hF w k t A
      (E⁻¹ * Z * R⁻¹) D hA hD j hj
  refine ⟨A, D, rfl, rfl, hA, hD, by group, hbelow, ?_⟩
  intro t ht j hj
  rcases lt_or_eq_of_le hj with hlt | heq
  · rw [hbelow t j hlt]
    exact hlower t (hK ht) j hlt
  · subst j
    rw [hmiddle, F.realSymbolGradeEvaluation_current_correction b ω hF w k t A
      (E⁻¹ * Z * R⁻¹) D hA hD]
    have hevalA : F.realSymbolGradeEvaluation b ω hF w k t A.coord =
        basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
          (S.baseChange ℝ (eval₂ t pS)) := by
      dsimp only [A]
      apply F.realSymbolGradeEvaluation_quotientLift
      exact hpS
    have hevalD : F.realSymbolGradeEvaluation b ω hF w k t D.coord =
        basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
          (S.baseChange ℝ (eval₂ t pR)) := by
      dsimp only [D]
      apply F.realSymbolGradeEvaluation_quotientLift
      exact hpR
    rw [hevalA, hevalD]
    exact real_graded_quotient_section_residual (F.associatedGradedBasis b ω hF) ω U hU S hS k
      _ (eval₂ t pS) (eval₂ t pR)
      (F.realSymbolGradeEvaluation_homogeneous b ω hF w k t _) (hquot t ht)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realSymbolGradeQuotientPolynomial
    (U : Submodule ℚ F.AssociatedGraded) (k : ℕ) (x : F.RealPolynomialSymbol w) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)) :=
  VectorPolynomial.map ((U.mkQ.baseChange ℝ).restrictScalars ℚ)
    (F.realGradedSymbolPolynomial b ω hF w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ)
        (fun z => ω z.val.2) k x))

theorem realSymbolGradeQuotientPolynomial_eval
    (U : Submodule ℚ F.AssociatedGraded) (k : ℕ)
    (x : F.RealPolynomialSymbol w) (t : σ → ℝ) :
    eval₂ t (F.realSymbolGradeQuotientPolynomial b ω hF w U k x) =
      U.mkQ.baseChange ℝ (F.realSymbolGradeEvaluation b ω hF w k t x) := by
  exact eval₂_map _ t _

theorem realSymbolGradeQuotientPolynomial_homogeneous
    (U : Submodule ℚ F.AssociatedGraded) (k : ℕ)
    (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) (hα : Finsupp.weight w α ≠ k) :
    coefficients (F.realSymbolGradeQuotientPolynomial b ω hF w U k x) α = 0 := by
  rw [realSymbolGradeQuotientPolynomial, coefficients_map,
    F.realGradedSymbolPolynomial_gradeProjection_homogeneous b ω hF w k x α hα, map_zero]

theorem restricted_symbol_major_grade_step
    (U : Submodule ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U)
    (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)
    (hS : ∀ y, U.mkQ (S y) = y)
    (k : ℕ) (Z E R : F.RealPolynomialSymbolGroup w)
    (K₀ K : Set (σ → ℝ)) (hK : K ⊆ K₀)
    (hdilate : ∀ t ∈ K, ∀ r : ℚ, (fun i => (r : ℝ) ^ w i * t i) ∈ K)
    (pS pR : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
    (hlower : ∀ t ∈ K₀, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord ∈ U.baseChange ℝ)
    (hquot : ∀ t ∈ K,
      U.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation b ω hF w k t (E⁻¹ * Z * R⁻¹).coord) =
          eval₂ t pS + eval₂ t pR) :
    ∃ A D : F.RealPolynomialSymbolGroup w,
      A.coord = F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ)
        (weightedHomogeneousPart w k pS) ∧
      D.coord = F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ)
        (weightedHomogeneousPart w k pR) ∧
      A.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
      D.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
      (E * A) * ((E * A)⁻¹ * Z * (D * R)⁻¹) * (D * R) = Z ∧
      (∀ t, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF w j t ((E * A)⁻¹ * Z * (D * R)⁻¹).coord =
          F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord) ∧
      ∀ t ∈ K, ∀ j ≤ k,
        F.realSymbolGradeEvaluation b ω hF w j t ((E * A)⁻¹ * Z * (D * R)⁻¹).coord ∈
          U.baseChange ℝ := by
  apply F.restricted_symbol_grade_matching b ω hF w U hU S hS k Z E R K₀ K hK
    (weightedHomogeneousPart w k pS) (weightedHomogeneousPart w k pR)
    (weightedHomogeneousPart_homogeneous w k pS)
    (weightedHomogeneousPart_homogeneous w k pR) hlower
  intro t ht
  let p := F.realSymbolGradeQuotientPolynomial b ω hF w U k (E⁻¹ * Z * R⁻¹).coord
  have hp : ∀ α, Finsupp.weight w α ≠ k → coefficients p α = 0 :=
    F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF w U k _
  have heq : ∀ x ∈ K, eval₂ x p = eval₂ x pS + eval₂ x pR := by
    intro x hx
    rw [realSymbolGradeQuotientPolynomial_eval]
    exact hquot x hx
  have h := eval₂_weightedHomogeneousPart_decomposition_on w p pS pR K hdilate k hp heq t ht
  rw [F.realSymbolGradeQuotientPolynomial_eval] at h
  exact h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ)

theorem realGradedSymbolPolynomial_gradeProjection_eq_weightedHomogeneousPart
    (k : ℕ) (x : F.RealPolynomialSymbol w) :
    F.realGradedSymbolPolynomial b ω hF w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ)
        (fun z => ω z.val.2) k x) =
      weightedHomogeneousPart w k (F.realGradedSymbolPolynomial b ω hF w x) := by
  apply coefficients.injective
  ext α
  rw [F.realGradedSymbolPolynomial_gradeProjection_coefficient,
    coefficients_weightedHomogeneousPart]
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [basisGradeProjection_repr]
  by_cases hi : ω i = k
  · rw [if_pos hi]
    by_cases hα : Finsupp.weight w α = k
    · rw [if_pos hα]
    · rw [if_neg hα, map_zero, Finsupp.zero_apply]
      exact F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w x α i
        (by simpa only [hi] using hα)
  · rw [if_neg hi]
    by_cases hα : Finsupp.weight w α = k
    · rw [if_pos hα]
      exact (F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w x α i
        (fun h => hi (h.symm.trans hα))).symm
    · rw [if_neg hα, map_zero, Finsupp.zero_apply]

theorem scalarSymbolPolynomial_weightedComponent_normalized_splitting
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (hθ : ∀ x ∈ W, θ x = 0) (k : ℕ)
    (E P R E₀ R₀ : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W))
    (hE : F.realSymbolGradeQuotientHom w k E₀ = F.realSymbolGradeQuotientHom w k E)
    (hR : F.realSymbolGradeQuotientHom w k R = F.realSymbolGradeQuotientHom w k R₀) :
    MvPolynomial.weightedHomogeneousComponent w k
      (F.scalarSymbolPolynomial b ω hF w θ (E₀⁻¹ * (E * P * R) * R₀⁻¹)) =
      MvPolynomial.weightedHomogeneousComponent w k
        (F.scalarSymbolPolynomial b ω hF w θ (E₀⁻¹ * E)) +
      MvPolynomial.weightedHomogeneousComponent w k
        (F.scalarSymbolPolynomial b ω hF w θ (R * R₀⁻¹)) := by
  have hproj := (F.polynomialSymbolFiltration w).realGradeProjection_normalized_splitting
    (F.polynomialSymbolBasis b ω hF w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hF w) k E P R E₀ R₀ hE hR
  have he := congrArg (fun x => F.realGradedSymbolPolynomial b ω hF w x) hproj
  simp only [map_add,
    F.realGradedSymbolPolynomial_gradeProjection_eq_weightedHomogeneousPart] at he
  have hc := congrArg (coordinate (realifyFunctional θ).toAddMonoidHom) he
  have hcoord_add (p q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
      coordinate (realifyFunctional θ).toAddMonoidHom (p + q) =
        coordinate (realifyFunctional θ).toAddMonoidHom p +
        coordinate (realifyFunctional θ).toAddMonoidHom q := by
    ext α
    simp only [coeff_coordinate, map_add, Finsupp.add_apply, MvPolynomial.coeff_add]
  simp only [hcoord_add, coordinate_weightedHomogeneousPart] at hc
  change MvPolynomial.weightedHomogeneousComponent w k
      (F.scalarSymbolPolynomial b ω hF w θ (E₀⁻¹ * (E * P * R) * R₀⁻¹)) =
      MvPolynomial.weightedHomogeneousComponent w k
        (F.scalarSymbolPolynomial b ω hF w θ (E₀⁻¹ * E)) +
      MvPolynomial.weightedHomogeneousComponent w k
        (F.scalarSymbolPolynomial b ω hF w θ P) +
      MvPolynomial.weightedHomogeneousComponent w k
        (F.scalarSymbolPolynomial b ω hF w θ (R * R₀⁻¹)) at hc
  simpa only [F.scalarSymbolPolynomial_eq_zero_of_fast b ω hF w θ W hθ P hP,
    map_zero, add_zero] using hc

theorem scalarSymbolPolynomial_homogeneous_normalized_splitting
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hθW : ∀ x ∈ W, θ x = 0) (k : ℕ)
    (E P R E₀ R₀ : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      (F.symbolPointwiseSubalgebra b ω hF (fun _ : σ => 1) W))
    (hE : F.realSymbolGradeQuotientHom (fun _ : σ => 1) k E₀ =
      F.realSymbolGradeQuotientHom (fun _ : σ => 1) k E)
    (hR : F.realSymbolGradeQuotientHom (fun _ : σ => 1) k R =
      F.realSymbolGradeQuotientHom (fun _ : σ => 1) k R₀) :
    MvPolynomial.homogeneousComponent k
      (F.scalarSymbolPolynomial b ω hF (fun _ : σ => 1) θ
        (E₀⁻¹ * (E * P * R) * R₀⁻¹)) =
      MvPolynomial.homogeneousComponent k
        (F.scalarSymbolPolynomial b ω hF (fun _ : σ => 1) θ (E₀⁻¹ * E)) +
      MvPolynomial.homogeneousComponent k
        (F.scalarSymbolPolynomial b ω hF (fun _ : σ => 1) θ (R * R₀⁻¹)) :=
  F.scalarSymbolPolynomial_weightedComponent_normalized_splitting b ω hF
    (fun _ : σ => 1) W θ hθW k E P R E₀ R₀ hP hE hR

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RestrictedSymbolGradeIteration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)
  (U : Submodule ℚ F.AssociatedGraded)
  (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)

noncomputable def restrictedMajorCorrection (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    F.RealPolynomialSymbolGroup w :=
  ⟨F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ)
    (weightedHomogeneousPart w k p)⟩

noncomputable def restrictedMajorOuterFactors
    (pS pR : ℕ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    ℕ → F.RealPolynomialSymbolGroup w × F.RealPolynomialSymbolGroup w
  | 0 => (1, 1)
  | n + 1 =>
    let previous := restrictedMajorOuterFactors pS pR n
    (previous.1 * F.restrictedMajorCorrection b ω hF w U S (n + 1) (pS n),
      F.restrictedMajorCorrection b ω hF w U S (n + 1) (pR n) * previous.2)

theorem realSymbolGradeEvaluation_zero (x : F.RealPolynomialSymbol w) (t : σ → ℝ) :
    F.realSymbolGradeEvaluation b ω hF w 0 t x = 0 := by
  have hz : basisGradeProjection ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ)
      (fun z => ω z.val.2) 0 x = 0 := by
    apply ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr.injective
    ext z
    rw [basisGradeProjection_repr, if_neg
      (Nat.ne_of_gt (F.adaptedBasis_weight_pos b ω hF z.val.2)), map_zero, Finsupp.zero_apply]
  rw [F.realSymbolGradeEvaluation_apply, hz, map_zero, map_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousRealSymbolPullback
namespace OAI

section

namespace Erdos3
open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem realChartSubstitute_mem_gradedPolynomialSubmodule
    {σ τ ι V : Type*} [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V]
    [IsScalarTower ℚ ℝ V] (b : Basis ι ℝ V) (ω : ι → ℕ)
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (p : VectorPolynomial σ ℚ V) (hp : p ∈ gradedPolynomialSubmodule b ω w) :
    realChartSubstitute β p ∈ gradedPolynomialSubmodule b ω v := by
  classical
  intro α
  change basisGradeProjection b ω (Finsupp.weight v α)
    (coefficients (realChartSubstitute β p) α) = _
  rw [coefficients_realChartSubstitute, map_sum]
  apply Finset.sum_congr rfl
  intro γ _
  rw [map_smul]
  by_cases h : Finsupp.weight v α = Finsupp.weight w γ
  · rw [h]
    exact congrArg (fun z =>
      (MvPolynomial.aeval β (MvPolynomial.monomial γ (1 : ℝ))).coeff α • z) (hp γ)
  · rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero α h,
      zero_smul, zero_smul]

namespace NilpotentLieFiltration
variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)

noncomputable def realSymbolHomogeneousPullback (x : F.RealPolynomialSymbol w) :
    F.RealPolynomialSymbol v :=
  F.realSymbolOfGradedPolynomial b ω hF v
    (realChartSubstitute β (F.realGradedSymbolPolynomial b ω hF w x))

attribute [local irreducible] realSymbolHomogeneousPullback realSymbolOfGradedPolynomial realChartSubstitute realGradedSymbolPolynomial gradedPolynomialSubmodule

theorem realGradedSymbolPolynomial_homogeneousPullback
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i)) (x : F.RealPolynomialSymbol w) :
    F.realGradedSymbolPolynomial b ω hF v
      (F.realSymbolHomogeneousPullback b ω hF w v β x) =
    realChartSubstitute β (F.realGradedSymbolPolynomial b ω hF w x) := by
  have hp := F.realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule b ω hF w x
  have hsub := realChartSubstitute_mem_gradedPolynomialSubmodule
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w v β hβ
    (F.realGradedSymbolPolynomial b ω hF w x) hp
  rw [realSymbolHomogeneousPullback]
  exact F.realGradedSymbolPolynomial_ofGradedPolynomial b ω hF v
    (realChartSubstitute β (F.realGradedSymbolPolynomial b ω hF w x)) hsub

theorem realSymbolGradeEvaluation_homogeneousPullback
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (x : F.RealPolynomialSymbol w) (j : ℕ) (u : τ → ℝ) :
    F.realSymbolGradeEvaluation b ω hF v j u
      (F.realSymbolHomogeneousPullback b ω hF w v β x) =
    F.realSymbolGradeEvaluation b ω hF w j (fun i => MvPolynomial.eval u (β i)) x := by
  rw [F.realSymbolGradeEvaluation_eq_projection,
    F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
    eval₂_realChartSubstitute, F.realSymbolGradeEvaluation_eq_projection]

theorem homogeneousPullback_quotient_mem_of_restricted_grade_values
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded) (K : Set (σ → ℝ))
    (hK : ∀ u : τ → ℝ, (fun i => MvPolynomial.eval u (β i)) ∈ K)
    (x : F.RealPolynomialSymbol w) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t x ∈ realificationLieSubalgebra U) :
    F.realSymbolGradeQuotientHom v k
      ⟨F.realSymbolHomogeneousPullback b ω hF w v β x⟩ ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot v)
        (F.symbolPointwiseSubalgebra b ω hF v U)).map (F.realSymbolGradeQuotientHom v k) := by
  exact F.realSymbolGradeQuotient_mem_of_restricted_path b ω hF w v U K β hK x
    ⟨F.realSymbolHomogeneousPullback b ω hF w v β x⟩ k hx
    (fun u j _ => F.realSymbolGradeEvaluation_homogeneousPullback b ω hF w v β hβ x j u)

noncomputable def realSymbolHomogeneousPullbackLie
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i)) :
    F.RealPolynomialSymbol w →ₗ⁅ℚ⁆ F.RealPolynomialSymbol v where
  toFun := F.realSymbolHomogeneousPullback b ω hF w v β
  map_add' x y := by
    apply F.realGradedSymbolPolynomial_injective b ω hF v
    simp only [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
      map_add]
  map_smul' r x := by
    apply F.realGradedSymbolPolynomial_injective b ω hF v
    simp only [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
      map_smul, RingHom.id_apply]
  map_lie' {x y} := by
    apply F.realGradedSymbolPolynomial_injective b ω hF v
    simp only [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
      LieHom.map_lie, realChartSubstitute_lie]

noncomputable def realSymbolHomogeneousPullbackHom
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i)) :
    F.RealPolynomialSymbolGroup w →* F.RealPolynomialSymbolGroup v :=
  NilpotentLieBCHGroup.map (F.realSymbolHomogeneousPullbackLie b ω hF w v β hβ)

@[simp] theorem realSymbolHomogeneousPullbackHom_coord
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (x : F.RealPolynomialSymbolGroup w) :
    (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ x).coord =
      F.realSymbolHomogeneousPullback b ω hF w v β x.coord := rfl

theorem homogeneousPullback_residual_quotient_mem
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded) (K : Set (σ → ℝ))
    (hK : ∀ u : τ → ℝ, (fun i => MvPolynomial.eval u (β i)) ∈ K)
    (E Z R : F.RealPolynomialSymbolGroup w) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord ∈
        realificationLieSubalgebra U) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
    F.realSymbolGradeQuotientHom v k ((pull E)⁻¹ * pull Z * (pull R)⁻¹) ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot v)
        (F.symbolPointwiseSubalgebra b ω hF v U)).map (F.realSymbolGradeQuotientHom v k) := by
  dsimp only
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul]
  exact F.homogeneousPullback_quotient_mem_of_restricted_grade_values
    b ω hF w v β hβ U K hK (E⁻¹ * Z * R⁻¹).coord k hx

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerHomogeneousSymbolPullbackGrid
namespace OAI

section

namespace Erdos3
open Module _root_.MvPolynomial
open scoped TensorProduct

namespace VectorPolynomial

variable {σ τ ι V : Type*} [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V]
  [IsScalarTower ℚ ℝ V]

theorem coordinate_realChartSubstitute_for_grid
    (A : σ → MvPolynomial τ ℝ) (f : V →ₗ[ℝ] ℝ)
    (P : VectorPolynomial σ ℚ V) :
    coordinate f.toAddMonoidHom (realChartSubstitute A P) =
      aeval A (coordinate f.toAddMonoidHom P) := by
  apply MvPolynomial.funext
  intro u
  rw [← coordinate_eval₂, eval₂_realChartSubstitute, coordinate_eval₂]
  exact (MvPolynomial.comp_aeval_apply A (MvPolynomial.aeval u) _).symm

omit [IsScalarTower ℚ ℝ V] in
theorem coefficientGrid_iff_coordinate (b : Basis ι ℝ V) (q : ℕ)
    (P : VectorPolynomial σ ℚ V) :
    CoefficientGrid b q P ↔
      ∀ i, realPolynomialCoefficientGrid q (coordinate (b.coord i).toAddMonoidHom P) := by
  constructor
  · intro h i
    choose z hz using h
    refine ⟨fun α => z α i, funext fun α => ?_⟩
    simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe, Basis.coord_apply,
      Pi.smul_apply, smul_eq_mul]
      using congrFun (hz α) i
  · intro h α
    choose z hz using h
    refine ⟨fun i => z i α, funext fun i => ?_⟩
    simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe, Basis.coord_apply,
      Pi.smul_apply, smul_eq_mul]
      using congrFun (hz i) α

theorem CoefficientGrid.realChartSubstitute_integral
    (b : Basis ι ℝ V) (q : ℕ) (P : VectorPolynomial σ ℚ V)
    (hP : CoefficientGrid b q P) (A : σ → MvPolynomial τ ℝ)
    (hA : ∀ i, realPolynomialCoefficientGrid 1 (A i)) :
    CoefficientGrid b q (realChartSubstitute A P) := by
  rw [coefficientGrid_iff_coordinate]
  intro i
  rw [coordinate_realChartSubstitute_for_grid]
  exact realPolynomialCoefficientGrid_aeval_integral
    (coordinate (b.coord i).toAddMonoidHom P) A q
    ((coefficientGrid_iff_coordinate b q P).mp hP i) hA

end VectorPolynomial

namespace NilpotentLieFiltration
open VectorPolynomial
variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (v : τ → ℕ)

theorem symbolRationalGrid_homogeneousPullback_of_coefficientGrid
    (A : σ → MvPolynomial τ ℝ)
    (hA : ∀ i, (A i).IsWeightedHomogeneous v (w i))
    (hAZ : ∀ i, realPolynomialCoefficientGrid 1 (A i))
    (q : ℕ) (R : F.RealPolynomialSymbolGroup w)
    (hR : CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
      (F.realGradedSymbolPolynomial b ω hF w R.coord)) :
    F.SymbolRationalGrid b ω hF v q
      (F.realSymbolHomogeneousPullbackHom b ω hF w v A hA R) := by
  apply F.symbolRationalGrid_of_gradedPolynomial b ω hF v q
  change CoefficientGrid _ q
    (F.realGradedSymbolPolynomial b ω hF v
      (F.realSymbolHomogeneousPullback b ω hF w v A R.coord))
  rw [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v A hA]
  with_reducible exact (CoefficientGrid.realChartSubstitute_integral
    (V := ℝ ⊗[ℚ] F.AssociatedGraded)
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
    (F.realGradedSymbolPolynomial b ω hF w R.coord) hR A hAZ)

theorem symbolRationalGrid_integerTopPullback_of_coefficientGrid
    (βZ : σ → MvPolynomial τ ℤ) (q : ℕ) (R : F.RealPolynomialSymbolGroup w)
    (hR : CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
      (F.realGradedSymbolPolynomial b ω hF w R.coord)) :
    F.SymbolRationalGrid b ω hF v q
      (F.realSymbolHomogeneousPullbackHom b ω hF w v
        (fun i => weightedHomogeneousComponent v (w i) (MvPolynomial.map (Int.castRingHom ℝ) (βZ i)))
        (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _) R) := by
  apply F.symbolRationalGrid_homogeneousPullback_of_coefficientGrid b ω hF w v _ _ ?_ q R hR
  intro i
  exact realPolynomialCoefficientGrid_weightedHomogeneousComponent v (w i) 1 _
    (realPolynomialCoefficientGrid_intCast (βZ i))

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.HomogeneousRealSymbolPolynomial
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct
attribute [local irreducible] realChartSubstitute realGradedSymbolPolynomial realSymbolHomogeneousPullback realSymbolOfGradedPolynomial realSymbolOfPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)

theorem realSymbolOfPolynomial_homogeneousChart
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    F.realSymbolOfPolynomial b ω hF v (realChartSubstitute β p) =
      F.realSymbolHomogeneousPullback b ω hF w v β
        (F.realSymbolOfPolynomial b ω hF w p) := by
  classical
  apply ((F.polynomialSymbolBasis b ω hF v).baseChange ℝ).repr.injective
  ext z
  rw [F.realSymbolOfPolynomial_coordinate, realSymbolHomogeneousPullback,
    F.realSymbolOfGradedPolynomial_coordinate]
  rw [coefficients_realChartSubstitute, coefficients_realChartSubstitute]
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr_of_eq_on_inter
  · intro γ hγ hγ'
    have hz : coefficients (F.realGradedSymbolPolynomial b ω hF w
        (F.realSymbolOfPolynomial b ω hF w p)) γ = 0 := Finsupp.notMem_support_iff.mp hγ'
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · have he := F.realGradedSymbolPolynomial_coordinate b ω hF w
        (F.realSymbolOfPolynomial b ω hF w p) ⟨(γ, z.val.2), h⟩
      rw [hz, map_zero, Finsupp.zero_apply, F.realSymbolOfPolynomial_coordinate] at he
      rw [← he, mul_zero]
    · rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero _
        (fun he => h (he.symm.trans z.property)), zero_mul]
  · intro γ hγ hγ'
    have hz : coefficients p γ = 0 := Finsupp.notMem_support_iff.mp hγ'
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(γ, z.val.2), h⟩,
        F.realSymbolOfPolynomial_coordinate, hz, map_zero, Finsupp.zero_apply, mul_zero]
    · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w _ γ z.val.2 h, mul_zero]
  · intro γ hγ hγ'
    have hz := z.property
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(γ, z.val.2), h⟩,
        F.realSymbolOfPolynomial_coordinate]
    · have ha : Finsupp.weight v z.val.1 ≠ Finsupp.weight w γ :=
        fun he => h (he.symm.trans hz)
      rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero _ ha]
      simp only [zero_mul]

theorem realPolynomialSymbolHom_homogeneousChart
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (h : (F.realification.adaptedPolynomialFiltration v).Group)
    (hlog : (h.coord : VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute β (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) :
    F.realPolynomialSymbolHom b ω hF v h =
      F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
        (F.realPolynomialSymbolHom b ω hF w g) := by
  apply NilpotentLieBCHGroup.ext
  change F.realSymbolOfPolynomial b ω hF v (h.coord : VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
    F.realSymbolHomogeneousPullback b ω hF w v β
      (F.realSymbolOfPolynomial b ω hF w (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))
  rw [hlog]
  exact F.realSymbolOfPolynomial_homogeneousChart b ω hF w v β hβ _

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedGridNaturalWindow
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

end Erdos3

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
variable (selected : {a // allocatedGridAxis (I := I) U b S.value a} → Prop)
variable [DecidablePred selected]
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q r hcell

noncomputable def allocatedSelectedGridExtension (g : ((a : {a : gridAxes // selected a}) → CoefficientJetAxisRow O (Subtype.val (Subtype.val a))) → ℂ) (N : ℝ) :
    AllocatedFrozenJetRows B U b S O → ℂ :=
  selectedProductExtension selected (fun a z => (laws a z).toReal) g N

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

variable (α : Type*) [Fintype α]

variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedBadProductSpatialBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedBadProductSpatialBudget (m A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ B : ℝ, 0 ≤ B →
      let P := (B + A) ^ A
      let Ps := (B + C) ^ C
      let Q := allocatedFourierLogBudget m P
      P ≤ Ps ∧ 2 * P + 7 * B + 24 ≤ Ps ∧
        allocatedMaskedFourierBudget m P ≤ Ps ∧
        (4 * Q + 2) ^ 4 ≤ Ps ∧ 4 * Q * (4 * Q + 2) ^ 4 + Q ≤ Ps := by
  obtain ⟨a, _, ha⟩ := exists_allocatedMaskedFourierBudget_bound m 2
  let p : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget
    (2 * p + 7 * Polynomial.X + 24 + (p + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro B hB P Ps Q
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hF : 0 ≤ (P + a) ^ a := by positivity
  have htotal : 2 * P + 7 * B + 24 + (P + a) ^ a ≤ Ps := by
    simpa [p, P, Ps, Polynomial.eval₂_pow] using hbound B hB
  have hmask : allocatedMaskedFourierBudget m P ≤ Ps :=
    (ha P hP).1.trans (by linarith)
  have hcomponents := allocatedMaskedFourierBudget_bounds m hP
  exact ⟨by linarith, by linarith, hmask,
    hcomponents.2.2.1.trans hmask, hcomponents.2.2.2.trans hmask⟩

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedSameScaleBadProductBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedModularCanonicalDetectorAllocationBudget (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {P : ℝ} {M nX : ℕ},
      0 ≤ P → (M : ℝ) ≤ P → (nX : ℝ) ≤ P →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
      let budget := (P + A) ^ A
      P ≤ budget ∧ (Jalloc : ℝ) ∈ Set.Icc 0 budget ∧ pnum ∈ Set.Icc 0 budget ∧
        pnum + Jalloc + nX + M + 1 ≤ budget := by
  let c := 2 ^ m * (2 ^ (2 * m) * m.factorial + 1) + 1
  let blocks := ∑ j : Fin m, preparedCommonBlockCount m j
  let X : Polynomial ℕ := Polynomial.X
  let allocation : Polynomial ℕ := Polynomial.C c * (Polynomial.C (m + 1) * X + 11)
  let base : Polynomial ℕ := Polynomial.C ((m + 1) * (m + 3)) +
    X * Polynomial.C m * Polynomial.C blocks + X + Polynomial.C m + 2
  let dimension := base + (Polynomial.C (m + 2) + X * Polynomial.C m * Polynomial.C m) * allocation
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget (dimension + allocation + 3 * X + 1)
  refine ⟨A, hA, ?_⟩
  intro P M nX hP hM hnX Jalloc pnum budget
  let allocBound : ℝ := c * (((m : ℝ) + 1) * P + 11)
  let baseBound : ℝ := ((m : ℝ) + 1) * (m + 3) + P * m * blocks + P + m + 2
  let dimBound : ℝ := baseBound + ((m : ℝ) + 2 + P * m * m) * allocBound
  have halloc0 : 0 ≤ allocBound := by dsimp only [allocBound]; positivity
  have hbase0 : 0 ≤ baseBound := by dsimp only [baseBound]; positivity
  have hdim0 : 0 ≤ dimBound := by dsimp only [dimBound]; positivity
  have halloc : (Jalloc : ℝ) ≤ allocBound := by
    have hlinear := Nat.cast_le (α := ℝ).mpr (modularInitialBlockCount_linear_bound m (nX + m * M))
    change (Jalloc : ℝ) ≤ (c * (nX + m * M + 11) : ℕ) at hlinear
    push_cast at hlinear
    apply hlinear.trans
    dsimp only [allocBound]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg c)
    have hmM := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg m)
    nlinarith
  have hbase : (preparedCommonSamplerDimension m M : ℝ) ≤ baseBound := by
    simp only [preparedCommonSamplerDimension, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
    dsimp only [baseBound, blocks]
    gcongr
  have hdim : pnum ≤ dimBound := by
    dsimp only [pnum]
    rw [enlargedPreparedCommonSamplerDimension_polynomial]
    push_cast
    dsimp only [dimBound]
    apply add_le_add hbase
    exact mul_le_mul (by gcongr) halloc (Nat.cast_nonneg _) (by positivity)
  have hsum : dimBound + allocBound + 3 * P + 1 ≤ budget := by
    simpa [dimension, allocation, base, X, dimBound, allocBound, baseBound,
      Nat.cast_add, Nat.cast_mul] using hbound P hP
  have hallocNonneg : (0 : ℝ) ≤ Jalloc := Nat.cast_nonneg _
  have hnumNonneg : 0 ≤ pnum := Nat.cast_nonneg _
  refine ⟨?_, ⟨hallocNonneg, ?_⟩, ⟨hnumNonneg, ?_⟩, ?_⟩
  all_goals linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedBadProductSourceBudget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {B P0 E V : ℝ} {M nX : ℕ},
      0 ≤ B → (M : ℝ) ≤ B → (nX : ℝ) ≤ B →
      P0 ∈ Set.Icc 0 B → E ∈ Set.Icc 0 B → V ∈ Set.Icc 0 B →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum := enlargedPreparedCommonSamplerDimension m M Jalloc
      let ncoeff := (m + 1) * (pnum + 1) ^ m
      let P := (B + C) ^ C
      B ≤ P ∧ P0 ≤ P ∧ (ncoeff : ℝ) + pnum ≤ P ∧
        allocatedWitnessScaleLog P0 (2 * P0 + 2 * V + 5 * E + 24) ≤ P ∧
        V + 3 * E + 16 ≤ P ∧ ((pnum + 1) * nX : ℕ) ≤ P := by
  obtain ⟨A, _, halloc⟩ := exists_preparedModularCanonicalDetectorAllocationBudget m
  let X : Polynomial ℕ := Polynomial.X
  let dim : Polynomial ℕ := (X + Polynomial.C A) ^ A
  let coeff : Polynomial ℕ := Polynomial.C (m + 1) * (dim + 1) ^ m
  let scale : Polynomial ℕ := (1 + X ^ 2) * (5 * X + 49) + X ^ 2 * (9 * X + 24)
  let total := X + coeff + dim + scale + (4 * X + 16) + (dim + 1) * X
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget total
  refine ⟨C, hC, ?_⟩
  intro B P0 E V M nX hB hM hnX hP0 hE hV Jalloc pnum ncoeff P
  have hP0lo := hP0.1
  have hP0hi := hP0.2
  have hElo := hE.1
  have hEhi := hE.2
  have hVlo := hV.1
  have hVhi := hV.2
  let dimBound : ℝ := (B + A) ^ A
  let coeffBound : ℝ := (m + 1 : ℕ) * (dimBound + 1) ^ m
  let scaleBound : ℝ := (1 + B ^ 2) * (5 * B + 49) + B ^ 2 * (9 * B + 24)
  have hdim0 : 0 ≤ dimBound := by dsimp only [dimBound]; positivity
  have hcoeff0 : 0 ≤ coeffBound := by dsimp only [coeffBound]; positivity
  have hscale0 : 0 ≤ scaleBound := by dsimp only [scaleBound]; positivity
  have hframe0 : 0 ≤ (dimBound + 1) * B := by positivity
  obtain ⟨_, _, hnum, _⟩ := halloc hB hM hnX
  have hnumBound : (pnum : ℝ) ≤ dimBound := hnum.2
  have hcoeff : (ncoeff : ℝ) ≤ coeffBound := by
    dsimp only [ncoeff, coeffBound]
    push_cast
    gcongr
  have hframe : (((pnum + 1) * nX : ℕ) : ℝ) ≤ (dimBound + 1) * B := by
    push_cast
    gcongr
  have hscale : allocatedWitnessScaleLog P0 (2 * P0 + 2 * V + 5 * E + 24) ≤ scaleBound := by
    unfold allocatedWitnessScaleLog allocatedScaleLog
    dsimp only [scaleBound]
    gcongr; linarith
  have htotal : B + coeffBound + dimBound + scaleBound + (4 * B + 16) +
      (dimBound + 1) * B ≤ P := by
    simpa [total, X, coeff, dim, scale, coeffBound, dimBound, scaleBound, P,
      Nat.cast_add, Polynomial.eval₂_pow] using hbound B hB
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem exists_preparedBadProductFinalBudget (m : ℕ) :
    ∃ C1 C2 : ℕ, 2 ≤ C1 ∧ 2 ≤ C2 ∧ ∀ {B P0 E V : ℝ} {M nX : ℕ},
      1 ≤ B → (M : ℝ) ≤ B → (nX : ℝ) ≤ B →
      P0 ∈ Set.Icc 0 B → E ∈ Set.Icc 0 B → V ∈ Set.Icc 0 B →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum := enlargedPreparedCommonSamplerDimension m M Jalloc
      let ncoeff := (m + 1) * (pnum + 1) ^ m
      let P := (B + C1) ^ C1
      let Ps := (B + C2) ^ C2
      let Qf := allocatedFourierLogBudget m P
      1 ≤ P ∧ 1 ≤ Ps ∧ B ≤ P ∧ P0 ≤ P ∧
        (ncoeff : ℝ) + pnum ≤ P ∧
        allocatedWitnessScaleLog P0 (2 * P0 + 2 * V + 5 * E + 24) ≤ P ∧
        V + 3 * E + 16 ≤ P ∧ ((pnum + 1) * nX : ℕ) ≤ Ps ∧
        P ≤ Ps ∧ 2 * P + 2 * V + 5 * E + 24 ≤ Ps ∧
        (4 * Qf + 2) ^ 4 ≤ Ps ∧ 4 * Qf * (4 * Qf + 2) ^ 4 + Qf ≤ Ps := by
  obtain ⟨C1, hC1, hsource⟩ := exists_preparedBadProductSourceBudget m
  obtain ⟨C2, hC2, hspatial⟩ := exists_preparedBadProductSpatialBudget m C1
  refine ⟨C1, C2, hC1, hC2, ?_⟩
  intro B P0 E V M nX hB hM hnX hP0 hE hV Jalloc pnum ncoeff P Ps Qf
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  obtain ⟨hBP, hP0P, hprimitive, hscale, haccuracy, hframe⟩ := hsource hB0 hM hnX hP0 hE hV
  obtain ⟨hPPS, hwidth, _, hfreq, hmass⟩ := hspatial B hB0
  refine ⟨hB.trans hBP, hB.trans (hBP.trans hPPS), hBP, hP0P, hprimitive, hscale,
    haccuracy, hframe.trans hPPS, hPPS, ?_, hfreq, hmass⟩
  have hEhi := hE.2
  have hVhi := hV.2
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCanonicalProjectionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

noncomputable def canonicalProjectionRowCost (m dim : ℕ) : ℕ :=
  Fintype.card (Finset (Fin dim)) *
    ∑ j : Fin m, Fintype.card (BoundedBooleanJet (Fin dim) (j.val + 1))

noncomputable def allocatedCanonicalProjectionLog (m dim : ℕ) (P coverLog : ℝ) : ℝ :=
  allocatedFourierLogBudget m P + coverLog + canonicalProjectionRowCost m dim

theorem exists_allocatedCanonicalProjection_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P coverLog : ℝ, 0 ≤ P → 0 ≤ coverLog →
      allocatedCanonicalProjectionLog m dim P coverLog ≤ (P + coverLog + A) ^ A := by
  obtain ⟨a, ha, hfourier⟩ := exists_allocatedFourierLogBudget_bound m
  let polynomial : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C a) ^ a + Polynomial.X +
      Polynomial.C (canonicalProjectionRowCost m dim)
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget polynomial
  refine ⟨A, hA, ?_⟩
  intro P coverLog hP hcoverLog
  have hpow : (P + a) ^ a ≤ (P + coverLog + a) ^ a := by
    gcongr
    linarith only [hcoverLog]
  have hpoly := hbound (P + coverLog) (add_nonneg hP hcoverLog)
  have hle : allocatedCanonicalProjectionLog m dim P coverLog ≤
      (P + coverLog + a) ^ a + (P + coverLog) + canonicalProjectionRowCost m dim := by
    unfold allocatedCanonicalProjectionLog
    linarith only [hfourier P hP, hpow, hP]
  apply hle.trans
  simpa [polynomial, Polynomial.eval₂_pow] using hpoly

theorem exists_allocatedCanonicalProjection_composed_budget (m dim Acover : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      let coverLog := (P + (dim + 2 : ℕ) + Acover) ^ Acover
      let Aproj := Classical.choose (exists_allocatedCanonicalProjection_budget m dim)
      coverLog ≤ (P + C) ^ C ∧
        (P + coverLog + Aproj) ^ Aproj ≤ (P + C) ^ C := by
  let Aproj := Classical.choose (exists_allocatedCanonicalProjection_budget m dim)
  let coverPolynomial : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C (dim + 2) + Polynomial.C Acover) ^ Acover
  let densityPolynomial : Polynomial ℕ :=
    (Polynomial.X + coverPolynomial + Polynomial.C Aproj) ^ Aproj
  obtain ⟨C, hC, hbound⟩ :=
    exists_natPolynomial_eval_budget (coverPolynomial + densityPolynomial)
  refine ⟨C, hC, ?_⟩
  intro P hP coverLog Aprojection
  have hsum : coverLog + (P + coverLog + Aprojection) ^ Aprojection ≤ (P + C) ^ C := by
    simpa [coverPolynomial, densityPolynomial, Polynomial.eval₂_pow, coverLog,
      Aprojection, Aproj] using hbound P hP
  have hcover : 0 ≤ coverLog := by dsimp [coverLog]; positivity
  have hdensity : 0 ≤ (P + coverLog + Aprojection) ^ Aprojection := by positivity
  exact ⟨(le_add_of_nonneg_right hdensity).trans hsum,
    (le_add_of_nonneg_left hcover).trans hsum⟩

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MarkedPolynomialSectionSlow
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ)

theorem polynomialSlowBound_filteredRealPolynomialSection [Fintype κ]
    (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A B : ℝ} (hA : 0 ≤ A)
    (hB : ∀ i j, |(b.baseChange ℝ).repr (S.baseChange ℝ ((c.baseChange ℝ) j)) i| ≤ B)
    (g : (G.realification.adaptedPolynomialFiltration w).Group)
    (hg : G.PolynomialSlowBound c w T A g) :
    F.PolynomialSlowBound b w T ((Fintype.card κ : ℝ) * B * A)
      (F.filteredRealPolynomialSection G w S hS g) := by
  intro α i
  change |(b.baseChange ℝ).repr (coefficients (map ((S.baseChange ℝ).restrictScalars ℚ)
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M))) α) i| ≤ _
  rw [coefficients_map]
  exact (linearMap_abs_repr_le (c.baseChange ℝ) (b.baseChange ℝ) (S.baseChange ℝ)
    (div_nonneg hA (monomialScale_pos T hT α).le) hB _ (hg α) i).trans
    (le_of_eq (by ring))

theorem section_exponential_budget (a : ℕ) {p n : ℝ} (hp : 0 ≤ p)
    (hnp : n ≤ p) :
    n * Real.exp ((p + 2) ^ a) * Real.exp ((p + 2) ^ a) ≤
      Real.exp ((p + 2) ^ (a + 2)) := by
  have hp1 : 1 ≤ p + 2 := by linarith
  have hq1 : 1 ≤ (p + 2) ^ a := one_le_pow₀ hp1
  have hnexp : n ≤ Real.exp p := hnp.trans (by linarith [Real.add_one_le_exp p])
  have hsmall : p + 2 * (p + 2) ^ a ≤ (p + 2) * (p + 2) ^ a := by
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hq1)]
  have hlarge : (p + 2) * (p + 2) ^ a ≤ (p + 2) ^ (a + 2) := by
    rw [pow_add, pow_two]
    nlinarith [mul_nonneg (show 0 ≤ (p + 2) ^ a by positivity)
      (show 0 ≤ (p + 2) * (p + 2) - (p + 2) by nlinarith)]
  calc
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ a) * Real.exp ((p + 2) ^ a) := by
      gcongr
    _ = Real.exp (p + 2 * (p + 2) ^ a) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (hsmall.trans hlarge)

theorem polynomialSlowBound_filteredRealPolynomialSection_exp [Fintype κ]
    (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (a : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hB : ∀ i j, |(b.baseChange ℝ).repr (S.baseChange ℝ ((c.baseChange ℝ) j)) i| ≤
      Real.exp ((p + 2) ^ a))
    (g : (G.realification.adaptedPolynomialFiltration w).Group)
    (hg : G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ a)) g) :
    F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ (a + 2)))
      (F.filteredRealPolynomialSection G w S hS g) := by
  exact F.polynomialSlowBound_mono b w T hT
    (section_exponential_budget a hp hκ) _
    (F.polynomialSlowBound_filteredRealPolynomialSection G b c w S hS T hT
      (Real.exp_nonneg _) hB g hg)

theorem exists_marked_polynomial_kernel_slow_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {t : ℕ}
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
      (b : Basis ι ℚ L) (c : Basis κ ℚ M) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j),
      (∀ i j, |(b.baseChange ℝ).repr (S.baseChange ℝ ((c.baseChange ℝ) j)) i| ≤
        Real.exp ((p + 2) ^ a)) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∀ (E : (F.realification.adaptedPolynomialFiltration w).Group)
        (EF : (G.realification.adaptedPolynomialFiltration w).Group),
      F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a)) E →
      G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ a)) EF →
      F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C))
        (E * (F.filteredRealPolynomialSection G w S hS EF)⁻¹) ∧
      F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C))
        ((F.filteredRealPolynomialSection G w S hS EF)⁻¹ * E) := by
  obtain ⟨C, hC, hprod⟩ := exists_polynomial_slow_product_bound s (a + 2) 2
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ t F G b c ω hF w hw H p hH hp hι hκ hσ hHp hb
    S hS hB T hT E EF hE hEF
  let V := F.filteredRealPolynomialSection G w S hS EF
  have hV : F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ (a + 2))) V :=
    F.polynomialSlowBound_filteredRealPolynomialSection_exp G b c w S hS T hT a p hp hκ hB EF hEF
  have hVi := (F.polynomialSlowBound_inv_iff b w T _ V).mpr hV
  have hE' : F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ (a + 2))) E :=
    F.polynomialSlowBound_mono b w T hT (Real.exp_le_exp.mpr
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 2) (by omega : a ≤ a + 2))) E hE
  have hleft := hprod F b ω hF w hw H p hH hp hι hσ hHp hb T hT [E, V⁻¹]
    (by simp) (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hE'
      · have heq := List.mem_singleton.mp hr
        simpa only [heq] using hVi)
  have hright := hprod F b ω hF w hw H p hH hp hι hσ hHp hb T hT [V⁻¹, E]
    (by simp) (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hVi
      · have heq := List.mem_singleton.mp hr
        simpa only [heq] using hE')
  exact ⟨by simpa only [List.prod_cons, List.prod_nil, mul_one] using hleft,
    by simpa only [List.prod_cons, List.prod_nil, mul_one] using hright⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedPolynomialPhysicalBadProductSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

noncomputable def preparedBadProductCoefficientExponent (m : ℕ) : ℕ :=
  (exists_preparedBadProductFinalBudget m).choose
noncomputable def preparedBadProductSpatialExponent (m : ℕ) : ℕ :=
  (exists_preparedBadProductFinalBudget m).choose_spec.choose

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S0 : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

variable (Elog Vlog : ℝ) (Q : ℕ)

end Erdos3.VectorPolynomial

end

end OAI

end


