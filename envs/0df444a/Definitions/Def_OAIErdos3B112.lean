-- Prove2me | Definitions.Def_OAIErdos3B112
-- name    : OAIErdos3B112
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T03:35:27.144691+00:00
-- url     : https://prove2.me/theorems/a6497d24-78c9-40c4-a26a-e0d34fc38ff5
-- title:
--   OpenAI Erdős-3 split, definitions bundle 113 of 132
-- statement:
--   Definitions bundle 113 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B111`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 113 available.
--
--   Modules: `OAI.Erdos3.MultidegreeLieFiltration.realComparisonCoefficient_first`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonCoefficient_second`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedCoefficient_ne`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedCoefficient_self`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedLog`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedLog_adapted`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedLog_coefficient`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedLog_coefficient_nonsquarefree`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedLog_eval`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedLog_eval_coefficient`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedOrbit`, `OAI.Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors.middle_values`, `OAI.Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors.noConfusion`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedMap_basis_logHeight`, `OAI.Erdos3.NilpotentLieFiltration.exists_associatedGradedMap_comap_bounded_spanning`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_marked_kernel_normalization`, `OAI.Erdos3.NilpotentLieFiltration.exists_filtered_linear_section`, `OAI.Erdos3.NilpotentLieFiltration.exists_formal_marked_orbit_restoration`, `OAI.Erdos3.NilpotentLieFiltration.exists_fractional_integral_constant_normalization`, `OAI.Erdos3.NilpotentLieFiltration.exists_fractional_integral_polynomial_normalization`, `OAI.Erdos3.NilpotentLieFiltration.exists_frozenMarkedLeftOrbit_exp_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_globalMarkedNativeFactors_of_outer_lifts`, `OAI.Erdos3.NilpotentLieFiltration.exists_marked_kernel_normalized_factors`, `OAI.Erdos3.NilpotentLieFiltration.exists_marked_kernel_rational_grid_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_realPolynomialGroupMap_grid`, `OAI.Erdos3.NilpotentLieFiltration.externalCandidate_stepZero_coord_eq_zero`, `OAI.Erdos3.NilpotentLieFiltration.externalCandidate_stepZero_group_eq_one`, `OAI.Erdos3.NilpotentLieFiltration.filteredRealPolynomialSection_rationalGrid`, `OAI.Erdos3.NilpotentLieFiltration.formal_mark_realEval`, `OAI.Erdos3.NilpotentLieFiltration.frozenMarkedLeft`, `OAI.Erdos3.NilpotentLieFiltration.frozenMarkedLeftOrbit`, `OAI.Erdos3.NilpotentLieFiltration.frozenMarkedLeftOrbit_formal_mark`, `OAI.Erdos3.NilpotentLieFiltration.frozenMarkedLeftOrbit_realEval`, `OAI.Erdos3.NilpotentLieFiltration.frozenMarkedLeftOrbit_realEval_eq_local`, `OAI.Erdos3.NilpotentLieFiltration.frozenMarkedOuter_product_mark_eq`, `OAI.Erdos3.NilpotentLieFiltration.frozenMarkedRight`, `OAI.Erdos3.NilpotentLieFiltration.frozenMarkedRightOrbit`, `OAI.Erdos3.NilpotentLieFiltration.frozenMarkedRightOrbit_formal_mark`, `OAI.Erdos3.NilpotentLieFiltration.frozenMarkedRightOrbit_realEval`, `OAI.Erdos3.NilpotentLieFiltration.frozenMarkedRightOrbit_realEval_eq_local`, `OAI.Erdos3.NilpotentLieFiltration.frozenMarked_factors_mark`, `OAI.Erdos3.NilpotentLieFiltration.gradedImagePointwiseSpanningFamily`, `OAI.Erdos3.NilpotentLieFiltration.gradedImagePointwiseSpanningFamily_controlled`, `OAI.Erdos3.NilpotentLieFiltration.gradedImagePointwiseSpanningFamily_height`, `OAI.Erdos3.NilpotentLieFiltration.gradedImagePointwiseSpanningFamily_span`, `OAI.Erdos3.NilpotentLieFiltration.gradedImagePointwiseSpanning_heightBound`, `OAI.Erdos3.NilpotentLieFiltration.gradedImageSpanningFamily`, `OAI.Erdos3.NilpotentLieFiltration.gradedImageSpanningFamily_logHeight`, `OAI.Erdos3.NilpotentLieFiltration.gradedImageSpanningFamily_span`, `OAI.Erdos3.NilpotentLieFiltration.gradedImage_bounded_spanning`, `OAI.Erdos3.NilpotentLieFiltration.nativeFrozenMarkedOrbitCoordinates_realValue`, `OAI.Erdos3.NilpotentLieFiltration.nativeFrozenMarkedOrbitCoordinates_symm_realEval`, `OAI.Erdos3.NilpotentLieFiltration.native_refiltered_symbol_conditions`, `OAI.Erdos3.NilpotentLieFiltration.ordinaryGradedImagePointwiseSpanning_controlled`, `OAI.Erdos3.NilpotentLieFiltration.ordinaryImagePointwiseBudget`, `OAI.Erdos3.NilpotentLieFiltration.ordinaryImagePointwiseBudget_ge`, `OAI.Erdos3.NilpotentLieFiltration.ordinaryImagePointwiseBudget_height`, `OAI.Erdos3.NilpotentLieFiltration.ordinaryImagePointwiseBudget_source`, `OAI.Erdos3.NilpotentLieFiltration.ordinaryImagePointwiseBudget_target`, `OAI.Erdos3.NilpotentLieFiltration.pointwiseSpanningIndex_card_le`, `OAI.Erdos3.NilpotentLieFiltration.polynomialRationalGrid_iff_coefficients`, `OAI.Erdos3.NilpotentLieFiltration.polynomialRationalGrid_inv`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialGroupMap_slow_exp`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolHom_constant`, `OAI.Erdos3.NilpotentLieFiltration.real_linear_section_rightInverse`, `OAI.Erdos3.NilpotentLieFiltration.real_projected_discrepancy_mem_shifted`, `OAI.Erdos3.NilpotentLieFiltration.sectionCorrectedPolynomial_prescribed_symbol`, `OAI.Erdos3.RationalFilteredNilmanifold.AdaptedMapGeometryData.optionTarget_observable_regularity`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeCyclicRecoverySpec`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeModelEquiv`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeModelEquiv.mapOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeModelEquiv.mapOrbit_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeModelEquiv.realGroupEquiv`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeModelEquiv.real_lattice_le`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeModelEquiv.spaceMap`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeModelEquiv.spaceMap_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeModelEquiv.spaceMap_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeModelEquiv.symm`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeModelEquiv.symm_realGroupEquiv_apply`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeModelEquiv.symm_spaceMap_apply`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeModelEquiv.transport`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeModelEquiv.transport_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeModelEquiv.transport_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeModelEquiv.transport_unit_interval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.observable_freeze_marked_kernel_factors`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.observable_frozenMarked_polynomial_factors`, `OAI.Erdos3.RationalFilteredNilmanifold.RefilteredProductExpansionSpec`, `OAI.Erdos3.RationalFilteredNilmanifold.RefilteredRecoveredExpansionSpec`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_common_native_niltest_model`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_common_variable_dimension_niltest_model`, `OAI.Erdos3.RationalFilteredNilmanifold.externalCandidateOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.externalCandidateOrbit_realEval`, `OAI.Erdos3.RationalFilteredNilmanifold.includedRefilteredOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.includedRefilteredOrbit_log`, `OAI.Erdos3.RationalFilteredNilmanifold.includedRefilteredOrbit_realEval`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeModelEquivOfCoordinates`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeOptionTargetObservableBudget`, `OAI.Erdos3.RationalFilteredNilmanifold.rationalModelEquiv`, `OAI.Erdos3.RationalFilteredNilmanifold.rationalModelEquiv_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.rationalModelEquiv_layer`, `OAI.Erdos3.RationalFilteredNilmanifold.rationalModelEquiv_layer_succ`, `OAI.Erdos3.RationalFilteredNilmanifold.rationalModelEquiv_paddedLayerVector`, `OAI.Erdos3.RationalFilteredNilmanifold.rationalModelEquiv_repr`, `OAI.Erdos3.RationalFilteredNilmanifold.rationalModelGroupEquiv`, `OAI.Erdos3.RationalFilteredNilmanifold.rationalModelGroupEquiv_coordinates`, `OAI.Erdos3.RationalFilteredNilmanifold.rationalModelGroupEquiv_mem_integral_lattice`, `OAI.Erdos3.RationalFilteredNilmanifold.rationalModelGroupEquiv_mem_layer`, `OAI.Erdos3.RationalFilteredNilmanifold.refiltered_mark_realification_commutes`, `OAI.Erdos3.kernel_coordinate_factor_le_exp`, `OAI.Erdos3.kernel_inclusion_denominator_mul_le_exp`, `OAI.Erdos3.kernel_inclusion_height_mul_le_exp`, `OAI.Erdos3.realificationLieEquiv_inverse`, `OAI.Erdos3.sectionCorrectedPolynomial_map`, `OAI.Erdos3.squarefreePolynomialLift`, `OAI.Erdos3.squarefreePolynomialLift_coefficient`, `OAI.Erdos3.squarefreePolynomialLift_coefficient_nonsquarefree`, `OAI.Erdos3.squarefreePolynomialLift_eval`, `_private.Linear.ActualOrdinaryPointwiseSpanning.0.OAI.Erdos3.NilpotentLieFiltration.sectionInput_nonneg`, `_private.Linear.ActualOrdinaryPointwiseSpanning.0.OAI.Erdos3.NilpotentLieFiltration.symbolCount_le_sectionInput`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B118

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolarizedPolynomialOrbit
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]

noncomputable def squarefreePolynomialLift (f : SquarefreeIndex ι → V) : VectorPolynomial ι ℚ V :=
  ∑ a, monomial a.val (f a)

theorem squarefreePolynomialLift_coefficient (f : SquarefreeIndex ι → V) (a : SquarefreeIndex ι) :
    coefficients (squarefreePolynomialLift f) a.val = f a := by
  classical
  simp only [squarefreePolynomialLift, map_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single a]
  · simp only [coefficients_monomial, Finsupp.single_eq_same]
  · intro b _ hb
    rw [coefficients_monomial]
    exact Finsupp.single_eq_of_ne (fun h => hb (Subtype.ext h.symm))
  · simp

theorem squarefreePolynomialLift_coefficient_nonsquarefree (f : SquarefreeIndex ι → V)
    (a : ι →₀ ℕ) (ha : ¬SquarefreeExponent a) : coefficients (squarefreePolynomialLift f) a = 0 := by
  classical
  simp only [squarefreePolynomialLift, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [coefficients_monomial]
  apply Finsupp.single_eq_of_ne
  intro h
  apply ha
  rw [h]
  exact b.property

theorem squarefreePolynomialLift_eval (f : SquarefreeIndex ι → V) (x : ι → ℚ) :
    eval x (squarefreePolynomialLift f) = ∑ a, (a.val.prod fun i n => x i ^ n) • f a := by
  simp only [squarefreePolynomialLift, map_sum, eval_monomial]

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realPolarizedLog (p : F.realification.adaptedLieSubalgebra) :
    VectorPolynomial ι ℚ (ℝ ⊗[ℚ] F.SquarefreeAlgebra π) :=
  squarefreePolynomialLift (F.realPolarizedCoefficient π p)

theorem realPolarizedLog_coefficient (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) :
    coefficients (F.realPolarizedLog π p) a.val = F.realPolarizedCoefficient π p a :=
  squarefreePolynomialLift_coefficient _ a

theorem realPolarizedLog_coefficient_nonsquarefree (p : F.realification.adaptedLieSubalgebra)
    (a : ι →₀ ℕ) (ha : ¬SquarefreeExponent a) :
    coefficients (F.realPolarizedLog π p) a = 0 :=
  squarefreePolynomialLift_coefficient_nonsquarefree _ a ha

theorem realPolarizedLog_adapted (p : F.realification.adaptedLieSubalgebra) :
    (F.squarefreeMultidegreeFiltration π).realification.Adapted (F.realPolarizedLog π p) := by
  intro a
  by_cases ha : SquarefreeExponent a
  · rw [F.realPolarizedLog_coefficient π p ⟨a, ha⟩]
    exact F.realPolarizedCoefficient_mem π p ⟨a, ha⟩
  · rw [F.realPolarizedLog_coefficient_nonsquarefree π p a ha]
    exact Submodule.zero_mem _

theorem realPolarizedLog_eval (p : F.realification.adaptedLieSubalgebra) (x : ι → ℚ) :
    eval x (F.realPolarizedLog π p) =
      ∑ a, (a.val.prod fun i n => x i ^ n) • F.realPolarizedCoefficient π p a :=
  squarefreePolynomialLift_eval _ x

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realPolarizedOrbit (p : F.realification.adaptedLieSubalgebra) :
    (F.squarefreeMultidegreeFiltration π).realification.PolynomialOrbit :=
  (F.squarefreeMultidegreeFiltration π).realification.polynomialOrbitOfLog
    (F.realPolarizedLog π p) (F.realPolarizedLog_adapted π p)

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealPolarizedCoefficientCoordinates
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realPolarizedCoefficient_self (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) (ha : a.val ≠ 0) :
    realSquarefreePolynomialEquiv (F.realSquarefreeInclusion π (F.realPolarizedCoefficient π p a)) a =
      (multidegreeFactorial (blockDegree π a.val) : ℚ) •
        coefficients p.val (blockExponent π a.val) := by
  rw [F.realPolarizedCoefficient_inclusion π p a ha, map_rat_smul, Pi.smul_apply,
    realSquarefreeMonomial_self]

theorem realPolarizedCoefficient_ne (p : F.realification.adaptedLieSubalgebra)
    (a c : SquarefreeIndex ι) (hac : a ≠ c) :
    realSquarefreePolynomialEquiv (F.realSquarefreeInclusion π (F.realPolarizedCoefficient π p a)) c = 0 := by
  by_cases ha : a.val = 0
  · rw [F.realPolarizedCoefficient_zero π p a ha, map_zero, map_zero, Pi.zero_apply]
  · rw [F.realPolarizedCoefficient_inclusion π p a ha, map_rat_smul, Pi.smul_apply,
      realSquarefreeMonomial_ne a c hac, smul_zero]

theorem realPolarizedLog_eval_coefficient (p : F.realification.adaptedLieSubalgebra)
    (x : ι → ℚ) (c : SquarefreeIndex ι) :
    realSquarefreePolynomialEquiv (F.realSquarefreeInclusion π (eval x (F.realPolarizedLog π p))) c =
      (c.val.prod fun i n => x i ^ n) •
        realSquarefreePolynomialEquiv (F.realSquarefreeInclusion π (F.realPolarizedCoefficient π p c)) c := by
  classical
  let C : (ℝ ⊗[ℚ] F.SquarefreeAlgebra π) →ₗ[ℝ] (ℝ ⊗[ℚ] L) := (LinearMap.proj c).comp
    (realSquarefreePolynomialEquiv.toLinearMap.comp (F.realSquarefreeInclusion π))
  change C (eval x (F.realPolarizedLog π p)) = _
  rw [F.realPolarizedLog_eval, map_sum]
  simp only [LinearMap.map_smul_of_tower]
  rw [Finset.sum_eq_single c]
  · rfl
  · intro a _ hac
    have hz : C (F.realPolarizedCoefficient π p a) = 0 := F.realPolarizedCoefficient_ne π p a c hac
    rw [hz, smul_zero]
  · simp

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealComparisonCoefficientProjections
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realComparisonCoefficient_first (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (a : σ →₀ ℕ) :
    realificationLieHom (F.comparisonFirst π) (F.realComparisonCoefficient π p a) =
      coefficients p.val a := by
  by_cases ha : a = 0
  · subst a
    rw [F.realComparisonCoefficient_zero_index, map_zero, hp]
  · rw [realComparisonCoefficient, dif_neg ha, F.realComparisonGraphLift_first]

theorem realComparisonCoefficient_second (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (a : σ →₀ ℕ) :
    F.realSquarefreeInclusion π
        (realificationLieHom (F.comparisonSecond π) (F.realComparisonCoefficient π p a)) =
      (factorialBlockMonomial π (fun i => a i)).baseChange ℝ (coefficients p.val a) := by
  by_cases ha : a = 0
  · subst a
    rw [F.realComparisonCoefficient_zero_index, map_zero, map_zero, hp, map_zero]
  · rw [realComparisonCoefficient, dif_neg ha, F.realComparisonGraphLift_second]

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeModelOrbit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s d)
  (h : D.rationalModelCoordinates = E.rationalModelCoordinates)

noncomputable def rationalModelEquiv : L ≃ₗ⁅ℚ⁆ M :=
  { D.basis.repr.trans E.basis.repr.symm with
    map_lie' {x y} := by
      apply E.basis.repr.injective
      ext k
      change E.basis.repr (E.basis.repr.symm (D.basis.repr ⁅x, y⁆)) k = _
      rw [LinearEquiv.apply_symm_apply, lie_coordinate_formula, lie_coordinate_formula]
      apply Finset.sum_congr rfl
      intro ij _
      have hc : lieStructureConstants D.basis ij.1 ij.2 k =
          lieStructureConstants E.basis ij.1 ij.2 k := congrFun h (.inl (ij.1, ij.2, k))
      change lieStructureConstants D.basis ij.1 ij.2 k * D.basis.repr x ij.1 * D.basis.repr y ij.2 =
        lieStructureConstants E.basis ij.1 ij.2 k *
          E.basis.repr (E.basis.repr.symm (D.basis.repr x)) ij.1 *
          E.basis.repr (E.basis.repr.symm (D.basis.repr y)) ij.2
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hc] }

theorem rationalModelEquiv_repr (x : L) :
    E.basis.repr (D.rationalModelEquiv E h x) = D.basis.repr x :=
  E.basis.repr.apply_symm_apply _

theorem rationalModelEquiv_basis (i : Fin d) :
    D.rationalModelEquiv E h (D.basis i) = E.basis i := by
  apply E.basis.repr.injective
  rw [rationalModelEquiv_repr]
  simp only [Basis.repr_self]

theorem rationalModelEquiv_paddedLayerVector (i : Fin (s + 1)) (k : Fin d) :
    D.rationalModelEquiv E h (D.paddedLayerVector i k) = E.paddedLayerVector i k := by
  apply E.basis.repr.injective
  rw [rationalModelEquiv_repr]
  ext j
  exact congrFun h (.inr (i, k, j))

theorem rationalModelEquiv_layer_succ (i : Fin (s + 1)) :
    (D.filtration.layer (i.val + 1)).map (D.rationalModelEquiv E h).toLinearEquiv.toLinearMap =
      E.filtration.layer (i.val + 1) := by
  rw [← D.paddedLayerVector_span i, ← E.paddedLayerVector_span i,
    Submodule.map_span, ← Set.range_comp]
  congr 2
  funext k
  exact D.rationalModelEquiv_paddedLayerVector E h i k

theorem rationalModelEquiv_layer (n : ℕ) :
    (D.filtration.layer n).map (D.rationalModelEquiv E h).toLinearEquiv.toLinearMap =
      E.filtration.layer n := by
  by_cases hn : n = 0
  · subst n
    have hD : D.filtration.layer 0 = ⊤ :=
      top_unique (D.filtration.one_eq_top ▸ D.filtration.antitone (by omega : 0 ≤ 1))
    have hE : E.filtration.layer 0 = ⊤ :=
      top_unique (E.filtration.one_eq_top ▸ E.filtration.antitone (by omega : 0 ≤ 1))
    rw [hD, hE]
    rw [Submodule.map_top]
    apply LinearMap.range_eq_top.mpr
    exact (D.rationalModelEquiv E h).surjective
  · by_cases hns : n ≤ s + 1
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
        D.rationalModelEquiv_layer_succ E h ⟨n - 1, by omega⟩
    · have hD : D.filtration.layer n = ⊥ :=
        bot_unique ((D.filtration.antitone (by omega : s + 1 ≤ n)).trans D.filtration.terminal.le)
      have hE : E.filtration.layer n = ⊥ :=
        bot_unique ((E.filtration.antitone (by omega : s + 1 ≤ n)).trans E.filtration.terminal.le)
      rw [hD, hE, Submodule.map_bot]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s d)
  (h : D.rationalModelCoordinates = E.rationalModelCoordinates)

noncomputable def rationalModelGroupEquiv : D.filtration.Group ≃* E.filtration.Group :=
  { NilpotentLieBCHGroup.map (D.rationalModelEquiv E h).toLieHom with
    invFun := fun g => ⟨(D.rationalModelEquiv E h).symm g.coord⟩
    left_inv g := by
      apply NilpotentLieBCHGroup.ext
      exact (D.rationalModelEquiv E h).symm_apply_apply g.coord
    right_inv g := by
      apply NilpotentLieBCHGroup.ext
      exact (D.rationalModelEquiv E h).apply_symm_apply g.coord }

theorem rationalModelGroupEquiv_coordinates (g : D.filtration.Group) :
    E.basis.equivFun (D.rationalModelGroupEquiv E h g).coord = D.basis.equivFun g.coord := by
  funext k
  exact congrArg (fun v => v k) (D.rationalModelEquiv_repr E h g.coord)

theorem rationalModelGroupEquiv_mem_layer (n : ℕ) (g : D.filtration.Group) :
    D.rationalModelGroupEquiv E h g ∈ E.filtration.subgroup n ↔ g ∈ D.filtration.subgroup n := by
  change D.rationalModelEquiv E h g.coord ∈ E.filtration.layer n ↔ g.coord ∈ D.filtration.layer n
  rw [← D.rationalModelEquiv_layer E h n]
  constructor
  · rintro ⟨x, hx, heq⟩
    have hxg : x = g.coord := (D.rationalModelEquiv E h).injective heq
    change x ∈ D.filtration.layer n at hx
    exact hxg ▸ hx
  · intro hx
    exact ⟨g.coord, hx, rfl⟩

theorem rationalModelGroupEquiv_mem_integral_lattice
    (Λ : Subgroup D.filtration.Group) (Γ : Subgroup E.filtration.Group) (B : ℕ)
    (hΛ : bchSubgroupCoordinates D.basis Λ = scaledIntegerGrid B)
    (hΓ : bchSubgroupCoordinates E.basis Γ = scaledIntegerGrid B) (g : D.filtration.Group) :
    D.rationalModelGroupEquiv E h g ∈ Γ ↔ g ∈ Λ := by
  rw [← bchSubgroupCoordinates_repr E.basis Γ (D.rationalModelGroupEquiv E h g),
    ← bchSubgroupCoordinates_repr D.basis Λ g, hΛ, hΓ,
    rationalModelGroupEquiv_coordinates]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s d)

structure NativeModelEquiv where
  toLieEquiv : L ≃ₗ⁅ℚ⁆ M
  map_basis : ∀ i, toLieEquiv (D.basis i) = E.basis i
  mem_layer : ∀ n x, toLieEquiv x ∈ E.filtration.layer n ↔ x ∈ D.filtration.layer n
  mem_lattice : ∀ g : D.filtration.Group,
    NilpotentLieBCHGroup.map toLieEquiv.toLieHom g ∈ E.lattice ↔ g ∈ D.lattice

namespace NativeModelEquiv

variable {D E} (e : NativeModelEquiv D E)

noncomputable def symm : NativeModelEquiv E D where
  toLieEquiv := e.toLieEquiv.symm
  map_basis i := by
    apply e.toLieEquiv.injective
    change e.toLieEquiv (e.toLieEquiv.symm (E.basis i)) = e.toLieEquiv (D.basis i)
    rw [LieEquiv.apply_symm_apply, e.map_basis]
  mem_layer n x := by
    have h := e.mem_layer n (e.toLieEquiv.symm x)
    rw [LieEquiv.apply_symm_apply] at h
    exact h.symm
  mem_lattice g := by
    have h := e.mem_lattice (⟨e.toLieEquiv.symm g.coord⟩ : D.filtration.Group)
    have heq : NilpotentLieBCHGroup.map (hM := E.filtration.lowerCentralSeries_eq_bot)
        e.toLieEquiv.toLieHom (⟨e.toLieEquiv.symm g.coord⟩ : D.filtration.Group) = g := by
      apply NilpotentLieBCHGroup.ext
      exact e.toLieEquiv.apply_symm_apply g.coord
    rw [heq] at h
    exact h.symm

end NativeModelEquiv

noncomputable def nativeModelEquivOfCoordinates
    (h : D.rationalModelCoordinates = E.rationalModelCoordinates) (B : ℕ)
    (hD : bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B)
    (hE : bchSubgroupCoordinates E.basis E.lattice = scaledIntegerGrid B) : NativeModelEquiv D E where
  toLieEquiv := D.rationalModelEquiv E h
  map_basis := D.rationalModelEquiv_basis E h
  mem_layer n x := D.rationalModelGroupEquiv_mem_layer E h n ⟨x⟩
  mem_lattice := D.rationalModelGroupEquiv_mem_integral_lattice E h D.lattice E.lattice B hD hE

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3

open scoped TensorProduct

theorem realificationLieEquiv_inverse
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (e : L ≃ₗ⁅ℚ⁆ M) (x : ℝ ⊗[ℚ] L) :
    realificationLieHom e.symm.toLieHom (realificationLieHom e.toLieHom x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change a ⊗ₜ[ℚ] e.symm (e x) = a ⊗ₜ[ℚ] x
    rw [LieEquiv.symm_apply_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M s d}
  (e : NativeModelEquiv D E)

noncomputable def realGroupEquiv : D.RealGroup ≃* E.RealGroup :=
  { realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) e.toLieEquiv.toLieHom with
    invFun := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) e.toLieEquiv.symm.toLieHom
    left_inv g := by
      apply NilpotentLieBCHGroup.ext
      exact realificationLieEquiv_inverse e.toLieEquiv g.coord
    right_inv g := by
      apply NilpotentLieBCHGroup.ext
      exact realificationLieEquiv_inverse e.toLieEquiv.symm g.coord }

theorem symm_realGroupEquiv_apply (g : D.RealGroup) :
    e.symm.realGroupEquiv (e.realGroupEquiv g) = g :=
  e.realGroupEquiv.symm_apply_apply g

theorem real_lattice_le : D.realLattice ≤ E.realLattice.comap e.realGroupEquiv.toMonoidHom := by
  apply realificationMap_subgroup e.toLieEquiv.toLieHom D.lattice E.lattice
  intro g hg
  exact (e.mem_lattice g).mpr hg

noncomputable def spaceMap : D.Space → E.Space :=
  cosetMap D.realLattice E.realLattice e.realGroupEquiv.toMonoidHom e.real_lattice_le

theorem spaceMap_mk (g : D.RealGroup) :
    e.spaceMap (QuotientGroup.mk g) = QuotientGroup.mk (e.realGroupEquiv g) := rfl

theorem symm_spaceMap_apply (x : D.Space) : e.symm.spaceMap (e.spaceMap x) = x := by
  induction x using Quotient.inductionOn with
  | _ g =>
    rw [e.spaceMap_mk, e.symm.spaceMap_mk, e.symm_realGroupEquiv_apply]

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]

theorem spaceMap_lipschitz :
    letI := D.metricSpace
    letI := E.metricSpace
    LipschitzWith (coordinateLipschitzBound d d 1) e.spaceMap := by
  have hmatrix : ∀ k i, RationalHeightLE (E.basis.repr (e.toLieEquiv (D.basis i)) k) 1 := by
    intro k i
    rw [e.map_basis]
    simp only [Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> norm_num [RationalHeightLE]
  have hh :=
    lipschitz_realificationMap_quotient D.basis E.basis e.toLieEquiv.toLieHom
      D.lattice E.lattice (fun g hg => (e.mem_lattice g).mpr hg)
      D.grid E.grid D.grid_pos E.grid_pos D.outer_grid E.outer_grid 1 hmatrix
  simp only [Fintype.card_fin, Nat.cast_one] at hh
  convert hh using 1
  rfl

end Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

end

section

namespace Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

open NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M s d}
  (e : NativeModelEquiv D E) {w : σ → ℕ}

noncomputable def mapOrbit (g : D.filtration.realification.PolynomialOrbit w) :
    E.filtration.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog
    (VectorPolynomial.map ((realificationLieHom e.toLieEquiv.toLieHom).toLinearMap.restrictScalars ℚ) g.log)
    (D.filtration.realification.adapted_map E.filtration.realification
      ((realificationLieHom e.toLieEquiv.toLieHom).toLinearMap.restrictScalars ℚ)
      (D.filtration.realificationLieHom_mem_layer E.filtration e.toLieEquiv.toLieHom
        (fun n x hx => (e.mem_layer n x).mpr hx)) w g.adapted)

theorem mapOrbit_eval (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    E.filtration.realification.polynomialOrbitEval w x (e.mapOrbit g) =
      e.realGroupEquiv (D.filtration.realification.polynomialOrbitEval w x g) := by
  apply NilpotentLieBCHGroup.ext
  exact eval_map (fun i => (x i : ℚ))
    ((realificationLieHom e.toLieEquiv.toLieHom).toLinearMap.restrictScalars ℚ) g.log

end Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CommonVariableDimensionNiltests
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

open Module CircleFourier
open scoped TensorProduct NNReal

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M s d}
  (e : NativeModelEquiv D E) {w : σ → ℕ}

noncomputable def transport (T : D.Niltest w) : E.Niltest w where
  orbit := e.mapOrbit T.orbit
  observable := T.observable ∘ e.symm.spaceMap
  normBound := T.normBound
  lipBound := T.lipBound * coordinateLipschitzBound d d 1
  norm_le x := T.norm_le _
  lipschitz := by
    let := D.metricSpace
    let := E.metricSpace
    exact T.lipschitz.comp e.symm.spaceMap_lipschitz

theorem transport_eval (T : D.Niltest w) (x : σ → ℤ) : (e.transport T).eval x = T.eval x := by
  change T.observable (e.symm.spaceMap
    (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval w x (e.mapOrbit T.orbit)))) = _
  rw [e.mapOrbit_eval, ← e.spaceMap_mk, e.symm_spaceMap_apply]
  rfl

theorem transport_unit_interval (T : D.Niltest w) (hT : T.UnitIntervalValued) :
    (e.transport T).UnitIntervalValued := fun x => hT (e.symm.spaceMap x)

theorem transport_complexity (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hT : T.ComplexityLE p) (hE : E.GeometryComplexityLE p) :
    (e.transport T).ComplexityLE (p + (p + 2) ^ 2) := by
  have hK : (coordinateLipschitzBound d d 1 : ℝ) ≤ Real.exp ((p + 2) ^ 2) :=
    coordinateLipschitzBound_le_exp d d 1 hp hT.1.1 hE.1 (Real.one_le_exp_iff.mpr hp)
  have h1 : 1 ≤ Real.exp ((p + 2) ^ 2) := Real.one_le_exp_iff.mpr (sq_nonneg _)
  refine ⟨hE.mono E (le_add_of_nonneg_right (sq_nonneg _)), ?_⟩
  change Real.log (2 + (T.normBound : ℝ) +
    (T.lipBound : ℝ) * coordinateLipschitzBound d d 1) ≤ p + (p + 2) ^ 2
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    2 + (T.normBound : ℝ) + (T.lipBound : ℝ) * coordinateLipschitzBound d d 1 ≤
        (2 + (T.normBound : ℝ)) * Real.exp ((p + 2) ^ 2) +
          (T.lipBound : ℝ) * Real.exp ((p + 2) ^ 2) :=
      add_le_add (le_mul_of_one_le_right (by positivity) h1)
        (mul_le_mul_of_nonneg_left hK T.lipBound.coe_nonneg)
    _ = (2 + (T.normBound : ℝ) + (T.lipBound : ℝ)) * Real.exp ((p + 2) ^ 2) := by ring
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ 2) :=
      mul_le_mul_of_nonneg_right (Niltest.observable_budget hT) (Real.exp_pos _).le
    _ = Real.exp (p + (p + 2) ^ 2) := (Real.exp_add _ _).symm

end Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_common_native_niltest_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G σ : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)]
      [∀ h, TopologicalSpace (ℝ ⊗[ℚ] L h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] L h)]
      [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] L h)] [∀ h, T2Space (ℝ ⊗[ℚ] L h)] {d : ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s d) {w : σ → ℕ}
      (T : ∀ h, (D h).Niltest w) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h, (T h).ComplexityLE p) →
      ∃ h₀ ∈ H, ∃ E : RationalFilteredNilmanifold (L h₀) s d,
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ (H' : Finset G) (S : G → E.Niltest w),
          H' ⊆ H ∧ h₀ ∈ H' ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', (S h).ComplexityLE ((p + C) ^ C) ∧ (S h).normBound = (T h).normBound ∧
            (∀ x : σ → ℤ, (S h).eval x = (T h).eval x) ∧
            ((T h).UnitIntervalValued → (S h).UnitIntervalValued) := by
  classical
  obtain ⟨c, _, hmodels⟩ := exists_common_integral_models s
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + 2) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro G σ L _ _ _ _ _ _ d D w T H hH p hp hT
  let q := p + (p + c) ^ c
  have hc0 : 0 ≤ (p + c) ^ c := by positivity
  have hpq : p ≤ q := le_add_of_nonneg_right hc0
  have hcq : (p + c) ^ c ≤ q := le_add_of_nonneg_left hp
  have hq0 : 0 ≤ q := hp.trans hpq
  have hbud : q + (q + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := (le_add_of_nonneg_right (sq_nonneg _)).trans hbud
  obtain ⟨B, Λ, hB, hin, hout, hcover, h₀, hh₀, H', hsub, hh₀', hsame, hlarge⟩ :=
    hmodels D H hH hp (fun h => (hT h).1)
  let E₀ := (D h₀).withLattice (Λ h₀) (B h₀) (hB h₀) (hin h₀) (hout h₀)
  have hE₀ : E₀.GeometryComplexityLE q := (hcover h₀).2.2.2.mono E₀ hcq
  have hbuild (h : {h // h ∈ H'}) : ∃ S : E₀.Niltest w,
      S.ComplexityLE ((p + C) ^ C) ∧ S.normBound = (T h.val).normBound ∧
      (∀ x : σ → ℤ, S.eval x = (T h.val).eval x) ∧
      ((T h.val).UnitIntervalValued → S.UnitIntervalValued) := by
    let E₁ := (D h.val).withLattice (Λ h.val) (B h.val) (hB h.val) (hin h.val) (hout h.val)
    have hE₁ : E₁.GeometryComplexityLE q := (hcover h.val).2.2.2.mono E₁ hcq
    have hcode : E₁.rationalModelCoordinates = E₀.rationalModelCoordinates := (hsame h.val h.property).2
    have hcoords₁ : bchSubgroupCoordinates E₁.basis E₁.lattice = scaledIntegerGrid (B h₀) := by
      change bchSubgroupCoordinates (D h.val).basis (Λ h.val) = _
      rw [(hcover h.val).2.2.1, (hsame h.val h.property).1]
    let e := nativeModelEquivOfCoordinates E₁ E₀ hcode (B h₀) hcoords₁ (hcover h₀).2.2.1
    let T₁ := (T h.val).onSublattice (Λ h.val) (B h.val) (hB h.val)
      (hin h.val) (hout h.val) (hcover h.val).2.1
    have hT₁ : T₁.ComplexityLE q := (T h.val).onSublattice_complexity
      (Λ h.val) (B h.val) (hB h.val) (hin h.val) (hout h.val) (hcover h.val).2.1
      ((hT h.val).mono hpq) hE₁
    refine ⟨e.transport T₁, (e.transport_complexity T₁ hq0 hT₁ hE₀).mono hbud, rfl, ?_, ?_⟩
    · intro x
      exact e.transport_eval T₁ x
    · intro ht
      apply e.transport_unit_interval
      exact (T h.val).onSublattice_unit_interval (Λ h.val) (B h.val) (hB h.val)
        (hin h.val) (hout h.val) (hcover h.val).2.1 ht
  choose S hS using hbuild
  let S₀ : G → E₀.Niltest w := fun h =>
    if hh : h ∈ H' then S ⟨h, hh⟩ else Niltest.const E₀ w 0
  refine ⟨h₀, hh₀, E₀, hE₀.mono E₀ hqC, H', S₀, hsub, hh₀', ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (hcq.trans hqC)))
      (Nat.cast_nonneg _)).trans hlarge
  · intro h hh
    simpa only [S₀, dif_pos hh] using hS ⟨h, hh⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_common_variable_dimension_niltest_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G σ : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)]
      [∀ h, TopologicalSpace (ℝ ⊗[ℚ] L h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] L h)]
      [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] L h)] [∀ h, T2Space (ℝ ⊗[ℚ] L h)] {d : G → ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s (d h)) {w : σ → ℕ}
      (T : ∀ h, (D h).Niltest w) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h, (T h).ComplexityLE p) →
      ∃ h₀ ∈ H, ∃ E : RationalFilteredNilmanifold (L h₀) s (d h₀),
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ (H' : Finset G) (S : G → E.Niltest w),
          H' ⊆ H ∧ h₀ ∈ H' ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', (S h).ComplexityLE ((p + C) ^ C) ∧ (S h).normBound = (T h).normBound ∧
            (∀ x : σ → ℤ, (S h).eval x = (T h).eval x) ∧
            ((T h).UnitIntervalValued → (S h).UnitIntervalValued) := by
  classical
  obtain ⟨c, _, hmodels⟩ := exists_common_native_niltest_model s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C c) ^ c + X + 1)
  refine ⟨C, hC, ?_⟩
  intro G σ L _ _ _ _ _ _ d D w T H hH p hp hT
  let q := (p + c) ^ c
  have hbud : q + p + 1 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hpexp : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  obtain ⟨hbase, _, H₀, hsub₀, hhbase, hsame, hlarge₀⟩ :=
    exists_common_bounded_moduli H hH (fun h (_ : Unit) => d h) hp
      (fun h _ _ => (hT h).1.1.trans hpexp)
  have hdim (h : {h // h ∈ H₀}) : d h.val = d hbase := congrFun (hsame h.val h.property) ()
  let D₀ := fun h : {h // h ∈ H₀} => (D h.val).castDimension (hdim h)
  let T₀ := fun h : {h // h ∈ H₀} => (T h.val).castDimension (hdim h)
  have hT₀ (h : {h // h ∈ H₀}) : (T₀ h).ComplexityLE p :=
    ((T h.val).castDimension_complexity (hdim h) p).mpr (hT h.val)
  obtain ⟨a, _, E₀, hE₀, H₁, S₁, _, ha, hlarge₁, hS₁⟩ :=
    hmodels D₀ T₀ Finset.univ ⟨⟨hbase, hhbase⟩, Finset.mem_univ _⟩ hp hT₀
  let E := E₀.castDimension (hdim a).symm
  let H' := H₁.image Subtype.val
  let S : G → E.Niltest w := fun h => if hh : h ∈ H₀ then
    (S₁ ⟨h, hh⟩).castDimension (hdim a).symm else Niltest.const E w 0
  have hcard : H'.card = H₁.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hcard₀ : (Finset.univ : Finset {h // h ∈ H₀}).card = H₀.card := by simp
  have hlarge₀' : Real.exp (-(p + 1)) * H.card ≤ (H₀.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hlarge₀
  have hlarge₁' : Real.exp (-q) * H₀.card ≤ (H'.card : ℝ) := by
    rw [hcard]
    simpa only [hcard₀] using hlarge₁
  refine ⟨a.val, hsub₀ a.property, E,
    (E₀.castDimension_geometry (hdim a).symm _).mpr (hE₀.mono E₀ hqC), H', S, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hh
    exact hsub₀ g.property
  · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · calc
      Real.exp (-((p + C) ^ C)) * H.card ≤ Real.exp (-(q + (p + 1))) * H.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (by linarith))) (Nat.cast_nonneg _)
      _ = Real.exp (-q) * (Real.exp (-(p + 1)) * H.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-q) * H₀.card := mul_le_mul_of_nonneg_left hlarge₀' (Real.exp_pos _).le
      _ ≤ H'.card := hlarge₁'
  · intro h hh
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hh
    have hSg := hS₁ g hg
    dsimp only [S]
    rw [dif_pos g.property]
    refine ⟨((S₁ g).castDimension_complexity (hdim a).symm _).mpr (hSg.1.mono hqC), ?_, ?_, ?_⟩
    · calc
        _ = (S₁ g).normBound := (S₁ g).castDimension_normBound _
        _ = (T₀ g).normBound := hSg.2.1
        _ = (T g.val).normBound := (T g.val).castDimension_normBound _
    · intro x
      calc
        _ = (S₁ g).eval x := (S₁ g).castDimension_eval _ x
        _ = (T₀ g).eval x := hSg.2.2.1 x
        _ = (T g.val).eval x := (T g.val).castDimension_eval _ x
    · intro ht
      apply ((S₁ g).castDimension_unit_interval (hdim a).symm).mpr
      apply hSg.2.2.2
      exact ((T g.val).castDimension_unit_interval (hdim g)).mpr ht

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledRefilteredRecoveredExpansion
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

universe u v w

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

def NativeCyclicRecoverySpec (s k C : ℕ) : Prop :=
    ∀ {L : Type u} {M : Type v} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 1 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ P m : ℕ, 0 < P ∧ 0 < m ∧
        (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
          (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
          (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ (l : ℕ) (hl : 0 < l)
            (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates D.basis Λ)
            (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid l),
            let Q := D.withLattice Λ l hl hin hout
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            letI := Q.metricSpace
            letI := E.metricSpace
            let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
              (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            ∀ R : (E.filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group,
              E.filtration.PolynomialRationalGrid E.basis (fun _ : Unit => 1) q R →
              ∃ z : (Unit → ZMod P) → E.RealGroup,
                (∀ c, (∀ i, |(E.basis.baseChange ℝ).repr (z c).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
                  (E.basis.baseChange ℝ).equivFun (z c).coord ∈ realDenominatorGrid m) ∧
                ∀ κ : D.RealGroup, κ ∈ D.realLattice →
                  ∀ a b r f : (Unit → ℤ) → D.RealGroup,
                    (∀ x, a x * b x * r x * κ = f x) →
                    (∀ x, ψ (r x) = E.filtration.adaptedPolynomialRealValueHom (fun _ : Unit => 1)
                      (fun i => (x i : ℝ)) R) →
                    (∀ x, (QuotientGroup.mk (ψ (b x)) : E.Space) =
                      QuotientGroup.mk ((ψ (a x))⁻¹ * ψ (f x) * (ψ κ)⁻¹ *
                        (z (fun i => (x i : ZMod P)))⁻¹)) ∧
                    ∀ (N : ℕ) [NeZero N]
                      (S : (E.filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group),
                      E.filtration.PolynomialSlowBound E.basis (fun _ : Unit => 1)
                        (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ k)) S →
                      (∀ x, ψ (a x) = E.filtration.adaptedPolynomialRealValueHom (fun _ : Unit => 1)
                        (fun i => (x i : ℝ)) S) →
                      ∀ {I J : Type w} (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ)
                        (label : I → ZMod P) {ρ K : ℝ}, 0 < ρ →
                        (∀ i x, 0 ≤ A i x) →
                        (∀ i x, 0 < A i x → (x.val : ZMod P) = label i) →
                        (∀ i x y, 0 < A i x → 0 < A i y →
                          dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) →
                        ∀ (h : ZMod N) i j x y,
                          x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                          0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                          dist (QuotientGroup.mk (f (fun _ => (x.val : ℤ))) : Q.Space)
                            (QuotientGroup.mk (f (fun _ => (y.val : ℤ)))) ≤ K * ρ →
                          dist (QuotientGroup.mk (ψ (b (fun _ => (x.val : ℤ)))) : E.Space)
                            (QuotientGroup.mk (ψ (b (fun _ => (y.val : ℤ))))) ≤
                              Real.exp ((p + C) ^ C) * (K + 1) * ρ

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v w z

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v w z

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def RefilteredRecoveredExpansionSpec (p : ℝ) (q r : ℕ) (cost : ℝ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp cost ∧
    ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
      Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
      Q'.GeometryComplexityLE cost ∧
      ∃ Z : RationalFilteredNilmanifold (∀ i : I₀, L i.val) (s + 1)
          (Fintype.card (Σ i : I₀, Fin (d i.val))),
        Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
        Z.GeometryComplexityLE cost ∧
        ∃ Λ : Subgroup Z₀.filtration.Group, Λ ≤ Z₀.lattice ∧
          (Λ.subgroupOf Z₀.lattice).Characteristic ∧ (Λ.subgroupOf Z₀.lattice).Normal ∧
          (Λ.subgroupOf Z₀.lattice).FiniteIndex ∧ (Λ.relIndex Z₀.lattice : ℝ) ≤ Real.exp cost ∧
          ∃ (l : ℕ) (hl : 0 < l)
            (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates Z₀.basis Λ)
            (hout : bchSubgroupCoordinates Z₀.basis Λ ⊆ denominatorGrid l),
            let V := Z₀.withLattice Λ l hl hin hout
            V.GeometryComplexityLE cost ∧
            letI := V.metricSpace
            let w := fun _ : Unit => 1
            let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
              (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a)
            let ψ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
              (hM := Z.filtration.lowerCentralSeries_eq_bot)
              (liePiMap (fun i : I₀ => refilteredComponentMap D W i.val))
            ∀ {J₀ : Type u} (freq : J₀ → ∀ i, L i →ₗ[ℚ] ℚ),
              (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
                realifyFunctional (piFrequency (freq j)) x = 0) →
              ∀ (N : ℕ) [NeZero N] {I J : Type u} [Fintype I] [Fintype J]
                (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) (label : I → ZMod P) {ρ K : ℝ},
                0 < ρ → 0 ≤ K →
                (∀ i x, 0 ≤ A i x) → (∀ j x, 0 ≤ B j x) →
                (∀ x, ∑ i, A i x = 1) → (∀ x, ∑ j, B j x = 1) →
                (∀ i x, 0 < A i x → (x.val : ZMod P) = label i) →
                (∀ i x y, 0 < A i x → 0 < A i y →
                  dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) →
                ∀ (S : ZMod N → (D a).Niltest w),
                  (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
                  (∀ h z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
                    (∀ j, realifyFunctional (freq j a) z.coord = 0) →
                    ∀ x, (S h).observable (z • x) = (S h).observable x) →
                  ∀ (slow middle rat : ZMod N → ((D a).filtration.realification.adaptedPolynomialFiltration w).Group)
                    (κ : ZMod N → (D a).RealGroup)
                    (g : ZMod N → E.filtration.realification.PolynomialOrbit w),
                    (∀ h, κ h ∈ (D a).realLattice) →
                    (∀ h, slow h * middle h * rat h * (D a).filtration.realification.adaptedConstantGroupHom w (κ h) =
                      ⟨⟨(S h).orbit.log, (S h).orbit.property⟩⟩) →
                    (∀ h, (D a).filtration.PolynomialSlowBound (D a).basis w
                      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
                    (∀ h, (D a).filtration.PolynomialRationalGrid (D a).basis w q (rat h)) →
                    (∀ h x, (D a).filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (middle h) =
                      φ (E.filtration.realification.polynomialOrbitEval w x (g h))) →
                    ∀ (slowZ ratZ : ZMod N → (Z.filtration.realification.adaptedPolynomialFiltration w).Group)
                      (κZ : ZMod N → Z₀.RealGroup) (fZ : ZMod N → (Unit → ℤ) → Z₀.RealGroup),
                      (∀ h, κZ h ∈ Z₀.realLattice) →
                      (∀ h x, Z.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (slowZ h) *
                        ψ (E.filtration.realification.polynomialOrbitEval w x (g h)) *
                        Z.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (ratZ h) * κZ h = fZ h x) →
                      (∀ h, Z.filtration.PolynomialSlowBound Z.basis w (fun _ => (N : ℝ))
                        (Real.exp ((p + 2) ^ r)) (slowZ h)) →
                      (∀ h, Z.filtration.PolynomialRationalGrid Z.basis w q (ratZ h)) →
                      (∀ i j h x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                        0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                        dist (QuotientGroup.mk (fZ h (fun _ => (x.val : ℤ))) : V.Space)
                          (QuotientGroup.mk (fZ h (fun _ => (y.val : ℤ)))) ≤ K * ρ) →
                      ∃ U : I → J → ZMod N → Q'.Niltest w,
                        (∀ i j h, (U i j h).UnitIntervalValued) ∧
                        (∀ i j h, (U i j h).ComplexityLE (cost + 2)) ∧
                        (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x * B j (x + h)) →
                          ∀ x, (U i j h).eval x = 0) ∧
                        ∃ err : ZMod N → ZMod N → ℝ,
                          (∀ h x, ((S h).evalCyclic N (fun _ => x)).re =
                            (∑ i, ∑ j, A i x * B j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                          ∀ h, (𝔼 x, |err h x|) ≤ Real.exp cost * (K + 2) * ρ + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def RefilteredProductExpansionSpec (p : ℝ) (q r : ℕ) (cost : ℝ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp cost ∧
    ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
      Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
      Q'.GeometryComplexityLE cost ∧
        ∃ Λ : Subgroup Z₀.filtration.Group, Λ ≤ Z₀.lattice ∧
          (Λ.subgroupOf Z₀.lattice).Characteristic ∧ (Λ.subgroupOf Z₀.lattice).Normal ∧
          (Λ.subgroupOf Z₀.lattice).FiniteIndex ∧ (Λ.relIndex Z₀.lattice : ℝ) ≤ Real.exp cost ∧
          ∃ (l : ℕ) (hl : 0 < l)
            (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates Z₀.basis Λ)
            (hout : bchSubgroupCoordinates Z₀.basis Λ ⊆ denominatorGrid l),
            let V := Z₀.withLattice Λ l hl hin hout
            V.GeometryComplexityLE cost ∧
            letI := V.metricSpace
            let w := fun _ : Unit => 1
            ∀ {J₀ : Type u} (freq : J₀ → ∀ i, L i →ₗ[ℚ] ℚ),
              (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
                realifyFunctional (piFrequency (freq j)) x = 0) →
              ∀ (N : ℕ) [NeZero N] {I J : Type u} [Fintype I] [Fintype J]
                (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) (label : I → ZMod P) {ρ K : ℝ},
                0 < ρ → 0 ≤ K →
                (∀ i x, 0 ≤ A i x) → (∀ j x, 0 ≤ B j x) →
                (∀ x, ∑ i, A i x = 1) → (∀ x, ∑ j, B j x = 1) →
                (∀ i x, 0 < A i x → (x.val : ZMod P) = label i) →
                (∀ i x y, 0 < A i x → 0 < A i y →
                  dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) →
                ∀ (S : ZMod N → (D a).Niltest w),
                  (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
                  (∀ h z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
                    (∀ j, realifyFunctional (freq j a) z.coord = 0) →
                    ∀ x, (S h).observable (z • x) = (S h).observable x) →
                  ∀ (g : ZMod N → ∀ i, (D i).filtration.realification.PolynomialOrbit w),
                    (∀ h, g h a = (S h).orbit) →
                    ∀ (slow middle rat : ZMod N → ((pi D).filtration.realification.adaptedPolynomialFiltration w).Group)
                      (κ : ZMod N → (pi D).RealGroup),
                      (∀ h, κ h ∈ (pi D).realLattice) →
                      (∀ h, slow h * middle h * rat h * (pi D).filtration.realification.adaptedConstantGroupHom w (κ h) =
                        ⟨⟨(NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (g h)).log,
                          (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (g h)).property⟩⟩) →
                      (∀ h, (pi D).filtration.PolynomialSlowBound (pi D).basis w
                        (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
                      (∀ h, (pi D).filtration.PolynomialRationalGrid (pi D).basis w q (rat h)) →
                      (∀ h α, VectorPolynomial.coefficients
                        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
                          (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight w α)) →
                      (∀ h, VectorPolynomial.coefficients
                        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0) →
                      (∀ i j h x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                        0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                        dist (V.cyclicOrbitPoint
                          (NilpotentLieFiltration.piRealOrbit (fun i : I₀ => (D i.val).filtration)
                            (fun i : I₀ => g h i.val)) N (fun _ : Unit => x))
                          (V.cyclicOrbitPoint
                            (NilpotentLieFiltration.piRealOrbit (fun i : I₀ => (D i.val).filtration)
                              (fun i : I₀ => g h i.val)) N (fun _ : Unit => y)) ≤ K * ρ) →
                      ∃ U : I → J → ZMod N → Q'.Niltest w,
                        (∀ i j h, (U i j h).UnitIntervalValued) ∧
                        (∀ i j h, (U i j h).ComplexityLE (cost + 2)) ∧
                        (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x * B j (x + h)) →
                          ∀ x, (U i j h).eval x = 0) ∧
                        ∃ err : ZMod N → ZMod N → ℝ,
                          (∀ h x, ((S h).evalCyclic N (fun _ => x)).re =
                            (∑ i, ∑ j, A i x * B j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                          ∀ h, (𝔼 x, |err h x|) ≤ Real.exp cost * (K + 2) * ρ + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeMarkedKernelFreezing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest
open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L Q : Type*} [LieRing L] [LieAlgebra ℚ L] [Group Q] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem observable_freeze_marked_kernel_factors
    (T : D.Niltest w) (π : D.RealGroup →* Q) (ρ : Q → D.RealGroup)
    (hρ : Function.RightInverse ρ π)
    (a b r : D.RealGroup) (aF rF : Q)
    (kE kR : D.RealGroup) (hkE : π kE = 1) (hkR : π kR = 1)
    (hcoset : (QuotientGroup.mk ((ρ rF)⁻¹ * r) : D.Space) = QuotientGroup.mk kR) :
    π (kE * ρ aF) = aF ∧ π (ρ rF * kR) = rF ∧
      letI := rightMetricSpace
        (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      ‖T.observable (QuotientGroup.mk (a * b * r)) -
        T.observable (QuotientGroup.mk ((kE * ρ aF) * b * (ρ rF * kR)))‖ ≤
          (T.lipBound : ℝ) * dist (a * (ρ aF)⁻¹) kE := by
  let := rightMetricSpace
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  have hright : (QuotientGroup.mk r : D.Space) = QuotientGroup.mk (ρ rF * kR) := by
    have h := congrArg (fun x : D.Space => (ρ rF) • x) hcoset
    change QuotientGroup.mk (ρ rF * ((ρ rF)⁻¹ * r)) =
      (QuotientGroup.mk (ρ rF * kR) : D.Space) at h
    simpa only [mul_inv_cancel_left] using h
  refine ⟨by rw [map_mul, hkE, hρ, one_mul], by rw [map_mul, hkR, hρ, mul_one], ?_⟩
  have hfreeze := T.observable_freeze_factors a (kE * ρ aF) b r (ρ rF * kR) hright
  have hdist : dist a (kE * ρ aF) = dist (a * (ρ aF)⁻¹) kE := by
    rw [← dist_mul_right a (kE * ρ aF) (ρ aF)⁻¹, mul_inv_cancel_right]
  exact hfreeze.trans_eq (congrArg (fun z : ℝ => (T.lipBound : ℝ) * z) hdist)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeMarkedPolynomialFreezing
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module NilpotentLieBCHGroup
open scoped TensorProduct
variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)

theorem real_linear_section_rightInverse (φ : L →ₗ⁅ℚ⁆ M) (S : M →ₗ[ℚ] L)
    (hS : Function.RightInverse S φ) :
    Function.RightInverse (fun y : G.realification.Group =>
      (⟨S.baseChange ℝ y.coord⟩ : F.realification.Group))
      (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ) := by
  have hcomp : φ.toLinearMap.comp S = LinearMap.id := LinearMap.ext hS
  have hcompR := congrArg (fun f : M →ₗ[ℚ] M => f.baseChange ℝ) hcomp
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hcompR
  intro y
  apply NilpotentLieBCHGroup.ext
  exact DFunLike.congr_fun hcompR y.coord

variable (w : σ → ℕ)

noncomputable def frozenMarkedLeft (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (EF : (G.realification.adaptedPolynomialFiltration w).Group)
    (kE : F.realification.Group) :
    (F.realification.adaptedPolynomialFiltration w).Group :=
  F.realification.adaptedConstantGroupHom w kE *
    F.filteredRealPolynomialSection G w S hS EF

noncomputable def frozenMarkedRight (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (RF : (G.realification.adaptedPolynomialFiltration w).Group)
    (kR : F.realification.Group) :
    (F.realification.adaptedPolynomialFiltration w).Group :=
  F.filteredRealPolynomialSection G w S hS RF *
    F.realification.adaptedConstantGroupHom w kR

theorem frozenMarked_factors_mark
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (hsection : Function.RightInverse S φ)
    (EF RF : (G.realification.adaptedPolynomialFiltration w).Group)
    (kE kR : F.realification.Group)
    (hkE : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kR = 1) :
    F.realPolynomialGroupMap G φ hφ w (F.frozenMarkedLeft G w S hS EF kE) = EF ∧
    F.realPolynomialGroupMap G φ hφ w (F.frozenMarkedRight G w S hS RF kR) = RF := by
  simp only [frozenMarkedLeft, frozenMarkedRight, map_mul,
    realPolynomialGroupMap_constant, hkE, hkR, map_one, one_mul, mul_one,
    realPolynomialGroupMap_filteredSection, hsection, and_self]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.Niltest
open NilpotentLieBCHGroup
open scoped TensorProduct NNReal
variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem observable_frozenMarked_polynomial_factors
    (T : D.Niltest w) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ D.filtration.layer j)
    (hsection : Function.RightInverse S φ)
    (g E P R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (hfac : E * P * R = g)
    (EF RF : (G.realification.adaptedPolynomialFiltration w).Group)
    (kE kR : D.RealGroup)
    (hkE : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kR = 1)
    (z : σ → ℝ)
    (hcoset : (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w z
      ((D.filtration.filteredRealPolynomialSection G w S hS RF)⁻¹ * R)) : D.Space) =
        QuotientGroup.mk kR) :
    letI := rightMetricSpace
      (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    ‖T.observable (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w z g)) -
      T.observable (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w z
        (D.filtration.frozenMarkedLeft G w S hS EF kE * P *
          D.filtration.frozenMarkedRight G w S hS RF kR)))‖ ≤
      (T.lipBound : ℝ) * dist
        (D.filtration.adaptedPolynomialRealValueHom w z
          (E * (D.filtration.filteredRealPolynomialSection G w S hS EF)⁻¹)) kE := by
  let ρ := fun y : G.realification.Group =>
    (⟨S.baseChange ℝ y.coord⟩ : D.RealGroup)
  have he := D.filtration.filteredRealPolynomialSection_value G w S hS EF z
  have hr := D.filtration.filteredRealPolynomialSection_value G w S hS RF z
  have hc : (QuotientGroup.mk
      ((ρ (G.adaptedPolynomialRealValueHom w z RF))⁻¹ *
        D.filtration.adaptedPolynomialRealValueHom w z R) : D.Space) =
      QuotientGroup.mk kR := by
    simpa only [map_mul, map_inv, hr] using hcoset
  have hout := T.observable_freeze_marked_kernel_factors
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ) ρ
    (D.filtration.real_linear_section_rightInverse G φ S hsection)
    (D.filtration.adaptedPolynomialRealValueHom w z E)
    (D.filtration.adaptedPolynomialRealValueHom w z P)
    (D.filtration.adaptedPolynomialRealValueHom w z R)
    (G.adaptedPolynomialRealValueHom w z EF) (G.adaptedPolynomialRealValueHom w z RF)
    kE kR hkE hkR hc
  rw [← hfac]
  simpa only [NilpotentLieFiltration.frozenMarkedLeft,
    NilpotentLieFiltration.frozenMarkedRight, map_mul, map_inv,
    NilpotentLieFiltration.adaptedPolynomialRealValueHom_constant, he, hr] using hout.2.2

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FrozenMarkedLeftOrbitBound
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ η L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (w : σ → ℕ) (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)

noncomputable def frozenMarkedLeftOrbit
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group) :
    F.realification.PolynomialOrbit w :=
  (F.realification.polynomialOrbitCoordinates w).symm
    (F.frozenMarkedLeft G w S hS
      (G.realification.polynomialOrbitCoordinates w marked) center)

noncomputable def frozenMarkedRightOrbit
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group) :
    F.realification.PolynomialOrbit w :=
  (F.realification.polynomialOrbitCoordinates w).symm
    (F.frozenMarkedRight G w S hS
      (G.realification.polynomialOrbitCoordinates w marked) center)

theorem nativeFrozenMarkedOrbitCoordinates_realValue
    (g : F.realification.PolynomialOrbit w) (x : σ → ℝ) :
    F.adaptedPolynomialRealValueHom w x (F.realification.polynomialOrbitCoordinates w g) =
      F.realification.polynomialOrbitRealEval w x g := rfl

theorem nativeFrozenMarkedOrbitCoordinates_symm_realEval
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (x : σ → ℝ) :
    F.realification.polynomialOrbitRealEval w x
      ((F.realification.polynomialOrbitCoordinates w).symm g) =
      F.adaptedPolynomialRealValueHom w x g := rfl

theorem frozenMarkedLeftOrbit_realEval
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (x : σ → ℝ) :
    F.realification.polynomialOrbitRealEval w x
      (F.frozenMarkedLeftOrbit G w S hS marked center) =
      center * ⟨S.baseChange ℝ (G.realification.polynomialOrbitRealEval w x marked).coord⟩ := by
  rw [frozenMarkedLeftOrbit, F.nativeFrozenMarkedOrbitCoordinates_symm_realEval,
    frozenMarkedLeft, map_mul, F.adaptedPolynomialRealValueHom_constant,
    F.filteredRealPolynomialSection_value, G.nativeFrozenMarkedOrbitCoordinates_realValue]

theorem frozenMarkedRightOrbit_realEval
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (x : σ → ℝ) :
    F.realification.polynomialOrbitRealEval w x
      (F.frozenMarkedRightOrbit G w S hS marked center) =
      ⟨S.baseChange ℝ (G.realification.polynomialOrbitRealEval w x marked).coord⟩ * center := by
  rw [frozenMarkedRightOrbit, F.nativeFrozenMarkedOrbitCoordinates_symm_realEval,
    frozenMarkedRight, map_mul, F.adaptedPolynomialRealValueHom_constant,
    F.filteredRealPolynomialSection_value, G.nativeFrozenMarkedOrbitCoordinates_realValue]

theorem frozenMarkedLeftOrbit_realEval_eq_local
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (v : η → ℕ) (localMarked : (G.realification.adaptedPolynomialFiltration v).Group)
    (x : η → ℝ) (y : σ → ℝ)
    (hmarked : G.adaptedPolynomialRealValueHom v x localMarked =
      G.realification.polynomialOrbitRealEval w y marked) :
    F.realification.polynomialOrbitRealEval w y
      (F.frozenMarkedLeftOrbit G w S hS marked center) =
      F.adaptedPolynomialRealValueHom v x (F.frozenMarkedLeft G v S hS localMarked center) := by
  rw [F.frozenMarkedLeftOrbit_realEval, frozenMarkedLeft, map_mul,
    F.adaptedPolynomialRealValueHom_constant, F.filteredRealPolynomialSection_value, hmarked]

theorem frozenMarkedRightOrbit_realEval_eq_local
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (v : η → ℕ) (localMarked : (G.realification.adaptedPolynomialFiltration v).Group)
    (x : η → ℝ) (y : σ → ℝ)
    (hmarked : G.adaptedPolynomialRealValueHom v x localMarked =
      G.realification.polynomialOrbitRealEval w y marked) :
    F.realification.polynomialOrbitRealEval w y
      (F.frozenMarkedRightOrbit G w S hS marked center) =
      F.adaptedPolynomialRealValueHom v x (F.frozenMarkedRight G v S hS localMarked center) := by
  rw [F.frozenMarkedRightOrbit_realEval, frozenMarkedRight, map_mul,
    F.adaptedPolynomialRealValueHom_constant, F.filteredRealPolynomialSection_value, hmarked]

variable (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (hsection : Function.RightInverse S φ)

include hφ hsection

theorem frozenMarkedLeftOrbit_formal_mark
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (hcenter : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ center = 1) :
    map (realLieHomToRat (realificationLieHom φ)).toLinearMap
      (F.frozenMarkedLeftOrbit G w S hS marked center).log = marked.log := by
  have h := (F.frozenMarked_factors_mark G w φ hφ S hS hsection
    (G.realification.polynomialOrbitCoordinates w marked)
    (G.realification.polynomialOrbitCoordinates w marked) center center hcenter hcenter).1
  exact congrArg (fun q : (G.realification.adaptedPolynomialFiltration w).Group =>
    (q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M))) h

theorem frozenMarkedRightOrbit_formal_mark
    (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
    (hcenter : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ center = 1) :
    map (realLieHomToRat (realificationLieHom φ)).toLinearMap
      (F.frozenMarkedRightOrbit G w S hS marked center).log = marked.log := by
  have h := (F.frozenMarked_factors_mark G w φ hφ S hS hsection
    (G.realification.polynomialOrbitCoordinates w marked)
    (G.realification.polynomialOrbitCoordinates w marked) center center hcenter hcenter).2
  exact congrArg (fun q : (G.realification.adaptedPolynomialFiltration w).Group =>
    (q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M))) h

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ η L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {v : η → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_frozenMarkedLeftOrbit_exp_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ ι κ L M : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
        [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
        {t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
        (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ) (S : M →ₗ[ℚ] L)
        (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) (H HS : ℕ) (p : ℝ),
        0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
        (H : ℝ) ≤ Real.exp p → (HS : ℝ) ≤ Real.exp p →
        (∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) →
        (∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) HS) →
        ∀ (marked : G.realification.PolynomialOrbit w) (center : F.realification.Group)
          (x : σ → ℤ),
          (∀ i, |(c.baseChange ℝ).repr
            (G.realification.polynomialOrbitEval w x marked).coord i| ≤ Real.exp p) →
          (∀ i, |(b.baseChange ℝ).repr center.coord i| ≤ Real.exp p) →
          ∀ i, |(b.baseChange ℝ).repr
            (F.realification.polynomialOrbitEval w x
              (F.frozenMarkedLeftOrbit G w S hS marked center)).coord i| ≤
                Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hproduct⟩ := exists_bch_fixed_product_exp_bound s 2 2
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ t F G b c w S hS H HS p hp hd hdmark hH hHS hb hSheight
    marked center x hmarked hcenter i
  have hmarkedNorm :
      ‖(c.baseChange ℝ).equivFun
        (G.realification.polynomialOrbitEval w x marked).coord‖ ≤ Real.exp p := by
    apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg p)).mpr
    intro j
    simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using hmarked j
  have hdim : (Fintype.card κ : ℝ) + 1 ≤ Real.exp p := by
    linarith [Real.add_one_le_exp p]
  have hheight : (HS : ℝ) + 1 ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp p * 2 := by linarith [Real.one_le_exp hp]
      _ ≤ Real.exp p * Real.exp 1 :=
        mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg p)
      _ = _ := (Real.exp_add _ _).symm
  have hsectionNorm :
      ‖(b.baseChange ℝ).equivFun
        (S.baseChange ℝ (G.realification.polynomialOrbitEval w x marked).coord)‖ ≤
          Real.exp ((p + 2) ^ 2) := by
    apply (realified_linear_coordinate_norm c b S hSheight _).trans
    calc
      _ ≤ (Real.exp p * Real.exp (p + 1)) * Real.exp p :=
        mul_le_mul (mul_le_mul hdim hheight (by positivity) (Real.exp_nonneg p))
          hmarkedNorm (norm_nonneg _) (by positivity)
      _ = Real.exp (3 * p + 1) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  let sectionValue : F.realification.Group :=
    ⟨S.baseChange ℝ (G.realification.polynomialOrbitEval w x marked).coord⟩
  have hsection (j : ι) :
      |(b.baseChange ℝ).repr sectionValue.coord j| ≤ Real.exp ((p + 2) ^ 2) := by
    have hj := norm_le_pi_norm ((b.baseChange ℝ).equivFun sectionValue.coord) j
    have hj' : |(b.baseChange ℝ).repr sectionValue.coord j| ≤
        ‖(b.baseChange ℝ).equivFun sectionValue.coord‖ := by
      simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using hj
    exact hj'.trans hsectionNorm
  have hcenter' (j : ι) :
      |(b.baseChange ℝ).repr center.coord j| ≤ Real.exp ((p + 2) ^ 2) :=
    (hcenter j).trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p]))
  have hbound := hproduct (b.baseChange ℝ) (lieStructureConstants b) H p
    F.realification.lowerCentralSeries_eq_bot [center, sectionValue]
    (fun j k z => (realLieBasis_structure b j k z).symm) hp hd (by simp) hH hb
    (by
      intro a ha j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact hcenter' j
      · exact hsection j) i
  rw [← polynomialOrbitRealEval_integer, frozenMarkedLeftOrbit_realEval,
    polynomialOrbitRealEval_integer]
  simpa only [List.prod_cons, List.prod_nil, mul_one] using hbound

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledMarkedKernelNormalization
namespace OAI

section

namespace Erdos3

theorem kernel_inclusion_height_mul_le_exp (n k H l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ((H ^ (n * k) * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg H) hH (n * k)
  rw [← Real.exp_nat_mul] at hpow
  have hprod : ((n * k : ℕ) : ℝ) * p ≤ (p + 2) ^ 3 := by
    rw [Nat.cast_mul, show (3 : ℕ) = 2 + 1 by decide, pow_succ, pow_two]
    gcongr <;> linarith
  have hlog : ((n * k : ℕ) : ℝ) * p + p ≤ (p + 2) ^ 4 := by
    calc
      _ ≤ 2 * (p + 2) ^ 3 := by
        linarith [le_power_budget hp (by decide : 1 ≤ 3)]
      _ ≤ (p + 2) * (p + 2) ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  rw [Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp (((n * k : ℕ) : ℝ) * p) * Real.exp p :=
      mul_le_mul hpow hl (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (((n * k : ℕ) : ℝ) * p + p) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

theorem kernel_inclusion_denominator_mul_le_exp (n k H q l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hq : q ≤ H ^ (n * k))
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((q * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  have hql : ((q * l : ℕ) : ℝ) ≤ ((H ^ (n * k) * l : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.mul_le_mul_right l hq)
  exact hql.trans (kernel_inclusion_height_mul_le_exp n k H l hp hn hk hH hl)

theorem kernel_coordinate_factor_le_exp (k H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hk : (k : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (k : ℝ) * H ≤ Real.exp ((p + 2) ^ 2) := by
  have hkexp : (k : ℝ) ≤ Real.exp p :=
    hk.trans (by linarith [Real.add_one_le_exp p])
  calc
    _ ≤ Real.exp p * Real.exp p :=
      mul_le_mul hkexp hH (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (p + p) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ)

@[simp] theorem realPolynomialSymbolHom_constant (g : F.realification.Group) :
    F.realPolynomialSymbolHom b ω hF w
      (F.realification.adaptedConstantGroupHom w g) = 1 := by
  apply NilpotentLieBCHGroup.ext
  change F.realPolynomialSymbolMap b ω hF w _ = 0
  rw [F.realPolynomialSymbolMap_eq_zero_iff]
  exact F.realification.polynomialSymbolMap_constant w g.coord

theorem exists_marked_kernel_normalized_factors
    (H : Submodule ℚ L) (hH : F.layer 2 ≤ H)
    (bk : Basis κ ℚ (LinearMap.ker φ.toLinearMap))
    (e p r : (F.realification.adaptedPolynomialFiltration w).Group)
    (hp : realificationLieHom φ
      (coefficients (p.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0) ∈
        (H.map φ.toLinearMap).baseChange ℝ) :
    ∃ (a : ℝ ⊗[ℚ] LinearMap.ker φ.toLinearMap)
      (c : LinearMap.ker φ.toLinearMap)
      (e' p' r' : (F.realification.adaptedPolynomialFiltration w).Group),
      (∀ i, 0 ≤ (bk.baseChange ℝ).repr a i ∧ (bk.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, bk.repr c i = z) ∧
      e' = e * F.realification.adaptedConstantGroupHom w
        ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ a⟩ ∧
      r' = F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] (c : L)⟩ * r ∧
      e' * p' * r' = e * p * r ∧
      F.realPolynomialSymbolHom b ω hF w e' = F.realPolynomialSymbolHom b ω hF w e ∧
      F.realPolynomialSymbolHom b ω hF w p' = F.realPolynomialSymbolHom b ω hF w p ∧
      F.realPolynomialSymbolHom b ω hF w r' = F.realPolynomialSymbolHom b ω hF w r ∧
      F.realPolynomialGroupMap G φ hφ w e' = F.realPolynomialGroupMap G φ hφ w e ∧
      F.realPolynomialGroupMap G φ hφ w p' = F.realPolynomialGroupMap G φ hφ w p ∧
      F.realPolynomialGroupMap G φ hφ w r' = F.realPolynomialGroupMap G φ hφ w r ∧
      coefficients (p'.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈ H.baseChange ℝ := by
  obtain ⟨a, c, ha, hc, hka, hkc, hmid⟩ :=
    F.exists_kernel_constant_factors G φ H hH bk
      (F.realification.adaptedPolynomialConstantHom w p)
      (by simpa only [F.realification.adaptedPolynomialConstantHom_coord] using hp)
  let ka : F.realification.Group := ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ a⟩
  let kc : F.realification.Group := ⟨(1 : ℝ) ⊗ₜ[ℚ] (c : L)⟩
  let C := F.realification.adaptedConstantGroupHom w
  let p' := (C ka)⁻¹ * p * (C kc)⁻¹
  have hma : F.realPolynomialGroupMap G φ hφ w (C ka) = 1 := by
    rw [F.realPolynomialGroupMap_constant, hka, map_one]
  have hmc : F.realPolynomialGroupMap G φ hφ w (C kc) = 1 := by
    rw [F.realPolynomialGroupMap_constant, hkc, map_one]
  refine ⟨a, c, e * C ka, p', C kc * r, ha, hc, rfl, rfl, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · dsimp only [p']; group
  · simp only [map_mul, C, F.realPolynomialSymbolHom_constant, mul_one]
  · simp only [p', map_mul, map_inv, C, F.realPolynomialSymbolHom_constant,
      inv_one, one_mul, mul_one]
  · simp only [map_mul, C, F.realPolynomialSymbolHom_constant, one_mul]
  · rw [map_mul, hma, mul_one]
  · simp only [p', map_mul, map_inv, hma, hmc, inv_one, one_mul, mul_one]
  · rw [map_mul, hmc, one_mul]
  · rw [← F.realification.adaptedPolynomialConstantHom_coord]
    simpa only [p', map_mul, map_inv, C,
      F.realification.adaptedPolynomialConstantHom_constant] using hmid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_controlled_marked_kernel_normalization (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (bk : Basis κ ℚ (LinearMap.ker φ.toLinearMap))
        (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (S : Submodule ℚ L), F.layer 2 ≤ S →
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
        ∀ e middle r : (F.realification.adaptedPolynomialFiltration w).Group,
        F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a)) e →
        F.PolynomialRationalGrid b w l r →
        realificationLieHom φ
          (coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0) ∈
            (S.map φ.toLinearMap).baseChange ℝ →
        ∃ (u : ℝ ⊗[ℚ] LinearMap.ker φ.toLinearMap)
          (v : LinearMap.ker φ.toLinearMap)
          (e' middle' r' : (F.realification.adaptedPolynomialFiltration w).Group),
          (∀ i, 0 ≤ (bk.baseChange ℝ).repr u i ∧ (bk.baseChange ℝ).repr u i < 1) ∧
          (∀ i, ∃ z : ℤ, bk.repr v i = z) ∧
          e' = e * F.realification.adaptedConstantGroupHom w
            ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ u⟩ ∧
          r' = F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] (v : L)⟩ * r ∧
          e' * middle' * r' = e * middle * r ∧
          F.realPolynomialSymbolHom b ω hF w e' = F.realPolynomialSymbolHom b ω hF w e ∧
          F.realPolynomialSymbolHom b ω hF w middle' =
            F.realPolynomialSymbolHom b ω hF w middle ∧
          F.realPolynomialSymbolHom b ω hF w r' = F.realPolynomialSymbolHom b ω hF w r ∧
          F.realPolynomialGroupMap G φ hφ w e' = F.realPolynomialGroupMap G φ hφ w e ∧
          F.realPolynomialGroupMap G φ hφ w middle' =
            F.realPolynomialGroupMap G φ hφ w middle ∧
          F.realPolynomialGroupMap G φ hφ w r' = F.realPolynomialGroupMap G φ hφ w r ∧
          coefficients (middle'.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
            S.baseChange ℝ ∧
          F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C)) e' ∧
          F.PolynomialRationalGrid b w m r' := by
  obtain ⟨ce, _, hslow⟩ := exists_polynomial_slow_product_bound s 1 2
  obtain ⟨cr, _, hrational⟩ := exists_polynomial_rational_product_bound s 2
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ a + (Polynomial.X + 2) ^ 4
  let B : Polynomial ℕ := (Q + Polynomial.C ce) ^ ce + (Q + Polynomial.C cr) ^ cr
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ t F G φ hφ b ω hF w hw bk H l p hH hl hp
    hι hκ hσ hHp hlp hbracket hkernel
  obtain ⟨q, hq, hqbound, hkb, hkg⟩ := exists_basis_image_bounds_of_height b bk
    (LinearMap.ker φ.toLinearMap).subtype H hkernel
  let P : ℝ := (p + 2) ^ a + (p + 2) ^ 4
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hp4 : p ≤ (p + 2) ^ 4 := by
    apply (show p ≤ p + 2 by linarith).trans
    simpa only [pow_one] using
      pow_le_pow_right₀ (show (1 : ℝ) ≤ p + 2 by linarith) (show 1 ≤ 4 by omega)
  have hpP : p ≤ P := hp4.trans (le_add_of_nonneg_left (by positivity))
  have hden : ((q * l : ℕ) : ℝ) ≤ Real.exp P :=
    (kernel_inclusion_denominator_mul_le_exp (Fintype.card ι) (Fintype.card κ)
      H q l hp hι hκ hHp hqbound hlp).trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_left (by positivity)))
  have hbudgetP : (P + ce) ^ ce + (P + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [B, Q, P, Polynomial.eval₂_pow] using hbudget p hp
  have heBudget : (P + ce) ^ ce ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hbudgetP
  have hrBudget : (P + cr) ^ cr ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hbudgetP
  obtain ⟨m, hm, hmp, hqlm, hprod⟩ := hrational F b ω hF w hw H P hH hP
    (hι.trans hpP) (hσ.trans hpP) (hHp.trans (Real.exp_le_exp.mpr hpP)) hbracket
    (q * l) (Nat.mul_pos hq hl) hden
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hrBudget),
    (dvd_mul_left l q).trans hqlm, ?_⟩
  intro S hS T hT e middle r he hr hmiddle
  obtain ⟨u, v, e', middle', r', hu, hv, he', hr', hproduct, hsymE, hsymP, hsymR,
    hmarkE, hmarkP, hmarkR, hconstant⟩ :=
    F.exists_marked_kernel_normalized_factors G φ hφ b ω hF w S hS bk
      e middle r hmiddle
  refine ⟨u, v, e', middle', r', hu, hv, he', hr', hproduct, hsymE, hsymP, hsymR,
    hmarkE, hmarkP, hmarkR, hconstant, ?_, ?_⟩
  · let ku : F.realification.Group :=
      ⟨(LinearMap.ker φ.toLinearMap).subtype.baseChange ℝ u⟩
    have hku : ∀ i, |(b.baseChange ℝ).repr ku.coord i| ≤ Real.exp (P + 2) := by
      intro i
      have hcoord := scalarExtension_fractional_coordinates_bound b bk
        (LinearMap.ker φ.toLinearMap).subtype H hkb u hu i
      have hfactor := kernel_coordinate_factor_le_exp (Fintype.card κ) H hp hκ hHp
      have h24 : (p + 2) ^ 2 ≤ (p + 2) ^ 4 :=
        pow_le_pow_right₀ (by linarith) (by omega)
      exact hcoord.trans (hfactor.trans (Real.exp_le_exp.mpr
        (h24.trans (by dsimp [P]; have := pow_nonneg (by linarith : 0 ≤ p + 2) a; linarith))))
    have hcs := F.polynomialSlowBound_constant b w T hT (Real.exp_nonneg _) ku hku
    have hes := F.polynomialSlowBound_mono b w T hT
      (Real.exp_le_exp.mpr (show (p + 2) ^ a ≤ P + 2 by
        dsimp [P]; have := pow_nonneg (by linarith : 0 ≤ p + 2) 4; linarith)) e he
    have hout := hslow F b ω hF w hw H P hH hP (hι.trans hpP) (hσ.trans hpP)
      (hHp.trans (Real.exp_le_exp.mpr hpP)) hbracket T hT
      [e, F.realification.adaptedConstantGroupHom w ku] (by simp)
      (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · simpa only [pow_one] using hes
        · simpa only [pow_one] using hcs)
    have hout' : F.PolynomialSlowBound b w T (Real.exp ((P + ce) ^ ce)) e' := by
      simpa only [List.prod_cons, List.prod_nil, mul_one, ← he', ku] using hout
    exact F.polynomialSlowBound_mono b w T hT (Real.exp_le_exp.mpr heBudget) e' hout'
  · let kv : F.realification.Group := ⟨(1 : ℝ) ⊗ₜ[ℚ] (v : L)⟩
    have hkv := integral_basis_image_realDenominatorGrid b bk
      (LinearMap.ker φ.toLinearMap).subtype q hkg v hv
    have hcs := F.polynomialRationalGrid_constant b w q kv hkv
    have hcs' := F.polynomialRationalGrid_of_dvd b w hq (dvd_mul_right q l) _ hcs
    have hrs := F.polynomialRationalGrid_of_dvd b w hl (dvd_mul_left l q) r hr
    have hout := hprod [F.realification.adaptedConstantGroupHom w kv, r] (by simp)
      (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact hcs'
        · exact hrs)
    simpa only [List.prod_cons, List.prod_nil, mul_one, ← hr', kv] using hout

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FullMarkedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ ξ L M : Type*} [Fintype ξ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include c τ hG hw

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)

theorem exists_fractional_integral_constant_normalization (g : F.realification.Group) :
    ∃ (a : ℝ ⊗[ℚ] L) (v : L),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr a i ∧ (b.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr v i = z) ∧
      ((⟨a⟩ : F.realification.Group)⁻¹ * g *
        (⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩ : F.realification.Group)⁻¹).coord ∈ F.realification.layer 2 := by
  obtain ⟨a, v, hav, ha, hv⟩ := realification_fractional_integer_split b g.coord
  refine ⟨a, v, ha, hv, ?_⟩
  have h := F.realification.bch_triple_sub_sum_mem_next_layer 1 (-a) g.coord
    (-(1 : ℝ) ⊗ₜ[ℚ] v)
    (by rw [F.realification.one_eq_top]; trivial)
    (by rw [F.realification.one_eq_top]; trivial)
  have hz : -a + g.coord + -(1 : ℝ) ⊗ₜ[ℚ] v = 0 := by rw [hav]; abel
  simpa only [hz, sub_zero, NilpotentLieBCHGroup.coord_mul,
    NilpotentLieBCHGroup.coord_inv] using h

theorem exists_fractional_integral_polynomial_normalization
    (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (e p r : (F.realification.adaptedPolynomialFiltration w).Group) :
    ∃ (a : ℝ ⊗[ℚ] L) (v : L)
      (e' p' r' : (F.realification.adaptedPolynomialFiltration w).Group),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr a i ∧ (b.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr v i = z) ∧
      e' = e * F.realification.adaptedConstantGroupHom w ⟨a⟩ ∧
      r' = F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩ * r ∧
      e' * p' * r' = e * p * r ∧
      F.realPolynomialSymbolHom b ω hF w e' = F.realPolynomialSymbolHom b ω hF w e ∧
      F.realPolynomialSymbolHom b ω hF w p' = F.realPolynomialSymbolHom b ω hF w p ∧
      F.realPolynomialSymbolHom b ω hF w r' = F.realPolynomialSymbolHom b ω hF w r ∧
      coefficients (p'.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈ F.realification.layer 2 := by
  obtain ⟨a, v, ha, hv, hmid⟩ := F.exists_fractional_integral_constant_normalization b
    (F.realification.adaptedPolynomialConstantHom w p)
  let C := F.realification.adaptedConstantGroupHom w
  let ka : F.realification.Group := ⟨a⟩
  let kr : F.realification.Group := ⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩
  let p' := (C ka)⁻¹ * p * (C kr)⁻¹
  refine ⟨a, v, e * C ka, p', C kr * r, ha, hv, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [p']; group
  · simp only [map_mul, C, F.realPolynomialSymbolHom_constant, mul_one]
  · simp only [p', map_mul, map_inv, C, F.realPolynomialSymbolHom_constant,
      inv_one, one_mul, mul_one]
  · simp only [map_mul, C, F.realPolynomialSymbolHom_constant, one_mul]
  · rw [← F.realification.adaptedPolynomialConstantHom_coord]
    simpa only [p', map_mul, map_inv, C,
      F.realification.adaptedPolynomialConstantHom_constant] using hmid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ ξ L M : Type*} [Fintype σ] [Fintype κ] [Fintype ξ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include hw

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ ξ L M : Type*} [Fintype σ] [Fintype κ] [Fintype ξ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include hw

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GlobalMarkedOuterNormalization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

structure GlobalMarkedNativeFactors
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E R : F.RealPolynomialSymbolGroup w) where
  left : (F.realification.adaptedPolynomialFiltration w).Group
  middle : (F.realification.adaptedPolynomialFiltration w).Group
  right : (F.realification.adaptedPolynomialFiltration w).Group
  markedMiddle : (F.gradedRefiltration W).realification.PolynomialOrbit w
  product : left * middle * right = g
  left_symbol : F.realPolynomialSymbolHom b ω hF w left = E
  right_symbol : F.realPolynomialSymbolHom b ω hF w right = R
  constant_second : coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
    F.realification.layer 2
  middle_log : VectorPolynomial.map
    (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
    markedMiddle.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
  (g : (F.realification.adaptedPolynomialFiltration w).Group)
  (E R : F.RealPolynomialSymbolGroup w)

namespace GlobalMarkedNativeFactors
variable {F b ω hF w W g E R}
  (A : GlobalMarkedNativeFactors F b ω hF w W g E R)

theorem middle_values (t : σ → ℝ) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
      ((F.gradedRefiltration W).realification.polynomialOrbitRealEval w t A.markedMiddle) =
        F.adaptedPolynomialRealValueHom w t A.middle :=
  F.native_refiltered_orbit_real_value W w A.markedMiddle _ A.middle_log t

end GlobalMarkedNativeFactors
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)

theorem exists_globalMarkedNativeFactors_of_outer_lifts [Fintype ι]
    (hw : ∀ i, 0 < w i)
    (g e₀ r₀ : (F.realification.adaptedPolynomialFiltration w).Group)
    (E R : F.RealPolynomialSymbolGroup w)
    (he : F.realPolynomialSymbolHom b ω hF w e₀ = E)
    (hr : F.realPolynomialSymbolHom b ω hF w r₀ = R)
    (hfast : (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W)) :
    ∃ (a : ℝ ⊗[ℚ] L) (v : L) (A : GlobalMarkedNativeFactors F b ω hF w W g E R),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr a i ∧ (b.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr v i = z) ∧
      A.left = e₀ * F.realification.adaptedConstantGroupHom w ⟨a⟩ ∧
      A.right = F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩ * r₀ := by
  obtain ⟨a, v, e, middle, r, ha, hv, he', hr', hprod, hesym, hp, hrsym, hc⟩ :=
    F.exists_fractional_integral_polynomial_normalization b ω hF w
      e₀ (e₀⁻¹ * g * r₀⁻¹) r₀
  have hprod' : e * middle * r = g := hprod.trans (by group)
  have hpfast : (F.realPolynomialSymbolHom b ω hF w middle).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W) := by
    rw [hp, map_mul, map_mul, map_inv, map_inv, he, hr]
    exact hfast
  rw [F.realPolynomialSymbolHom_coord] at hpfast
  have hfirst := Submodule.baseChange_mono ℝ
    (F.layer_succ_le_gradedRefiltrationLayer W 1) hc
  obtain ⟨q, hq, _⟩ := F.exists_native_pointwise_refiltered_orbit_of_constant W
    b ω hF w hw middle.coord hfirst
    ((F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w W _).mp hpfast)
  exact ⟨a, v, ⟨e, middle, r, q, hprod', hesym.trans he, hrsym.trans hr, hc, hq⟩,
    ha, hv, he', hr'⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFrozenMarkedLocalMark
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M]

theorem sectionCorrectedPolynomial_map (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    (hS : Function.RightInverse S φ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) :
    map ((φ.baseChange ℝ).restrictScalars ℚ) (sectionCorrectedPolynomial φ S p q) = q := by
  apply coefficients.injective
  ext a
  rw [coefficients_map, sectionCorrectedPolynomial_coefficients]
  change φ.baseChange ℝ (coefficients p a -
    S.baseChange ℝ (φ.baseChange ℝ (coefficients p a) - coefficients q a)) = _
  rw [map_sub, linearMap_baseChange_rightInverse φ S hS]
  abel

namespace NilpotentLieFiltration

variable {ι κ : Type*} {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ)

theorem real_projected_discrepancy_mem_shifted
    (p : F.realification.adaptedLieSubalgebra w)
    (q : G.realification.adaptedLieSubalgebra w)
    (hcompat : (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
      (F.realPolynomialSymbolMap b ω hF w p) = G.realPolynomialSymbolMap c τ hG w q) :
    F.realification.filteredPolynomialMap G.realification
      (realLieHomToRat (realificationLieHom φ))
      (F.realificationLieHom_mem_layer G φ hφ) w p - q ∈
        G.realification.shiftedAdaptedIdeal w := by
  let r : G.realification.adaptedLieSubalgebra w :=
    F.realification.filteredPolynomialMap G.realification
      (realLieHomToRat (realificationLieHom φ))
      (F.realificationLieHom_mem_layer G φ hφ) w p
  have he : G.realSymbolOfPolynomial c τ hG w r.val =
      G.realSymbolOfPolynomial c τ hG w q.val := by
    calc
      _ = G.realSymbolOfPolynomial c τ hG w
        (map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) p.val) :=
        congrArg (G.realSymbolOfPolynomial c τ hG w)
          (F.realification.filteredPolynomialMap_coe G.realification
            (realLieHomToRat (realificationLieHom φ))
            (F.realificationLieHom_mem_layer G φ hφ) w p)
      _ = (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
        (F.realPolynomialSymbolMap b ω hF w p) :=
        (F.realFilteredPolynomialSymbolMap_polynomial G φ hφ b ω hF c τ hG w p).symm
      _ = _ := hcompat
  have h := (G.realSymbolOfPolynomial_eq_iff_symbolMap_eq c τ hG w r q).mp he
  exact (G.realification.polynomialSymbolMap_eq_iff w r q).mp h

theorem sectionCorrectedPolynomial_prescribed_symbol
    (S : M →ₗ[ℚ] L) (hS : Function.RightInverse S φ)
    (hSlayer : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (x : F.RealPolynomialSymbol w) (q : G.realification.adaptedLieSubalgebra w)
    (hcompat : (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ x =
      G.realPolynomialSymbolMap c τ hG w q) :
    ∃ p : F.realification.adaptedLieSubalgebra w,
      p.val = sectionCorrectedPolynomial φ.toLinearMap S
        (F.realSymbolRepresentative b ω hF w x) q.val ∧
      F.realPolynomialSymbolMap b ω hF w p = x ∧
      F.realification.filteredPolynomialMap G.realification
        (realLieHomToRat (realificationLieHom φ))
        (F.realificationLieHom_mem_layer G φ hφ) w p = q := by
  let p₀ : F.realification.adaptedLieSubalgebra w :=
    F.realAdaptedSymbolRepresentative b ω hF w x
  have hp₀ : F.realPolynomialSymbolMap b ω hF w p₀ = x := by
    dsimp only [p₀]
    exact F.realPolynomialSymbolMap_representative b ω hF w x
  let φR : (ℝ ⊗[ℚ] L) →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] M) := realLieHomToRat (realificationLieHom φ)
  let hφR := F.realificationLieHom_mem_layer G φ hφ
  let δ : G.realification.adaptedLieSubalgebra w :=
    F.realification.filteredPolynomialMap G.realification φR hφR w p₀ - q
  have hδ : δ ∈ G.realification.shiftedAdaptedIdeal w := by
    apply F.real_projected_discrepancy_mem_shifted G φ hφ b ω hF c τ hG w p₀ q
    rw [hp₀]
    exact hcompat
  have hd (a : σ →₀ ℕ) :
      coefficients (map ((S.baseChange ℝ).restrictScalars ℚ) δ.val) a ∈
        F.realification.layer (Finsupp.weight w a + 1) := by
    rw [coefficients_map]
    exact baseChange_mem_of_mapsTo (G.layer (Finsupp.weight w a + 1))
      (F.layer (Finsupp.weight w a + 1)) S (hSlayer _) (hδ a)
  let d : F.realification.adaptedLieSubalgebra w :=
    ⟨map ((S.baseChange ℝ).restrictScalars ℚ) δ.val,
      fun a => F.realification.antitone (Nat.le_succ _) (hd a)⟩
  have hdz : F.realPolynomialSymbolMap b ω hF w d = 0 := by
    apply (F.realPolynomialSymbolMap_eq_zero_iff b ω hF w d).mpr
    exact (F.realification.polynomialSymbolMap_eq_zero_iff w d).mpr hd
  refine ⟨p₀ - d, rfl, ?_, ?_⟩
  · rw [map_sub, hdz, sub_zero]
    exact hp₀
  · apply Subtype.ext
    exact sectionCorrectedPolynomial_map φ.toLinearMap S hS
      (F.realSymbolRepresentative b ω hF w x) q.val

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)

theorem exists_filtered_linear_section
    (c : Basis κ ℚ M) (v : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {k | j ≤ v k}))
    (φ : L →ₗ[ℚ] M)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) :
    ∃ S : M →ₗ[ℚ] L, Function.RightInverse S φ ∧
      ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j := by
  classical
  have hmem (k : κ) : c k ∈ G.layer (v k) := by
    rw [hG]
    exact Submodule.subset_span ⟨k, (show v k ≤ v k from le_rfl), rfl⟩
  choose x hx hφx using fun k => hsurj (v k) (c k) (hmem k)
  let S := c.constr ℚ x
  have hS (k : κ) : S (c k) = x k := c.constr_basis ℚ x k
  refine ⟨S, ?_, ?_⟩
  · have heq : φ.comp S = LinearMap.id := by
      apply c.ext
      intro k
      change φ (S (c k)) = c k
      rw [hS, hφx]
    intro y
    exact congrArg (fun f : M →ₗ[ℚ] M => f y) heq
  · intro j y hy
    have hle : G.layer j ≤ (F.layer j).comap S := by
      rw [hG]
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      change S (c k) ∈ F.layer j
      rw [hS]
      exact F.antitone hk (hx k)
    exact hle hy

theorem exists_formal_marked_orbit_restoration
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (c : Basis κ ℚ M) (v : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {k | j ≤ v k}))
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (w : σ → ℕ) (g : F.realification.PolynomialOrbit w)
    (q : G.realification.PolynomialOrbit w) :
    ∃ restored : F.realification.PolynomialOrbit w,
      map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) restored.log = q.log ∧
      (∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := F.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
          (F.realification.polynomialOrbitRealEval w z restored) =
            G.realification.polynomialOrbitRealEval w z q) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := F.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
          (F.realification.polynomialOrbitRealEval w z g) =
            G.realification.polynomialOrbitRealEval w z q →
        F.realification.polynomialOrbitRealEval w z restored =
          F.realification.polynomialOrbitRealEval w z g := by
  obtain ⟨S, hS, hSlayer⟩ := F.exists_filtered_linear_section G c v hG φ.toLinearMap hsurj
  let P := sectionCorrectedPolynomial φ.toLinearMap S g.log q.log
  have hP : F.realification.Adapted w P := by
    apply (F.realification.adapted_iff_coefficients w P).mpr
    intro a
    rw [show P = sectionCorrectedPolynomial φ.toLinearMap S g.log q.log from rfl,
      sectionCorrectedPolynomial_coefficients]
    apply Submodule.sub_mem
    · exact (F.realification.adapted_iff_coefficients w g.log).mp g.adapted a
    · apply baseChange_mem_of_mapsTo (G.layer (Finsupp.weight w a))
        (F.layer (Finsupp.weight w a)) S (hSlayer _)
      apply Submodule.sub_mem
      · exact F.realificationLieHom_mem_layer G φ hφ _ _
          ((F.realification.adapted_iff_coefficients w g.log).mp g.adapted a)
      · exact (G.realification.adapted_iff_coefficients w q.log).mp q.adapted a
  let restored := polynomialOrbitOfLog P hP
  have hm : map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) restored.log = q.log :=
    sectionCorrectedPolynomial_map φ.toLinearMap S hS g.log q.log
  refine ⟨restored, hm, ?_, ?_⟩
  · intro z
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom φ (eval₂ z P) = eval₂ z q.log
    rw [← hm]
    exact (eval₂_map (realificationLieHom φ).toLinearMap z P).symm
  · intro z hz
    have hc := congrArg NilpotentLieBCHGroup.coord hz
    change φ.toLinearMap.baseChange ℝ (eval₂ z g.log) = eval₂ z q.log at hc
    apply NilpotentLieBCHGroup.ext
    change eval₂ z P = eval₂ z g.log
    dsimp only [P, sectionCorrectedPolynomial]
    rw [map_sub, eval₂_map, map_sub, eval₂_map, hc, sub_self, map_zero, sub_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem externalCandidate_stepZero_coord_eq_zero (F : NilpotentLieFiltration L 0)
    (x : L) : x = 0 := by
  have hx : x ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  simpa only [F.terminal, Submodule.mem_bot] using hx

theorem externalCandidate_stepZero_group_eq_one (F : NilpotentLieFiltration L 0)
    (g : F.Group) : g = 1 := by
  apply NilpotentLieBCHGroup.ext
  exact F.externalCandidate_stepZero_coord_eq_zero g.coord

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial
open scoped TensorProduct

variable {L M σ τ X Ω : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {d : ℕ}
    (D : RationalFilteredNilmanifold L 0 d)
    (G : NilpotentLieFiltration M 0)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

variable {L M σ κ Ω J X : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d n t : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) s n)
    (hEF : E.filtration = D.filtration.gradedRefiltration W)

noncomputable def includedRefilteredOrbit (w : σ → ℕ)
    (g : E.filtration.realification.PolynomialOrbit w) :
    D.filtration.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog
    (map ((realificationLieHom (D.filtration.gradedRefiltrationSubalgebra W).incl).toLinearMap.restrictScalars ℚ) g.log)
    (E.filtration.realification.adapted_map D.filtration.realification _
      (E.filtration.realificationLieHom_mem_layer D.filtration
        (D.filtration.gradedRefiltrationSubalgebra W).incl (by
          intro j x hx
          apply D.filtration.gradedRefiltrationLayer_le W j
          exact (D.filtration.mem_gradedRefiltration_layer W j x).mp (hEF ▸ hx))) w g.adapted)

@[simp] theorem includedRefilteredOrbit_log (w : σ → ℕ)
    (g : E.filtration.realification.PolynomialOrbit w) :
    (D.includedRefilteredOrbit W E hEF w g).log =
      map ((realificationLieHom (D.filtration.gradedRefiltrationSubalgebra W).incl).toLinearMap.restrictScalars ℚ) g.log := rfl

theorem includedRefilteredOrbit_realEval (w : σ → ℕ)
    (g : E.filtration.realification.PolynomialOrbit w) (x : σ → ℝ) :
    D.filtration.realification.polynomialOrbitRealEval w x
        (D.includedRefilteredOrbit W E hEF w g) =
      realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl
        (E.filtration.realification.polynomialOrbitRealEval w x g) := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_map (realificationLieHom
    (D.filtration.gradedRefiltrationSubalgebra W).incl).toLinearMap x g.log

noncomputable def externalCandidateOrbit (w : σ → ℕ)
    (left right : D.filtration.realification.PolynomialOrbit w)
    (middle : E.filtration.realification.PolynomialOrbit w) :
    D.filtration.realification.PolynomialOrbit w :=
  left * D.includedRefilteredOrbit W E hEF w middle * right

theorem externalCandidateOrbit_realEval (w : σ → ℕ)
    (left right : D.filtration.realification.PolynomialOrbit w)
    (middle : E.filtration.realification.PolynomialOrbit w) (x : σ → ℝ) :
    D.filtration.realification.polynomialOrbitRealEval w x
        (D.externalCandidateOrbit W E hEF w left right middle) =
      D.filtration.realification.polynomialOrbitRealEval w x left *
        realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (E.filtration.realification.polynomialOrbitRealEval w x middle) *
      D.filtration.realification.polynomialOrbitRealEval w x right := by
  simp only [externalCandidateOrbit, map_mul, includedRefilteredOrbit_realEval]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem formal_mark_realEval
    {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (w : σ → ℕ)
    (g : F.realification.PolynomialOrbit w) (marked : G.realification.PolynomialOrbit w)
    (hm : map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log)
    (x : σ → ℝ) :
    realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ (F.realification.polynomialOrbitRealEval w x g) =
      G.realification.polynomialOrbitRealEval w x marked := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom φ (eval₂ x g.log) = eval₂ x marked.log
  rw [← hm]
  exact (eval₂_map (realificationLieHom φ).toLinearMap x g.log).symm

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M σ ι κ Ω J X : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nE nF : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nE)
    (hE : E.filtration = D.filtration.gradedRefiltration W)

variable (EF : RationalFilteredNilmanifold
    (Fmark.filtration.gradedRefiltrationSubalgebra (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hEF : EF.filtration = Fmark.filtration.gradedRefiltration (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

include hφ

attribute [local irreducible] NilpotentLieFiltration.associatedGradedMap NilpotentLieFiltration.gradedRefiltrationMap includedRefilteredOrbit externalCandidateOrbit

theorem refiltered_mark_realification_commutes (z : E.RealGroup) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl z) =
    realificationMap (hnil := EF.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot)
      (Fmark.filtration.gradedRefiltrationSubalgebra (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl
      (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := EF.filtration.lowerCentralSeries_eq_bot) (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) z) := by
  have hc : φ.toLinearMap.comp (D.filtration.gradedRefiltrationSubalgebra W).incl.toLinearMap =
      (Fmark.filtration.gradedRefiltrationSubalgebra (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl.toLinearMap.comp ((D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)).toLinearMap := by
    ext x
    exact (D.filtration.gradedRefiltrationMap_apply Fmark.filtration φ hφ W x).symm
  have he := congrArg (fun g => g.baseChange ℝ) hc
  apply NilpotentLieBCHGroup.ext
  change φ.toLinearMap.baseChange ℝ
      ((D.filtration.gradedRefiltrationSubalgebra W).incl.toLinearMap.baseChange ℝ z.coord) =
    (Fmark.filtration.gradedRefiltrationSubalgebra (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl.toLinearMap.baseChange ℝ
      (((D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)).toLinearMap.baseChange ℝ z.coord)
  simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using
    congrArg (fun g => g z.coord) he

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ η L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (hsection : Function.RightInverse S φ)

include hsection

theorem frozenMarkedOuter_product_mark_eq
    (v : η → ℕ)
    (g E P R : (F.realification.adaptedPolynomialFiltration v).Group)
    (hfactor : E * P * R = g)
    (EF RF : (G.realification.adaptedPolynomialFiltration v).Group)
    (hE : F.realPolynomialGroupMap G φ hφ v E = EF)
    (hR : F.realPolynomialGroupMap G φ hφ v R = RF)
    (w : σ → ℕ) (leftMark rightMark : G.realification.PolynomialOrbit w)
    (kE kR : F.realification.Group)
    (hkE : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kR = 1)
    (x : η → ℝ) (y : σ → ℝ)
    (hleft : G.adaptedPolynomialRealValueHom v x EF =
      G.realification.polynomialOrbitRealEval w y leftMark)
    (hright : G.adaptedPolynomialRealValueHom v x RF =
      G.realification.polynomialOrbitRealEval w y rightMark) :
    realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ
      (F.realification.polynomialOrbitRealEval w y
          (F.frozenMarkedLeftOrbit G w S hS leftMark kE) *
        F.adaptedPolynomialRealValueHom v x P *
        F.realification.polynomialOrbitRealEval w y
          (F.frozenMarkedRightOrbit G w S hS rightMark kR)) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ
        (F.adaptedPolynomialRealValueHom v x g) := by
  have hl := F.formal_mark_realEval G φ w
    (F.frozenMarkedLeftOrbit G w S hS leftMark kE) leftMark
    (F.frozenMarkedLeftOrbit_formal_mark G w S hS φ hφ hsection leftMark kE hkE) y
  have hr := F.formal_mark_realEval G φ w
    (F.frozenMarkedRightOrbit G w S hS rightMark kR) rightMark
    (F.frozenMarkedRightOrbit_formal_mark G w S hS φ hφ hsection rightMark kR hkR) y
  rw [← hfactor]
  simp only [map_mul, hl, hr]
  rw [← F.realPolynomialGroupMap_value G φ hφ v E x,
    ← F.realPolynomialGroupMap_value G φ hφ v R x, hE, hR, hleft, hright]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionTargetObservableRegularity
namespace OAI

section

universe u v w₀ w₁ w₂

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

def nativeOptionTargetObservableBudget (p : ℝ) : ℝ :=
  (p + 3) ^ 2 + 2 + 2 * ((p + 3) ^ 2 + 4) ^ 2

variable {Pivot : Type v} {LQ : Type u} {LS : Type w₀} {Param : Type w₁} {σ : Type w₂}
    [Fintype Pivot] {LP : Pivot → Type u}
    [LieRing LQ] [LieAlgebra ℚ LQ] [LieRing LS] [LieAlgebra ℚ LS]
    [∀ j, LieRing (LP j)] [∀ j, LieAlgebra ℚ (LP j)]
    {s t dQ dS : ℕ} {dp : Pivot → ℕ}
    (Q : RationalFilteredNilmanifold LQ s dQ)
    (partners : ∀ j, RationalFilteredNilmanifold (LP j) s (dp j))
    {Source : RationalFilteredNilmanifold LS t dS}
    {ψ : LS →ₗ⁅ℚ⁆ (∀ i : Option Pivot, optionLieSpace LQ LP i)}
    [TopologicalSpace (ℝ ⊗[ℚ] LQ)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LQ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LQ)] [T2Space (ℝ ⊗[ℚ] LQ)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] LP j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] LP j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] LP j)] [∀ j, T2Space (ℝ ⊗[ℚ] LP j)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQ LP i))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQ LP i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQ LP i))]
    [T2Space (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQ LP i))]

theorem AdaptedMapGeometryData.optionTarget_observable_regularity
    {p0 q : ℝ}
    (geometry : Source.AdaptedMapGeometryData (optionProduct Q partners) ψ ((p0 + 3) ^ 2) q)
    {w : σ → ℕ} (descended : Param → Q.Niltest w)
    (hp0 : 0 ≤ p0) (hQ : Q.GeometryComplexityLE p0)
    (hunit : ∀ x, (descended x).UnitIntervalValued)
    (hcomplexity : ∀ x, (descended x).ComplexityLE p0) :
    (∀ x (y : geometry.target.model.Space),
      (optionOriginalObservable Q partners (fun x => (descended x).observable) x y).im = 0 ∧
      0 ≤ (optionOriginalObservable Q partners (fun x => (descended x).observable) x y).re ∧
      (optionOriginalObservable Q partners (fun x => (descended x).observable) x y).re ≤ 1) ∧
    (∀ x (y : geometry.target.model.Space),
      ‖optionOriginalObservable Q partners (fun x => (descended x).observable) x y‖ ≤ 1) ∧
    (∀ x, letI := geometry.target.model.metricSpace;
      LipschitzWith ⟨Real.exp (nativeOptionTargetObservableBudget p0), Real.exp_nonneg _⟩
        (fun y : geometry.target.model.Space =>
          optionOriginalObservable Q partners (fun x => (descended x).observable) x y)) ∧
    ∀ (sites : Set Param) (entropy : ℝ → ℝ),
      (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
        (n : ℝ) ≤ entropy η ∧ ∃ rep : Fin n → {x : Param // x ∈ sites},
          ∀ x ∈ sites, ∃ i, ∀ y,
            ‖(descended x).observable y - (descended (rep i).val).observable y‖ ≤ η) →
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
        (n : ℝ) ≤ entropy η ∧ ∃ rep : Fin n → {x : Param // x ∈ sites},
          ∀ x ∈ sites, ∃ i, ∀ y : geometry.target.model.Space,
            ‖optionOriginalObservable Q partners (fun x => (descended x).observable) x y -
              optionOriginalObservable Q partners (fun x => (descended x).observable)
                (rep i).val y‖ ≤ η := by
  classical
  let ℓ : ℝ≥0 := ⟨Real.exp p0, Real.exp_nonneg _⟩
  have hLip (x : Param) : letI := Q.metricSpace; LipschitzWith ℓ (descended x).observable := by
    let := Q.metricSpace
    apply (descended x).lipschitz.weaken
    change ((descended x).lipBound : ℝ) ≤ Real.exp p0
    have hb := (descended x).observable_budget (hcomplexity x)
    linarith [(descended x).normBound.coe_nonneg]
  let jointGeo := (p0 + 3) ^ 2
  let r := jointGeo + 2
  have hjoint : 0 ≤ jointGeo := by dsimp [jointGeo]; positivity
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hpr : p0 ≤ r := by dsimp [r, jointGeo]; nlinarith
  have htotal : (Fintype.card (Σ i : Option Pivot, Fin (optionDimension dQ dp i)) : ℝ) ≤
      jointGeo := by
    simpa only [finrank_eq_card_basis (optionProduct Q partners).basis, Fintype.card_fin] using
      geometry.target_dimension
  have hH : (⌈Real.exp (jointGeo + 1)⌉₊ : ℝ) ≤ Real.exp r := by
    simpa only [r, show jointGeo + 1 + 1 = jointGeo + 2 by ring] using
      ceil_exp_le_exp_add_one (show 0 ≤ jointGeo + 1 by linarith)
  have hbound := optionOriginalAdaptedLipschitzBound_le_exp Q partners ℓ
    ⌈Real.exp (jointGeo + 1)⌉₊ hr (Real.exp_le_exp.mpr hpr) (hQ.1.trans hpr)
    (htotal.trans (by dsimp [r]; linarith)) hH
  refine ⟨optionOriginalObservable_adapted_unit_interval Q partners
      (fun x => (descended x).observable) geometry.target hunit,
    fun x y => (hunit x).norm_le_one (optionOriginalSpaceProjection Q partners y), ?_, ?_⟩
  · intro x
    let := geometry.target.model.metricSpace
    have hl := optionOriginalObservable_adapted_lipschitz_of_logHeight Q partners
      (fun x => (descended x).observable) geometry.target ℓ (jointGeo + 1)
      geometry.target_forward hLip x
    apply hl.weaken
    change (optionOriginalAdaptedLipschitzBound (L₀ := LQ) (L := LP)
      (d₀ := dQ) (d := dp) ℓ ⌈Real.exp (jointGeo + 1)⌉₊ : ℝ) ≤
        Real.exp (nativeOptionTargetObservableBudget p0)
    convert hbound using 1
    unfold nativeOptionTargetObservableBudget r jointGeo
    congr 1
    ring
  · intro sites entropy hnets
    exact optionOriginalObservable_adapted_member_nets Q partners
      (fun x => (descended x).observable) geometry.target sites entropy hnets

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRefilteredSymbolConditions
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {L σ ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (W : LieSubalgebra ℚ F.AssociatedGraded)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem native_refiltered_symbol_conditions
    (q : (F.gradedRefiltration W).realification.PolynomialOrbit w)
    (middle : (F.realification.adaptedPolynomialFiltration w).Group)
    (hmap : VectorPolynomial.map
      (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      q.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) :
    (F.realPolynomialSymbolHom b ω hF w middle).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W) ∧
    coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
      F.realGradedRefiltrationLayer W 1 := by
  have hcoeff : ∀ α,
      coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
        F.realGradedRefiltrationLayer W (Finsupp.weight w α) := by
    intro α
    rw [← hmap, coefficients_map]
    exact (F.mem_native_refiltration_layer W (Finsupp.weight w α) _).mp
      (((F.gradedRefiltration W).realification.adapted_iff_coefficients w q.log).mp
        q.adapted α)
  constructor
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w W _).mpr
    exact (F.real_symbol_values_iff_refiltration_coefficients b ω hF w W middle.coord).mpr hcoeff
  · rw [← hmap, coefficients_map]
    apply (F.mem_native_refiltration_layer W 1 _).mp
    rw [(F.gradedRefiltration W).realification.one_eq_top]
    trivial

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualOrdinaryPointwiseSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem associatedGradedMap_basis_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hφH : ∀ i j, rationalLogHeight (f.repr (φ (e i)) j) ≤ p) (i : ι) (j : κ) :
    rationalLogHeight ((G.associatedGradedBasis f ν hG).repr
      (F.associatedGradedMap G φ hφ (F.associatedGradedBasis e ω hF i)) j) ≤ p := by
  classical
  rw [F.associatedGradedMap_basis_repr G e ω hF f ν hG φ hφ]
  split_ifs
  · exact hφH i j
  · simpa [rationalLogHeight] using hp

theorem exists_associatedGradedMap_comap_bounded_spanning [Fintype ι] [Fintype κ]
    (U : LieSubalgebra ℚ G.AssociatedGraded) (v : κ → G.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hvH : ∀ a j, rationalLogHeight ((G.associatedGradedBasis f ν hG).repr (v a) j) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (f.repr (φ (e i)) j) ≤ p) :
    ∃ u : ι → F.AssociatedGraded,
      Submodule.span ℚ (Set.range u) =
        (U.comap (F.associatedGradedMap G φ hφ)).toSubmodule ∧
      ∀ a i, rationalLogHeight ((F.associatedGradedBasis e ω hF).repr (u a) i) ≤
        preimageBasisBudget p + 1 := by
  classical
  let eA := F.associatedGradedBasis e ω hF
  let fA := G.associatedGradedBasis f ν hG
  let T := (F.associatedGradedMap G φ hφ).toLinearMap
  let K := U.toSubmodule.comap T
  have heH (a i : ι) : rationalLogHeight (eA.repr (eA a) i) ≤ p := by
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simpa [rationalLogHeight] using hp
  obtain ⟨b, hb⟩ := exists_preimage_basis_logHeight eA fA ⊤ U.toSubmodule T eA v
    eA.span_eq hv hp hκ hι hκ heH hvH
    (F.associatedGradedMap_basis_logHeight G e ω hF f ν hG φ hφ hp hφH)
  have hspan : Submodule.span ℚ (Set.range (fun a => (b a : F.AssociatedGraded))) = K := by
    change Submodule.span ℚ (Set.range ((⊤ ⊓ K).subtype ∘ b)) = K
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      Submodule.range_subtype, top_inf_eq]
  obtain ⟨z, hz, hzH⟩ := exists_bounded_submodule_ambient_spanning eA K
    (fun a => (b a : F.AssociatedGraded)) hspan (one_le_ceil_exp (preimageBasisBudget p))
    (fun a i => rationalHeightLE_ceil_exp (hb a i))
  refine ⟨fun a => z (Fintype.equivFin ι a), ?_, fun a i => ?_⟩
  · change Submodule.span ℚ (Set.range (z ∘ Fintype.equivFin ι)) = K
    rw [Set.range_comp, (Fintype.equivFin ι).surjective.range_eq, Set.image_univ]
    exact hz
  · exact rationalLogHeight_le_of_height (hzH _ i)
      (ceil_exp_le_exp_add_one (preimageBasisBudget_nonneg hp))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ γ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

noncomputable def gradedImageSpanningFamily (v : γ → F.AssociatedGraded) :
    γ → G.AssociatedGraded := fun a => F.associatedGradedMap G φ hφ (v a)

theorem gradedImageSpanningFamily_span (W : LieSubalgebra ℚ F.AssociatedGraded)
    (v : γ → F.AssociatedGraded) (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (F.gradedImageSpanningFamily G φ hφ v)) =
      (W.map (F.associatedGradedMap G φ hφ)).toSubmodule := by
  change Submodule.span ℚ (Set.range ((F.associatedGradedMap G φ hφ).toLinearMap ∘ v)) =
    W.toSubmodule.map (F.associatedGradedMap G φ hφ).toLinearMap
  rw [Set.range_comp, ← Submodule.map_span, hv]

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))

theorem gradedImageSpanningFamily_logHeight [Fintype ι]
    (v : γ → F.AssociatedGraded) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight ((F.associatedGradedBasis e ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (e i)) j) ≤ p) (a : γ) (j : κ) :
    rationalLogHeight ((G.associatedGradedBasis c ν hG).repr
      (F.gradedImageSpanningFamily G φ hφ v a) j) ≤ (p + 2) ^ 4 := by
  exact linearMap_coordinate_logHeight (F.associatedGradedBasis e ω hF)
    (G.associatedGradedBasis c ν hG) (F.associatedGradedMap G φ hφ).toLinearMap hp hι
    (F.associatedGradedMap_basis_logHeight G e ω hF c ν hG φ hφ hp hφH) (v a) (hvH a) j

theorem gradedImage_bounded_spanning [Fintype ι]
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : γ → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω W.toSubmodule)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight ((F.associatedGradedBasis e ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (e i)) j) ≤ p) :
    Submodule.span ℚ (Set.range (F.gradedImageSpanningFamily G φ hφ v)) =
      (W.map (F.associatedGradedMap G φ hφ)).toSubmodule ∧
    BasisGradedSubmodule (G.associatedGradedBasis c ν hG) ν
      (W.map (F.associatedGradedMap G φ hφ)).toSubmodule ∧
    ∀ a j, rationalLogHeight ((G.associatedGradedBasis c ν hG).repr
      (F.gradedImageSpanningFamily G φ hφ v a) j) ≤ (p + 2) ^ 4 := by
  exact ⟨F.gradedImageSpanningFamily_span G φ hφ W v hv,
    F.associatedGradedMap_image_graded G e ω hF c ν hG φ hφ W hW,
    F.gradedImageSpanningFamily_logHeight G φ hφ e ω hF c ν hG v hp hι hvH hφH⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem gradedImagePointwiseSpanning_heightBound {p : ℝ} (hp : 0 ≤ p) :
    (⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  apply (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 4)).trans
  apply Real.exp_le_exp.mpr
  have hpow : 1 ≤ (p + 2) ^ 4 := one_le_pow₀ (by linarith)
  calc
    (p + 2) ^ 4 + 1 ≤ (p + 2) ^ 4 + (p + 2) ^ 4 := by linarith only [hpow]
    _ = (p + 2) ^ 4 * 2 := by ring
    _ ≤ (p + 2) ^ 4 * (p + 2) :=
      mul_le_mul_of_nonneg_left (by linarith : 2 ≤ p + 2) (by positivity)
    _ = (p + 2) ^ 5 := by ring

theorem pointwiseSpanningIndex_card_le
    {σ κ γ M : Type*} [Fintype σ] [Fintype κ] [Fintype γ]
    [LieRing M] [LieAlgebra ℚ M] {t : ℕ}
    (G : NilpotentLieFiltration M t) (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) [Fintype (SymbolBasisIndex w ν)]
    {p : ℝ} (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hγ : (Fintype.card γ : ℝ) ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p) :
    (Fintype.card (SymbolBasisIndex w ν × γ) : ℝ) ≤ pointwiseFastSectionInput t p :=
  (G.pointwiseSymbolSpanning_section_counts (ξ := γ) G c ν hG c ν hG w hw
    hp hκ hκ hγ hσ).1

variable {σ ι κ γ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
  (w : σ → ℕ)

noncomputable def gradedImagePointwiseSpanningFamily (v : γ → F.AssociatedGraded) :
    SymbolBasisIndex w ν × γ → G.PolynomialSymbol w :=
  G.pointwiseSymbolSpanningFamily c ν hG w (F.gradedImageSpanningFamily G φ hφ v)

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem gradedImagePointwiseSpanningFamily_span [Fintype (SymbolBasisIndex w ν)]
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : γ → F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω W.toSubmodule)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range
      (F.gradedImagePointwiseSpanningFamily G φ hφ c ν hG w v)) =
      (G.symbolPointwiseSubalgebra c ν hG w
        (W.map (F.associatedGradedMap G φ hφ))).toSubmodule := by
  exact G.pointwiseSymbolSpanningFamily_span c ν hG w
    (W.map (F.associatedGradedMap G φ hφ))
    (F.associatedGradedMap_image_graded G e ω hF c ν hG φ hφ W hW)
    (F.gradedImageSpanningFamily G φ hφ v)
    (F.gradedImageSpanningFamily_span G φ hφ W v hv)

theorem gradedImagePointwiseSpanningFamily_height [Fintype ι]
    (v : γ → F.AssociatedGraded) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight
      ((F.associatedGradedBasis e ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (e i)) j) ≤ p) :
    ∀ z i, RationalHeightLE ((G.polynomialSymbolBasis c ν hG w).repr
      (F.gradedImagePointwiseSpanningFamily G φ hφ c ν hG w v z) i)
        ⌈Real.exp ((p + 2) ^ 4)⌉₊ := by
  exact G.pointwiseSymbolSpanningFamily_height c ν hG w
    (F.gradedImageSpanningFamily G φ hφ v) (one_le_ceil_exp _)
    (fun a j => rationalHeightLE_ceil_exp
      (F.gradedImageSpanningFamily_logHeight G φ hφ e ω hF c ν hG v hp hι hvH hφH a j))

theorem gradedImagePointwiseSpanningFamily_controlled
    [Fintype σ] [Fintype ι] [Fintype κ] [Fintype γ]
    [Fintype (SymbolBasisIndex w ν)]
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : γ → F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω W.toSubmodule)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (hw : ∀ i, 0 < w i) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hγ : (Fintype.card γ : ℝ) ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight
      ((F.associatedGradedBasis e ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (e i)) j) ≤ p) :
    Submodule.span ℚ (Set.range
      (F.gradedImagePointwiseSpanningFamily G φ hφ c ν hG w v)) =
        (G.symbolPointwiseSubalgebra c ν hG w
          (W.map (F.associatedGradedMap G φ hφ))).toSubmodule ∧
    BasisGradedSubmodule (G.associatedGradedBasis c ν hG) ν
      (W.map (F.associatedGradedMap G φ hφ)).toSubmodule ∧
    (∀ z i, RationalHeightLE ((G.polynomialSymbolBasis c ν hG w).repr
      (F.gradedImagePointwiseSpanningFamily G φ hφ c ν hG w v z) i)
        ⌈Real.exp ((p + 2) ^ 4)⌉₊) ∧
    (Fintype.card (SymbolBasisIndex w ν × γ) : ℝ) ≤ pointwiseFastSectionInput t p ∧
    1 ≤ ⌈Real.exp ((p + 2) ^ 4)⌉₊ ∧
    (⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  exact ⟨F.gradedImagePointwiseSpanningFamily_span G φ hφ c ν hG w e ω hF W v hW hv,
    F.associatedGradedMap_image_graded G e ω hF c ν hG φ hφ W hW,
    F.gradedImagePointwiseSpanningFamily_height G φ hφ c ν hG w e ω hF v hp hι hvH hφH,
    G.pointwiseSpanningIndex_card_le c ν hG w hw hp hκ hγ hσ,
    one_le_ceil_exp _, gradedImagePointwiseSpanning_heightBound hp⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

noncomputable def ordinaryImagePointwiseBudget (s t : ℕ) (p : ℝ) : ℝ :=
  pointwiseFastSectionInput s p + pointwiseFastSectionInput t p + (p + 2) ^ 5

theorem sectionInput_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ pointwiseFastSectionInput s p := by
  unfold pointwiseFastSectionInput
  positivity

theorem ordinaryImagePointwiseBudget_source (s t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    pointwiseFastSectionInput s p ≤ ordinaryImagePointwiseBudget s t p := by
  have ht := sectionInput_nonneg t hp
  have hh : 0 ≤ (p + 2) ^ 5 := by positivity
  unfold ordinaryImagePointwiseBudget
  linarith

theorem ordinaryImagePointwiseBudget_target (s t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    pointwiseFastSectionInput t p ≤ ordinaryImagePointwiseBudget s t p := by
  have hs := sectionInput_nonneg s hp
  have hh : 0 ≤ (p + 2) ^ 5 := by positivity
  unfold ordinaryImagePointwiseBudget
  linarith

theorem ordinaryImagePointwiseBudget_height (s t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + 2) ^ 5 ≤ ordinaryImagePointwiseBudget s t p := by
  have hs := sectionInput_nonneg s hp
  have ht := sectionInput_nonneg t hp
  unfold ordinaryImagePointwiseBudget
  linarith

theorem ordinaryImagePointwiseBudget_ge (s t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ ordinaryImagePointwiseBudget s t p :=
  (pointwiseFastSectionInput_ge s hp).trans (ordinaryImagePointwiseBudget_source s t hp)

theorem symbolCount_le_sectionInput (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + (s + 3)) ^ (s + 3) ≤ pointwiseFastSectionInput s p := by
  have h : 0 ≤ (p + (s + 3)) ^ (s + 3) := by positivity
  unfold pointwiseFastSectionInput
  nlinarith [sq_nonneg ((p + (s + 3)) ^ (s + 3))]

variable {σ ι κ γ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype γ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))

theorem ordinaryGradedImagePointwiseSpanning_controlled
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : γ → F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hγ : (Fintype.card γ : ℝ) ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight
      ((F.associatedGradedBasis b ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (b i)) j) ≤ p) :
    let vg := F.gradedImagePointwiseSpanningFamily G φ hφ c ν hG (fun _ : σ => 1) v
    Submodule.span ℚ (Set.range vg) =
        (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))).toSubmodule ∧
    BasisGradedSubmodule (G.associatedGradedBasis c ν hG) ν
      (W.map (F.associatedGradedMap G φ hφ)).toSubmodule ∧
    (∀ z i, RationalHeightLE ((G.polynomialSymbolBasis c ν hG (fun _ : σ => 1)).repr
      (vg z) i) ⌈Real.exp ((p + 2) ^ 4)⌉₊) ∧
    (Nat.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ ordinaryImagePointwiseBudget s t p ∧
    (Nat.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ ordinaryImagePointwiseBudget s t p ∧
    (Nat.card (SymbolBasisIndex (fun _ : σ => 1) ν × γ) : ℝ) ≤ ordinaryImagePointwiseBudget s t p ∧
    1 ≤ ⌈Real.exp ((p + 2) ^ 4)⌉₊ ∧
    (⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp (ordinaryImagePointwiseBudget s t p) := by
  let : Fintype (SymbolBasisIndex (fun _ : σ => 1) ω) :=
    F.ordinarySymbolBasisFintype b ω hF
  let : Fintype (SymbolBasisIndex (fun _ : σ => 1) ν) :=
    G.ordinarySymbolBasisFintype c ν hG
  obtain ⟨hspan, hgraded, hheight, hcount, hH, hHexp⟩ :=
    F.gradedImagePointwiseSpanningFamily_controlled G φ hφ c ν hG (fun _ : σ => 1)
      b ω hF W v hW hv (fun _ => Nat.zero_lt_one) hp hι hκ hγ hσ hvH hφH
  refine ⟨hspan, hgraded, hheight, ?_, ?_, ?_, hH, ?_⟩
  · have hsource := F.symbolBasisIndex_card_le_spanning_budget b ω hF
      (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) hp hι hσ
    simpa only [Nat.card_eq_fintype_card] using
      (hsource.trans (symbolCount_le_sectionInput s hp)).trans
        (ordinaryImagePointwiseBudget_source s t hp)
  · have htarget := G.symbolBasisIndex_card_le_spanning_budget c ν hG
      (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) hp hκ hσ
    simpa only [Nat.card_eq_fintype_card] using
      (htarget.trans (symbolCount_le_sectionInput t hp)).trans
        (ordinaryImagePointwiseBudget_target s t hp)
  · simpa only [Nat.card_eq_fintype_card] using
      hcount.trans (ordinaryImagePointwiseBudget_target s t hp)
  · exact hHexp.trans (Real.exp_le_exp.mpr (ordinaryImagePointwiseBudget_height s t hp))

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPolynomialGroupMapBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ)

theorem polynomialRationalGrid_iff_coefficients [Finite ι] (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.PolynomialRationalGrid b w l g ↔ ∀ α,
      (b.baseChange ℝ).equivFun
        (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) ∈
          realDenominatorGrid l := by
  classical
  constructor
  · rintro ⟨a, ha⟩ α
    exact ⟨fun i => a (α, i), funext fun i => congrFun ha (α, i)⟩
  · intro h
    choose a ha using h
    exact ⟨fun z => a z.1 z.2, funext fun z => congrFun (ha z.1) z.2⟩

theorem polynomialRationalGrid_inv (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w l g) :
    F.PolynomialRationalGrid b w l g⁻¹ := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => -a z, funext fun z => ?_⟩
  change ((-a z : ℤ) : ℝ) = (l : ℝ) * (b.baseChange ℝ).repr
    (coefficients ((g⁻¹).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
  rw [coord_inv]
  change ((-a z : ℤ) : ℝ) = (l : ℝ) * (b.baseChange ℝ).repr
    (coefficients (-(g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) z.1) z.2
  simp only [map_neg, Finsupp.neg_apply, Int.cast_neg, mul_neg]
  exact congrArg Neg.neg (congrFun ha z)

theorem filteredRealPolynomialSection_rationalGrid [Fintype ι] [Fintype κ]
    [DecidableEq κ] (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) (l : ℕ)
    (g : (G.realification.adaptedPolynomialFiltration w).Group)
    (hg : G.PolynomialRationalGrid c w l g) :
    F.PolynomialRationalGrid b w
      (matrixDenominator (LinearMap.toMatrix c b S) * l)
      (F.filteredRealPolynomialSection G w S hS g) := by
  rw [F.polynomialRationalGrid_iff_coefficients]
  intro α
  have hc := (G.polynomialRationalGrid_iff_coefficients c w l g).mp hg α
  have ho := realified_linear_coordinate_grid c b S l _ hc
  change (b.baseChange ℝ).equivFun (coefficients
    (map ((S.baseChange ℝ).restrictScalars ℚ)
      (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M))) α) ∈ _
  simpa only [coefficients_map, LinearMap.restrictScalars_apply] using ho

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (b : Basis ι ℚ L) (c : Basis κ ℚ M)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (w : σ → ℕ)

theorem realPolynomialGroupMap_slow_exp
    {H : ℕ} (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hsource : (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A : ℝ} (hA : 0 ≤ A)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T A g) :
    G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ 3) * A)
      (F.realPolynomialGroupMap G φ hφ w g) := by
  classical
  let Q := LinearMap.toMatrix b c φ.toLinearMap
  have hQ : ∀ i j, RationalHeightLE (Q i j) H := by
    simpa only [Q, LinearMap.toMatrix_apply, LieHom.coe_toLinearMap] using hentries
  have hnum : ∀ i j, ((Q i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 1) := by
    intro i j
    exact (Nat.cast_le.mpr (hQ i j).1).trans
      (hHp.trans (Real.exp_le_exp.mpr (by simp)))
  intro α i
  change |(c.baseChange ℝ).repr (coefficients
    ((F.realPolynomialGroupMap G φ hφ w g).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) α) i| ≤ _
  rw [F.realPolynomialGroupMap_log G φ hφ w, coefficients_map]
  change |(c.baseChange ℝ).equivFun (φ.toLinearMap.baseChange ℝ
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α)) i| ≤ _
  exact rational_coordinate_map_weighted_exp (b.baseChange ℝ) (c.baseChange ℝ)
    (φ.toLinearMap.baseChange ℝ) Q (realified_linear_coordinate_matrix b c φ.toLinearMap)
    (fun _ : ι => ()) (fun _ : κ => ()) (fun _ _ h => (h rfl).elim)
    hp hsource 1 (by decide) hnum (fun _ : Unit => monomialScale T α)
    (fun _ => monomialScale_pos T hT α) hA
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) (hg α) i

theorem exists_realPolynomialGroupMap_grid
    {H : ℕ} (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hsource : (Fintype.card ι : ℝ) ≤ p)
    (htarget : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ g : (F.realification.adaptedPolynomialFiltration w).Group,
        F.PolynomialRationalGrid b w l g →
        G.PolynomialRationalGrid c w m (F.realPolynomialGroupMap G φ hφ w g) := by
  classical
  let Q := LinearMap.toMatrix b c φ.toLinearMap
  have hQ : ∀ i j, RationalHeightLE (Q i j) H := by
    simpa only [Q, LinearMap.toMatrix_apply, LieHom.coe_toLinearMap] using hentries
  refine ⟨l * matrixDenominator Q, Nat.mul_pos hl (matrixDenominator_pos Q),
    matrixDenominator_allowance_le_exp Q l H hQ hp htarget hsource hHp hlp,
    dvd_mul_right l (matrixDenominator Q), ?_⟩
  intro g hg
  rw [G.polynomialRationalGrid_iff_coefficients]
  intro α
  have hc := (F.polynomialRationalGrid_iff_coefficients b w l g).mp hg α
  have ho := realified_linear_coordinate_grid b c φ.toLinearMap l _ hc
  rw [F.realPolynomialGroupMap_log G φ hφ w, coefficients_map]
  change (c.baseChange ℝ).equivFun (φ.toLinearMap.baseChange ℝ
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α)) ∈
      realDenominatorGrid (l * matrixDenominator Q)
  simpa only [Q, Nat.mul_comm] using ho

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MarkedKernelRationalGrid
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module
open scoped TensorProduct

theorem exists_marked_kernel_rational_grid_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
      (b : Basis ι ℚ L) (c : Basis κ ℚ M) (ω : ι → ℕ)
      (_hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
        (l : ℕ), 0 < l →
      (by classical exact
        ((matrixDenominator (LinearMap.toMatrix c b S) * l : ℕ) : ℝ)) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (R : (F.realification.adaptedPolynomialFiltration w).Group)
          (RF : (G.realification.adaptedPolynomialFiltration w).Group),
          F.PolynomialRationalGrid b w l R → G.PolynomialRationalGrid c w l RF →
          F.PolynomialRationalGrid b w m
            ((F.filteredRealPolynomialSection G w S hS RF)⁻¹ * R) := by
  classical
  obtain ⟨C, hC, hprod⟩ := exists_polynomial_rational_product_bound s 2
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ t F G b c ω hlayers w hw H p hH hp hι hσ hHp hb S hS l hl hlp
  let q := matrixDenominator (LinearMap.toMatrix c b S) * l
  have hq : 0 < q := Nat.mul_pos (matrixDenominator_pos _) hl
  have hlq : l ∣ q := dvd_mul_left _ _
  obtain ⟨m, hm, hmp, hqm, hmul⟩ :=
    hprod F b ω hlayers w hw H p hH hp hι hσ hHp hb q hq hlp
  refine ⟨m, hm, hmp, hlq.trans hqm, ?_⟩
  intro R RF hR hRF
  have hs := F.filteredRealPolynomialSection_rationalGrid G b c w S hS l RF hRF
  have hi := F.polynomialRationalGrid_inv b w q _ hs
  have hr := F.polynomialRationalGrid_of_dvd b w hl hlq R hR
  have hout := hmul [(F.filteredRealPolynomialSection G w S hS RF)⁻¹, R]
    (by simp) (by intro r hr'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr';
                  rcases hr' with rfl | rfl; exact hi; exact hr)
  simpa only [List.prod_cons, List.prod_nil, mul_one] using hout

end Erdos3.NilpotentLieFiltration

end

end OAI

end


