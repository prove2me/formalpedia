-- Prove2me | Definitions.Def_OAIErdos3B052
-- name    : OAIErdos3B052
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T16:43:44.759988+00:00
-- url     : https://prove2.me/theorems/01b8b32d-d315-48d9-b4cc-064fc3d10e35
-- title:
--   OpenAI Erdős-3 split, definitions bundle 53 of 150
-- statement:
--   Definitions bundle 53 of 150 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B051`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 53 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.affineCubeFourierProjection_approx`, `OAI.Erdos3.BooleanCubeKernel.affineCubeFourierProjection_eq_fiberAverage`, `OAI.Erdos3.BooleanCubeKernel.coefficientTorusFourierSum_fiberAverage`, `OAI.Erdos3.BooleanCubeKernel.coefficientTorusFourierSum_fiber_integrable`, `OAI.Erdos3.BooleanCubeKernel.exists_affine_oneSite_density_comparison`, `OAI.Erdos3.BooleanCubeKernel.integerSiteValue_oneSite`, `OAI.Erdos3.BooleanCubeKernel.layeredSiteWeight_physical`, `OAI.Erdos3.BooleanCubeKernel.oneSiteDensity_projection_error`, `OAI.Erdos3.BooleanCubeKernel.physicalAffineSite`, `OAI.Erdos3.BooleanCubeKernel.physicalAffineSite_baseArrayJoin_apply`, `OAI.Erdos3.BooleanCubeKernel.selectedResidue_oneSite_density_error`, `OAI.Erdos3.CoordinateErrorReductionStatement`, `OAI.Erdos3.GlobalErrorSplittingStatement`, `OAI.Erdos3.MixedExpansionIndex`, `OAI.Erdos3.NativeCorrelationStructure.absorb_split_term`, `OAI.Erdos3.NativeCorrelationStructure.exists_fixed_transferred_correlation`, `OAI.Erdos3.NativeCorrelationStructure.mixed_correlation_transfer`, `OAI.Erdos3.NativeCorrelationStructure.normalizedErrorCorrelator`, `OAI.Erdos3.NativeCorrelationStructure.normalizedErrorCorrelator_correlation`, `OAI.Erdos3.NativeCorrelationStructure.normalizedErrorCorrelator_norm`, `OAI.Erdos3.NativeIntegerExpansion.fourPoint`, `OAI.Erdos3.NativeIntegerExpansion.select_sample_product_correlation`, `OAI.Erdos3.NativeIntegerExpansion.translate`, `OAI.Erdos3.NativeMixedReductionData.LowerCode`, `OAI.Erdos3.NativeMixedReductionData.ReductionCode.recOn`, `OAI.Erdos3.NativeMixedReductionData.TranslationCode`, `OAI.Erdos3.NativeMixedReductionData.correction`, `OAI.Erdos3.NativeMixedReductionData.correction_factorization`, `OAI.Erdos3.NativeMixedReductionData.fourthInput`, `OAI.Erdos3.NativeMixedReductionData.globalError`, `OAI.Erdos3.NativeMixedReductionData.globalErrorExpansion`, `OAI.Erdos3.NativeMixedReductionData.lowerTerm`, `OAI.Erdos3.NativeMixedReductionData.lowerTermExpansion`, `OAI.Erdos3.NativeMixedReductionData.noConfusion`, `OAI.Erdos3.NativeMixedReductionData.parallelogramInput`, `OAI.Erdos3.NativeMixedReductionData.parallelogramTermExpansion`, `OAI.Erdos3.NativeMixedReductionData.secondInput`, `OAI.Erdos3.NativeMixedReductionData.translationCoordinates`, `OAI.Erdos3.NativeMixedReductionData.translationGlobal`, `OAI.Erdos3.NativeMixedReductionData.translationGlobalExpansion`, `OAI.Erdos3.NativeMixedReductionData.translationGlobal_sample`, `OAI.Erdos3.NativeMixedReductionData.translationLower`, `OAI.Erdos3.NativeMixedReductionData.translationLowerExpansion`, `OAI.Erdos3.NativeMixedReductionData.translationTerm`, `OAI.Erdos3.NativeMixedReductionData.translationTermExpansion`, `OAI.Erdos3.NativeMixedReductionData.translation_negative`, `OAI.Erdos3.NativeMixedReductionData.translation_positive`, `OAI.Erdos3.NativeMultidegreeNilcharacter.cyclicDiagonalDerivative`, `OAI.Erdos3.NativeMultidegreeNilcharacter.cyclicDiagonalDerivative_branches`, `OAI.Erdos3.NativeMultidegreeNilcharacter.diagonalWrapCoefficient`, `OAI.Erdos3.NativeMultidegreeNilcharacter.diagonalWrapCoefficient_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_bounded_root_degree_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_diagonalWrapCoefficient_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_dilation_degree_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_explicit_half_root_exchange_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_factorial_diagonal`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_finite_assignment_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_finite_sum_coordinate_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_frozen_translation_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_halfDilationExchangeCorrection_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_half_dilation_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_parallelogram_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_parallelogram_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_remainder_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_translation_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_quadratic_diagonal_derivative_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_quadratic_diagonal_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_quadratic_integer_translation_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_remainder_expansion_of_evaluation_coordinates`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_replaced_mixed_translation_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_symmetric_multilinearization`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_tensorSquareExchangeCorrection_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_translation_expansion_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_uniform_dilation_degree_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_uniform_root_degree_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.explicit_half_root_exchange_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.halfDilationExchangeCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.halfDilationExchangeCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.halfDilationExchangeCorrection_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.halfDilationExchangeCorrection_pointwise_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.half_dilation_integer_representative`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedTranslationExpansion_factor`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixed_translation_reduction_transfer`, `OAI.Erdos3.NativeMultidegreeNilcharacter.quadraticDiagonalDerivative`, `OAI.Erdos3.NativeMultidegreeNilcharacter.quadraticDiagonalDerivative_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.quadraticMixedTriple`, `OAI.Erdos3.NativeMultidegreeNilcharacter.rationalDilation`, `OAI.Erdos3.NativeMultidegreeNilcharacter.rationalDilation_eval_rescaled`, `OAI.Erdos3.NativeMultidegreeNilcharacter.tensorSquareExchangeCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.tensorSquareExchangeCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.tensorSquare_antisymmetricKernel`, `OAI.Erdos3.NativeMultidegreeNilcharacter.wrappedDiagonalDerivative`, `OAI.Erdos3.NativeMultidegreeNilcharacter.wrappedDiagonalDerivative_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.wrappedDiagonalDerivative_resolution`, `OAI.Erdos3.NativeNilsequenceExpansion.absorb_correlation`, `OAI.Erdos3.NativeTwoVariableSplit.exists_fixed_correlating_term`, `OAI.Erdos3.NativeVectorEquivalence.transfer_correlation`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData.exists_nilcharacter`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonVerticalProduct_top_invariant`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparison_diagonal_equivalence`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparison_diagonal_expansion`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_controlled_diagonal_comparison`, `OAI.Erdos3.RationalFilteredNilmanifold.topInvariant_integer_expansion_of_step`, `OAI.Erdos3.VectorPolynomial.JetAmbientIndex`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.eval`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.eval_mono`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.eval_shiftConstant`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.eval_shiftConstant_neg_subtractConstant`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.mono`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.norm_eval_le`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.scaleMask`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.scaleMask_eval`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.shiftConstant`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.shiftConstant_cover`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.shiftConstant_mask`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.shiftConstant_modulus`, `OAI.Erdos3.VectorPolynomial.allocatedGridAmbientCoordinates`, `OAI.Erdos3.VectorPolynomial.allocatedGridAxisScale`, `OAI.Erdos3.VectorPolynomial.allocatedGridJetScale`, `OAI.Erdos3.VectorPolynomial.allocatedGridNormalizedRows`, `OAI.Erdos3.VectorPolynomial.allocatedNormalizedGridFactor`, `OAI.Erdos3.VectorPolynomial.allocatedNormalizedGridInterpolation`, `OAI.Erdos3.VectorPolynomial.exists_normalizedTwist_native_approximation`, `OAI.Erdos3.VectorPolynomial.mixedJetAmbientPoint`, `OAI.Erdos3.VectorPolynomial.physicalGridFactorInput`, `OAI.Erdos3.VectorPolynomial.physicalGridFactorInput_subtractConstant`, `OAI.Erdos3.VectorPolynomial.physicalMaskedFactorInput`, `OAI.Erdos3.VectorPolynomial.subtractConstant_neg_cancel`, `OAI.Erdos3.circleCarryCutoff`, `OAI.Erdos3.circleCarryCutoff_lipschitz`, `OAI.Erdos3.circleCarryCutoff_range`, `OAI.Erdos3.circle_dist_half_of_unit_interval`, `OAI.Erdos3.coordinateTranslationExpansion_factor`, `OAI.Erdos3.cyclicCarry`, `OAI.Erdos3.exists_coordinate_error_reduction`, `OAI.Erdos3.exists_coordinate_reduction_budget`, `OAI.Erdos3.exists_fixed_multilinearized_correlation`, `OAI.Erdos3.exists_fixed_shift_smoothCyclicCarry_expansion`, `OAI.Erdos3.exists_mixed_error_budget`, `OAI.Erdos3.exists_multilinear_quadruples`, `OAI.Erdos3.exists_multilinear_quadruples_with_equivalence`, `OAI.Erdos3.exists_multilinearized_correlation`, `OAI.Erdos3.exists_smoothCyclicCarry_expansion`, `OAI.Erdos3.exists_split_global_error`, `OAI.Erdos3.exists_weighted_multilinear_correlation`, `OAI.Erdos3.exists_weighted_multilinear_correlation_with_equivalence`, `OAI.Erdos3.finiteChoiceCoordinateHom`, `OAI.Erdos3.finiteChoiceCoordinateInput`, `OAI.Erdos3.finiteChoiceCoordinateInput_cons`, `OAI.Erdos3.finiteChoiceCoordinateInput_replace`, `OAI.Erdos3.finiteChoiceExpansion`, `OAI.Erdos3.finiteChoiceExpansion_cons`, `OAI.Erdos3.finiteChoiceLeafInput`, `OAI.Erdos3.finiteChoiceReplaceIndex`, `OAI.Erdos3.finiteChoiceReplaceInput`, `OAI.Erdos3.firstTranslationCoordinate`, `OAI.Erdos3.le_mixedErrorPairBudget`, `OAI.Erdos3.map_correlationInput`, `OAI.Erdos3.mem_mixedTranslationCoordinates`, `OAI.Erdos3.mixedErrorBudget`, `OAI.Erdos3.mixedErrorPairBudget`, `OAI.Erdos3.mixedParallelogramProduct`, `OAI.Erdos3.mixedTranslationCoordinates`, `OAI.Erdos3.mixedTranslationCoordinates_nodup`, `OAI.Erdos3.mixedTranslationIntercept`, `OAI.Erdos3.mixedTranslationSample`, `OAI.Erdos3.mixedTranslationSampleHom`, `OAI.Erdos3.mixedTranslationSample_affine`, `OAI.Erdos3.mixedTranslationSample_translated`, `OAI.Erdos3.mixedTranslationSlope`, `OAI.Erdos3.mixedTranslationSlope_replaced_none`, `OAI.Erdos3.mixedTranslationSlope_replaced_vanishes`, `OAI.Erdos3.native_weight_pair_removal`, `OAI.Erdos3.norm_unit_pair_replacement_error`, `OAI.Erdos3.prod_fin_succ_function`, `OAI.Erdos3.replicatedMixed_card`, `OAI.Erdos3.replicatedMixed_nonempty`, `OAI.Erdos3.selectedResidueSmoothPMF_test_le_of_complex`, `OAI.Erdos3.smoothCyclicCarry`, `OAI.Erdos3.smoothCyclicCarry_eq_of_outside`, `OAI.Erdos3.smoothCyclicCarry_fixed_shift_mean_error`, `OAI.Erdos3.smoothCyclicCarry_mean_error`, `OAI.Erdos3.star_finite_expect`, `OAI.Erdos3.translatedMixedProduct`, `OAI.Erdos3.translationExpansionRemainder`, `OAI.Erdos3.untranslatedMixedProduct`, `OAI.Erdos3.untranslatedMixedProduct_eq`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B126
import Definitions.Def_OAIErdos3B134

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.OneSiteFourierAverage
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

theorem coefficientTorusFourierSum_fiber_integrable {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => coefficientTorusFourierSum U frequency c (coefficientFiberMap U t y x)) μ := by
  apply integrable_finsetSum
  intro a _
  exact (coefficientTorusCharacter_fiber_integrable U t (frequency a) μ y).const_mul (c a)

theorem coefficientTorusFourierSum_fiberAverage {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (x : CoefficientTorus (K := K) U) :
    coefficientFiberAverage U μ t (coefficientTorusFourierSum U frequency c) (coefficientEvaluationTorus U t x) =
      ∑ a, if affineCubeModeFactors U t difference (frequency a) then
        c a * coefficientTorusCharacter U (frequency a) x else 0 := by
  change (∫ z, ∑ a, c a * coefficientTorusCharacter U (frequency a)
    (coefficientFiberMap U t (coefficientEvaluationTorus U t x) z) ∂μ) = _
  rw [integral_finsetSum _ (fun a _ =>
    (coefficientTorusCharacter_fiber_integrable U t (frequency a) μ _).const_mul (c a))]
  simp only [integral_const_mul]
  change (∑ a, c a * coefficientFiberAverage U μ t (coefficientTorusCharacter U (frequency a))
    (coefficientEvaluationTorus U t x)) = _
  simp only [coefficientTorusCharacter_fiberAverage_evaluation,
    coefficientResidualFunctional_eq_zero_iff_oneSite U t difference, mul_ite, mul_zero]

theorem affineCubeFourierProjection_eq_fiberAverage {I K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (b : Option K → I → ℝ) :
    affineCubeFourierProjection U t difference frequency p c b =
      coefficientFiberAverage U μ t (coefficientTorusFourierSum U frequency c)
        (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm b)) := by
  rw [coefficientTorusFourierSum_fiberAverage U t difference]
  simp only [coefficientTorusCharacter_sample U _ p hp hm b, affineCubeFourierProjection]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductOneSiteProjectionCap
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial

theorem affineCubeFourierProjection_approx {I K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) {η : ℝ}
    (happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (b : Option K → I → ℝ)
    (hD : Integrable (fun x => D (coefficientFiberMap U t
      (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm b)) x)) μ) :
    ‖affineCubeFourierProjection U t difference frequency p c b -
      ((coefficientFiberAverage U μ t D
        (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm b)) : ℝ) : ℂ)‖ ≤ η := by
  rw [affineCubeFourierProjection_eq_fiberAverage U t difference frequency c μ p hp hm b]
  have he := coefficientFiberAverage_approx U μ t (coefficientTorusFourierSum U frequency c)
    (fun x => (D x : ℂ)) happrox _
    (coefficientTorusFourierSum_fiber_integrable U t frequency c μ _) hD.ofReal
  simpa only [coefficientFiberAverage, integral_complex_ofReal] using he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial

theorem oneSiteDensity_projection_error {X I K F : Type*} [Fintype X] [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) {η ε B : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (prob : FiniteProbabilityWeights X) (b : X → Option K → I → ℝ) (w : X → ℂ)
    (hD : ∀ x, prob.weight x ≠ 0 → Integrable (fun z => D (coefficientFiberMap U t
      (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm (b x))) z)) μ)
    (hw : prob.mean (fun x => ‖w x‖) ≤ B)
    (hprojection : ‖prob.complexMean (fun x => w x * affineCubeFourierSum frequency p c (b x)) -
      prob.complexMean (fun x => w x * affineCubeFourierProjection U t difference frequency p c (b x))‖ ≤ ε) :
    ‖prob.complexMean (fun x => w x * (D (affineSampleCoefficientTorus U p hm (b x)) : ℂ)) -
      prob.complexMean (fun x => w x * ((coefficientFiberAverage U μ t D
        (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm (b x))) : ℝ) : ℂ))‖ ≤
      2 * B * η + ε := by
  apply prob.weighted_projection_comparison w _
    (fun x => affineCubeFourierSum frequency p c (b x))
    (fun x => affineCubeFourierProjection U t difference frequency p c (b x)) _ hη hw
  · intro x _
    rw [norm_sub_rev]
    simpa only [affineCubeFourierSum, coefficientTorusFourierSum,
      coefficientTorusCharacter_sample U _ p hp hm] using happrox (affineSampleCoefficientTorus U p hm (b x))
  · intro x hx
    exact affineCubeFourierProjection_approx U t difference frequency c μ D happrox p hp hm (b x) (hD x hx)
  · exact hprojection

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineOneSiteNormalizedLaw
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem selectedResidueSmoothPMF_test_le_of_complex {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D g φ : (K × I → ℤ) → ℝ) {C ε : ℝ}
    (hg : ∀ x, g x ≤ C) (hφ : ∀ x, 0 ≤ φ x)
    (he : ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        ((φ x : ℂ) * (D x : ℂ))) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        ((φ x : ℂ) * (g x : ℂ))‖ ≤ ε) :
    (∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * (φ x * D x)) ≤
      C * (∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * φ x) + ε := by
  let prob := selectedResidueFiniteLaw modulus G V hV hZ
  have hmean (f : (K × I → ℤ) → ℝ) : prob.mean (fun x => f x.val) =
      ∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * f x :=
    selectedResidueFiniteLaw_mean modulus G V hV hZ f
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_tsum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at he
  have h := prob.mean_mul_le_of_capped_comparison (ε := ε) (fun x => D x.val)
    (fun x => g x.val) (fun x => φ x.val) (fun x => hφ x.val) (fun x => hg x.val) (by
      rw [hmean (fun x => D x * φ x), hmean (fun x => g x * φ x)]
      simpa only [mul_comm, mul_left_comm, mul_assoc] using he)
  rw [hmean (fun x => D x * φ x), hmean φ] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

noncomputable def physicalAffineSite {I K : Type*} [Fintype K]
    (root : K → ℤ) (z : Option K × I → ℤ) : I → ℝ :=
  integerSiteValue (fun k => match k with | none => 1 | some k => root k)
    (fun k j => (z (k,j) : ℝ))

theorem integerSiteValue_oneSite {I K : Type*} [Fintype K]
    (root : K → ℤ) (difference : Fin 0 → K → ℤ) (z : Option K × I → ℤ) :
    integerSiteValue (affineSite root difference ∅) (fun k j => (z (k,j) : ℝ)) =
      physicalAffineSite root z := by
  have hs : affineSite root difference ∅ = (fun k => match k with | none => 1 | some k => root k) := by
    funext k
    cases k <;> simp [affineSite]
  rw [hs]
  rfl

theorem layeredSiteWeight_physical {I K : Type*} [Fintype K]
    (root : K → ℤ) (difference : Fin 0 → K → ℤ) (φ : (I → ℝ) → ℂ)
    (z : Option K × I → ℤ) :
    layeredSiteWeight 0 (fun s => affineSite root difference s) (fun _ => φ)
      (fun k j => (z (k,j) : ℝ)) = φ (physicalAffineSite root z) := by
  rw [layeredSiteWeight_oneSite, integerSiteValue_oneSite]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial

theorem selectedResidue_oneSite_density_error {I K F : Type*} [Fintype I] [Fintype K] [Fintype F]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) {η ε : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (hD : ∀ y, Integrable (fun x => D (coefficientFiberMap U t y x)) μ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (G : Finset (ColumnResiduePattern (Option K) I stride))
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x)
    (w : (Option K × I → ℤ) → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1)
    (hprojection : ‖(∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
      (w x * affineCubeFourierSum frequency p c (fun k j => (x (k, j) : ℝ)))) -
      ∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
        (w x * affineCubeFourierProjection U t difference frequency p c (fun k j => (x (k, j) : ℝ)))‖ ≤ ε) :
    ‖(∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
      (w x * (D (affineSampleCoefficientTorus U p hm (fun k j => (x (k, j) : ℝ))) : ℂ))) -
      ∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
        (w x * ((coefficientFiberAverage U μ t D (coefficientEvaluationTorus U t
          (affineSampleCoefficientTorus U p hm (fun k j => (x (k, j) : ℝ)))) : ℝ) : ℂ))‖ ≤ 2 * η + ε := by
  let prob := selectedResidueFiniteLaw stride G V hV hZ
  have hmean (f : (Option K × I → ℤ) → ℂ) : prob.complexMean (fun x => f x.val) =
      ∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) * f x :=
    selectedResidueFiniteLaw_complexMean stride G V hV hZ f
  have hw' : prob.mean (fun x => ‖w x.val‖) ≤ 1 :=
    (prob.mean_mono (fun x => hw x.val)).trans_eq (prob.mean_const 1)
  have he := oneSiteDensity_projection_error (ε := ε) U t difference frequency c μ D hη happrox p hp hm
    prob (fun x k j => (x.val (k, j) : ℝ)) (fun x => w x.val) (fun _ _ => hD _) hw'
    (by
      rw [hmean (fun x => w x * affineCubeFourierSum frequency p c (fun k j => (x (k, j) : ℝ))),
        hmean (fun x => w x * affineCubeFourierProjection U t difference frequency p c (fun k j => (x (k, j) : ℝ)))]
      exact hprojection)
  rw [hmean (fun x => w x * (D (affineSampleCoefficientTorus U p hm (fun k j => (x (k, j) : ℝ))) : ℂ)),
    hmean (fun x => w x * ((coefficientFiberAverage U μ t D (coefficientEvaluationTorus U t
      (affineSampleCoefficientTorus U p hm (fun k j => (x (k, j) : ℝ)))) : ℝ) : ℂ))] at he
  simpa only [mul_one] using he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

theorem exists_affine_oneSite_density_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (root : K → ℤ) (difference : Fin 0 → K → ℤ)
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin 0)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin 0) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ)
    (_hD : ∀ y, Integrable (fun x => D (coefficientFiberMap U root y x)) μ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          (D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ))) : ℂ))) -
      (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          ((coefficientFiberAverage U μ root D (coefficientEvaluationTorus U root
            (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) : ℝ) : ℂ)))‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hprojection⟩ := exists_affine_cube_fourier_projection m 0
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ root difference
    L C hL hC hLP hCP hsite frequency hbound c B hB hBP hcoefficients p hp hm
    stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR Q hQ test htest
    G hG V hV hwidth D hD η hη happrox
  obtain ⟨hZ, he⟩ := hprojection hP hn hd U root difference linearIndependent_empty_type
    hL hC hLP hCP hsite frequency hbound c hB hBP hcoefficients p hp hm stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  exact selectedResidue_oneSite_density_error U root difference frequency c μ D hη happrox hD p hp hm
    stride G V hV hZ
    (fun z => layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)))
    (fun z => layeredSiteWeight_norm_le Q _ test htest _) he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalBaseInjection
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalAffineSite_baseArrayJoin_apply {K I : Type*} [Fintype K]
    (root : K → ℤ) (tail : K × I → ℤ) (base : I → ℤ) (i : I) :
    physicalAffineSite root (baseArrayJoin tail base) i =
      (base i : ℝ) + ∑ k, (root k : ℝ) * (tail (k,i) : ℝ) := by
  simp only [physicalAffineSite, integerSiteValue, Fintype.sum_option, Finset.sum_apply,
    baseArrayJoin, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, Int.cast_one, one_mul]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedProbabilityGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedGridAxisScale : {a // grid a} → ℝ≥0
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, _⟩ => basisAxisScale (b j) i

variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

noncomputable def allocatedGridNormalizedRows (z : AllocatedFrozenJetRows B U b S O) :
    ∀ a : {a // grid a}, O a.val.1 → ℝ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, ha⟩ => fun t => (z ⟨⟨j, .inr i⟩, ha⟩ t : ℝ) / basisAxisScale (b j) i

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

abbrev JetAmbientIndex {m : ℕ} (O J : Fin m → Type*) := Σ j, O j × J j

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def mixedJetAmbientPoint
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) : JetAmbientIndex O J → ℝ :=
  fun a => normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1)
    (orthonormalMixedChart (o a.1) (mixedArrayRegroup _ _ _ (z a.1) a.2.1)) a.2.2

noncomputable def allocatedGridAmbientCoordinates (z : JetAmbientIndex O J → ℝ) :
    ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, O a.val.1 → ℝ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, _⟩ => fun t => (mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
      ((EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, t, k⟩))).2 i

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedNormalizedGridFactor :
    ∀ a : {a // grid a}, (O a.val.1 → ℝ) → ℝ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, ha⟩ => normalizedIntegerRowInterpolation (basisAxisScale (b j) i)
      (allocatedFrozenBlockPMF B U b hR hσ S u rows ⟨⟨j, .inr i⟩, ha⟩)

noncomputable def allocatedNormalizedGridInterpolation
    (z : ∀ a : {a // grid a}, O a.val.1 → ℝ) : ℝ :=
  ∏ a, allocatedNormalizedGridFactor B U b hR hσ S u rows a (z a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (p : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, PMF (CoefficientJetAxisRow O a.val))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalFactorCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial
variable {X : Type*} {m : ℕ} {J : Fin m → Type*}

noncomputable def physicalMaskedFactorInput (period : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (t : X → ℝ) :
    (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle) :=
  ((fun a => (eval t (p a.1) a.2.2 : UnitAddCircle)),
    (fun a => ((eval t (p a.1) a.2 / period : ℝ) : UnitAddCircle)))

noncomputable def physicalGridFactorInput (period : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (t : X → ℝ) :
    (Σ j, J j) → UnitAddCircle :=
  fun a => ((eval t (p a.1) a.2 / period : ℝ) : UnitAddCircle)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MeasureDegreeZeroTwistTransfer
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical NNReal

structure NormalizedPolynomialTwist (X : Type*) [Fintype X]
    (Y : Type*) [Fintype Y] (periodCap coverCap : ℝ) (L : ℝ≥0) where
  modulus : ℕ
  modulus_pos : 0 < modulus
  modulus_bound : (modulus : ℝ) ≤ periodCap
  cover : ℕ
  cover_pos : 0 < cover
  cover_bound : (cover : ℝ) ≤ coverCap
  mask : (X → ZMod modulus) → ℂ
  mask_bound : ∀ z, ‖mask z‖ ≤ 1
  smooth : (X → ℝ) × (Y → UnitAddCircle) → ℂ
  smooth_bound : ∀ z, ‖smooth z‖ ≤ 1
  smooth_lipschitz : LipschitzWith L smooth

namespace NormalizedPolynomialTwist
variable {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def eval (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) : ℂ :=
  W.mask (fun i => (u i : ZMod W.modulus)) *
    W.smooth (fun i => (u i : ℝ) / N i, physicalGridFactorInput W.cover p (fun i => (u i : ℝ)))

theorem norm_eval_le (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    ‖W.eval N p u‖ ≤ 1 := by
  unfold eval
  rw [norm_mul]
  exact (mul_le_mul (W.mask_bound _) (W.smooth_bound _) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)

noncomputable def mono {Y : Type*} [Fintype Y]
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    {periodCap' coverCap' : ℝ} {L' : ℝ≥0}
    (hp : periodCap ≤ periodCap') (hc : coverCap ≤ coverCap') (hL : L ≤ L') :
    NormalizedPolynomialTwist X Y periodCap' coverCap' L' :=
  { W with
    modulus_bound := W.modulus_bound.trans hp
    cover_bound := W.cover_bound.trans hc
    smooth_lipschitz := W.smooth_lipschitz.weaken hL }

@[simp] theorem eval_mono (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    {periodCap' coverCap' : ℝ} {L' : ℝ≥0}
    (hp : periodCap ≤ periodCap') (hc : coverCap ≤ coverCap') (hL : L ≤ L')
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.mono hp hc hL).eval N p u = W.eval N p u := rfl

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped NNReal Classical

variable {X : Type*} {m : ℕ} {J : Fin m → Type*}

theorem physicalGridFactorInput_subtractConstant (period : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ) (t : X → ℝ) :
    physicalGridFactorInput period (fun j => subtractConstant (c j) (p j)) t =
      physicalGridFactorInput period p t -
        (fun a : Σ j, J j => ((c a.1 a.2 / period : ℝ) : UnitAddCircle)) := by
  funext a
  simp only [physicalGridFactorInput, eval_subtractConstant, Pi.sub_apply, sub_div,
    AddCircle.coe_sub]

namespace NormalizedPolynomialTwist

variable [Fintype X] [∀ j, Fintype (J j)]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def shiftConstant
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) :
    NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L :=
  { W with
    smooth := fun z => W.smooth (z.1, z.2 -
      (fun a : Σ j, J j => ((c a.1 a.2 / W.cover : ℝ) : UnitAddCircle)))
    smooth_bound := fun z => W.smooth_bound _
    smooth_lipschitz := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [Prod.dist_eq, dist_sub_right] using W.smooth_lipschitz.dist_le_mul
        (x.1, x.2 - (fun a : Σ j, J j => ((c a.1 a.2 / W.cover : ℝ) : UnitAddCircle)))
        (y.1, y.2 - (fun a : Σ j, J j => ((c a.1 a.2 / W.cover : ℝ) : UnitAddCircle))) }

@[simp] theorem shiftConstant_modulus
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) : (W.shiftConstant c).modulus = W.modulus := rfl

@[simp] theorem shiftConstant_cover
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) : (W.shiftConstant c).cover = W.cover := rfl

@[simp] theorem shiftConstant_mask
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) : (W.shiftConstant c).mask = W.mask := rfl

@[simp] theorem eval_shiftConstant
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) (N : X → ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.shiftConstant c).eval N p u =
      W.eval N (fun j => subtractConstant (c j) (p j)) u := by
  simp only [eval, shiftConstant, physicalGridFactorInput_subtractConstant]
  rfl

end NormalizedPolynomialTwist

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra NativeSampleModel.topology NativeSampleModel.topologicalAdd NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

namespace VectorPolynomial.NormalizedPolynomialTwist

variable {X Y : Type*} [Fintype X] [Fintype Y]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def scaleMask
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (c : ℂ) (hc : ‖c‖ ≤ 1) : NormalizedPolynomialTwist X Y periodCap coverCap L :=
  { W with
    mask := fun z => c * W.mask z
    mask_bound := fun z => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (W.mask_bound z) }

@[simp] theorem scaleMask_eval {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ℂ) (hc : ‖c‖ ≤ 1) (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.scaleMask c hc).eval N poly u = c * W.eval N poly u := by
  simp only [eval, scaleMask, mul_assoc]
  rfl

end VectorPolynomial.NormalizedPolynomialTwist

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

theorem subtractConstant_neg_cancel {X R V : Type*}
    [CommRing R] [AddCommGroup V] [Module R V]
    (c : V) (p : VectorPolynomial X R V) :
    subtractConstant (-c) (subtractConstant c p) = p := by
  simp [subtractConstant, monomial, TensorProduct.tmul_neg]

namespace NormalizedPolynomialTwist

variable {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*}
variable [∀ j, Fintype (J j)] {periodCap coverCap : ℝ} {L : ℝ≥0}

@[simp] theorem eval_shiftConstant_neg_subtractConstant
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.shiftConstant (fun j => -c j)).eval N
      (fun j => subtractConstant (c j) (poly j)) u = W.eval N poly u := by
  rw [eval_shiftConstant]
  simp only [subtractConstant_neg_cancel]

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open scoped BigOperators NNReal

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistNativeApproximation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_native_approximation
    {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {periodCap coverCap : ℝ} {lip : ℝ≥0}
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (μ : FiniteProbabilityWeights Ω)
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (w : X → ℕ) (degree : ℕ) (complexity : ℝ)
    {K C cap beta tau εtail : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hcap : 0 < cap)
    (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ u, ‖signal u‖ ≤ 1) →
      (∀ u, u ∉ integerBox N → signal u = 0) →
      (tau / cap ^ 2) / max 1 (K * (2 * C) / tau) ≤
        sampledSliceSeminorm μ site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree complexity
          (fun u : integerBox N => u.val) G) ∧
        beta ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun u => signal u.val)
          (fun u => star (W.eval N poly u.val) * G u)‖)
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass (μ.siteLaw physical) C ≤ εtail)
    (input : integerBox N → ℂ) (hinput : ∀ u, ‖input u‖ ≤ cap) :
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (Q : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, Q i ∈ twistedNativeSampleFunctions w degree complexity
        (fun u : integerBox N => u.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
          (u : integerBox N) => W.eval N poly u.val)) ∧
      input = (∑ i, coeff i • Q i) + err ∧
      (∑ i, |coeff i|) ≤ 2 / beta ∧
      sampledSliceSeminorm μ physical slices tests err ≤
        2 * tau + 2 * K * (cap + 2 / beta) * εtail ∧
      (nterms : ℝ) ≤ 1 + 4 * (K * (2 * C)) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let : Nonempty (integerBox N) := (integerBox_nonempty N).to_subtype
  have htwist (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
      (u : integerBox N) : ‖W.eval N poly u.val‖ ≤ 1 := W.norm_eval_le N poly u.val
  have hdetector (g : integerBox N → ℂ) (hg : ∀ u, ‖g u‖ ≤ 1)
      (hlarge : (tau / cap ^ 2) / max 1 (K * (2 * C) / tau) ≤
        sampledSliceSeminorm μ physical slices tests g) :
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree complexity
          (fun u : integerBox N => u.val) G) ∧
        beta ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation g
          (fun u => star (W.eval N poly u.val) * G u)‖ := by
    let ext := finiteSiteExtension (Subtype.val : integerBox N → X → ℤ) g
    let signal := zeroExtendFinset (integerBox N) ext
    have hsignal (u) : ‖signal u‖ ≤ 1 :=
      zeroExtendFinset_norm_le_one (integerBox N) ext
        (fun u _ => finiteSiteExtension_norm_le _ g hg u) u
    have hzero (u) (hu : u ∉ integerBox N) : signal u = 0 := by
      simp only [signal, zeroExtendFinset, if_neg hu]
    have hvalue (u : integerBox N) : signal u.val = g u := by
      simpa only [signal, zeroExtendFinset, if_pos u.property, ext] using
        finiteSiteExtension_apply Subtype.val Subtype.val_injective g u
    have hseminorm := sampledSliceSeminorm_congr_values μ site physical slices tests
      hsize htests signal g (fun z t => by rw [← hphysical z t]; exact hvalue _)
    obtain ⟨W, G, hG, hc⟩ := hdetect signal hsignal hzero
      (hseminorm.symm ▸ hlarge)
    exact ⟨W, G, hG, by simpa only [hvalue] using hc⟩
  have hr (u : integerBox N) : 0 <
      (FiniteProbabilityWeights.uniformFinset (integerBox N)
        (integerBox_nonempty N)).weight u := by
    change 0 < (Fintype.card (integerBox N) : ℝ)⁻¹
    positivity
  exact exists_sampled_native_model μ physical slices tests
    (FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)) hr
    w degree complexity (fun u : integerBox N => u.val)
    (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
      (u : integerBox N) => W.eval N poly u.val)
    htwist hK hC hcap hbeta htau hsize htests hdetector hexcess input hinput

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedErrorInterpolation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedGridJetScale : ℝ :=
  ∏ a : {a // grid a}, (allocatedGridAxisScale B U b S a : ℝ) ^ Fintype.card (O a.val.1)

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeGlobalErrorSplitting
namespace OAI

section

namespace Erdos3.NativeTwoVariableSplit

open scoped TensorProduct BigOperators

attribute [local instance] NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem exists_fixed_correlating_term {G X : Type*} [Fintype X] [Nonempty X]
    {s d : ℕ} {p epsilon rho : ℝ} {u : (Fin 2 → ℤ) → ℂ}
    (R : NativeTwoVariableSplit s d p epsilon u) (H : Finset G) (hH : H.Nonempty)
    (sample : G → X → Fin 2 → ℤ) (f : G → X → ℂ)
    (hrho : 0 < rho) (hepsilon : epsilon ≤ rho / 2)
    (hf : ∀ h ∈ H, ∀ x, ‖f h x‖ ≤ 1)
    (hcorr : ∀ h ∈ H, rho ≤ ‖𝔼 x, f h x * star (u (sample h x))‖) :
    ∃ (j : Fin R.count) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-p) * (H.card : ℝ) ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, rho / (2 * Real.exp p) ≤
        ‖𝔼 x, f h x * star ((R.test false j).eval (sample h x) *
          (R.test true j).eval (sample h x))‖ := by
  classical
  let rel (h : G) (_ : Unit) (j : Fin R.count) : Prop :=
    rho / (2 * Real.exp p) ≤
      ‖𝔼 x, f h x * star ((R.test false j).eval (sample h x) *
        (R.test true j).eval (sample h x))‖
  have hcount : (Fintype.card (Fin R.count) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using R.count_bound
  have hchoice : ∀ h ∈ H, ∀ i, ∃ j, rel h i j := by
    intro h hh _
    apply exists_correlating_summand (J := Fin R.count) Finset.univ_nonempty
      (f h) (fun x => u (sample h x))
      (fun j x => (R.test false j).eval (sample h x) * (R.test true j).eval (sample h x))
      hrho (Real.exp_pos p) hcount (fun x _ => hf h hh x) _ (hcorr h hh)
    intro x _
    rw [norm_sub_rev]
    exact (R.approximation (sample h x)).trans hepsilon
  obtain ⟨j, S, hsub, hS, hsize, hfixed⟩ :=
    exists_large_fixed_choices H hH rel hchoice hcount
  refine ⟨j (), S, hsub, hS, ?_, fun h hh => hfixed h hh ()⟩
  simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize

end Erdos3.NativeTwoVariableSplit

end

section

namespace Erdos3.NativeVectorEquivalence

open scoped TensorProduct BigOperators

attribute [local instance] NativeNilsequenceExpansion.lie NativeNilsequenceExpansion.algebra NativeNilsequenceExpansion.topology NativeNilsequenceExpansion.topologicalAdd NativeNilsequenceExpansion.continuousSMul NativeNilsequenceExpansion.hausdorff NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem transfer_correlation {I J K : Type*} [Fintype J] [Fintype K]
    {s N : ℕ} [NeZero N] {p : ℝ} {chi : J → ZMod N → ℂ} {chi' : K → ZMod N → ℂ}
    (E : NativeVectorEquivalence s N p chi chi')
    (hunit : ∀ x, ∑ k, ‖chi' k x‖ ^ 2 = 1) (f : I → ZMod N → ℂ)
    (W : NativeVectorCorrelation s N p
      (fun ij : I × J => fun x => f ij.1 x * star (chi ij.2 x))) :
    Nonempty (NativeVectorCorrelation s N (productNiltestBudget (3 * p + 4))
      (fun ik : I × K => fun x => f ik.1 x * star (chi' ik.2 x))) := by
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let R (k : K) := Classical.choice (E.expansion W.coordinate.2 k)
  let psi (k : K) (a : Fin (R k).count) (x : ZMod N) : ℂ :=
    star (((R k).test a).evalCyclic N (fun _ => x))
  have hExpansion (k : K) (x : ZMod N) (_hx : x ∈ (Finset.univ : Finset (ZMod N))) :
      star (chi W.coordinate.2 x) * star (star (chi' k x)) =
        ∑ a, star ((R k).coefficient a) * psi k a x := by
    have h := congrArg star ((R k).eval x)
    simpa only [psi, star_sum, star_mul, star_star, mul_comm] using h
  have hCorr : Real.exp (-p) ≤
      ‖𝔼 x ∈ (Finset.univ : Finset (ZMod N)),
        (f W.coordinate.1 x * star (W.test.evalCyclic N (fun _ => x))) *
          star (chi W.coordinate.2 x)‖ := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using W.correlation
  obtain ⟨k, a, hka⟩ := exists_unit_expansion_correlation Finset.univ
    (fun x => f W.coordinate.1 x * star (W.test.evalCyclic N (fun _ => x)))
    (fun x => star (chi W.coordinate.2 x)) (fun k x => star (chi' k x))
    (fun k a => star ((R k).coefficient a)) psi
    (fun x _ => by simpa only [norm_star] using hunit x) hExpansion
    (Real.exp_pos (-p)) (Real.exp_pos p) (Real.exp_pos p) E.right_dimension
    (fun k => by simpa only [norm_star] using (R k).cost) hCorr
  have hfrac : Real.exp (-p) / (Real.exp p * Real.exp p) = Real.exp (-(3 * p)) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  rw [hfrac] at hka
  have hpq : p ≤ 3 * p + 4 := by linarith
  let g (ik : I × K) (x : ZMod N) := f ik.1 x * star (chi' ik.2 x)
  let T := (R k).test a
  have hW : NativeVectorCorrelation s N (3 * p + 4)
      (fun iu : (I × K) × Unit => fun x => g iu.1 x * star (T.evalCyclic N (fun _ => x))) := {
    L := W.L
    dim := W.dim
    model := W.model
    test := W.test
    complexity := W.complexity.mono hpq
    coordinate := ((W.coordinate.1, k), ())
    correlation := by
      have h := (Real.exp_le_exp.mpr (show -(3 * p + 4) ≤ -(3 * p) by linarith)).trans hka
      simpa only [g, T, psi, mul_assoc, mul_left_comm, mul_comm] using h
  }
  exact NativeVectorCorrelation.exists_absorb ((R k).model a) (fun _ : Unit => T) g
    (by linarith : 2 ≤ 3 * p + 4) (fun _ => ((R k).complexity a).mono hpq) hW

end Erdos3.NativeVectorEquivalence

end

section

namespace Erdos3.NativeNilsequenceExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem absorb_correlation {I : Type*} {s N : ℕ} [NeZero N] {p : ℝ}
    {eta : ZMod N → ℂ} (E : NativeNilsequenceExpansion s N p eta)
    (f : I → ZMod N → ℂ)
    (W : NativeVectorCorrelation s N p (fun i x => f i x * star (eta x))) :
    Nonempty (NativeVectorCorrelation s N (productNiltestBudget (3 * p + 4)) f) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hdim : (Fintype.card Unit : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_unit, Nat.cast_one] using Real.one_le_exp hp
  let V : NativeVectorEquivalence s N p (fun _ : Unit => eta) (fun _ : Unit => fun _ => 1) := {
    left_dimension := hdim
    right_dimension := hdim
    expansion := fun _ _ => by
      simpa only [star_one, mul_one] using (show Nonempty (NativeNilsequenceExpansion s N p eta) from ⟨E⟩) }
  let W' : NativeVectorCorrelation s N p
      (fun iu : I × Unit => fun x => f iu.1 x * star (eta x)) :=
    { W with coordinate := (W.coordinate, ()) }
  obtain ⟨R⟩ := V.transfer_correlation (fun _ => by simp) f W'
  exact ⟨{ R with
    coordinate := R.coordinate.1
    correlation := by simpa only [star_one, mul_one] using R.correlation }⟩

end Erdos3.NativeNilsequenceExpansion

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def normalizedErrorCorrelator (b : ℝ) (m : ZMod N → ZMod N → ℂ)
    (h x : ZMod N) : ℂ :=
  multiplicativeDerivative f h x * star (m h x * W.normalizedLower b h x)

theorem normalizedErrorCorrelator_norm {b : ℝ} (hpb : p ≤ b)
    (hf : ∀ x, ‖f x‖ ≤ 1) (m : ZMod N → ZMod N → ℂ) (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (h x : ZMod N) : ‖W.normalizedErrorCorrelator b m h x‖ ≤ 1 := by
  simp only [normalizedErrorCorrelator, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (by positivity)
    (multiplicativeDerivative_norm_le_one f hf h x)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hm h x)).trans
        (W.normalizedLower_norm hpb h x))

theorem normalizedErrorCorrelator_correlation {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} {D : RationalFilteredNilmanifold L s d}
    (T : D.Niltest (fun _ : Fin 2 => 1)) (b : ℝ) (m : ZMod N → ZMod N → ℂ)
    (h : ZMod N) (hh : h ∈ W.shifts)
    (hcorr : Real.exp (-b) ≤ ‖𝔼 x, multiplicativeDerivative f h x * star
      (m h x * (W.selectedWitness ⟨h, hh⟩).test.evalCyclic N (fun _ => x) *
        T.eval ![(h.val : ℤ), (x.val : ℤ)])‖) :
    Real.exp (-(3 * b)) ≤ ‖𝔼 x, W.normalizedErrorCorrelator b m h x *
      star ((T.expNormalize b).eval ![(h.val : ℤ), (x.val : ℤ)])‖ := by
  have hc : (Real.exp (-(2 * b)) : ℂ) = (Real.exp (-b) : ℂ) * (Real.exp (-b) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring_nf
  have hmean : (𝔼 x, W.normalizedErrorCorrelator b m h x *
        star ((T.expNormalize b).eval ![(h.val : ℤ), (x.val : ℤ)])) =
      (Real.exp (-(2 * b)) : ℂ) * (𝔼 x, multiplicativeDerivative f h x * star
        (m h x * (W.selectedWitness ⟨h, hh⟩).test.evalCyclic N (fun _ => x) *
          T.eval ![(h.val : ℤ), (x.val : ℤ)])) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    rw [normalizedErrorCorrelator, W.normalizedLower_of_mem b h hh]
    simp only [RationalFilteredNilmanifold.Niltest.expNormalize,
      RationalFilteredNilmanifold.Niltest.scaleComplex_eval,
      RationalFilteredNilmanifold.Niltest.scaleComplex_evalCyclic, hc,
      star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [hmean, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ = Real.exp (-(2 * b)) * Real.exp (-b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

def GlobalErrorSplittingStatement (s C : ℕ) : Prop :=
    ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f)
      {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d}
      (T : D.Niltest (fun _ : Fin 2 => 1)) (b : ℝ),
      2 ≤ b → p ≤ b → T.ComplexityLE b →
      ∀ (H : Finset (ZMod N)) (hsub : H ⊆ W.shifts), H.Nonempty →
      ∀ m : ZMod N → ZMod N → ℂ, (∀ h x, ‖m h x‖ ≤ 1) → (∀ x, ‖f x‖ ≤ 1) →
      (∀ h (hh : h ∈ H), Real.exp (-b) ≤
        ‖𝔼 x, multiplicativeDerivative f h x * star
          (m h x * (W.selectedWitness ⟨h, hsub hh⟩).test.evalCyclic N (fun _ => x) *
            T.eval ![(h.val : ℤ), (x.val : ℤ)])‖) →
      ∃ (weight : ZMod N → ℂ) (S : Finset (ZMod N)),
        (∀ x, ‖weight x‖ ≤ 1) ∧ S ⊆ H ∧ S.Nonempty ∧
        Real.exp (-((b + C) ^ C)) * (H.card : ℝ) ≤ (S.card : ℝ) ∧
        ∀ h ∈ S, Nonempty (NativeVectorCorrelation (s - 1) N ((b + C) ^ C)
          (fun _ : Unit => fun x => multiplicativeDerivative f h x * star (m h x * weight x)))

end Erdos3

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem absorb_split_term {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (W : NativeCorrelationStructure s r N p f)
    {d : ℕ} {B epsilon : ℝ} {u : (Fin 2 → ℤ) → ℂ}
    (R : NativeTwoVariableSplit s d B epsilon u) (j : Fin R.count)
    (m : ZMod N → ZMod N → ℂ) (weight : ZMod N → ℂ)
    (h : ZMod N) (hmem : h ∈ W.shifts) {b F Q : ℝ}
    (hpb : p ≤ b) (hbQ : b ≤ Q) (hFQ : F ≤ Q)
    (E : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) F
      (fun x => (R.test true j).eval ![(h.val : ℤ), x ()]))
    (hfirst : ∀ x : ZMod N, (R.test false j).eval ![(h.val : ℤ), (x.val : ℤ)] = weight x)
    (hcorr : Real.exp (-Q) ≤
      ‖𝔼 x, W.normalizedErrorCorrelator b m h x * star
        ((R.test false j).eval ![(h.val : ℤ), (x.val : ℤ)] *
          (R.test true j).eval ![(h.val : ℤ), (x.val : ℤ)])‖) :
    Nonempty (NativeVectorCorrelation (s - 1) N (productNiltestBudget (3 * Q + 4))
      (fun _ : Unit => fun x => multiplicativeDerivative f h x * star (m h x * weight x))) := by
  let U := (W.selectedWitness ⟨h, hmem⟩).test.expNormalize b
  have hU : U.ComplexityLE b :=
    (W.selectedWitness ⟨h, hmem⟩).test.expNormalize_complexity
      ((W.selectedWitness ⟨h, hmem⟩).complexity.mono hpb)
  let g (_ : Unit) (x : ZMod N) := multiplicativeDerivative f h x * star (m h x * weight x)
  let Z : NativeVectorCorrelation (s - 1) N Q
      (fun z : Unit => fun x => g z x * star ((R.test true j).eval ![(h.val : ℤ), (x.val : ℤ)])) := {
    L := (W.selectedWitness ⟨h, hmem⟩).L
    dim := (W.selectedWitness ⟨h, hmem⟩).dim
    model := (W.selectedWitness ⟨h, hmem⟩).model
    test := U
    complexity := hU.mono hbQ
    coordinate := ()
    correlation := by
      simpa only [g, normalizedErrorCorrelator,
        W.normalizedLower_of_mem b h hmem, hfirst, U, star_mul,
        mul_assoc, mul_left_comm, mul_comm] using hcorr }
  exact ((E.toCyclic N).mono hFQ).absorb_correlation g Z

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem exists_split_global_error (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ GlobalErrorSplittingStatement s C := by
  obtain ⟨a, _, hsplit⟩ := exists_totalDegree_niltest_splitting s 2
  obtain ⟨c, _, hfreeze⟩ := NativeTwoVariableSplit.exists_second_expansion_budget s
  obtain ⟨C, hC, hbudget⟩ := exists_global_error_budget a c
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W L _ _ _ _ _ _ d D T b hb hpb hT H hsub hH m hm hf hcorr
  have hb0 : 0 ≤ b := by linarith only [hb]
  let B := (b + a) ^ a
  let F := (B + c) ^ c
  let Q := 3 * b + B + F + 3
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hbQ : b ≤ Q := by dsimp [Q]; linarith only [hb0, hB, hF]
  have hFQ : F ≤ Q := by dsimp [Q]; linarith only [hb0, hB]
  have hcQ : 3 * b + B + 1 ≤ Q := by dsimp [Q]; linarith only [hF]
  have hcostB : B ≤ (b + C) ^ C := (hbudget b hb0).1
  have hcost : productNiltestBudget (3 * Q + 4) ≤ (b + C) ^ C := (hbudget b hb0).2
  let epsilon := Real.exp (-(3 * b + 1))
  have hscale : 1 / epsilon ≤ Real.exp ((b + 2) ^ 2) := by
    dsimp [epsilon]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith only [hb0, sq_nonneg b]
  have hR : Nonempty (NativeTwoVariableSplit s d B epsilon (T.expNormalize b).eval) :=
    hsplit (T.expNormalize b) (T.expNormalize_complexity hT)
      (T.expNormalize_norm hT) epsilon (Real.exp_pos _) hscale
  obtain ⟨R⟩ := hR
  have hepsilon : epsilon ≤ Real.exp (-(3 * b)) / 2 := by
    simpa only [epsilon, show -(3 * b + 1) = -(3 * b) - 1 by ring] using
      exp_sub_one_le_half_exp (-(3 * b))
  obtain ⟨j, S, hSH, hS, hsize, hterm⟩ := R.exists_fixed_correlating_term H hH
    (fun (h x : ZMod N) => ![(h.val : ℤ), (x.val : ℤ)]) (W.normalizedErrorCorrelator b m)
    (Real.exp_pos _) hepsilon
    (fun h _ x => W.normalizedErrorCorrelator_norm hpb hf m hm h x)
    (fun h hh => W.normalizedErrorCorrelator_correlation T b m h (hsub hh) (hcorr h hh))
  let weight (x : ZMod N) := (R.test false j).eval ![0, (x.val : ℤ)]
  have hweight (x : ZMod N) : ‖weight x‖ ≤ 1 :=
    ((R.test false j).norm_eval_le _).trans
      (show ((R.test false j).normBound : ℝ) ≤ 1 from R.test_norm false j)
  have hfirst (h x : ZMod N) :
      (R.test false j).eval ![(h.val : ℤ), (x.val : ℤ)] = weight x :=
    R.first_eval_eq j _ _ rfl
  have hsmall : Real.exp (-(3 * b + B + 1)) ≤ Real.exp (-(3 * b)) / (2 * Real.exp B) := by
    calc
      _ = Real.exp (-(3 * b + B) - 1) := by congr 1; ring
      _ ≤ Real.exp (-(3 * b + B)) / 2 := exp_sub_one_le_half_exp _
      _ = _ := by rw [show -(3 * b + B) = -(3 * b) - B by ring, Real.exp_sub]; ring
  refine ⟨weight, S, hweight, hSH, hS, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcostB))
      (Nat.cast_nonneg H.card)).trans hsize
  · intro h hh
    let hmem : h ∈ W.shifts := hsub (hSH hh)
    have hE : ∃ E : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) F
        (fun x => (R.test true j).eval ![(h.val : ℤ), x ()]), E.count = 1 :=
      hfreeze R j (h.val : ℤ)
    obtain ⟨E, _⟩ := hE
    have hz := (Real.exp_le_exp.mpr (neg_le_neg hcQ)).trans (hsmall.trans (hterm h hh))
    obtain ⟨V⟩ := W.absorb_split_term R j m weight h hmem hpb hbQ hFQ E (hfirst h) hz
    exact ⟨V.mono hcost⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeFiniteSumCoordinate
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_finite_sum_coordinate_equivalence {σ : Type*}
    [Fintype σ] [DecidableEq σ] [Nonempty σ] (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p)
      (i : σ), NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun k (x : (σ ⊕ Fin (n + 1)) → ℤ) => W.eval k (finiteSumCoordinateInput i x))
        (fun a : Fin (n + 1) → Fin W.outputDim => fun x =>
          ∏ j, W.eval (a j) (finiteTermCoordinateInput i j x)) := by
  induction n with
  | zero =>
      obtain ⟨C, hC, hself⟩ := exists_integer_self_equivalence (σ := σ)
      refine ⟨C, hC, ?_⟩
      intro p W i
      have E := (hself W).linearPullbackHom (finiteTermCoordinateHom i (0 : Fin 1))
      apply E.of_coordinate_maps _ _ id (fun a => a 0) _ _ E.left_dimension _ le_rfl
      · intro k x
        rw [finiteSumCoordinateInput_one]
        rfl
      · intro a x
        rw [Fin.prod_univ_one]
        rfl
      · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.zero_add, pow_one] using E.right_dimension
  | succ n ih =>
      obtain ⟨A, _, hprevious⟩ := ih
      obtain ⟨B, _, hadd⟩ := exists_multilinearity_equivalence (σ := σ)
      obtain ⟨D, _, hself⟩ := exists_integer_self_equivalence (σ := σ)
      obtain ⟨F, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
      obtain ⟨G, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
      let X : Polynomial ℕ := Polynomial.X
      let R := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B +
        (X + Polynomial.C D) ^ D
      let Q := (R + (R + Polynomial.C F) ^ F + Polynomial.C G) ^ G
      obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
        (Q + Polynomial.C (n + 2) * X + X)
      refine ⟨C, hC, ?_⟩
      intro p W i
      have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
      let r := (p + A) ^ A + (p + B) ^ B + (p + D) ^ D
      let t := (r + F) ^ F
      let q := (r + t + G) ^ G
      have hA : 0 ≤ (p + A) ^ A := by positivity
      have hB : 0 ≤ (p + B) ^ B := by positivity
      have hD : 0 ≤ (p + D) ^ D := by positivity
      have hr : 0 ≤ r := by dsimp [r]; linarith
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have hAr : (p + A) ^ A ≤ r := by dsimp [r]; linarith
      have hBr : (p + B) ^ B ≤ r := by dsimp [r]; linarith
      have hDr : (p + D) ^ D ≤ r := by dsimp [r]; linarith
      have hsum : q + (n + 2 : ℕ) * p + p ≤ (p + C) ^ C := by
        simpa [X, R, Q, r, t, q, Polynomial.eval₂_pow] using hbudget p hp
      have hnp : 0 ≤ (n + 2 : ℕ) * p := mul_nonneg (Nat.cast_nonneg _) hp
      have hqC : q ≤ (p + C) ^ C := by linarith
      have hpC : p ≤ (p + C) ^ C := by linarith
      have hnC : (n + 2 : ℕ) * p ≤ (p + C) ^ C := by linarith
      let tailMap : (σ ⊕ Fin (n + 1)) → (((σ ⊕ Fin (n + 2)) → ℤ) →+ ℤ) := fun j =>
        match j with
        | Sum.inl j =>
          { toFun := fun x => x (Sum.inl j)
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        | Sum.inr a =>
          { toFun := fun x => x (Sum.inr a.succ)
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
      let addMap : Option σ → (((σ ⊕ Fin (n + 2)) → ℤ) →+ ℤ) := fun j =>
        match j with
        | none =>
          { toFun := fun x => ∑ a : Fin (n + 1), x (Sum.inr a.succ)
            map_zero' := by simp
            map_add' := fun x y => by
              simp only [Pi.add_apply, Finset.sum_add_distrib] }
        | some j => finiteTermCoordinateHom i 0 j
      have hleft (x : (σ ⊕ Fin (n + 2)) → ℤ) :
          coordinateAdditionInputs i (fun j => addMap j x) 0 = finiteSumCoordinateInput i x := by
        rw [coordinateAdditionInputs_sum]
        change Function.update (finiteTermCoordinateInput i 0 x) i
          (finiteTermCoordinateInput i 0 x i + ∑ a : Fin (n + 1), x (Sum.inr a.succ)) = _
        simp only [finiteTermCoordinateInput, finiteSumCoordinateInput,
          Function.update_self, Function.update_idem]
        congr 1
        exact (Fin.sum_univ_succ (fun a : Fin (n + 2) => x (Sum.inr a))).symm
      have hfirst (x : (σ ⊕ Fin (n + 2)) → ℤ) :
          coordinateAdditionInputs i (fun j => addMap j x) 1 = finiteTermCoordinateInput i 0 x := rfl
      have htail (x : (σ ⊕ Fin (n + 2)) → ℤ) :
          coordinateAdditionInputs i (fun j => addMap j x) 2 =
            finiteSumCoordinateInput i (fun j => tailMap j x) := by
        rw [coordinateAdditionInputs_right]
        change Function.update (finiteTermCoordinateInput i 0 x) i
          (∑ a : Fin (n + 1), x (Sum.inr a.succ)) = _
        simp only [finiteTermCoordinateInput, finiteSumCoordinateInput, Function.update_idem]
        rfl
      have E₀ : NativeIntegerVectorEquivalence (Fintype.card σ - 1) r
          (fun k x => W.eval k (finiteSumCoordinateInput i x))
          (fun a : Fin W.outputDim × Fin W.outputDim => fun x =>
            W.eval a.1 (finiteTermCoordinateInput i 0 x) *
              W.eval a.2 (finiteSumCoordinateInput i (fun j => tailMap j x))) := by
        have E := ((hadd W i).linearPullbackHom addMap).mono hBr
        simpa only [coordinateSumVector, coordinateTensorVector, hleft, hfirst, htail] using E
      have Efirst := ((hself W).linearPullbackHom
        (finiteTermCoordinateHom i (0 : Fin (n + 2)))).mono hDr
      have Etail := ((hprevious W i).linearPullbackHom tailMap).mono hAr
      have E₂ := htensor hr Efirst Etail
      have hunit (x : (σ ⊕ Fin (n + 2)) → ℤ) :
          ∑ a : Fin W.outputDim × Fin W.outputDim,
            ‖W.eval a.1 (finiteTermCoordinateInput i 0 x) *
              W.eval a.2 (finiteSumCoordinateInput i (fun j => tailMap j x))‖ ^ 2 = 1 := by
        simp only [Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum,
          W.unit_eval, mul_one]
      have H := htrans (add_nonneg hr ht) (E₀.mono (le_add_of_nonneg_right ht))
        (E₂.mono (le_add_of_nonneg_left hr)) hunit
      have hdim : (Fintype.card (Fin (n + 2) → Fin W.outputDim) : ℝ) ≤
          Real.exp ((p + C) ^ C) := by
        simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
        calc
          _ ≤ Real.exp p ^ (n + 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound _
          _ = Real.exp ((n + 2 : ℕ) * p) := (Real.exp_nat_mul p (n + 2)).symm
          _ ≤ _ := Real.exp_le_exp.mpr hnC
      apply H.of_coordinate_maps _ _ id (fun a => (a 0, fun j => a j.succ))
        (fun _ _ => rfl) _ _ hdim hqC
      · intro a x
        rw [Fin.prod_univ_succ]
        rfl
      · simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpC)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBinaryAssignments
namespace OAI

section

namespace Erdos3

variable {σ I : Type*} [DecidableEq σ]

noncomputable def firstTranslationCoordinate : (l : List σ) → BinaryTensorIndex I l.length → I
  | [], a => a
  | _ :: l, a => firstTranslationCoordinate l a.1

noncomputable def translationExpansionRemainder (f : I → (σ → ℤ) → ℂ) :
    (l : List σ) → BinaryTensorIndex I l.length → (Option σ → ℤ) → ℂ
  | [], _, _ => 1
  | i :: l, a, x => translationExpansionRemainder f l a.1 x *
      coordinateTranslationExpansion f l a.2 (coordinateReplaceInput i x)

theorem coordinateTranslationExpansion_factor (f : I → (σ → ℤ) → ℂ)
    (l : List σ) (a : BinaryTensorIndex I l.length) (x : Option σ → ℤ) :
    coordinateTranslationExpansion f l a x =
      f (firstTranslationCoordinate l a) (fun j => x (some j)) *
        translationExpansionRemainder f l a x := by
  induction l generalizing x with
  | nil => exact (mul_one _).symm
  | cons i l ih =>
    change coordinateTranslationExpansion f l a.1 x *
      coordinateTranslationExpansion f l a.2 (coordinateReplaceInput i x) = _
    rw [ih]
    exact mul_assoc _ _ _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem prod_fin_succ_function {n m : ℕ} (f : (Fin (n + 1) → Fin m) → ℂ) :
    (∏ v, f v) = ∏ a : Fin m, ∏ v : Fin n → Fin m, f (Fin.cons a v) := by
  calc
    _ = ∏ a : Fin m × (Fin n → Fin m), f (Fin.cons a.1 a.2) :=
      ((Fin.consEquiv (fun _ : Fin (n + 1) => Fin m)).prod_comp f).symm
    _ = _ := Fintype.prod_prod_type _

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

variable {σ I : Type*} [DecidableEq σ] {n : ℕ}

def finiteChoiceCoordinateInput (l : List σ) (x : (Fin (n + 1) × σ) → ℤ) (j : σ) : ℤ :=
  if j ∈ l then ∑ a : Fin (n + 1), x (a, j) else x (0, j)

def finiteChoiceCoordinateHom (l : List σ) (j : σ) : (((Fin (n + 1) × σ) → ℤ) →+ ℤ) where
  toFun x := finiteChoiceCoordinateInput l x j
  map_zero' := by simp [finiteChoiceCoordinateInput]
  map_add' x y := by
    simp only [finiteChoiceCoordinateInput, Pi.add_apply, Finset.sum_add_distrib]
    split_ifs <;> rfl

def finiteChoiceReplaceIndex (i : σ) (a : Fin (n + 1)) (j : Fin (n + 1) × σ) : Fin (n + 1) × σ :=
  if j = (0, i) then (a, i) else j

def finiteChoiceReplaceInput (i : σ) (a : Fin (n + 1))
    (x : (Fin (n + 1) × σ) → ℤ) : (Fin (n + 1) × σ) → ℤ :=
  fun j => x (finiteChoiceReplaceIndex i a j)

theorem finiteChoiceCoordinateInput_replace (l : List σ) (i : σ) (hi : i ∉ l)
    (a : Fin (n + 1)) (x : (Fin (n + 1) × σ) → ℤ) :
    finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i a x) =
      Function.update (finiteChoiceCoordinateInput l x) i (x (a, i)) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [finiteChoiceCoordinateInput, finiteChoiceReplaceInput, finiteChoiceReplaceIndex, hi]
  · simp [finiteChoiceCoordinateInput, finiteChoiceReplaceInput, finiteChoiceReplaceIndex, hj]

theorem finiteChoiceCoordinateInput_cons (l : List σ) (i : σ)
    (x : (Fin (n + 1) × σ) → ℤ) :
    finiteChoiceCoordinateInput (i :: l) x = Function.update (finiteChoiceCoordinateInput l x) i
      (∑ a : Fin (n + 1), x (a, i)) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [finiteChoiceCoordinateInput]
  · simp [finiteChoiceCoordinateInput, hj]

def finiteChoiceLeafInput : (l : List σ) → (Fin l.length → Fin (n + 1)) →
    ((Fin (n + 1) × σ) → ℤ) → σ → ℤ
  | [], _, x => fun j => x (0, j)
  | i :: l, v, x => finiteChoiceLeafInput l (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x)

noncomputable def finiteChoiceExpansion (f : I → (σ → ℤ) → ℂ) (l : List σ)
    (a : (Fin l.length → Fin (n + 1)) → I) (x : (Fin (n + 1) × σ) → ℤ) : ℂ :=
  ∏ v : Fin l.length → Fin (n + 1), f (a v) (finiteChoiceLeafInput l v x)

theorem finiteChoiceExpansion_cons (f : I → (σ → ℤ) → ℂ) (l : List σ) (i : σ)
    (a : (Fin (i :: l).length → Fin (n + 1)) → I) (x : (Fin (n + 1) × σ) → ℤ) :
    finiteChoiceExpansion f (i :: l) a x = ∏ j : Fin (n + 1),
      finiteChoiceExpansion f l (fun v => a (Fin.cons j v)) (finiteChoiceReplaceInput i j x) := by
  simp only [finiteChoiceExpansion, List.length_cons, prod_fin_succ_function, finiteChoiceLeafInput,
    Fin.cons_zero, Fin.tail_cons]

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_translation_expansion_equivalence {σ : Type*}
    [Fintype σ] [DecidableEq σ] [Nonempty σ] (l : List σ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p),
      l.Nodup → NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun k x => W.eval k (coordinateTranslatedInput l x))
        (coordinateTranslationExpansion W.eval l) := by
  induction l with
  | nil =>
    obtain ⟨C, hC, hself⟩ := exists_integer_self_equivalence (σ := σ)
    refine ⟨C, hC, ?_⟩
    intro p W _
    have E := (hself W).coordinatePullback (some : σ → Option σ)
    have hinput (x : Option σ → ℤ) :
        coordinateTranslatedInput [] x = fun j => x (some j) := by
      funext j
      simp [coordinateTranslatedInput]
    simp only [hinput, coordinateTranslationExpansion]
    convert E using 1 <;> rfl
  | cons i l ih =>
    obtain ⟨a, _, hprevious⟩ := ih
    obtain ⟨b, _, hstep⟩ := exists_coordinate_translation_equivalence (σ := σ)
    obtain ⟨c, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
    obtain ⟨d, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
    let X : Polynomial ℕ := Polynomial.X
    let A := (X + Polynomial.C a) ^ a
    let B := (X + Polynomial.C b) ^ b
    let T := (A + Polynomial.C c) ^ c
    let Q := B + T + 2
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C d) ^ d)
    refine ⟨C, hC, ?_⟩
    intro p W hl
    have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
    let q := (p + a) ^ a
    let r := (q + c) ^ c
    let t := (p + b) ^ b + r + 2
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hb : 0 ≤ (p + b) ^ b := by positivity
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hbt : (p + b) ^ b ≤ t := by dsimp [t]; linarith only [hr]
    have hrt : r ≤ t := by dsimp [t]; linarith only [hb]
    have E := hprevious W hl.tail
    have F := htensor hq E (E.coordinatePullback (coordinateReplaceIndex i))
    have F' : NativeIntegerVectorEquivalence (Fintype.card σ - 1) r
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateTranslatedInput l x) *
            W.eval k.2 (coordinateTranslatedInput l (coordinateReplaceInput i x)))
        (coordinateTranslationExpansion W.eval (i :: l)) := F
    have hunit (x : Option σ → ℤ) :
        ∑ k : Fin W.outputDim × Fin W.outputDim,
          ‖W.eval k.1 (coordinateTranslatedInput l x) *
            W.eval k.2 (coordinateTranslatedInput l (coordinateReplaceInput i x))‖ ^ 2 = 1 := by
      simp only [Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]
    have R := htrans ht ((hstep W l i (List.nodup_cons.mp hl).1).mono hbt) (F'.mono hrt) hunit
    have hcost : (t + d) ^ d ≤ (p + C) ^ C := by
      simpa [X, A, B, T, Q, q, r, t, Polynomial.eval₂_pow] using hbudget p hp
    exact R.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_finite_assignment_equivalence {σ : Type*}
    [Fintype σ] [DecidableEq σ] [Nonempty σ] (n : ℕ) (l : List σ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p),
      l.Nodup → NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun k (x : (Fin (n + 1) × σ) → ℤ) => W.eval k (finiteChoiceCoordinateInput l x))
        (finiteChoiceExpansion W.eval l) := by
  induction l with
  | nil =>
      obtain ⟨C, hC, hself⟩ := exists_integer_self_equivalence (σ := σ)
      refine ⟨C, hC, ?_⟩
      intro p W _
      have E := (hself W).coordinatePullback (fun j => ((0 : Fin (n + 1)), j))
      apply E.of_coordinate_maps _ _ id (fun a => a Fin.elim0)
        (fun _ _ => rfl) _ E.left_dimension _ le_rfl
      · intro a x
        change (∏ v : Fin 0 → Fin (n + 1), W.eval (a v) (fun j => x (0, j))) =
          W.eval (a Fin.elim0) (fun j => x (0, j))
        rw [Fintype.prod_unique]
        exact congrArg (fun v => W.eval (a v) (fun j => x (0, j))) (by
          funext j
          exact Fin.elim0 j)
      · simpa only [Fintype.card_fun, Fintype.card_fin, List.length_nil, pow_zero, pow_one]
          using E.right_dimension
  | cons i l ih =>
      obtain ⟨A, _, hprevious⟩ := ih
      obtain ⟨B, _, hstep⟩ := exists_finite_sum_coordinate_equivalence (σ := σ) n
      obtain ⟨D, _, hproduct⟩ := NativeIntegerVectorEquivalence.exists_fin_product_budget (n + 1)
      obtain ⟨F, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
      let X : Polynomial ℕ := Polynomial.X
      let Q := (X + Polynomial.C A) ^ A
      let T := (Q + Polynomial.C D) ^ D
      let R := (X + Polynomial.C B) ^ B + T
      obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
        ((R + Polynomial.C F) ^ F + Polynomial.C ((n + 1) ^ (l.length + 1)) * X + X)
      refine ⟨C, hC, ?_⟩
      intro p W hl
      have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
      let q := (p + A) ^ A
      let t := (q + D) ^ D
      let r := (p + B) ^ B + t
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have hB : 0 ≤ (p + B) ^ B := by positivity
      have hr : 0 ≤ r := by dsimp [r]; linarith
      have hBr : (p + B) ^ B ≤ r := by dsimp [r]; linarith
      have htr : t ≤ r := by dsimp [r]; linarith
      have hsum : (r + F) ^ F + ((n + 1) ^ (l.length + 1) : ℕ) * p + p ≤ (p + C) ^ C := by
        simpa [X, Q, T, R, q, t, r, Polynomial.eval₂_pow] using hbudget p hp
      have hpow : 0 ≤ (r + F) ^ F := by positivity
      have hnp : 0 ≤ ((n + 1) ^ (l.length + 1) : ℕ) * p := mul_nonneg (Nat.cast_nonneg _) hp
      have hFC : (r + F) ^ F ≤ (p + C) ^ C := by linarith
      have hpC : p ≤ (p + C) ^ C := by linarith
      have hnC : ((n + 1) ^ (l.length + 1) : ℕ) * p ≤ (p + C) ^ C := by linarith
      let P : (σ ⊕ Fin (n + 1)) → (((Fin (n + 1) × σ) → ℤ) →+ ℤ) := fun j =>
        match j with
        | Sum.inl j => finiteChoiceCoordinateHom l j
        | Sum.inr a =>
          { toFun := fun x => x (a, i)
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
      have hleft (x : (Fin (n + 1) × σ) → ℤ) :
          finiteSumCoordinateInput i (fun j => P j x) = finiteChoiceCoordinateInput (i :: l) x := by
        change Function.update (finiteChoiceCoordinateInput l x) i
          (∑ a : Fin (n + 1), x (a, i)) = _
        exact (finiteChoiceCoordinateInput_cons l i x).symm
      have hright (a : Fin (n + 1)) (x : (Fin (n + 1) × σ) → ℤ) :
          finiteTermCoordinateInput i a (fun j => P j x) =
            finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i a x) := by
        change Function.update (finiteChoiceCoordinateInput l x) i (x (a, i)) = _
        exact (finiteChoiceCoordinateInput_replace l i (List.nodup_cons.mp hl).1 a x).symm
      have E₀ : NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + B) ^ B)
          (fun k x => W.eval k (finiteChoiceCoordinateInput (i :: l) x))
          (fun a : Fin (n + 1) → Fin W.outputDim => fun x => ∏ j,
            W.eval (a j) (finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i j x))) := by
        have E := (hstep W i).linearPullbackHom P
        simpa only [hleft, hright] using E
      have E := hprevious W hl.tail
      have E₁ := hproduct
        (fun j k x => W.eval k (finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i j x)))
        (fun j a x => finiteChoiceExpansion W.eval l a (finiteChoiceReplaceInput i j x))
        hq E.left_dimension E.right_dimension
        (fun j => E.coordinatePullback (finiteChoiceReplaceIndex i j))
      have hunit (x : (Fin (n + 1) × σ) → ℤ) :
          ∑ a : Fin (n + 1) → Fin W.outputDim,
            ‖∏ j, W.eval (a j) (finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i j x))‖ ^ 2 = 1 := by
        simp only [norm_prod, ← Finset.prod_pow]
        calc
          _ = ∏ j : Fin (n + 1), ∑ k : Fin W.outputDim,
              ‖W.eval k (finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i j x))‖ ^ 2 :=
            (Fintype.prod_sum _).symm
          _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]
      have H := htrans hr (E₀.mono hBr) (E₁.mono htr) hunit
      have hdim : (Fintype.card ((Fin (i :: l).length → Fin (n + 1)) → Fin W.outputDim) : ℝ) ≤
          Real.exp ((p + C) ^ C) := by
        simp only [Fintype.card_fun, Fintype.card_fin, List.length_cons, Nat.cast_pow]
        calc
          _ ≤ Real.exp p ^ ((n + 1) ^ (l.length + 1)) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound _
          _ = Real.exp (((n + 1) ^ (l.length + 1) : ℕ) * p) :=
            (Real.exp_nat_mul p ((n + 1) ^ (l.length + 1))).symm
          _ ≤ _ := Real.exp_le_exp.mpr hnC
      apply H.of_coordinate_maps _ _ id (fun a j v => a (Fin.cons j v))
        (fun _ _ => rfl) _ _ hdim hFC
      · intro a x
        exact finiteChoiceExpansion_cons W.eval l i a x
      · simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpC)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def mixedTranslationCoordinates (s : ℕ) :
    List (ReplicatedIndex (mixedCorrelationDegree s)) :=
  (Finset.univ.filter (fun j : ReplicatedIndex (mixedCorrelationDegree s) => j.1 = 1)).toList

@[simp] theorem mem_mixedTranslationCoordinates (s : ℕ) (j : ReplicatedIndex (mixedCorrelationDegree s)) :
    j ∈ mixedTranslationCoordinates s ↔ j.1 = 1 := by
  simp [mixedTranslationCoordinates]

theorem mixedTranslationCoordinates_nodup (s : ℕ) : (mixedTranslationCoordinates s).Nodup :=
  Finset.nodup_toList _

def mixedTranslationSample (s : ℕ) (x : Fin 3 → ℤ) :
    Option (ReplicatedIndex (mixedCorrelationDegree s)) → ℤ
  | none => x 2
  | some j => correlationInput (x 0) (x 1) j.1

def mixedTranslationSampleHom (s : ℕ) (j : Option (ReplicatedIndex (mixedCorrelationDegree s))) :
    ((Fin 3 → ℤ) →+ ℤ) where
  toFun x := mixedTranslationSample s x j
  map_zero' := by
    rcases j with _ | ⟨j, k⟩
    · rfl
    · fin_cases j <;> rfl
  map_add' x y := by
    rcases j with _ | ⟨j, k⟩
    · rfl
    · fin_cases j <;> rfl

theorem mixedTranslationSample_translated (s : ℕ) (x : Fin 3 → ℤ) :
    coordinateTranslatedInput (mixedTranslationCoordinates s) (mixedTranslationSample s x) =
      fun j => correlationInput (x 0) (x 1 + x 2) j.1 := by
  funext ⟨j, k⟩
  fin_cases j <;> simp [coordinateTranslatedInput, mixedTranslationSample, correlationInput]
  rfl

theorem replicatedMixed_nonempty (s : ℕ) : Nonempty (ReplicatedIndex (mixedCorrelationDegree s)) :=
  ⟨⟨0, ⟨0, by change 0 < 1; omega⟩⟩⟩

theorem replicatedMixed_card (s : ℕ) :
    Fintype.card (ReplicatedIndex (mixedCorrelationDegree s)) = s + 1 := by
  rw [replicatedIndex_card, Fin.sum_univ_two]
  change 1 + s = s + 1
  omega

namespace NativeMultidegreeNilcharacter

theorem mixedTranslationExpansion_factor {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (a : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length) (x : Fin 3 → ℤ) :
    coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a (mixedTranslationSample s x) =
      V.eval (firstTranslationCoordinate (mixedTranslationCoordinates s) a)
        (fun j => correlationInput (x 0) (x 1) j.1) *
      translationExpansionRemainder V.eval (mixedTranslationCoordinates s) a (mixedTranslationSample s x) :=
  coordinateTranslationExpansion_factor V.eval (mixedTranslationCoordinates s) a (mixedTranslationSample s x)

theorem exists_mixed_translation_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun k (x : Fin 3 → ℤ) => V.eval k (fun j => correlationInput (x 0) (x 1 + x 2) j.1))
        (fun a x => coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a
          (mixedTranslationSample s x)) := by
  let := replicatedMixed_nonempty s
  obtain ⟨C, hC, hexpand⟩ := exists_translation_expansion_equivalence (mixedTranslationCoordinates s)
  refine ⟨C, hC, ?_⟩
  intro p V
  have E := (hexpand V (mixedTranslationCoordinates_nodup s)).linearPullbackHom
    (mixedTranslationSampleHom s)
  change NativeIntegerVectorEquivalence _ _
    (fun k x => V.eval k (coordinateTranslatedInput (mixedTranslationCoordinates s)
      (mixedTranslationSample s x)))
    (fun a x => coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a
      (mixedTranslationSample s x)) at E
  simpa only [replicatedMixed_card, Nat.add_sub_cancel, mixedTranslationSample_translated] using E

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TensorSquarePairComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

noncomputable def rationalDilation (r : ℚ) : NativeMultidegreeNilcharacter bound p :=
  { W with orbit := W.multi.filtration.realification.rationalDilationOrbit r W.orbit }

theorem rationalDilation_eval_rescaled (r : ℚ) (q : ℤ) (hr : r * (q : ℚ) = 1)
    (a : Fin W.outputDim) (x : σ → ℤ) :
    (W.rationalDilation r).eval a (fun i => q * x i) = W.eval a x := by
  unfold eval rationalDilation
  rw [W.multi.filtration.realification.rationalDilationOrbit_rescaled r q hr]

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_quadratic_integer_translation_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (a b : Fin 2 → ℤ),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        (fun i x => W.eval i (x + a)) (fun i x => W.eval i (x + b)) := by
  obtain ⟨C, hC, htranslate⟩ :=
    UnitVerticalObservable.exists_integer_translation_equivalence_budget 1
  refine ⟨C, hC, ?_⟩
  intro p W a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have htop : W.multi.realSubgroup (mixedCorrelationDegree 1) =
      W.model.filtration.realification.subgroup 2 := by
    have hsum : (∑ i, mixedCorrelationDegree 1 i) = 2 := by decide
    simpa only [hsum] using W.multi.realSubgroup_top
  let V : W.model.UnitVerticalObservable (W.model.filtration.realification.subgroup 2)
      (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (htop.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (htop.symm ▸ hz) hL }
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have E := htranslate W.model V (W.multi.orbitToOrdinary W.orbit) hp W.complexity.1 hdim a b
  refine ⟨E.left_dimension, E.right_dimension, ?_⟩
  intro i j
  obtain ⟨F⟩ := E.expansion i j
  have heq (k : Fin W.outputDim) (x : Fin 2 → ℤ) :
      V.observable k (QuotientGroup.mk (W.model.filtration.realification.polynomialOrbitEval
        (fun _ : Fin 2 => 1) x (W.multi.orbitToOrdinary W.orbit))) = W.eval k x := by
    rw [W.multi.orbitToOrdinary_eval]
    rfl
  have hf : (fun x => V.observable i (QuotientGroup.mk
      (W.model.filtration.realification.polynomialOrbitEval (fun _ : Fin 2 => 1)
        (x + a) (W.multi.orbitToOrdinary W.orbit))) *
      star (V.observable j (QuotientGroup.mk
        (W.model.filtration.realification.polynomialOrbitEval (fun _ : Fin 2 => 1)
          (x + b) (W.multi.orbitToOrdinary W.orbit))))) =
      (fun x => W.eval i (x + a) * star (W.eval j (x + b))) := by
    funext x
    rw [heq, heq]
  exact ⟨hf ▸ F⟩

theorem half_dilation_integer_representative {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (x : Fin 2 → ℤ) (j : Fin W.outputDim) :
    (W.rationalDilation (1 / 2)).eval j (fun i => x i - ((x i : ZMod 2).val : ℤ)) =
      W.eval j (fun i => x i / 2) := by
  have hx : (fun i => x i - ((x i : ZMod 2).val : ℤ)) = (fun i => 2 * (x i / 2)) := by
    funext i
    rw [ZMod.val_intCast]
    omega
  rw [hx]
  exact W.rationalDilation_eval_rescaled (1 / 2) 2 (by norm_num) j _

theorem exists_half_dilation_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        (W.rationalDilation (1 / 2)).eval (fun j x => W.eval j (fun i => x i / 2)) := by
  obtain ⟨A, _, hshift⟩ := exists_quadratic_integer_translation_equivalence
  obtain ⟨B, _, hparity⟩ := exists_pairParityIndicator_expansion
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + Polynomial.C B + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C D) ^ D + T + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let V := W.rationalDilation (1 / 2)
  let t : ℝ := (p + A) ^ A + B + p + 2
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hb : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hat : (p + A) ^ A ≤ t := by dsimp [t]; linarith
  have hbt : (B : ℝ) ≤ t := by dsimp [t]; linarith
  have hbound : (t + D) ^ D + t + 2 ≤ (p + C) ^ C := by
    simpa [T, t, X, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (t + D) ^ D := by positivity
  have hpc : p ≤ (p + C) ^ C := by linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpc)
  refine ⟨hdim, hdim, ?_⟩
  intro i j
  let F (r : Fin 2 → ZMod 2) (x : Fin 2 → ℤ) :=
    V.eval i x * star (V.eval j (fun k => x k - ((r k).val : ℤ)))
  have hF (r : Fin 2 → ZMod 2) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 t (F r)) := by
    obtain ⟨E⟩ := (hshift V 0 (fun k => -((r k).val : ℤ))).expansion i j
    have heq : (fun x => V.eval i (x + 0) * star (V.eval j (x + fun k => -((r k).val : ℤ)))) = F r := by
      funext x
      simp only [F, add_zero, sub_eq_add_neg]
      rfl
    rw [heq] at E
    exact ⟨E.mono hat⟩
  have hterm (r : Fin 2 → ZMod 2) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
      ((t + D) ^ D) (fun x => pairParityIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hparity r)).mono hbt) (Classical.choice (hF r))
  have hc : (Fintype.card (Fin 2 → ZMod 2) : ℝ) ≤ Real.exp 2 := by
    norm_num only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hh := Real.add_one_le_exp (1 : ℝ)
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hcost : (∑ _ : Fin 2 → ZMod 2, ‖(1 : ℂ)‖) ≤ Real.exp 2 := by simpa using hc
  let S := NativeIntegerExpansion.weightedSum (fun r => Classical.choice (hterm r)) (fun _ => 1)
    (by norm_num : (0 : ℝ) ≤ 2) hc hcost
  have heq : (fun x => ∑ r : Fin 2 → ZMod 2, (1 : ℂ) * (pairParityIndicator r x * F r x)) =
      (fun x => V.eval i x * star (W.eval j (fun k => x k / 2))) := by
    funext x
    let r : Fin 2 → ZMod 2 := fun k => (x k : ZMod 2)
    rw [Finset.sum_eq_single r]
    · simp only [pairParityIndicator, r, ite_true, one_mul, F]
      rw [show V.eval j (fun k => x k - ((x k : ZMod 2).val : ℤ)) =
        W.eval j (fun k => x k / 2) from W.half_dilation_integer_representative x j]
    · intro a _ ha
      have hne : (fun k => (x k : ZMod 2)) ≠ a := fun h => ha h.symm
      simp only [pairParityIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  rw [heq] at S
  exact ⟨S.mono (by linarith)⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_unit_pair_replacement_error {I J : Type*} [Fintype I] [Fintype J]
    (u : I → ℂ) (v : J → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) (hv : ∑ j, ‖v j‖ ^ 2 = 1)
    (huc : ∀ i, ‖u i‖ ≤ 1) (hvc : ∀ j, ‖v j‖ ≤ 1)
    (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (G : I → J → ℂ) :
    ‖star a * b - ∑ ij : I × J,
      (star (a * star (u ij.1)) * (b * star (v ij.2))) * G ij.1 ij.2‖ ≤
      ∑ ij : I × J, ‖star (u ij.1) * v ij.2 - G ij.1 ij.2‖ := by
  have hleft := congrArg star (complex_unit_vector_resolution u hu a)
  simp only [star_sum, star_mul] at hleft
  have hright := complex_unit_vector_resolution v hv b
  have hrepr : star a * b = ∑ ij : I × J,
      (star (a * star (u ij.1)) * (b * star (v ij.2))) * (star (u ij.1) * v ij.2) := by
    conv_lhs => rw [hleft, hright]
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [star_mul]
    ring
  rw [hrepr, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ij _
  rw [← mul_sub, norm_mul]
  have hcap : ‖star (a * star (u ij.1)) * (b * star (v ij.2))‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans ?_
    · rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (huc _)
    · rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans (hvc _)
  exact mul_le_of_le_one_left (norm_nonneg _) hcap

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def halfDilationExchangeCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ ij : Fin W.outputDim × Fin W.outputDim,
    (star ((W.rationalDilation (1 / 2)).eval a x * star (W.eval ij.1 (fun k => x k / 2))) *
      ((W.rationalDilation (1 / 2)).eval b (fun k => x k.rev) *
        star (W.eval ij.2 (fun k => x k.rev / 2)))) * G ij.1 ij.2 (fun k => x k / 2)

theorem halfDilationExchangeCorrection_pointwise_error
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖(W.rationalDilation (1 / 2)).antisymmetricKernel a b (x 0) (x 1) -
        W.halfDilationExchangeCorrection G a b x‖ ≤
      ∑ ij : Fin W.outputDim × Fin W.outputDim,
        ‖W.antisymmetricKernel ij.1 ij.2 (x 0 / 2) (x 1 / 2) -
          G ij.1 ij.2 (fun k => x k / 2)‖ := by
  have hinput (z : Fin 2 → ℤ) : correlationInput (z 0) (z 1) = z := by
    funext k
    fin_cases k <;> rfl
  have hswap (z : Fin 2 → ℤ) : correlationInput (z 1) (z 0) = (fun k => z k.rev) := by
    funext k
    fin_cases k <;> rfl
  simp only [antisymmetricKernel, hinput x, hswap x,
    hinput (fun k => x k / 2), hswap (fun k => x k / 2), halfDilationExchangeCorrection]
  exact norm_unit_pair_replacement_error
    (fun i => W.eval i (fun k => x k / 2)) (fun j => W.eval j (fun k => x k.rev / 2))
    (W.unit_eval _) (W.unit_eval _) (fun i => W.norm_eval i _) (fun j => W.norm_eval j _)
    ((W.rationalDilation (1 / 2)).eval a x) ((W.rationalDilation (1 / 2)).eval b (fun k => x k.rev))
    ((W.rationalDilation (1 / 2)).norm_eval a _) ((W.rationalDilation (1 / 2)).norm_eval b _)
    (fun i j => G i j (fun k => x k / 2))

theorem halfDilationExchangeCorrection_mean_error {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel i j ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.rationalDilation (1 / 2)).antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
        W.halfDilationExchangeCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤
      4 * (W.outputDim : ℝ) ^ 2 * ε := by
  have hmean := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => W.halfDilationExchangeCorrection_pointwise_error G a b (fun k => ((x k).val : ℤ)))
  rw [Finset.expect_sum_comm] at hmean
  have he (ij : Fin W.outputDim × Fin W.outputDim) :
      (𝔼 x : Fin 2 → ZMod N,
        ‖W.antisymmetricKernel ij.1 ij.2 (((x 0).val : ℤ) / 2) (((x 1).val : ℤ) / 2) -
          G ij.1 ij.2 (fun k => ((x k).val : ℤ) / 2)‖) ≤ 4 * ε := by
    have h := expect_pair_cyclicHalf_le (fun x : Fin 2 → ZMod N =>
      ‖W.antisymmetricKernel ij.1 ij.2 ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G ij.1 ij.2 (fun k => ((x k).val : ℤ))‖) (fun _ => norm_nonneg _)
    simp only [cyclicHalf_val, Int.natCast_ediv, Nat.cast_ofNat] at h
    exact h.trans (mul_le_mul_of_nonneg_left (herr ij.1 ij.2) (by norm_num))
  apply hmean.trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, 4 * ε :=
      Finset.sum_le_sum (fun ij _ => he ij)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      ring

theorem halfDilationExchangeCorrection_norm {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {B : ℝ}
    (hG : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (a b : Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.halfDilationExchangeCorrection G a b (fun k => ((x k).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 2 * B := by
  unfold halfDilationExchangeCorrection
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin W.outputDim × Fin W.outputDim, B := by
      apply Finset.sum_le_sum
      intro ij _
      rw [norm_mul]
      have hc : ‖star ((W.rationalDilation (1 / 2)).eval a (fun k => ((x k).val : ℤ)) *
          star (W.eval ij.1 (fun k => ((x k).val : ℤ) / 2))) *
          ((W.rationalDilation (1 / 2)).eval b (fun k => ((x k.rev).val : ℤ)) *
          star (W.eval ij.2 (fun k => ((x k.rev).val : ℤ) / 2)))‖ ≤ 1 := by
        rw [norm_mul, norm_star]
        refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans ?_
        · rw [norm_mul, norm_star]
          exact (mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation (1 / 2)).norm_eval a _)).trans (W.norm_eval _ _)
        · rw [norm_mul, norm_star]
          exact (mul_le_of_le_one_left (norm_nonneg _)
            ((W.rationalDilation (1 / 2)).norm_eval b _)).trans (W.norm_eval _ _)
      apply (mul_le_of_le_one_left (norm_nonneg _) hc).trans
      have h := hG ij.1 ij.2 (fun k => cyclicHalf (x k))
      simpa only [cyclicHalf_val, Int.natCast_ediv, Nat.cast_ofNat] using h
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, pow_two]

theorem exists_halfDilationExchangeCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p), 0 ≤ q →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
        (W.halfDilationExchangeCorrection G a b)) := by
  obtain ⟨A, _, hcompare⟩ := exists_half_dilation_equivalence
  obtain ⟨B, _, hhalf⟩ := NativeIntegerExpansion.exists_halving_expansion
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B + X + 2
  let U := (T + Polynomial.C D) ^ D + T
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((U + Polynomial.C D) ^ D + 2 * T + 2)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG a b
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let t := (v + A) ^ A + (v + B) ^ B + v + 2
  let u := (t + D) ^ D + t
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpt : p ≤ t := by
    have hA : 0 ≤ (v + A) ^ A := by positivity
    have hB : 0 ≤ (v + B) ^ B := by positivity
    dsimp [t, v]
    dsimp [v] at hA hB
    linarith
  have hAt : (p + A) ^ A ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show p + A ≤ v + A by dsimp [v]; linarith) A).trans
    dsimp [t]
    have hB : 0 ≤ (v + B) ^ B := by positivity
    linarith
  have hBt : (q + B) ^ B ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show q + B ≤ v + B by dsimp [v]; linarith) B).trans
    dsimp [t]
    have hA : 0 ≤ (v + A) ^ A := by positivity
    linarith
  have htu : t ≤ u := by
    have hh : 0 ≤ (t + D) ^ D := by positivity
    dsimp [u]
    linarith
  have hprod : (t + D) ^ D ≤ u := by dsimp [u]; linarith
  have hbound : (u + D) ^ D + (2 * t + 2) ≤ (p + q + C) ^ C := by
    simpa [T, U, X, t, u, v, Polynomial.eval₂_pow, add_assoc] using hbudget v hv
  let V := W.rationalDilation (1 / 2)
  let Amap : Fin 2 → ((Fin 2 → ℤ) →+ ℤ) :=
    fun k => { toFun := fun x => x k.rev, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hterm (ij : Fin W.outputDim × Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((u + D) ^ D)
        (fun x => (star (V.eval a x * star (W.eval ij.1 (fun k => x k / 2))) *
          (V.eval b (fun k => x k.rev) * star (W.eval ij.2 (fun k => x k.rev / 2)))) *
          G ij.1 ij.2 (fun k => x k / 2))) := by
    obtain ⟨E⟩ := (hcompare W).expansion a ij.1
    obtain ⟨F⟩ := (hcompare W).expansion b ij.2
    obtain ⟨H⟩ := hhalf hq (Classical.choice (hG ij.1 ij.2))
    obtain ⟨K⟩ := hmul ht (E.conjugate.mono hAt) ((F.linearPullbackHom Amap).mono hAt)
    exact hmul hu (K.mono hprod) (H.mono (hBt.trans htu))
  have hc : (Fintype.card (Fin W.outputDim × Fin W.outputDim) : ℝ) ≤ Real.exp (2 * t + 2) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul W.output_bound W.output_bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add, two_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hcost : (∑ _ : Fin W.outputDim × Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp (2 * t + 2) := by
    simpa using hc
  let S := NativeIntegerExpansion.weightedSum (fun ij => Classical.choice (hterm ij)) (fun _ => 1)
    (by linarith : 0 ≤ 2 * t + 2) hc hcost
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
    (fun x => W.halfDilationExchangeCorrection G a b x)
  simpa only [one_mul, halfDilationExchangeCorrection, V] using S.mono hbound

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def tensorSquareExchangeCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin (W.outputDim ^ 2)) (x : Fin 2 → ℤ) : ℂ :=
  G ((tensorIndexEquiv W.outputDim 2).symm a 0) ((tensorIndexEquiv W.outputDim 2).symm b 0) x *
    G ((tensorIndexEquiv W.outputDim 2).symm a 1) ((tensorIndexEquiv W.outputDim 2).symm b 1) x

theorem tensorSquare_antisymmetricKernel (a b : Fin (W.outputDim ^ 2)) (h n : ℤ) :
    (W.tensorPower 2).antisymmetricKernel a b h n =
      W.antisymmetricKernel ((tensorIndexEquiv W.outputDim 2).symm a 0)
        ((tensorIndexEquiv W.outputDim 2).symm b 0) h n *
      W.antisymmetricKernel ((tensorIndexEquiv W.outputDim 2).symm a 1)
        ((tensorIndexEquiv W.outputDim 2).symm b 1) h n := by
  simp only [antisymmetricKernel, tensorPower_eval, Fin.prod_univ_two, star_mul]
  ring

theorem tensorSquareExchangeCorrection_mean_error {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {B ε : ℝ}
    (hB : 0 ≤ B)
    (hcap : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ B)
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel i j ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : Fin (W.outputDim ^ 2)) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖(W.tensorPower 2).antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
        W.tensorSquareExchangeCorrection G a b (fun k => ((x k).val : ℤ))‖) ≤ (1 + B) * ε := by
  let i := (tensorIndexEquiv W.outputDim 2).symm a
  let j := (tensorIndexEquiv W.outputDim 2).symm b
  let K (r : Fin 2) (x : Fin 2 → ZMod N) :=
    W.antisymmetricKernel (i r) (j r) ((x 0).val : ℤ) ((x 1).val : ℤ)
  let F (r : Fin 2) (x : Fin 2 → ZMod N) := G (i r) (j r) (fun k => ((x k).val : ℤ))
  have hpoint (x : Fin 2 → ZMod N) :
      ‖K 0 x * K 1 x - F 0 x * F 1 x‖ ≤
        ‖K 1 x - F 1 x‖ + B * ‖K 0 x - F 0 x‖ := by
    have heq : K 0 x * K 1 x - F 0 x * F 1 x =
        K 0 x * (K 1 x - F 1 x) + (K 0 x - F 0 x) * F 1 x := by ring
    rw [heq]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    apply add_le_add
    · exact mul_le_of_le_one_left (norm_nonneg _) (W.antisymmetricKernel_norm _ _ _ _)
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hcap _ _ x) (norm_nonneg (K 0 x - F 0 x))
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun x _ => hpoint x)
  rw [Finset.expect_add_distrib, ← Finset.mul_expect] at hm
  have h0 : (𝔼 x, ‖K 0 x - F 0 x‖) ≤ ε := herr _ _
  have h1 : (𝔼 x, ‖K 1 x - F 1 x‖) ≤ ε := herr _ _
  have hbnd := hm.trans (add_le_add h1 (mul_le_mul_of_nonneg_left h0 hB))
  have hfinal : (𝔼 x, ‖K 0 x * K 1 x - F 0 x * F 1 x‖) ≤ (1 + B) * ε :=
    hbnd.trans_eq (by ring)
  simpa only [K, F, i, j, tensorSquare_antisymmetricKernel, tensorSquareExchangeCorrection] using hfinal

theorem exists_tensorSquareExchangeCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p), 0 ≤ q →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((q + C) ^ C)
        (W.tensorSquareExchangeCorrection G a b)) := by
  obtain ⟨C, hC, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG a b
  exact hmul hq (Classical.choice (hG _ _)) (Classical.choice (hG _ _))

theorem explicit_half_root_exchange_mean_error {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (hcap : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel i j ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a b : Fin (W.outputDim ^ 2)) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖((W.rationalDilation (1 / 2)).tensorPower 2).antisymmetricKernel a b
          ((x 0).val : ℤ) ((x 1).val : ℤ) -
        (W.rationalDilation (1 / 2)).tensorSquareExchangeCorrection
          (W.halfDilationExchangeCorrection G) a b (fun k => ((x k).val : ℤ))‖) ≤
      (1 + (W.outputDim : ℝ) ^ 2) * (4 * (W.outputDim : ℝ) ^ 2 * ε) := by
  apply tensorSquareExchangeCorrection_mean_error (W.rationalDilation (1 / 2))
    (W.halfDilationExchangeCorrection G) (by positivity)
  · intro i j x
    simpa only [mul_one] using W.halfDilationExchangeCorrection_norm G hcap i j x
  · exact W.halfDilationExchangeCorrection_mean_error G herr

theorem exists_explicit_half_root_exchange_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p), 0 ≤ q →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
        ((W.rationalDilation (1 / 2)).tensorSquareExchangeCorrection
          (W.halfDilationExchangeCorrection G) a b)) := by
  obtain ⟨A, _, hhalf⟩ := exists_halfDilationExchangeCorrection_expansion
  obtain ⟨B, _, hsquare⟩ := exists_tensorSquareExchangeCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := hsquare (W.rationalDilation (1 / 2)) (by positivity : 0 ≤ (p + q + A) ^ A)
    (W.halfDilationExchangeCorrection G) (hhalf W hq G hG) a b
  have hbound : ((p + q + A) ^ A + B) ^ B ≤ (p + q + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  exact ⟨E.mono hbound⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BoundedRootDegreeEquivalence
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_dilation_degree_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) (hpos : 1 ≤ ∑ j, bound j) (q : ℤ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) ((p + C) ^ C)
        (integerDilationVector W.eval q) (signedTensorVector W.eval (q ^ ∑ j, bound j)) := by
  obtain ⟨a, _, hfamily⟩ := exists_dilation_family bound hpos q
  let n := (q ^ ∑ j, bound j).natAbs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C (n + 1) * X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hb : (p + a) ^ a + (n + 1 : ℝ) * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by nlinarith [mul_nonneg hn hp]
  have hnpr : (n : ℝ) * p ≤ (p + C) ^ C := by nlinarith
  have har : (p + a) ^ a ≤ (p + C) ^ C := by nlinarith [mul_nonneg hn hp]
  obtain ⟨R, _⟩ := hfamily W
  exact NativeIntegerVectorEquivalence.of_dilation_family W.eval q (∑ j, bound j) R
    (by simpa only [Fintype.card_fin] using W.output_bound) hpr hnpr har

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold.MultidegreeStructure
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_uniform_dilation_degree_equivalence (s : ℕ) (q : ℤ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      (bound : σ → ℕ), (∑ j, bound j) = s + 1 →
      ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (integerDilationVector W.eval q) (signedTensorVector W.eval (q ^ (s + 1))) := by
  obtain ⟨a, _, hfamily⟩ := exists_controlled_dilation_family s q
  let n := (q ^ (s + 1)).natAbs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C (n + 1) * X + 2)
  refine ⟨C, hC, ?_⟩
  intro σ _ _ bound hs p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hb : (p + a) ^ a + (n + 1 : ℝ) * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by nlinarith [mul_nonneg hn hp]
  have hnpr : (n : ℝ) * p ≤ (p + C) ^ C := by nlinarith
  have har : (p + a) ^ a ≤ (p + C) ^ C := by nlinarith [mul_nonneg hn hp]
  obtain ⟨R, _⟩ := hfamily W.model W.multi rfl hs W.complexity W.vertical W.orbit
  have R' : NativeIntegerModelFamily (fun _ : σ => 1) s ((p + a) ^ a)
      (dilationTensorCrossProduct W.eval q (s + 1)) := by
    exact hs ▸ R
  exact NativeIntegerVectorEquivalence.of_dilation_family W.eval q (s + 1) R'
    (by simpa only [Fintype.card_fin] using W.output_bound) hpr hnpr har

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_uniform_root_degree_equivalence (s q : ℕ) (hq : 0 < q) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      (bound : σ → ℕ), (∑ j, bound j) = s + 1 →
      ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      ∃ R : NativeMultidegreeNilcharacter bound ((p + C) ^ C),
        R.dim = W.dim ∧ NativeIntegerVectorEquivalence s ((p + C) ^ C)
          W.eval (tensorVector R.eval q) := by
  obtain ⟨a, _, hdilation⟩ := exists_uniform_dilation_degree_equivalence s (q : ℤ)
  let n := q ^ s
  let X : Polynomial ℕ := Polynomial.X
  let B := Polynomial.C (n + 1) * (X + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C (q + 1) * B + X + 2)
  refine ⟨C, hC, ?_⟩
  intro σ _ _ bound hs p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hA : 0 ≤ (p + a) ^ a := by positivity
  have hB : 0 ≤ tensorPowerBudget n p := by unfold tensorPowerBudget; positivity
  have hqB : 0 ≤ (q : ℝ) * tensorPowerBudget n p := mul_nonneg (Nat.cast_nonneg _) hB
  have hb : (p + a) ^ a + (q + 1 : ℝ) * tensorPowerBudget n p + p + 2 ≤ (p + C) ^ C := by
    simpa [X, B, tensorPowerBudget, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by nlinarith
  have hBr : tensorPowerBudget n p ≤ (p + C) ^ C := by nlinarith
  have hqBr : (q : ℝ) * tensorPowerBudget n p ≤ (p + C) ^ C := by nlinarith
  have hAr : (p + a) ^ a ≤ (p + C) ^ C := by nlinarith
  let V := W.rationalDilation ((q : ℚ)⁻¹)
  let R₀ := V.tensorPower n
  let R := R₀.mono hBr
  have hscale : (q : ℚ)⁻¹ * ((q : ℤ) : ℚ) = 1 := by
    rw [Int.cast_natCast]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hq.ne')
  have hleft (i : Fin W.outputDim) (x : σ → ℤ) :
      W.eval i x = integerDilationVector V.eval (q : ℤ) i x :=
    (W.rationalDilation_eval_rescaled _ _ hscale i x).symm
  have hpos : 1 ≤ s + 1 := by omega
  have hright (b : Fin q → Fin R.outputDim) (x : σ → ℤ) :
      tensorVector R.eval q b x =
        signedTensorVector V.eval ((q : ℤ) ^ (s + 1))
          (rootTensorIndex W.outputDim q (s + 1) hpos b) x := by
    change tensorVector (V.tensorPower n).eval q b x = _
    exact V.tensorPower_tensor_eval q (s + 1) hpos b x
  have hdim : (Fintype.card (Fin q → Fin R.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    have hroot : (R.outputDim : ℝ) ≤ Real.exp (tensorPowerBudget n p) := R₀.output_bound
    calc
      _ ≤ Real.exp (tensorPowerBudget n p) ^ q := pow_le_pow_left₀ (Nat.cast_nonneg _) hroot _
      _ = Real.exp ((q : ℝ) * tensorPowerBudget n p) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hqBr
  refine ⟨R, rfl, ?_⟩
  exact (hdilation bound hs V).of_coordinate_maps W.eval (tensorVector R.eval q) id
    (rootTensorIndex W.outputDim q (s + 1) hpos) hleft hright
    (by simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpr)) hdim hAr

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_bounded_root_degree_equivalence (s Q : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {q : ℕ}, 0 < q → q ≤ Q →
      ∀ {σ : Type} [Fintype σ] [DecidableEq σ]
        (bound : σ → ℕ), (∑ j, bound j) = s + 1 →
        ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
        ∃ R : NativeMultidegreeNilcharacter bound ((p + C) ^ C),
          R.dim = W.dim ∧ NativeIntegerVectorEquivalence s ((p + C) ^ C)
            W.eval (tensorVector R.eval q) := by
  classical
  let a : Fin Q → ℕ := fun i => Classical.choose
    (exists_uniform_root_degree_equivalence.{0} s (i.val + 1) (by omega))
  let C := 2 + ∑ i, a i
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro q hq hqQ σ _ _ bound hs p W
  let i : Fin Q := ⟨q - 1, by omega⟩
  have hi : i.val + 1 = q := by dsimp [i]; omega
  have ha : 2 ≤ a i := (Classical.choose_spec
    (exists_uniform_root_degree_equivalence.{0} s (i.val + 1) (by omega))).1
  have hroot : ∀ {τ : Type} [Fintype τ] [DecidableEq τ]
      (b : τ → ℕ), (∑ j, b j) = s + 1 →
      ∀ {r : ℝ} (V : NativeMultidegreeNilcharacter b r),
      ∃ R : NativeMultidegreeNilcharacter b ((r + a i) ^ a i),
        R.dim = V.dim ∧ NativeIntegerVectorEquivalence s ((r + a i) ^ a i)
          V.eval (tensorVector R.eval (i.val + 1)) :=
    (Classical.choose_spec
      (exists_uniform_root_degree_equivalence.{0} s (i.val + 1) (by omega))).2
  rw [hi] at hroot
  obtain ⟨R, hdim, hE⟩ := hroot bound hs W
  have hsum : a i ≤ ∑ j, a j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
  have haC : a i ≤ C := by dsimp [C]; omega
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hbudget := shifted_power_self_mono hp (by omega : 1 ≤ a i) haC
  exact ⟨R.mono hbudget, hdim, hE.mono hbudget⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicAntisymmetricTransfer
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem topInvariant_integer_expansion_of_step {L σ : Type}
    [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s t d : ℕ} (ht : t = s + 1) (D : RationalFilteredNilmanifold L t d)
    {w : σ → ℕ} (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (hinv : ∀ z ∈ D.filtration.realification.subgroup t, ∀ x,
      T.observable (z • x) = T.observable x) :
    Nonempty (NativeIntegerExpansion w s
      ((p + topInvariantIntegerExponent s) ^ topInvariantIntegerExponent s) T.eval) := by
  subst t
  exact topInvariant_integer_expansion D T hp hT hinv

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {σ : Type} {L I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) {p q v : ℝ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (V : D.UnitVerticalObservable (D.filtration.realification.subgroup s) I v)
  (U : M.SymmetricSquarefreeUnitData p V.frequency q)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
    (max s (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p U.grid U.grid_pos U.stable)

theorem comparisonVerticalProduct_top_invariant (hstep : s = ∑ i, bound i)
    (hEF : E.filtration = M.filtration.comparisonFiltration (fun j : ReplicatedIndex bound => j.1))
    (ε : D.RealGroup) (a : Fin (multidegreeFactorial bound) → I)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (z : E.RealGroup) (hz : z ∈ E.filtration.realification.subgroup
      (max s (Fintype.card (ReplicatedIndex bound)))) (x : E.Space) :
    M.comparisonVerticalProduct V U E hEL ε a k (z • x) =
      M.comparisonVerticalProduct V U E hEL ε a k x := by
  let π := fun j : ReplicatedIndex bound => j.1
  have hcard : Fintype.card (ReplicatedIndex bound) = s := (replicatedIndex_card bound).trans hstep.symm
  have hzF : z.coord ∈ (M.filtration.comparisonFiltration π).realification.layer s := by
    have hh : z.coord ∈ E.filtration.realification.layer s :=
      E.filtration.realification.antitone (le_max_left s _) hz
    simpa only [hEF] using hh
  let z₁ : D.RealGroup := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot) (M.filtration.comparisonFirst π) z
  let z₂ : (M.squarefreeModel p U.grid U.grid_pos U.stable).RealGroup :=
    realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := (M.squarefreeModel p U.grid U.grid_pos U.stable).filtration.lowerCentralSeries_eq_bot)
      (M.filtration.comparisonSecond π) z
  have hz₁ : z₁ ∈ D.filtration.realification.subgroup s := by
    change realificationLieHom (M.filtration.comparisonFirst π) z.coord ∈ D.filtration.realification.layer s
    rw [← M.ordinary]
    exact M.filtration.comparisonFirst_real_mem_layer π s z.coord hzF
  have hz₂ : z₂ ∈ (M.squarefreeModel p U.grid U.grid_pos U.stable).filtration.realification.subgroup
      (Fintype.card (ReplicatedIndex bound)) := by
    change realificationLieHom (M.filtration.comparisonSecond π) z.coord ∈
      (M.filtration.squarefreeOrdinaryFiltration π).realification.layer (Fintype.card (ReplicatedIndex bound))
    rw [congrArg (fun n => (M.filtration.squarefreeOrdinaryFiltration π).realification.layer n) hcard]
    exact M.filtration.comparisonSecond_real_mem_layer π s z.coord hzF
  have hfreq : realifyFunctional (V.tensorPower (multidegreeFactorial bound)).frequency z₁.coord =
      realifyFunctional U.observable.frequency z₂.coord := by
    change realifyFunctional (multidegreeFactorial bound • V.frequency)
      (realificationLieHom (M.filtration.comparisonFirst π) z.coord) =
      realifyFunctional U.observable.frequency (realificationLieHom (M.filtration.comparisonSecond π) z.coord)
    rw [realifyFunctional_nsmul, U.frequency, nsmul_eq_mul]
    exact M.filtration.realComparisonTop_frequency hstep V.frequency hzF
  have hcomm : Commute z₁ ε := commute_of_lie_eq_zero z₁ ε
    (D.filtration.realification.top_layer_central hz₁ ε.coord)
  have hswap (y : D.Space) : ε • (z₁ • y) = z₁ • (ε • y) := by
    rw [← mul_smul, ← hcomm.eq, mul_smul]
  let c := CircleFourier.character ((realifyFunctional U.observable.frequency z₂.coord : ℝ) : CircleFourier.Circle)
  have hc : c * star c = 1 := by
    change CircleFourier.character ((realifyFunctional U.observable.frequency z₂.coord : ℝ) : CircleFourier.Circle) *
      star (CircleFourier.character ((realifyFunctional U.observable.frequency z₂.coord : ℝ) : CircleFourier.Circle)) = 1
    rw [← CircleFourier.character_neg, ← CircleFourier.character_add,
      add_neg_cancel, CircleFourier.character_zero]
  unfold comparisonVerticalProduct
  rw [M.comparisonFirstSpace_smul, M.comparisonSecondSpace_smul]
  change (V.tensorPower (multidegreeFactorial bound)).observable a
    (ε • (z₁ • M.comparisonFirstSpace p U.grid U.grid_pos U.stable E hEL x)) *
    star (U.observable.observable k (z₂ • M.comparisonSecondSpace p U.grid U.grid_pos U.stable E hEL x)) = _
  rw [hswap, (V.tensorPower (multidegreeFactorial bound)).vertical a z₁ hz₁,
    U.observable.vertical k z₂ hz₂, hfreq, star_mul]
  let u := (V.tensorPower (multidegreeFactorial bound)).observable a
    (ε • M.comparisonFirstSpace p U.grid U.grid_pos U.stable E hEL x)
  let w := U.observable.observable k (M.comparisonSecondSpace p U.grid U.grid_pos U.stable E hEL x)
  change (c * u) * (star w * star c) = u * star w
  calc
    _ = (c * star c) * (u * star w) := by ring
    _ = _ := by rw [hc, one_mul]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

open scoped TensorProduct

theorem exists_nilcharacter {σ L : Type} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
    {M : D.MultidegreeStructure bound} {p q : ℝ} {η : L →ₗ[ℚ] ℚ}
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
    [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
    (U : M.SymmetricSquarefreeUnitData p η q)
    (g : M.filtration.realification.PolynomialOrbit) :
    ∃ W : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex bound => 1) q,
    ∃ e : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound))
        (Fin U.coordinateCount) ≃ Fin W.outputDim,
      W.dim = Fintype.card M.SquarefreeBasisIndex ∧
      (∀ k x, W.eval (e k) x = U.eval g k x) ∧
      ∀ (a : ReplicatedPermutation bound) k x,
        W.eval k (fun j => x ((replicatedPermutation bound a).symm j)) = W.eval k x := by
  classical
  obtain ⟨W, e, hdim, heval⟩ := NativeMultidegreeNilcharacter.exists_of_unit_data
    (M.squarefreeModel p U.grid U.grid_pos U.stable)
    (M.squarefreeModelMultidegree p U.grid U.grid_pos U.stable)
    (by simp) U.complexity
    (M.filtration.polarizeRealOrbit (fun j : ReplicatedIndex bound => j.1) g)
    U.observable U.dimension
  change ∀ k x, W.eval (e k) x = U.eval g k x at heval
  refine ⟨W, e, hdim, heval, ?_⟩
  intro a k x
  have h (y : ReplicatedIndex bound → ℤ) : W.eval k y = U.eval g (e.symm k) y := by
    simpa only [Equiv.apply_symm_apply] using heval (e.symm k) y
  rw [h, h, U.eval_permute]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct BigOperators NNReal

variable {σ L : Type} {I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) {p q v : ℝ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I v)
  (U : M.SymmetricSquarefreeUnitData p V.frequency q)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
    (max (s + 1) (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p U.grid U.grid_pos U.stable)
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]

include hEL in
theorem comparison_diagonal_expansion
    (hstep : s + 1 = ∑ i, bound i)
    (hEF : E.filtration = M.filtration.comparisonFiltration (fun j : ReplicatedIndex bound => j.1))
    {R : ℝ} (hR : 0 ≤ R) (hD : D.GeometryComplexityLE R) (hE : E.GeometryComplexityLE R)
    (hv : v ≤ R) (hq : q ≤ R)
    (hfirst : ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ R)
    (hsecond : ∀ j k, rationalLogHeight ((M.squarefreeFinBasis p).repr (E.basis j).val.2 k) ≤ R)
    (hc : (multidegreeFactorial bound : ℝ) ≤ Real.exp R)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup) (A : ℝ≥0)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (hA : (A : ℝ) ≤ Real.exp R)
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x))
    (a : Fin (multidegreeFactorial bound) → I)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount)) :
    Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s (comparisonDescentBudget s R)
      (fun x => (∏ j, V.observable (a j) (QuotientGroup.mk
          (M.filtration.realification.polynomialOrbitEval x g))) *
        star (U.eval (M.filtration.realification.normalizeMultidegreeOrbit g ε γ) k (fun j => x j.1)))) := by
  let := E.metricSpace
  obtain ⟨h, _, hdiag⟩ := M.exists_normalized_comparison_orbit p U.grid U.grid_pos U.stable
    E hEF hEL g ε γ hγ hfactor
  let K := comparisonProductLip (multidegreeFactorial bound) V.lipBound U.observable.lipBound A R
  have hLip : LipschitzWith K (M.comparisonVerticalProduct V U E hEL ε a k) :=
    M.comparisonVerticalProduct_lipschitz V U E hEL hR hD
      (U.complexity.1.mono _ hq) hE hfirst hsecond ε A hε a k
  let T : E.Niltest (fun _ : σ => 1) := {
    orbit := h
    observable := M.comparisonVerticalProduct V U E hEL ε a k
    normBound := 1
    lipBound := K
    norm_le := M.comparisonVerticalProduct_norm V U E hEL ε a k
    lipschitz := hLip }
  have hK : (K : ℝ) ≤ Real.exp ((R + 3) ^ 2 + 3 * R + 1) :=
    comparisonProductLip_le_exp _ _ _ _ hR hc
      (V.lip_bound.trans (Real.exp_le_exp.mpr hv))
      (U.observable.lip_bound.trans (Real.exp_le_exp.mpr hq)) hA
  have hcost : 0 ≤ comparisonProductCost R := by dsimp [comparisonProductCost]; positivity
  have hT : T.ComplexityLE (comparisonProductCost R) := by
    refine ⟨hE.mono E ?_, ?_⟩
    · dsimp [comparisonProductCost]
      nlinarith [sq_nonneg (R + 3)]
    · have hh := niltest_log_bound_of_exp (1 : ℝ≥0) K (a := 0)
        (b := (R + 3) ^ 2 + 3 * R + 1) (by norm_num) (by positivity) (by simp) hK
      simp only [NNReal.coe_one, zero_add] at hh
      change Real.log (2 + (1 : ℝ) + K) ≤ comparisonProductCost R
      dsimp [comparisonProductCost]
      linarith
  have heq : max (s + 1) (Fintype.card (ReplicatedIndex bound)) = s + 1 := by
    rw [replicatedIndex_card, ← hstep, max_self]
  have hexp : Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s
      (comparisonDescentBudget s R) T.eval) :=
    topInvariant_integer_expansion_of_step heq E T hcost hT
      (fun z hz x => M.comparisonVerticalProduct_top_invariant V U E hEL hstep hEF ε a k z hz x)
  have heval : T.eval = (fun x => (∏ j, V.observable (a j) (QuotientGroup.mk
        (M.filtration.realification.polynomialOrbitEval x g))) *
      star (U.eval (M.filtration.realification.normalizeMultidegreeOrbit g ε γ) k (fun j => x j.1))) := by
    funext x
    change M.comparisonVerticalProduct V U E hEL ε a k
      (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval _ x h)) = _
    unfold comparisonVerticalProduct
    rw [(hdiag x).1, (hdiag x).2]
    rfl
  exact heval ▸ hexp

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct BigOperators NNReal

variable {σ L : Type} {I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) {p q v : ℝ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I v)
  (U : M.SymmetricSquarefreeUnitData p V.frequency q)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
    (max (s + 1) (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p U.grid U.grid_pos U.stable)
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))]

include hEL in
theorem comparison_diagonal_equivalence
    (hstep : s + 1 = ∑ i, bound i)
    (hEF : E.filtration = M.filtration.comparisonFiltration (fun j : ReplicatedIndex bound => j.1))
    {R : ℝ} (hR : 0 ≤ R) (hD : D.GeometryComplexityLE R) (hE : E.GeometryComplexityLE R)
    (hv : v ≤ R) (hq : q ≤ R)
    (hfirst : ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ R)
    (hsecond : ∀ j k, rationalLogHeight ((M.squarefreeFinBasis p).repr (E.basis j).val.2 k) ≤ R)
    (hc : (multidegreeFactorial bound : ℝ) ≤ Real.exp R)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp R)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup) (A : ℝ≥0)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (hA : (A : ℝ) ≤ Real.exp R)
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) :
    NativeIntegerVectorEquivalence s (comparisonEquivalenceBudget s R)
      (fun (a : Fin (multidegreeFactorial bound) → I) x =>
        ∏ j, V.observable (a j) (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)))
      (fun k x => U.eval (M.filtration.realification.normalizeMultidegreeOrbit g ε γ) k (fun j => x j.1)) := by
  obtain ⟨hdesc, hbase, htensor⟩ := comparisonEquivalenceBudget_bounds s hR
  refine ⟨?_, U.dimension.trans ((Real.exp_le_exp.mpr hq).trans (Real.exp_le_exp.mpr hbase)), ?_⟩
  · have hfac : multidegreeFactorial bound ≤ (s + 1).factorial := by
      simpa only [← hstep] using multidegreeFactorial_le_total bound
    have hfacR : (multidegreeFactorial bound : ℝ) ≤ (s + 1).factorial := by exact_mod_cast hfac
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp R) ^ multidegreeFactorial bound :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hI _
      _ = Real.exp ((multidegreeFactorial bound : ℝ) * R) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (((s + 1).factorial : ℝ) * R) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hfacR hR)
      _ ≤ _ := Real.exp_le_exp.mpr htensor
  · intro a k
    obtain ⟨F⟩ := M.comparison_diagonal_expansion V U E hEL hstep hEF hR hD hE hv hq
      hfirst hsecond hc g ε γ A hγ hfactor hA hε a k
    exact ⟨F.mono hdesc⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped TensorProduct BigOperators

theorem exists_controlled_diagonal_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type} {I : Type*}
      [Fintype σ] [Fintype I] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {t d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L t d)
      (M : D.MultidegreeStructure bound), (∑ i, bound i) = t → t = s + 1 →
      ∀ {p : ℝ}, M.ComplexityLE p →
      ∀ (V : D.UnitVerticalObservable (D.filtration.realification.subgroup t) I p),
      (Fintype.card I : ℝ) ≤ Real.exp p → ∀ g : M.filtration.realification.PolynomialOrbit,
      let P := p + (s + 1).factorial + 1
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))
      letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
        IsModuleTopology.topologicalAddGroup ℝ _
      letI : T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
        realification_moduleTopology_t2 (M.squarefreeFinBasis P)
      ∃ U : M.SymmetricSquarefreeUnitData P V.frequency ((p + C) ^ C),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        M.filtration.realification.polynomialOrbitEval 0 g = ε * γ ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C)
          (fun (a : Fin (multidegreeFactorial bound) → I) x =>
            ∏ j, V.observable (a j) (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)))
          (fun k x => U.eval (M.filtration.realification.normalizeMultidegreeOrbit g ε γ) k (fun j => x j.1)) := by
  obtain ⟨a, _, hsymm⟩ := exists_controlled_symmetric_squarefree_unit (s + 1)
  obtain ⟨b, _, hnormal⟩ := exists_controlled_group_normalization (s + 1)
  obtain ⟨c, _, hequivalence⟩ := exists_comparisonEquivalence_cost s
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := X + Polynomial.C (s + 1).factorial + 1
  let Q₀ := (X + Polynomial.C a) ^ a
  let H₀ := P₀ + 1 + Polynomial.C ((s + 1) ^ 2)
  let G₀ := ((P₀ + Q₀ + 4) ^ 2 + H₀ + 6) ^ 11
  let N₀ := (X + Polynomial.C b) ^ b
  let R₀ := X + P₀ + Q₀ + H₀ + G₀ + N₀ + Polynomial.C (s + 1).factorial + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R₀ + Q₀ + (R₀ + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ L I _ _ _ _ _ _ _ _ t d bound D M hs ht p hM V hI g
  subst ht
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let P := p + (s + 1).factorial + 1
  let Q := (p + a) ^ a
  let H := comparisonBasisBudget (s + 1) P
  let G := comparisonGeometryBudget (s + 1) P Q
  let N := (p + b) ^ b
  let R := p + P + Q + H + G + N + (s + 1).factorial + 1
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hH : 0 ≤ H := by dsimp [H, comparisonBasisBudget]; positivity
  have hG : 0 ≤ G := by dsimp [G, comparisonGeometryBudget]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hF : 0 ≤ ((s + 1).factorial : ℝ) := Nat.cast_nonneg _
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpP : p ≤ P := by dsimp [P]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hQR : Q ≤ R := by dsimp [R]; linarith
  have hHR : H ≤ R := by dsimp [R]; linarith
  have hGR : G ≤ R := by dsimp [R]; linarith
  have hNR : N ≤ R := by dsimp [R]; linarith
  have hFR : ((s + 1).factorial : ℝ) ≤ R := by dsimp [R]; linarith
  let := moduleTopology ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
    realification_moduleTopology_t2 (M.squarefreeFinBasis P)
  obtain ⟨U⟩ := hsymm D M hs hM V.frequency V.height
  obtain ⟨E, hEF, hEL, hE, he⟩ := M.exists_comparison_model (hM.mono M hpP)
    U.grid U.grid_pos U.stable U.complexity.1
  rw [hs] at hE he
  let K := M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  obtain ⟨ε, γ, A, hγ, hfactor, _, hA, hε⟩ := hnormal D p hp hM.1
    (M.filtration.realification.polynomialOrbitEval 0 g)
  have hfirst (j k) : rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ R := by
    have hh := (he j (Sum.inl k)).trans hHR
    simpa only [Basis.prod_repr_inl] using hh
  have hsecond (j k) : rationalLogHeight ((M.squarefreeFinBasis P).repr (E.basis j).val.2 k) ≤ R := by
    have hh := (he j (Sum.inr k)).trans hHR
    simpa only [Basis.prod_repr_inr] using hh
  have hc : (multidegreeFactorial bound : ℝ) ≤ Real.exp R := by
    have hh : multidegreeFactorial bound ≤ (s + 1).factorial := by
      simpa only [hs] using multidegreeFactorial_le_total bound
    exact (Nat.cast_le.mpr hh).trans (hFR.trans (by linarith [Real.add_one_le_exp R]))
  have hcompare := M.comparison_diagonal_equivalence V U E hEL hs.symm hEF hR
    (hM.1.mono D hpR) (hE.mono E hGR) hpR hQR hfirst hsecond hc
    (hI.trans (Real.exp_le_exp.mpr hpR)) g ε γ A hγ hfactor
    (hA.trans (Real.exp_le_exp.mpr hNR)) hε
  have htotal : R + Q + (R + c) ^ c ≤ (p + C) ^ C := by
    simpa [R₀, G₀, H₀, N₀, P₀, Q₀, X, R, G, H, N, P, Q,
      comparisonGeometryBudget, comparisonBasisBudget, Polynomial.eval₂_pow] using hbudget p hp
  have hRc : 0 ≤ (R + c) ^ c := by positivity
  have hQC : Q ≤ (p + C) ^ C := by linarith
  have hcompareC : comparisonEquivalenceBudget s R ≤ (p + C) ^ C :=
    (hequivalence R hR).trans (by linarith)
  exact ⟨U.mono hQC, ε, γ, hγ, hfactor, hcompare.mono hcompareC⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open Module
open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_factorial_diagonal (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} [Fintype σ] (bound : σ → ℕ),
      (∑ i, bound i) = s + 1 → ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      ∃ V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex bound => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.dim ∧
        (∀ (e : ReplicatedPermutation bound) k x,
          V.eval k (fun j => x ((replicatedPermutation bound e).symm j)) = V.eval k x) ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C)
          (tensorVector W.eval (multidegreeFactorial bound))
          (fun k x => V.eval k (fun j => x j.1)) := by
  obtain ⟨C, hC, hcompare⟩ := exists_controlled_diagonal_comparison s
  refine ⟨C, hC, ?_⟩
  intro σ _ bound hs p W
  classical
  let T : W.model.UnitVerticalObservable
      (W.model.filtration.realification.subgroup (∑ i, bound i)) (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (W.multi.realSubgroup_top.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (W.multi.realSubgroup_top.symm ▸ hz) hL }
  let P := p + (s + 1).factorial + 1
  let := moduleTopology ℝ (ℝ ⊗[ℚ] W.multi.filtration.SquarefreeAlgebra
    (fun j : ReplicatedIndex bound => j.1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] W.multi.filtration.SquarefreeAlgebra
      (fun j : ReplicatedIndex bound => j.1)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] W.multi.filtration.SquarefreeAlgebra
      (fun j : ReplicatedIndex bound => j.1)) :=
    realification_moduleTopology_t2 (W.multi.squarefreeFinBasis P)
  obtain ⟨U, ε, γ, _, _, hE⟩ := hcompare W.model W.multi rfl hs W.complexity T
    (by simpa only [Fintype.card_fin] using W.output_bound) W.orbit
  obtain ⟨V, e, hdim, heval, hsymm⟩ := U.exists_nilcharacter
    (W.multi.filtration.realification.normalizeMultidegreeOrbit W.orbit ε γ)
  refine ⟨V, ?_, hsymm, ?_⟩
  · rw [hdim]
    simpa only [hs] using W.multi.squarefreeBasisIndex_card_le P
  refine hE.of_coordinate_maps _ _ id e.symm (fun _ _ => rfl) ?_ hE.left_dimension ?_ le_rfl
  · intro k x
    simpa only [Equiv.apply_symm_apply] using heval (e.symm k) (fun j => x j.1)
  · simpa only [Fintype.card_fin] using V.output_bound

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_symmetric_multilinearization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} [Fintype σ] (bound : σ → ℕ),
      (∑ i, bound i) = s + 1 → ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p),
      ∃ V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex bound => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.dim ∧
        (∀ (e : ReplicatedPermutation bound) k x,
          V.eval k (fun j => x ((replicatedPermutation bound e).symm j)) = V.eval k x) ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C)
          W.eval (fun k x => V.eval k (fun j => x j.1)) := by
  obtain ⟨a, _, hroot⟩ := exists_bounded_root_degree_equivalence s (s + 1).factorial
  obtain ⟨b, _, hdiagonal⟩ := exists_factorial_diagonal s
  obtain ⟨c, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  let A₀ := (X + Polynomial.C a) ^ a
  let B₀ := (A₀ + Polynomial.C b) ^ b
  let R₀ := A₀ + B₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (B₀ + (R₀ + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ _ bound hs p W
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : multidegreeFactorial bound ≤ (s + 1).factorial := by
    simpa only [hs] using multidegreeFactorial_le_total bound
  obtain ⟨R, hRdim, hER⟩ := hroot (multidegreeFactorial_pos bound) hq bound hs W
  obtain ⟨V, hVdim, hsymm, hEV⟩ := hdiagonal bound hs R
  let A := (p + a) ^ a
  let B := (A + b) ^ b
  let r := A + B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hr : 0 ≤ r := add_nonneg hA hB
  have hAr : A ≤ r := le_add_of_nonneg_right hB
  have hBr : B ≤ r := le_add_of_nonneg_left hA
  have hE := htrans hr (hER.mono hAr) (hEV.mono hBr)
    (tensorVector_unit R.eval R.unit_eval (multidegreeFactorial bound))
  have hb : B + (r + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, A₀, B₀, R₀, A, B, r, Polynomial.eval₂_pow] using hbudget p hp
  have hc : 0 ≤ (r + c) ^ c := by positivity
  have hBC : B ≤ (p + C) ^ C := by linarith
  have hEC : (r + c) ^ c ≤ (p + C) ^ C := by linarith
  exact ⟨V.mono hBC, hRdim ▸ hVdim, hsymm, hE.mono hEC⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem map_correlationInput {A B : Type*} (g : A → B) (h n : A) :
    (fun i => g (correlationInput h n i)) = correlationInput (g h) (g n) := by
  funext i
  fin_cases i <;> rfl

namespace NativeCorrelationStructure

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

theorem mixed_correlation_transfer {K : Type*} [Fintype K] {q : ℝ}
    {eta : K → (Fin 2 → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s q W.mixed.eval eta)
    (hunit : ∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) (h : W.shifts) :
    ∃ (k : K) (a : Fin (E.selectedExpansion (W.selectedWitness h).coordinate.1 k).count),
      Real.exp (-(p + 2 * q)) ≤
        ‖𝔼 x, multiplicativeDerivative f h.val x * star
          (eta k (correlationInput (h.val.val : ℤ) (x.val : ℤ)) *
            W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x *
            (W.selectedWitness h).test.evalCyclic N (fun _ => x) *
            ((E.selectedExpansion (W.selectedWitness h).coordinate.1 k).test a).eval
              (correlationInput (h.val.val : ℤ) (x.val : ℤ)))‖ := by
  have hinput (x : ZMod N) :
      (fun i => ((correlationInput h.val x i).val : ℤ)) =
        correlationInput (h.val.val : ℤ) (x.val : ℤ) :=
    map_correlationInput (fun z : ZMod N => (z.val : ℤ)) h.val x
  have hcorr : Real.exp (-p) ≤
      ‖𝔼 x, (multiplicativeDerivative f h.val x *
          star (W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x) *
          star ((W.selectedWitness h).test.evalCyclic N (fun _ => x))) *
        star (W.mixed.eval (W.selectedWitness h).coordinate.1
          (correlationInput (h.val.val : ℤ) (x.val : ℤ)))‖ := by
    simpa only [nativeCorrelationResidual, NativeMultidegreeNilcharacter.evalCyclic,
      hinput, mul_assoc, mul_left_comm, mul_comm]
      using (W.selectedWitness h).correlation
  obtain ⟨k, a, hka⟩ := E.transfer_sample_correlation Finset.univ
    (fun x : ZMod N => correlationInput (h.val.val : ℤ) (x.val : ℤ))
    (W.selectedWitness h).coordinate.1
    (fun x => multiplicativeDerivative f h.val x *
      star (W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x) *
      star ((W.selectedWitness h).test.evalCyclic N (fun _ => x)))
    (fun x _ => hunit _) hcorr
  refine ⟨k, a, ?_⟩
  simpa only [star_mul, mul_assoc, mul_left_comm, mul_comm] using hka

end NativeCorrelationStructure

theorem exists_multilinearized_correlation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f),
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        ∃ E : NativeIntegerVectorEquivalence s ((p + C) ^ C)
            W.mixed.eval (fun k x => V.eval k (fun j => x j.1)),
          ∀ h : W.shifts,
            ∃ (k : Fin V.outputDim)
              (a : Fin (E.selectedExpansion (W.selectedWitness h).coordinate.1 k).count),
              Real.exp (-(p + 2 * (p + C) ^ C)) ≤
                ‖𝔼 x, multiplicativeDerivative f h.val x * star
                  (V.eval k (fun j => correlationInput (h.val.val : ℤ) (x.val : ℤ) j.1) *
                    W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x *
                    (W.selectedWitness h).test.evalCyclic N (fun _ => x) *
                    ((E.selectedExpansion (W.selectedWitness h).coordinate.1 k).test a).eval
                      (correlationInput (h.val.val : ℤ) (x.val : ℤ)))‖ := by
  obtain ⟨C, hC, hmulti⟩ := NativeMultidegreeNilcharacter.exists_symmetric_multilinearization s
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W
  have hsum : (∑ i, mixedCorrelationDegree s i) = s + 1 := by
    rw [Fin.sum_univ_two]
    change 1 + s = s + 1
    omega
  obtain ⟨V, hdim, hsymm, E⟩ := hmulti (mixedCorrelationDegree s) hsum W.mixed
  exact ⟨V, hdim, hsymm, E, fun h => W.mixed_correlation_transfer E
    (fun x => V.unit_eval (fun j => x j.1)) h⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {p : ℝ}

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalWrapComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def cyclicCarry {N : ℕ} (h n : ZMod N) : ℝ :=
  if N ≤ h.val + n.val then 1 else 0

noncomputable def circleCarryCutoff (δ : ℝ≥0) (x : CircleFourier.Circle) : ℝ :=
  linearCutoff (1 / 6) δ (dist x ((1 / 2 : ℝ) : CircleFourier.Circle))

noncomputable def smoothCyclicCarry (N : ℕ) (δ : ℝ≥0) (x : Fin 2 → ℤ) : ℝ :=
  circleCarryCutoff δ ((((x 0 : ℝ) + (x 1 : ℝ)) / (3 * N) : ℝ) : CircleFourier.Circle)

theorem circleCarryCutoff_range (δ : ℝ≥0) (x : CircleFourier.Circle) :
    0 ≤ circleCarryCutoff δ x ∧ circleCarryCutoff δ x ≤ 1 := linearCutoff_range _ _ _

theorem circleCarryCutoff_lipschitz (δ : ℝ≥0) (hδ : 0 < δ) :
    LipschitzWith δ⁻¹ (circleCarryCutoff δ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply ((linearCutoff_lipschitz (1 / 6) δ hδ).dist_le_mul _ _).trans
  apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
  rw [Real.dist_eq]
  exact abs_dist_sub_le _ _ _

theorem circle_dist_half_of_unit_interval {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    dist (t : CircleFourier.Circle) ((1 / 2 : ℝ) : CircleFourier.Circle) = |t - 1 / 2| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  apply (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (by norm_num)).mpr
  norm_num only [abs_one]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem smoothCyclicCarry_eq_of_outside {N : ℕ} [NeZero N]
    (δ : ℝ≥0) (hδ : 0 < δ) (h n : ZMod N)
    (hn : n ∉ cyclicCutNeighborhood N ((N : ℤ) - h.val) (3 * N * (δ : ℝ))) :
    smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)] = cyclicCarry h n := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  let s : ℝ := h.val + n.val
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs2 : s < 2 * N := by
    have hh : (h.val : ℝ) < N := Nat.cast_lt.mpr h.val_lt
    have hn' : (n.val : ℝ) < N := Nat.cast_lt.mpr n.val_lt
    dsimp [s]
    linarith
  have ht0 : 0 ≤ s / (3 * N) := by positivity
  have ht2 : s / (3 * N) ≤ 2 / 3 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hdist := circle_dist_half_of_unit_interval ⟨ht0, ht2.trans (by norm_num)⟩
  change linearCutoff (1 / 6) δ (dist ((s / (3 * N) : ℝ) : CircleFourier.Circle)
    ((1 / 2 : ℝ) : CircleFourier.Circle)) = cyclicCarry h n
  rw [hdist]
  by_cases hw : N ≤ h.val + n.val
  · have hsN : (N : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hw
    have ht1 : 1 / 3 ≤ s / (3 * N) := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    rw [linearCutoff_eq_one _ _ hδ (abs_le.mpr ⟨by linarith, by linarith⟩)]
    simp only [cyclicCarry, hw, ite_true]
  · have hsN : s < (N : ℝ) := by dsimp [s]; exact_mod_cast Nat.lt_of_not_ge hw
    have hgap := lt_of_not_ge (fun hh => hn ((mem_cyclicCutNeighborhood _ _ _ _).mpr hh))
    simp only [Int.cast_sub, Int.cast_natCast] at hgap
    rw [abs_of_neg (by dsimp [s] at hsN; linarith)] at hgap
    have hfar : 1 / 6 + (δ : ℝ) ≤ |s / (3 * N) - 1 / 2| := by
      rw [abs_of_neg (by
        have : s / (3 * N) < 1 / 3 := (div_lt_iff₀ (by positivity)).mpr (by linarith)
        linarith)]
      have ht : s / (3 * N) ≤ 1 / 3 - (δ : ℝ) := by
        apply (div_le_iff₀ (by positivity)).mpr
        dsimp [s]
        nlinarith
      linarith
    rw [linearCutoff_eq_zero _ _ hfar]
    simp only [cyclicCarry, hw, ite_false]

theorem smoothCyclicCarry_mean_error {N : ℕ} [NeZero N] (δ : ℝ≥0) (hδ : 0 < δ) :
    (𝔼 x : Fin 2 → ZMod N,
      |cyclicCarry (x 0) (x 1) - smoothCyclicCarry N δ (fun j => ((x j).val : ℤ))|) ≤
      6 * (δ : ℝ) + 1 / N := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hrow (h : ZMod N) :
      (𝔼 n : ZMod N, |cyclicCarry h n - smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)]|) ≤
        6 * (δ : ℝ) + 1 / N := by
    let E := cyclicCutNeighborhood N ((N : ℤ) - h.val) (3 * N * (δ : ℝ))
    have hcard : (E.card : ℝ) ≤ 6 * N * (δ : ℝ) + 1 := by
      simpa only [show 2 * (3 * (N : ℝ) * (δ : ℝ)) = 6 * N * (δ : ℝ) by ring] using
        cyclicCutNeighborhood_card_le N ((N : ℤ) - h.val) (by positivity : 0 ≤ 3 * N * (δ : ℝ))
    have hcap (n : ZMod N) :
        |cyclicCarry h n - smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)]| ≤ 1 := by
      have hr := circleCarryCutoff_range δ
        (((((h.val : ℤ) : ℝ) + ((n.val : ℤ) : ℝ)) / (3 * N) : ℝ) : CircleFourier.Circle)
      change 0 ≤ smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)] ∧
        smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)] ≤ 1 at hr
      unfold cyclicCarry
      split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hh := expect_abs_le_of_exceptional_set E
      (fun n => cyclicCarry h n - smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)])
      (by norm_num : (0 : ℝ) ≤ 0) hcap (fun n hn => by
        rw [smoothCyclicCarry_eq_of_outside δ hδ h n hn, sub_self, abs_zero])
    simp only [zero_add, one_mul, ZMod.card] at hh
    apply hh.trans
    apply (div_le_iff₀ hN).mpr
    calc
      _ ≤ 6 * N * (δ : ℝ) + 1 := hcard
      _ = (6 * (δ : ℝ) + 1 / N) * N := by field_simp
  rw [expect_fin_two]
  exact (Finset.expect_le_expect (fun h _ => hrow h)).trans_eq (Fintype.expect_const _)

theorem exists_smoothCyclicCarry_expansion (N : ℕ) (δ : ℝ≥0) (hδ : 0 < δ)
    {p : ℝ} (hp : 0 ≤ p) (hinv : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 (p + 4)
      (fun x => (smoothCyclicCarry N δ x : ℂ))) := by
  let Ψ : (Fin 1 → CircleFourier.Circle) → ℂ := fun v => (circleCarryCutoff δ (v 0) : ℂ)
  have hΨ (v : Fin 1 → CircleFourier.Circle) : ‖Ψ v‖ ≤ (1 : ℝ≥0) := by
    change ‖(circleCarryCutoff δ (v 0) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (circleCarryCutoff_range δ _).1]
    exact (circleCarryCutoff_range δ _).2
  have hcoord : LipschitzWith 1 (fun v : Fin 1 → CircleFourier.Circle => v 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa only [NNReal.coe_one, one_mul] using dist_le_pi_dist v w 0
  have hLip : LipschitzWith δ⁻¹ Ψ := by
    simpa only [mul_one, one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitz.comp ((circleCarryCutoff_lipschitz δ hδ).comp hcoord)
  let T := RationalTorus.affineNiltest 1 0
    (fun _ : Fin 2 => fun _ : Fin 1 => 1 / (3 * (N : ℝ))) Ψ 1 δ⁻¹ hΨ hLip
  have hlog : Real.log (3 + (δ : ℝ)⁻¹) ≤ p + 4 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have h1 := Real.one_le_exp hp
    have h4 : 4 ≤ Real.exp (4 : ℝ) := by linarith [Real.add_one_le_exp (4 : ℝ)]
    rw [Real.exp_add]
    nlinarith
  have hT : T.ComplexityLE (p + 4) :=
    RationalTorus.affineNiltest_complexity 1 0
      (fun _ : Fin 2 => fun _ : Fin 1 => 1 / (3 * (N : ℝ))) Ψ 1 δ⁻¹ hΨ hLip
      (by linarith) (by norm_num; linarith)
      (by simpa only [NNReal.coe_one, NNReal.coe_inv, show (2 : ℝ) + 1 = 3 by norm_num] using hlog)
  refine ⟨NativeIntegerExpansion.ofTest T hT ?_⟩
  intro x
  simp only [T, RationalTorus.affineNiltest_eval, smoothCyclicCarry, Ψ,
    Fin.sum_univ_two,
    Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, zero_add]
  apply congrArg (fun t : ℝ => (circleCarryCutoff δ (t : CircleFourier.Circle) : ℂ))
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem smoothCyclicCarry_fixed_shift_mean_error {N : ℕ} [NeZero N]
    (δ : ℝ≥0) (hδ : 0 < δ) (k : ZMod N) :
    (𝔼 n : ZMod N, |cyclicCarry k n -
      smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]|) ≤ 6 * (δ : ℝ) + 1 / N := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  let E := cyclicCutNeighborhood N ((N : ℤ) - k.val) (3 * N * (δ : ℝ))
  have hcard : (E.card : ℝ) ≤ 6 * N * (δ : ℝ) + 1 := by
    simpa only [show 2 * (3 * (N : ℝ) * (δ : ℝ)) = 6 * N * (δ : ℝ) by ring] using
      cyclicCutNeighborhood_card_le N ((N : ℤ) - k.val) (by positivity : 0 ≤ 3 * N * (δ : ℝ))
  have hcap (n : ZMod N) :
      |cyclicCarry k n - smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]| ≤ 1 := by
    have hr := circleCarryCutoff_range δ
      (((((k.val : ℤ) : ℝ) + ((n.val : ℤ) : ℝ)) / (3 * N) : ℝ) : CircleFourier.Circle)
    change 0 ≤ smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)] ∧
      smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)] ≤ 1 at hr
    unfold cyclicCarry
    split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hh := expect_abs_le_of_exceptional_set E
    (fun n => cyclicCarry k n - smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)])
    (by norm_num : (0 : ℝ) ≤ 0) hcap (fun n hn => by
      rw [smoothCyclicCarry_eq_of_outside δ hδ k n hn, sub_self, abs_zero])
  simp only [zero_add, one_mul, ZMod.card] at hh
  apply hh.trans
  apply (div_le_iff₀ hN).mpr
  calc
    _ ≤ 6 * N * (δ : ℝ) + 1 := hcard
    _ = (6 * (δ : ℝ) + 1 / N) * N := by field_simp

theorem exists_fixed_shift_smoothCyclicCarry_expansion (N : ℕ) (δ : ℝ≥0)
    (hδ : 0 < δ) {p : ℝ} (hp : 0 ≤ p) (hinv : (δ : ℝ)⁻¹ ≤ Real.exp p) (k : ℤ) :
    Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 (p + 4)
      (fun x => (smoothCyclicCarry N δ ![k, x 1] : ℂ))) := by
  obtain ⟨E⟩ := exists_smoothCyclicCarry_expansion N δ hδ hp hinv
  let A : Fin 2 → Fin 2 → ℤ := ![![0, 0], ![0, 1]]
  let b : Fin 2 → ℤ := ![k, 0]
  have hinput (x : Fin 2 → ℤ) : integerAffineMap A b x = ![k, x 1] := by
    funext i
    fin_cases i <;> simp [integerAffineMap, A, b, Fin.sum_univ_two]
  simpa only [hinput] using
    (show Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 (p + 4)
      (fun x => (smoothCyclicCarry N δ (integerAffineMap A b x) : ℂ))) from
        ⟨E.affinePullback A b⟩)

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_quadratic_diagonal_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        (fun k (x : Fin 2 → ℤ) => W.eval k (fun _ => x 1 + x 0))
        (fun k : (Fin W.outputDim × Fin W.outputDim) ×
            (Fin W.outputDim × Fin W.outputDim) => fun x =>
          (W.eval k.1.1 (fun _ => x 1) * W.eval k.1.2 (correlationInput (x 1) (x 0))) *
            (W.eval k.2.1 (correlationInput (x 0) (x 1)) * W.eval k.2.2 (fun _ => x 0))) := by
  have hbound : mixedCorrelationDegree 1 = (fun _ : Fin 2 => 1) := by
    funext i
    fin_cases i <;> rfl
  rw [hbound]
  obtain ⟨C, hC, hexpand⟩ := exists_translation_expansion_equivalence ([0, 1] : List (Fin 2))
  refine ⟨C, hC, ?_⟩
  intro p W
  let a : Option (Fin 2) → Fin 2 := fun j => match j with
    | none => 0
    | some _ => 1
  have E := (hexpand W (by decide)).coordinatePullback a
  have hleft (k : Fin W.outputDim) (x : Fin 2 → ℤ) :
      W.eval k (coordinateTranslatedInput [0, 1] (fun j => x (a j))) =
        W.eval k (fun _ => x 1 + x 0) := by
    apply congrArg (W.eval k)
    funext i
    fin_cases i <;> simp [coordinateTranslatedInput, a]
  have hright (k : (Fin W.outputDim × Fin W.outputDim) ×
      (Fin W.outputDim × Fin W.outputDim)) (x : Fin 2 → ℤ) :
      coordinateTranslationExpansion W.eval [0, 1] k (fun j => x (a j)) =
      (W.eval k.1.1 (fun _ => x 1) * W.eval k.1.2 (correlationInput (x 1) (x 0))) *
        (W.eval k.2.1 (correlationInput (x 0) (x 1)) * W.eval k.2.2 (fun _ => x 0)) := by
    simp only [coordinateTranslationExpansion]
    apply congrArg₂ (fun z w : ℂ => z * w)
    · apply congrArg₂ (fun z w : ℂ => z * w)
      · rfl
      · apply congrArg (W.eval k.1.2)
        funext i
        fin_cases i <;> rfl
    · apply congrArg₂ (fun z w : ℂ => z * w)
      · apply congrArg (W.eval k.2.1)
        funext i
        fin_cases i <;> rfl
      · apply congrArg (W.eval k.2.2)
        funext i
        fin_cases i <;> rfl
  refine ⟨E.left_dimension, E.right_dimension, ?_⟩
  intro k l
  obtain ⟨F⟩ := E.expansion k l
  exact ⟨by simpa only [Fintype.card_fin, Nat.reduceSub, hleft, hright] using F⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def quadraticDiagonalDerivative (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0))

noncomputable def quadraticMixedTriple (a : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  star ((W.eval a.1 (correlationInput (x 1) (x 0)) *
    W.eval a.2.1 (correlationInput (x 0) (x 1))) * W.eval a.2.2 (fun _ => x 0))

theorem quadraticDiagonalDerivative_norm (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.quadraticDiagonalDerivative a x‖ ≤ 1 := by
  simp only [quadraticDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem exists_quadratic_diagonal_derivative_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        W.quadraticDiagonalDerivative W.quadraticMixedTriple := by
  obtain ⟨A, _, hdiag⟩ := exists_quadratic_diagonal_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + 3 * X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hsum : (p + A) ^ A + 3 * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have htwo : 2 * p ≤ (p + C) ^ C := by linarith
  have hthree : 3 * p ≤ (p + C) ^ C := by linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hdim2 := card_product_le_exp_two hdim hdim
  have hdim3 : (Fintype.card (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) : ℝ) ≤
      Real.exp (3 * p) := by
    rw [Fintype.card_prod, Nat.cast_mul]
    apply (mul_le_mul hdim hdim2 (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨hdim2.trans (Real.exp_le_exp.mpr htwo),
    hdim3.trans (Real.exp_le_exp.mpr hthree), ?_⟩
  intro a b
  obtain ⟨F⟩ := (hdiag W).expansion a.2 ((a.1, b.1), (b.2.1, b.2.2))
  have heq : (fun x : Fin 2 → ℤ => star (W.eval a.2 (fun _ => x 1 + x 0) *
      star ((W.eval a.1 (fun _ => x 1) * W.eval b.1 (correlationInput (x 1) (x 0))) *
        (W.eval b.2.1 (correlationInput (x 0) (x 1)) * W.eval b.2.2 (fun _ => x 0))))) =
      (fun x => W.quadraticDiagonalDerivative a x * star (W.quadraticMixedTriple b x)) := by
    funext x
    simp only [quadraticDiagonalDerivative, quadraticMixedTriple, star_mul, star_star]
    ring
  exact ⟨heq ▸ F.conjugate.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def cyclicDiagonalDerivative {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) : ℂ :=
  W.eval a.1 (fun _ => ((x 1).val : ℤ)) *
    star (W.eval a.2 (fun _ => ((x 0 + x 1).val : ℤ)))

noncomputable def wrappedDiagonalDerivative (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0 - N))

noncomputable def diagonalWrapCoefficient (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval k (fun _ => x 1 + x 0) * star (W.eval j (fun _ => x 1 + x 0 - N))

theorem wrappedDiagonalDerivative_norm (N : ℕ) (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.wrappedDiagonalDerivative N a x‖ ≤ 1 := by
  simp only [wrappedDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem diagonalWrapCoefficient_norm (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.diagonalWrapCoefficient N j k x‖ ≤ 1 := by
  simp only [diagonalWrapCoefficient, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem wrappedDiagonalDerivative_resolution (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.wrappedDiagonalDerivative N a x =
      ∑ k, W.diagonalWrapCoefficient N a.2 k x * W.quadraticDiagonalDerivative (a.1, k) x := by
  have h := complex_unit_vector_resolution
    (fun k => W.eval k (fun _ => x 1 + x 0)) (W.unit_eval _)
    (star (W.eval a.2 (fun _ => x 1 + x 0 - N)))
  calc
    _ = W.eval a.1 (fun _ => x 1) *
        ∑ k, (star (W.eval a.2 (fun _ => x 1 + x 0 - N)) *
          star (W.eval k (fun _ => x 1 + x 0))) * W.eval k (fun _ => x 1 + x 0) := by
      rw [← h]
      rfl
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [diagonalWrapCoefficient, quadraticDiagonalDerivative]
      ring

theorem cyclicDiagonalDerivative_branches {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    W.cyclicDiagonalDerivative a x =
      (1 - (cyclicCarry (x 0) (x 1) : ℂ)) *
          W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) +
        (cyclicCarry (x 0) (x 1) : ℂ) *
          W.wrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) := by
  have hval := cyclic_representative_add (x 0) (x 1)
  have hlt := (x 0).val_lt
  by_cases hw : N ≤ (x 0).val + (x 1).val
  · have hcut : N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_true, Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add,
      cyclicDiagonalDerivative, wrappedDiagonalDerivative]
    rw [hval, if_pos hcut]
  · have hcut : ¬N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_false, Complex.ofReal_zero, sub_zero, zero_mul, one_mul, add_zero,
      cyclicDiagonalDerivative, quadraticDiagonalDerivative]
    rw [hval, if_neg hcut, sub_zero]

theorem exists_diagonalWrapCoefficient_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ)
      (j k : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
        (W.diagonalWrapCoefficient N j k)) := by
  obtain ⟨C, hC, htranslate⟩ :=
    RationalFilteredNilmanifold.UnitVerticalObservable.exists_integer_translation_equivalence_budget 1
  refine ⟨C, hC, ?_⟩
  intro p W N j k
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have htop : W.multi.realSubgroup (mixedCorrelationDegree 1) =
      W.model.filtration.realification.subgroup 2 := by
    have hsum : (∑ i, mixedCorrelationDegree 1 i) = 2 := by decide
    simpa only [hsum] using W.multi.realSubgroup_top
  let V : W.model.UnitVerticalObservable (W.model.filtration.realification.subgroup 2)
      (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (htop.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (htop.symm ▸ hz) hL }
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have E := htranslate W.model V (W.multi.orbitToOrdinary W.orbit) hp W.complexity.1 hdim
    0 (fun _ => -(N : ℤ))
  let A : Fin 2 → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1 + x 0, map_zero' := by simp,
      map_add' := fun x y => by simp only [Pi.add_apply]; ring }
  obtain ⟨F⟩ := E.expansion k j
  have H := F.linearPullbackHom A
  have heval (i : Fin W.outputDim) (x : Fin 2 → ℤ) (c : ℤ) :
      V.observable i (QuotientGroup.mk (W.model.filtration.realification.polynomialOrbitEval
        (fun _ : Fin 2 => 1) ((fun l => A l x) + fun _ => c) (W.multi.orbitToOrdinary W.orbit))) =
      W.eval i (fun _ => x 1 + x 0 + c) := by
    rw [W.multi.orbitToOrdinary_eval]
    rfl
  have heq : (W.diagonalWrapCoefficient N j k) =
      (fun x => V.observable k (QuotientGroup.mk (W.model.filtration.realification.polynomialOrbitEval
          (fun _ : Fin 2 => 1) ((fun l => A l x) + 0) (W.multi.orbitToOrdinary W.orbit))) *
        star (V.observable j (QuotientGroup.mk (W.model.filtration.realification.polynomialOrbitEval
          (fun _ : Fin 2 => 1) ((fun l => A l x) + fun _ => -(N : ℤ))
          (W.multi.orbitToOrdinary W.orbit))))) := by
    funext x
    rw [show (0 : Fin 2 → ℤ) = (fun _ => 0) from rfl, heval, heval]
    simp only [diagonalWrapCoefficient, add_zero, sub_eq_add_neg]
  exact ⟨heq.symm ▸ H⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMultilinearQuadruples
namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

theorem exists_fixed_transferred_correlation {K : Type*} [Fintype K] {q : ℝ}
    {eta : K → (Fin 2 → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s q W.mixed.eval eta)
    (hunit : ∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) :
    ∃ (j : Fin W.mixed.outputDim) (k : K)
      (a : Fin (E.selectedExpansion j k).count) (i : Fin W.family.outputDim)
      (H : Finset (ZMod N)), H ⊆ W.shifts ∧ H.Nonempty ∧
      Real.exp (-(3 * p + 2 * q)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, ∃ hh : h ∈ W.shifts,
        (W.selectedWitness ⟨h, hh⟩).coordinate = (j, i) ∧
        Real.exp (-(p + 2 * q)) ≤
          ‖𝔼 x, multiplicativeDerivative f h x * star
            (eta k (correlationInput (h.val : ℤ) (x.val : ℤ)) *
              W.family.evalCyclic N i h x *
              (W.selectedWitness ⟨h, hh⟩).test.evalCyclic N (fun _ => x) *
              ((E.selectedExpansion j k).test a).eval
                (correlationInput (h.val : ℤ) (x.val : ℤ)))‖ := by
  classical
  let P := E.ExpansionIndex × Fin W.family.outputDim
  let rel (h : ZMod N) (_ : Unit) (c : P) : Prop :=
    ∃ hh : h ∈ W.shifts,
      (W.selectedWitness ⟨h, hh⟩).coordinate = (c.1.1, c.2) ∧
      Real.exp (-(p + 2 * q)) ≤
        ‖𝔼 x, multiplicativeDerivative f h x * star
          (eta c.1.2.1 (correlationInput (h.val : ℤ) (x.val : ℤ)) *
            W.family.evalCyclic N c.2 h x *
            (W.selectedWitness ⟨h, hh⟩).test.evalCyclic N (fun _ => x) *
            ((E.selectedExpansion c.1.1 c.1.2.1).test c.1.2.2).eval
              (correlationInput (h.val : ℤ) (x.val : ℤ)))‖
  have hchoice : ∀ h ∈ W.shifts, ∀ u, ∃ c, rel h u c := by
    intro h hh _
    obtain ⟨k, a, hcorr⟩ := W.mixed_correlation_transfer E hunit ⟨h, hh⟩
    refine ⟨(⟨(W.selectedWitness ⟨h, hh⟩).coordinate.1, k, a⟩,
      (W.selectedWitness ⟨h, hh⟩).coordinate.2), hh, ?_, hcorr⟩
    exact (Prod.eta _).symm
  have hcount : (Fintype.card P : ℝ) ≤ Real.exp (2 * p + 2 * q) := by
    have hleft : (Fintype.card (Fin W.mixed.outputDim) : ℝ) ≤ Real.exp p := by
      simpa only [Fintype.card_fin] using W.mixed.output_bound
    have hindex := E.expansionIndex_card_bound hleft E.right_dimension
    change (Fintype.card (E.ExpansionIndex × Fin W.family.outputDim) : ℝ) ≤ _
    rw [Fintype.card_prod, Nat.cast_mul, Fintype.card_fin]
    calc
      _ ≤ Real.exp (p + q + q) * Real.exp p :=
        mul_le_mul hindex W.family.output_bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨c, H, hsub, hH, hsize, hfixed⟩ :=
    exists_large_fixed_choices W.shifts W.nonempty rel hchoice hcount
  have hsize' : Real.exp (-(2 * p + 2 * q)) * (W.shifts.card : ℝ) ≤ (H.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize
  refine ⟨(c ()).1.1, (c ()).1.2.1, (c ()).1.2.2, (c ()).2, H, hsub, hH,
    ?_, fun h hh => hfixed h hh ()⟩
  calc
    _ = Real.exp (-(2 * p + 2 * q)) *
        (Real.exp (-p) * Fintype.card (ZMod N)) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-(2 * p + 2 * q)) * (W.shifts.card : ℝ) :=
      mul_le_mul_of_nonneg_left W.density (Real.exp_nonneg _)
    _ ≤ _ := hsize'

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_fixed_multilinearized_correlation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f),
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        ∃ E : NativeIntegerVectorEquivalence s ((p + C) ^ C)
            W.mixed.eval (fun k x => V.eval k (fun j => x j.1)),
          ∃ (j : Fin W.mixed.outputDim) (k : Fin V.outputDim)
            (a : Fin (E.selectedExpansion j k).count) (i : Fin W.family.outputDim)
            (H : Finset (ZMod N)), H ⊆ W.shifts ∧ H.Nonempty ∧
            Real.exp (-(3 * p + 2 * (p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
            ∀ h ∈ H, ∃ hh : h ∈ W.shifts,
              (W.selectedWitness ⟨h, hh⟩).coordinate = (j, i) ∧
              Real.exp (-(p + 2 * (p + C) ^ C)) ≤
                ‖𝔼 x, multiplicativeDerivative f h x * star
                  (V.eval k (fun l => correlationInput (h.val : ℤ) (x.val : ℤ) l.1) *
                    W.family.evalCyclic N i h x *
                    (W.selectedWitness ⟨h, hh⟩).test.evalCyclic N (fun _ => x) *
                    ((E.selectedExpansion j k).test a).eval
                      (correlationInput (h.val : ℤ) (x.val : ℤ)))‖ := by
  obtain ⟨C, hC, htransfer⟩ := exists_multilinearized_correlation s
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W
  obtain ⟨V, hdim, hsymm, E, _⟩ := htransfer W
  exact ⟨V, hdim, hsymm, E, W.exists_fixed_transferred_correlation E
    (fun x => V.unit_eval (fun j => x j.1))⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_weighted_multilinear_correlation_with_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C) W.mixed.eval
          (fun k x => V.eval k (fun j => x j.1)) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
            (fun _ : Unit => fun x => multiplicativeDerivative f h x * star
              ((V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
                W.family.evalCyclic N i h x) * weight x))) := by
  obtain ⟨a, _, hmulti⟩ := exists_fixed_multilinearized_correlation s
  obtain ⟨c, _, hsplit⟩ := exists_split_global_error s
  let X : Polynomial ℕ := Polynomial.X
  let Q₀ := (X + Polynomial.C a) ^ a
  let B₀ := 2 * X + 3 * Q₀ + 3
  let R₀ := (B₀ + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (4 * X + 4 * Q₀ + R₀ + 4)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  let b := 2 * p + 3 * q + 3
  let R := (b + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 2 ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hpb : p ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hqb : q ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hcb : p + 2 * q ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpoly : 4 * p + 4 * q + R + 4 ≤ (p + C) ^ C := by
    simpa [X, Q₀, B₀, R₀, q, b, R, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  have hRC : R ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  have hdenseC : 3 * p + 2 * q + R ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  obtain ⟨V, hdim, hsymm, E, j, k, z, i, H, hsub, hH, hdense, hcorr⟩ := hmulti W
  let T := (E.selectedExpansion j k).test z
  let m (h x : ZMod N) :=
    V.eval k (fun l => correlationInput (h.val : ℤ) (x.val : ℤ) l.1) *
      W.family.evalCyclic N i h x
  have hm (h x : ZMod N) : ‖m h x‖ ≤ 1 := by
    dsimp only [m]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hinput (h n : ℤ) : correlationInput h n = ![h, n] := by
    funext t
    fin_cases t <;> rfl
  have hcor' (h : ZMod N) (hh : h ∈ H) : Real.exp (-b) ≤
      ‖𝔼 x, multiplicativeDerivative f h x * star
        (m h x * (W.selectedWitness ⟨h, hsub hh⟩).test.evalCyclic N (fun _ => x) *
          T.eval ![(h.val : ℤ), (x.val : ℤ)])‖ := by
    obtain ⟨hh', _, hc⟩ := hcorr h hh
    apply (Real.exp_le_exp.mpr (neg_le_neg hcb)).trans
    simpa only [m, T, hinput] using hc
  obtain ⟨weight, S, hweight, hSH, hS, hsize, hnew⟩ := hsplit W T b hb hpb
    (((E.selectedExpansion j k).complexity z).mono hqb) H hsub hH m hm hf hcor'
  have htotal : Real.exp (-(3 * p + 2 * q + R)) * Fintype.card (ZMod N) ≤ (S.card : ℝ) := by
    calc
      _ = Real.exp (-R) * (Real.exp (-(3 * p + 2 * q)) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-R) * (H.card : ℝ) := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  refine ⟨V.mono hqC, hdim, hsymm, E.mono hqC, k, i, weight, S, hweight, hSH.trans hsub, hS, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hdenseC))
      (Nat.cast_nonneg _)).trans htotal
  · intro h hh
    obtain ⟨Z⟩ := hnew h hh
    exact ⟨Z.mono hRC⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_weighted_multilinear_correlation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
            (fun _ : Unit => fun x => multiplicativeDerivative f h x * star
              ((V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
                W.family.evalCyclic N i h x) * weight x))) := by
  obtain ⟨a, _, hmulti⟩ := exists_fixed_multilinearized_correlation s
  obtain ⟨c, _, hsplit⟩ := exists_split_global_error s
  let X : Polynomial ℕ := Polynomial.X
  let Q₀ := (X + Polynomial.C a) ^ a
  let B₀ := 2 * X + 3 * Q₀ + 3
  let R₀ := (B₀ + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (4 * X + 4 * Q₀ + R₀ + 4)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  let b := 2 * p + 3 * q + 3
  let R := (b + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 2 ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hpb : p ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hqb : q ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hcb : p + 2 * q ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpoly : 4 * p + 4 * q + R + 4 ≤ (p + C) ^ C := by
    simpa [X, Q₀, B₀, R₀, q, b, R, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  have hRC : R ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  have hdenseC : 3 * p + 2 * q + R ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  obtain ⟨V, hdim, hsymm, E, j, k, z, i, H, hsub, hH, hdense, hcorr⟩ := hmulti W
  let T := (E.selectedExpansion j k).test z
  let m (h x : ZMod N) :=
    V.eval k (fun l => correlationInput (h.val : ℤ) (x.val : ℤ) l.1) *
      W.family.evalCyclic N i h x
  have hm (h x : ZMod N) : ‖m h x‖ ≤ 1 := by
    dsimp only [m]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hinput (h n : ℤ) : correlationInput h n = ![h, n] := by
    funext t
    fin_cases t <;> rfl
  have hcor' (h : ZMod N) (hh : h ∈ H) : Real.exp (-b) ≤
      ‖𝔼 x, multiplicativeDerivative f h x * star
        (m h x * (W.selectedWitness ⟨h, hsub hh⟩).test.evalCyclic N (fun _ => x) *
          T.eval ![(h.val : ℤ), (x.val : ℤ)])‖ := by
    obtain ⟨hh', _, hc⟩ := hcorr h hh
    apply (Real.exp_le_exp.mpr (neg_le_neg hcb)).trans
    simpa only [m, T, hinput] using hc
  obtain ⟨weight, S, hweight, hSH, hS, hsize, hnew⟩ := hsplit W T b hb hpb
    (((E.selectedExpansion j k).complexity z).mono hqb) H hsub hH m hm hf hcor'
  have htotal : Real.exp (-(3 * p + 2 * q + R)) * Fintype.card (ZMod N) ≤ (S.card : ℝ) := by
    calc
      _ = Real.exp (-R) * (Real.exp (-(3 * p + 2 * q)) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-R) * (H.card : ℝ) := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  refine ⟨V.mono hqC, hdim, hsymm, k, i, weight, S, hweight, hSH.trans hsub, hS, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hdenseC))
      (Nat.cast_nonneg _)).trans htotal
  · intro h hh
    obtain ⟨Z⟩ := hnew h hh
    exact ⟨Z.mono hRC⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_multilinear_quadruples_with_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C) W.mixed.eval
          (fun k x => V.eval k (fun j => x j.1)) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∃ U : NativeCrossWitnesses (s - 1) N ((p + C) ^ C)
              (fun x => f x * star (weight x)) f
              (fun h x => V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
                W.family.evalCyclic N i h x) H,
            ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
                Real.exp (-((p + C) ^ C)) ≤
                  additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 := by
  obtain ⟨a, _, hweighted⟩ := exists_weighted_multilinear_correlation_with_equivalence s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (13 * (X + Polynomial.C a) ^ a + 2)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hQbudget : 13 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hQbudget]
  obtain ⟨V, hdim, hsymm, E, k, i, weight, H, hweight, hsub, hH, hdense, hcorr⟩ := hweighted W hf
  let f₀ (x : ZMod N) := f x * star (weight x)
  let m (h x : ZMod N) := V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
    W.family.evalCyclic N i h x
  have hf₀ (x : ZMod N) : ‖f₀ x‖ ≤ 1 := by
    simp only [f₀, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf x)).trans (hweight x)
  have hm (h x : ZMod N) : ‖m h x‖ ≤ 1 := by
    simp only [m, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hc (h : H) : Nonempty (NativeVectorCorrelation (s - 1) N q (nativeCrossResidual f₀ f m h.val)) := by
    obtain ⟨R⟩ := hcorr h.val h.property
    refine ⟨{ R with correlation := ?_ }⟩
    simpa only [nativeCrossResidual, f₀, m, multiplicativeDerivative, star_mul,
      mul_assoc, mul_left_comm, mul_comm] using R.correlation
  let U : NativeCrossWitnesses (s - 1) N q f₀ f m H := fun h => Classical.choice (hc h)
  obtain ⟨Q, hQ, hsize, hquad⟩ := U.exists_quadruples_budget hH hf₀ hf hm hdense
  refine ⟨V.mono hqC, hdim, hsymm, E.mono hqC, k, i, weight, H, hweight, hsub, hH, ?_, U.mono hqC,
    Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hQbudget))
      (by positivity)).trans hsize
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, hcor⟩ := hquad t ht
    refine ⟨h₁, h₂, h₃, h₄, ?_⟩
    change Real.exp (-((p + C) ^ C)) ≤ additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2
    exact (Real.exp_le_exp.mpr (neg_le_neg hQbudget)).trans hcor

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_multilinear_quadruples (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∃ U : NativeCrossWitnesses (s - 1) N ((p + C) ^ C)
              (fun x => f x * star (weight x)) f
              (fun h x => V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
                W.family.evalCyclic N i h x) H,
            ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
                Real.exp (-((p + C) ^ C)) ≤
                  additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 := by
  obtain ⟨a, _, hweighted⟩ := exists_weighted_multilinear_correlation s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (13 * (X + Polynomial.C a) ^ a + 2)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hQbudget : 13 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hQbudget]
  obtain ⟨V, hdim, hsymm, k, i, weight, H, hweight, hsub, hH, hdense, hcorr⟩ := hweighted W hf
  let f₀ (x : ZMod N) := f x * star (weight x)
  let m (h x : ZMod N) := V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
    W.family.evalCyclic N i h x
  have hf₀ (x : ZMod N) : ‖f₀ x‖ ≤ 1 := by
    simp only [f₀, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf x)).trans (hweight x)
  have hm (h x : ZMod N) : ‖m h x‖ ≤ 1 := by
    simp only [m, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hc (h : H) : Nonempty (NativeVectorCorrelation (s - 1) N q (nativeCrossResidual f₀ f m h.val)) := by
    obtain ⟨R⟩ := hcorr h.val h.property
    refine ⟨{ R with correlation := ?_ }⟩
    simpa only [nativeCrossResidual, f₀, m, multiplicativeDerivative, star_mul,
      mul_assoc, mul_left_comm, mul_comm] using R.correlation
  let U : NativeCrossWitnesses (s - 1) N q f₀ f m H := fun h => Classical.choice (hc h)
  obtain ⟨Q, hQ, hsize, hquad⟩ := U.exists_quadruples_budget hH hf₀ hf hm hdense
  refine ⟨V.mono hqC, hdim, hsymm, k, i, weight, H, hweight, hsub, hH, ?_, U.mono hqC,
    Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hQbudget))
      (by positivity)).trans hsize
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, hcor⟩ := hquad t ht
    refine ⟨h₁, h₂, h₃, h₄, ?_⟩
    change Real.exp (-((p + C) ^ C)) ≤ additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2
    exact (Real.exp_le_exp.mpr (neg_le_neg hQbudget)).trans hcor

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedTranslationAffineInput
namespace OAI

section

namespace Erdos3

def mixedTranslationSlope (s : ℕ) : Option (ReplicatedIndex (mixedCorrelationDegree s)) → ℤ
  | none => 0
  | some j => if j.1 = 1 then 1 else 0

def mixedTranslationIntercept (s : ℕ) (h δ : ℤ) :
    Option (ReplicatedIndex (mixedCorrelationDegree s)) → ℤ
  | none => δ
  | some j => if j.1 = 1 then 0 else h

theorem mixedTranslationSample_affine (s : ℕ) (h n δ : ℤ) :
    (fun j => mixedTranslationIntercept s h δ j + mixedTranslationSlope s j * n) =
      mixedTranslationSample s ![h, n, δ] := by
  funext j
  rcases j with _ | ⟨j, k⟩
  · simp [mixedTranslationIntercept, mixedTranslationSlope, mixedTranslationSample]
  · fin_cases j <;> simp [mixedTranslationIntercept, mixedTranslationSlope,
      mixedTranslationSample, correlationInput]
    rfl

theorem mixedTranslationSlope_replaced_none (s : ℕ) (i : ReplicatedIndex (mixedCorrelationDegree s)) :
    mixedTranslationSlope s (coordinateReplaceIndex i none) = 0 := by
  simp [coordinateReplaceIndex, mixedTranslationSlope]

theorem mixedTranslationSlope_replaced_vanishes (s : ℕ)
    (i j : ReplicatedIndex (mixedCorrelationDegree s))
    (hj : j ∉ (mixedEvaluationCoordinates s).erase i) :
    mixedTranslationSlope s (coordinateReplaceIndex i (some j)) = 0 := by
  by_cases hji : j = i
  · simp [coordinateReplaceIndex, hji, mixedTranslationSlope]
  · have hj₁ : j.1 ≠ 1 := by
      intro h
      exact hj (Finset.mem_erase.mpr ⟨hji, (mem_mixedEvaluationCoordinates s j).mpr h⟩)
    simp [coordinateReplaceIndex, hji, mixedTranslationSlope, hj₁]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem select_sample_product_correlation {σ X : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ}
    {eta : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion w s p eta)
    (S : Finset X) (sample : X → σ → ℤ) (f : X → ℂ)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * eta (sample u)‖) :
    ∃ i : Fin E.count, Real.exp (-(q + p)) ≤
      ‖𝔼 u ∈ S, f u * (E.test i).eval (sample u)‖ := by
  have hpoint (u : X) : f u * eta (sample u) =
      ∑ i, E.coefficient i * (f u * (E.test i).eval (sample u)) := by
    rw [E.eval, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hmean : (𝔼 u ∈ S, f u * eta (sample u)) =
      ∑ i, E.coefficient i * (𝔼 u ∈ S, f u * (E.test i).eval (sample u)) := by
    calc
      _ = 𝔼 u ∈ S, ∑ i, E.coefficient i * (f u * (E.test i).eval (sample u)) :=
        Finset.expect_congr rfl (fun u _ => hpoint u)
      _ = _ := by simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  obtain ⟨i, hi⟩ := exists_large_weighted_term E.coefficient
    (fun i => 𝔼 u ∈ S, f u * (E.test i).eval (sample u))
    (Real.exp_pos (-q)) (Real.exp_pos p) E.cost (by rwa [← hmean])
  refine ⟨i, ?_⟩
  have heq : Real.exp (-q) / Real.exp p = Real.exp (-(q + p)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rwa [heq] at hi

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_frozen_translation_expansion {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) (l : List σ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (S : Finset σ) (A b : Option σ → ℤ) (a : BinaryTensorIndex (Fin W.outputDim) l.length),
      A none = 0 → (∀ i, i ∉ S → A (some i) = 0) →
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (∑ i ∈ S, bound i) ((p + C) ^ C)
        (fun x => coordinateTranslationExpansion W.eval l a (fun j => b j + A j * x ()))) := by
  induction l with
  | nil =>
    obtain ⟨C, hC, hfreeze⟩ := exists_frozen_affine_expansion bound
    refine ⟨C, hC, ?_⟩
    intro p W S A b a _ hA
    obtain ⟨E, _⟩ := hfreeze W S (fun i => A (some i)) (fun i => b (some i)) a hA
    exact ⟨E⟩
  | cons i l ih =>
    obtain ⟨a, _, hprevious⟩ := ih
    obtain ⟨c, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
    let X : Polynomial ℕ := Polynomial.X
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
      (((X + Polynomial.C a) ^ a + Polynomial.C c) ^ c)
    refine ⟨C, hC, ?_⟩
    intro p W S A b k hnone hA
    have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
    let q := (p + a) ^ a
    have hq : 0 ≤ q := by dsimp [q]; positivity
    let A' (j : Option σ) := A (coordinateReplaceIndex i j)
    let b' (j : Option σ) := b (coordinateReplaceIndex i j)
    have hnone' : A' none = 0 := by simp [A', coordinateReplaceIndex, hnone]
    have hA' (j : σ) (hj : j ∉ S) : A' (some j) = 0 := by
      by_cases hji : j = i
      · simp [A', coordinateReplaceIndex, hji, hnone]
      · simp [A', coordinateReplaceIndex, hji, hA j hj]
    obtain ⟨E⟩ := hprevious W S A b k.1 hnone hA
    obtain ⟨F⟩ := hprevious W S A' b' k.2 hnone' hA'
    obtain ⟨R⟩ := hmul hq E F
    have hcost : (q + c) ^ c ≤ (p + C) ^ C := by
      simpa [q, X, Polynomial.eval₂_pow] using hbudget p hp
    exact ⟨R.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

noncomputable def untranslatedMixedProduct {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (k : Fin 4 → Fin V.outputDim) (h₁ h₂ h₃ h₄ n : ℤ) : ℂ :=
  star (V.eval (k 0) (fun j => correlationInput h₁ n j.1)) *
    V.eval (k 1) (fun j => correlationInput h₂ n j.1) *
    V.eval (k 2) (fun j => correlationInput h₃ n j.1) *
    star (V.eval (k 3) (fun j => correlationInput h₄ n j.1))

noncomputable def mixedParallelogramProduct {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (k : Fin 4 → Fin V.outputDim) (x : Fin 4 → ℤ) : ℂ :=
  untranslatedMixedProduct V k (x 0) (x 1) (x 2) (x 1 + x 2 - x 0) (x 3)

theorem untranslatedMixedProduct_eq {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (k : Fin 4 → Fin V.outputDim) (h₁ h₂ h₃ h₄ n : ℤ)
    (hrel : -h₁ + h₂ + h₃ - h₄ = 0) :
    untranslatedMixedProduct V k h₁ h₂ h₃ h₄ n = mixedParallelogramProduct V k ![h₁, h₂, h₃, n] := by
  have hh₄ : h₄ = h₂ + h₃ - h₁ := by omega
  subst h₄
  rfl

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_replaced_mixed_translation_expansion (s : ℕ)
    (l : List (ReplicatedIndex (mixedCorrelationDegree s))) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
      (i : ReplicatedIndex (mixedCorrelationDegree s)), i.1 = 1 →
      ∀ (h δ : ℤ) (a : BinaryTensorIndex (Fin V.outputDim) l.length),
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => coordinateTranslationExpansion V.eval l a
            (coordinateReplaceInput i (mixedTranslationSample s ![h, x (), δ])))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_frozen_translation_expansion
    (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) l
  refine ⟨C, hC, ?_⟩
  intro p V i hi h δ a
  let S := (mixedEvaluationCoordinates s).erase i
  let A (j) := mixedTranslationSlope s (coordinateReplaceIndex i j)
  let b (j) := mixedTranslationIntercept s h δ (coordinateReplaceIndex i j)
  have hA : ∀ j, j ∉ S → A (some j) = 0 :=
    fun j hj => mixedTranslationSlope_replaced_vanishes s i j hj
  have hdegree : (∑ _j ∈ S, (1 : ℕ)) = s - 1 := by
    simpa only [Finset.sum_const, smul_eq_mul, mul_one] using
      mixedEvaluationCoordinates_erase_card s i hi
  have hinput (x : Unit → ℤ) : (fun j => b j + A j * x ()) =
      coordinateReplaceInput i (mixedTranslationSample s ![h, x (), δ]) := by
    change coordinateReplaceInput i
      (fun j => mixedTranslationIntercept s h δ j + mixedTranslationSlope s j * x ()) = _
    rw [mixedTranslationSample_affine]
  have R := hfreeze V S A b a (mixedTranslationSlope_replaced_none s i) hA
  simpa only [hdegree, hinput] using R

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_parallelogram_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun k : Fin V.outputDim × Fin V.outputDim => fun x : Fin 4 → ℤ =>
          V.eval k.1 (fun j => correlationInput (x 1) (x 3) j.1) *
            V.eval k.2 (fun j => correlationInput (x 2) (x 3) j.1))
        (fun k : Fin V.outputDim × Fin V.outputDim => fun x : Fin 4 → ℤ =>
          V.eval k.1 (fun j => correlationInput (x 0) (x 3) j.1) *
            V.eval k.2 (fun j => correlationInput (x 1 + x 2 - x 0) (x 3) j.1)) := by
  obtain ⟨C, hC, hpair⟩ := exists_coordinate_parallelogram_equivalence
    (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1)
  refine ⟨C, hC, ?_⟩
  intro p V
  let v (i : Fin 4) : ((Fin 4 → ℤ) →+ ℤ) := ⟨⟨fun x => x i, rfl⟩, fun _ _ => rfl⟩
  have hv (i : Fin 4) (x : Fin 4 → ℤ) : v i x = x i := rfl
  have E := hpair V (mixedShiftCoordinate s) rfl (v 0) (v 1) (v 2) (v 3)
  have hdegree : (∑ _j : ReplicatedIndex (mixedCorrelationDegree s), (1 : ℕ)) - 1 = s := by
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, replicatedMixed_card,
      Nat.add_sub_cancel]
  simpa only [hdegree, hv, ← mixed_input_eq_coordinateConstant] using E

theorem exists_mixed_parallelogram_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
      (k : Fin 4 → Fin V.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) s ((p + C) ^ C)
        (mixedParallelogramProduct V k)) := by
  obtain ⟨C, hC, hpair⟩ := exists_mixed_parallelogram_equivalence s
  refine ⟨C, hC, ?_⟩
  intro p V k
  obtain ⟨R⟩ := (hpair V).expansion (k 1, k 2) (k 0, k 3)
  have heq : (fun x : Fin 4 → ℤ =>
      (V.eval (k 1) (fun j => correlationInput (x 1) (x 3) j.1) *
        V.eval (k 2) (fun j => correlationInput (x 2) (x 3) j.1)) *
      star (V.eval (k 0) (fun j => correlationInput (x 0) (x 3) j.1) *
        V.eval (k 3) (fun j => correlationInput (x 1 + x 2 - x 0) (x 3) j.1))) =
      mixedParallelogramProduct V k := by
    funext x
    simp only [mixedParallelogramProduct, untranslatedMixedProduct, star_mul]
    ring
  exact ⟨heq ▸ R⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_remainder_expansion_of_evaluation_coordinates (s : ℕ)
    (l : List (ReplicatedIndex (mixedCorrelationDegree s))) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
      (∀ i ∈ l, i.1 = 1) → ∀ (h δ : ℤ) (a : BinaryTensorIndex (Fin V.outputDim) l.length),
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => translationExpansionRemainder V.eval l a (mixedTranslationSample s ![h, x (), δ]))) := by
  induction l with
  | nil =>
    refine ⟨2, le_rfl, ?_⟩
    intro p V _ h δ a
    have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
    have hbudget : 2 ≤ (p + (2 : ℕ)) ^ (2 : ℕ) := by
      norm_num only [Nat.cast_ofNat]
      nlinarith only [hp, sq_nonneg p]
    exact ⟨NativeIntegerExpansion.constOne (fun _ : Unit => 1) (s - 1) hbudget⟩
  | cons i l ih =>
    obtain ⟨a, _, hprevious⟩ := ih
    obtain ⟨b, _, hright⟩ := exists_replaced_mixed_translation_expansion s l
    obtain ⟨c, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
    let X : Polynomial ℕ := Polynomial.X
    let Q := (X + Polynomial.C a) ^ a + (X + Polynomial.C b) ^ b + 2
    obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C c) ^ c)
    refine ⟨C, hC, ?_⟩
    intro p V hl h δ k
    have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
    let q := (p + a) ^ a + (p + b) ^ b + 2
    have ha : 0 ≤ (p + a) ^ a := by positivity
    have hb : 0 ≤ (p + b) ^ b := by positivity
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have haq : (p + a) ^ a ≤ q := by dsimp [q]; linarith only [hb]
    have hbq : (p + b) ^ b ≤ q := by dsimp [q]; linarith only [ha]
    obtain ⟨E⟩ := hprevious V (fun j hj => hl j (List.mem_cons_of_mem i hj)) h δ k.1
    obtain ⟨F⟩ := hright V i (hl i (List.mem_cons_self)) h δ k.2
    obtain ⟨R⟩ := hmul hq (E.mono haq) (F.mono hbq)
    have hcost : (q + c) ^ c ≤ (p + C) ^ C := by
      simpa [q, Q, X, Polynomial.eval₂_pow] using hbound p hp
    exact ⟨R.mono hcost⟩

theorem exists_mixed_remainder_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
      (h δ : ℤ)
      (a : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
        (fun x => translationExpansionRemainder V.eval (mixedTranslationCoordinates s) a
          (mixedTranslationSample s ![h, x (), δ]))) := by
  obtain ⟨C, hC, hrem⟩ := exists_remainder_expansion_of_evaluation_coordinates s (mixedTranslationCoordinates s)
  exact ⟨C, hC, fun V h δ a => hrem V
    (fun i hi => (mem_mixedTranslationCoordinates s i).mp hi) h δ a⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem mixed_translation_reduction_transfer {s : ℕ} {p P : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (E : NativeIntegerVectorEquivalence s P
      (fun k (x : Fin 3 → ℤ) => V.eval k (fun j => correlationInput (x 0) (x 1 + x 2) j.1))
      (fun a x => coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a
        (mixedTranslationSample s x)))
    (h δ : ℤ)
    (R : ∀ a : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length,
      NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) P
        (fun x => translationExpansionRemainder V.eval (mixedTranslationCoordinates s) a
          (mixedTranslationSample s ![h, x (), δ])))
    {Y : Type*} (S : Finset Y) (n : Y → ℤ) (k : Fin V.outputDim) (f : Y → ℂ) (q : ℝ)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star
      (V.eval k (fun j => correlationInput h (n u + δ) j.1))‖) :
    ∃ (a : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length)
      (b : Fin (E.selectedExpansion k a).count) (c : Fin (R a).count),
      Real.exp (-(q + 3 * P)) ≤ ‖𝔼 u ∈ S, f u * star
        (V.eval (firstTranslationCoordinate (mixedTranslationCoordinates s) a)
            (fun j => correlationInput h (n u) j.1) *
          ((E.selectedExpansion k a).test b).eval ![h, n u, δ] *
          ((R a).test c).eval (fun _ => n u))‖ := by
  let sample (u : Y) : Fin 3 → ℤ := ![h, n u, δ]
  have hc : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star
      (V.eval k (fun j => correlationInput (sample u 0) (sample u 1 + sample u 2) j.1))‖ := hcorr
  obtain ⟨j, v, hjv⟩ := E.transfer_sample_correlation S sample k f
    (fun u _ => coordinateTranslationExpansion_unit V.eval V.unit_eval
      (mixedTranslationCoordinates s) (mixedTranslationSample s (sample u))) hc
  let g (u : Y) := f u * star
    (V.eval (firstTranslationCoordinate (mixedTranslationCoordinates s) j)
        (fun z => correlationInput h (n u) z.1) *
      ((E.selectedExpansion k j).test v).eval (sample u))
  have hg : Real.exp (-(q + 2 * P)) ≤ ‖𝔼 u ∈ S, g u * star
      (translationExpansionRemainder V.eval (mixedTranslationCoordinates s) j
        (mixedTranslationSample s ![h, n u, δ]))‖ := by
    simpa only [V.mixedTranslationExpansion_factor, sample, Matrix.cons_val_zero,
      Matrix.cons_val_one, g, star_mul, mul_assoc, mul_left_comm, mul_comm] using hjv
  obtain ⟨w, hw⟩ := (R j).select_sample_correlation S (fun u (_ : Unit) => n u) g hg
  refine ⟨j, v, w, ?_⟩
  rw [show (q + 2 * P) + P = q + 3 * P by ring] at hw
  simpa only [g, sample, star_mul, mul_assoc, mul_left_comm, mul_comm] using hw

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

abbrev MixedExpansionIndex {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p) :=
  BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length

structure NativeMixedReductionData {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (P : ℝ) where
  budget_two : 2 ≤ P
  translation : NativeIntegerVectorEquivalence s P
    (fun k (x : Fin 3 → ℤ) => V.eval k (fun j => correlationInput (x 0) (x 1 + x 2) j.1))
    (fun a x => coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a
      (mixedTranslationSample s x))
  lower : ∀ h δ : ℤ, ∀ a : MixedExpansionIndex V,
    NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) P
      (fun x => translationExpansionRemainder V.eval (mixedTranslationCoordinates s) a
        (mixedTranslationSample s ![h, x (), δ]))
  parallelogram : ∀ k : Fin 4 → Fin V.outputDim,
    NativeIntegerExpansion (fun _ : Fin 4 => 1) s P (mixedParallelogramProduct V k)

namespace NativeMixedReductionData

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

noncomputable def translationTerm (k : Fin V.outputDim) (a : MixedExpansionIndex V)
    (b : Fin (D.translation.selectedExpansion k a).count) (x : Fin 3 → ℤ) : ℂ :=
  ((D.translation.selectedExpansion k a).test b).eval x

noncomputable def lowerTerm (h δ : ℤ) (a : MixedExpansionIndex V)
    (c : Fin (D.lower h δ a).count) (n : ℤ) : ℂ :=
  ((D.lower h δ a).test c).eval (fun _ => n)

noncomputable def correction (h δ : ℤ) (k : Fin V.outputDim) (a : MixedExpansionIndex V)
    (b : Fin (D.translation.selectedExpansion k a).count) (c : Fin (D.lower h δ a).count) (n : ℤ) : ℂ :=
  V.eval (firstTranslationCoordinate (mixedTranslationCoordinates s) a) (fun j => correlationInput h n j.1) *
    D.translationTerm k a b ![h, n, δ] * D.lowerTerm h δ a c n

end NativeMixedReductionData

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

noncomputable def translatedMixedProduct {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (k : Fin 4 → Fin V.outputDim) (h₁ h₂ h₃ h₄ δ n : ℤ) : ℂ :=
  fourPointProduct
    (fun n => V.eval (k 0) (fun j => correlationInput h₁ n j.1))
    (fun n => V.eval (k 1) (fun j => correlationInput h₂ n j.1))
    (fun n => V.eval (k 2) (fun j => correlationInput h₃ n j.1))
    (fun n => V.eval (k 3) (fun j => correlationInput h₄ n j.1)) δ n

namespace NativeMixedReductionData

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

structure TranslationCode (k : Fin 4 → Fin V.outputDim) where
  second : MixedExpansionIndex V
  fourth : MixedExpansionIndex V
  secondTerm : Fin (D.translation.selectedExpansion (k 1) second).count
  fourthTerm : Fin (D.translation.selectedExpansion (k 3) fourth).count

noncomputable def translationCoordinates (k : Fin 4 → Fin V.outputDim) (t : D.TranslationCode k) :
    Fin 4 → Fin V.outputDim :=
  ![k 0, firstTranslationCoordinate (mixedTranslationCoordinates s) t.second,
    k 2, firstTranslationCoordinate (mixedTranslationCoordinates s) t.fourth]

structure LowerCode {k : Fin 4 → Fin V.outputDim} (t : D.TranslationCode k) (h₂ h₄ δ : ℤ) where
  second : Fin (D.lower h₂ δ t.second).count
  fourth : Fin (D.lower h₄ δ t.fourth).count

noncomputable def translationGlobal (k : Fin 4 → Fin V.outputDim) (t : D.TranslationCode k)
    (x : Fin 5 → ℤ) : ℂ :=
  D.translationTerm (k 1) t.second t.secondTerm ![x 1, x 3, x 4] *
    star (D.translationTerm (k 3) t.fourth t.fourthTerm ![x 1 + x 2 - x 0, x 3, x 4])

noncomputable def translationLower {k : Fin 4 → Fin V.outputDim} (t : D.TranslationCode k)
    (h₂ h₄ δ : ℤ) (c : D.LowerCode t h₂ h₄ δ) (n : ℤ) : ℂ :=
  D.lowerTerm h₂ δ t.second c.second n * star (D.lowerTerm h₄ δ t.fourth c.fourth n)

theorem translationGlobal_sample (k : Fin 4 → Fin V.outputDim) (t : D.TranslationCode k)
    (h₁ h₂ h₃ h₄ n δ : ℤ) (hrel : -h₁ + h₂ + h₃ - h₄ = 0) :
    D.translationGlobal k t ![h₁, h₂, h₃, n, δ] =
      D.translationTerm (k 1) t.second t.secondTerm ![h₂, n, δ] *
        star (D.translationTerm (k 3) t.fourth t.fourthTerm ![h₄, n, δ]) := by
  have hh₄ : h₄ = h₂ + h₃ - h₁ := by omega
  subst h₄
  rfl

structure ReductionCode (k : Fin 4 → Fin V.outputDim) where
  translations : D.TranslationCode k
  term : Fin (D.parallelogram (D.translationCoordinates k translations)).count

noncomputable def globalError (k : Fin 4 → Fin V.outputDim) (a : D.ReductionCode k)
    (x : Fin 5 → ℤ) : ℂ :=
  D.translationGlobal k a.translations x *
    ((D.parallelogram (D.translationCoordinates k a.translations)).test a.term).eval
      ![x 0, x 1, x 2, x 3]

end NativeMixedReductionData

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem star_finite_expect {X : Type*} (S : Finset X) (f : X → ℂ) :
    star (𝔼 u ∈ S, f u) = 𝔼 u ∈ S, star (f u) := by
  simp [Finset.expect]

namespace NativeMixedReductionData

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem translation_negative (h δ : ℤ) {X : Type*} (S : Finset X) (n : X → ℤ)
    (k : Fin V.outputDim) (f : X → ℂ) (q : ℝ)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star
      (V.eval k (fun j => correlationInput h (n u + δ) j.1))‖) :
    ∃ (a : MixedExpansionIndex V) (b : Fin (D.translation.selectedExpansion k a).count)
      (c : Fin (D.lower h δ a).count), Real.exp (-(q + 3 * P)) ≤
        ‖𝔼 u ∈ S, f u * star (D.correction h δ k a b c (n u))‖ :=
  V.mixed_translation_reduction_transfer D.translation h δ (D.lower h δ) S n k f q hcorr

theorem translation_positive (h δ : ℤ) {X : Type*} (S : Finset X) (n : X → ℤ)
    (k : Fin V.outputDim) (f : X → ℂ) (q : ℝ)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u *
      V.eval k (fun j => correlationInput h (n u + δ) j.1)‖) :
    ∃ (a : MixedExpansionIndex V) (b : Fin (D.translation.selectedExpansion k a).count)
      (c : Fin (D.lower h δ a).count), Real.exp (-(q + 3 * P)) ≤
        ‖𝔼 u ∈ S, f u * D.correction h δ k a b c (n u)‖ := by
  have hc : Real.exp (-q) ≤ ‖𝔼 u ∈ S, star (f u) * star
      (V.eval k (fun j => correlationInput h (n u + δ) j.1))‖ := by
    simpa only [← star_mul, ← star_finite_expect, norm_star, mul_comm] using hcorr
  obtain ⟨a, b, c, habc⟩ := D.translation_negative h δ S n k (fun u => star (f u)) q hc
  exact ⟨a, b, c, by simpa only [← star_mul, ← star_finite_expect, norm_star, mul_comm] using habc⟩

end NativeMixedReductionData

end Erdos3

end

section

namespace Erdos3.NativeMixedReductionData

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem correction_factorization (k : Fin 4 → Fin V.outputDim) (t : D.TranslationCode k)
    (h₁ h₂ h₃ h₄ δ n : ℤ) (c : D.LowerCode t h₂ h₄ δ) (z : ℂ)
    (hrel : -h₁ + h₂ + h₃ - h₄ = 0) :
    z * star (V.eval (k 0) (fun j => correlationInput h₁ n j.1)) *
        V.eval (k 2) (fun j => correlationInput h₃ n j.1) *
        star (D.correction h₄ δ (k 3) t.fourth t.fourthTerm c.fourth n) *
        D.correction h₂ δ (k 1) t.second t.secondTerm c.second n =
      z * D.translationGlobal k t ![h₁, h₂, h₃, n, δ] *
        D.translationLower t h₂ h₄ δ c n *
        untranslatedMixedProduct V (D.translationCoordinates k t) h₁ h₂ h₃ h₄ n := by
  rw [D.translationGlobal_sample k t h₁ h₂ h₃ h₄ n δ hrel]
  have hzero : D.translationCoordinates k t 0 = k 0 := rfl
  have hone : D.translationCoordinates k t 1 =
      firstTranslationCoordinate (mixedTranslationCoordinates s) t.second := rfl
  have htwo : D.translationCoordinates k t 2 = k 2 := rfl
  have hthree : D.translationCoordinates k t 3 =
      firstTranslationCoordinate (mixedTranslationCoordinates s) t.fourth := rfl
  simp only [correction, translationLower, untranslatedMixedProduct,
    hzero, hone, htwo, hthree, star_mul]
  ring

end Erdos3.NativeMixedReductionData

end

section

namespace Erdos3.NativeMixedReductionData

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

noncomputable def translationTermExpansion (k : Fin V.outputDim) (a : MixedExpansionIndex V)
    (b : Fin (D.translation.selectedExpansion k a).count) :
    NativeIntegerExpansion (fun _ : Fin 3 => 1) s P (D.translationTerm k a b) :=
  NativeIntegerExpansion.ofTest ((D.translation.selectedExpansion k a).test b)
    ((D.translation.selectedExpansion k a).complexity b) (fun _ => rfl)

def secondInput (i : Fin 3) : ((Fin 5 → ℤ) →+ ℤ) where
  toFun x := (![x 1, x 3, x 4] : Fin 3 → ℤ) i
  map_zero' := by fin_cases i <;> rfl
  map_add' x y := by fin_cases i <;> rfl

def fourthInput (i : Fin 3) : ((Fin 5 → ℤ) →+ ℤ) where
  toFun x := (![x 1 + x 2 - x 0, x 3, x 4] : Fin 3 → ℤ) i
  map_zero' := by fin_cases i <;> rfl
  map_add' x y := by
    fin_cases i
    · change (x 1 + y 1) + (x 2 + y 2) - (x 0 + y 0) =
        (x 1 + x 2 - x 0) + (y 1 + y 2 - y 0)
      ring
    · rfl
    · rfl

def parallelogramInput (i : Fin 4) : ((Fin 5 → ℤ) →+ ℤ) where
  toFun x := (![x 0, x 1, x 2, x 3] : Fin 4 → ℤ) i
  map_zero' := by fin_cases i <;> rfl
  map_add' x y := by fin_cases i <;> rfl

noncomputable def translationGlobalExpansion (k : Fin 4 → Fin V.outputDim)
    (t : D.TranslationCode k) :
    NativeIntegerExpansion (fun _ : Fin 5 => 1) s (productNiltestBudget P + 2 * P)
      (D.translationGlobal k t) :=
  ((D.translationTermExpansion (k 1) t.second t.secondTerm).linearPullbackHom secondInput).mul
    (((D.translationTermExpansion (k 3) t.fourth t.fourthTerm).linearPullbackHom fourthInput).conjugate)
    D.budget_two

noncomputable def lowerTermExpansion (h δ : ℤ) (a : MixedExpansionIndex V)
    (c : Fin (D.lower h δ a).count) :
    NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) P
      (fun x => D.lowerTerm h δ a c (x ())) :=
  NativeIntegerExpansion.ofTest ((D.lower h δ a).test c) ((D.lower h δ a).complexity c)
    (fun _ => rfl)

noncomputable def translationLowerExpansion {k : Fin 4 → Fin V.outputDim}
    (t : D.TranslationCode k) (h₂ h₄ δ : ℤ) (c : D.LowerCode t h₂ h₄ δ) :
    NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) (productNiltestBudget P + 2 * P)
      (fun x => D.translationLower t h₂ h₄ δ c (x ())) :=
  (D.lowerTermExpansion h₂ δ t.second c.second).mul
    (D.lowerTermExpansion h₄ δ t.fourth c.fourth).conjugate D.budget_two

noncomputable def parallelogramTermExpansion (k : Fin 4 → Fin V.outputDim)
    (a : D.ReductionCode k) :
    NativeIntegerExpansion (fun _ : Fin 5 => 1) s P
      (fun x => ((D.parallelogram (D.translationCoordinates k a.translations)).test a.term).eval
        ![x 0, x 1, x 2, x 3]) :=
  (NativeIntegerExpansion.ofTest
    ((D.parallelogram (D.translationCoordinates k a.translations)).test a.term)
    ((D.parallelogram (D.translationCoordinates k a.translations)).complexity a.term)
    (fun _ => rfl)).linearPullbackHom parallelogramInput

end Erdos3.NativeMixedReductionData

end

section

namespace Erdos3

def mixedErrorPairBudget (p : ℝ) : ℝ := productNiltestBudget p + 2 * p

def mixedErrorBudget (p : ℝ) : ℝ :=
  productNiltestBudget (mixedErrorPairBudget p) + 2 * mixedErrorPairBudget p

theorem le_mixedErrorPairBudget {p : ℝ} (hp : 0 ≤ p) : p ≤ mixedErrorPairBudget p := by
  have h := productNiltestBudget_geometry hp
  unfold mixedErrorPairBudget
  nlinarith only [hp, h, sq_nonneg (p + 2)]

namespace NativeMixedReductionData

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

noncomputable def globalErrorExpansion (k : Fin 4 → Fin V.outputDim)
    (a : D.ReductionCode k) :
    NativeIntegerExpansion (fun _ : Fin 5 => 1) s (mixedErrorBudget P) (D.globalError k a) := by
  have hp : 0 ≤ P := le_trans (by norm_num) D.budget_two
  have hP : P ≤ mixedErrorPairBudget P := le_mixedErrorPairBudget hp
  exact (D.translationGlobalExpansion k a.translations).mul
    ((D.parallelogramTermExpansion k a).mono hP) (D.budget_two.trans hP)

end NativeMixedReductionData

theorem exists_mixed_error_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      mixedErrorPairBudget p ≤ (p + C) ^ C ∧ mixedErrorBudget p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4 + 2 * X
  let T := (R + 2) ^ 2 + R + (R + (R ^ 2 + R + 3) ^ 2) + R ^ 2 + 4 + 2 * R
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + T)
  refine ⟨C, hC, fun p hp => ?_⟩
  have hpair : 0 ≤ mixedErrorPairBudget p := hp.trans (le_mixedErrorPairBudget hp)
  have hglobal : 0 ≤ mixedErrorBudget p := by
    change 0 ≤ mixedErrorPairBudget (mixedErrorPairBudget p)
    exact hpair.trans (le_mixedErrorPairBudget hpair)
  have hb : mixedErrorPairBudget p + mixedErrorBudget p ≤ (p + C) ^ C := by
    simpa [X, R, T, mixedErrorPairBudget, mixedErrorBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget p hp
  constructor <;> linarith only [hpair, hglobal, hb]

end Erdos3

end

section

namespace Erdos3.NativeIntegerExpansion

noncomputable def translate {s : ℕ} {p : ℝ} {f : ℤ → ℂ}
    (E : NativeIntegerExpansion (fun _ : Unit => 1) s p (fun x => f (x ()))) (δ : ℤ) :
    NativeIntegerExpansion (fun _ : Unit => 1) s p (fun x => f (x () + δ)) := by
  simpa [integerAffineMap, add_comm] using E.affinePullback (fun (_ : Unit) (_ : Unit) => (1 : ℤ)) (fun _ => δ)

noncomputable def fourPoint {s : ℕ} {p : ℝ} (f : Fin 4 → ℤ → ℂ)
    (E : ∀ i, NativeIntegerExpansion (fun _ : Unit => 1) s p (fun x => f i (x ())))
    (hp : 2 ≤ p) (δ : ℤ) :
    NativeIntegerExpansion (fun _ : Unit => 1) s (mixedErrorBudget p)
      (fun x => fourPointProduct (f 0) (f 1) (f 2) (f 3) δ (x ())) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hpair : 2 ≤ mixedErrorPairBudget p := hp.trans (le_mixedErrorPairBudget hp0)
  let E₁₂ := (E 0).conjugate.mul ((E 1).translate δ) hp
  let E₃₄ := (E 2).mul ((E 3).translate δ).conjugate hp
  simpa only [mixedErrorBudget, mixedErrorPairBudget, fourPointProduct, mul_assoc] using E₁₂.mul E₃₄ hpair

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3

open scoped BigOperators

theorem native_weight_pair_removal {I : Type} [Fintype I] [Nonempty I]
    {d : ℕ} {p : ℝ} (hp : 2 ≤ p) (A : Finset ℤ) (hA : A.Nonempty)
    (S : I → Finset ℤ) (hSA : ∀ i, S i ⊆ A)
    (weight : ℤ → ℂ) (a v : I → ℤ → ℂ)
    (E : ∀ i, NativeIntegerExpansion (fun _ : Unit => 1) d p (fun x => v i (x ())))
    (hw : ∀ x ∈ A, ‖weight x‖ ≤ 1) (ha : ∀ i x, x ∈ S i → ‖a i x‖ ≤ 1)
    (hsize : ∀ i, Real.exp (-p) ≤ (S i).card / (A.card : ℝ))
    (hcorr : ∀ i, Real.exp (-p) ≤ ‖𝔼 x ∈ S i, weight x * (a i x * v i x)‖) :
    ∃ P : Finset (I × I), P.Nonempty ∧
      Real.exp (-(8 * p + 1)) * (Fintype.card I : ℝ) ^ 2 ≤ (P.card : ℝ) ∧
      ∀ t ∈ P, (S t.1 ∩ S t.2).Nonempty ∧
        Real.exp (-(8 * p + 1)) ≤ (S t.1 ∩ S t.2).card / (A.card : ℝ) ∧
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) d (mixedErrorPairBudget p)
          (fun x => v t.1 (x ()) * star (v t.2 (x ())))) ∧
        Real.exp (-(8 * p + 1)) ≤ ‖𝔼 x ∈ S t.1 ∩ S t.2,
          (a t.1 x * star (a t.2 x)) * (v t.1 x * star (v t.2 x))‖ := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  let u (i : I) (x : ℤ) := (Real.exp (-(2 * p)) : ℂ) * (a i x * v i x)
  have hu (i : I) (x : ℤ) (hx : x ∈ S i) : ‖u i x‖ ≤ 1 := by
    apply exp_scaled_norm_le_one
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (ha i x hx) ((E i).norm_eval_le (fun _ => x))
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have huc (i : I) : Real.exp (-(3 * p)) ≤ ‖𝔼 x ∈ S i, weight x * u i x‖ := by
    have heq : (𝔼 x ∈ S i, weight x * u i x) =
        (Real.exp (-(2 * p)) : ℂ) * (𝔼 x ∈ S i, weight x * (a i x * v i x)) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      dsimp only [u]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ = Real.exp (-(2 * p)) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcorr i) (Real.exp_nonneg _)
  obtain ⟨P, hP, hPsize, hpair⟩ := exists_supported_correlation_pairs A hA S hSA
    weight u (Real.exp_pos (-p)) (Real.exp_pos (-(3 * p))) hw hu hsize huc
  have hthreshold : Real.exp (-(8 * p + 1)) ≤ (Real.exp (-p) * Real.exp (-(3 * p))) ^ 2 / 2 := by
    have heq : (Real.exp (-p) * Real.exp (-(3 * p))) ^ 2 = Real.exp (-(8 * p)) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [heq]
    simpa only [show -(8 * p + 1) = -(8 * p) - 1 by ring] using exp_sub_one_le_half_exp (-(8 * p))
  refine ⟨P, hP, (mul_le_mul_of_nonneg_right hthreshold (sq_nonneg _)).trans hPsize, ?_⟩
  intro t ht
  obtain ⟨hJ, hcor, hvol⟩ := hpair t ht
  refine ⟨hJ, hthreshold.trans hvol, ⟨(E t.1).mul (E t.2).conjugate hp⟩, ?_⟩
  have hcoef : (Real.exp (-(4 * p)) : ℂ) =
      (Real.exp (-(2 * p)) : ℂ) * (Real.exp (-(2 * p)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring_nf
  have hmean : (𝔼 x ∈ S t.1 ∩ S t.2, u t.1 x * star (u t.2 x)) =
      𝔼 x ∈ S t.1 ∩ S t.2, ((Real.exp (-(4 * p)) : ℂ) * (a t.1 x * star (a t.2 x))) *
        (v t.1 x * star (v t.2 x)) := by
    apply Finset.expect_congr rfl
    intro x _
    simp only [u, star_mul, Complex.star_def, Complex.conj_ofReal, hcoef]
    ring
  have hc := hthreshold.trans hcor
  rw [hmean] at hc
  exact finite_remove_normalization (S t.1 ∩ S t.2)
    (fun x => a t.1 x * star (a t.2 x)) (fun x => v t.1 x * star (v t.2 x))
    (by linarith : 0 ≤ 4 * p) hc

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateErrorReduction
namespace OAI

section

namespace Erdos3

theorem exists_coordinate_reduction_budget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + a) ^ a ≤ (p + C) ^ C ∧
      ((p + a) ^ a + b) ^ b ≤ (p + C) ^ C ∧
      3 * p + (p + a) ^ a + 1 ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (3 * X + Y + (Y + Polynomial.C b) ^ b + 2)
  refine ⟨C, hC, fun p hp => ?_⟩
  have hY : 0 ≤ (p + a) ^ a := by positivity
  have hZ : 0 ≤ ((p + a) ^ a + b) ^ b := by positivity
  have hb : 3 * p + (p + a) ^ a + ((p + a) ^ a + b) ^ b + 2 ≤ (p + C) ^ C := by
    simpa [X, Y, Polynomial.eval₂_pow] using hbudget p hp
  constructor
  · linarith only [hp, hY, hZ, hb]
  constructor <;> linarith only [hp, hY, hZ, hb]

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

def CoordinateErrorReductionStatement (σ : Type) [Fintype σ] [DecidableEq σ] (s C : ℕ) : Prop :=
  ∀ (i : σ) {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} {D : RationalFilteredNilmanifold L s d} {p : ℝ}
    (T : D.Niltest (fun _ : σ => 1)), 2 ≤ p → T.ComplexityLE p →
    ∀ {G X : Type} (H : Finset G), H.Nonempty →
    ∀ (S : G → Finset X) (b : G → σ → ℤ) (n : G → X → ℤ) (f : G → X → ℂ),
    (∀ h ∈ H, (S h).Nonempty) → (∀ h ∈ H, ∀ x ∈ S h, ‖f h x‖ ≤ Real.exp p) →
    (∀ h ∈ H, Real.exp (-p) ≤
      ‖𝔼 x ∈ S h, f h x * T.eval (Function.update (b h) i (n h x))‖) →
    ∃ (weight : ℤ → ℂ) (Q : Finset G), (∀ z, ‖weight z‖ ≤ 1) ∧ Q ⊆ H ∧ Q.Nonempty ∧
      Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (Q.card : ℝ) ∧
      ∀ h ∈ Q, ∃ v : ℤ → ℂ,
        (∀ z, ‖v z‖ ≤ 1) ∧
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => v (x ()))) ∧
        Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 x ∈ S h, f h x * weight (n h x) * v (n h x)‖

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCoordinateSplit.lie NativeCoordinateSplit.algebra NativeCoordinateSplit.topology NativeCoordinateSplit.topologicalAdd NativeCoordinateSplit.continuousSMul NativeCoordinateSplit.hausdorff

theorem exists_coordinate_error_reduction (σ : Type) [Fintype σ] [DecidableEq σ] [Nonempty σ]
    (s : ℕ) : ∃ C : ℕ, 2 ≤ C ∧ CoordinateErrorReductionStatement σ s C := by
  obtain ⟨a, _, hsplit⟩ := exists_coordinate_niltest_splitting σ s 2
  obtain ⟨b, _, hfreeze⟩ := NativeCoordinateSplit.exists_second_expansion_budget σ s
  obtain ⟨C, hC, hbudget⟩ := exists_coordinate_reduction_budget a b
  refine ⟨C, hC, ?_⟩
  intro i L _ _ _ _ _ _ d D p T hp hT G X H hH S z n f hS hf hcorr
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  let U := T.conjugate.expNormalize p
  let epsilon := Real.exp (-(3 * p + 1))
  have hscale : 1 / epsilon ≤ Real.exp ((p + 2) ^ 2) := by
    dsimp [epsilon]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith only [hp0, sq_nonneg p]
  obtain ⟨R⟩ := hsplit i U (T.conjugate.expNormalize_complexity hT)
    (T.conjugate.expNormalize_norm hT) epsilon (Real.exp_pos _) hscale
  let sample (h : G) (x : X) := Function.update (z h) i (n h x)
  let f₀ (h : G) (x : X) := (Real.exp (-p) : ℂ) * f h x
  have hf₀ : ∀ h ∈ H, ∀ x ∈ S h, ‖f₀ h x‖ ≤ 1 :=
    fun h hh x hx => exp_scaled_norm_le_one (hf h hh x hx)
  have hc₀ : ∀ h ∈ H, Real.exp (-(3 * p)) ≤
      ‖𝔼 x ∈ S h, f₀ h x * star (U.eval (sample h x))‖ := by
    intro h hh
    have hc := finite_double_normalization (S h) (f h) (fun x => T.eval (sample h x)) p (hcorr h hh)
    simpa only [f₀, U, RationalFilteredNilmanifold.Niltest.expNormalize_eval,
      RationalFilteredNilmanifold.Niltest.eval_conjugate, star_mul,
      Complex.star_def, Complex.conj_ofReal, Complex.conj_conj, mul_assoc, mul_left_comm, mul_comm] using hc
  have hepsilon : epsilon ≤ Real.exp (-(3 * p)) / 2 := by
    simpa only [epsilon, show -(3 * p + 1) = -(3 * p) - 1 by ring] using
      exp_sub_one_le_half_exp (-(3 * p))
  obtain ⟨j, Q, hQH, hQ, hsize, hterm⟩ := R.exists_fixed_correlating_term
    H hH S hS sample f₀ (Real.exp_pos _) hepsilon hf₀ hc₀
  let weight (x : ℤ) := star (R.firstFactor j x)
  have hweight (x : ℤ) : ‖weight x‖ ≤ 1 := by
    simpa only [weight, norm_star] using R.firstFactor_norm j x
  have hfirst (h : G) (x : X) : (R.test false j).eval (sample h x) = R.firstFactor j (n h x) := by
    simpa only [sample, Function.update_self] using R.first_eval_firstFactor j (sample h x)
  have hsmall : Real.exp (-(3 * p + (p + a) ^ a + 1)) ≤
      Real.exp (-(3 * p)) / (2 * Real.exp ((p + a) ^ a)) := by
    calc
      _ = Real.exp (-(3 * p + (p + a) ^ a) - 1) := by congr 1; ring
      _ ≤ Real.exp (-(3 * p + (p + a) ^ a)) / 2 := exp_sub_one_le_half_exp _
      _ = _ := by
        rw [show -(3 * p + (p + a) ^ a) = -(3 * p) - (p + a) ^ a by ring, Real.exp_sub]
        ring
  refine ⟨weight, Q, hweight, hQH, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp0).1)) (Nat.cast_nonneg H.card)).trans hsize
  · intro h hh
    let v (x : ℤ) := star ((R.test true j).eval (Function.update (z h) i x))
    obtain ⟨E, _⟩ := hfreeze R j (z h)
    refine ⟨v, ?_, ⟨E.conjugate.mono (hbudget p hp0).2.1⟩, ?_⟩
    · intro x
      simpa only [v, norm_star] using ((R.test true j).norm_eval_le (Function.update (z h) i x)).trans
        (show ((R.test true j).normBound : ℝ) ≤ 1 from R.test_norm true j)
    · have hc : Real.exp (-(3 * p)) / (2 * Real.exp ((p + a) ^ a)) ≤
          ‖𝔼 x ∈ S h, ((Real.exp (-p) : ℂ) * f h x) * (weight (n h x) * v (n h x))‖ := by
        simpa only [f₀, hfirst, weight, v, sample, star_mul,
          mul_assoc, mul_left_comm, mul_comm] using hterm h hh
      have hout := finite_remove_normalization (S h) (f h)
        (fun x => weight (n h x) * v (n h x)) hp0 hc
      have hthreshold := (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp0).2.2)).trans
        (hsmall.trans hout)
      simpa only [mul_assoc] using hthreshold

end Erdos3

end

end OAI

end


