-- Prove2me | Definitions.Def_OAIErdos3B111
-- name    : OAIErdos3B111
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T02:27:37.625205+00:00
-- url     : https://prove2.me/theorems/6522c6aa-503c-4f6f-bedd-41ccd47ac057
-- title:
--   OpenAI Erdős-3 split, definitions bundle 112 of 132
-- statement:
--   Definitions bundle 112 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B110`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 112 available.
--
--   Modules: `OAI.Erdos3.FiniteProbabilityWeights.finiteScore`, `OAI.Erdos3.FiniteProbabilityWeights.finiteScore_abs_le`, `OAI.Erdos3.FiniteProbabilityWeights.finiteScore_integrable`, `OAI.Erdos3.FiniteProbabilityWeights.finiteScore_le`, `OAI.Erdos3.FiniteProbabilityWeights.finiteScore_measurable`, `OAI.Erdos3.FiniteProbabilityWeights.integral_finiteScore`, `OAI.Erdos3.FiniteProbabilityWeights.sampledComplexTest`, `OAI.Erdos3.NativeNormalizedSquareSpec`, `OAI.Erdos3.NativeSampleModel.weaken`, `OAI.Erdos3.NilpotentLieFiltration.CoefficientCorrectionSpec`, `OAI.Erdos3.NilpotentLieFiltration.NormalizedCommonFamilySpec`, `OAI.Erdos3.NilpotentLieFiltration.PolynomialShiftAlgebra`, `OAI.Erdos3.NilpotentLieFiltration.SynchronizedSquareBoundSpec`, `OAI.Erdos3.NilpotentLieFiltration.adaptedReducedRealSymbolHom_square_diagonal`, `OAI.Erdos3.NilpotentLieFiltration.adaptedReducedRealSymbolHom_square_projection`, `OAI.Erdos3.NilpotentLieFiltration.adaptedReducedRealSymbolHom_square_relative`, `OAI.Erdos3.NilpotentLieFiltration.adaptedShiftAction`, `OAI.Erdos3.NilpotentLieFiltration.adaptedShiftAction_coe`, `OAI.Erdos3.NilpotentLieFiltration.adaptedShiftDerivation`, `OAI.Erdos3.NilpotentLieFiltration.adaptedShiftDerivationLinear`, `OAI.Erdos3.NilpotentLieFiltration.adaptedShiftDerivation_coe`, `OAI.Erdos3.NilpotentLieFiltration.adaptedShiftDerivation_commute`, `OAI.Erdos3.NilpotentLieFiltration.exists_coefficient_correction_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_normalized_common_family`, `OAI.Erdos3.NilpotentLieFiltration.exists_synchronizedSquare_bound`, `OAI.Erdos3.NilpotentLieFiltration.map_log_constantGroupOrbit_mul_of_realificationMap_eq_one`, `OAI.Erdos3.NilpotentLieFiltration.normalized_real_square_derivative_identity`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitRealEval_constantGroupOrbit`, `OAI.Erdos3.NilpotentLieFiltration.polynomialShiftBasis`, `OAI.Erdos3.NilpotentLieFiltration.polynomialShiftBasis_inl`, `OAI.Erdos3.NilpotentLieFiltration.polynomialShiftBasis_inl_left`, `OAI.Erdos3.NilpotentLieFiltration.polynomialShiftBasis_inl_right`, `OAI.Erdos3.NilpotentLieFiltration.polynomialShiftBasis_inr`, `OAI.Erdos3.NilpotentLieFiltration.polynomialShiftBasis_inr_left`, `OAI.Erdos3.NilpotentLieFiltration.polynomialShiftBasis_inr_right`, `OAI.Erdos3.NilpotentLieFiltration.polynomialShiftBasis_mixed_height`, `OAI.Erdos3.NilpotentLieFiltration.polynomialShiftBasis_repr_inl`, `OAI.Erdos3.NilpotentLieFiltration.polynomialShiftBasis_repr_inr`, `OAI.Erdos3.NilpotentLieFiltration.polynomialShiftBasis_structure_height`, `OAI.Erdos3.NilpotentLieFiltration.polynomialShift_bracket`, `OAI.Erdos3.NilpotentLieFiltration.polynomialShift_direction_bracket`, `OAI.Erdos3.NilpotentLieFiltration.polynomialShift_finiteDimensional`, `OAI.Erdos3.NilpotentLieFiltration.polynomialShift_finrank_le`, `OAI.Erdos3.NilpotentLieFiltration.realReducedRelativeSquareSymbolMap_of_square_factorization`, `OAI.Erdos3.NilpotentLieFiltration.synchronized_normalized_coefficient_common_derivative`, `OAI.Erdos3.OrdinaryPolynomialPhase.canonicalContinuousSMul`, `OAI.Erdos3.OrdinaryPolynomialPhase.canonicalT2Space`, `OAI.Erdos3.OrdinaryPolynomialPhase.canonicalTopologicalAddGroup`, `OAI.Erdos3.OrdinaryPolynomialPhase.canonicalTopology`, `OAI.Erdos3.OrdinaryPolynomialPhase.withCanonicalTopology`, `OAI.Erdos3.PolynomialPatch.fullSliceLaw_shearObservable_score`, `OAI.Erdos3.PolynomialPatch.shearNiltest`, `OAI.Erdos3.PolynomialPatch.shearNiltest_complexity`, `OAI.Erdos3.PolynomialPatch.shearNiltest_unitInterval`, `OAI.Erdos3.PolynomialPatch.shearObservable_local_integerEval`, `OAI.Erdos3.PolynomialPatch.shearObservable_local_realEval`, `OAI.Erdos3.PolynomialSlots.coordinateFiberForm`, `OAI.Erdos3.PolynomialSlots.shearObservable_eval_lift`, `OAI.Erdos3.PolynomialSlots.shearObservable_eval_orbit`, `OAI.Erdos3.PolynomialTranslationLie.exists_associatedGraded_controlled_potential`, `OAI.Erdos3.PolynomialTranslationLie.exists_controlled_projected_potential`, `OAI.Erdos3.PolynomialTranslationLie.exists_controlled_projected_potential_bounds`, `OAI.Erdos3.PolynomialTranslationLie.exists_controlled_projected_potential_lifts`, `OAI.Erdos3.PolynomialTranslationLie.exists_intrinsic_controlled_projected_potential_bounds`, `OAI.Erdos3.PolynomialTranslationLie.exists_majorTranslation_buffered_niltest`, `OAI.Erdos3.PolynomialTranslationLie.exists_majorTranslation_degree_reduced_niltest`, `OAI.Erdos3.PolynomialTranslationLie.explicit_projected_weighted_potential`, `OAI.Erdos3.PolynomialTranslationLie.fractionalMajorPolynomial_mass`, `OAI.Erdos3.PolynomialTranslationLie.fractionalMajorPolynomial_support`, `OAI.Erdos3.PolynomialTranslationLie.majorZeroParameterSlice_degree`, `OAI.Erdos3.PolynomialTranslationLie.majorZeroParameterSlice_eq`, `OAI.Erdos3.PolynomialTranslationLie.majorZeroParameterSlice_mass`, `OAI.Erdos3.PolynomialTranslationLie.reducedMajorTranslationTwistedNiltest`, `OAI.Erdos3.PolynomialTranslationLie.reducedMajorTranslationTwistedNiltest_lipBound`, `OAI.Erdos3.PolynomialTranslationLie.reducedMajorTranslationTwistedNiltest_normBound`, `OAI.Erdos3.PolynomialTranslationLie.reducedMajorTranslationTwistedNiltest_observable`, `OAI.Erdos3.PolynomialTranslationLie.reducedMajorTranslationTwistedNiltest_orbit`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_polynomial_height_of_coordinates`, `OAI.Erdos3.PolynomialTranslationLie.weightedBasis_projection_polynomial_height`, `OAI.Erdos3.PrecenterForecastNativeAtomLabel`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.exists_external_kernelProjection_common_translation`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.exists_external_kernelProjection_prescribed_marked_orbit`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.exists_external_kernelProjection_restored_orbit`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_stepOne_graded_niltest_splitting`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_stepOne_niltest_splitting`, `OAI.Erdos3.RationalFilteredNilmanifold.stepOne_niltest_eval_affine`, `OAI.Erdos3.RationalFilteredNilmanifold.stepOne_niltest_linear_phase_bias`, `OAI.Erdos3.VectorPolynomial.AllocatedActualCoefficientIndex`, `OAI.Erdos3.VectorPolynomial.AllocatedCongruenceCoefficientIndex`, `OAI.Erdos3.VectorPolynomial.AllocatedCongruenceScalarIndex`, `OAI.Erdos3.VectorPolynomial.AllocatedDeckRankCoefficientIndex`, `OAI.Erdos3.VectorPolynomial.AllocatedProjectionCoefficientIndex`, `OAI.Erdos3.VectorPolynomial.AllocatedRankComponentCoefficient`, `OAI.Erdos3.VectorPolynomial.AllocatedRankComponentCoefficientIndex`, `OAI.Erdos3.VectorPolynomial.AllocatedSelectedCoefficientIndex`, `OAI.Erdos3.VectorPolynomial.AllocatedSmoothRankCoefficientIndex`, `OAI.Erdos3.VectorPolynomial.CoefficientDeckScalarIndex`, `OAI.Erdos3.VectorPolynomial.allocatedActualCoefficientEmbedding`, `OAI.Erdos3.VectorPolynomial.allocatedActualCoefficientSlot`, `OAI.Erdos3.VectorPolynomial.allocatedActualCoefficientSlot_injective`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceActualCoefficientEmbedding`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceCoefficientEmbedding`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceCoefficientReindex`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceCoefficientSplit`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceModulusBad`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceRankBad`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceRankBlockFamily`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceRankFailureProbability`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceRankIntegerResidualFamily`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceRankPolynomial`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceRankPolynomial_original`, `OAI.Erdos3.VectorPolynomial.allocatedDegreeRankPolynomial`, `OAI.Erdos3.VectorPolynomial.allocatedDegreeRankPolynomial_eq_designated`, `OAI.Erdos3.VectorPolynomial.allocatedDegreeRankResidual`, `OAI.Erdos3.VectorPolynomial.allocatedMixedCoefficientEquiv`, `OAI.Erdos3.VectorPolynomial.allocatedMixedSelectedValues`, `OAI.Erdos3.VectorPolynomial.allocatedNaturalFullSiteRatio`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalTaggedTop`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalTaggedTop_eq_designated`, `OAI.Erdos3.VectorPolynomial.allocatedPrincipalChartRatio`, `OAI.Erdos3.VectorPolynomial.allocatedRankComponentCoefficientEmbedding`, `OAI.Erdos3.VectorPolynomial.allocatedRankComponentCoefficientSlot`, `OAI.Erdos3.VectorPolynomial.allocatedRankComponentCoefficientSlot_injective`, `OAI.Erdos3.VectorPolynomial.allocatedRankComponentSelectedEmbedding`, `OAI.Erdos3.VectorPolynomial.allocatedRankComponentSelectedSlot`, `OAI.Erdos3.VectorPolynomial.allocatedRankComponentSelectedSlot_injective`, `OAI.Erdos3.VectorPolynomial.allocatedReadDeck`, `OAI.Erdos3.VectorPolynomial.allocatedReadNoise`, `OAI.Erdos3.VectorPolynomial.allocatedReadProjection`, `OAI.Erdos3.VectorPolynomial.allocatedSelectedRankCoefficients`, `OAI.Erdos3.VectorPolynomial.allocatedSlicedGridResourceLog`, `OAI.Erdos3.VectorPolynomial.allocatedSlicedGridResourceLog_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedTaggedRankIntegerResidual`, `OAI.Erdos3.VectorPolynomial.allocatedTaggedRankPolynomial`, `OAI.Erdos3.VectorPolynomial.allocatedTaggedRankPolynomial_eq_designated`, `OAI.Erdos3.VectorPolynomial.allocatedTaggedRankPolynomial_original`, `OAI.Erdos3.VectorPolynomial.allocatedTaggedRankResidual`, `OAI.Erdos3.VectorPolynomial.coefficientDeckScalarEquiv`, `OAI.Erdos3.VectorPolynomial.coefficients_torusDerivative`, `OAI.Erdos3.VectorPolynomial.congruenceIndexDecidableEq`, `OAI.Erdos3.VectorPolynomial.congruenceIndexFintype`, `OAI.Erdos3.VectorPolynomial.directionalDerivationLinear`, `OAI.Erdos3.VectorPolynomial.directionalDerivationLinear_apply`, `OAI.Erdos3.VectorPolynomial.directionalDerivative_commute`, `OAI.Erdos3.VectorPolynomial.directionalLieDerivation`, `OAI.Erdos3.VectorPolynomial.directionalLieDerivation_apply`, `OAI.Erdos3.VectorPolynomial.exists_affine_coefficient_amplitude_density_test`, `OAI.Erdos3.VectorPolynomial.exists_allocatedAffineAnalytic_budget`, `OAI.Erdos3.VectorPolynomial.exists_allocatedAffineModelMass_budget`, `OAI.Erdos3.VectorPolynomial.exists_allocatedSlicedGridResource_budget`, `OAI.Erdos3.VectorPolynomial.exists_normalizedNative_uniform_budget`, `OAI.Erdos3.VectorPolynomial.modularDeckPolynomial`, `OAI.Erdos3.VectorPolynomial.modularDeckPolynomial_degree`, `OAI.Erdos3.VectorPolynomial.modularDeckPolynomial_kernel_resample_long_top`, `OAI.Erdos3.VectorPolynomial.modularDeckPolynomial_resample_top`, `OAI.Erdos3.VectorPolynomial.pderiv_commute`, `OAI.Erdos3.VectorPolynomial.resampleCoefficientDeckCoordinate`, `OAI.Erdos3.VectorPolynomial.resampleCoefficientDeckCoordinate_apply`, `OAI.Erdos3.VectorPolynomial.torusDerivative_monomial_height`, `OAI.Erdos3.exists_common_translation_retained_scores`, `OAI.Erdos3.exists_external_kernel_precenter_native_point_partners`, `OAI.Erdos3.exists_mass_bounded_patch_niltest_budget`, `OAI.Erdos3.exists_native_normalized_square`, `OAI.Erdos3.exists_precenter_forecast_finiteLaw_native_partners`, `OAI.Erdos3.exists_projectedPotential_height_budget`, `OAI.Erdos3.exists_synchronizedSquare_budget`, `OAI.Erdos3.extend_selected_original`, `OAI.Erdos3.externalNetMaskFamily`, `OAI.Erdos3.fractionalCoefficientPolynomial_mass_le_of_weightedSupportLE`, `OAI.Erdos3.fractionalCoefficientPolynomial_mem_weightedSupportLE`, `OAI.Erdos3.linearRestrictionArithmeticBudget_le_exp`, `OAI.Erdos3.linearRestrictionHeight_le_exp_logPolynomial`, `OAI.Erdos3.linearRestrictionLogPolynomial`, `OAI.Erdos3.linearRestrictionLogPolynomial_eval`, `OAI.Erdos3.mem_taggedSubmodule`, `OAI.Erdos3.potential_integration_height_le_exp`, `OAI.Erdos3.precenterForecastNativeAtomLabelFintype`, `OAI.Erdos3.projectedPotentialHeight`, `OAI.Erdos3.projectedPotentialHeight_le_exp_logPolynomial`, `OAI.Erdos3.projectedPotentialLogPolynomial`, `OAI.Erdos3.samplerLongEmbedding_kernelExponent`, `OAI.Erdos3.stepOne_vertical_character`, `OAI.Erdos3.taggedSubmodule`, `OAI.Erdos3.taggedSubmoduleBasis`, `OAI.Erdos3.taggedSubmoduleBasis_apply`, `OAI.Erdos3.taggedSubmoduleBasis_of_ne`, `OAI.Erdos3.taggedSubmoduleBasis_same`, `OAI.Erdos3.taggedSubmoduleEquiv`, `OAI.Erdos3.taggedSubmoduleEquiv_apply`, `OAI.Erdos3.taggedSubmoduleEquiv_symm_apply`, `OAI.Erdos3.weightedPolynomialPotential_coeff`, `OAI.Erdos3.weightedPolynomialPotential_height`, `OAI.MvPolynomial.IsWeightedHomogeneous.totalDegree_le_of_positive_weights`, `_private.Sampling.MarkedKernelProjectionScoreRestoration.0.OAI.Erdos3.integral_threshold_indicator_lower`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B041
import Definitions.Def_OAIErdos3B108
import Definitions.Def_OAIErdos3B117

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MarkedKernelProjectionScoreRestoration
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {Ω Λ : Type*} [Fintype Ω] [MeasurableSpace Λ]

theorem integral_threshold_indicator_lower
    (μ : Measure Λ) [IsProbabilityMeasure μ] {f : Λ → ℝ} {B δ : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hf : Measurable f) (hi : Integrable f μ)
    (hcap : ∀ l, f l ≤ B) (havg : δ ≤ ∫ l, f l ∂μ) :
    δ / (2 * B) ≤ ∫ l, {l | δ / 2 ≤ f l}.indicator (fun _ => (1 : ℝ)) l ∂μ := by
  let E : Set Λ := {l | δ / 2 ≤ f l}
  have hE : MeasurableSet E := measurableSet_le measurable_const hf
  have hg : Integrable (E.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hE
  have hpoint : ∀ l, f l ≤ δ / 2 + B * E.indicator (fun _ => (1 : ℝ)) l := by
    intro l
    by_cases hl : l ∈ E
    · simp only [Set.indicator_of_mem hl]
      linarith [hcap l]
    · have hl' : f l < δ / 2 := lt_of_not_ge hl
      simp only [Set.indicator_of_notMem hl, mul_zero, add_zero]
      exact hl'.le
  have hbound := integral_mono hi ((integrable_const (δ / 2)).add (hg.const_mul B))
    hpoint
  change (∫ l, f l ∂μ) ≤ ∫ l, δ / 2 + B * E.indicator (fun _ => (1 : ℝ)) l ∂μ at hbound
  rw [integral_add (integrable_const (δ / 2)) (hg.const_mul B),
    integral_const_mul] at hbound
  simp only [integral_const, probReal_univ, one_smul] at hbound
  apply (div_le_iff₀ (by positivity : 0 < 2 * B)).2
  dsimp only [E] at hbound
  nlinarith

theorem exists_common_translation_retained_scores
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (μ : Measure Λ) [IsProbabilityMeasure μ]
    (f : Ω → Λ → ℝ) {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hf : ∀ a ∈ H, Measurable (f a))
    (hi : ∀ a ∈ H, Integrable (f a) μ)
    (hcap : ∀ a ∈ H, ∀ l, f a l ≤ B)
    (havg : ∀ a ∈ H, δ ≤ ∫ l, f a l ∂μ) :
    ∃ l, ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
      δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
      ∀ a ∈ H', δ / 2 ≤ f a l := by
  classical
  let E (a : Ω) : Set Λ := {l | δ / 2 ≤ f a l}
  let g (a : Ω) : Λ → ℝ := (E a).indicator (fun _ => 1)
  have hg : ∀ a ∈ H, Integrable (g a) μ := by
    intro a ha
    exact (integrable_const 1).indicator (measurableSet_le measurable_const (hf a ha))
  let m (l : Λ) : ℝ := ∑ a ∈ H, outer.weight a * g a l
  have hm : Integrable m μ :=
    integrable_finsetSum H (fun a ha => (hg a ha).const_mul (outer.weight a))
  have hmean : δ / (2 * B) * outer.mass H ≤ ∫ l, m l ∂μ := by
    dsimp only [m]
    rw [integral_finsetSum H (fun a ha => (hg a ha).const_mul (outer.weight a))]
    simp only [integral_const_mul, FiniteProbabilityWeights.mass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [mul_comm (δ / (2 * B))]
    exact mul_le_mul_of_nonneg_left
      (integral_threshold_indicator_lower μ hB hδ (hf a ha) (hi a ha)
        (hcap a ha) (havg a ha)) (outer.nonneg a)
  obtain ⟨l, hl⟩ := probabilityIntegralThresholdPoint μ hm hmean
  let H' := H.filter (fun a => δ / 2 ≤ f a l)
  have hmass : outer.mass H' = m l := by
    simp only [FiniteProbabilityWeights.mass, H', Finset.sum_filter, m, g, E,
      Set.indicator, Set.mem_ofPred_eq]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  refine ⟨l, H', Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · rw [hmass]
    exact (mul_pos (div_pos hδ (by positivity)) hH).trans_le hl
  · rwa [hmass]
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory

variable {G Λ : Type*} [Fintype G] (p : FiniteProbabilityWeights G)

noncomputable def finiteScore (weight : G → ℂ) (observable : G → Λ → ℂ) (l : Λ) : ℝ :=
  (p.complexMean (fun x => weight x * observable x l)).re

variable [MeasurableSpace Λ]

theorem finiteScore_measurable (weight : G → ℂ) (observable : G → Λ → ℂ)
    (hobservable : ∀ x, Measurable (observable x)) :
    Measurable (p.finiteScore weight observable) :=
  (p.complexMean_measurable (fun l x => weight x * observable x l)
    (fun x => (hobservable x).const_mul (weight x))).re

theorem finiteScore_integrable (μ : Measure Λ) (weight : G → ℂ) (observable : G → Λ → ℂ)
    (hobservable : ∀ x, Integrable (observable x) μ) :
    Integrable (p.finiteScore weight observable) μ :=
  (p.complexMean_integrable μ (fun l x => weight x * observable x l)
    (fun x => (hobservable x).const_mul (weight x))).re

omit [MeasurableSpace Λ] in

theorem finiteScore_abs_le (weight : G → ℂ) (observable : G → Λ → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hweight : ∀ x, ‖weight x‖ ≤ B)
    (hobservable : ∀ x l, ‖observable x l‖ ≤ 1) (l : Λ) :
    |p.finiteScore weight observable l| ≤ B := by
  apply (RCLike.abs_re_le_norm (p.complexMean (fun x => weight x * observable x l))).trans
  apply (p.norm_complexMean_le_mean_norm _).trans
  apply (p.mean_mono (fun x => ?_)).trans_eq (p.mean_const B)
  rw [norm_mul]
  simpa only [mul_one] using mul_le_mul (hweight x) (hobservable x l) (norm_nonneg _) hB

omit [MeasurableSpace Λ] in
theorem finiteScore_le (weight : G → ℂ) (observable : G → Λ → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hweight : ∀ x, ‖weight x‖ ≤ B)
    (hobservable : ∀ x l, ‖observable x l‖ ≤ 1) (l : Λ) :
    p.finiteScore weight observable l ≤ B :=
  (le_abs_self _).trans (p.finiteScore_abs_le weight observable hB hweight hobservable l)

theorem integral_finiteScore (μ : Measure Λ) (weight : G → ℂ) (observable : G → Λ → ℂ)
    (hobservable : ∀ x, Integrable (observable x) μ) :
    (∫ l, p.finiteScore weight observable l ∂μ) =
      (p.complexMean (fun x => weight x * ∫ l, observable x l ∂μ)).re := by
  change (∫ l, RCLike.re (p.complexMean (fun x => weight x * observable x l)) ∂μ) = _
  rw [integral_re (p.complexMean_integrable μ _
    (fun x => (hobservable x).const_mul (weight x)))]
  rw [p.integral_complexMean μ _ (fun x => (hobservable x).const_mul (weight x))]
  simp only [integral_const_mul]
  rfl

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open MeasureTheory Module CircleFourier
open scoped TensorProduct

variable {L σ τ Ω G : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [Fintype Ω] [Fintype G]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open MeasureTheory Module CircleFourier
open scoped TensorProduct

variable {L σ τ Ω J X : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype J]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem exists_external_kernelProjection_common_translation
    (T : X → D.Niltest w) (hT : ∀ x, (T x).UnitIntervalValued)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (path : Ω → J → D.Space) (weight : Ω → J → ℂ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ j, ‖weight a j‖ ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun j => weight a j * ((T (physical a j)).kernelProjection K hK).observable
        (path a j))).re) :
    ∃ z : D.RealGroup, z.coord ∈ K.baseChange ℝ ∧
      (∀ y : ℝ ⊗[ℚ] L, ⁅z.coord, y⁆ = 0) ∧
      ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
        δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
        ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean
          (fun j => weight a j * (T (physical a j)).observable (z • path a j))).re := by
  let μ := circleAverageTupleMeasure (List.finRange (finrank ℚ K))
  let obs (a : Ω) (j : J) (t : KernelProjectionParameters K) :=
    (T (physical a j)).observable (D.kernelProjectionTranslation K hK t • path a j)
  let score (a : Ω) := (localLaw a).finiteScore (weight a) (obs a)
  have hmeas (a : Ω) (j : J) : Measurable (obs a j) :=
    ((T (physical a j)).continuous_kernelProjectionTranslation_observable
      K hK (path a j)).measurable
  have hi (a : Ω) (j : J) : Integrable (obs a j) μ :=
    (T (physical a j)).integrable_kernelProjectionTranslation_observable K hK (path a j)
  have hscoreMeas (a : Ω) : Measurable (score a) :=
    (localLaw a).finiteScore_measurable (weight a) (obs a) (hmeas a)
  have hscoreInt (a : Ω) : Integrable (score a) μ :=
    (localLaw a).finiteScore_integrable μ (weight a) (obs a) (hi a)
  have hcap (a : Ω) (ha : a ∈ H) (t : KernelProjectionParameters K) : score a t ≤ B :=
    (localLaw a).finiteScore_le (weight a) (obs a) hB.le (hweight a ha)
      (fun j _ => (hT (physical a j)).norm_le_one _) t
  have havg (a : Ω) (ha : a ∈ H) : δ ≤ ∫ t, score a t ∂μ := by
    rw [(localLaw a).integral_finiteScore μ (weight a) (obs a) (hi a)]
    simpa only [obs, μ, ← kernelProjection_observable_eq_integral] using hscore a ha
  obtain ⟨t, H', hsub, hpos, hmass, hs⟩ :=
    exists_common_translation_retained_scores outer H hH μ score hB hδ
      (fun a _ => hscoreMeas a) (fun a _ => hscoreInt a) hcap havg
  exact ⟨D.kernelProjectionTranslation K hK t,
    D.kernelProjectionTranslation_mem K hK t,
    D.kernelProjectionTranslation_central K hK t,
    H', hsub, hpos, hmass, hs⟩

theorem exists_external_kernelProjection_restored_orbit
    (T : X → D.Niltest w) (hT : ∀ x, (T x).UnitIntervalValued)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (orbit : D.filtration.realification.PolynomialOrbit v)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → J → τ → ℤ) (weight : Ω → J → ℂ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ j, ‖weight a j‖ ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun j => weight a j * (((T (physical a j)).kernelProjection K hK).withOrbit orbit).eval
        (point a j))).re) :
    ∃ z : D.RealGroup, z.coord ∈ K.baseChange ℝ ∧
      (∀ x, ((T x).withLeftTranslatedOrbit z orbit).observable = (T x).observable ∧
        ((T x).withLeftTranslatedOrbit z orbit).UnitIntervalValued ∧
        ∀ p, ((T x).withLeftTranslatedOrbit z orbit).ComplexityLE p ↔ (T x).ComplexityLE p) ∧
      ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
        δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
        ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean (fun j => weight a j *
          ((T (physical a j)).withLeftTranslatedOrbit z orbit).eval (point a j))).re := by
  obtain ⟨z, hz, _, H', hsub, hpos, hmass, hs⟩ :=
    exists_external_kernelProjection_common_translation T hT K hK outer H hH localLaw
      physical (fun a j => QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval v (point a j) orbit))
      weight hB hδ hweight hscore
  refine ⟨z, hz, fun x => ⟨rfl, hT x, fun _ => Iff.rfl⟩,
    H', hsub, hpos, hmass, ?_⟩
  intro a ha
  simpa only [withLeftTranslatedOrbit_eval] using hs a ha

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.NilpotentLieFiltration
open VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

@[simp] theorem polynomialOrbitRealEval_constantGroupOrbit
    (w : σ → ℕ) (g : F.realification.Group) (x : σ → ℝ) :
    F.realification.polynomialOrbitRealEval w x
      (F.realification.constantGroupOrbit w g) = g := by
  apply NilpotentLieBCHGroup.ext
  simp only [polynomialOrbitRealEval_coord, constantGroupOrbit, polynomialOrbitOfLog_log,
    eval₂_monomial, Finsupp.prod_zero_index, one_smul]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.Niltest
open scoped TensorProduct

variable {L M σ τ Ω X : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype X]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedNaturalChartScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*}
variable {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (j : Fin m) (i : Fin (n j))

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

noncomputable def allocatedPrincipalChartRatio : ℝ :=
  (basisAxisScale (basis j) i : ℝ) / scale

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.TaggedSubmoduleBasis
namespace OAI

section

namespace Erdos3

open Module

variable {R T : Type*} [Semiring R] {J I : T → Type*}

def taggedSubmodule (U : ∀ t, Submodule R (J t → R)) : Submodule R ((Σ t, J t) → R) where
  carrier := {x | ∀ t, (fun j => x ⟨t, j⟩) ∈ U t}
  zero_mem' := fun t => (U t).zero_mem
  add_mem' := fun hx hy t => (U t).add_mem (hx t) (hy t)
  smul_mem' := fun c _ hx t => (U t).smul_mem c (hx t)

@[simp]
theorem mem_taggedSubmodule (U : ∀ t, Submodule R (J t → R)) (x : (Σ t, J t) → R) :
    x ∈ taggedSubmodule U ↔ ∀ t, (fun j => x ⟨t, j⟩) ∈ U t := Iff.rfl

def taggedSubmoduleEquiv (U : ∀ t, Submodule R (J t → R)) :
    (∀ t, U t) ≃ₗ[R] taggedSubmodule U where
  toFun x := ⟨fun j => (x j.1 : J j.1 → R) j.2, fun t => (x t).property⟩
  invFun x := fun t => ⟨fun j => (x : (Σ t, J t) → R) ⟨t, j⟩, x.property t⟩
  left_inv x := by
    funext t
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    funext j
    rfl
  map_add' x y := rfl
  map_smul' c x := rfl

@[simp]
theorem taggedSubmoduleEquiv_apply (U : ∀ t, Submodule R (J t → R))
    (x : ∀ t, U t) (t : T) (j : J t) :
    (taggedSubmoduleEquiv U x : (Σ t, J t) → R) ⟨t, j⟩ = (x t : J t → R) j := rfl

@[simp]
theorem taggedSubmoduleEquiv_symm_apply (U : ∀ t, Submodule R (J t → R))
    (x : taggedSubmodule U) (t : T) (j : J t) :
    ((taggedSubmoduleEquiv U).symm x t : J t → R) j =
      (x : (Σ t, J t) → R) ⟨t, j⟩ := rfl

variable [Fintype T]

noncomputable def taggedSubmoduleBasis (U : ∀ t, Submodule R (J t → R))
    (b : ∀ t, Basis (I t) R (U t)) : Basis (Σ t, I t) R (taggedSubmodule U) :=
  (Pi.basis b).map (taggedSubmoduleEquiv U)

theorem taggedSubmoduleBasis_apply [DecidableEq T]
    (U : ∀ t, Submodule R (J t → R)) (b : ∀ t, Basis (I t) R (U t))
    (t : T) (i : I t) (t' : T) (j : J t') :
    (taggedSubmoduleBasis U b ⟨t, i⟩ : (Σ t, J t) → R) ⟨t', j⟩ =
      ((Pi.single (M := fun t => U t) t (b t i) t' : U t') : J t' → R) j := by
  rw [taggedSubmoduleBasis, Basis.map_apply, Pi.basis_apply]
  rfl

@[simp]
theorem taggedSubmoduleBasis_same
    (U : ∀ t, Submodule R (J t → R)) (b : ∀ t, Basis (I t) R (U t))
    (t : T) (i : I t) (j : J t) :
    (taggedSubmoduleBasis U b ⟨t, i⟩ : (Σ t, J t) → R) ⟨t, j⟩ = (b t i : J t → R) j := by
  classical
  rw [taggedSubmoduleBasis_apply, Pi.single_eq_same]

theorem taggedSubmoduleBasis_of_ne
    (U : ∀ t, Submodule R (J t → R)) (b : ∀ t, Basis (I t) R (U t))
    (t : T) (i : I t) (t' : T) (j : J t') (h : t' ≠ t) :
    (taggedSubmoduleBasis U b ⟨t, i⟩ : (Σ t, J t) → R) ⟨t', j⟩ = 0 := by
  classical
  rw [taggedSubmoduleBasis_apply, Pi.single_eq_of_ne h]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolynomialPatchWeightedChartNiltest
namespace OAI

section

namespace Erdos3.PolynomialPatch

open scoped NNReal TensorProduct

variable {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
  [Fintype (PolynomialShearIndex A.weight)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

noncomputable def shearNiltest (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    (polynomialShearNilmanifold A.weight s A.weight_le).Niltest (fun _ : σ => 1) where
  orbit := A.shearOrbit
  observable z := (A.shearObservable z : ℂ)
  normBound := 1
  lipBound := A.shearObservableLipBound M
  norm_le z := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, NNReal.coe_one] using A.abs_shearObservable_le_one z
  lipschitz := by
    let : MetricSpace ((polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) :=
      (polynomialShearNilmanifold A.weight s A.weight_le).metricSpace
    change LipschitzWith (A.shearObservableLipBound M)
      (fun z : (polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
        polynomialShearRealLattice s A.weight_le => (A.shearObservable z : ℂ))
    simpa only [one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitz.comp (A.shearObservable_lipschitz M hA)

theorem shearNiltest_unitInterval (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    (A.shearNiltest M hA).UnitIntervalValued := by
  intro z
  exact ⟨rfl, A.shearObservable_mem_Icc z⟩

theorem shearNiltest_complexity (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) {p : ℝ}
    (hgeometry : (polynomialShearNilmanifold A.weight s A.weight_le).GeometryComplexityLE p)
    (hbound : Real.log (3 + (A.shearObservableLipBound M : ℝ)) ≤ p) :
    (A.shearNiltest M hA).ComplexityLE p := by
  exact ⟨hgeometry, by simpa only [shearNiltest, NNReal.coe_one, show (2 : ℝ) + 1 = 3 by norm_num] using hbound⟩

end Erdos3.PolynomialPatch

end

section

namespace Erdos3.PolynomialSlots

variable {X Y : Type*} {d s : ℕ} {w : Fin d → ℕ}

theorem shearObservable_eval_lift (B : PolynomialSlots X d w) (A : PolynomialSlots Y d w)
    (hw : Monotone w) (hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s)
    (Φ : PatchKernel d) (t : Y → ℝ) :
    let P : PolynomialPatch X s d := ⟨w, hpos, hs, hw, B, Φ⟩
    P.shearObservable (QuotientGroup.mk (A.shearGroupLift s hs t)) =
      (B.shearTransformedSlots hw (A.loweringAt t)).patchValue Φ := by
  intro P
  change polynomialShearOrbitSum w s hs P.shearKernel (A.shearGroupLift s hs t) = _
  rw [P.shearOrbitSum_eq_patchValue]
  simp only [P, shearGroupLift, MulEquiv.apply_symm_apply, inv_inv]

theorem shearObservable_eval_orbit [Fintype (PolynomialShearIndex w)]
    (B : PolynomialSlots X d w) (A : PolynomialSlots Y d w)
    (hw : Monotone w) (hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s)
    (Φ : PatchKernel d) (t : Y → ℝ) :
    let P : PolynomialPatch X s d := ⟨w, hpos, hs, hw, B, Φ⟩
    P.shearObservable (QuotientGroup.mk
      ((polynomialShearFiltration w s hs).realification.polynomialOrbitRealEval
        (fun _ : Y => 1) t (A.shearPolynomialOrbit s hs))) =
      (B.shearTransformedSlots hw (A.loweringAt t)).patchValue Φ := by
  rw [A.shearPolynomialOrbit_realEval]
  exact shearObservable_eval_lift B A hw hpos hs Φ t

end Erdos3.PolynomialSlots

end

section

namespace Erdos3

open scoped NNReal TensorProduct

end Erdos3

end

section

namespace Erdos3

open scoped NNReal TensorProduct

namespace PolynomialPatch

variable {X Y : Type*} {s d : ℕ} (P : PolynomialPatch X s d)
  [Fintype (PolynomialShearIndex P.weight)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]

end PolynomialPatch

theorem exists_mass_bounded_patch_niltest_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type*} {d : ℕ} (P : PolynomialPatch X s d)
      [Fintype (PolynomialShearIndex P.weight)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      (M : ℝ≥0) (hP : ∀ i, realPolynomialMass (P.form.center i) ≤ M) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (M : ℝ) ≤ p → (P.kernel.lip : ℝ) ≤ Real.exp p →
      (P.shearNiltest M hP).ComplexityLE ((p + 2) ^ C) := by
  obtain ⟨a, ha, hlog⟩ := exists_bchLogMetricConstant_exp_bound s
  obtain ⟨C, hC, hbudget⟩ := exists_mass_bounded_shear_parameter_budget s a
  refine ⟨C, hC, ?_⟩
  intro X d P _ _ _ _ _ M hP p hp hd hMp hLip
  let D := Fintype.card (PolynomialShearIndex P.weight)
  have hD : D ≤ d * (d + 1) ^ s := by
    simpa only [Fintype.card_fin] using polynomialShearIndex_card_le P.weight s
      (fun i => lt_of_lt_of_le Nat.zero_lt_one (P.weight_pos i)) P.weight_le
  obtain ⟨t, ht, hgeom, htotal⟩ := hbudget d D M p hp M.coe_nonneg hMp hd hD
  have hDt : (D : ℝ) ≤ t := by
    have hle : D ≤ D + s.factorial + 2 * s + 1 := by omega
    exact (Nat.cast_le.mpr hle).trans hgeom
  have hHt : ((2 * s + 1 : ℕ) : ℝ) ≤ t := by
    have hle : 2 * s + 1 ≤ D + s.factorial + 2 * s + 1 := by omega
    exact (Nat.cast_le.mpr hle).trans hgeom
  have hHexp : ((2 * s + 1 : ℕ) : ℝ) ≤ Real.exp t :=
    hHt.trans (by linarith [Real.add_one_le_exp t])
  have hClog := hlog D (2 * s + 1) t ht hDt hHexp
  have hv : 0 ≤ (t + a) ^ a + 1 := by positivity
  have hObs := shearObservable_log_bound P M hp hv hLip hClog
  have hK := shearKernelLogBudget_nonneg s d M.coe_nonneg hp
  have hT := shearActionLogBudget_nonneg s d M.coe_nonneg
  have htP : t ≤ (p + 2) ^ C := by
    linarith [pow_nonneg (by positivity : 0 ≤ t + a) a]
  apply P.shearNiltest_complexity M hP
  · exact RationalFilteredNilmanifold.GeometryComplexityLE.mono
      (polynomialShearNilmanifold P.weight s P.weight_le)
      (polynomialShearNilmanifold_complexity_budget P.weight s
        (fun i => lt_of_lt_of_le Nat.zero_lt_one (P.weight_pos i)) P.weight_le)
      (hgeom.trans htP)
  · linarith

end Erdos3

end

section

namespace Erdos3

open scoped NNReal TensorProduct

end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open scoped NNReal TensorProduct

variable {σ τ ξ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
    [Fintype (PolynomialShearIndex A.weight)]
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

end Erdos3.PolynomialPatch

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedNativeUniformBudget
namespace OAI

section

namespace Erdos3
open scoped NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra NativeSampleModel.topology NativeSampleModel.topologicalAdd NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

noncomputable def NativeSampleModel.weaken {σ X : Type*} {w : σ → ℕ}
    {degree : ℕ} {p q : ℝ} {sample : X → σ → ℤ} {f : X → ℂ}
    (F : NativeSampleModel w degree p sample f) (hpq : p ≤ q) :
    NativeSampleModel w degree q sample f :=
  { F with complexity := F.complexity.mono hpq }

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem exists_normalizedNative_uniform_budget (m Anorm Anative : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {B P E analytic gain mass spatial volume coverLog : ℝ} {nX : ℕ},
      0 ≤ B → P ∈ Set.Icc 0 B → E ∈ Set.Icc 0 B → analytic ∈ Set.Icc 0 B →
      gain ∈ Set.Icc 0 B → mass ∈ Set.Icc 0 B → spatial ∈ Set.Icc 0 B →
      volume ∈ Set.Icc 0 B → coverLog ≤ B → (nX : ℝ) ≤ B →
      let budget := (B + A) ^ A
      (((m + 1 : ℕ) : ℝ) * P + nX * P ≤ budget) ∧
      coverLog ≤ budget ∧
      (P + E + analytic + Anorm) ^ Anorm ≤ budget ∧
      (gain + 8 + mass + spatial + volume + 2) ^ Anative ≤ budget := by
  let X : Polynomial ℕ := Polynomial.X
  let poly : Polynomial ℕ := (m + 1 : ℕ) * X + X ^ 2 + X +
    (3 * X + Polynomial.C Anorm) ^ Anorm + (4 * X + 10) ^ Anative
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro B P E analytic gain mass spatial volume coverLog nX hB hP hE ha hg hm hs hv hc hn budget
  have hsum : ((m + 1 : ℕ) : ℝ) * B + B ^ 2 + B +
      (3 * B + Anorm) ^ Anorm + (4 * B + 10) ^ Anative ≤ budget := by
    simpa [poly, X, Polynomial.eval₂_pow] using hbound B hB
  have hnorm0 : 0 ≤ (3 * B + Anorm) ^ Anorm := by positivity
  have hnative0 : 0 ≤ (4 * B + 10) ^ Anative := by positivity
  have hperiod0 : 0 ≤ ((m + 1 : ℕ) : ℝ) * B := by positivity
  have hperiod : ((m + 1 : ℕ) : ℝ) * P + nX * P ≤ ((m + 1 : ℕ) : ℝ) * B + B ^ 2 := by
    rw [pow_two]
    exact add_le_add (mul_le_mul_of_nonneg_left hP.2 (Nat.cast_nonneg _))
      (mul_le_mul hn hP.2 hP.1 hB)
  have hnorm : (P + E + analytic + Anorm) ^ Anorm ≤ (3 * B + Anorm) ^ Anorm := by
    apply pow_le_pow_left₀ (add_nonneg (add_nonneg (add_nonneg hP.1 hE.1) ha.1) (Nat.cast_nonneg _))
    linarith only [hP.2, hE.2, ha.2]
  have hnative : (gain + 8 + mass + spatial + volume + 2) ^ Anative ≤ (4 * B + 10) ^ Anative := by
    apply pow_le_pow_left₀ (add_nonneg
      (add_nonneg (add_nonneg (add_nonneg (add_nonneg hg.1 (by norm_num)) hm.1) hs.1) hv.1) (by norm_num))
    linarith only [hg.2, hm.2, hs.2, hv.2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith only [hsum, hperiod, hB, hnorm0, hnative0]
  · linarith only [hsum, hc, hperiod0, sq_nonneg B, hnorm0, hnative0]
  · linarith only [hsum, hnorm, hperiod0, sq_nonneg B, hB, hnative0]
  · linarith only [hsum, hnative, hperiod0, sq_nonneg B, hB, hnorm0]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealReducedSquarePolynomial
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem adaptedReducedRealSymbolHom_square_diagonal (g : F.RealAdaptedPolynomialGroup w) :
    F.squareFiltration.adaptedReducedRealSymbolHom w (F.realSquareDiagonalPolynomialHom w g) =
      F.reducedSquareRealDiagonalHom w (F.adaptedReducedRealSymbolHom w g) := by
  have hcomp : (F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap.comp
      (F.squareDiagonalPolynomialMap w).toLinearMap =
        (F.reducedSquareDiagonalSymbolMap w).toLinearMap.comp (F.adaptedReducedSymbolMap w).toLinearMap := by
    apply LinearMap.ext
    intro p
    change F.reducedSquareSymbolMap w
        (F.squareFiltration.polynomialSymbolMap w (F.squareDiagonalPolynomialMap w p)) =
      F.reducedSquareDiagonalSymbolMap w (F.quotientTopSymbolMap w (F.polynomialSymbolMap w p))
    rw [← F.squareDiagonalSymbolMap_symbol, F.reducedSquareDiagonalSymbolMap_quotient]
  apply NilpotentLieBCHGroup.ext
  change (F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ
    ((F.squareDiagonalPolynomialMap w).toLinearMap.baseChange ℝ g.coord) =
      (F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ
        ((F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ g.coord)
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_comp,
    LinearMap.comp_apply]

theorem adaptedReducedRealSymbolHom_square_relative (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.squareFiltration.adaptedReducedRealSymbolHom w (F.realRelativeSquarePolynomial w hw x) =
      (⟨F.realReducedRelativeSquareSymbolMap w hw x⟩ :
        F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) := by
  have hcomp : (F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap.comp
      (F.relativeSquareLift w hw) = F.reducedRelativeSquareSymbolMap w hw := by
    apply LinearMap.ext
    intro p
    rfl
  apply NilpotentLieBCHGroup.ext
  change (F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ
    ((F.relativeSquareLift w hw).baseChange ℝ x) = (F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ x
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp]

theorem adaptedReducedRealSymbolHom_square_projection
    (r : F.squareFiltration.RealAdaptedPolynomialGroup w) :
    F.reducedSquareRealSymbolHom w (F.squareFiltration.adaptedReducedRealSymbolHom w r) =
      F.adaptedReducedRealSymbolHom w (F.realSquareSndPolynomialHom w r) := by
  have hcomp : (F.reducedSquareSndSymbolMap w).toLinearMap.comp
      (F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap =
        (F.adaptedReducedSymbolMap w).toLinearMap.comp (F.squareSndPolynomialMap w).toLinearMap := by
    apply LinearMap.ext
    intro p
    change F.reducedSquareSndSymbolMap w
        (F.reducedSquareSymbolMap w (F.squareFiltration.polynomialSymbolMap w p)) =
      F.quotientTopSymbolMap w (F.polynomialSymbolMap w (F.squareSndPolynomialMap w p))
    rw [F.reducedSquareSndSymbolMap_quotient, F.squareSndSymbolMap_symbol]
  apply NilpotentLieBCHGroup.ext
  change (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
    ((F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ r.coord) =
      (F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ
        ((F.squareSndPolynomialMap w).toLinearMap.baseChange ℝ r.coord)
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_comp,
    LinearMap.comp_apply]

theorem realReducedRelativeSquareSymbolMap_of_square_factorization (hw : ∀ i, 0 < w i)
    (r : F.squareFiltration.RealAdaptedPolynomialGroup w) (g : F.RealAdaptedPolynomialGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (hr : r = F.realRelativeSquarePolynomial w hw x * F.realSquareDiagonalPolynomialHom w g) :
    F.realReducedRelativeSquareSymbolMap w hw x =
      (F.reducedSquareRealRelativePart w (F.squareFiltration.adaptedReducedRealSymbolHom w r)).coord := by
  rw [hr, map_mul, F.adaptedReducedRealSymbolHom_square_relative,
    F.adaptedReducedRealSymbolHom_square_diagonal]
  let k : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w :=
    ⟨F.realReducedRelativeSquareSymbolMap w hw x⟩
  have hk : F.reducedSquareRealSymbolHom w k = 1 := by
    apply NilpotentLieBCHGroup.ext
    exact F.realReducedRelativeSquareSymbolMap_projection w hw x
  have he := F.reducedSquareRealRelativePart_of_factors w k (F.adaptedReducedRealSymbolHom w g) hk
  exact (congrArg NilpotentLieBCHGroup.coord he).symm

variable [Fintype σ] (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hF in
theorem normalized_real_square_derivative_identity (h : σ → ℚ) (e m : ℝ ⊗[ℚ] L)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (r : F.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hf : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) r).coord =
      normalizedShiftLog (s + 1) h (-e) (-m) (F.realAdaptedPolynomialMap (fun _ => 1) g.coord))
    (hs : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareSndPolynomialHom (fun _ => 1) r).coord =
      F.realAdaptedPolynomialMap (fun _ => 1) g.coord) :
    F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
        F.realFirstCoefficientConstant (fun _ => 1) e -
        F.realFirstCoefficientAdjoint (fun _ => 1) g (F.realFirstCoefficientConstant (fun _ => 1) m) =
      F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
        (F.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) := by
  obtain ⟨x, hx, hr, _⟩ := F.exists_real_normalized_square_factors b ω hF h e m g r hf hs
  exact F.real_normalized_square_coefficient_identity b ω hF h e m g _ x
    (F.realReducedRelativeSquareSymbolMap_of_square_factorization (fun _ => 1)
      (fun _ => Nat.zero_lt_one) r g x hr) hx

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedCommonFamily
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

universe uσ uι uL

def CoefficientCorrectionSpec (s C : ℕ) : Prop :=
  ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
    [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
        (A D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (_hA : F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T (Real.exp p) A.coord)
        (_hD : F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l D.coord)
        (h : σ → ℤ) (_hh : ∀ i, |(h i : ℝ)| ≤ T i)
        (ε u μ v : F.RealFirstCoefficientModule (fun _ : σ => 1))
        (_hε : F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp p) ε)
        (_hu : F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp p) u)
        (_hμ : F.FirstCoefficientGrid e ω hF (fun _ => 1) l μ)
        (_hv : F.FirstCoefficientGrid e ω hF (fun _ => 1) l v),
        F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C))
          (F.coefficientSlowCorrection A (fun i => (h i : ℝ)) ε u) ∧
        F.FirstCoefficientGrid e ω hF (fun _ => 1) m
          (F.coefficientGridCorrection D (fun i => (h i : ℝ)) μ v)

theorem exists_coefficient_correction_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CoefficientCorrectionSpec.{uσ, uι, uL} s C := by
  obtain ⟨a, _, hadjoint⟩ := exists_firstCoefficient_adjoint_bound.{uσ, uι, uL} (s + 1) 1
  obtain ⟨d, _, hderivative⟩ := exists_firstCoefficient_direction_bound.{uσ, uι, uL} (s + 1) 1
  obtain ⟨r, _, hgrid⟩ := exists_firstCoefficient_operation_grid.{uσ, uι, uL} (s + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_synchronizedCorrection_budget a d r
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  have hgrids := hgrid F e ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨m, hm, hmp, hlm, hAdjointGrid, hDerivativeGrid⟩ := hgrids
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr (hbudget p hp).2), hlm, ?_⟩
  intro T hT A D hA hD h hh ε u μ v hε hu hμ hv
  have hinput : Real.exp p ≤ Real.exp ((p + 2) ^ 1) :=
    Real.exp_le_exp.mpr (by rw [pow_one]; linarith)
  have hA' := F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hT hinput A.coord hA
  have hAi : F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T (Real.exp ((p + 2) ^ 1)) A⁻¹.coord := by
    intro i
    simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hA' i
  have hdir := hderivative F e ω hF H p hH hp hι hσ hHp hstructure T hT A hA' h hh
  have hsum := F.firstCoefficientSlowBound_add e ω hF (fun _ => 1) T (Real.exp p) (Real.exp p) ε u hε hu
  have hdiff := F.firstCoefficientSlowBound_sub e ω hF (fun _ => 1) T
    (Real.exp p + Real.exp p) (Real.exp ((p + d) ^ d)) _ _ hsum hdir
  have hslow := hadjoint F e ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    H p hH hp hι hσ hHp hstructure T hT A⁻¹ hAi
    (Real.exp p + Real.exp p + Real.exp ((p + d) ^ d)) (by positivity) _ hdiff
  have hsize : Real.exp ((p + a) ^ a) * (Real.exp p + Real.exp p + Real.exp ((p + d) ^ d)) ≤
      Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp ((p + a) ^ a) * Real.exp (p + (p + d) ^ d + 2) :=
        mul_le_mul_of_nonneg_left (exp_repeated_add_le hp (by positivity)) (Real.exp_nonneg _)
      _ = Real.exp ((p + a) ^ a + p + (p + d) ^ d + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (hbudget p hp).1
  constructor
  · exact F.firstCoefficientSlowBound_mono e ω hF (fun _ => 1) T hT hsize _ hslow
  · have hv' := F.firstCoefficientGrid_mono e ω hF (fun _ => 1) hl hlm v hv
    have hsumGrid := F.firstCoefficientGrid_add e ω hF (fun _ => 1) m _ _ hv'
      (hAdjointGrid D μ hD hμ)
    exact F.firstCoefficientGrid_sub e ω hF (fun _ => 1) m _ _ hsumGrid (hDerivativeGrid D.coord hD h)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

universe uσ uι uL

def NativeNormalizedSquareSpec (s C : ℕ) : Prop :=
  ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
    [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (_hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (p : ℝ) (_hp : 0 ≤ p) (_hD : D.GeometryComplexityLE p)
    (h : σ → ℚ) (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
    ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
      (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
      ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
        D.filtration.realAdaptedPolynomialMap (fun _ => 1)
            (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
          normalizedShiftLog (s + 1) h (-ε.coord) (-γ.coord)
            (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
        D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
        D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
            D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
            D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
              (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
          D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
            (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r)

theorem exists_native_normalized_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeNormalizedSquareSpec.{uσ, uι, uL} s C := by
  obtain ⟨C, hC, hnorm⟩ := exists_bounded_realified_square_polynomial.{uσ, uL} (s + 1)
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ d _ _ _ D b ω hF p hp hD h g
  let f : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1) :=
    polynomialOrbitOfLog (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord)
      (D.filtration.realAdaptedPolynomialMap_adapted (fun _ => 1) g.coord)
  obtain ⟨ε, γ, hγ, hε, q, hq, hfst, hsnd⟩ := hnorm D p hp hD (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) h f
  let q' : D.filtration.squareFiltration.realification.adaptedLieSubalgebra (fun _ : σ => 1) :=
    ⟨q, (D.filtration.squareFiltration.realification.mem_adaptedSubmodule (fun _ => 1) q).mpr hq⟩
  obtain ⟨r, _, hrf, hrs⟩ := D.filtration.exists_realSquarePolynomial_lift (fun _ => 1) b ω hF q'
  have hf : D.filtration.realAdaptedPolynomialMap (fun _ => 1)
        (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
      normalizedShiftLog (s + 1) h (-ε.coord) (-γ.coord)
        (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) := hrf.trans hfst
  have hs : D.filtration.realAdaptedPolynomialMap (fun _ => 1)
        (D.filtration.realSquareSndPolynomialHom (fun _ => 1) r).coord =
      D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord := hrs.trans hsnd
  refine ⟨ε, γ, hγ, hε, r, hf, ?_, ?_⟩
  · apply D.filtration.realAdaptedPolynomialGroupHom_injective (fun _ => 1) b ω hF
    apply NilpotentLieBCHGroup.ext
    exact Subtype.ext hs
  · exact D.filtration.normalized_real_square_derivative_identity b ω hF h ε.coord γ.coord g r hf hs

end Erdos3

end

section

namespace Erdos3

theorem exists_synchronizedSquare_budget (r a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + (p + r) ^ r + a) ^ a ≤ (p + C) ^ C := by
  let P : Polynomial ℕ :=
    (Polynomial.X + (Polynomial.X + Polynomial.C r) ^ r + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [P, Polynomial.eval₂_pow] using hbudget p hp

namespace NilpotentLieFiltration

open Module

universe uσ uι uL

def SynchronizedSquareBoundSpec (s C : ℕ) : Prop :=
  ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
    [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
        (A D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (_hA : F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T (Real.exp p) A.coord)
        (_hD : F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l D.coord)
        (h : σ → ℤ) (_hh : ∀ i, |(h i : ℝ)| ≤ T i)
        (E R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
        (_hE : F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF)
          (fun _ => 1) T (Real.exp p) E)
        (_hR : F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF)
          (fun _ => 1) l R)
        (ε μ : F.RealFirstCoefficientModule (fun _ : σ => 1))
        (_hε : F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp p) ε)
        (_hμ : F.FirstCoefficientGrid e ω hF (fun _ => 1) l μ),
        F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C))
          (F.coefficientSlowCorrection A (fun i => (h i : ℝ)) ε
            (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) E)) ∧
        F.FirstCoefficientGrid e ω hF (fun _ => 1) m
          (F.coefficientGridCorrection D (fun i => (h i : ℝ)) μ
            (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) R))

theorem exists_synchronizedSquare_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SynchronizedSquareBoundSpec.{uσ, uι, uL} s C := by
  obtain ⟨r, _, hrelative⟩ := exists_reducedRelativeCoefficient_bound.{uσ, uι, uL} s
  obtain ⟨a, _, hcorrection⟩ := exists_coefficient_correction_bound.{uσ, uι, uL} s
  obtain ⟨C, hC, hbudget⟩ := exists_synchronizedSquare_budget r a
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨n, hn, hnp, hln, hrelative⟩ := hrelative F e ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  let q : ℝ := p + (p + r) ^ r
  have hpow : 0 ≤ (p + r) ^ r := by positivity
  have hq : 0 ≤ q := add_nonneg hp hpow
  have hpq : p ≤ q := le_add_of_nonneg_right hpow
  have hrq : (p + r) ^ r ≤ q := le_add_of_nonneg_left hp
  have hpqExp := Real.exp_le_exp.mpr hpq
  have hrqExp := Real.exp_le_exp.mpr hrq
  obtain ⟨m, hm, hmp, hnm, hcorrection⟩ := hcorrection F e ω hF H q hH hq
    (hι.trans hpq) (hσ.trans hpq) (hHp.trans hpqExp) hstructure n hn (hnp.trans hrqExp)
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr (hbudget p hp)), hln.trans hnm, ?_⟩
  intro T hT A D hA hD h hh E R hE hR ε μ hε hμ
  obtain ⟨hu, hv⟩ := hrelative T hT E R hE hR
  have hA' := F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hT hpqExp A.coord hA
  have hD' := F.realAdaptedCoefficientGrid_mono e ω hF (fun _ => 1) hl hln D.coord hD
  have hε' := F.firstCoefficientSlowBound_mono e ω hF (fun _ => 1) T hT hpqExp ε hε
  have hu' := F.firstCoefficientSlowBound_mono e ω hF (fun _ => 1) T hT hrqExp _ hu
  have hμ' := F.firstCoefficientGrid_mono e ω hF (fun _ => 1) hl hln μ hμ
  obtain ⟨hleft, hright⟩ := hcorrection T hT A D hA' hD' h hh ε _ μ _ hε' hu' hμ' hv
  exact ⟨F.firstCoefficientSlowBound_mono e ω hF (fun _ => 1) T hT
    (Real.exp_le_exp.mpr (hbudget p hp)) _ hleft, hright⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hF in
theorem synchronized_normalized_coefficient_common_derivative
    (h : σ → ℚ) (ε μ : ℝ ⊗[ℚ] L)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (A B D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (r : F.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (E P R P₀ : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hf : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) r).coord =
      normalizedShiftLog (s + 1) h (-ε) (-μ) (F.realAdaptedPolynomialMap (fun _ => 1) (A * B * D).coord))
    (hs : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareSndPolynomialHom (fun _ => 1) r).coord =
      F.realAdaptedPolynomialMap (fun _ => 1) (A * B * D).coord)
    (hr : F.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r = E * P * R)
    (hA : F.adaptedReducedRealSymbolHom (fun _ => 1) A = F.reducedSquareRealSymbolHom (fun _ => 1) E)
    (hB : F.adaptedReducedRealSymbolHom (fun _ => 1) B = F.reducedSquareRealSymbolHom (fun _ => 1) P)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hP₀ : P₀.coord ∈ realificationLieSubalgebra U)
    (hdiag : F.reducedSquareRealSymbolHom (fun _ => 1) P = F.reducedSquareRealSymbolHom (fun _ => 1) P₀) :
    F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (F.coefficientSlowCorrection A (fun i => (h i : ℝ)) (F.realFirstCoefficientConstant (fun _ => 1) ε)
          (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) E) +
        F.realFirstCoefficientAdjoint (fun _ => 1) B
          (F.coefficientGridCorrection D (fun i => (h i : ℝ)) (F.realFirstCoefficientConstant (fun _ => 1) μ)
            (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) R)) +
        F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) P₀) ∈
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U) := by
  apply F.synchronized_coefficient_common_derivative b ω hF h U A B D E P R P₀
    (F.realFirstCoefficientConstant (fun _ => 1) ε) (F.realFirstCoefficientConstant (fun _ => 1) μ)
    hA hB hP hP₀ hdiag
  have hderivative := F.normalized_real_square_derivative_identity b ω hF h ε μ (A * B * D) r hf hs
  rwa [hr] at hderivative

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

universe uσ uι uL

variable {σ : Type uσ} {ι : Type uι} {L : Type uL}
  [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
local notation "E₁" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "SGroup" => F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1)

def NormalizedCommonFamilySpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
        (A B D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (_hA : F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp p) A.coord)
        (_hD : F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l D.coord)
        (Hshifts : Finset (σ → ℤ))
        (r : (σ → ℤ) → F.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (E P R : (σ → ℤ) → SGroup) (P₀ : SGroup)
        (ε μ : (σ → ℤ) → ℝ ⊗[ℚ] L)
        (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
        (_hf : ∀ h ∈ Hshifts,
          F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) (r h)).coord =
            normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε h) (-μ h)
              (F.realAdaptedPolynomialMap (fun _ => 1) (A * B * D).coord))
        (_hs : ∀ h ∈ Hshifts,
          F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareSndPolynomialHom (fun _ => 1) (r h)).coord =
            F.realAdaptedPolynomialMap (fun _ => 1) (A * B * D).coord)
        (_hr : ∀ h ∈ Hshifts, F.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) (r h) =
          E h * P h * R h)
        (_hleft : ∀ h ∈ Hshifts, F.adaptedReducedRealSymbolHom (fun _ => 1) A =
          F.reducedSquareRealSymbolHom (fun _ => 1) (E h))
        (_hmiddle : ∀ h ∈ Hshifts, F.adaptedReducedRealSymbolHom (fun _ => 1) B =
          F.reducedSquareRealSymbolHom (fun _ => 1) (P h))
        (_hP : ∀ h ∈ Hshifts, (P h).coord ∈ realificationLieSubalgebra U)
        (_hP₀ : P₀.coord ∈ realificationLieSubalgebra U)
        (_hdiag : ∀ h ∈ Hshifts, F.reducedSquareRealSymbolHom (fun _ => 1) (P h) =
          F.reducedSquareRealSymbolHom (fun _ => 1) P₀)
        (_hE : ∀ h ∈ Hshifts, F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)
          (fun _ => 1) T (Real.exp p) (E h))
        (_hR : ∀ h ∈ Hshifts, F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)
          (fun _ => 1) l (R h))
        (_hε : ∀ h ∈ Hshifts, ∀ i, |(b.baseChange ℝ).repr (ε h) i| ≤ Real.exp p)
        (_hμ : ∀ h ∈ Hshifts, (fun i => (b.baseChange ℝ).repr (μ h) i) ∈ realDenominatorGrid l),
        ∃ S K : (σ → ℤ) → E₁, ∀ h ∈ Hshifts,
          (F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
            (S h + F.realFirstCoefficientAdjoint (fun _ => 1) B (K h) +
              F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) P₀) ∈ J) ∧
          F.FirstCoefficientSlowBound b ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C)) (S h) ∧
          F.FirstCoefficientGrid b ω hF (fun _ => 1) m (K h)

theorem exists_normalized_common_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
        [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
        (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1))),
        F.NormalizedCommonFamilySpec b ω hF U C := by
  obtain ⟨C, hC, hbound⟩ := exists_synchronizedSquare_bound.{uσ, uι, uL} s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF U H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨m, hm, hmp, hlm, hcorrect⟩ := hbound F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro T hT A B D hA hD Hshifts r E P R P₀ ε μ hbox hf hs hr hleft hmiddle hP hP₀ hdiag hE hR hε hμ
  let S : (σ → ℤ) → F.RealFirstCoefficientModule (fun _ : σ => 1) := fun h =>
    F.coefficientSlowCorrection A (fun i => (h i : ℝ)) (F.realFirstCoefficientConstant (fun _ => 1) (ε h))
      (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) (E h))
  let K : (σ → ℤ) → F.RealFirstCoefficientModule (fun _ : σ => 1) := fun h =>
    F.coefficientGridCorrection D (fun i => (h i : ℝ)) (F.realFirstCoefficientConstant (fun _ => 1) (μ h))
      (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) (R h))
  refine ⟨S, K, ?_⟩
  intro h hh
  have hε' := F.realFirstCoefficientConstant_slow (fun _ => 1) b ω hF T hT
    (Real.exp p) (Real.exp_nonneg _) (ε h) (hε h hh)
  have hμ' := F.realFirstCoefficientConstant_grid (fun _ : σ => 1) b ω hF l (μ h) (hμ h hh)
  have hbounds := hcorrect T hT A D hA hD h (hbox h hh) (E h) (R h) (hE h hh) (hR h hh)
    (F.realFirstCoefficientConstant (fun _ : σ => 1) (ε h))
    (F.realFirstCoefficientConstant (fun _ : σ => 1) (μ h)) hε' hμ'
  refine ⟨?_, hbounds.1, hbounds.2⟩
  have hcommon := F.synchronized_normalized_coefficient_common_derivative b ω hF
    (fun i => (h i : ℚ)) (ε h) (μ h) U A B D (r h) (E h) (P h) (R h) P₀
    (hf h hh) (hs h hh) (hr h hh) (hleft h hh) (hmiddle h hh) (hP h hh) hP₀ (hdiag h hh)
  simpa only [Rat.cast_intCast] using hcommon

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.StepOneGradedNiltestSplitting
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

theorem stepOne_vertical_character {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L 1) (Γ : Subgroup F.realification.Group)
    (η : L →ₗ[ℚ] ℚ) (f : F.realification.Group ⧸ Γ → ℂ)
    (hf : ∀ z : F.realification.Group, z ∈ F.realification.subgroup 1 → ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (g : F.realification.Group) :
    f (QuotientGroup.mk g) = character ((realifyFunctional η g.coord : ℝ) : CircleFourier.Circle) *
      f (QuotientGroup.mk (1 : F.realification.Group)) := by
  have hg : g ∈ F.realification.subgroup 1 := by rw [F.realification.subgroup_one]; trivial
  simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] using
    hf g hg (QuotientGroup.mk (1 : F.realification.Group))

namespace RationalFilteredNilmanifold

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L 1 d)

omit [DecidableEq σ] in
theorem stepOne_niltest_eval_affine (P : D.Niltest (fun _ : σ => 1)) (η : L →ₗ[ℚ] ℚ)
    (hP : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup 1 → ∀ x,
      P.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * P.observable x)
    (x : σ → ℤ) :
    P.eval x = P.observable (QuotientGroup.mk (1 : D.RealGroup)) *
      character (((realifyFunctional η (coefficients P.orbit.log 0) +
        ∑ i, (x i : ℝ) * realifyFunctional η (coefficients P.orbit.log (Finsupp.single i 1))) : ℝ) :
          CircleFourier.Circle) := by
  rw [Niltest.eval, ← D.filtration.realification.polynomialOrbitRealEval_integer]
  rw [stepOne_vertical_character D.filtration D.realLattice η P.observable hP,
    D.filtration.realification.polynomialOrbitRealEval_coord,
    eval₂_affine_of_degreeLE_one P.orbit.log P.orbit.degreeLE]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  rw [mul_comm]

theorem stepOne_niltest_linear_phase_bias (P : D.Niltest (fun _ : σ => 1)) (η : L →ₗ[ℚ] ℚ)
    (hP : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup 1 → ∀ x,
      P.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * P.observable x)
    (T : σ → ℕ) {M δ : ℝ} (hM : 0 < M)
    (hbound : (P.normBound : ℝ) ≤ M) (hbias : δ ≤ ‖𝔼 x ∈ integerBox T, P.eval x‖) :
    δ / M ≤ ‖linearPhaseMean T (fun i =>
      (realifyFunctional η (coefficients P.orbit.log (Finsupp.single i 1)) : CircleFourier.Circle))‖ := by
  apply linearPhaseMean_norm_ge_of_affine_bias T
    (P.observable (QuotientGroup.mk (1 : D.RealGroup)))
    (realifyFunctional η (coefficients P.orbit.log 0) : CircleFourier.Circle) _ hM
    ((P.norm_le _).trans hbound)
  rw [integerBox_expect_eq_fin] at hbias
  convert hbias using 2
  apply Finset.expect_congr rfl
  intro t _
  rw [D.stepOne_niltest_eval_affine P η hP]
  congr 2
  have hcoe (f : σ → ℝ) : ((∑ i, f i : ℝ) : CircleFourier.Circle) = ∑ i, (f i : CircleFourier.Circle) :=
    map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f Finset.univ
  simp only [Int.cast_natCast, AddCircle.coe_add, hcoe, ← nsmul_eq_mul, AddCircle.coe_nsmul]

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L 1 d)

theorem exists_stepOne_niltest_splitting (P : D.Niltest (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) {p : ℝ} (hp : 0 ≤ p) (hP : P.ComplexityLE p)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hvertical : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup 1 → ∀ x,
      P.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * P.observable x)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i)
    (hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ integerBox T, P.eval x‖) :
    ∃ (m : ℕ) (E Q R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
      (v : Fin d → L),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧
      D.filtration.realification.polynomialSymbolHom (fun _ => 1) (E * Q * R) =
        D.filtration.realification.polynomialSymbolHom (fun _ => 1) ⟨⟨P.orbit.log, P.orbit.property⟩⟩ ∧
      D.filtration.PolynomialSlowBound D.basis (fun _ => 1) (fun i => (T i : ℝ))
        (Real.exp ((p + 2) ^ 4)) E ∧
      D.filtration.PolynomialRationalGrid D.basis (fun _ => 1) m R ∧
      Submodule.span ℚ (Set.range v) = (D.filtration.stepOneFrequencyKernel η).toSubmodule ∧
      (∀ i j, rationalLogHeight (D.basis.repr (v i) j) ≤ (p + 2) ^ 4) ∧
      (∀ t : σ → ℝ, eval₂ t (Q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
        realificationLieSubalgebra (D.filtration.stepOneFrequencyKernel η)) ∧
      coefficients (Q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hheight : ∀ i, RationalHeightLE (η (D.basis i)) H :=
    fun i => rationalHeightLE_ceil_exp (hηheight i)
  have hnorm : (P.normBound : ℝ) ≤ Real.exp p := by
    have h := P.observable_budget hP
    have hl := P.lipBound.coe_nonneg
    linarith
  have hphase := D.stepOne_niltest_linear_phase_bias P η hvertical T (Real.exp_pos p) hnorm hbias
  obtain ⟨m, E, Q, R, hm, hmH, hsum, he, hr, hq, hq0⟩ :=
    D.filtration.exists_stepOne_linear_splitting D.basis η hH hheight T hT
      (fun i => coefficients P.orbit.log (Finsupp.single i 1))
      (div_pos (Real.exp_pos (-p)) (Real.exp_pos p)) hphase
  obtain ⟨v, hvspan, hvheight⟩ := exists_bounded_frequency_kernel_spanning D.basis η hH hheight
  refine ⟨m, E, Q, R, v, hm, (Nat.cast_le.mpr hmH).trans (stepOne_denominator_budget hp), ?_, ?_, hr,
    hvspan, ?_, hq, hq0⟩
  · rw [hsum]
    apply NilpotentLieBCHGroup.ext
    exact D.filtration.realification.stepOne_symbol_linearPart ⟨P.orbit.log, P.orbit.property⟩
  · exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) (fun i => (T i : ℝ))
      (fun i => Nat.cast_pos.mpr (hT i)) (stepOne_slow_budget hp) E he
  · intro i j
    exact rationalLogHeight_le_of_height
      (hvheight i j) (stepOne_kernel_height_budget hp)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L 1 d)

theorem exists_stepOne_graded_niltest_splitting
    (ω : Fin d → ℕ)
    (hlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (P : D.Niltest (fun _ : σ => 1)) (η : L →ₗ[ℚ] ℚ)
    {p : ℝ} (hp : 0 ≤ p) (hP : P.ComplexityLE p)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hvertical : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup 1 → ∀ x,
      P.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * P.observable x)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i)
    (hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ integerBox T, P.eval x‖) :
    ∃ (m : ℕ) (E Q R : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (v : Fin d → D.filtration.AssociatedGraded),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧
      E * Q * R = D.filtration.realPolynomialSymbolHom D.basis ω hlayers (fun _ => 1)
        ⟨⟨P.orbit.log, P.orbit.property⟩⟩ ∧
      D.filtration.SymbolSlowBound D.basis ω hlayers (fun _ => 1) (fun i => (T i : ℝ))
        (Real.exp ((p + 2) ^ 4)) E ∧
      D.filtration.SymbolRationalGrid D.basis ω hlayers (fun _ => 1) m R ∧
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hlayers) ω W.toSubmodule ∧
      (∀ i j, rationalLogHeight
        ((D.filtration.associatedGradedBasis D.basis ω hlayers).repr (v i) j) ≤ (p + 2) ^ 4) ∧
      (∀ x ∈ W, D.filtration.stepOneGradedFrequency D.basis ω hlayers η x = 0) ∧
      (∀ t : σ → ℝ, eval₂ t
        (D.filtration.realGradedSymbolPolynomial D.basis ω hlayers (fun _ => 1) Q.coord) ∈
          realificationLieSubalgebra W) := by
  obtain ⟨m, E, Q, R, v, hm, hmbound, hsymbol, he, hr, hvspan, hvheight, hq, _⟩ :=
    D.exists_stepOne_niltest_splitting P η hp hP hηheight hvertical T hT hbias
  refine ⟨m,
    D.filtration.realPolynomialSymbolHom D.basis ω hlayers (fun _ => 1) E,
    D.filtration.realPolynomialSymbolHom D.basis ω hlayers (fun _ => 1) Q,
    D.filtration.realPolynomialSymbolHom D.basis ω hlayers (fun _ => 1) R,
    D.filtration.stepOneGradedKernel D.basis ω hlayers η,
    (fun i => D.filtration.stepOneGradedEquiv D.basis ω hlayers (v i)),
    hm, hmbound, ?_,
    D.filtration.polynomialSlowBound_symbol D.basis ω hlayers (fun _ => 1) _ _ E he,
    D.filtration.polynomialRationalGrid_symbol D.basis ω hlayers (fun _ => 1) m R hr,
    D.filtration.stepOneGradedKernel_span D.basis ω hlayers η v hvspan,
    D.filtration.stepOne_graded_submodule D.basis ω hlayers _, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul]
    exact D.filtration.realPolynomialSymbolHom_eq_of_quotient_eq D.basis ω hlayers
      (fun _ => 1) _ _ hsymbol
  · intro i j
    rw [D.filtration.stepOneGradedEquiv_coordinate]
    exact hvheight i j
  · intro x hx
    exact (D.filtration.mem_stepOneGradedKernel D.basis ω hlayers η x).mp hx
  · exact D.filtration.stepOne_symbol_values_in_gradedKernel D.basis ω hlayers η
      (fun _ => 1) (Q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) hq

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShiftStructure
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem pderiv_commute (i j : σ) (p : VectorPolynomial σ ℚ L) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor L
        ((MvPolynomial.pderiv j).toLinearMap.rTensor L p) =
      (MvPolynomial.pderiv j).toLinearMap.rTensor L
        ((MvPolynomial.pderiv i).toLinearMap.rTensor L p) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  apply coefficients.injective
  ext α
  simp only [coefficients_pderiv, Finsupp.add_apply,
    Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne (Ne.symm hij),
    Nat.add_zero, smul_smul]
  congr 1
  · ring
  · congr 1
    abel

theorem directionalDerivative_commute [Fintype σ]
    (h k : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalDerivative h (directionalDerivative k p) =
      directionalDerivative k (directionalDerivative h p) := by
  simp only [directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [pderiv_commute, mul_comm]

noncomputable def directionalLieDerivation [Fintype σ] (h : σ → ℚ) :
    LieDerivation ℚ (VectorPolynomial σ ℚ L) (VectorPolynomial σ ℚ L) where
  toLinearMap := directionalDerivative h
  leibniz' p q := by
    rw [directionalDerivative_lie, sub_eq_add_neg, ← lie_skew]
    exact add_comm _ _

@[simp] theorem directionalLieDerivation_apply [Fintype σ]
    (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalLieDerivation h p = directionalDerivative h p := rfl

noncomputable def directionalDerivationLinear [Fintype σ] :
    (σ → ℚ) →ₗ[ℚ] LieDerivation ℚ (VectorPolynomial σ ℚ L) (VectorPolynomial σ ℚ L) where
  toFun := directionalLieDerivation
  map_add' h k := by
    apply LieDerivation.ext
    intro p
    exact directionalDerivative_direction_add h k p
  map_smul' r h := by
    apply LieDerivation.ext
    intro p
    exact directionalDerivative_direction_smul r h p

@[simp] theorem directionalDerivationLinear_apply [Fintype σ]
    (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalDerivationLinear h p = directionalDerivative h p := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedShiftDerivation (h : σ → ℚ) :
    LieDerivation ℚ (F.adaptedLieSubalgebra (fun _ : σ => 1))
      (F.adaptedLieSubalgebra (fun _ : σ => 1)) where
  toLinearMap := F.adaptedDirectionalDerivative h
  leibniz' p q := by
    rw [F.adaptedDirectionalDerivative_lie, sub_eq_add_neg, ← lie_skew]
    exact add_comm _ _

@[simp] theorem adaptedShiftDerivation_coe (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (F.adaptedShiftDerivation h p : VectorPolynomial σ ℚ L) =
      directionalDerivative h p.val := rfl

noncomputable def adaptedShiftDerivationLinear :
    (σ → ℚ) →ₗ[ℚ] LieDerivation ℚ (F.adaptedLieSubalgebra (fun _ : σ => 1))
      (F.adaptedLieSubalgebra (fun _ : σ => 1)) where
  toFun := F.adaptedShiftDerivation
  map_add' h k := by
    apply LieDerivation.ext
    intro p
    apply Subtype.ext
    exact directionalDerivative_direction_add h k p.val
  map_smul' r h := by
    apply LieDerivation.ext
    intro p
    apply Subtype.ext
    exact directionalDerivative_direction_smul r h p.val

theorem adaptedShiftDerivation_commute (h k : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.adaptedShiftDerivation h (F.adaptedShiftDerivation k p) =
      F.adaptedShiftDerivation k (F.adaptedShiftDerivation h p) := by
  apply Subtype.ext
  exact directionalDerivative_commute h k p.val

omit [Fintype σ] in
noncomputable def adaptedShiftAction (d : ℕ) :
    RationalTorus.Algebra d →ₗ⁅ℚ⁆
      LieDerivation ℚ (F.adaptedLieSubalgebra (fun _ : Fin d => 1))
        (F.adaptedLieSubalgebra (fun _ : Fin d => 1)) where
  toLinearMap := F.adaptedShiftDerivationLinear
  map_lie' {h k} := by
    apply LieDerivation.ext
    intro p
    rw [RationalTorus.lie_eq_zero]
    change (F.adaptedShiftDerivationLinear (0 : Fin d → ℚ)) p = _
    rw [map_zero, LieDerivation.zero_apply, LieDerivation.lie_apply]
    exact (sub_eq_zero.mpr (F.adaptedShiftDerivation_commute h k p)).symm

omit [Fintype σ] in
@[simp] theorem adaptedShiftAction_coe (d : ℕ) (h : RationalTorus.Algebra d)
    (p : F.adaptedLieSubalgebra (fun _ : Fin d => 1)) :
    (F.adaptedShiftAction d h p : VectorPolynomial (Fin d) ℚ L) =
      directionalDerivative h p.val := rfl

omit [Fintype σ] in

abbrev PolynomialShiftAlgebra (d : ℕ) :=
  LieAlgebra.SemiDirectSum (F.adaptedLieSubalgebra (fun _ : Fin d => 1))
    (RationalTorus.Algebra d) (F.adaptedShiftAction d)

omit [Fintype σ] in
theorem polynomialShift_bracket (d : ℕ) (x y : F.PolynomialShiftAlgebra d) :
    ⁅x, y⁆ = ⟨⁅x.left, y.left⁆ + F.adaptedDirectionalDerivative x.right y.left -
      F.adaptedDirectionalDerivative y.right x.left, 0⟩ := rfl

omit [Fintype σ] in
theorem polynomialShift_direction_bracket (d : ℕ) (h : RationalTorus.Algebra d)
    (p : F.adaptedLieSubalgebra (fun _ : Fin d => 1)) :
    ⁅(⟨0, h⟩ : F.PolynomialShiftAlgebra d), (⟨p, 0⟩ : F.PolynomialShiftAlgebra d)⁆ =
      ⟨F.adaptedDirectionalDerivative h p, 0⟩ := by
  rw [F.polynomialShift_bracket]
  simp only [zero_lie, zero_add, map_zero, sub_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s)

include b hF hω in
theorem polynomialShift_finiteDimensional (d : ℕ) :
    FiniteDimensional ℚ (F.PolynomialShiftAlgebra d) := by
  let w : Fin d → ℕ := fun _ => 1
  let : Finite (AdaptedBasisIndex w ω) := adaptedBasisIndex_finite w ω s (by simp [w]) hω
  let : FiniteDimensional ℚ (F.adaptedLieSubalgebra w) :=
    (F.adaptedMonomialBasis b ω hF w).finiteDimensional_of_finite
  let : FiniteDimensional ℚ (RationalTorus.Algebra d) :=
    (RationalTorus.basis d).finiteDimensional_of_finite
  exact FiniteDimensional.of_injective
    (LieAlgebra.SemiDirectSum.toProdl (F.adaptedShiftAction d)).toLinearMap
    (LieAlgebra.SemiDirectSum.toProdl (F.adaptedShiftAction d)).injective

include b hF hω in
theorem polynomialShift_finrank_le (d : ℕ) :
    finrank ℚ (F.PolynomialShiftAlgebra d) ≤
      Fintype.card ι * (s + 1) * (d + 1) ^ s + d := by
  let w : Fin d → ℕ := fun _ => 1
  let : Fintype (AdaptedBasisIndex w ω) :=
    adaptedBasisIndexFintype w ω s (by simp [w]) hω
  let : FiniteDimensional ℚ (F.adaptedLieSubalgebra w) :=
    (F.adaptedMonomialBasis b ω hF w).finiteDimensional_of_finite
  let : FiniteDimensional ℚ (RationalTorus.Algebra d) :=
    (RationalTorus.basis d).finiteDimensional_of_finite
  rw [(LieAlgebra.SemiDirectSum.toProdl (F.adaptedShiftAction d)).finrank_eq,
    Module.finrank_prod, finrank_eq_card_basis (F.adaptedMonomialBasis b ω hF w),
    finrank_eq_card_basis (RationalTorus.basis d), Fintype.card_fin]
  exact Nat.add_le_add_right
    (by simpa only [Fintype.card_fin] using adaptedBasisIndex_card_le w ω s (by simp [w]) hω) d

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def polynomialShiftBasis (t : ℕ) :
    Basis (AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) ℚ (F.PolynomialShiftAlgebra t) :=
  ((F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).prod (RationalTorus.basis t)).map
    (LieAlgebra.SemiDirectSum.toProdl (F.adaptedShiftAction t)).symm

theorem polynomialShiftBasis_repr_inl (t : ℕ) (x : F.PolynomialShiftAlgebra t)
    (z : AdaptedBasisIndex (fun _ : Fin t => 1) ω) :
    (F.polynomialShiftBasis b ω hF t).repr x (.inl z) =
      b.repr (coefficients x.left.val z.val.1) z.val.2 := by
  change (F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).repr x.left z = _
  exact F.adaptedMonomialBasis_repr b ω hF (fun _ : Fin t => 1) x.left z

theorem polynomialShiftBasis_repr_inr (t : ℕ) (x : F.PolynomialShiftAlgebra t) (i : Fin t) :
    (F.polynomialShiftBasis b ω hF t).repr x (.inr i) = x.right i := by
  change (RationalTorus.basis t).repr x.right i = x.right i
  rfl

theorem polynomialShiftBasis_inl_left (t : ℕ)
    (z : AdaptedBasisIndex (fun _ : Fin t => 1) ω) :
    ((F.polynomialShiftBasis b ω hF t) (.inl z)).left =
      F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1) z := by
  change (((F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).prod
    (RationalTorus.basis t)) (.inl z)).1 = _
  exact Basis.prod_apply_inl_fst _ _ z

theorem polynomialShiftBasis_inl_right (t : ℕ)
    (z : AdaptedBasisIndex (fun _ : Fin t => 1) ω) :
    ((F.polynomialShiftBasis b ω hF t) (.inl z)).right = 0 := by
  change (((F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).prod
    (RationalTorus.basis t)) (.inl z)).2 = _
  exact Basis.prod_apply_inl_snd _ _ z

theorem polynomialShiftBasis_inr_left (t : ℕ) (i : Fin t) :
    ((F.polynomialShiftBasis b ω hF t) (.inr i)).left = 0 := by
  change (((F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).prod
    (RationalTorus.basis t)) (.inr i)).1 = _
  exact Basis.prod_apply_inr_fst _ _ i

theorem polynomialShiftBasis_inr_right (t : ℕ) (i : Fin t) :
    ((F.polynomialShiftBasis b ω hF t) (.inr i)).right = RationalTorus.basis t i := by
  change (((F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).prod
    (RationalTorus.basis t)) (.inr i)).2 = _
  exact Basis.prod_apply_inr_snd _ _ i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

namespace VectorPolynomial

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem coefficients_torusDerivative {t : ℕ} (i : Fin t)
    (p : VectorPolynomial (Fin t) ℚ L) (α : Fin t →₀ ℕ) :
    coefficients (directionalDerivative (RationalTorus.basis t i) p) α =
      (α i + 1 : ℚ) • coefficients p (α + Finsupp.single i 1) := by
  have hdir (j : Fin t) : (RationalTorus.basis t i) j = if i = j then 1 else 0 := by
    rw [← RationalTorus.basis_repr t (RationalTorus.basis t i) j,
      (RationalTorus.basis t).repr_self, Finsupp.single_apply]
  change coefficients (directionalDerivative (fun j : Fin t => (RationalTorus.basis t i) j) p) α = _
  rw [coefficients_directionalDerivative]
  simp_rw [hdir]
  simp

theorem torusDerivative_monomial_height {ι : Type*} (b : Basis ι ℚ L)
    {s t : ℕ} (β : Fin t →₀ ℕ) (hβ : Finsupp.weight (fun _ : Fin t => 1) β ≤ s)
    (i : Fin t) (j : ι) (α : Fin t →₀ ℕ) (k : ι) :
    RationalHeightLE (b.repr (coefficients
      (directionalDerivative (RationalTorus.basis t i) (monomial (R := ℚ) β (b j))) α) k) (s + 1) := by
  classical
  rw [coefficients_torusDerivative, coefficients_monomial]
  by_cases he : β = α + Finsupp.single i 1
  · rw [he, Finsupp.single_eq_same, map_smul, Finsupp.smul_apply, b.repr_self]
    have hi := (Finsupp.le_weight (fun _ : Fin t => 1) (s := i) (by norm_num) β).trans hβ
    rw [he, Finsupp.add_apply, Finsupp.single_eq_same] at hi
    have hn : RationalHeightLE ((α i + 1 : ℕ) : ℚ) (s + 1) := by
      constructor
      · simpa only [Rat.num_natCast, Int.natAbs_natCast] using hi.trans (Nat.le_succ s)
      · simp only [Rat.den_natCast]
        omega
    by_cases hj : j = k
    · subst k
      simpa only [Finsupp.single_eq_same, smul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one] using hn
    · rw [Finsupp.single_eq_of_ne (Ne.symm hj), smul_zero]
      exact rationalHeightLE_zero (by omega)
  · rw [Finsupp.single_eq_of_ne (Ne.symm he), smul_zero, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (by omega)

end VectorPolynomial

namespace NilpotentLieFiltration

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem polynomialShiftBasis_inl (t : ℕ) (i : AdaptedBasisIndex (fun _ : Fin t => 1) ω) :
    F.polynomialShiftBasis b ω hF t (.inl i) =
      LieAlgebra.SemiDirectSum.inl (F.adaptedShiftAction t)
        (F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1) i) := by
  apply LieAlgebra.SemiDirectSum.ext
  · exact F.polynomialShiftBasis_inl_left b ω hF t i
  · exact F.polynomialShiftBasis_inl_right b ω hF t i

theorem polynomialShiftBasis_inr (t : ℕ) (i : Fin t) :
    F.polynomialShiftBasis b ω hF t (.inr i) =
      LieAlgebra.SemiDirectSum.inr (F.adaptedShiftAction t) (RationalTorus.basis t i) := by
  apply LieAlgebra.SemiDirectSum.ext
  · exact F.polynomialShiftBasis_inr_left b ω hF t i
  · exact F.polynomialShiftBasis_inr_right b ω hF t i

theorem polynomialShiftBasis_mixed_height (hω : ∀ i, ω i ≤ s) (t : ℕ) (i : Fin t)
    (j : AdaptedBasisIndex (fun _ : Fin t => 1) ω)
    (k : AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) :
    RationalHeightLE ((F.polynomialShiftBasis b ω hF t).repr
      ⁅F.polynomialShiftBasis b ω hF t (.inr i), F.polynomialShiftBasis b ω hF t (.inl j)⁆ k) (s + 1) := by
  rw [F.polynomialShiftBasis_inr, F.polynomialShiftBasis_inl]
  rw [LieAlgebra.SemiDirectSum.inr_eq_mk, LieAlgebra.SemiDirectSum.inl_eq_mk,
    F.polynomialShift_direction_bracket]
  rcases k with k | k
  · rw [F.polynomialShiftBasis_repr_inl]
    change RationalHeightLE (b.repr (coefficients
      (directionalDerivative (RationalTorus.basis t i)
        (F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1) j).val) k.val.1) k.val.2) _
    rw [F.adaptedMonomialBasis_coe]
    exact torusDerivative_monomial_height b j.val.1 (j.property.trans (hω j.val.2)) i j.val.2 k.val.1 k.val.2
  · rw [F.polynomialShiftBasis_repr_inr]
    exact rationalHeightLE_zero (by omega)

theorem polynomialShiftBasis_structure_height (hω : ∀ i, ω i ≤ s) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) (t : ℕ)
    (i j k : AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) :
    RationalHeightLE (lieStructureConstants (F.polynomialShiftBasis b ω hF t) i j k) (max H (s + 1)) := by
  change RationalHeightLE ((F.polynomialShiftBasis b ω hF t).repr
    ⁅F.polynomialShiftBasis b ω hF t i, F.polynomialShiftBasis b ω hF t j⁆ k) _
  rcases i with i | i <;> rcases j with j | j
  · rw [F.polynomialShiftBasis_inl, F.polynomialShiftBasis_inl,
      ← (LieAlgebra.SemiDirectSum.inl (F.adaptedShiftAction t)).map_lie]
    rcases k with k | k
    · rw [F.polynomialShiftBasis_repr_inl]
      simp only [LieAlgebra.SemiDirectSum.inl_eq_mk]
      simpa only [F.adaptedMonomialBasis_repr] using
        (F.adaptedMonomialBasis_bracket_height b ω hF (fun _ : Fin t => 1) hH hc i j k).mono
          (Nat.le_max_left H (s + 1))
    · rw [F.polynomialShiftBasis_repr_inr]
      exact rationalHeightLE_zero (hH.trans (Nat.le_max_left _ _))
  · rw [← lie_skew, map_neg, Finsupp.neg_apply]
    exact ((F.polynomialShiftBasis_mixed_height b ω hF hω t j i k).mono (Nat.le_max_right _ _)).neg
  · exact (F.polynomialShiftBasis_mixed_height b ω hF hω t i j k).mono (Nat.le_max_right _ _)
  · rw [F.polynomialShiftBasis_inr, F.polynomialShiftBasis_inr,
      ← (LieAlgebra.SemiDirectSum.inr (F.adaptedShiftAction t)).map_lie,
      RationalTorus.lie_eq_zero, map_zero, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (hH.trans (Nat.le_max_left _ _))

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CanonicalReducedMajorTwistedNiltest
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped NNReal TensorProduct

variable {U : Type*} {m : ℕ}

theorem majorZeroParameterSlice_eq (D : MvPolynomial (U ⊕ Fin m) ℝ) :
    specializeMajorParameters (RingHom.id ℝ) D 0 =
      aeval (Sum.elim (fun _ : U => (0 : MvPolynomial (Fin m) ℝ)) X) D := by
  simp only [specializeMajorParameters, RingHom.comp_id, Pi.zero_apply, map_zero]
  rfl

theorem majorZeroParameterSlice_mass (D : MvPolynomial (U ⊕ Fin m) ℝ) :
    realPolynomialMass (specializeMajorParameters (RingHom.id ℝ) D 0) ≤
      realPolynomialMass D := by
  rw [majorZeroParameterSlice_eq]
  exact realPolynomialMass_zeroParameterEval_le D

theorem majorZeroParameterSlice_degree (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
    {d : ℕ} {D : MvPolynomial (U ⊕ Fin m) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    (specializeMajorParameters (RingHom.id ℝ) D 0).totalDegree ≤ d := by
  rw [majorZeroParameterSlice_eq]
  apply totalDegree_le_of_positive_weightedSupport w hw
  apply weightedSupportLE_aeval _ _ _ _ hD
  intro i
  cases i with
  | inl i => exact Submodule.zero_mem _
  | inr i => exact weightedSupportLE_X w i

variable (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem exists_majorTranslation_buffered_niltest (hd : 0 < d)
    (Ψ : PatchKernel m) (D : MvPolynomial (U ⊕ Fin m) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (M : ℝ≥0) (hM : realPolynomialMass D ≤ M) :
    ∃ F : (weightedTranslationNilmanifold w d hw hwd).Niltest (fun _ : U => 1),
      F.normBound = 1 ∧ F.lipBound = 2 * bufferedTranslationTermLip w d Ψ M ∧
      F.orbit = majorTranslationPolynomialOrbit w d hw hwd D hD A hA ∧
      (∀ u : U → ℝ, ∀ β : Fin m → ℤ,
        (∀ i, |eval u (A i) - (β i : ℝ)| ≤ 1 / 2) →
        F.evalReal u = (Ψ.value (fun i => eval u (A i) - (β i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (Sum.elim u (fun i => (β i : ℝ))) D) : ℂ)) ∧
      (∀ u : U → ℝ, ‖F.evalReal u‖ ≤ 1) := by
  let q := majorTranslationPolynomialOrbit w d hw hwd D hD A hA
  have hq := majorTranslationPolynomialOrbit_realEval w d hw hwd D hD A hA
  let D₀ := specializeMajorParameters (RingHom.id ℝ) D 0
  have hdegree : D₀.totalDegree ≤ d := majorZeroParameterSlice_degree w hw hD
  have hmass : realPolynomialMass D₀ ≤ M := (majorZeroParameterSlice_mass D).trans hM
  let F := weightedTranslationBufferedNiltest w d hw hwd (fun _ : U => 1)
    hd Ψ D₀ M hdegree hmass q
  refine ⟨F, rfl, rfl, rfl, ?_, ?_⟩
  · intro u β hβ
    change bufferedTranslationPhase Ψ D₀
      (bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
          (fun _ : U => 1) u q)) = _
    rw [hq u]
    exact bufferedTranslationPhase_majorSymbol Ψ D D₀ A u β hβ
  · intro u
    exact weightedTranslationBufferedObservable_norm_le_one w d hw hwd Ψ D₀ _

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem fractionalCoefficientPolynomial_mem_weightedSupportLE {σ : Type*}
    (D : MvPolynomial σ ℝ) (w : σ → ℕ) (d : ℕ)
    (hD : D ∈ weightedSupportLE w d) :
    fractionalCoefficientPolynomial D ∈ weightedSupportLE w d := by
  intro a ha
  apply hD
  apply mem_support_iff.mpr
  intro hz
  change D.coeff a = 0 at hz
  have hcoeff := mem_support_iff.mp ha
  apply hcoeff
  change (fractionalCoefficientPolynomial D).coeff a = 0
  simp only [fractionalCoefficientPolynomial_coeff, hz, Int.fract_zero]

theorem fractionalCoefficientPolynomial_mass_le_of_weightedSupportLE
    {σ : Type*} [Fintype σ] (D : MvPolynomial σ ℝ)
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ)
    (hD : D ∈ weightedSupportLE w d) :
    realPolynomialMass (fractionalCoefficientPolynomial D) ≤
      ((Fintype.card σ : ℝ) + 1) ^ d := by
  refine (fractionalCoefficientPolynomial_mass_le_card D).trans ?_
  have hcard := boundedExponentSet_card_le (fractionalCoefficientPolynomial D).support d
    (fun a ha => (exponentSum_le_positive_weight w hw a).trans
      (fractionalCoefficientPolynomial_mem_weightedSupportLE D w d hD ha))
  exact_mod_cast hcard

end Erdos3

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped NNReal TensorProduct

theorem exists_majorTranslation_degree_reduced_niltest (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U : Type*} [Fintype U] {m : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      (_hd : 0 < d) (Ψ : PatchKernel m) (D : MvPolynomial (U ⊕ Fin m) ℝ)
      (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      {p : ℝ} (_hp : 0 ≤ p) (_hdim : (Fintype.card U + m : ℕ) ≤ p)
      (_hΨ : (Ψ.lip : ℝ) ≤ Real.exp p),
      ∃ F : (weightedTranslationNilmanifold w d hw hwd).Niltest (fun _ : U => 1),
        F.normBound = 1 ∧ F.ComplexityLE ((p + C) ^ C) ∧
        F.orbit = majorTranslationPolynomialOrbit w d hw hwd
          (fractionalCoefficientPolynomial D)
          (fractionalCoefficientPolynomial_mem_weightedSupportLE D
            (Sum.elim (fun _ : U => 1) w) d hD) A hA ∧
        ∀ u : U → ℤ, ∀ β : Fin m → ℤ,
          (∀ i, |eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)| ≤ 1 / 2) →
          F.eval u =
            (Ψ.value (fun i => eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)) : ℂ) *
              (Real.fourierChar (eval (fun j => ((Sum.elim u β j : ℤ) : ℝ)) D) : ℂ) := by
  obtain ⟨a, ha, hbudget⟩ := exists_weightedTranslationBuffered_budget d
  let X : Polynomial ℕ := Polynomial.X
  let Q := (Polynomial.C (d + 1) * (X + 1) + Polynomial.C a) ^ a + 4
  obtain ⟨C, hC, hCbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro U _ m w hw hwd _ _ _ _ _ hd Ψ D hD A hA p hp hdim hΨ
  let v : U ⊕ Fin m → ℕ := Sum.elim (fun _ : U => 1) w
  have hv : ∀ i, 0 < v i := by intro i; cases i with
    | inl i => exact Nat.zero_lt_one
    | inr i => exact hw i
  let Dred := fractionalCoefficientPolynomial D
  have hDred : Dred ∈ weightedSupportLE v d :=
    fractionalCoefficientPolynomial_mem_weightedSupportLE D v d hD
  let M : ℝ≥0 := ((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d
  have hmass : realPolynomialMass Dred ≤ M := by
    change realPolynomialMass Dred ≤ (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d)
    have hh := fractionalCoefficientPolynomial_mass_le_of_weightedSupportLE D v hv d hD
    simpa only [Dred,
      Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hh
  obtain ⟨F, hnorm, hlip, horbit, heval, _⟩ := exists_majorTranslation_buffered_niltest
    w d hw hwd hd Ψ Dred hDred A hA M hmass
  let q : ℝ := (d + 1 : ℕ) * (p + 1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    dsimp [q]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hm : (m : ℝ) ≤ q := by
    have hh : (m : ℝ) ≤ (Fintype.card U + m : ℕ) := by exact_mod_cast Nat.le_add_left m (Fintype.card U)
    exact hh.trans (hdim.trans hpq)
  have hM : (M : ℝ) ≤ Real.exp q := by
    have hb : ((Fintype.card U + m + 1 : ℕ) : ℝ) ≤ Real.exp (p + 1) := by
      push_cast at hdim ⊢
      linarith [Real.add_one_le_exp (p + 1)]
    calc
      (M : ℝ) ≤ (Real.exp (p + 1)) ^ d := by
        change (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d) ≤ _
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hb d
      _ = Real.exp ((d : ℝ) * (p + 1)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp q := by apply Real.exp_le_exp.mpr; dsimp [q]; push_cast; nlinarith
  obtain ⟨hgeometry, hlipBudget⟩ := hbudget w hw hwd Ψ M q hq hm
    (hΨ.trans (Real.exp_le_exp.mpr hpq)) hM
  have hcost : (q + a) ^ a + 4 ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hCbudget p hp
  have hlog : Real.log (3 + (F.lipBound : ℝ)) ≤ (q + a) ^ a + 4 := by
    have hnonneg : 0 ≤ (q + a) ^ a := by positivity
    have hh := add_le_exp_add_one (by norm_num : (0 : ℝ) ≤ 3) hnonneg
      (show (3 : ℝ) ≤ Real.exp 3 by linarith [Real.add_one_le_exp (3 : ℝ)])
      (show (F.lipBound : ℝ) ≤ Real.exp ((q + a) ^ a) by rw [hlip]; exact hlipBudget)
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    convert hh using 1
    congr 1
    ring
  refine ⟨F, hnorm, ⟨RationalFilteredNilmanifold.GeometryComplexityLE.mono _
    hgeometry (by linarith), ?_⟩, horbit, ?_⟩
  · simpa only [hnorm, NNReal.coe_one, show (2 : ℝ) + 1 = 3 by norm_num]
      using hlog.trans hcost
  · intro u β hβ
    rw [← F.evalReal_integer u, heval _ β hβ]
    have hcast : Sum.elim (fun j => (u j : ℝ)) (fun i => (β i : ℝ)) =
        (fun j => ((Sum.elim u β j : ℤ) : ℝ)) := by
      funext j
      cases j <;> rfl
    rw [hcast]
    congr 1
    exact congrArg (fun z : Circle => (z : ℂ))
      (fractionalCoefficientPolynomial_fourierChar D (Sum.elim u β))

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped NNReal TensorProduct

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped NNReal TensorProduct

section Construction

variable {U : Type*} {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

end Construction

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped NNReal TensorProduct

section Construction

variable {U : Type*} [Fintype U] {m : ℕ}

omit [Fintype U] in
theorem fractionalMajorPolynomial_support (w : Fin m → ℕ) (d : ℕ)
    (D : MvPolynomial (U ⊕ Fin m) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d) :
    fractionalCoefficientPolynomial D ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
  fun _ hα => (fractionalCoefficientPolynomial_isWeightedHomogeneous D
    (Sum.elim (fun _ : U => 1) w) d hD (mem_support_iff.mp hα)).le

theorem fractionalMajorPolynomial_mass (w : Fin m → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (D : MvPolynomial (U ⊕ Fin m) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d) :
    realPolynomialMass (fractionalCoefficientPolynomial D) ≤
      ((((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d : ℝ≥0) : ℝ) := by
  change realPolynomialMass (fractionalCoefficientPolynomial D) ≤
    (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d)
  have hv : ∀ i, 0 < Sum.elim (fun _ : U => 1) w i := by
    intro i
    cases i with
    | inl i => exact Nat.zero_lt_one
    | inr i => exact hw i
  simpa only [Fintype.card_sum, Fintype.card_fin, NNReal.coe_pow,
    NNReal.coe_natCast, Nat.cast_add, Nat.cast_one] using
    fractionalCoefficientPolynomial_mass_le D (Sum.elim (fun _ : U => 1) w) hv d hD

variable (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

noncomputable def reducedMajorTranslationTwistedNiltest (hd : 0 < d)
    (M : ℕ) (hM : 0 < M) (Ψ : PatchKernel m)
    (D : MvPolynomial (U ⊕ Fin m) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r)) :
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).Niltest (fun _ : U => 1) :=
  weightedTranslationTwistedNiltest w d hw hwd M hM (fun _ : U => 1) hd Ψ
    (specializeMajorParameters (RingHom.id ℝ) (fractionalCoefficientPolynomial D) 0)
    (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K
    (majorZeroParameterSlice_degree w hw (fractionalMajorPolynomial_support w d D hD))
    ((majorZeroParameterSlice_mass (fractionalCoefficientPolynomial D)).trans
      (fractionalMajorPolynomial_mass w d hw D hD)) T hT hLip
    (majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial D)
      (fractionalMajorPolynomial_support w d D hD) A hA)

variable (hd : 0 < d) (M : ℕ) (hM : 0 < M) (Ψ : PatchKernel m)
    (D : MvPolynomial (U ⊕ Fin m) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))

@[simp] theorem reducedMajorTranslationTwistedNiltest_normBound :
    (reducedMajorTranslationTwistedNiltest w d hw hwd hd M hM Ψ D hD A hA K T hT hLip).normBound = 1 := rfl

@[simp] theorem reducedMajorTranslationTwistedNiltest_lipBound :
    (reducedMajorTranslationTwistedNiltest w d hw hwd hd M hM Ψ D hD A hA K T hT hLip).lipBound = 2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K := rfl

@[simp] theorem reducedMajorTranslationTwistedNiltest_orbit :
    (reducedMajorTranslationTwistedNiltest w d hw hwd hd M hM Ψ D hD A hA K T hT hLip).orbit = majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial D)
        (fractionalMajorPolynomial_support w d D hD) A hA := rfl

@[simp] theorem reducedMajorTranslationTwistedNiltest_observable :
    (reducedMajorTranslationTwistedNiltest w d hw hwd hd M hM Ψ D hD A hA K T hT hLip).observable = weightedTranslationTwistedObservable w d hw hwd M hM Ψ
        (specializeMajorParameters (RingHom.id ℝ) (fractionalCoefficientPolynomial D) 0) T := rfl

end Construction

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotential
namespace OAI

section

namespace Erdos3

theorem linearRestrictionArithmeticBudget_le_exp (n m d H K : ℕ) {p P Q : ℝ}
    (hp : 0 ≤ p) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp Q) :
    (((((n + 1) ^ d * K) * (m * H + 1) ^ d) *
      (K ^ ((n + 1) ^ d) * H ^ ((n * m) * d)) : ℕ) : ℝ) ≤
        Real.exp ((d : ℝ) * p + Q + (d : ℝ) * (p + P + 1) +
          (p + 1) ^ d * Q + p * p * d * P) := by
  have hn1 : (n : ℝ) + 1 ≤ Real.exp p :=
    (add_le_add hn (le_refl 1)).trans (Real.add_one_le_exp p)
  have hnPow : ((n : ℝ) + 1) ^ d ≤ Real.exp ((d : ℝ) * p) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hn1 d
  have hmexp : (m : ℝ) ≤ Real.exp p := by
    exact hm.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp p))
  have hmH : (m : ℝ) * H ≤ Real.exp (p + P) := by
    rw [Real.exp_add]
    exact mul_le_mul hmexp hH (Nat.cast_nonneg H) (Real.exp_nonneg p)
  have hmH1 : (m : ℝ) * H + 1 ≤ Real.exp (p + P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ (add_nonneg hp hP) hmH
  have hmPow : ((m : ℝ) * H + 1) ^ d ≤ Real.exp ((d : ℝ) * (p + P + 1)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hmH1 d
  have hKPow : (K : ℝ) ^ ((n + 1) ^ d) ≤ Real.exp ((p + 1) ^ d * Q) := by
    calc
      _ ≤ (Real.exp Q) ^ ((n + 1) ^ d) := pow_le_pow_left₀ (Nat.cast_nonneg K) hK _
      _ = Real.exp ((((n : ℝ) + 1) ^ d) * Q) := by
        rw [← Real.exp_nat_mul]
        simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (add_le_add hn (le_refl 1)) d) hQ)
  have hHPow : (H : ℝ) ^ ((n * m) * d) ≤ Real.exp (p * p * d * P) := by
    calc
      _ ≤ (Real.exp P) ^ ((n * m) * d) := pow_le_pow_left₀ (Nat.cast_nonneg H) hH _
      _ = Real.exp ((n : ℝ) * m * d * P) := by
        rw [← Real.exp_nat_mul]
        simp only [Nat.cast_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul hn hm (Nat.cast_nonneg m) hp)
          (Nat.cast_nonneg d)) hP)
  have hfront := mul_le_mul hnPow hK (Nat.cast_nonneg K) (Real.exp_nonneg _)
  have hscaled := mul_le_mul hfront hmPow (by positivity) (by positivity)
  have hden := mul_le_mul hKPow hHPow (by positivity) (Real.exp_nonneg _)
  have htotal := mul_le_mul hscaled hden (by positivity) (by positivity)
  push_cast
  refine htotal.trans_eq ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem weightedPolynomialPotential_coeff (w : σ → ℕ) (d : ℕ)
    (P : σ → MvPolynomial σ ℚ) (m : σ →₀ ℕ) :
    (weightedPolynomialPotential w d P).coeff m =
      ∑ i, ((w i : ℚ) / d) * (X i * P i).coeff m := by
  classical
  rw [weightedPolynomialPotential, Finset.smul_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, coeff_smul]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem weightedPolynomialPotential_height (w : σ → ℕ) {d H : ℕ}
    (hd : 0 < d) (P : σ → MvPolynomial σ ℚ)
    (hweight : ∀ i, w i ≤ d) (hP : ∀ i, RationalPolynomialHeightLE (P i) H) :
    RationalPolynomialHeightLE (weightedPolynomialPotential w d P)
      ((Fintype.card σ + 1) * (d * H) ^ Fintype.card σ) := by
  classical
  intro m
  rw [weightedPolynomialPotential_coeff]
  apply rationalHeightLE_sum
  intro i
  have hw : RationalHeightLE ((w i : ℚ) / d) d := by
    simpa only [Int.cast_natCast, Int.natAbs_natCast] using
      rationalHeightLE_fraction (w i : ℤ) (d : ℤ)
        (by exact_mod_cast hd.ne') (by simpa using hweight i) (by simp)
  exact hw.mul (by simpa only [mul_comm] using (hP i).mul_X i m)

end Erdos3

end

section

namespace Erdos3

noncomputable def linearRestrictionLogPolynomial (d : ℕ) (P Q : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C d * Polynomial.X + Q +
    Polynomial.C d * (Polynomial.X + P + 1) +
    (Polynomial.X + 1) ^ d * Q +
    Polynomial.X * Polynomial.X * Polynomial.C d * P

theorem linearRestrictionLogPolynomial_eval (d : ℕ) (P Q : Polynomial ℕ) (p : ℝ) :
    (linearRestrictionLogPolynomial d P Q).eval₂ (Nat.castRingHom ℝ) p =
      (d : ℝ) * p + Q.eval₂ (Nat.castRingHom ℝ) p +
      (d : ℝ) * (p + P.eval₂ (Nat.castRingHom ℝ) p + 1) +
      (p + 1) ^ d * Q.eval₂ (Nat.castRingHom ℝ) p +
      p * p * d * P.eval₂ (Nat.castRingHom ℝ) p := by
  simp only [linearRestrictionLogPolynomial, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_one, Nat.coe_castRingHom]

noncomputable def projectedPotentialLogPolynomial (d : ℕ) : Polynomial ℕ :=
  let U := linearRestrictionLogPolynomial d Polynomial.X Polynomial.X
  let V := Polynomial.X + Polynomial.X * (Polynomial.C d + U)
  linearRestrictionLogPolynomial d ((Polynomial.X + 2) ^ 7) V

theorem potential_integration_height_le_exp (n d K : ℕ) {p P : ℝ}
    (hP : 0 ≤ P) (hn : (n : ℝ) ≤ p)
    (hK : (K : ℝ) ≤ Real.exp P) :
    (((n + 1) * (d * K) ^ n : ℕ) : ℝ) ≤
      Real.exp (p + p * ((d : ℝ) + P)) := by
  have hn1 : (n : ℝ) + 1 ≤ Real.exp p :=
    (add_le_add hn (le_refl 1)).trans (Real.add_one_le_exp p)
  have hd : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  have hbase : (d : ℝ) * K ≤ Real.exp ((d : ℝ) + P) := by
    rw [Real.exp_add]
    exact mul_le_mul hd hK (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg K)) hbase n
  rw [← Real.exp_nat_mul] at hpow
  push_cast
  calc
    _ ≤ Real.exp p * Real.exp ((n : ℝ) * ((d : ℝ) + P)) :=
      mul_le_mul hn1 hpow (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p + (n : ℝ) * ((d : ℝ) + P)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr
      (add_le_add (le_refl p) (mul_le_mul_of_nonneg_right hn (by positivity)))

theorem linearRestrictionHeight_le_exp_logPolynomial (n m d H K : ℕ)
    (P Q : Polynomial ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp (P.eval₂ (Nat.castRingHom ℝ) p))
    (hK : (K : ℝ) ≤ Real.exp (Q.eval₂ (Nat.castRingHom ℝ) p)) :
    (linearRestrictionHeight n m d H K : ℝ) ≤
      Real.exp ((linearRestrictionLogPolynomial d P Q).eval₂ (Nat.castRingHom ℝ) p) := by
  rw [linearRestrictionLogPolynomial_eval]
  exact linearRestrictionArithmeticBudget_le_exp n m d H K hp
    (natPolynomial_eval_nonneg P hp) (natPolynomial_eval_nonneg Q hp) hn hm hH hK

def projectedPotentialHeight (N n d H : ℕ) : ℕ :=
  linearRestrictionHeight n N d (rationalKernelHeight N H)
    ((n + 1) * (d * linearRestrictionHeight N n d H H) ^ n)

theorem projectedPotentialHeight_le_exp_logPolynomial (N n d H : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hn : n ≤ N) (hN : (N : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (projectedPotentialHeight N n d H : ℝ) ≤
      Real.exp ((projectedPotentialLogPolynomial d).eval₂ (Nat.castRingHom ℝ) p) := by
  let U := linearRestrictionLogPolynomial d Polynomial.X Polynomial.X
  let V := Polynomial.X + Polynomial.X * (Polynomial.C d + U)
  have hnp : (n : ℝ) ≤ p := (Nat.cast_le.mpr hn).trans hN
  have hfirst : (linearRestrictionHeight N n d H H : ℝ) ≤
      Real.exp (U.eval₂ (Nat.castRingHom ℝ) p) := by
    exact linearRestrictionHeight_le_exp_logPolynomial N n d H H
      Polynomial.X Polynomial.X hp hN hnp (by simpa using hH) (by simpa using hH)
  have hsecond : (((n + 1) * (d * linearRestrictionHeight N n d H H) ^ n : ℕ) : ℝ) ≤
      Real.exp (V.eval₂ (Nat.castRingHom ℝ) p) := by
    simpa only [V, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Nat.coe_castRingHom] using
      potential_integration_height_le_exp n d (linearRestrictionHeight N n d H H)
        (natPolynomial_eval_nonneg U hp) hnp hfirst
  have hkernel : (rationalKernelHeight N H : ℝ) ≤
      Real.exp (((Polynomial.X + 2) ^ 7 : Polynomial ℕ).eval₂ (Nat.castRingHom ℝ) p) := by
    simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X,
      Polynomial.eval₂_ofNat] using rationalKernelHeight_le_budget N H hp hN hH
  exact linearRestrictionHeight_le_exp_logPolynomial n N d (rationalKernelHeight N H)
    ((n + 1) * (d * linearRestrictionHeight N n d H H) ^ n)
    ((Polynomial.X + 2) ^ 7) V hp hnp hN hkernel hsecond

theorem exists_projectedPotential_height_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N n H : ℕ) (p : ℝ),
      0 ≤ p → n ≤ N → (N : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (projectedPotentialHeight N n d H : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ((projectedPotentialHeight N n d H * (N + 1) ^ d : ℕ) : ℝ) ≤
        Real.exp ((p + C) ^ C) ∧
      ((projectedPotentialHeight N n d H ^ ((N + 1) ^ d) : ℕ) : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  let W := projectedPotentialLogPolynomial d
  let T := W + (W + Polynomial.C d * Polynomial.X) + (Polynomial.X + 1) ^ d * W
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro N n H p hp hn hN hH
  let w := W.eval₂ (Nat.castRingHom ℝ) p
  have hw : 0 ≤ w := natPolynomial_eval_nonneg W hp
  have hd : 0 ≤ (d : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hsw : 0 ≤ (p + 1) ^ d * w := by positivity
  have htotal : w + (w + (d : ℝ) * p) + (p + 1) ^ d * w ≤ (p + C) ^ C := by
    simpa only [T, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one,
      Nat.coe_castRingHom] using hbound p hp
  have hheight := projectedPotentialHeight_le_exp_logPolynomial N n d H hp hn hN hH
  have hsupport : (((N + 1) ^ d : ℕ) : ℝ) ≤ Real.exp ((d : ℝ) * p) := by
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity)
      ((add_le_add hN (le_refl 1)).trans (Real.add_one_le_exp p)) d
  have hsupport' : (((N + 1) ^ d : ℕ) : ℝ) ≤ (p + 1) ^ d := by
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    exact pow_le_pow_left₀ (by positivity) (add_le_add hN (le_refl 1)) d
  refine ⟨hheight.trans (Real.exp_le_exp.mpr (by change w ≤ _; linarith)), ?_, ?_⟩
  · calc
      _ ≤ Real.exp w * Real.exp ((d : ℝ) * p) := by
        rw [Nat.cast_mul]
        exact mul_le_mul hheight hsupport (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (w + (d : ℝ) * p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · calc
      _ ≤ (Real.exp w) ^ ((N + 1) ^ d) := by
        rw [Nat.cast_pow]
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hheight _
      _ = Real.exp ((((N + 1) ^ d : ℕ) : ℝ) * w) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp ((p + 1) ^ d * w) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsupport' hw)
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
variable {σ : Type*} [Fintype σ]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem weightedBasis_polynomial_height_of_coordinates
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) {H : ℕ} (hH : 1 ≤ H)
    (hx : ∀ i, RationalHeightLE ((weightedBasis w d hw).repr x i) H) :
    RationalPolynomialHeightLE x.val.polynomial H := by
  intro α
  by_cases hα : Finsupp.weight w α < d
  · exact hx (Sum.inr ⟨α, hα⟩)
  · have hz : x.val.polynomial.coeff α = 0 := by
      by_contra hne
      have hb := x.property.2 (MvPolynomial.mem_support_iff.mpr hne)
      change Finsupp.weight w α + 1 ≤ d at hb
      omega
    rw [hz]
    exact rationalHeightLE_zero hH

theorem explicit_projected_weighted_potential
    (w : σ → ℕ) (v : τ → ℕ) {d : ℕ}
    (hd : 0 < d) (hvd : ∀ i, v i ≤ d)
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ)) (hBA : ∀ x, B (A x) = x)
    [DecidableEq σ] [DecidableEq τ]
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (hBweight : ∀ i j, w i ≠ v j → B (Pi.single i 1) j = 0)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0)
    (L : τ → PolynomialTranslationLie σ)
    (hL : ∀ j, L j ∈ U) (hbase : ∀ j, (L j).base = A (Pi.single j 1))
    (hhom : ∀ j, (L j).polynomial.IsWeightedHomogeneous w (d - v j)) :
    let P := fun j => polynomialLinearRestriction A (L j).polynomial
    let W := polynomialLinearRestriction B (weightedPolynomialPotential v d P)
    W.IsWeightedHomogeneous w d ∧
      ∀ x ∈ U, x.base ∈ A.range → ∀ z ∈ A.range,
        eval z (scalarDirectionalDerivative x.base W) = eval z x.polynomial := by
  let P := fun j => polynomialLinearRestriction A (L j).polynomial
  let V := weightedPolynomialPotential v d P
  let W := polynomialLinearRestriction B V
  let rel := projectedPotentialRelation A hA w d U hgraded frequency hfrequency hkill
  have hPhom : ∀ j, (P j).IsWeightedHomogeneous v (d - v j) :=
    fun j => polynomialLinearRestriction_isWeightedHomogeneous A v w hweight (hhom j)
  have hlift : ∀ j, (Pi.single j 1, P j) ∈ rel.space := by
    intro j
    apply (mem_relationSpace _ _ _).mpr
    let y : baseRange A := ⟨L j, by
      change (L j).base ∈ A.range
      rw [hbase j]
      exact A.mem_range_self (Pi.single j 1)⟩
    refine ⟨y, hL j, ?_⟩
    apply PolynomialTranslationLie.ext
    · apply hA
      exact (apply_projectedBaseCoordinates A hA y).trans (hbase j)
    · rfl
  have hV : V.IsWeightedHomogeneous v d :=
    weightedPolynomialPotential_homogeneous v d P hvd hPhom
  have hres : polynomialLinearRestriction A W = V :=
    polynomialLinearRestriction_leftInverse A B hBA V
  refine ⟨polynomialLinearRestriction_isWeightedHomogeneous B w v hBweight hV, ?_⟩
  intro x hx hxrange z hz
  let x' : baseRange A := ⟨x, hxrange⟩
  have hderiv : scalarDirectionalDerivative (projectedBaseCoordinates A hA x') V =
      polynomialLinearRestriction A x.polynomial :=
    rel.weighted_potential_derivative P hlift v hd hvd hPhom _ _
      ((mem_relationSpace _ _ _).mpr ⟨x', hx, rfl⟩)
  have hpoly : polynomialLinearRestriction A (scalarDirectionalDerivative x.base W) =
      polynomialLinearRestriction A x.polynomial := by
    rw [← apply_projectedBaseCoordinates A hA x',
      ← scalarDirectionalDerivative_linearRestriction, hres]
    exact hderiv
  obtain ⟨t, ht⟩ := hz
  have he := congrArg (eval t) hpoly
  simpa only [eval_polynomialLinearRestriction, ht] using he

theorem weightedBasis_projection_polynomial_height
    (w : σ → ℕ) (d j : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) {H : ℕ} (hH : 1 ≤ H)
    (hx : RationalPolynomialHeightLE x.val.polynomial H) :
    RationalPolynomialHeightLE
      (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.polynomial H := by
  intro α
  by_cases hα : Finsupp.weight w α < d
  · rw [weightedBasis_projection_coeff w d j hw x ⟨α, hα⟩]
    split_ifs
    · exact hx α
    · exact rationalHeightLE_zero hH
  · have hz :
        (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.polynomial.coeff α = 0 := by
      by_contra hne
      have hb := (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).property.2
        (MvPolynomial.mem_support_iff.mpr hne)
      change Finsupp.weight w α + 1 ≤ d at hb
      omega
    rw [hz]
    exact rationalHeightLE_zero hH

end Erdos3.PolynomialTranslationLie

end

section

namespace MvPolynomial
open scoped _root_.MvPolynomial

theorem IsWeightedHomogeneous.totalDegree_le_of_positive_weights
    {σ R : Type*} [CommRing R] {w : σ → ℕ} {d : ℕ}
    {P : MvPolynomial σ R} (hP : P.IsWeightedHomogeneous w d)
    (hw : ∀ i, 0 < w i) : P.totalDegree ≤ d := by
  apply Erdos3.totalDegree_le_of_positive_weightedSupport w hw
  intro α hα
  exact (hP (MvPolynomial.mem_support_iff.mp hα)).le

end MvPolynomial

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ J : Type*} [Fintype σ]

theorem exists_controlled_projected_potential_lifts
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (U : Submodule ℚ (PolynomialTranslationLie σ))
    (hU : U ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.comap (weightedSubalgebra w d).subtype))
    (g : J → PolynomialTranslationLie σ)
    (hspan : Submodule.span ℚ (Set.range g) = U)
    {H : ℕ} (hH : 1 ≤ H)
    (hbaseHeight : ∀ j i, RationalHeightLE ((g j).base i) H)
    (hpolyHeight : ∀ j, RationalPolynomialHeightLE (g j).polynomial H) :
    ∃ (n : ℕ) (v : Fin n → ℕ) (A : (Fin n → ℚ) →ₗ[ℚ] (σ → ℚ))
      (L : Fin n → PolynomialTranslationLie σ),
      n ≤ Fintype.card σ ∧ (∀ j, 0 < v j) ∧ (∀ j, v j ≤ d) ∧
      Function.Injective A ∧ A.range = U.map baseLinear ∧
      (∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0) ∧
      (∀ j i, RationalHeightLE (A (Pi.single j 1) i) H) ∧
      (∀ j, L j ∈ U) ∧ (∀ j, (L j).base = A (Pi.single j 1)) ∧
      (∀ j, (L j).polynomial.IsWeightedHomogeneous w (d - v j)) ∧
      (∀ j, RationalPolynomialHeightLE (L j).polynomial H) ∧
      ∀ j, (L j).polynomial.totalDegree ≤ d := by
  classical
  have hgm : ∀ a, g a ∈ U := by
    intro a
    rw [← hspan]
    exact Submodule.subset_span ⟨a, rfl⟩
  have hspanbase : Submodule.span ℚ (Set.range (fun a => (g a).base)) =
      U.map baseLinear := by
    rw [← hspan, Submodule.map_span, ← Set.range_comp]
    rfl
  obtain ⟨n, v, A, hn, hv, hvd, hinj, hrange, hweight, hheight, hselected⟩ :=
    exists_controlled_graded_base_coordinates w d hw hwd (U.map baseLinear)
      (basisGradedSubmodule_ambient_base_image w d hw U hU hgraded)
      (fun a => (g a).base) hspanbase hH hbaseHeight
  choose a ha using hselected
  let x (j : Fin n) : weightedSubalgebra w d := ⟨g (a j), hU (hgm (a j))⟩
  let y (j : Fin n) : weightedSubalgebra w d :=
    basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) (v j) (x j)
  refine ⟨n, v, A, fun j => (y j).val, hn, hv, hvd, hinj, hrange, hweight,
    hheight, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hgraded (v j) (x j) (hgm (a j))
  · intro j
    change weightedBaseLinear w d (y j) = A (Pi.single j 1)
    rw [show y j = basisGradeProjection (weightedBasis w d hw)
      (weightedBasisGrade w d) (v j) (x j) from rfl, base_gradeProjection]
    exact (ha j).symm
  · intro j
    exact weightedBasis_projection_isWeightedHomogeneous w d (v j) hw (x j)
  · intro j
    exact weightedBasis_projection_polynomial_height w d (v j) hw (x j) hH
      (hpolyHeight (a j))
  · intro j
    have hhom := weightedBasis_projection_isWeightedHomogeneous w d (v j) hw (x j)
    exact (_root_.OAI.MvPolynomial.IsWeightedHomogeneous.totalDegree_le_of_positive_weights hhom hw).trans (Nat.sub_le d (v j))

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ J : Type*} [Fintype σ]

theorem exists_controlled_projected_potential
    (w : σ → ℕ) {d H : ℕ} (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hbound : U.toSubmodule ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.toSubmodule.comap (weightedSubalgebra w d).subtype))
    (g : J → PolynomialTranslationLie σ)
    (hspan : Submodule.span ℚ (Set.range g) = U.toSubmodule) (hH : 1 ≤ H)
    (hbase : ∀ j i, RationalHeightLE ((g j).base i) H)
    (hpoly : ∀ j, RationalPolynomialHeightLE (g j).polynomial H)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0) :
    ∃ (n : ℕ) (W : MvPolynomial σ ℚ), n ≤ Fintype.card σ ∧
      W.IsWeightedHomogeneous w d ∧
      (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map baseLinear,
        eval z (scalarDirectionalDerivative x.base W) = eval z x.polynomial) ∧
      RationalPolynomialHeightLE W
        (linearRestrictionHeight n (Fintype.card σ) d
          (rationalKernelHeight (Fintype.card σ) H)
          ((n + 1) * (d * linearRestrictionHeight (Fintype.card σ) n d H H) ^ n)) := by
  classical
  obtain ⟨n, v, A, L, hn, hv, hvd, hA, hrange, hweight, hAheight,
    hL, hLbase, hLhom, hLheight, hLdegree⟩ :=
    exists_controlled_projected_potential_lifts w d hw hwd U.toSubmodule
      hbound hgraded g hspan hH hbase hpoly
  obtain ⟨B, hBA, hBweight, hBheight⟩ :=
    exists_controlled_weighted_leftInverse A v w hweight hA hH hAheight
  let P := fun j => polynomialLinearRestriction A (L j).polynomial
  let V := weightedPolynomialPotential v d P
  let W := polynomialLinearRestriction B V
  have hPheight : ∀ j, RationalPolynomialHeightLE (P j)
      (linearRestrictionHeight (Fintype.card σ) n d H H) := by
    intro j
    simpa only [Fintype.card_fin] using polynomialLinearRestriction_height
      A (L j).polynomial (fun i k => hAheight k i) (hLheight j) (hLdegree j)
  have hPhom : ∀ j, (P j).IsWeightedHomogeneous v (d - v j) :=
    fun j => polynomialLinearRestriction_isWeightedHomogeneous A v w hweight (hLhom j)
  have hVheight : RationalPolynomialHeightLE V
      ((n + 1) * (d * linearRestrictionHeight (Fintype.card σ) n d H H) ^ n) := by
    simpa only [Fintype.card_fin] using weightedPolynomialPotential_height v hd P hvd hPheight
  have hVhom : V.IsWeightedHomogeneous v d :=
    weightedPolynomialPotential_homogeneous v d P hvd hPhom
  have hW := explicit_projected_weighted_potential w v hd hvd A hA B hBA hweight hBweight
    U (fun _ hx => topProjection_mem_of_basisGraded w d hw hd U.toSubmodule hbound hgraded hx)
    frequency hfrequency hkill L hL hLbase hLhom
  refine ⟨n, W, hn, hW.1, ?_, ?_⟩
  · intro x hx z hz
    apply hW.2 x hx
    · rw [hrange]
      exact ⟨x, hx, rfl⟩
    · rwa [hrange]
  · simpa only [Fintype.card_fin] using polynomialLinearRestriction_height B V
      (fun i j => hBheight j i) hVheight (_root_.OAI.MvPolynomial.IsWeightedHomogeneous.totalDegree_le_of_positive_weights hVhom hv)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

theorem exists_controlled_projected_potential_bounds (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ J : Type*} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i),
      (∀ i, w i ≤ d) →
      ∀ U : LieSubalgebra ℚ (PolynomialTranslationLie σ),
      U.toSubmodule ≤ (weightedSubalgebra w d).toSubmodule →
      BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
        (U.toSubmodule.comap (weightedSubalgebra w d).subtype) →
      ∀ (g : J → PolynomialTranslationLie σ),
      Submodule.span ℚ (Set.range g) = U.toSubmodule →
      ∀ H : ℕ, 1 ≤ H →
      (∀ j i, RationalHeightLE ((g j).base i) H) →
      (∀ j, RationalPolynomialHeightLE (g j).polynomial H) →
      ∀ (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ),
      frequency constantDirection ≠ 0 →
      (∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0) →
      ∀ p : ℝ, 0 ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      ∃ (W : MvPolynomial σ ℚ) (q : ℕ),
        W.IsWeightedHomogeneous w d ∧
        (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map baseLinear,
          eval z (scalarDirectionalDerivative x.base W) = eval z x.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (fun α => W.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (map (algebraMap ℚ ℝ) W) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ α, ((W.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ((W.coeff α).den : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hbudget⟩ := exists_projectedPotential_height_budget d
  refine ⟨C, hC, ?_⟩
  intro σ J _ w hw hwd U hbound hgraded g hspan H hH hbase hpoly
    frequency hfrequency hkill p hp hN hHp
  obtain ⟨n, W, hn, hW, hderiv, hheight⟩ := exists_controlled_projected_potential
    w hw hd hwd U hbound hgraded g hspan hH hbase hpoly frequency hfrequency hkill
  change RationalPolynomialHeightLE W (projectedPotentialHeight (Fintype.card σ) n d H) at hheight
  have hb := hbudget (Fintype.card σ) n H p hp hn hN hHp
  have hdegree := _root_.OAI.MvPolynomial.IsWeightedHomogeneous.totalDegree_le_of_positive_weights hW hw
  have hcard : W.support.card ≤ (Fintype.card σ + 1) ^ d :=
    boundedExponentSet_card_le W.support d (fun _ hα => (le_totalDegree hα).trans hdegree)
  have hden : polynomialDenominator W ≤
      projectedPotentialHeight (Fintype.card σ) n d H ^ ((Fintype.card σ + 1) ^ d) :=
    (polynomialDenominator_le W hheight).trans
      (Nat.pow_le_pow_right hheight.one_le hcard)
  refine ⟨W, polynomialDenominator W, hW, hderiv, polynomialDenominator_pos W,
    (Nat.cast_le.mpr hden).trans hb.2.2, polynomialDenominator_coefficientGrid W, ?_, ?_⟩
  · have hm := rationalPolynomial_realMass_le W hheight hdegree
    exact hm.trans (by simpa only [Nat.mul_comm] using hb.2.1)
  · intro α
    exact ⟨(Nat.cast_le.mpr (hheight α).1).trans hb.1,
      (Nat.cast_le.mpr (hheight α).2).trans hb.1⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

theorem exists_intrinsic_controlled_projected_potential_bounds (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ J : Type*} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
      (hwd : ∀ i, w i ≤ d),
      ∀ U : LieSubalgebra ℚ (weightedSubalgebra w d),
      BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) U.toSubmodule →
      ∀ (g : J → weightedSubalgebra w d),
      Submodule.span ℚ (Set.range g) = U.toSubmodule →
      ∀ H : ℕ, 1 ≤ H →
      (∀ j i, RationalHeightLE ((g j).val.base i) H) →
      (∀ j, RationalPolynomialHeightLE (g j).val.polynomial H) →
      ∀ (frequency : weightedSubalgebra w d →ₗ[ℚ] ℚ),
      frequency (centralRationalElement w d hd 1) = 1 →
      (∀ x ∈ U, x ∈ (weightedFiltration w d hwd).layer d → frequency x = 0) →
      ∀ p : ℝ, 0 ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      ∃ (W : MvPolynomial σ ℚ) (q : ℕ),
        W.IsWeightedHomogeneous w d ∧
        (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base W) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (fun α => W.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (map (algebraMap ℚ ℝ) W) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ α, ((W.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ((W.coeff α).den : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hpotential⟩ := exists_controlled_projected_potential_bounds d hd
  refine ⟨C, hC, ?_⟩
  intro σ J _ w hw hwd U hgraded g hspan H hH hbase hpoly
    frequency hfrequency hkill p hp hN hHp
  let V : LieSubalgebra ℚ (PolynomialTranslationLie σ) :=
    U.map (weightedSubalgebra w d).incl
  have hVsub : V.toSubmodule =
      U.toSubmodule.map (weightedSubalgebra w d).subtype := rfl
  have hbound : V.toSubmodule ≤ (weightedSubalgebra w d).toSubmodule := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hVgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (V.toSubmodule.comap (weightedSubalgebra w d).subtype) := by
    rw [hVsub, Submodule.comap_map_eq_of_injective
      (weightedSubalgebra w d).subtype_injective]
    exact hgraded
  have hVspan : Submodule.span ℚ (Set.range (fun j => (g j).val)) = V.toSubmodule := by
    rw [hVsub, ← hspan, ← Submodule.span_image, ← Set.range_comp]
    rfl
  obtain ⟨η, hη⟩ := LinearMap.exists_extend
    (show (weightedSubalgebra w d).toSubmodule →ₗ[ℚ] ℚ from frequency)
  have hext (x : weightedSubalgebra w d) : η x.val = frequency x :=
    congrArg (fun f : weightedSubalgebra w d →ₗ[ℚ] ℚ => f x) hη
  have hconstant : (centralRationalElement w d hd 1).val =
      (constantDirection : PolynomialTranslationLie σ) := by
    apply PolynomialTranslationLie.ext <;> simp [centralRationalElement, constantDirection]
  have hηconstant : η constantDirection ≠ 0 := by
    rw [← hconstant, hext, hfrequency]
    exact one_ne_zero
  have hηkill : ∀ x ∈ V, x ∈ weightedLayer w d d → η x = 0 := by
    rintro x ⟨y, hy, rfl⟩ htop
    change η y.val = 0
    rw [hext]
    exact hkill y hy htop
  obtain ⟨W, q, hW, hderiv, hq, hqp, hgrid, hmass, hcoeff⟩ :=
    hpotential w hw hwd V hbound hVgraded (fun j => (g j).val) hVspan
      H hH hbase hpoly η hηconstant hηkill p hp hN hHp
  refine ⟨W, q, hW, ?_, hq, hqp, hgrid, hmass, hcoeff⟩
  intro x hx z hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact hderiv x.val ⟨x, hx, rfl⟩ _ ⟨y.val, ⟨y, hy, rfl⟩, rfl⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

theorem exists_associatedGraded_controlled_potential (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L d) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra w d)
      (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ (weightedFiltration w d hwd).layer j)
      (W : LieSubalgebra ℚ F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule →
      ∀ (v : J → F.AssociatedGraded), Submodule.span ℚ (Set.range v) = W.toSubmodule →
      ∀ (p : ℝ), 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight ((weightedBasis w d hw).repr (φ (b i)) j) ≤ p) →
      (∀ j i, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v j) i) ≤ p) →
      ∀ η : weightedSubalgebra w d →ₗ[ℚ] ℚ,
      η (centralRationalElement w d hd 1) = 1 →
      (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω d x = x →
        F.gradedFrequency b ω hF (η.comp φ.toLinearMap) x = 0) →
      let U := W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)
      ∃ (V : MvPolynomial σ ℚ) (q : ℕ),
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (map (algebraMap ℚ ℝ) V) ≤
          Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
        ∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) := by
  obtain ⟨C, hC, hpotential⟩ := exists_intrinsic_controlled_projected_potential_bounds d hd
  refine ⟨C, hC, ?_⟩
  intro σ ι J L _ _ _ _ F b ω hF w hw hwd φ hφ W hW v hv
    p hp hι hσ hentries hcoords η hη hkill U
  let π := weightedTranslationGradedProjection F w d hw hwd φ hφ
  let g : J → weightedSubalgebra w d := fun j => π (v j)
  let H := ⌈Real.exp ((p + 2)^4)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp _
  have hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      U.toSubmodule :=
    weightedTranslationGradedProjection_image_graded F w d hw hwd φ hφ b ω hF W hW
  have hspan : Submodule.span ℚ (Set.range g) = U.toSubmodule :=
    F.homogeneousGradedProjection_span (weightedFiltration w d hwd)
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd)
      (weightedBasis_homogeneous_brackets w d hw) φ hφ W v hv
  have hheight (j : J) (i : WeightedBasisIndex w d) :
      RationalHeightLE ((weightedBasis w d hw).repr (g j) i) H :=
    F.homogeneousGradedProjection_coordinate_ceil_height (weightedFiltration w d hwd)
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd)
      (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF
      hp hι hentries (v j) (hcoords j) i
  have hbase (j : J) (i : σ) : RationalHeightLE ((g j).val.base i) H :=
    weightedBasis_base_height w d hw (g j) (hheight j) i
  have hpoly (j : J) : RationalPolynomialHeightLE (g j).val.polynomial H :=
    weightedBasis_polynomial_height_of_coordinates w d hw (g j) hH (hheight j)
  have hfrequency : ∀ x ∈ U, x ∈ (weightedFiltration w d hwd).layer d → η x = 0 := by
    intro x hx htop
    exact F.homogeneousGradedProjection_top_frequency_zero (weightedFiltration w d hwd)
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd)
      (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF W hW η hkill hx htop
  have hpow : 0 ≤ (p + 2)^4 := by positivity
  have hp' : 0 ≤ p + (p + 2)^4 + 1 := by linarith
  have hσ' : (Fintype.card σ : ℝ) ≤ p + (p + 2)^4 + 1 := by linarith
  have hHp : (H : ℝ) ≤ Real.exp (p + (p + 2)^4 + 1) :=
    (ceil_exp_le_exp_add_one hpow).trans (Real.exp_le_exp.mpr (by linarith))
  exact hpotential w hw hwd U hgraded g hspan H hH hbase hpoly η hη hfrequency
    (p + (p + 2)^4 + 1) hp' hσ' hHp

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedNaturalFullSiteScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*}
variable {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (j : Fin m) (i : Fin (n j))

local notation "slots" => Finset.card (layerIntegerPrincipalSlots (G := G) B j i)
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i

noncomputable def allocatedNaturalFullSiteRatio : ℝ :=
  R j * allocatedPrincipalChartRatio (G := G) B U b (R := R) j i

variable [Fintype G] [∀ j, Fintype (I j)] {σ : Fin m → ℝ}
variable (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalMarkedOrbitTranslation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}

theorem map_log_constantGroupOrbit_mul_of_realificationMap_eq_one
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (w : σ → ℕ)
    (orbit : F.realification.PolynomialOrbit w) (z : F.realification.Group)
    (hz : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ z = 1) :
    VectorPolynomial.map (realLieHomToRat (realificationLieHom φ)).toLinearMap
        (F.realification.constantGroupOrbit w z * orbit).log =
      VectorPolynomial.map (realLieHomToRat (realificationLieHom φ)).toLinearMap orbit.log := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro x
  rw [map_sub]
  apply sub_eq_zero.mpr
  have he : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ
        (F.realification.polynomialOrbitRealEval w x
          (F.realification.constantGroupOrbit w z * orbit)) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ
          (F.realification.polynomialOrbitRealEval w x orbit) := by
    rw [map_mul, polynomialOrbitRealEval_constantGroupOrbit, map_mul, hz, one_mul]
  have hc := congrArg NilpotentLieBCHGroup.coord he
  calc
    _ = realificationLieHom φ
        (eval₂ x (F.realification.constantGroupOrbit w z * orbit).log) :=
      eval₂_map (realificationLieHom φ).toLinearMap x _
    _ = realificationLieHom φ (eval₂ x orbit.log) := hc
    _ = _ := (eval₂_map (realificationLieHom φ).toLinearMap x orbit.log).symm

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientAmplitudeDensityTest
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_affine_coefficient_amplitude_density_test (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
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
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (amplitude : (Option K × I → ℝ) → ℂ) (_hamp : ∀ x, ‖amplitude x‖ ≤ 1)
    {Lip : ℝ≥0} (_hLip : LipschitzWith Lip amplitude) (_hLipP : (Lip : ℝ) ≤ Real.exp P)
    (D : CoefficientTorus (K := K) U → ℝ) (_hD : Integrable D μ)
    (_hDmass : (∫ x, D x ∂μ) = 1)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (amplitude (fun t => (z t : ℝ) / V t) *
          (D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ))) : ℂ))) -
      ∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        amplitude (fun t => (z t : ℝ) / V t)‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hnormalization⟩ := exists_affine_coefficient_amplitude_fourier_normalization m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    amplitude hamp Lip hLip hLipP D hD hDmass η hη happrox
  obtain ⟨hZ, hfourier⟩ := hnormalization hP hn hd U hC hCP frequency hbound c hB hBP hcoefficients
    p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    amplitude hamp hLip hLipP
  refine ⟨hZ, ?_⟩
  apply selectedResidueSmoothPMF_weighted_coefficient_density U μ frequency c stride G V hV hZ
    (fun z => affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ)))
    (fun z => amplitude (fun t => (z t : ℝ) / V t)) (fun z _ => hamp _) D hD hDmass hη happrox
  simpa only [coefficientTorusFourierSum, coefficientTorusCharacter_sample U _ p hp hm] using hfourier

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSlicedGridResourceBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

noncomputable def allocatedSlicedGridResourceLog {A : Type*} [Semiring A]
    (m dim : ℕ) (D p v E : A) : A :=
  let L := fun (j : Fin m) (e : A) => slicedGridSiteLog j.val
    (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
    ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card)
    ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) D p e
  let Cp := ∑ j, (L j 0 + D * (v + 1))
  let E' := uniformProductAccuracyLog D Cp E + D * (v + 1) + 1
  ∑ j, (siteExponentialOutputLog (Fintype.card (Finset (Fin dim))) (L j E') + (D + 1) * (v + 1))

theorem allocatedSlicedGridResourceLog_nonneg (m dim : ℕ) {D p v E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    0 ≤ allocatedSlicedGridResourceLog m dim D p v E := by
  unfold allocatedSlicedGridResourceLog
  dsimp only
  apply Finset.sum_nonneg
  intro j _
  apply add_nonneg
  · apply siteExponentialOutputLog_nonneg
    apply (slicedGridSiteLog_bounds _ _ _ _ hD hp ?_).1
    apply add_nonneg _ zero_le_one
    apply add_nonneg _ (by positivity)
    apply uniformProductAccuracyLog_nonneg hD _ hE
    exact Finset.sum_nonneg (fun i _ =>
      add_nonneg (slicedGridSiteLog_bounds _ _ _ _ hD hp (le_refl 0)).1 (by positivity))
  · positivity

theorem exists_allocatedSlicedGridResource_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p v E : ℝ}, 0 ≤ D → 0 ≤ p → 0 ≤ v → 0 ≤ E →
      allocatedSlicedGridResourceLog m dim D p v E ≤ (D + p + v + E + A) ^ A := by
  obtain ⟨b, hb, hsite⟩ := exists_slicedGridSiteLog_uniform_budget m dim
  let X : Polynomial ℕ := Polynomial.X
  let Cp : Polynomial ℕ := (m : Polynomial ℕ) * ((X + Polynomial.C b) ^ b + X * (X + 1))
  let Epoly := uniformProductAccuracyLog X Cp X + X * (X + 1) + 1
  let poly : Polynomial ℕ := (m : Polynomial ℕ) *
    (siteExponentialOutputLog (Fintype.card (Finset (Fin dim))) ((2 * X + Epoly + Polynomial.C b) ^ b) + (X + 1) ^ 2)
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D p v E hD hp hv hE
  let R := D + p + v + E
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hDR : D ≤ R := by dsimp [R]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hvR : v ≤ R := by dsimp [R]; linarith
  have hER : E ≤ R := by dsimp [R]; linarith
  let L := fun (j : Fin m) (e : ℝ) => slicedGridSiteLog j.val
    (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
    ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card)
    ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) D p e
  have hL0 (j : Fin m) : L j 0 ≤ (R + b) ^ b :=
    (hsite hD hp (le_refl (0 : ℝ)) j).trans
      (pow_le_pow_left₀ (by positivity) (by dsimp [R]; linarith) b)
  let Cbound := (m : ℝ) * ((R + b) ^ b + R * (R + 1))
  have hCb : 0 ≤ Cbound := by dsimp [Cbound]; positivity
  have hCp0 : 0 ≤ ∑ j : Fin m, (L j 0 + D * (v + 1)) :=
    Finset.sum_nonneg (fun j _ => add_nonneg (slicedGridSiteLog_bounds _ _ _ _ hD hp (le_refl 0)).1 (by positivity))
  have hCp : (∑ j : Fin m, (L j 0 + D * (v + 1))) ≤ Cbound := by
    calc
      _ ≤ ∑ _j : Fin m, ((R + b) ^ b + R * (R + 1)) := Finset.sum_le_sum (fun j _ => by
        apply add_le_add (hL0 j)
        exact mul_le_mul hDR (add_le_add hvR le_rfl) (by positivity) hR)
      _ = _ := by simp [Cbound, mul_add]
  let E' := uniformProductAccuracyLog D (∑ j, (L j 0 + D * (v + 1))) E + D * (v + 1) + 1
  let Ebound := uniformProductAccuracyLog R Cbound R + R * (R + 1) + 1
  have hE' : 0 ≤ E' := by
    dsimp only [E']
    exact add_nonneg (add_nonneg (uniformProductAccuracyLog_nonneg hD hCp0 hE) (by positivity)) zero_le_one
  have hEb : 0 ≤ Ebound := by
    dsimp only [Ebound]
    exact add_nonneg (add_nonneg (uniformProductAccuracyLog_nonneg hR hCb hR) (by positivity)) zero_le_one
  have hEbound : E' ≤ Ebound := by
    dsimp only [E', Ebound, uniformProductAccuracyLog]
    gcongr
  have hL (j : Fin m) : L j E' ≤ (2 * R + Ebound + b) ^ b :=
    (hsite hD hp hE' j).trans (pow_le_pow_left₀ (by positivity)
      (by linarith only [hDR, hpR, hEbound]) b)
  have htotal : allocatedSlicedGridResourceLog m dim D p v E ≤
      (m : ℝ) * (siteExponentialOutputLog (Fintype.card (Finset (Fin dim)))
        ((2 * R + Ebound + b) ^ b) + (R + 1) ^ 2) := by
    change (∑ j : Fin m, (siteExponentialOutputLog _ (L j E') + (D + 1) * (v + 1))) ≤ _
    calc
      _ ≤ ∑ _j : Fin m, (siteExponentialOutputLog (Fintype.card (Finset (Fin dim)))
          ((2 * R + Ebound + b) ^ b) + (R + 1) ^ 2) := Finset.sum_le_sum (fun j _ => by
        apply add_le_add
        · unfold siteExponentialOutputLog
          gcongr
          all_goals exact hL j
        · rw [pow_two]
          exact mul_le_mul (add_le_add hDR le_rfl) (add_le_add hvR le_rfl) (by positivity) (by positivity))
      _ = _ := by simp [mul_add]
  apply htotal.trans
  simpa [poly, X, Epoly, Cp, Ebound, Cbound, uniformProductAccuracyLog,
    siteExponentialOutputLog, Polynomial.eval₂_pow] using hbound R hR

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineAnalyticBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_allocatedAffineModelMass_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p v F Prho Pk target : ℝ},
      0 ≤ D → 0 ≤ p → 0 ≤ v → 0 ≤ F → 0 ≤ Prho → 0 ≤ Pk → 0 ≤ target →
      ∀ (outputs axes gridaxes ambient : ℕ),
      (outputs : ℝ) ≤ D → (axes : ℝ) ≤ D → (gridaxes : ℝ) ≤ D → (ambient : ℝ) ≤ D →
      (dim : ℝ) ≤ D → (probabilityProfileLipschitz : ℝ) ≤ D →
      let Eg := outputs * Prho + (target + F) + 1
      let Op := allocatedSlicedGridResourceLog m dim D p v Eg
      let Plong := ((m : ℝ) + 2) * dim + m + 4 + Prho + axes * max Op 0 + (target + F) + 2
      let Q := idealSiteLogBudget outputs dim Plong
      2 * (2 : ℝ) ^ dim + F + (2 : ℝ) ^ dim * (ambient * ((m + 1 : ℕ) * Pk)) +
        ((2 : ℝ) ^ dim * axes * (4 * Q + 8) + Q) + gridaxes * Op ≤
        (D + p + v + F + Prho + Pk + target + A) ^ A := by
  obtain ⟨b, hb, hgrid⟩ := exists_allocatedSlicedGridResource_budget m dim
  let X : Polynomial ℕ := Polynomial.X
  let O : Polynomial ℕ := (3 * X + (X ^ 2 + 2 * X + 1) + Polynomial.C b) ^ b
  let Pbox : Polynomial ℕ := Polynomial.C ((m + 2) * dim + m + 4)
  let Pl : Polynomial ℕ := Pbox + X + X * O + 2 * X + 2
  let Qp := allocatedFiniteIdealProfileLog X Pl
  let poly : Polynomial ℕ := 2 * (2 : Polynomial ℕ) ^ dim + X + (2 : Polynomial ℕ) ^ dim *
    (X * ((m + 1 : ℕ) * X)) + ((2 : Polynomial ℕ) ^ dim * X * (4 * Qp + 8) + Qp) + X * O
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D p v F Prho Pk target hD hp hv hF hPrho hPk htarget outputs axes gridaxes ambient
    hout haxes hgridaxes hamb hdim hprofile Eg Op Plong Q
  let R := D + p + v + F + Prho + Pk + target
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hDR : D ≤ R := by dsimp [R]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hvR : v ≤ R := by dsimp [R]; linarith
  have hFR : F ≤ R := by dsimp [R]; linarith
  have hPrhoR : Prho ≤ R := by dsimp [R]; linarith
  have hPkR : Pk ≤ R := by dsimp [R]; linarith
  have htR : target ≤ R := by dsimp [R]; linarith
  have hEg : 0 ≤ Eg := by dsimp [Eg]; positivity
  have hEgR : Eg ≤ R ^ 2 + 2 * R + 1 := by
    have hprod := mul_le_mul (hout.trans hDR) hPrhoR hPrho hR
    dsimp only [Eg]
    nlinarith only [hprod, htR, hFR]
  let Ob := (3 * R + (R ^ 2 + 2 * R + 1) + b) ^ b
  have hOb : 0 ≤ Ob := by dsimp [Ob]; positivity
  have hOp : 0 ≤ Op := allocatedSlicedGridResourceLog_nonneg m dim hD hp hv hEg
  have hOpR : Op ≤ Ob := (hgrid hD hp hv hEg).trans
    (pow_le_pow_left₀ (by positivity) (by linarith only [hDR, hpR, hvR, hEgR]) b)
  let Plb := (((m + 2) * dim + m + 4 : ℕ) : ℝ) + R + R * Ob + 2 * R + 2
  have hPlb : 0 ≤ Plb := by dsimp [Plb]; positivity
  have hPl : 0 ≤ Plong := by dsimp [Plong]; positivity
  have hPlR : Plong ≤ Plb := by
    have hm : (axes : ℝ) * max Op 0 ≤ R * Ob := by
      rw [max_eq_left hOp]
      exact mul_le_mul (haxes.trans hDR) hOpR hOp hR
    dsimp only [Plong, Plb]
    push_cast
    linarith only [hPrhoR, htR, hFR, hm]
  let Qb := allocatedFiniteIdealProfileLog R Plb
  have hQb : 0 ≤ Qb := (allocatedFiniteIdeal_budget_nonneg m hR hPlb (le_refl (0 : ℝ))).1
  have hQ : 0 ≤ Q := (idealSiteLogBudget_bounds outputs dim hPl).1
  have hQR : Q ≤ Qb := by
    apply (idealSiteLogBudget_le_finite_profile hPl hout hdim hprofile).trans
    change allocatedFiniteIdealProfileLog D Plong ≤ allocatedFiniteIdealProfileLog R Plb
    unfold allocatedFiniteIdealProfileLog
    gcongr
  have hmass : 2 * (2 : ℝ) ^ dim + F + (2 : ℝ) ^ dim * (ambient * ((m + 1 : ℕ) * Pk)) +
      ((2 : ℝ) ^ dim * axes * (4 * Q + 8) + Q) + gridaxes * Op ≤
      2 * (2 : ℝ) ^ dim + R + (2 : ℝ) ^ dim * (R * ((m + 1 : ℕ) * R)) +
      ((2 : ℝ) ^ dim * R * (4 * Qb + 8) + Qb) + R * Ob := by
    gcongr
    · exact hamb.trans hDR
    · exact haxes.trans hDR
    · exact hgridaxes.trans hDR
  apply hmass.trans
  simpa [poly, X, O, Pbox, Pl, Qp, Ob, Plb, Qb, allocatedFiniteIdealProfileLog,
    Polynomial.eval₂_pow] using hbound R hR

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem exists_allocatedAffineAnalytic_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p v F Prho Pk target B : ℝ},
      0 ≤ D → 0 ≤ p → 0 ≤ v → 0 ≤ F → 0 ≤ Prho → 0 ≤ Pk → 0 ≤ target → 0 ≤ B →
      ∀ (outputs axes : ℕ), (outputs : ℝ) ≤ D → (axes : ℝ) ≤ D →
      (dim : ℝ) ≤ D → (probabilityProfileLipschitz : ℝ) ≤ D →
      let Eg := outputs * Prho + (target + F) + 1
      let Op := allocatedSlicedGridResourceLog m dim D p v Eg
      let Plong := ((m : ℝ) + 2) * dim + m + 4 + Prho + axes * max Op 0 + (target + F) + 2
      let Q := idealSiteLogBudget outputs dim Plong
      10 * B + 6 * Q + 2 * ((m + 1 : ℕ) * Pk) + (2 * B + 1) * Op + 19 ≤
        (D + p + v + F + Prho + Pk + target + B + A) ^ A := by
  obtain ⟨b, hb, hgrid⟩ := exists_allocatedSlicedGridResource_budget m dim
  let X : Polynomial ℕ := Polynomial.X
  let O : Polynomial ℕ := (3 * X + (X ^ 2 + 2 * X + 1) + Polynomial.C b) ^ b
  let Pbox : Polynomial ℕ := Polynomial.C ((m + 2) * dim + m + 4)
  let Pl : Polynomial ℕ := Pbox + X + X * O + 2 * X + 2
  let Qp := allocatedFiniteIdealProfileLog X Pl
  let poly : Polynomial ℕ := 10 * X + 6 * Qp + 2 * ((m + 1 : ℕ) * X) + (2 * X + 1) * O + 19
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D p v F Prho Pk target B hD hp hv hF hPrho hPk htarget hB outputs axes
    hout haxes hdim hprofile Eg Op Plong Q
  let R := D + p + v + F + Prho + Pk + target + B
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hBR : B ≤ R := by dsimp [R]; linarith
  have hDR : D ≤ R := by dsimp [R]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hvR : v ≤ R := by dsimp [R]; linarith
  have hFR : F ≤ R := by dsimp [R]; linarith
  have hPrhoR : Prho ≤ R := by dsimp [R]; linarith
  have hPkR : Pk ≤ R := by dsimp [R]; linarith
  have htR : target ≤ R := by dsimp [R]; linarith
  have hEg : 0 ≤ Eg := by dsimp [Eg]; positivity
  have hEgR : Eg ≤ R ^ 2 + 2 * R + 1 := by
    have hprod := mul_le_mul (hout.trans hDR) hPrhoR hPrho hR
    dsimp only [Eg]
    nlinarith only [hprod, htR, hFR]
  let Ob := (3 * R + (R ^ 2 + 2 * R + 1) + b) ^ b
  have hOb : 0 ≤ Ob := by dsimp [Ob]; positivity
  have hOp : 0 ≤ Op := allocatedSlicedGridResourceLog_nonneg m dim hD hp hv hEg
  have hOpR : Op ≤ Ob := (hgrid hD hp hv hEg).trans
    (pow_le_pow_left₀ (by positivity) (by linarith only [hDR, hpR, hvR, hEgR]) b)
  let Plb := (((m + 2) * dim + m + 4 : ℕ) : ℝ) + R + R * Ob + 2 * R + 2
  have hPlb : 0 ≤ Plb := by dsimp [Plb]; positivity
  have hPl : 0 ≤ Plong := by dsimp [Plong]; positivity
  have hPlR : Plong ≤ Plb := by
    have hm : (axes : ℝ) * max Op 0 ≤ R * Ob := by
      rw [max_eq_left hOp]
      exact mul_le_mul (haxes.trans hDR) hOpR hOp hR
    dsimp only [Plong, Plb]
    push_cast
    linarith only [hPrhoR, htR, hFR, hm]
  let Qb := allocatedFiniteIdealProfileLog R Plb
  have hQb : 0 ≤ Qb := (allocatedFiniteIdeal_budget_nonneg m hR hPlb (le_refl (0 : ℝ))).1
  have hQ : 0 ≤ Q := (idealSiteLogBudget_bounds outputs dim hPl).1
  have hQR : Q ≤ Qb := by
    apply (idealSiteLogBudget_le_finite_profile hPl hout hdim hprofile).trans
    change allocatedFiniteIdealProfileLog D Plong ≤ allocatedFiniteIdealProfileLog R Plb
    unfold allocatedFiniteIdealProfileLog
    gcongr
  have hcost : 10 * B + 6 * Q + 2 * ((m + 1 : ℕ) * Pk) + (2 * B + 1) * Op + 19 ≤
      10 * R + 6 * Qb + 2 * ((m + 1 : ℕ) * R) + (2 * R + 1) * Ob + 19 := by
    gcongr
  apply hcost.trans
  simpa [poly, X, O, Pbox, Pl, Qp, Ob, Plb, Qb, allocatedFiniteIdealProfileLog,
    Polynomial.eval₂_pow] using hbound R hR

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators Matrix

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ} {E : Fin m → Type*} {N : ℕ}

noncomputable def modularDeckPolynomial (r : CoefficientDeckResidues (K := K) E N)
    (j : Fin m) (i : E j) : MvPolynomial K (ZMod N) :=
  modularBoundedCoefficientPolynomial (j.val + 1) (fun e => r j e i)

theorem modularDeckPolynomial_degree (r : CoefficientDeckResidues (K := K) E N)
    (j : Fin m) (i : E j) : (modularDeckPolynomial r j i).totalDegree ≤ j.val + 1 := by
  apply totalDegree_finsetSum_le
  intro e _
  exact (totalDegree_monomial_le e.val (r j e i)).trans e.property

noncomputable def resampleCoefficientDeckCoordinate {A : Type*}
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m) (i : E j)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (c : A → ZMod N) :
    CoefficientDeckResidues (K := K) E N :=
  Function.update r j (fun e => Function.update (r j e) i
    (Function.extend slot c (fun e => r j e i) e))

omit [Fintype K] in
theorem resampleCoefficientDeckCoordinate_apply {A : Type*}
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m) (i : E j)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (c : A → ZMod N)
    (e : BoundedCoefficientExponent K (j.val + 1)) :
    resampleCoefficientDeckCoordinate r j i slot c j e i =
      Function.extend slot c (fun e => r j e i) e := by
  simp only [resampleCoefficientDeckCoordinate, Function.update_self]

theorem modularDeckPolynomial_resample_top {A : Type*} [Fintype A]
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m) (i : E j)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (hinj : Function.Injective slot)
    (hdegree : ∀ a, (slot a).val.degree = j.val + 1) (c : A → ZMod N) :
    homogeneousComponent (j.val + 1)
      (modularDeckPolynomial (resampleCoefficientDeckCoordinate r j i slot c) j i) =
      homogeneousComponent (j.val + 1)
        (modularUnselectedCoefficientPolynomial (j.val + 1) slot (fun e => r j e i)) +
      ∑ a, MvPolynomial.monomial (slot a).val (c a) := by
  simp only [modularDeckPolynomial, resampleCoefficientDeckCoordinate_apply]
  exact modularBoundedCoefficientPolynomial_selected_top _ slot hinj hdegree _ c

end VectorPolynomial

variable {D G A : Type*} {B : D → Type*} {h : ℕ}

theorem samplerLongEmbedding_kernelExponent (inactive : D → Prop) (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) :
    ((kernelRankCoefficientSlot (G := G)
      (B := fun d : {d // ¬ inactive d} => B d.val) (fun d => degree d.val) e a).val).mapDomain
        (samplerLongEmbedding inactive degree) =
      (kernelRankCoefficientSlot (B := B) degree e a).val := by
  simp only [kernelRankCoefficientSlot, productBlockExponent,
    Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single,
    kernelRankBlockEmbedding_apply, samplerLongEmbedding_common]

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {E : Fin m → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)] [Fintype A]
    {N : ℕ}

theorem modularDeckPolynomial_kernel_resample_long_top
    (inactive : LayerSamplerAxis I n → Prop)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (j : Fin m) (i : E j) (e : A × Fin (j.val + 1) ↪ G) (c : A → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N) :
    homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularDeckPolynomial (resampleCoefficientDeckCoordinate r j i
          (kernelRankCoefficientSlot (layerSamplerDegree I n) e) c) j i)) =
      killCompl (allocatedLongEmbedding inactive).injective
        (homogeneousComponent (j.val + 1)
          (modularUnselectedCoefficientPolynomial (j.val + 1)
            (kernelRankCoefficientSlot (layerSamplerDegree I n) e) (fun q => r j q i))) +
      ∑ a, c a • ∏ k ∈ kernelRankBlock
        (B := fun d : {d : LayerSamplerAxis I n // ¬ inactive d} => B d.val)
        (fun d => layerSamplerDegree I n d.val) e a, X k := by
  rw [homogeneousComponent_conditionPolynomial_top _ _ _ v _
    (modularDeckPolynomial_degree _ j i)]
  rw [modularDeckPolynomial_resample_top r j i _
    (kernelRankCoefficientSlot_injective _ e (Nat.zero_lt_succ _))
    (kernelRankCoefficientSlot_degree _ e), map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change killCompl (samplerLongEmbedding inactive (layerSamplerDegree I n)).injective
    (MvPolynomial.monomial (kernelRankCoefficientSlot (layerSamplerDegree I n) e a).val (c a)) = _
  rw [← samplerLongEmbedding_kernelExponent inactive (layerSamplerDegree I n) e a,
    killCompl_monomial_mapDomain, kernelRankCoefficientSlot_monomial]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {K A : Type*} {m : ℕ} {E : Fin m → Type*} {N : ℕ}

abbrev CoefficientDeckScalarIndex (K : Type*) (E : Fin m → Type*) :=
  Σ j : Fin m, BoundedCoefficientExponent K (j.val + 1) × E j

def coefficientDeckScalarEquiv :
    CoefficientDeckResidues (K := K) E N ≃ (CoefficientDeckScalarIndex K E → ZMod N) where
  toFun r t := r t.1 t.2.1 t.2.2
  invFun f j e i := f ⟨j, e, i⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype K] [Fintype A] [∀ j, Fintype (E j)] [NeZero N]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev AllocatedProjectionCoefficientIndex (K : Type*) (I : Fin m → Type*) (n : Fin m → ℕ) :=
  Σ a : LayerSamplerAxis I n, BoundedCoefficientExponent K (a.1.val + 1)

abbrev AllocatedActualCoefficientIndex (G X : Type*) (I E : Fin m → Type*)
    (n : Fin m → ℕ) (B : LayerSamplerAxis I n → Type*) :=
  (Option (LayerSamplerVariables G I n B) × X) ⊕
    (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E ⊕
      AllocatedProjectionCoefficientIndex (LayerSamplerVariables G I n B) I n)

abbrev AllocatedSelectedCoefficientIndex (X : Type*) (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :=
  Σ j : Fin m, AllocatedTaggedRankOutput X E inactive j × Fin L

noncomputable def allocatedActualCoefficientSlot
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedSelectedCoefficientIndex X E inactive L → AllocatedActualCoefficientIndex G X I E n B
  | ⟨_j, .inl x, l⟩ => .inl (some (.inl (spatial l)), x.val)
  | ⟨j, .inr (.inl i), l⟩ => .inr (.inl ⟨j,
      kernelRankCoefficientSlot (layerSamplerDegree I n) (kernel j) l, i⟩)
  | ⟨j, .inr (.inr a), l⟩ => .inr (.inr ⟨⟨j, a.val⟩,
      principalCoefficientSlot (layerSamplerDegree I n) ⟨j, a.val⟩ (block j a l)⟩)

theorem allocatedActualCoefficientSlot_injective
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩) :
    Function.Injective (allocatedActualCoefficientSlot (X := X) (E := E) inactive spatial kernel block) := by
  rintro ⟨j, o, l⟩ ⟨k, p, q⟩ he
  cases o with
  | inl x =>
    cases p with
    | inl y =>
      have hjk : j = k := Fin.ext (x.property.trans y.property.symm)
      subst k
      change Sum.inl (some (Sum.inl (spatial l)), x.val) =
        Sum.inl (some (Sum.inl (spatial q)), y.val) at he
      have hp := Sum.inl.inj he
      have hl : l = q := spatial.injective
        (Sum.inl.inj (Option.some.inj (congrArg Prod.fst hp)))
      have hxy : x = y := Subtype.ext (congrArg Prod.snd hp)
      subst q
      subst y
      rfl
    | inr p => cases p <;> cases he
  | inr o =>
    cases p with
    | inl y => cases o <;> cases he
    | inr p =>
      cases o with
      | inl i =>
        cases p with
        | inl t =>
          have hh := Sum.inl.inj (Sum.inr.inj he)
          have hjk : j = k := congrArg Sigma.fst hh
          subst k
          have hp : (kernelRankCoefficientSlot (B := B) (layerSamplerDegree I n) (kernel j) l, i) =
              (kernelRankCoefficientSlot (B := B) (layerSamplerDegree I n) (kernel j) q, t) := by
            simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hh
          have hl : l = q := kernelRankCoefficientSlot_injective
            (layerSamplerDegree I n) (kernel j) (Nat.zero_lt_succ _) (congrArg Prod.fst hp)
          have hit : i = t := congrArg Prod.snd hp
          subst q
          subst t
          rfl
        | inr a => cases he
      | inr a =>
        cases p with
        | inl t => cases he
        | inr b =>
          have hh := Sum.inr.inj (Sum.inr.inj he)
          have haxis : (⟨j, a.val⟩ : LayerSamplerAxis I n) = ⟨k, b.val⟩ := congrArg Sigma.fst hh
          have hjk : j = k := congrArg Sigma.fst haxis
          subst k
          have hab : a = b := Subtype.ext (by
            simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using haxis)
          subst b
          have hslot : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, a.val⟩
              (block j a l) = principalCoefficientSlot (layerSamplerDegree I n) ⟨j, a.val⟩
              (block j a q) := by
            exact eq_of_heq (Sigma.mk.inj hh).2
          have hblocks := principalCoefficientSlot_injective (G := G)
            (layerSamplerDegree I n) ⟨j, a.val⟩ (Nat.zero_lt_succ _) hslot
          have hl : l = q := (block j a).injective hblocks
          subst q
          rfl

noncomputable def allocatedActualCoefficientEmbedding
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedSelectedCoefficientIndex X E inactive L ↪ AllocatedActualCoefficientIndex G X I E n B :=
  ⟨allocatedActualCoefficientSlot inactive spatial kernel block,
    allocatedActualCoefficientSlot_injective inactive spatial kernel block⟩

variable {R : Type*}

def allocatedReadNoise (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    Option (LayerSamplerVariables G I n B) × X → R :=
  fun t => f (.inl t)

def allocatedReadDeck (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    ∀ j : Fin m, BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → R :=
  fun j e i => f (.inr (.inl ⟨j, e, i⟩))

def allocatedReadProjection (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    ∀ a : LayerSamplerAxis I n,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (a.1.val + 1) → R :=
  fun a e => f (.inr (.inr ⟨a, e⟩))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {K A : Type*} {m : ℕ} {E : Fin m → Type*} {N : ℕ}

variable [Fintype K] [Fintype A] [∀ j, Fintype (E j)] [NeZero N]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)] {N L : ℕ} [NeZero N]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev AllocatedCongruenceCoefficientIndex (X : Type*) (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :=
  Σ j : Fin m, AllocatedCongruenceRankOutput X E inactive j × Fin L

abbrev AllocatedSmoothRankCoefficientIndex (X : Type*)
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :=
  Σ j : Fin m, (SpatialDegreeOutput X j ⊕ AllocatedCongruenceIntegerAxis inactive j) × Fin L

abbrev AllocatedDeckRankCoefficientIndex (E : Fin m → Type*) (L : ℕ) :=
  Σ j : Fin m, E j × Fin L

def allocatedCongruenceCoefficientSplit (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    AllocatedCongruenceCoefficientIndex X E inactive L ≃
      AllocatedSmoothRankCoefficientIndex X inactive L ⊕ AllocatedDeckRankCoefficientIndex E L where
  toFun k := match k with
    | ⟨j,.inl x,l⟩ => .inl ⟨j,.inl x,l⟩
    | ⟨j,.inr (.inl e),l⟩ => .inr ⟨j,e,l⟩
    | ⟨j,.inr (.inr i),l⟩ => .inl ⟨j,.inr i,l⟩
  invFun k := match k with
    | .inl ⟨j,.inl x,l⟩ => ⟨j,.inl x,l⟩
    | .inr ⟨j,e,l⟩ => ⟨j,.inr (.inl e),l⟩
    | .inl ⟨j,.inr i,l⟩ => ⟨j,.inr (.inr i),l⟩
  left_inv := by rintro ⟨j,(x | e | i),l⟩ <;> rfl
  right_inv := by rintro (⟨j,(x | i),l⟩ | ⟨j,e,l⟩) <;> rfl

def allocatedCongruenceCoefficientEmbedding (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    AllocatedCongruenceCoefficientIndex X E inactive L ↪
      AllocatedSelectedCoefficientIndex X E inactive L :=
  Function.Embedding.sigmaMap (Function.Embedding.refl _)
    (fun j => Function.Embedding.prodMap (allocatedCongruenceOutputEmbedding inactive j)
      (Function.Embedding.refl _))

noncomputable def allocatedCongruenceActualCoefficientEmbedding
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedCongruenceCoefficientIndex X E inactive L ↪ AllocatedActualCoefficientIndex G X I E n B :=
  (allocatedCongruenceCoefficientEmbedding inactive L).trans
    (allocatedActualCoefficientEmbedding inactive spatial kernel block)

noncomputable def allocatedMixedSelectedValues (inactive : LayerSamplerAxis I n → Prop)
    {L N : ℕ} (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    AllocatedCongruenceCoefficientIndex X E inactive L → ℤ :=
  Sum.elim x (fun j => (deck j).val) ∘ allocatedCongruenceCoefficientSplit inactive L

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

def AllocatedRankComponentCoefficient
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    AllocatedCongruenceRankOutput X E inactive j → Type _
  | .inl _ => Option (LayerSamplerVariables G I n B)
  | .inr _ => BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)

abbrev AllocatedRankComponentCoefficientIndex
    (G X : Type*) (I E : Fin m → Type*) (n : Fin m → ℕ)
    (B : LayerSamplerAxis I n → Type*) (inactive : LayerSamplerAxis I n → Prop) :=
  Σ t : (Σ j : Fin m, AllocatedCongruenceRankOutput X E inactive j),
    AllocatedRankComponentCoefficient (G := G) (B := B) inactive t.1 t.2

def allocatedRankComponentCoefficientSlot
    (inactive : LayerSamplerAxis I n → Prop) :
    AllocatedRankComponentCoefficientIndex G X I E n B inactive →
      AllocatedActualCoefficientIndex G X I E n B
  | ⟨⟨_j, .inl x⟩, q⟩ => .inl (q, x.val)
  | ⟨⟨j, .inr (.inl i)⟩, q⟩ => .inr (.inl ⟨j, q, i⟩)
  | ⟨⟨j, .inr (.inr i)⟩, q⟩ => .inr (.inr ⟨⟨j, .inr i.val⟩, q⟩)

theorem allocatedRankComponentCoefficientSlot_injective
    (inactive : LayerSamplerAxis I n → Prop) :
    Function.Injective
      (allocatedRankComponentCoefficientSlot (G := G) (X := X) (E := E) (B := B) inactive) := by
  rintro ⟨⟨j, o⟩, q⟩ ⟨⟨k, p⟩, r⟩ he
  cases o with
  | inl x =>
    cases p with
    | inl y =>
      have hjk : j = k := Fin.ext (x.property.trans y.property.symm)
      subst k
      have hp : (q, x.val) = (r, y.val) := Sum.inl.inj he
      have hxy : x = y := Subtype.ext (congrArg Prod.snd hp)
      subst y
      have hqr : q = r := congrArg Prod.fst hp
      subst r
      rfl
    | inr p => cases p <;> cases he
  | inr o =>
    cases p with
    | inl y => cases o <;> cases he
    | inr p =>
      cases o with
      | inl i =>
        cases p with
        | inl t =>
          have hh := Sum.inl.inj (Sum.inr.inj he)
          have hjk : j = k := congrArg Sigma.fst hh
          subst k
          have hp : (q, i) = (r, t) := by
            simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and,
              AllocatedRankComponentCoefficient] using hh
          have hit : i = t := congrArg Prod.snd hp
          subst t
          have hqr : q = r := congrArg Prod.fst hp
          subst r
          rfl
        | inr a => cases he
      | inr a =>
        cases p with
        | inl t => cases he
        | inr b =>
          have hh := Sum.inr.inj (Sum.inr.inj he)
          have haxis : (⟨j, .inr a.val⟩ : LayerSamplerAxis I n) = ⟨k, .inr b.val⟩ :=
            congrArg Sigma.fst hh
          have hjk : j = k := congrArg Sigma.fst haxis
          subst k
          have hab : a = b := Subtype.ext (by
            apply Sum.inr.inj
            exact eq_of_heq (Sigma.mk.inj haxis).2)
          subst b
          have hqr : q = r := eq_of_heq (Sigma.mk.inj hh).2
          subst r
          rfl

def allocatedRankComponentCoefficientEmbedding
    (inactive : LayerSamplerAxis I n → Prop) :
    AllocatedRankComponentCoefficientIndex G X I E n B inactive ↪
      AllocatedActualCoefficientIndex G X I E n B :=
  ⟨allocatedRankComponentCoefficientSlot inactive,
    allocatedRankComponentCoefficientSlot_injective inactive⟩

noncomputable def allocatedRankComponentSelectedSlot
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (j : Fin m) : (o : AllocatedCongruenceRankOutput X E inactive j) →
      Fin L → AllocatedRankComponentCoefficient (G := G) (B := B) inactive j o
  | .inl _ => spatialKernelRankSlot spatial
  | .inr (.inl _) => kernelRankCoefficientSlot (layerSamplerDegree I n) (kernel j)
  | .inr (.inr i) => canonicalPrincipalSubblockSlot (layerSamplerDegree I n)
      ⟨j, .inr i.val⟩ (block j (allocatedCongruenceIntegerEmbedding inactive j i))

theorem allocatedRankComponentSelectedSlot_injective
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j) :
    Function.Injective (allocatedRankComponentSelectedSlot inactive spatial kernel block j o) := by
  rcases o with x | i | a
  · exact spatialKernelRankSlot_injective spatial
  · exact kernelRankCoefficientSlot_injective (layerSamplerDegree I n) (kernel j)
      (Nat.zero_lt_succ _)
  · exact canonicalPrincipalSubblockSlot_injective (layerSamplerDegree I n)
      ⟨j, .inr a.val⟩ (Nat.zero_lt_succ _)
      (block j (allocatedCongruenceIntegerEmbedding inactive j a))

noncomputable def allocatedRankComponentSelectedEmbedding
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j) :
    Fin L ↪ AllocatedRankComponentCoefficient (G := G) (B := B) inactive j o :=
  ⟨allocatedRankComponentSelectedSlot inactive spatial kernel block j o,
    allocatedRankComponentSelectedSlot_injective inactive spatial kernel block j o⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

def allocatedMixedCoefficientEquiv (inactive : LayerSamplerAxis I n → Prop) (L : ℕ)
    (R : Type*) [AddCommGroup R] :
    ((AllocatedSmoothRankCoefficientIndex X inactive L ⊕ AllocatedDeckRankCoefficientIndex E L) → R) ≃+
      (AllocatedCongruenceCoefficientIndex X E inactive L → R) where
  toFun f := f ∘ allocatedCongruenceCoefficientSplit inactive L
  invFun f := f ∘ (allocatedCongruenceCoefficientSplit inactive L).symm
  left_inv f := by funext j; simp only [Function.comp_apply, Equiv.apply_symm_apply]
  right_inv f := by funext j; simp only [Function.comp_apply, Equiv.symm_apply_apply]
  map_add' _ _ := rfl

noncomputable local instance congruenceIndexFintype [Fintype X] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    Fintype (AllocatedCongruenceCoefficientIndex X E inactive L) := inferInstance

noncomputable local instance congruenceIndexDecidableEq
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    DecidableEq (AllocatedCongruenceCoefficientIndex X E inactive L) := Classical.decEq _

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedModularRankTaggedPolynomials
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

noncomputable def allocatedDegreeRankPolynomial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (c : AllocatedDegreeRankOutput E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N) :
    AllocatedDegreeRankOutput E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)
  | .inl i => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularDeckPolynomial (resampleCoefficientDeckCoordinate r j i
          (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel) (c (.inl i))) j i))
  | .inr a => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (j.val + 1)
          (Function.extend (canonicalPrincipalSubblockSlot (layerSamplerDegree I n)
            ⟨j,a.val⟩ (block a)) (c (.inr a)) (projection a))))

noncomputable def allocatedDegreeRankResidual
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedDegreeRankOutput E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)
  | .inl i => killCompl (allocatedLongEmbedding inactive).injective
      (homogeneousComponent (j.val + 1)
        (modularUnselectedCoefficientPolynomial (j.val + 1)
          (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel) (fun q => r j q i)))
  | .inr a => canonicalSelectedLongTopResidual inactive (layerSamplerDegree I n)
      (allocatedDegreeLongAxis inactive j a) (block a) (projection a)

theorem allocatedDegreeRankPolynomial_eq_designated
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (c : AllocatedDegreeRankOutput E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedDegreeRankOutput E inactive j) :
    allocatedDegreeRankPolynomial inactive j r projection kernel block c v o =
      designatedVectorComponent (allocatedDegreeRankBlock inactive j kernel block)
        (allocatedDegreeRankResidual inactive j r projection kernel block) c o := by
  cases o with
  | inl i =>
    exact modularDeckPolynomial_kernel_resample_long_top inactive r j i kernel (c (.inl i)) v
  | inr a =>
    exact allocatedBoundedCoefficient_selected_long_top inactive
      (allocatedDegreeLongAxis inactive j a) (block a) (projection a) (c (.inr a)) v

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

noncomputable def allocatedTaggedRankPolynomial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (c : AllocatedTaggedRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N) :
    AllocatedTaggedRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)
  | .inl x => homogeneousComponent 1
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (spatialRankPolynomial (Function.extend (spatialKernelRankSlot spatial)
          (c (.inl x)) (fun d => noise (d,x.val)))))
  | .inr o => allocatedDegreeRankPolynomial inactive j r projection kernel block
      (fun o => c (.inr o)) v o

noncomputable def allocatedTaggedRankResidual
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedTaggedRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)
  | .inl x => killCompl (allocatedLongEmbedding inactive).injective
      (homogeneousComponent 1
        (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range
          (spatialKernelRankSlot (P := PrincipalTupleIndex B (layerSamplerDegree I n)) spatial)),
          MvPolynomial.monomial (spatialRankExponent d) (noise (d,x.val))))
  | .inr o => allocatedDegreeRankResidual inactive j r projection kernel block o

theorem allocatedTaggedRankPolynomial_eq_designated
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (c : AllocatedTaggedRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedTaggedRankOutput X E inactive j) :
    allocatedTaggedRankPolynomial inactive j noise r projection spatial kernel block c v o =
      designatedVectorComponent (allocatedTaggedRankBlock inactive j spatial kernel block)
        (allocatedTaggedRankResidual inactive j noise r projection spatial kernel block) c o := by
  cases o with
  | inl x =>
    have h := allocatedSpatialRankPolynomial_kernel_selected_long inactive spatial
      (fun d => noise (d,x.val)) (c (.inl x)) v
    simpa only [allocatedTaggedRankPolynomial, designatedVectorComponent,
      allocatedTaggedRankResidual, allocatedTaggedRankBlock,
      allocatedSpatialRankBlock_product] using h
  | inr o =>
    simpa only [allocatedTaggedRankPolynomial, designatedVectorComponent,
      allocatedTaggedRankBlock, allocatedTaggedRankResidual] using
      allocatedDegreeRankPolynomial_eq_designated inactive j r projection kernel block
        (fun o => c (.inr o)) v o

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankActualRead
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem extend_selected_original {A K R : Type*} (slot : A → K)
    (hinj : Function.Injective slot) (c : K → R) :
    Function.extend slot (fun a => c (slot a)) c = c := by
  funext k
  by_cases hk : k ∈ Set.range slot
  · obtain ⟨a,rfl⟩ := hk
    exact hinj.extend_apply _ _ a
  · exact Function.extend_apply' _ _ k hk

namespace VectorPolynomial
variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

noncomputable def allocatedSelectedRankCoefficients
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedTaggedRankOutput X E inactive j → Fin L → ZMod N
  | .inl x, l => noise (spatialKernelRankSlot spatial l,x.val)
  | .inr (.inl i), l => r j (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel l) i
  | .inr (.inr a), l => projection a
      (canonicalPrincipalSubblockSlot (layerSamplerDegree I n) ⟨j,a.val⟩ (block a) l)

noncomputable def allocatedOriginalTaggedTop
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N) :
    AllocatedTaggedRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)
  | .inl x => homogeneousComponent 1
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (spatialRankPolynomial (fun d => noise (d,x.val))))
  | .inr (.inl i) => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v (modularDeckPolynomial r j i))
  | .inr (.inr a) => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (j.val + 1) (projection a)))

theorem allocatedTaggedRankPolynomial_original
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedTaggedRankOutput X E inactive j) :
    allocatedTaggedRankPolynomial inactive j noise r projection spatial kernel block
      (allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block) v o =
        allocatedOriginalTaggedTop inactive j noise r projection v o := by
  rcases o with x | i | a
  · have hs : allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block
        (.inl x) = fun l => noise (spatialKernelRankSlot spatial l,x.val) := by
      funext l
      rfl
    simp only [allocatedTaggedRankPolynomial, allocatedOriginalTaggedTop, hs]
    rw [extend_selected_original _ (spatialKernelRankSlot_injective spatial) (fun d => noise (d,x.val))]
  · have hs : allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block
        (.inr (.inl i)) = fun l => r j (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel l) i := by
      funext l
      rfl
    simp only [allocatedTaggedRankPolynomial, allocatedDegreeRankPolynomial,
      allocatedOriginalTaggedTop, modularDeckPolynomial, resampleCoefficientDeckCoordinate_apply, hs]
    rw [extend_selected_original _ (kernelRankCoefficientSlot_injective
      (layerSamplerDegree I n) kernel (Nat.zero_lt_succ _)) (fun q => r j q i)]
  · have hs : allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block
        (.inr (.inr a)) = fun l => projection a
          (canonicalPrincipalSubblockSlot (layerSamplerDegree I n) ⟨j,a.val⟩ (block a) l) := by
      funext l
      rfl
    simp only [allocatedTaggedRankPolynomial, allocatedDegreeRankPolynomial,
      allocatedOriginalTaggedTop, hs]
    exact congrArg
      (fun coefficients : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N =>
        homogeneousComponent (j.val + 1)
          (conditionPolynomial (allocatedLongEmbedding inactive)
            (allocatedLongEmbedding inactive).injective v
            (modularBoundedCoefficientPolynomial (j.val + 1) coefficients)))
      (extend_selected_original _ (canonicalPrincipalSubblockSlot_injective
        (G := G) (layerSamplerDegree I n) ⟨j,a.val⟩ (Nat.zero_lt_succ _) (block a)) (projection a))

theorem allocatedOriginalTaggedTop_eq_designated
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedTaggedRankOutput X E inactive j) :
    allocatedOriginalTaggedTop inactive j noise r projection v o =
      designatedVectorComponent (allocatedTaggedRankBlock inactive j spatial kernel block)
        (allocatedTaggedRankResidual inactive j noise r projection spatial kernel block)
        (allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block) o := by
  rw [← allocatedTaggedRankPolynomial_original inactive j noise r projection spatial kernel block v o]
  exact allocatedTaggedRankPolynomial_eq_designated inactive j noise r projection spatial kernel block _ v o

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    {N L : ℕ}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankBadProduct
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

section RingMap

variable {K L A R S : Type*} [CommRing R] [CommRing S]

end RingMap

section ActualResidual

variable {D G R S : Type*} {B : D → Type*} [Fintype D] [Fintype G]
    [∀ d, Fintype (B d)] [CommRing R] [CommRing S]

end ActualResidual
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {L : ℕ}

noncomputable def allocatedTaggedRankIntegerResidual
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedTaggedRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) ℤ
  | .inl x => killCompl (allocatedLongEmbedding inactive).injective
      (homogeneousComponent 1
        (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range
          (spatialKernelRankSlot (P := PrincipalTupleIndex B (layerSamplerDegree I n)) spatial)),
          MvPolynomial.monomial (spatialRankExponent d) (noise (d,x.val))))
  | .inr (.inl i) => killCompl (allocatedLongEmbedding inactive).injective
      (homogeneousComponent (j.val + 1)
        (modularUnselectedCoefficientPolynomial (j.val + 1)
          (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel) (fun q => r j q i)))
  | .inr (.inr a) => canonicalSelectedLongTopResidual inactive (layerSamplerDegree I n)
      (allocatedDegreeLongAxis inactive j a) (block a) (projection a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable def allocatedCongruenceRankPolynomial {N L : ℕ}
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (c : AllocatedCongruenceRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N) :=
  allocatedTaggedRankPolynomial inactive j noise r projection spatial kernel block
    (Function.extend (allocatedCongruenceOutputEmbedding inactive j) c (fun _ _ => 0)) v
    (allocatedCongruenceOutputEmbedding inactive j o)

noncomputable def allocatedCongruenceRankFailureProbability {N L : ℕ} [NeZero N]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (c : AllocatedCongruenceRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod N) : ℝ :=
  𝔼 u : Fin j.val → LayerSamplerLongVariables inactive G B → ZMod N,
    if polynomialLinearRow (polynomialIterDifference j.val
      (∑ o, w o • allocatedCongruenceRankPolynomial inactive j noise r projection
        spatial kernel block c v o) u) = 0 then 1 else 0

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

abbrev AllocatedCongruenceScalarIndex (X : Type*) (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :=
  Σ j : Fin m, AllocatedCongruenceRankOutput X E inactive j × Fin L

def allocatedCongruenceRankBlockFamily (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩) :
    ∀ j, AllocatedCongruenceRankOutput X E inactive j → Fin L →
      Finset (LayerSamplerLongVariables inactive G B) :=
  fun j o => allocatedTaggedRankBlock inactive j spatial (kernel j) (block j)
    (allocatedCongruenceOutputEmbedding inactive j o)

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable def allocatedCongruenceRankIntegerResidualFamily
    (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩) :
    ∀ j, AllocatedCongruenceRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) ℤ :=
  fun j o => allocatedTaggedRankIntegerResidual inactive j noise r (projection j)
    spatial (kernel j) (block j) (allocatedCongruenceOutputEmbedding inactive j o)

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

local notation "rankS" => allocatedCongruenceRankBlockFamily (X := X) (E := E) inactive spatial kernel block
local notation "rankQ" => allocatedCongruenceRankIntegerResidualFamily inactive noise r projection spatial kernel block

def allocatedCongruenceModulusBad (C : ℝ) (N : ℕ) [NeZero N]
    (x : AllocatedCongruenceScalarIndex X E inactive L → ZMod N) : Prop :=
  ∃ v : LayerSamplerVariables G I n B → ZMod N, ∃ j : Fin m,
    ∃ w : AllocatedCongruenceRankOutput X E inactive j → ZMod N,
      (∃ o, IsUnit (w o)) ∧ (N : ℝ) ^ (-C) <
        allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod N))
          (fun j q i => (r j q i : ZMod N)) (fun b q => (projection j b q : ZMod N))
          spatial (kernel j) (block j) (fun o l => x ⟨j,(o,l)⟩) v w

def allocatedCongruenceRankBad (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) :
    ℕ → ℕ → (AllocatedCongruenceScalarIndex X E inactive L → ℤ) → Prop :=
  smoothResiduePrimeBad P (fun p a =>
    allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C (p.val ^ a))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)]
    [∀ a, Fintype (B a)] {N L : ℕ}

theorem allocatedCongruenceRankPolynomial_original
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    allocatedCongruenceRankPolynomial inactive j noise r projection spatial kernel block
      (fun z => allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block
        (allocatedCongruenceOutputEmbedding inactive j z)) v o =
      allocatedOriginalTaggedTop inactive j noise r projection v
        (allocatedCongruenceOutputEmbedding inactive j o) := by
  rw [allocatedCongruenceRankPolynomial, allocatedTaggedRankPolynomial_eq_designated,
    allocatedOriginalTaggedTop_eq_designated inactive j noise r projection spatial kernel block]
  simp only [designatedVectorComponent,
    (allocatedCongruenceOutputEmbedding (X := X) (E := E) inactive j).injective.extend_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

local notation "rankS" => allocatedCongruenceRankBlockFamily (X := X) (E := E) inactive spatial kernel block
local notation "rankQ" => allocatedCongruenceRankIntegerResidualFamily inactive noise r projection spatial kernel block

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankActualRefreshBad
namespace OAI

section

namespace Erdos3

end Erdos3

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

def allocatedCongruenceCoefficientReindex
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    ((Σ j : Fin m, AllocatedCongruenceRankOutput X E inactive j) × Fin L) ≃
      AllocatedCongruenceCoefficientIndex X E inactive L where
  toFun k := ⟨k.1.1, k.1.2, k.2⟩
  invFun k := (⟨k.1,k.2.1⟩,k.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (c : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)

local notation "refreshed" => Function.extend
  (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block) c f

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PrecenterForecastNativeAtomDictionary
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def FiniteProbabilityWeights.sampledComplexTest
    {T X : Type*} [Fintype T] (law : FiniteProbabilityWeights T)
    (physical : T → X) (weight : T → ℂ) : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun f := law.complexMean (fun t => f (physical t) * weight t)
  map_add' f g := by
    simp only [FiniteProbabilityWeights.complexMean, Pi.add_apply, add_mul,
      mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [FiniteProbabilityWeights.complexMean, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring

theorem exists_precenter_forecast_finiteLaw_native_partners
    {Ω T X Branch K σ Θ : Type*}
    [Fintype Ω] [Fintype T] [Fintype K]
    (input : Branch → X → ℂ) (models : Branch → CenteredForecastModel X)
    (nativeWeight : σ → ℕ) (degree : ℕ) (budget : ℝ)
    (sample : X → σ → ℤ) (twist : Θ → X → ℂ)
    (hnative : ∀ b i, (models b).models i ∈
      twistedNativeSampleFunctions nativeWeight degree budget sample twist)
    (hmodel : ∀ b, input b =
      (∑ i, (models b).coefficient i • (models b).models i) + (models b).residual)
    {M termBound delta : ℝ} {rank : ℕ}
    (hM : 0 < M) (hterm : 1 ≤ termBound) (hdelta : 0 < delta)
    (hc : ∀ b, (∑ i, |(models b).coefficient i|) ≤ M)
    (hterms : ∀ b, ((models b).nterms : ℝ) ≤ termBound)
    (selectedBranch : K → Branch) (hrank : Fintype.card K ≤ rank)
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (hproductive : 0 < outer.mass productive)
    (localLaw : Ω → K → FiniteProbabilityWeights T)
    (physical : Ω → T → X) (weight : Ω → K → T → ℂ)
    (herr : ∀ a ∈ productive, ∀ k,
      ‖(localLaw a k).complexMean (fun t =>
        (models (selectedBranch k)).residual (physical a t) * weight a k t)‖ ≤ delta / 2)
    (hscore : ∀ a ∈ productive, ∀ k, delta ≤
      ‖(localLaw a k).complexMean (fun t =>
        input (selectedBranch k) (physical a t) * weight a k t)‖) :
    ∃ (fixedTwist : K → Θ) (nativeValue : K → X → ℂ)
      (_native : ∀ k, NativeSampleModel nativeWeight degree budget sample (nativeValue k))
      (retained : Finset Ω),
      retained ⊆ productive ∧ 0 < outer.mass retained ∧
      outer.mass productive / termBound ^ rank ≤ outer.mass retained ∧
      ∀ a ∈ retained, ∀ k, delta / (2 * M) ≤
        ‖(localLaw a k).complexMean (fun t =>
          (star (twist (fixedTwist k) (physical a t)) * nativeValue k (physical a t)) *
            weight a k t)‖ := by
  let selectedModel := fun k => models (selectedBranch k)
  let : ∀ k, Nonempty (Fin (selectedModel k).nterms) :=
    fun k => ⟨⟨0, (selectedModel k).positive⟩⟩
  let test := fun a k => (localLaw a k).sampledComplexTest (physical a) (weight a k)
  have heval (a) (k) (f : X → ℂ) : test a k f =
      (localLaw a k).complexMean (fun t => f (physical a t) * weight a k t) := rfl
  have hmodelComplex (k : K) : input (selectedBranch k) =
      (∑ i, ((selectedModel k).coefficient i : ℂ) • (selectedModel k).models i) +
        (selectedModel k).residual := hmodel (selectedBranch k)
  have hcComplex (k : K) : ∑ i, ‖((selectedModel k).coefficient i : ℂ)‖ ≤ M := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hc (selectedBranch k)
  obtain ⟨partner, retained, hsub, hmass, hcorr⟩ :=
    exists_fixed_linear_model_partners_of_pointwise_error outer productive
      (fun k => input (selectedBranch k)) (fun k => (selectedModel k).residual)
      (fun k => (selectedModel k).models)
      (fun k i => ((selectedModel k).coefficient i : ℂ)) test
      hmodelComplex hdelta hM hcComplex
      (by intro a ha k; rw [heval]; exact herr a ha k)
      (by intro a ha k; rw [heval]; exact hscore a ha k)
  have hmasspos : 0 < outer.mass retained :=
    (div_pos hproductive (Finset.prod_pos (fun k _ =>
      Nat.cast_pos.mpr Fintype.card_pos))).trans_le hmass
  have hne : retained.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmasspos
    linarith)
  obtain ⟨a₀, ha₀⟩ := hne
  have hchosen (k : K) : ∃ (t : Θ) (g : X → ℂ),
      Nonempty (NativeSampleModel nativeWeight degree budget sample g) ∧
      (selectedModel k).models (partner k) = fun x => star (twist t x) * g x := by
    rcases hnative (selectedBranch k) (partner k) with hzero | hgood
    · have hn := hcorr a₀ ha₀ k
      change delta / (2 * M) ≤ ‖test a₀ k ((models (selectedBranch k)).models (partner k))‖ at hn
      rw [hzero, map_zero, norm_zero] at hn
      have hpos : 0 < delta / (2 * M) := div_pos hdelta (by positivity)
      linarith
    · exact hgood
  choose fixedTwist nativeValue hnativeValue heq using hchosen
  refine ⟨fixedTwist, nativeValue, fun k => Classical.choice (hnativeValue k),
    retained, hsub, hmasspos, ?_, ?_⟩
  · apply le_trans _ hmass
    apply div_le_div_of_nonneg_left hproductive.le
      (Finset.prod_pos (fun k _ => Nat.cast_pos.mpr Fintype.card_pos))
    calc
      (∏ k, (Fintype.card (Fin (selectedModel k).nterms) : ℝ))
          ≤ ∏ _k : K, termBound := by
        apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        intro k _
        simpa only [Fintype.card_fin] using hterms (selectedBranch k)
      _ = termBound ^ Fintype.card K := by rw [Finset.prod_const, Finset.card_univ]
      _ ≤ termBound ^ rank := pow_le_pow_right₀ hterm hrank
  · intro a ha k
    have h := hcorr a ha k
    rw [heval, heq] at h
    exact h

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

abbrev PrecenterForecastNativeAtomLabel {X Branch : Type*}
    (models : Branch → CenteredForecastModel X) :=
  {label : Σ b, Fin (models b).nterms // (models label.1).models label.2 ≠ 0}

noncomputable instance precenterForecastNativeAtomLabelFintype
    {X Branch : Type*} [Fintype Branch] (models : Branch → CenteredForecastModel X) :
    Fintype (PrecenterForecastNativeAtomLabel models) := by
  unfold PrecenterForecastNativeAtomLabel
  infer_instance

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ExternalKernelPrecenterNativePointPartners
namespace OAI

section

namespace Erdos3
open scoped BigOperators TensorProduct Classical

noncomputable def externalNetMaskFamily
    {Freq X Y I : Type*} (F : Freq → X → Y → ℂ)
    (centers : Freq → I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ f x, ∃ i, ∀ y, ‖F f x y - centers f i y‖ ≤ ε)
    (input : X → ℂ) : (Freq × I) → X → ℂ :=
  fun b x => if externalNetIndex (F b.1) (centers b.1) (hnet b.1) x = b.2
    then input x else 0

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators TensorProduct Classical

theorem exists_external_kernel_precenter_native_point_partners
    {L σ X Ω T I Freq NativeCoord Θ : Type*}
    [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype T] [Fintype I] [Nonempty I]
    {s d r : ℕ} (D : RationalFilteredNilmanifold L s d)
    {w : σ → ℕ}
    (U : Freq → X → D.Niltest w) (representative : I → X)
    {p B ε δ M termBound : ℝ}
    (hcomplex : ∀ f x, (U f x).ComplexityLE p)
    (hnet : ∀ f x, ∃ i, ∀ y, ‖(U f x).observable y -
      (U f (representative i)).observable y‖ ≤ ε)
    (input : X → ℂ) (models : (Freq × I) → CenteredForecastModel X)
    (nativeWeight : NativeCoord → ℕ) (degree : ℕ) (budget : ℝ)
    (sample : X → NativeCoord → ℤ) (twist : Θ → X → ℂ)
    (hnative : ∀ b i, (models b).models i ∈
      twistedNativeSampleFunctions nativeWeight degree budget sample twist)
    (hmodel : ∀ b, externalNetMaskFamily (fun f x => (U f x).observable)
      (fun f i => (U f (representative i)).observable) hnet input b =
        (∑ i, (models b).coefficient i • (models b).models i) + (models b).residual)
    (hc : ∀ b, (∑ i, |(models b).coefficient i|) ≤ M)
    (hterms : ∀ b, ((models b).nterms : ℝ) ≤ termBound)
    (hM : 0 < M) (hterm : 1 ≤ termBound)
    (code : Fin r → Option Freq)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights T)
    (localPoint : Ω → T → D.Space) (physical : Ω → T → X)
    (hB : 0 ≤ B) (hδ : 0 < δ) (herror : B * ε ≤ δ / 2)
    (hinput : ∀ x, ‖input x‖ ≤ B)
    (hresidual : ∀ a ∈ H, ∀ f i,
      ‖(localLaw a).complexMean (fun t => (models (f, i)).residual (physical a t) *
        (U f (representative i)).observable (localPoint a t))‖ ≤
          (δ / (2 * Fintype.card I)) / 2)
    (hscore : ∀ a ∈ H, ∀ i f, code i = some f → δ ≤
      ‖(localLaw a).complexMean (fun t => input (physical a t) *
        (U f (physical a t)).observable (localPoint a t))‖) :
    ∃ (chosen : KernelProjectionPresentPivot code → I)
      (fixedTwist : KernelProjectionPresentPivot code → Θ)
      (nativeValue : KernelProjectionPresentPivot code → X → ℂ)
      (_native : ∀ k, NativeSampleModel nativeWeight degree budget sample (nativeValue k))
      (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      outer.mass H / ((Fintype.card I : ℝ) ^ r * termBound ^ r) ≤ outer.mass retained ∧
      (∀ k, (U (kernelProjectionSelectedPivot code k)
        (representative (chosen k))).ComplexityLE p) ∧
      ∀ a ∈ retained, ∀ k, (δ / (2 * Fintype.card I)) / (2 * M) ≤
        ‖(localLaw a).complexMean (fun t =>
          (star (twist (fixedTwist k) (physical a t)) * nativeValue k (physical a t)) *
            (U (kernelProjectionSelectedPivot code k)
              (representative (chosen k))).observable (localPoint a t))‖ := by
  let K := KernelProjectionPresentPivot code
  let functions := fun (k : K) x => (U (kernelProjectionSelectedPivot code k) x).observable
  let centers := fun (k : K) i =>
    (U (kernelProjectionSelectedPivot code k) (representative i)).observable
  have hselected (a : Ω) (ha : a ∈ H) (k : K) : δ ≤
      ‖(localLaw a).complexMean (fun t => input (physical a t) *
        functions k (physical a t) (localPoint a t))‖ :=
    hscore a ha k.val (kernelProjectionSelectedPivot code k)
      (kernelProjectionSelectedPivot_spec code k)
  obtain ⟨chosen, masked, H', hmask, _, hsub, hpos, hmass, hlocal⟩ :=
    exists_simultaneous_external_pivot_masks functions centers
      (fun k => hnet (kernelProjectionSelectedPivot code k)) outer H hH
      (fun a _ => localLaw a) physical (fun a _ t => localPoint a t)
      input hB hδ herror hinput hselected
  have hmassRank : outer.mass H / (Fintype.card I : ℝ) ^ r ≤ outer.mass H' := by
    apply le_trans _ hmass
    apply div_le_div_of_nonneg_left (outer.mass_nonneg H)
      (pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _)
    exact pow_le_pow_right₀
      (by exact_mod_cast Fintype.card_pos : (1 : ℝ) ≤ Fintype.card I)
      (kernelProjectionPresentPivot_card_le code)
  let selectedBranch := fun k : KernelProjectionPresentPivot code =>
    (kernelProjectionSelectedPivot code k, chosen k)
  let family := externalNetMaskFamily (fun f x => (U f x).observable)
    (fun f i => (U f (representative i)).observable) hnet input
  have hfamily (k : KernelProjectionPresentPivot code) :
      family (selectedBranch k) = masked k := by
    funext x
    exact (hmask k x).symm
  obtain ⟨fixedTwist, nativeValue, native, retained, hretSub, hretPos, hretMass, hretScore⟩ :=
    exists_precenter_forecast_finiteLaw_native_partners family models
      nativeWeight degree budget sample twist hnative hmodel hM hterm
      (div_pos hδ (by positivity)) hc hterms selectedBranch
      (kernelProjectionPresentPivot_card_le code) outer H' hpos
      (fun a _ => localLaw a) physical
      (fun a k t => (U (kernelProjectionSelectedPivot code k)
        (representative (chosen k))).observable (localPoint a t))
      (fun a ha k => hresidual a (hsub ha) _ _)
      (by intro a ha k; rw [hfamily]; exact hlocal a ha k)
  refine ⟨chosen, fixedTwist, nativeValue, native, retained,
    fun a ha => hsub (hretSub ha), hretPos, ?_, fun k => hcomplex _ _, hretScore⟩
  calc
    outer.mass H / ((Fintype.card I : ℝ) ^ r * termBound ^ r)
        = (outer.mass H / (Fintype.card I : ℝ) ^ r) / termBound ^ r := by
      rw [div_div]
    _ ≤ outer.mass H' / termBound ^ r :=
      div_le_div_of_nonneg_right hmassRank (pow_nonneg (by linarith) _)
    _ ≤ outer.mass retained := hretMass

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseCanonicalTopology
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open PolynomialTranslationLie
open scoped TensorProduct

@[instance_reducible]
noncomputable def canonicalTopology (s : ℕ) :
    TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra weight s) :=
  moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)

theorem canonicalTopologicalAddGroup (s : ℕ) :
    letI := canonicalTopology s
    IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight s) := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)
  exact IsModuleTopology.topologicalAddGroup ℝ _

theorem canonicalContinuousSMul (s : ℕ) :
    letI := canonicalTopology s
    ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s) := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)
  infer_instance

theorem canonicalT2Space (s : ℕ) :
    letI := canonicalTopology s
    T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight s) :=
  realification_moduleTopology_t2 (nilmanifold s).basis

theorem withCanonicalTopology {P : Prop}
    (h : ∀ [∀ r, TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra weight r)]
      [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight r)]
      [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight r)]
      [∀ r, T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight r)], P) : P := by
  let (r : ℕ) := canonicalTopology r
  let (r : ℕ) := canonicalTopologicalAddGroup r
  let (r : ℕ) := canonicalContinuousSMul r
  let (r : ℕ) := canonicalT2Space r
  exact h

end Erdos3.OrdinaryPolynomialPhase

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPatchShearFiberCandidateScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal TensorProduct

namespace PolynomialPatch

variable {X Y : Type*} {s d : ℕ} (P : PolynomialPatch X s d)
  [Fintype (PolynomialShearIndex P.weight)]

theorem shearObservable_local_realEval (A : PolynomialSlots Y d P.weight) (u : Y → ℝ) :
    P.shearObservable (QuotientGroup.mk
      ((polynomialShearFiltration P.weight s P.weight_le).realification.polynomialOrbitRealEval
        (fun _ : Y => 1) u (A.shearPolynomialOrbit s P.weight_le))) =
      (P.form.shearTransformedSlots P.weight_mono (A.loweringAt u)).patchValue P.kernel := by
  exact PolynomialSlots.shearObservable_eval_orbit P.form A P.weight_mono
    P.weight_pos P.weight_le P.kernel u

theorem shearObservable_local_integerEval (A : PolynomialSlots Y d P.weight) (u : Y → ℤ) :
    P.shearObservable (QuotientGroup.mk
      ((polynomialShearNilmanifold P.weight s P.weight_le).filtration.realification.polynomialOrbitEval
        (fun _ : Y => 1) u (A.shearPolynomialOrbit s P.weight_le))) =
      (P.form.shearTransformedSlots P.weight_mono
        (A.loweringAt (fun i => (u i : ℝ)))).patchValue P.kernel := by
  change P.shearObservable (QuotientGroup.mk
    ((polynomialShearFiltration P.weight s P.weight_le).realification.polynomialOrbitEval
      (fun _ : Y => 1) u (A.shearPolynomialOrbit s P.weight_le))) = _
  rw [← NilpotentLieFiltration.polynomialOrbitRealEval_integer]
  exact P.shearObservable_local_realEval A _

theorem fullSliceLaw_shearObservable_score [Fintype Y] [DecidableEq Y]
    (A : PolynomialSlots Y d P.weight) {N : Y → ℕ} {q : ℕ}
    (S : ResidueBoxSlice N q) (hq : 0 < q) (hlen : ∀ i, 0 < S.length i)
    (f : (Y → ℤ) → ℝ) (lam : ℝ) :
    (S.fullSliceLaw hlen).mean (fun u => (f u.val - lam) *
      (P.form.shearTransformedSlots P.weight_mono
        (A.loweringAt (fun i => (u.val i : ℝ)))).patchValue P.kernel) =
      (𝔼 u ∈ S.integerPoints, ((f u - lam : ℝ) : ℂ) *
        (P.shearObservable (QuotientGroup.mk
          ((polynomialShearNilmanifold P.weight s P.weight_le).filtration.realification.polynomialOrbitEval
            (fun _ : Y => 1) u (A.shearPolynomialOrbit s P.weight_le))) : ℂ)).re := by
  rw [S.fullSliceLaw_mean hlen, S.expect_integerPoints hq, Complex.re_expect]
  apply Finset.expect_congr rfl
  intro u _
  rw [P.shearObservable_local_integerEval]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rfl

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {I : Type*} [Fintype I] [DecidableEq I]
  {keep : I → Prop} [DecidablePred keep] {N : I → ℕ} {q : ℕ}

end ResidueBoxSlice

namespace PolynomialSlots

variable {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ} {w : Fin d → ℕ}

noncomputable def coordinateFiberForm (A : PolynomialSlots I d w)
    (keep : I → Prop) (fixed : {i // ¬keep i} → ℤ) : PolynomialSlots {i // keep i} d w :=
  A.reparam (coordinateFiberParameters keep fixed) (coordinateFiberParameters_degree keep fixed)

end PolynomialSlots

namespace PolynomialPatch

variable {X I : Type*} [Fintype I] [DecidableEq I] {s d : ℕ}
    (P : PolynomialPatch X s d)

end PolynomialPatch

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MarkedExternalKernelProjectionScoreRestoration
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ τ Ω J X : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype J]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem exists_external_kernelProjection_prescribed_marked_orbit
    (tests : X → D.Niltest w) (htests : ∀ x, (tests x).UnitIntervalValued)
    (G : NilpotentLieFiltration M t) (φ : L →ₗ⁅ℚ⁆ M)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (hkernel : K ≤ LinearMap.ker φ.toLinearMap)
    (orbit : D.filtration.realification.PolynomialOrbit v)
    (marked : G.realification.PolynomialOrbit v)
    (hmark : map (realLieHomToRat (realificationLieHom φ)).toLinearMap orbit.log = marked.log)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → J → τ → ℤ) (weight : Ω → J → ℂ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ j, ‖weight a j‖ ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun j => weight a j * (((tests (physical a j)).kernelProjection K hK).withOrbit orbit).eval
        (point a j))).re) :
    ∃ restored : D.filtration.realification.PolynomialOrbit v,
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap restored.log = marked.log ∧
      ∃ z : D.RealGroup,
        restored = D.filtration.realification.constantGroupOrbit v z * orbit ∧
        z.coord ∈ K.baseChange ℝ ∧
        NilpotentLieBCHGroup.realificationMap
          (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := G.lowerCentralSeries_eq_bot) φ z = 1 ∧
        (∀ x, ((tests x).withOrbit restored).observable = (tests x).observable ∧
          ((tests x).withOrbit restored).normBound = (tests x).normBound ∧
          ((tests x).withOrbit restored).lipBound = (tests x).lipBound ∧
          ((tests x).withOrbit restored).UnitIntervalValued ∧
          ∀ p, ((tests x).withOrbit restored).ComplexityLE p ↔ (tests x).ComplexityLE p) ∧
        ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
          δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
          ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean
            (fun j => weight a j * ((tests (physical a j)).withOrbit restored).eval
              (point a j))).re := by
  obtain ⟨z, hz, _, H', hsub, hpos, hmass, hs⟩ :=
    exists_external_kernelProjection_restored_orbit tests htests K hK orbit
      outer H hH localLaw physical point weight hB hδ hweight hscore
  have hzmark : NilpotentLieBCHGroup.realificationMap
      (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ z = 1 :=
    (NilpotentLieBCHGroup.coord_mem_realificationKernel_iff
      (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ z).mp
        (Submodule.baseChange_mono ℝ hkernel hz)
  let restored := D.filtration.realification.constantGroupOrbit v z * orbit
  have hrestored : map (realLieHomToRat (realificationLieHom φ)).toLinearMap
      restored.log = marked.log :=
    (D.filtration.map_log_constantGroupOrbit_mul_of_realificationMap_eq_one
      G φ v orbit z hzmark).trans hmark
  refine ⟨restored, hrestored, z, rfl, hz, hzmark, ?_, H', hsub, hpos, hmass, ?_⟩
  · intro x
    exact ⟨rfl, rfl, rfl, htests x, fun _ => Iff.rfl⟩
  · intro a ha
    exact hs a ha

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end


