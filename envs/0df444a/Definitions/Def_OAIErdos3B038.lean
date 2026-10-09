-- Prove2me | Definitions.Def_OAIErdos3B038
-- name    : OAIErdos3B038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T02:33:27.476914+00:00
-- url     : https://prove2.me/theorems/2b8514d9-e5ec-4153-aab9-cebafb9591d7
-- title:
--   OpenAI Erdős-3 split, definitions bundle 39 of 132
-- statement:
--   Definitions bundle 39 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B037`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 39 available.
--
--   Modules: `OAI.Erdos3.MultidegreeLieFiltration.comparisonFiltration`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonFiltrationLayerEquiv`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonFirst`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonFirst_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonFirst_real_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonGraphLift`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonGraphLift_first`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonGraphLift_mem_degree`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonGraphLift_second`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonLayer_top_frequency`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonSecond`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonSecond_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonSecond_real_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonSubalgebra`, `OAI.Erdos3.MultidegreeLieFiltration.comparisonTop_frequency`, `OAI.Erdos3.MultidegreeLieFiltration.realBlockCoefficient`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonCoefficient`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonCoefficient_mem`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonCoefficient_zero_index`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonCoefficient_zero_value`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonGraphLift`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonGraphLift_first`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonGraphLift_mem_degree`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonGraphLift_second`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonGraphLift_tmul`, `OAI.Erdos3.MultidegreeLieFiltration.realComparisonTop_frequency`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedCoefficient`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedCoefficient_inclusion`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedCoefficient_mem`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedCoefficient_permute`, `OAI.Erdos3.MultidegreeLieFiltration.realPolarizedCoefficient_zero`, `OAI.Erdos3.MultidegreeLieFiltration.realSquarefreeInclusion`, `OAI.Erdos3.MultidegreeLieFiltration.realSquarefreeInclusion_injective`, `OAI.Erdos3.MultidegreeLieFiltration.realSquarefreeInclusion_layerMap`, `OAI.Erdos3.MultidegreeLieFiltration.realSquarefreeInclusion_permute`, `OAI.Erdos3.MultidegreeLieFiltration.realSquarefreeLayerMap`, `OAI.Erdos3.MultidegreeLieFiltration.realSquarefreeLayerMap_mem`, `OAI.Erdos3.MultidegreeLieFiltration.realSquarefreeLayerMap_tmul`, `OAI.Erdos3.MultidegreeLieFiltration.realSquarefreeLayerMap_zero`, `OAI.Erdos3.MultidegreeLieFiltration.replicatedFrequency`, `OAI.Erdos3.MultidegreeLieFiltration.replicatedFrequency_apply`, `OAI.Erdos3.MultidegreeLieFiltration.replicatedFrequency_basis_full`, `OAI.Erdos3.MultidegreeLieFiltration.replicatedFrequency_basis_ne`, `OAI.Erdos3.MultidegreeLieFiltration.replicatedFrequency_blockLayerMap_top`, `OAI.Erdos3.MultidegreeLieFiltration.replicatedTopCoefficient_blockLayerMap`, `OAI.Erdos3.NativeCrossWitnesses`, `OAI.Erdos3.NativeCrossWitnesses.extension`, `OAI.Erdos3.NativeCrossWitnesses.extension_norm`, `OAI.Erdos3.NativeCrossWitnesses.extension_of_mem`, `OAI.Erdos3.NativeCrossWitnesses.extension_of_not_mem`, `OAI.Erdos3.NativeCrossWitnesses.lower`, `OAI.Erdos3.NativeCrossWitnesses.mono`, `OAI.Erdos3.NativeCrossWitnesses.product`, `OAI.Erdos3.NativeCrossWitnesses.product_correlation`, `OAI.Erdos3.NativeCrossWitnesses.product_norm`, `OAI.Erdos3.NativeVectorCorrelation.exists_absorb`, `OAI.Erdos3.NativeVectorCorrelation.exists_of_mean`, `OAI.Erdos3.NativeVectorCorrelation.exists_of_mean_approx`, `OAI.Erdos3.NativeVectorCorrelation.exists_of_uniform_approx`, `OAI.Erdos3.NativeVectorCorrelation.mono`, `OAI.Erdos3.NativeVectorCorrelation.rec`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialRealValueHom`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialRealValueHom_constant`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialRealValueHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairToPi`, `OAI.Erdos3.NilpotentLieFiltration.dilationPairToPi_injective`, `OAI.Erdos3.NilpotentLieFiltration.exists_adapted_quotient_fiber_polynomial_lift`, `OAI.Erdos3.NilpotentLieFiltration.exists_model_refiltered_polynomial`, `OAI.Erdos3.NilpotentLieFiltration.exists_native_pointwise_refiltered_orbit_of_constant`, `OAI.Erdos3.NilpotentLieFiltration.exists_native_refiltered_orbit`, `OAI.Erdos3.NilpotentLieFiltration.exists_native_refiltered_orbit_of_constant`, `OAI.Erdos3.NilpotentLieFiltration.exists_native_refiltered_orbit_real_values_of_constant`, `OAI.Erdos3.NilpotentLieFiltration.exists_quotient_fiber_polynomialOrbit_lift`, `OAI.Erdos3.NilpotentLieFiltration.exists_quotient_marked_layer_lift`, `OAI.Erdos3.NilpotentLieFiltration.filteredRealPolynomialSection`, `OAI.Erdos3.NilpotentLieFiltration.filteredRealPolynomialSection_value`, `OAI.Erdos3.NilpotentLieFiltration.mem_native_refiltration_layer`, `OAI.Erdos3.NilpotentLieFiltration.native_refiltered_orbit_real_value`, `OAI.Erdos3.NilpotentLieFiltration.quotientFiberEquiv`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialGroupMap`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialGroupMap_constant`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialGroupMap_filteredSection`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialGroupMap_log`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialGroupMap_value`, `OAI.Erdos3.NilpotentLieFiltration.realificationLieHom_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.realificationTopQuotientEquiv`, `OAI.Erdos3.NilpotentLieFiltration.realificationTopQuotientEquiv_mem_layer_iff`, `OAI.Erdos3.NilpotentLieFiltration.realificationTopQuotientEquiv_mk`, `OAI.Erdos3.NilpotentLieFiltration.realificationTopQuotientEquiv_projection`, `OAI.Erdos3.NilpotentLieFiltration.realificationTopQuotientHom`, `OAI.Erdos3.NilpotentLieFiltration.realificationTopQuotientHom_bijective`, `OAI.Erdos3.NilpotentLieFiltration.realificationTopQuotientHom_mk`, `OAI.Erdos3.NilpotentLieFiltration.refiltration_coefficients_mem_first_of_constant`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonAmbient`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonAmbient_geometry`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonAmbient_point_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonGeometryBudget`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonLattice`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonLattice_first`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonLattice_second`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonToAmbient`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonToAmbient_injective`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.dilationPairLattice`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.dilationPairLattice_mem`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_comparison_filtration_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_comparison_layer_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_comparison_model`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_controlled_replicated_frequency`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_dilationPair_model`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_replicatedFrequency_denominator`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.replicatedFrequency_basis_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.replicatedFrequency_finBasis_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeLattice_frequency_integral`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.squarefreeRealLattice_frequency_integral`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.evalReal_of_lattice_factorization`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.eval_of_lattice_factorization`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.observable_change_left`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.observable_freeze_factors`, `OAI.Erdos3.RationalFilteredNilmanifold.dilationPairGeometryBudget`, `OAI.Erdos3.RationalFilteredNilmanifold.dilationPairLattice`, `OAI.Erdos3.RationalFilteredNilmanifold.embedding_basis_card_le`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_native_external_net`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_dilationPair_filtration_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_dilationPair_layer_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_dilationPair_model`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_dilationPair_model_of_eq`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_frozen_external_test_net`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_model_of_bounded_embedding`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_model_of_embedding_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_controlled_native_external_nets`, `OAI.Erdos3.RationalFilteredNilmanifold.frozen_observable_change_left`, `OAI.Erdos3.RationalFilteredNilmanifold.lattice_factorization_quotient`, `OAI.Erdos3.RationalFilteredNilmanifold.optionProductMap_point_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.pair_product_basis_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.quotientInducedMark_native_logHeight`, `OAI.Erdos3.exists_external_test_net`, `OAI.Erdos3.exists_lipschitz_reconstruction_of_positiveImageSlice_eq`, `OAI.Erdos3.exists_nativeMarkedQuotientHeightBudget`, `OAI.Erdos3.exists_native_two_unit_comparison`, `OAI.Erdos3.exists_squarefreeFrequency_cost`, `OAI.Erdos3.fourPointProduct`, `OAI.Erdos3.le_productNiltestBudget`, `OAI.Erdos3.lieQuotientFiberEquiv`, `OAI.Erdos3.lieQuotientFiberEquiv_apply`, `OAI.Erdos3.lieQuotientFiberMap`, `OAI.Erdos3.lieQuotientFiberMap_bijective`, `OAI.Erdos3.lieQuotientFiberProduct`, `OAI.Erdos3.lieQuotientProjection`, `OAI.Erdos3.lieQuotientProjection_basis_logHeight`, `OAI.Erdos3.lieQuotientProjection_mk`, `OAI.Erdos3.nativeCrossResidual`, `OAI.Erdos3.pairToPi`, `OAI.Erdos3.pairToPi_injective`, `OAI.Erdos3.pairToPi_one`, `OAI.Erdos3.pairToPi_zero`, `OAI.Erdos3.positiveImageExtension`, `OAI.Erdos3.positiveImageExtension_bound_of_reconstruction`, `OAI.Erdos3.positiveImageExtension_eq`, `OAI.Erdos3.positiveImageExtension_lipschitz`, `OAI.Erdos3.positiveImageExtension_nonexpansive`, `OAI.Erdos3.positiveImageExtension_norm_le_one`, `OAI.Erdos3.positiveImageExtension_reconstructs_of_positiveImageSlice_eq`, `OAI.Erdos3.positiveImageExtension_unit_interval`, `OAI.Erdos3.positiveImageSlice`, `OAI.Erdos3.positiveImageSlice_eq`, `OAI.Erdos3.positiveImageSlice_lipschitz`, `OAI.Erdos3.positiveImageSlice_parameter_bound`, `OAI.Erdos3.quotientInducedMapHeightBudget`, `OAI.Erdos3.quotientInducedMarkHeightBudget`, `OAI.Erdos3.quotientInducedMark_basis_logHeight`, `OAI.Erdos3.realSquarefreePermute_monomial`, `OAI.Erdos3.replicatedFrequencyDenominatorBudget`, `OAI.Erdos3.replicatedFrequencyDenominator_le_exp`, `OAI.Erdos3.replicatedFrequencyHeight`, `OAI.Erdos3.replicatedFrequencyHeight_ceil_exp`, `OAI.Erdos3.replicatedFrequencyHeight_le_exp`, `OAI.Erdos3.replicatedFrequencyHeight_pos`, `OAI.Erdos3.squarefreeFrequencyInputBudget`, `OAI.Erdos3.squarefreeFrequencyInputBudget_le_model`, `OAI.Erdos3.squarefreeFrequencyInputBudget_nonneg`, `OAI.Erdos3.squarefreeFrequencyModelBudget`, `OAI.Erdos3.squarefreeInputBudget_le_frequency`, `OAI.Erdos3.squarefree_frequency_grid_budget`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B111

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y : Type*} [Nonempty X] [PseudoMetricSpace Y]
  (φ : X → Y) (L : ℝ≥0)

noncomputable def positiveImageExtension (f : X → ℂ) (y : Y) : ℂ :=
  positiveClip (mcShaneEnvelope φ L (fun x => (f x).re) y)

omit [Nonempty X] in
theorem positiveImageExtension_unit_interval (f : X → ℂ) (y : Y) :
    (positiveImageExtension φ L f y).im = 0 ∧
      0 ≤ (positiveImageExtension φ L f y).re ∧ (positiveImageExtension φ L f y).re ≤ 1 :=
  positiveClip_unit_interval _

omit [Nonempty X] in
theorem positiveImageExtension_norm_le_one (f : X → ℂ) (y : Y) :
    ‖positiveImageExtension φ L f y‖ ≤ 1 := norm_positiveClip_le_one _

theorem positiveImageExtension_lipschitz (f : X → ℂ) (hf : ∀ x, 0 ≤ (f x).re) :
    LipschitzWith L (positiveImageExtension φ L f) := by
  unfold positiveImageExtension
  have h := positiveClip_lipschitz.comp
    (Complex.isometry_ofReal.lipschitz.comp (mcShaneEnvelope_lipschitz φ L _ hf))
  simpa only [Function.comp_def, one_mul] using h

theorem positiveImageExtension_eq (f : X → ℂ)
    (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1)
    (hLip : ∀ x z, ‖f x - f z‖ ≤ L * dist (φ x) (φ z)) (x : X) :
    positiveImageExtension φ L f (φ x) = f x := by
  have hreal : ∀ x z, |(f x).re - (f z).re| ≤ L * dist (φ x) (φ z) :=
    fun x z => (Complex.abs_re_le_norm (f x - f z)).trans (hLip x z)
  have heq : ((f x).re : ℂ) = f x := Complex.ext rfl (hf x).1.symm
  unfold positiveImageExtension
  rw [mcShaneEnvelope_eq φ L _ (fun x => (hf x).2.1) hreal, heq,
    positiveClip_eq_self _ (hf x)]

theorem positiveImageExtension_nonexpansive (f g : X → ℂ)
    (hf : ∀ x, 0 ≤ (f x).re) (hg : ∀ x, 0 ≤ (g x).re)
    {δ : ℝ} (hfg : ∀ x, ‖f x - g x‖ ≤ δ) (y : Y) :
    ‖positiveImageExtension φ L f y - positiveImageExtension φ L g y‖ ≤ δ := by
  have henv := mcShaneEnvelope_abs_sub_le φ L (fun x => (f x).re) (fun x => (g x).re)
    hf hg (fun x => (Complex.abs_re_le_norm (f x - g x)).trans (hfg x)) y
  have hclip := positiveClip_lipschitz.dist_le_mul
    (mcShaneEnvelope φ L (fun x => (f x).re) y : ℂ)
    (mcShaneEnvelope φ L (fun x => (g x).re) y : ℂ)
  have hbound : ‖positiveImageExtension φ L f y - positiveImageExtension φ L g y‖ ≤
      |mcShaneEnvelope φ L (fun x => (f x).re) y - mcShaneEnvelope φ L (fun x => (g x).re) y| := by
    simpa only [positiveImageExtension, NNReal.coe_one, one_mul, dist_eq_norm,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hclip
  exact hbound.trans henv

theorem positiveImageExtension_bound_of_reconstruction (f : X → ℂ) (v : Y → ℂ)
    (hv : LipschitzWith L v) (heval : ∀ x, v (φ x) = f x)
    (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1) :
    LipschitzWith L (positiveImageExtension φ L f) ∧
      (∀ y, (positiveImageExtension φ L f y).im = 0 ∧
        0 ≤ (positiveImageExtension φ L f y).re ∧ (positiveImageExtension φ L f y).re ≤ 1) ∧
      (∀ y, ‖positiveImageExtension φ L f y‖ ≤ 1) ∧
      ∀ x, positiveImageExtension φ L f (φ x) = f x := by
  refine ⟨positiveImageExtension_lipschitz φ L f (fun x => (hf x).2.1),
    positiveImageExtension_unit_interval φ L f, positiveImageExtension_norm_le_one φ L f, ?_⟩
  apply positiveImageExtension_eq φ L f hf
  intro x z
  simpa only [dist_eq_norm, heval] using hv.dist_le_mul (φ x) (φ z)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X Y Z : Type*} [Nonempty X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  (φ : X → Y × Z) (L : ℝ≥0)

noncomputable def positiveImageSlice (f : X → ℂ) (z : Z) (y : Y) : ℂ :=
  positiveImageExtension φ L f (y, z)

theorem positiveImageSlice_lipschitz (f : X → ℂ) (hf : ∀ x, 0 ≤ (f x).re) (z : Z) :
    LipschitzWith L (positiveImageSlice φ L f z) := by
  apply LipschitzWith.of_dist_le_mul
  intro y y'
  have h := (positiveImageExtension_lipschitz φ L f hf).dist_le_mul (y, z) (y', z)
  simpa only [positiveImageSlice, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using h

theorem positiveImageSlice_eq (f : X → ℂ)
    (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1)
    (hLip : ∀ x z, ‖f x - f z‖ ≤ L * dist (φ x) (φ z)) (x : X) :
    positiveImageSlice φ L f (φ x).2 (φ x).1 = f x :=
  positiveImageExtension_eq φ L f hf hLip x

theorem positiveImageSlice_parameter_bound (f g : X → ℂ)
    (hf : ∀ x, 0 ≤ (f x).re) (hg : ∀ x, 0 ≤ (g x).re)
    {δ : ℝ} (hfg : ∀ x, ‖f x - g x‖ ≤ δ) (z z' : Z) (y : Y) :
    ‖positiveImageSlice φ L f z y - positiveImageSlice φ L g z' y‖ ≤
      δ + L * dist z z' := by
  have hleft := positiveImageExtension_nonexpansive φ L f g hf hg hfg (y, z)
  have hright : ‖positiveImageSlice φ L g z y - positiveImageSlice φ L g z' y‖ ≤
      L * dist z z' := by
    have h := (positiveImageExtension_lipschitz φ L g hg).dist_le_mul (y, z) (y, z')
    simpa only [positiveImageSlice, Prod.dist_eq, dist_self, max_eq_right dist_nonneg,
      dist_eq_norm] using h
  exact (norm_sub_le_norm_sub_add_norm_sub (positiveImageSlice φ L f z y) (positiveImageSlice φ L g z y)
    (positiveImageSlice φ L g z' y)).trans (add_le_add hleft hright)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X Y Z : Type*} [Nonempty X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  (φ : X → Y × Z) (K : ℝ≥0) (f : X → ℂ)
  (hf : ∀ x, 0 ≤ (f x).re)
  (hrecovery : ∀ x, positiveImageSlice φ K f (φ x).2 (φ x).1 = f x)

include hf hrecovery

theorem positiveImageExtension_reconstructs_of_positiveImageSlice_eq :
    LipschitzWith K (positiveImageExtension φ K f) ∧
      ∀ x, positiveImageExtension φ K f (φ x) = f x := by
  refine ⟨positiveImageExtension_lipschitz φ K f hf, ?_⟩
  intro x
  simpa only [positiveImageSlice, Prod.mk.eta] using hrecovery x

theorem exists_lipschitz_reconstruction_of_positiveImageSlice_eq :
    ∃ (v : Y × Z → ℂ) (K' : ℝ≥0), K' ≤ K ∧ LipschitzWith K' v ∧
      ∀ x, v (φ x) = f x := by
  exact ⟨positiveImageExtension φ K f, K, le_rfl,
    positiveImageExtension_reconstructs_of_positiveImageSlice_eq φ K f hf hrecovery⟩

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_external_test_net {O A R X Y Z IO IA IZ : Type*}
    [Nonempty X] [PseudoMetricSpace A] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    [Fintype IO] [Fintype IA] [Fintype R] [Fintype IZ]
    (φ : X → Y × Z) (F : O → A → R → X → ℂ) (L M : ℝ≥0)
    (hpositive : ∀ o a r x, (F o a r x).im = 0 ∧ 0 ≤ (F o a r x).re ∧ (F o a r x).re ≤ 1)
    (hreconstruct : ∀ o a r, ∃ (v : Y × Z → ℂ) (K : ℝ≥0), K ≤ L ∧ LipschitzWith K v ∧
      ∀ x, v (φ x) = F o a r x)
    (hvariation : ∀ o a a' r x, ‖F o a r x - F o a' r x‖ ≤ M * dist a a')
    (oc : IO → O) (ac : IA → A) (zc : IZ → Z) {δO δA δZ : ℝ}
    (hO : ∀ o, ∃ i, ∀ a r x, ‖F o a r x - F (oc i) a r x‖ ≤ δO)
    (hA : ∀ a, ∃ i, dist a (ac i) ≤ δA) (hZ : ∀ z, ∃ i, dist z (zc i) ≤ δZ) :
    let n := Fintype.card IO * Fintype.card IA * Fintype.card R * Fintype.card IZ
    ∃ centers : Fin n → Y → ℂ,
      (∀ i, LipschitzWith L (centers i)) ∧
      (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
      (∀ i y, ‖centers i y‖ ≤ 1) ∧
      (∀ o a r x, positiveImageSlice φ L (F o a r) (φ x).2 (φ x).1 = F o a r x) ∧
      ∀ o a r z, ∃ i, ∀ y,
        ‖positiveImageSlice φ L (F o a r) z y - centers i y‖ ≤ δO + M * δA + L * δZ := by
  classical
  let I := IO × IA × R × IZ
  let n := Fintype.card IO * Fintype.card IA * Fintype.card R * Fintype.card IZ
  have hcard : Fintype.card I = n := by simp only [I, n, Fintype.card_prod, Nat.mul_assoc]
  let e : I ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let centers : Fin n → Y → ℂ := fun i =>
    positiveImageSlice φ L (F (oc (e.symm i).1) (ac (e.symm i).2.1) (e.symm i).2.2.1)
      (zc (e.symm i).2.2.2)
  refine ⟨centers, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact positiveImageSlice_lipschitz φ L _ (fun x => (hpositive _ _ _ x).2.1) _
  · intro i y
    exact positiveImageExtension_unit_interval φ L _ _
  · intro i y
    exact positiveImageExtension_norm_le_one φ L _ _
  · intro o a r x
    obtain ⟨v, K, hK, hv, heval⟩ := hreconstruct o a r
    exact (positiveImageExtension_bound_of_reconstruction φ L (F o a r) v
      (hv.weaken hK) heval (hpositive o a r)).2.2.2 x
  · intro o a r z
    obtain ⟨io, hio⟩ := hO o
    obtain ⟨ia, hia⟩ := hA a
    obtain ⟨iz, hiz⟩ := hZ z
    refine ⟨e (io, ia, r, iz), ?_⟩
    intro y
    have hsource : ∀ x, ‖F o a r x - F (oc io) (ac ia) r x‖ ≤ δO + M * δA := by
      intro x
      exact (norm_sub_le_norm_sub_add_norm_sub (F o a r x) (F (oc io) a r x)
        (F (oc io) (ac ia) r x)).trans (add_le_add (hio a r x)
          ((hvariation (oc io) a (ac ia) r x).trans (mul_le_mul_of_nonneg_left hia M.coe_nonneg)))
    have h := (positiveImageSlice_parameter_bound φ L (F o a r) (F (oc io) (ac ia) r)
      (fun x => (hpositive _ _ _ x).2.1) (fun x => (hpositive _ _ _ x).2.1) hsource z (zc iz) y).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hiz L.coe_nonneg))
    simpa only [centers, Equiv.symm_apply_apply] using h

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def adaptedPolynomialRealValueHom (t : σ → ℝ) :
    (F.realification.adaptedPolynomialFiltration w).Group →* F.realification.Group :=
  (F.realification.polynomialOrbitRealEval w t).comp (F.realification.adaptedBCHToOrbit w)

theorem adaptedPolynomialRealValueHom_coord (t : σ → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    (F.adaptedPolynomialRealValueHom w t g).coord =
      eval₂ t (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

theorem adaptedPolynomialRealValueHom_constant (t : σ → ℝ) (κ : F.realification.Group) :
    F.adaptedPolynomialRealValueHom w t (F.realification.adaptedConstantGroupHom w κ) = κ := by
  apply NilpotentLieBCHGroup.ext
  rw [adaptedPolynomialRealValueHom_coord, F.realification.adaptedConstantGroupHom_log,
    eval₂_monomial, Finsupp.prod_zero_index, one_smul]

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ)

theorem lattice_factorization_quotient
    (g E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ = g)
    (t : σ → ℝ) :
    (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w t g) : D.Space) =
      QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w t E *
        D.filtration.adaptedPolynomialRealValueHom w t b *
        D.filtration.adaptedPolynomialRealValueHom w t R) := by
  have h := congrArg (D.filtration.adaptedPolynomialRealValueHom w t) hprod
  simp only [map_mul, NilpotentLieFiltration.adaptedPolynomialRealValueHom_constant] at h
  rw [← h]
  exact QuotientGroup.mk_mul_of_mem _ hκ

namespace Niltest

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem evalReal_of_lattice_factorization (T : D.Niltest w)
    (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
      ⟨⟨T.orbit.log, T.orbit.property⟩⟩) (t : σ → ℝ) :
    T.evalReal t = T.observable (QuotientGroup.mk
      (D.filtration.adaptedPolynomialRealValueHom w t E *
        D.filtration.adaptedPolynomialRealValueHom w t b *
        D.filtration.adaptedPolynomialRealValueHom w t R)) := by
  exact congrArg T.observable (lattice_factorization_quotient D w _ E b R κ hκ hprod t)

theorem eval_of_lattice_factorization (T : D.Niltest w)
    (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
      ⟨⟨T.orbit.log, T.orbit.property⟩⟩) (x : σ → ℤ) :
    T.eval x = T.observable (QuotientGroup.mk
      (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) E *
        D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b *
        D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) R)) := by
  rw [← T.evalReal_integer]
  exact evalReal_of_lattice_factorization D w T E b R κ hκ hprod _

end Niltest
end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem observable_change_left (T : D.Niltest w) (a a₀ : D.RealGroup) (x : D.Space) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    ‖T.observable (a • x) - T.observable (a₀ • x)‖ ≤ (T.lipBound : ℝ) * dist a a₀ := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := D.metricSpace
  have hpoint : dist (a • x) (a₀ • x) ≤ dist a a₀ := by
    have hLip : LipschitzWith 1 (fun a : D.RealGroup => a • x) :=
      quotientMetricSpace_lipschitz_orbit (D.basis.baseChange ℝ) D.realLattice
        D.realLattice_closed_discrete.1 x
    simpa only [NNReal.coe_one, one_mul] using hLip.dist_le_mul a a₀
  calc
    _ ≤ (T.lipBound : ℝ) * dist (a • x) (a₀ • x) := by
      simpa only [dist_eq_norm] using T.lipschitz.dist_le_mul (a • x) (a₀ • x)
    _ ≤ _ := mul_le_mul_of_nonneg_left hpoint T.lipBound.coe_nonneg

theorem observable_freeze_factors (T : D.Niltest w) (a a₀ b r r₀ : D.RealGroup)
    (hr : (QuotientGroup.mk r : D.Space) = QuotientGroup.mk r₀) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    ‖T.observable (QuotientGroup.mk (a * b * r)) -
      T.observable (QuotientGroup.mk (a₀ * b * r₀))‖ ≤ (T.lipBound : ℝ) * dist a a₀ := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  have heq : T.observable (QuotientGroup.mk (a * b * r)) =
      T.observable (QuotientGroup.mk (a * b * r₀)) :=
    congrArg (fun x : D.Space => T.observable ((a * b) • x)) hr
  rw [heq, mul_assoc a b r₀, mul_assoc a₀ b r₀]
  exact T.observable_change_left a a₀ (QuotientGroup.mk (b * r₀))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

theorem frozen_observable_change_left (S : D.Space → ℂ) {ℓ : ℝ≥0}
    (hS : letI := D.metricSpace; LipschitzWith ℓ S) (a a' b r : D.RealGroup) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
    ‖S (QuotientGroup.mk (a * b * r)) - S (QuotientGroup.mk (a' * b * r))‖ ≤
      (ℓ : ℝ) * dist a a' := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := D.metricSpace
  let x : D.Space := QuotientGroup.mk (b * r)
  have hLip : LipschitzWith 1 (fun a : D.RealGroup => a • x) :=
    quotientMetricSpace_lipschitz_orbit (D.basis.baseChange ℝ) D.realLattice
      D.realLattice_closed_discrete.1 x
  have hpoint : dist (a • x) (a' • x) ≤ dist a a' := by
    simpa only [NNReal.coe_one, one_mul] using hLip.dist_le_mul a a'
  have h := (hS.dist_le_mul (a • x) (a' • x)).trans
    (mul_le_mul_of_nonneg_left hpoint ℓ.coe_nonneg)
  simpa only [x, MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc, dist_eq_norm] using h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_frozen_external_test_net {L O R X Y Z IO IA IZ : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Nonempty X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    [Fintype IO] [Fintype IA] [Fintype R] [Fintype IZ]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (φ : X → Y × Z)
    (b : X → D.RealGroup) (S : O → D.Space → ℂ) (A : Set D.RealGroup) (r : R → D.RealGroup)
    (K ℓ : ℝ≥0) (hS : ∀ o, letI := D.metricSpace; LipschitzWith ℓ (S o))
    (hpositive : ∀ o x, (S o x).im = 0 ∧ 0 ≤ (S o x).re ∧ (S o x).re ≤ 1)
    (hreconstruct : ∀ o (a : A) j, ∃ (v : Y × Z → ℂ) (C : ℝ≥0),
      C ≤ K ∧ LipschitzWith C v ∧ ∀ x, v (φ x) = S o (QuotientGroup.mk (a.val * b x * r j)))
    (oc : IO → O) (ac : IA → A) (zc : IZ → Z) {δO δA δZ : ℝ}
    (hO : ∀ o, ∃ i, ∀ x, ‖S o x - S (oc i) x‖ ≤ δO)
    (hA :
      letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ)
      ∀ a : A, ∃ i, dist a (ac i) ≤ δA)
    (hZ : ∀ z, ∃ i, dist z (zc i) ≤ δZ) :
    let F := fun o (a : A) j x => S o (QuotientGroup.mk (a.val * b x * r j))
    let n := Fintype.card IO * Fintype.card IA * Fintype.card R * Fintype.card IZ
    ∃ centers : Fin n → Y → ℂ,
      (∀ i, LipschitzWith K (centers i)) ∧
      (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
      (∀ i y, ‖centers i y‖ ≤ 1) ∧
      (∀ o a j x, positiveImageSlice φ K (F o a j) (φ x).2 (φ x).1 =
        S o (QuotientGroup.mk (a.val * b x * r j))) ∧
      ∀ o a j z, ∃ i, ∀ y,
        ‖positiveImageSlice φ K (F o a j) z y - centers i y‖ ≤ δO + ℓ * δA + K * δZ := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let F := fun o (a : A) j x => S o (QuotientGroup.mk (a.val * b x * r j))
  have hvariation : ∀ o (a a' : A) j x, ‖F o a j x - F o a' j x‖ ≤ ℓ * dist a a' := by
    intro o a a' j x
    exact D.frozen_observable_change_left (S o) (hS o) a.val a'.val (b x) (r j)
  exact exists_external_test_net φ F K ℓ (fun o a j x => hpositive o _)
    hreconstruct hvariation oc ac zc
    (fun o => by obtain ⟨i, hi⟩ := hO o; exact ⟨i, fun a j x => hi _⟩) hA hZ

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_controlled_native_external_net (s t r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M O R IO X Y : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [Fintype IO] [Fintype R] [Nonempty X] [PseudoMetricSpace Y] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
      (B K ℓ : ℝ≥0) {p ε : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      1 ≤ B → (B : ℝ) ≤ Real.exp ((p + 2) ^ r) →
      (K : ℝ) ≤ Real.exp p → (ℓ : ℝ) ≤ Real.exp p →
      0 < ε → 1 / ε ≤ Real.exp p →
      (Fintype.card IO : ℝ) ≤ Real.exp p → (Fintype.card R : ℝ) ≤ Real.exp p →
      ∀ (S : O → D.Space → ℂ) (b : X → D.RealGroup) (r₀ : R → D.RealGroup)
        (φ : X → Y × E.Space) (oc : IO → O),
      (∀ o, letI := D.metricSpace; LipschitzWith ℓ (S o)) →
      (∀ o x, (S o x).im = 0 ∧ 0 ≤ (S o x).re ∧ (S o x).re ≤ 1) →
      (∀ o, ∃ i, ∀ x, ‖S o x - S (oc i) x‖ ≤ ε / 3) →
      (∀ o (a : coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
          (D.basis.baseChange ℝ) B) j,
        ∃ (v : Y × E.Space → ℂ) (K' : ℝ≥0), K' ≤ K ∧
          (letI := E.metricSpace; LipschitzWith K' v) ∧
          ∀ x, v (φ x) = S o (QuotientGroup.mk (a.val * b x * r₀ j))) →
      letI := E.metricSpace
      let A := coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ) B
      let F := fun o (a : A) j x => S o (QuotientGroup.mk (a.val * b x * r₀ j))
      ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ ∃ centers : Fin n → Y → ℂ,
        (∀ i, LipschitzWith K (centers i)) ∧
        (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
        (∀ i y, ‖centers i y‖ ≤ 1) ∧
        (∀ o a j x, positiveImageSlice φ K (F o a j) (φ x).2 (φ x).1 = F o a j x) ∧
        ∀ o a j z, ∃ i, ∀ y, ‖positiveImageSlice φ K (F o a j) z y - centers i y‖ ≤ ε := by
  obtain ⟨cA, _, hgroup⟩ := exists_native_group_parameter_cover s r
  obtain ⟨cZ, _, hquot⟩ := exists_native_quotient_parameter_cover t
  let X : Polynomial ℕ := Polynomial.X
  let T := 2 * X + 7
  let P := 2 * X + (T + Polynomial.C cA) ^ cA + (T + Polynomial.C cZ) ^ cZ
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M O R IO X₀ Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d e D E B K ℓ p ε
    hp hD hE hB hBp hK hℓ hε hεinv hIO hR S b r₀ φ oc hS hpositive hO hreconstruct
  let q := 2 * p + 7
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hBq : (B : ℝ) ≤ Real.exp ((q + 2) ^ r) := hBp.trans
    (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) r))
  obtain ⟨nA, _, hnA, ac, hAcov⟩ := hgroup D B hq (hD.mono D hpq) hB hBq
    (externalNetMesh_pos ℓ hε) (externalNetMesh_inverse_bound ℓ hε hp hℓ hεinv)
  obtain ⟨nZ, _, hnZ, zc, hZcov⟩ := hquot E hq (hE.mono E hpq)
    (externalNetMesh_pos K hε) (externalNetMesh_inverse_bound K hε hp hK hεinv)
  let := E.metricSpace
  have hnet := D.exists_frozen_external_test_net φ b S
    (coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) B)
    r₀ K ℓ hS hpositive hreconstruct oc ac zc hO hAcov hZcov
  dsimp only at hnet
  obtain ⟨centers, hLip, hunit, hcap, heval, hcover⟩ := hnet
  have hfinal : 2 * p + (q + cA) ^ cA + (q + cZ) ^ cZ ≤ (p + C) ^ C := by
    simpa [P, T, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hcount : ((Fintype.card IO * nA * Fintype.card R * nZ : ℕ) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    push_cast
    calc
      _ ≤ Real.exp p * Real.exp ((q + cA) ^ cA) * Real.exp p * Real.exp ((q + cZ) ^ cZ) := by
        gcongr
      _ = Real.exp (2 * p + (q + cA) ^ cA + (q + cZ) ^ cZ) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hfinal
  refine ⟨_, ?_, centers, hLip, hunit, hcap, heval, ?_⟩
  · simpa only [Fintype.card_fin] using hcount
  · intro o a j z
    obtain ⟨i, hi⟩ := hcover o a j z
    exact ⟨i, fun y => (hi y).trans (externalNetMesh_error K ℓ hε.le)⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_controlled_native_external_nets (s t r netExponent : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M O R X Y : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [Fintype R] [Nonempty X] [PseudoMetricSpace Y] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
      (B K ℓ : ℝ≥0) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      1 ≤ B → (B : ℝ) ≤ Real.exp ((p + 2) ^ r) →
      (K : ℝ) ≤ Real.exp p → (ℓ : ℝ) ≤ Real.exp p →
      (Fintype.card R : ℝ) ≤ Real.exp p →
      ∀ (S : O → D.Space → ℂ) (b : X → D.RealGroup) (r₀ : R → D.RealGroup)
        (φ : X → Y × E.Space),
      (∀ o, letI := D.metricSpace; LipschitzWith ℓ (S o)) →
      (∀ o x, (S o x).im = 0 ∧ 0 ≤ (S o x).re ∧ (S o x).re ≤ 1) →
      (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
        (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + netExponent) ^ netExponent) ∧
        ∃ oc : Fin n → O, ∀ o, ∃ i, ∀ x, ‖S o x - S (oc i) x‖ ≤ η) →
      (∀ o (a : coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
          (D.basis.baseChange ℝ) B) j,
        ∃ (v : Y × E.Space → ℂ) (K' : ℝ≥0), K' ≤ K ∧
          (letI := E.metricSpace; LipschitzWith K' v) ∧
          ∀ x, v (φ x) = S o (QuotientGroup.mk (a.val * b x * r₀ j))) →
      letI := E.metricSpace
      let A := coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ) B
      let F := fun o (a : A) j x => S o (QuotientGroup.mk (a.val * b x * r₀ j))
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((p + Real.log (1 / ε) + C) ^ C) ∧ ∃ centers : Fin n → Y → ℂ,
        (∀ i, LipschitzWith K (centers i)) ∧
        (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
        (∀ i y, ‖centers i y‖ ≤ 1) ∧
        (∀ o a j x, positiveImageSlice φ K (F o a j) (φ x).2 (φ x).1 = F o a j x) ∧
        ∀ o a j z, ∃ i, ∀ y, ‖positiveImageSlice φ K (F o a j) z y - centers i y‖ ≤ ε := by
  obtain ⟨localExponent, _, hnet⟩ := exists_controlled_native_external_net s t r
  obtain ⟨C, hC, hscalar⟩ := exists_uniformExternalNetScalarBudget netExponent localExponent
  refine ⟨C, hC, ?_⟩
  intro L M O R X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d e D E B K ℓ p
    hp hD hE hB hBp hK hℓ hR S b r₀ φ hS hpositive hO hreconstruct
  let := E.metricSpace
  dsimp only
  intro ε hε hε1
  obtain ⟨q, hq, hpq, hlogq, hmemberq, hqC⟩ := hscalar p ε hp hε hε1
  obtain ⟨nO, hnO, oc, hcoverO⟩ := hO (ε / 3) (by positivity) (by linarith)
  have hexp := Real.exp_le_exp.mpr hpq
  have hBq : (B : ℝ) ≤ Real.exp ((q + 2) ^ r) :=
    hBp.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) r))
  have hεinv : 1 / ε ≤ Real.exp q := by
    calc
      1 / ε = Real.exp (Real.log (1 / ε)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlogq
  have hnOq : (Fintype.card (Fin nO) : ℝ) ≤ Real.exp q := by
    simpa only [Fintype.card_fin] using hnO.trans (Real.exp_le_exp.mpr hmemberq)
  obtain ⟨n, hn, centers, hLip, hunit, hcap, heval, hcover⟩ :=
    hnet D E B K ℓ hq (hD.mono D hpq) (hE.mono E hpq)
      hB hBq (hK.trans hexp) (hℓ.trans hexp) hε hεinv hnOq (hR.trans hexp)
      S b r₀ φ oc hS hpositive hcoverO hreconstruct
  exact ⟨n, hn.trans (Real.exp_le_exp.mpr hqC), centers, hLip, hunit, hcap, heval, hcover⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (W : LieSubalgebra ℚ F.AssociatedGraded)

theorem mem_native_refiltration_layer (j : ℕ)
    (x : ℝ ⊗[ℚ] F.gradedRefiltrationSubalgebra W) :
    x ∈ (F.gradedRefiltration W).realification.layer j ↔
      realificationLieHom (F.gradedRefiltrationSubalgebra W).incl x ∈
        F.realGradedRefiltrationLayer W j := by
  change x ∈ ((F.gradedRefiltrationLayer W j).comap
    (F.gradedRefiltrationSubalgebra W).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  rfl

theorem exists_native_refiltered_orbit (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) :
    ∃ q : (F.gradedRefiltration W).realification.PolynomialOrbit w,
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p ∧ coefficients q.log 0 = 0 := by
  obtain ⟨q₀, _, hq₀, hz₀⟩ := F.exists_refiltered_polynomial_of_coefficients w W hw p hp hzero
  let H := F.gradedRefiltrationSubalgebra W
  let inc := (realLieHomToRat (realificationLieHom H.incl)).toLinearMap
  let lift : F.realGradedRefiltrationSubalgebra W →ₗ[ℚ] (ℝ ⊗[ℚ] H) :=
    (realificationSubmoduleEquiv H.toSubmodule).symm.toLinearMap.restrictScalars ℚ
  have hcomp : inc.comp lift = (F.realGradedRefiltrationSubalgebra W).incl.toLinearMap := by
    ext x
    exact congrArg Subtype.val ((realificationSubmoduleEquiv H.toSubmodule).apply_symm_apply x)
  let q := VectorPolynomial.map lift q₀
  have hmap : VectorPolynomial.map inc q = p := by
    apply coefficients.injective
    ext α
    dsimp only [q]
    rw [coefficients_map, coefficients_map]
    change (inc.comp lift) (coefficients q₀ α) = coefficients p α
    rw [hcomp]
    simpa only [coefficients_map] using congrArg (fun r => coefficients r α) hq₀
  have hadapted : (F.gradedRefiltration W).realification.Adapted w q := by
    apply ((F.gradedRefiltration W).realification.adapted_iff_coefficients w q).mpr
    intro α
    rw [F.mem_native_refiltration_layer]
    have h := congrArg (fun r => coefficients r α) hmap
    rw [coefficients_map] at h
    change inc (coefficients q α) ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α)
    rw [h]
    exact hp α
  refine ⟨polynomialOrbitOfLog q hadapted, hmap, ?_⟩
  change coefficients (VectorPolynomial.map lift q₀) 0 = 0
  rw [coefficients_map, hz₀, map_zero]

theorem native_refiltered_orbit_real_value (w : σ → ℕ)
    (q : (F.gradedRefiltration W).realification.PolynomialOrbit w)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hmap : VectorPolynomial.map
      (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      q.log = p) (t : σ → ℝ) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
      ((F.gradedRefiltration W).realification.polynomialOrbitRealEval w t q) =
        (⟨eval₂ t p⟩ : F.realification.Group) := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (F.gradedRefiltrationSubalgebra W).incl (eval₂ t q.log) = eval₂ t p
  rw [← hmap]
  exact (eval₂_map (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl).toLinearMap t q.log).symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

include hφ in
theorem realificationLieHom_mem_layer (j : ℕ) (x : ℝ ⊗[ℚ] L)
    (hx : x ∈ F.realification.layer j) :
    realificationLieHom φ x ∈ G.realification.layer j :=
  baseChange_mem_of_mapsTo (F.layer j) (G.layer j) φ.toLinearMap (hφ j) hx

noncomputable def realPolynomialGroupMap :
    (F.realification.adaptedPolynomialFiltration w).Group →*
      (G.realification.adaptedPolynomialFiltration w).Group :=
  mapOfSteps (hL := (F.realification.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := (G.realification.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (F.realification.filteredPolynomialMap G.realification
      (realLieHomToRat (realificationLieHom φ)) (F.realificationLieHom_mem_layer G φ hφ) w)

theorem realPolynomialGroupMap_log
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    ((F.realPolynomialGroupMap G φ hφ w g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) =
      VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
        (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

theorem realPolynomialGroupMap_value
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (x : σ → ℝ) :
    G.adaptedPolynomialRealValueHom w x (F.realPolynomialGroupMap G φ hφ w g) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
        (F.adaptedPolynomialRealValueHom w x g) := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_map (realificationLieHom φ).toLinearMap x
    (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))

theorem realPolynomialGroupMap_constant (c : F.realification.Group) :
    F.realPolynomialGroupMap G φ hφ w (F.realification.adaptedConstantGroupHom w c) =
      G.realification.adaptedConstantGroupHom w
        (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
          (hM := G.lowerCentralSeries_eq_bot) φ c) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
    (monomial 0 c.coord) = monomial 0 (realificationLieHom φ c.coord)
  exact map_monomial _ _ _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (W : LieSubalgebra ℚ F.AssociatedGraded)

theorem refiltration_coefficients_mem_first_of_constant
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hconstant : coefficients p 0 ∈ F.realGradedRefiltrationLayer W 1) :
    ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W 1 := by
  intro α
  by_cases hα : α = 0
  · simpa only [hα] using hconstant
  · exact F.realGradedRefiltrationLayer_antitone W
      (positive_weight_of_ne_zero w hw hα) (hp α)

theorem exists_native_refiltered_orbit_of_constant
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hconstant : coefficients p 0 ∈ F.realGradedRefiltrationLayer W 1) :
    ∃ q : (F.gradedRefiltration W).realification.PolynomialOrbit w,
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p := by
  have hfirst := F.refiltration_coefficients_mem_first_of_constant W w hw p hp hconstant
  have hcoeff : ∀ α, coefficients p α ∈ (F.realGradedRefiltrationSubalgebra W).toSubmodule := by
    intro α
    exact (F.mem_realGradedRefiltrationSubalgebra W _).mpr (hfirst α)
  let q₀ := restrictCoefficients (F.realGradedRefiltrationSubalgebra W).toSubmodule p hcoeff
  have hq₀ : VectorPolynomial.map
      (F.realGradedRefiltrationSubalgebra W).incl.toLinearMap q₀ = p :=
    map_restrictCoefficients (F.realGradedRefiltrationSubalgebra W).toSubmodule p hcoeff
  let H := F.gradedRefiltrationSubalgebra W
  let inc := (realLieHomToRat (realificationLieHom H.incl)).toLinearMap
  let lift : F.realGradedRefiltrationSubalgebra W →ₗ[ℚ] (ℝ ⊗[ℚ] H) :=
    (realificationSubmoduleEquiv H.toSubmodule).symm.toLinearMap.restrictScalars ℚ
  have hcomp : inc.comp lift = (F.realGradedRefiltrationSubalgebra W).incl.toLinearMap := by
    ext x
    exact congrArg Subtype.val ((realificationSubmoduleEquiv H.toSubmodule).apply_symm_apply x)
  let q := VectorPolynomial.map lift q₀
  have hmap : VectorPolynomial.map inc q = p := by
    apply coefficients.injective
    ext α
    dsimp only [q]
    rw [coefficients_map, coefficients_map]
    change (inc.comp lift) (coefficients q₀ α) = coefficients p α
    rw [hcomp]
    simpa only [coefficients_map] using congrArg (fun r => coefficients r α) hq₀
  have hadapted : (F.gradedRefiltration W).realification.Adapted w q := by
    apply ((F.gradedRefiltration W).realification.adapted_iff_coefficients w q).mpr
    intro α
    rw [F.mem_native_refiltration_layer]
    have h := congrArg (fun r => coefficients r α) hmap
    rw [coefficients_map] at h
    change inc (coefficients q α) ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α)
    rw [h]
    exact hp α
  exact ⟨polynomialOrbitOfLog q hadapted, hmap⟩

theorem exists_native_refiltered_orbit_real_values_of_constant
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hconstant : coefficients p 0 ∈ F.realGradedRefiltrationLayer W 1) :
    ∃ q : (F.gradedRefiltration W).realification.PolynomialOrbit w,
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval w t q) =
          (⟨eval₂ t p⟩ : F.realification.Group) := by
  obtain ⟨q, hq⟩ := F.exists_native_refiltered_orbit_of_constant W w hw p hp hconstant
  exact ⟨q, hq, fun t => F.native_refiltered_orbit_real_value W w q p hq t⟩

theorem exists_native_pointwise_refiltered_orbit_of_constant
    {ι : Type*} (b : Module.Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : F.realification.adaptedLieSubalgebra w)
    (hconstant : coefficients (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
      F.realGradedRefiltrationLayer W 1)
    (hW : ∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realPolynomialSymbolMap b ω hlayers w p)) ∈ realificationLieSubalgebra W) :
    ∃ q : (F.gradedRefiltration W).realification.PolynomialOrbit w,
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval w t q) =
          (⟨eval₂ t (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))⟩ : F.realification.Group) :=
  F.exists_native_refiltered_orbit_real_values_of_constant W w hw p
    ((F.real_symbol_values_iff_refiltration_coefficients b ω hlayers w W p).mp hW) hconstant

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  (b : Basis ι ℚ L) (e : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M) (ν : κ → ι)
  (hν : ∀ x k, e.repr (φ x) k = b.repr x (ν k))

namespace NilpotentLieFiltration

variable {σ : Type*} {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (w : σ → ℕ)

noncomputable def filteredRealPolynomialSection (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (g : (G.realification.adaptedPolynomialFiltration w).Group) :
    (F.realification.adaptedPolynomialFiltration w).Group :=
  ⟨⟨map ((S.baseChange ℝ).restrictScalars ℚ)
      (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)), by
    intro α
    rw [coefficients_map]
    exact baseChange_mem_of_mapsTo (G.layer (Finsupp.weight w α))
      (F.layer (Finsupp.weight w α)) S (hS _) (g.coord.property α)⟩⟩

theorem filteredRealPolynomialSection_value (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (g : (G.realification.adaptedPolynomialFiltration w).Group) (z : σ → ℝ) :
    F.adaptedPolynomialRealValueHom w z (F.filteredRealPolynomialSection G w S hS g) =
      ⟨S.baseChange ℝ (G.adaptedPolynomialRealValueHom w z g).coord⟩ := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_map (S.baseChange ℝ) z (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M))

variable (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem realPolynomialGroupMap_filteredSection (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (hsection : Function.RightInverse S φ)
    (g : (G.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialGroupMap G φ hφ w (F.filteredRealPolynomialSection G w S hS g) = g := by
  have hcomp : φ.toLinearMap.comp S = LinearMap.id := LinearMap.ext hsection
  have hcompR := congrArg
    (fun f : M →ₗ[ℚ] M => f.baseChange ℝ) hcomp
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hcompR
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  apply coefficients.injective
  ext α
  change coefficients (map ((φ.toLinearMap.baseChange ℝ).restrictScalars ℚ)
    (map ((S.baseChange ℝ).restrictScalars ℚ)
      (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)))) α = _
  rw [coefficients_map, coefficients_map]
  exact DFunLike.congr_fun hcompR _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t e : ℕ} (F : NilpotentLieFiltration L s)
  (W : LieSubalgebra ℚ F.AssociatedGraded)
  (E : RationalFilteredNilmanifold (F.gradedRefiltrationSubalgebra W) s e)
  (hEF : E.filtration = F.gradedRefiltration W) (w : σ → ℕ)

include hEF in
theorem exists_model_refiltered_polynomial (hw : ∀ i, 0 < w i)
    (b : (F.realification.adaptedPolynomialFiltration w).Group)
    (hb : ∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hb0 : coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0) :
    ∃ g : E.filtration.realification.PolynomialOrbit w,
      ∀ x : σ → ℤ,
        realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
          (E.filtration.realification.polynomialOrbitEval w x g) =
            F.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b := by
  rw [hEF]
  obtain ⟨g, hg, _⟩ := F.exists_native_refiltered_orbit W w hw
    (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) hb hb0
  refine ⟨g, ?_⟩
  intro x
  rw [← polynomialOrbitRealEval_integer]
  exact F.native_refiltered_orbit_real_value W w g _ hg _

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedTopQuotient
namespace OAI

section

namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M]

noncomputable def lieQuotientProjection (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J) :
    (L ⧸ I) →ₗ⁅ℚ⁆ (M ⧸ J) :=
  lieQuotientDescend I ((lieQuotientMap J).comp φ)
    (fun x hx => (lieQuotientMap_eq_zero J (φ x)).mpr (hφ x hx))

@[simp] theorem lieQuotientProjection_mk (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J) (x : L) :
    lieQuotientProjection I J φ hφ (lieQuotientMap I x) = lieQuotientMap J (φ x) := rfl

noncomputable def lieQuotientFiberProduct (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J) :
    LieSubalgebra ℚ ((L ⧸ I) × M) where
  carrier := {z | lieQuotientProjection I J φ hφ z.1 = lieQuotientMap J z.2}
  zero_mem' := by simp
  add_mem' hx hy := by
    change _ = _
    simpa only [Prod.fst_add, Prod.snd_add, map_add] using congrArg₂ (· + ·) hx hy
  smul_mem' c x hx := by
    change lieQuotientProjection I J φ hφ (c • x.1) = lieQuotientMap J (c • x.2)
    simpa only [map_smul] using congrArg (c • ·) hx
  lie_mem' := by
    intro x y hx hy
    change lieQuotientProjection I J φ hφ ⁅x.1, y.1⁆ = lieQuotientMap J ⁅x.2, y.2⁆
    simpa only [LieHom.map_lie] using congrArg₂ (⁅·, ·⁆) hx hy

noncomputable def lieQuotientFiberMap (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J) :
    L →ₗ⁅ℚ⁆ lieQuotientFiberProduct I J φ hφ where
  toFun x := ⟨(lieQuotientMap I x, φ x), rfl⟩
  map_add' x y := by apply Subtype.ext; exact Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' c x := by apply Subtype.ext; exact Prod.ext (map_smul _ _ _) (map_smul _ _ _)
  map_lie' {x y} := by
    apply Subtype.ext
    exact Prod.ext (LieHom.map_lie _ _ _) (LieHom.map_lie _ _ _)

theorem lieQuotientFiberMap_bijective (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J)
    (hinj : ∀ x ∈ I, φ x = 0 → x = 0)
    (honto : ∀ y ∈ J, ∃ x ∈ I, φ x = y) :
    Function.Bijective (lieQuotientFiberMap I J φ hφ) := by
  constructor
  · intro x y hxy
    have hq : lieQuotientMap I (x - y) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg (fun z : lieQuotientFiberProduct I J φ hφ => z.val.1) hxy
    have hp : φ (x - y) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg (fun z : lieQuotientFiberProduct I J φ hφ => z.val.2) hxy
    exact sub_eq_zero.mp (hinj (x - y) ((lieQuotientMap_eq_zero I _).mp hq) hp)
  · intro z
    obtain ⟨x, hx⟩ := lieQuotientMap_surjective I z.val.1
    have hc : lieQuotientMap J (z.val.2 - φ x) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact z.property.symm.trans (congrArg (lieQuotientProjection I J φ hφ) hx.symm)
    obtain ⟨a, ha, hpa⟩ := honto (z.val.2 - φ x) ((lieQuotientMap_eq_zero J _).mp hc)
    refine ⟨x + a, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change lieQuotientMap I (x + a) = z.val.1
      rw [map_add, (lieQuotientMap_eq_zero I a).mpr ha, add_zero, hx]
    · change φ (x + a) = z.val.2
      rw [map_add, hpa]
      abel

noncomputable def lieQuotientFiberEquiv (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J)
    (hinj : ∀ x ∈ I, φ x = 0 → x = 0)
    (honto : ∀ y ∈ J, ∃ x ∈ I, φ x = y) :
    L ≃ₗ⁅ℚ⁆ lieQuotientFiberProduct I J φ hφ :=
  LieEquiv.ofBijective (lieQuotientFiberMap I J φ hφ)
    (lieQuotientFiberMap_bijective I J φ hφ hinj honto)

@[simp] theorem lieQuotientFiberEquiv_apply (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J)
    (hinj : ∀ x ∈ I, φ x = 0 → x = 0)
    (honto : ∀ y ∈ J, ∃ x ∈ I, φ x = y) (x : L) :
    (lieQuotientFiberEquiv I J φ hφ hinj honto x).val =
      (lieQuotientMap I x, φ x) := rfl

namespace NilpotentLieFiltration

variable {s : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

noncomputable def quotientFiberEquiv
    (hinj : ∀ x ∈ F.layer s, φ x = 0 → x = 0)
    (honto : ∀ y ∈ G.layer s, ∃ x ∈ F.layer s, φ x = y) :
    L ≃ₗ⁅ℚ⁆ lieQuotientFiberProduct (F.layerIdeal s) (G.layerIdeal s) φ (hφ s) :=
  lieQuotientFiberEquiv (F.layerIdeal s) (G.layerIdeal s) φ (hφ s) hinj honto

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem exists_quotient_marked_layer_lift
    (honto : ∀ y ∈ G.layer s, ∃ x ∈ F.layer s, φ x = y)
    (j : ℕ) (a : L ⧸ F.layerIdeal s) (b : M)
    (ha : a ∈ (F.layer j).map (lieQuotientMap (F.layerIdeal s)).toLinearMap)
    (hb : b ∈ G.layer j)
    (hcompat : lieQuotientProjection (F.layerIdeal s) (G.layerIdeal s) φ (hφ s) a =
      lieQuotientMap (G.layerIdeal s) b) :
    ∃ x ∈ F.layer j, lieQuotientMap (F.layerIdeal s) x = a ∧ φ x = b := by
  by_cases hjs : j ≤ s
  · obtain ⟨z, hz, hza⟩ := ha
    have hδ : b - φ z ∈ G.layer s := by
      apply (lieQuotientMap_eq_zero (G.layerIdeal s) _).mp
      rw [map_sub, sub_eq_zero]
      exact hcompat.symm.trans
        (congrArg (lieQuotientProjection (F.layerIdeal s) (G.layerIdeal s) φ (hφ s)) hza.symm)
    obtain ⟨t, ht, hφt⟩ := honto (b - φ z) hδ
    refine ⟨z + t, (F.layer j).add_mem hz (F.antitone hjs ht), ?_, ?_⟩
    · rw [map_add, (lieQuotientMap_eq_zero (F.layerIdeal s) t).mpr ht, add_zero]
      exact hza
    · rw [map_add, hφt]
      abel
  · have hj : s + 1 ≤ j := by omega
    have ha0 : a = 0 := by
      obtain ⟨z, hz, rfl⟩ := ha
      have hz0 : z = 0 := by
        have h := F.antitone hj hz
        rw [F.terminal] at h
        exact h
      rw [hz0, map_zero]
    have hb0 : b = 0 := by
      have h := G.antitone hj hb
      rw [G.terminal] at h
      exact h
    exact ⟨0, (F.layer j).zero_mem, by rw [map_zero, ha0], by rw [map_zero, hb0]⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem exists_adapted_quotient_fiber_polynomial_lift
    (honto : ∀ y ∈ G.layer s, ∃ x ∈ F.layer s, φ x = y)
    (w : σ → ℕ) (pbar : VectorPolynomial σ ℚ (L ⧸ F.layerIdeal s))
    (q : VectorPolynomial σ ℚ M)
    (hcompat : map (lieQuotientProjection (F.layerIdeal s) (G.layerIdeal s) φ (hφ s)).toLinearMap
      pbar = map (lieQuotientMap (G.layerIdeal s)).toLinearMap q)
    (hpbar : ∀ a, coefficients pbar a ∈
      (F.layer (Finsupp.weight w a)).map (lieQuotientMap (F.layerIdeal s)).toLinearMap)
    (hq : G.Adapted w q) :
    ∃ p : VectorPolynomial σ ℚ L,
      F.Adapted w p ∧ map (lieQuotientMap (F.layerIdeal s)).toLinearMap p = pbar ∧
        map φ.toLinearMap p = q := by
  classical
  have hc (a : σ →₀ ℕ) :
      lieQuotientProjection (F.layerIdeal s) (G.layerIdeal s) φ (hφ s) (coefficients pbar a) =
        lieQuotientMap (G.layerIdeal s) (coefficients q a) := by
    simpa only [coefficients_map, LieHom.coe_toLinearMap] using
      congrArg (fun P => coefficients P a) hcompat
  have hex (a : σ →₀ ℕ) : ∃ x ∈ F.layer (Finsupp.weight w a),
      lieQuotientMap (F.layerIdeal s) x = coefficients pbar a ∧ φ x = coefficients q a :=
    F.exists_quotient_marked_layer_lift G φ hφ honto (Finsupp.weight w a)
      (coefficients pbar a) (coefficients q a) (hpbar a)
      ((G.adapted_iff_coefficients w q).mp hq a) (hc a)
  let v (a : σ →₀ ℕ) : L :=
    if coefficients pbar a = 0 ∧ coefficients q a = 0 then 0 else Classical.choose (hex a)
  have hv (a : σ →₀ ℕ) : v a ∈ F.layer (Finsupp.weight w a) ∧
      lieQuotientMap (F.layerIdeal s) (v a) = coefficients pbar a ∧
        φ (v a) = coefficients q a := by
    dsimp only [v]
    split_ifs with hz
    · exact ⟨(F.layer _).zero_mem, (map_zero _).trans hz.1.symm,
        (map_zero _).trans hz.2.symm⟩
    · exact Classical.choose_spec (hex a)
  let c : (σ →₀ ℕ) →₀ L := Finsupp.onFinset
    ((coefficients pbar).support ∪ (coefficients q).support) v (by
      intro a ha
      apply Finset.mem_union.mpr
      by_cases hp0 : coefficients pbar a = 0
      · right
        apply Finsupp.mem_support_iff.mpr
        intro hq0
        exact ha (by simp only [v, hp0, hq0, and_self, ite_true])
      · exact Or.inl (Finsupp.mem_support_iff.mpr hp0))
  let p : VectorPolynomial σ ℚ L := coefficients.symm c
  have hcoef (a : σ →₀ ℕ) : coefficients p a = v a := by
    simp only [p, LinearEquiv.apply_symm_apply, c, Finsupp.onFinset_apply]
  refine ⟨p, ?_, ?_, ?_⟩
  · apply (F.adapted_iff_coefficients w p).mpr
    intro a
    rw [hcoef]
    exact (hv a).1
  · apply coefficients.injective
    ext a
    rw [coefficients_map, hcoef]
    exact (hv a).2.1
  · apply coefficients.injective
    ext a
    rw [coefficients_map, hcoef]
    exact (hv a).2.2

theorem exists_quotient_fiber_polynomialOrbit_lift
    {r : ℕ} (F : NilpotentLieFiltration L (r + 1)) (G : NilpotentLieFiltration M (r + 1))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (honto : ∀ y ∈ G.layer (r + 1), ∃ x ∈ F.layer (r + 1), φ x = y)
    (w : σ → ℕ) (pbar : F.quotientTop.PolynomialOrbit w) (q : G.PolynomialOrbit w)
    (hcompat : map (lieQuotientProjection (F.layerIdeal (r + 1)) (G.layerIdeal (r + 1))
      φ (hφ (r + 1))).toLinearMap pbar.log =
        map (lieQuotientMap (G.layerIdeal (r + 1))).toLinearMap q.log) :
    ∃ p : F.PolynomialOrbit w,
      map (lieQuotientMap (F.layerIdeal (r + 1))).toLinearMap p.log = pbar.log ∧
        map φ.toLinearMap p.log = q.log := by
  have hpbar : ∀ a, coefficients pbar.log a ∈
      (F.layer (Finsupp.weight w a)).map
        (lieQuotientMap (F.layerIdeal (r + 1))).toLinearMap :=
    (F.quotientTop.adapted_iff_coefficients w pbar.log).mp pbar.adapted
  obtain ⟨p, hp, heq, hproj⟩ := F.exists_adapted_quotient_fiber_polynomial_lift G φ hφ honto
    w pbar.log q.log hcompat hpbar q.adapted
  exact ⟨polynomialOrbitOfLog p hp, heq, hproj⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

def quotientInducedMapHeightBudget (p : ℝ) : ℝ :=
  let q := p + (p + 3) ^ 7 + 1
  ((q + 2) ^ 4 + q + 2) ^ 4

theorem lieQuotientProjection_basis_logHeight
    {L M ι κ β γ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] [Fintype ι] [Fintype κ] [Fintype β]
    (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (b : Basis β ℚ (L ⧸ I)) (c : Basis γ ℚ (M ⧸ J))
    (φ : L →ₗ⁅ℚ⁆ M) (hIJ : ∀ x ∈ I, φ x ∈ J)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hβ : (Fintype.card β : ℝ) ≤ p)
    (hI : ∀ i j, rationalLogHeight (b.repr (lieQuotientMap I (e i)) j) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (f.repr (φ (e i)) j) ≤ p)
    (hJ : ∀ i j, rationalLogHeight (c.repr (lieQuotientMap J (f i)) j) ≤ p) :
    ∀ i j, rationalLogHeight (c.repr (lieQuotientProjection I J φ hIJ (b i)) j) ≤
      quotientInducedMapHeightBudget p := by
  let H := ⌈Real.exp p⌉₊
  obtain ⟨S, hsection, hSH⟩ := exists_bounded_linear_image_section e b
    (lieQuotientMap I).toLinearMap (one_le_ceil_exp p)
    (fun i j => rationalHeightLE_ceil_exp (hI j i))
  have hright (x : L ⧸ I) : lieQuotientMap I (S x) = x := by
    obtain ⟨y, rfl⟩ := lieQuotientMap_surjective I x
    exact congrArg (fun T : L →ₗ[ℚ] (L ⧸ I) => T y) hsection
  have hcost : (rationalKernelHeight (Fintype.card β) H : ℝ) ≤ Real.exp ((p + 3) ^ 7) := by
    have h := rationalKernelHeight_le_budget (Fintype.card β) H
      (show 0 ≤ p + 1 by linarith) (hβ.trans (by linarith)) (ceil_exp_le_exp_add_one hp)
    simpa only [show p + 1 + 2 = p + 3 by ring] using h
  have hS (i : β) (j : ι) : rationalLogHeight (e.repr (S (b i)) j) ≤ (p + 3) ^ 7 :=
    rationalLogHeight_le_of_height (hSH j i) hcost
  let q := p + (p + 3) ^ 7 + 1
  have hseven : 0 ≤ (p + 3) ^ 7 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith only [hseven]
  have hsevenq : (p + 3) ^ 7 ≤ q := by dsimp [q]; linarith only [hp]
  have hmarked (i : β) (j : κ) : rationalLogHeight (f.repr (φ (S (b i))) j) ≤ (q + 2) ^ 4 :=
    linearMap_coordinate_logHeight e f φ.toLinearMap hq (hι.trans hpq)
      (fun a k => (hφ a k).trans hpq) (S (b i)) (fun a => (hS i a).trans hsevenq) j
  let t := (q + 2) ^ 4 + q
  have hfour : 0 ≤ (q + 2) ^ 4 := by positivity
  have ht : 0 ≤ t := add_nonneg hfour hq
  have hqt : q ≤ t := le_add_of_nonneg_left hfour
  have hpowt : (q + 2) ^ 4 ≤ t := le_add_of_nonneg_right hq
  intro i j
  have hinduced : lieQuotientProjection I J φ hIJ (b i) = lieQuotientMap J (φ (S (b i))) := by
    simpa only [hright] using lieQuotientProjection_mk I J φ hIJ (S (b i))
  rw [hinduced]
  exact linearMap_coordinate_logHeight f c (lieQuotientMap J).toLinearMap ht
    (hκ.trans (hpq.trans hqt)) (fun a k => (hJ a k).trans (hpq.trans hqt))
    (φ (S (b i))) (fun a => (hmarked i a).trans hpowt) j

end Erdos3

end

section

namespace Erdos3
open Module

noncomputable def quotientInducedMarkHeightBudget (p : ℝ) : ℝ :=
  (p + (p + 3) ^ 7 + 3) ^ 4

theorem quotientInducedMark_basis_logHeight
    {L M ι κ β : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] [Fintype ι] [Fintype β]
    (I : LieIdeal ℚ L) (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (b : Basis β ℚ (L ⧸ I)) (φ : L →ₗ⁅ℚ⁆ M)
    (hker : ∀ x ∈ I, φ x = 0) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hβ : (Fintype.card β : ℝ) ≤ p)
    (hI : ∀ i j, rationalLogHeight (b.repr (lieQuotientMap I (e i)) j) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (f.repr (φ (e i)) j) ≤ p) :
    ∀ i j, rationalLogHeight (f.repr (quotientInducedMark I φ hker (b i)) j) ≤
      quotientInducedMarkHeightBudget p := by
  let H := ⌈Real.exp p⌉₊
  obtain ⟨sectionMap, hsection, hheight⟩ := exists_bounded_linear_image_section e b
    (lieQuotientMap I).toLinearMap (one_le_ceil_exp p)
    (fun i j => rationalHeightLE_ceil_exp (hI j i))
  have hright (x : L ⧸ I) : lieQuotientMap I (sectionMap x) = x := by
    obtain ⟨y, rfl⟩ := lieQuotientMap_surjective I x
    exact congrArg (fun T : L →ₗ[ℚ] (L ⧸ I) => T y) hsection
  have hcost : (rationalKernelHeight (Fintype.card β) H : ℝ) ≤
      Real.exp ((p + 3) ^ 7) := by
    have h := rationalKernelHeight_le_budget (Fintype.card β) H
      (show 0 ≤ p + 1 by linarith) (hβ.trans (by linarith))
      (ceil_exp_le_exp_add_one hp)
    simpa only [show p + 1 + 2 = p + 3 by ring] using h
  have hS (i : β) (j : ι) :
      rationalLogHeight (e.repr (sectionMap (b i)) j) ≤ (p + 3) ^ 7 :=
    rationalLogHeight_le_of_height (hheight j i) hcost
  let q := p + (p + 3) ^ 7 + 1
  have hseven : 0 ≤ (p + 3) ^ 7 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hsevenq : (p + 3) ^ 7 ≤ q := by dsimp [q]; linarith
  intro i j
  have hinduced : quotientInducedMark I φ hker (b i) = φ (sectionMap (b i)) := by
    simpa only [hright] using quotientInducedMark_mk I φ hker (sectionMap (b i))
  rw [hinduced]
  have hbound := linearMap_coordinate_logHeight e f φ.toLinearMap hq (hι.trans hpq)
    (fun a k => (hφ a k).trans hpq) (sectionMap (b i))
    (fun a => (hS i a).trans hsevenq) j
  change rationalLogHeight (f.repr (φ (sectionMap (b i))) j) ≤ (q + 2) ^ 4 at hbound
  convert hbound using 1
  unfold quotientInducedMarkHeightBudget q
  congr 1
  ring

namespace RationalFilteredNilmanifold

theorem quotientInducedMark_native_logHeight
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t r d f n : ℕ}
    (D : RationalFilteredNilmanifold L s d) (Fmark : RationalFilteredNilmanifold M t f)
    (I : LieIdeal ℚ L) (Q : RationalFilteredNilmanifold (L ⧸ I) r n)
    (φ : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, φ x = 0)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hQ : Q.GeometryComplexityLE p)
    (hprojection : ∀ i j, rationalLogHeight
      (Q.basis.repr (lieQuotientMap I (D.basis j)) i) ≤ p)
    (hmark : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis j)) i) ≤ p) :
    ∀ i j, rationalLogHeight
      (Fmark.basis.repr (quotientInducedMark I φ hker (Q.basis j)) i) ≤
      quotientInducedMarkHeightBudget p := by
  intro i j
  exact quotientInducedMark_basis_logHeight I D.basis Fmark.basis Q.basis φ hker hp
    (by simpa only [Fintype.card_fin] using hD.1)
    (by simpa only [Fintype.card_fin] using hQ.1)
    (fun a k => hprojection k a) (fun a k => hmark k a) j i

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1))

noncomputable def realificationTopQuotientHom :
    ((ℝ ⊗[ℚ] L) ⧸ F.realification.layerIdeal (s + 1)) →ₗ⁅ℚ⁆
      (ℝ ⊗[ℚ] (L ⧸ F.layerIdeal (s + 1))) :=
  lieQuotientDescend (F.realification.layerIdeal (s + 1))
    (realLieHomToRat (realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1)))))
    (fun x hx => (realification_mkQ_eq_zero_iff (F.layer (s + 1)) x).mpr hx)

@[simp] theorem realificationTopQuotientHom_mk (x : ℝ ⊗[ℚ] L) :
    F.realificationTopQuotientHom (lieQuotientMap (F.realification.layerIdeal (s + 1)) x) =
      realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1))) x := rfl

theorem realificationTopQuotientHom_bijective :
    Function.Bijective F.realificationTopQuotientHom := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := lieQuotientMap_surjective (F.realification.layerIdeal (s + 1)) x
    obtain ⟨b, rfl⟩ := lieQuotientMap_surjective (F.realification.layerIdeal (s + 1)) y
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (lieQuotientMap_eq_zero _ _).mpr
    apply (realification_mkQ_eq_zero_iff (F.layer (s + 1)) (a - b)).mp
    change realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1))) (a - b) = 0
    rw [map_sub, sub_eq_zero]
    exact hxy
  · intro y
    obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective ℝ
      (lieQuotientMap_surjective (F.layerIdeal (s + 1))) y
    exact ⟨lieQuotientMap (F.realification.layerIdeal (s + 1)) x, hx⟩

noncomputable def realificationTopQuotientEquiv :
    ((ℝ ⊗[ℚ] L) ⧸ F.realification.layerIdeal (s + 1)) ≃ₗ⁅ℚ⁆
      (ℝ ⊗[ℚ] (L ⧸ F.layerIdeal (s + 1))) :=
  LieEquiv.ofBijective F.realificationTopQuotientHom F.realificationTopQuotientHom_bijective

@[simp] theorem realificationTopQuotientEquiv_mk (x : ℝ ⊗[ℚ] L) :
    F.realificationTopQuotientEquiv (lieQuotientMap (F.realification.layerIdeal (s + 1)) x) =
      realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1))) x := rfl

theorem realificationTopQuotientEquiv_mem_layer_iff (j : ℕ)
    (x : (ℝ ⊗[ℚ] L) ⧸ F.realification.layerIdeal (s + 1)) :
    F.realificationTopQuotientEquiv x ∈ F.quotientTop.realification.layer j ↔
      x ∈ F.realification.quotientTop.layer j := by
  change F.realificationTopQuotientEquiv x ∈
    ((F.layer j).map (lieQuotientMap (F.layerIdeal (s + 1))).toLinearMap).baseChange ℝ ↔ _
  rw [realification_map]
  constructor
  · rintro ⟨a, ha, he⟩
    refine ⟨a, ha, F.realificationTopQuotientEquiv.injective ?_⟩
    exact he
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem realificationTopQuotientEquiv_projection {M : Type*}
    [LieRing M] [LieAlgebra ℚ M] (G : NilpotentLieFiltration M (s + 1))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (x : (ℝ ⊗[ℚ] L) ⧸ F.realification.layerIdeal (s + 1)) :
    G.realificationTopQuotientEquiv
      (lieQuotientProjection (F.realification.layerIdeal (s + 1))
        (G.realification.layerIdeal (s + 1))
        (realLieHomToRat (realificationLieHom φ))
        (F.realificationLieHom_mem_layer G φ hφ (s + 1)) x) =
      realificationLieHom
        (lieQuotientProjection (F.layerIdeal (s + 1)) (G.layerIdeal (s + 1)) φ (hφ (s + 1)))
        (F.realificationTopQuotientEquiv x) := by
  obtain ⟨v, rfl⟩ := lieQuotientMap_surjective (F.realification.layerIdeal (s + 1)) x
  change realificationLieHom (lieQuotientMap (G.layerIdeal (s + 1)))
      (realificationLieHom φ v) =
    realificationLieHom
      (lieQuotientProjection (F.layerIdeal (s + 1)) (G.layerIdeal (s + 1)) φ (hφ (s + 1)))
      (realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1))) v)
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul r v => rfl
  | add v z hv hz => simp only [map_add, hv, hz]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeMarkedQuotientHeightBudget
namespace OAI

section

namespace Erdos3

theorem exists_nativeMarkedQuotientHeightBudget (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + A) ^ A ≤ (p + C) ^ C ∧
      quotientInducedMapHeightBudget ((p + A) ^ A) ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  let R : Polynomial ℕ := Q + (Q + 3) ^ 7 + 1
  let B : Polynomial ℕ := ((R + 2) ^ 4 + R + 2) ^ 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (Q + B)
  refine ⟨C, hC, fun p hp => ?_⟩
  have hsum : (p + A) ^ A + quotientInducedMapHeightBudget ((p + A) ^ A) ≤
      (p + C) ^ C := by
    simpa [Q, R, B, quotientInducedMapHeightBudget, Polynomial.eval₂_pow] using hbound p hp
  have hq : 0 ≤ (p + A) ^ A := pow_nonneg (add_nonneg hp (Nat.cast_nonneg A)) A
  have hb : 0 ≤ quotientInducedMapHeightBudget ((p + A) ^ A) := by
    unfold quotientInducedMapHeightBudget
    positivity
  exact ⟨(le_add_of_nonneg_right hb).trans hsum,
    (le_add_of_nonneg_left hq).trans hsum⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComparisonAmbient
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realSquarefreeLayerMap (a : SquarefreeIndex ι) :
    (F.layer (blockDegree π a.val)).baseChange ℝ →ₗ[ℝ] (ℝ ⊗[ℚ] F.SquarefreeAlgebra π) :=
  ((F.squarefreeLayerMap π a).baseChange ℝ).comp
    (realificationSubmoduleEquiv (F.layer (blockDegree π a.val))).symm.toLinearMap

theorem realSquarefreeLayerMap_tmul (a : SquarefreeIndex ι) (r : ℝ)
    (v : F.layer (blockDegree π a.val)) :
    F.realSquarefreeLayerMap π a
      (realificationSubmoduleEquiv (F.layer (blockDegree π a.val)) (r ⊗ₜ[ℚ] v)) =
      r ⊗ₜ[ℚ] F.squarefreeLayerMap π a v := by
  simp only [realSquarefreeLayerMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]

theorem realSquarefreeLayerMap_zero (a : SquarefreeIndex ι) (ha : a.val = 0)
    (v : (F.layer (blockDegree π a.val)).baseChange ℝ) :
    F.realSquarefreeLayerMap π a v = 0 := by
  obtain ⟨x, rfl⟩ := (realificationSubmoduleEquiv (F.layer (blockDegree π a.val))).surjective v
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [F.realSquarefreeLayerMap_tmul, F.squarefreeLayerMap_zero π a ha,
      TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem realSquarefreeLayerMap_mem (a : SquarefreeIndex ι)
    (v : (F.layer (blockDegree π a.val)).baseChange ℝ) :
    F.realSquarefreeLayerMap π a v ∈
      (F.squarefreeMultidegreeLayer π (fun i => a.val i)).baseChange ℝ := by
  obtain ⟨x, rfl⟩ := (realificationSubmoduleEquiv (F.layer (blockDegree π a.val))).surjective v
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [F.realSquarefreeLayerMap_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem r (F.squarefreeLayerMap_mem π a x)
  | add x y hx hy =>
    simpa only [map_add] using
      ((F.squarefreeMultidegreeLayer π (fun i => a.val i)).baseChange ℝ).add_mem hx hy

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realBlockCoefficient (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) : (F.layer (blockDegree π a.val)).baseChange ℝ :=
  ⟨coefficients p.val (blockExponent π a.val), p.property (blockExponent π a.val)⟩

noncomputable def realPolarizedCoefficient (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) : ℝ ⊗[ℚ] F.SquarefreeAlgebra π :=
  (multidegreeFactorial (blockDegree π a.val) : ℚ) •
    F.realSquarefreeLayerMap π a (F.realBlockCoefficient π p a)

theorem realPolarizedCoefficient_zero (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) (ha : a.val = 0) : F.realPolarizedCoefficient π p a = 0 := by
  rw [realPolarizedCoefficient, F.realSquarefreeLayerMap_zero π a ha, smul_zero]

theorem realPolarizedCoefficient_mem (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) :
    F.realPolarizedCoefficient π p a ∈
      (F.squarefreeMultidegreeFiltration π).realification.layer (fun i => a.val i) :=
  ((F.squarefreeMultidegreeFiltration π).realification.layer _).smul_mem _
    (F.realSquarefreeLayerMap_mem π a (F.realBlockCoefficient π p a))

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realSquarefreeInclusion :
    (ℝ ⊗[ℚ] F.SquarefreeAlgebra π) →ₗ[ℝ] (ℝ ⊗[ℚ] SquarefreePolynomial ι L) :=
  (F.squarefreeAdaptedSubalgebra π).toSubmodule.subtype.baseChange ℝ

theorem realSquarefreeInclusion_injective : Function.Injective (F.realSquarefreeInclusion π) :=
  realification_subtype_injective (F.squarefreeAdaptedSubalgebra π).toSubmodule

theorem realSquarefreeInclusion_layerMap (a : SquarefreeIndex ι) (ha : a.val ≠ 0)
    (v : (F.layer (blockDegree π a.val)).baseChange ℝ) :
    F.realSquarefreeInclusion π (F.realSquarefreeLayerMap π a v) =
      (squarefreeMonomial a).baseChange ℝ v.val := by
  obtain ⟨x, rfl⟩ := (realificationSubmoduleEquiv (F.layer (blockDegree π a.val))).surjective v
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [F.realSquarefreeLayerMap_tmul]
    change r ⊗ₜ[ℚ] (F.squarefreeLayerMap π a x).val = r ⊗ₜ[ℚ] squarefreeMonomial a x.val
    rw [F.squarefreeLayerMap_coe π a ha]
  | add x y hx hy => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hx hy

theorem realSquarefreeInclusion_permute (e : Equiv.Perm ι) (he : ∀ i, π (e i) = π i)
    (x : ℝ ⊗[ℚ] F.SquarefreeAlgebra π) :
    F.realSquarefreeInclusion π ((F.squarefreeBlockPermute π e he).toLinearMap.baseChange ℝ x) =
      (squarefreePermute (L := L) e).toLinearMap.baseChange ℝ (F.realSquarefreeInclusion π x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem realSquarefreePermute_monomial (e : Equiv.Perm ι) (a : SquarefreeIndex ι)
    (x : ℝ ⊗[ℚ] L) :
    (squarefreePermute (L := L) e).toLinearMap.baseChange ℝ
        ((squarefreeMonomial a).baseChange ℝ x) =
      (squarefreeMonomial (SquarefreeIndex.permute e a)).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, squarefreePermute_monomial]
  | add x y hx hy => simp only [map_add, hx, hy]

namespace MultidegreeLieFiltration

variable {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realPolarizedCoefficient_inclusion (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) (ha : a.val ≠ 0) :
    F.realSquarefreeInclusion π (F.realPolarizedCoefficient π p a) =
      (multidegreeFactorial (blockDegree π a.val) : ℚ) •
        (squarefreeMonomial a).baseChange ℝ (coefficients p.val (blockExponent π a.val)) := by
  rw [realPolarizedCoefficient, LinearMap.map_smul_of_tower,
    F.realSquarefreeInclusion_layerMap π a ha]
  rfl

theorem realPolarizedCoefficient_permute (p : F.realification.adaptedLieSubalgebra)
    (e : Equiv.Perm ι) (he : ∀ i, π (e i) = π i) (a : SquarefreeIndex ι) :
    (F.squarefreeBlockPermute π e he).toLinearMap.baseChange ℝ (F.realPolarizedCoefficient π p a) =
      F.realPolarizedCoefficient π p (SquarefreeIndex.permute e a) := by
  by_cases ha : a.val = 0
  · rw [F.realPolarizedCoefficient_zero π p a ha,
      F.realPolarizedCoefficient_zero π p _ ((SquarefreeIndex.permute_zero_iff e a).mpr ha),
      map_zero]
  · have hea : (SquarefreeIndex.permute e a).val ≠ 0 :=
      fun h => ha ((SquarefreeIndex.permute_zero_iff e a).mp h)
    apply F.realSquarefreeInclusion_injective π
    rw [F.realSquarefreeInclusion_permute, F.realPolarizedCoefficient_inclusion π p a ha,
      F.realPolarizedCoefficient_inclusion π p _ hea, LinearMap.map_smul_of_tower,
      realSquarefreePermute_monomial, SquarefreeIndex.permute_blockDegree π e he a,
      blockExponent_permute π e he a]

end MultidegreeLieFiltration
end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonSubalgebra : LieSubalgebra ℚ (L × F.SquarefreeAlgebra π) :=
  { F.comparisonLayer π 1 with
    lie_mem' := fun hx hy => F.comparisonLayer_antitone π (by decide : 1 ≤ 1 + 1)
      (F.comparisonLayer_lie_mem π hx hy) }

noncomputable def comparisonFiltration :
    NilpotentLieFiltration (F.comparisonSubalgebra π) (max s (Fintype.card ι)) where
  layer n := (F.comparisonLayer π n).comap (F.comparisonSubalgebra π).incl.toLinearMap
  antitone := fun _ _ h _ hx => F.comparisonLayer_antitone π h hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := fun hx hy => F.comparisonLayer_lie_mem π hx hy
  terminal := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    change x.val = (0 : L × F.SquarefreeAlgebra π)
    have h : x.val ∈ F.comparisonLayer π (max s (Fintype.card ι) + 1) := hx
    simpa only [F.comparisonLayer_terminal, Submodule.mem_bot] using h

noncomputable def comparisonFirst : F.comparisonSubalgebra π →ₗ⁅ℚ⁆ L :=
  (LieHom.fst ℚ L (F.SquarefreeAlgebra π)).comp (F.comparisonSubalgebra π).incl

noncomputable def comparisonSecond : F.comparisonSubalgebra π →ₗ⁅ℚ⁆ F.SquarefreeAlgebra π :=
  (LieHom.snd ℚ L (F.SquarefreeAlgebra π)).comp (F.comparisonSubalgebra π).incl

theorem comparisonFirst_mem_layer (n : ℕ) {x : F.comparisonSubalgebra π}
    (hx : x ∈ (F.comparisonFiltration π).layer n) : F.comparisonFirst π x ∈ F.ordinary.layer n :=
  (F.comparisonLayer_le_product π n hx).1

theorem comparisonSecond_mem_layer (n : ℕ) {x : F.comparisonSubalgebra π}
    (hx : x ∈ (F.comparisonFiltration π).layer n) :
    F.comparisonSecond π x ∈ F.squarefreeDegreeLayer π n :=
  (F.comparisonLayer_le_product π n hx).2

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonGraphLift (a : σ → ℕ) (ha : a ≠ 0) :
    F.layer a →ₗ[ℚ] F.comparisonSubalgebra π where
  toFun x := ⟨F.comparisonGraph π a ha x, F.comparisonGraph_mem_layer π 1 a ha (by
    by_contra h
    have hs : (∑ i, a i) = 0 := by omega
    apply ha
    funext i
    change a i = 0
    exact (Finset.sum_eq_zero_iff.mp hs) i (Finset.mem_univ i)) x⟩
  map_add' x y := Subtype.ext (map_add (F.comparisonGraph π a ha) x y)
  map_smul' r x := Subtype.ext (map_smul (F.comparisonGraph π a ha) r x)

theorem comparisonGraphLift_first (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    F.comparisonFirst π (F.comparisonGraphLift π a ha x) = x.val := rfl

theorem comparisonGraphLift_second (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    F.comparisonSecond π (F.comparisonGraphLift π a ha x) = F.blockLayerMap π a ha x := rfl

theorem comparisonGraphLift_mem_degree (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    F.comparisonGraphLift π a ha x ∈ (F.comparisonFiltration π).layer (∑ i, a i) :=
  F.comparisonGraph_mem_layer π _ a ha le_rfl x

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonFiltrationLayerEquiv (n : ℕ) (hn : 1 ≤ n) :
    (F.comparisonFiltration π).layer n ≃ₗ[ℚ] F.comparisonLayer π n where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, F.comparisonLayer_antitone π hn x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realComparisonGraphLift (a : σ → ℕ) (ha : a ≠ 0) :
    (F.layer a).baseChange ℝ →ₗ[ℝ] (ℝ ⊗[ℚ] F.comparisonSubalgebra π) :=
  ((F.comparisonGraphLift π a ha).baseChange ℝ).comp
    (realificationSubmoduleEquiv (F.layer a)).symm.toLinearMap

theorem realComparisonGraphLift_tmul (a : σ → ℕ) (ha : a ≠ 0) (r : ℝ) (x : F.layer a) :
    F.realComparisonGraphLift π a ha (realificationSubmoduleEquiv (F.layer a) (r ⊗ₜ[ℚ] x)) =
      r ⊗ₜ[ℚ] F.comparisonGraphLift π a ha x := by
  simp only [realComparisonGraphLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]

theorem realComparisonGraphLift_first (a : σ → ℕ) (ha : a ≠ 0)
    (x : (F.layer a).baseChange ℝ) :
    realificationLieHom (F.comparisonFirst π) (F.realComparisonGraphLift π a ha x) = x.val := by
  obtain ⟨y, rfl⟩ := (realificationSubmoduleEquiv (F.layer a)).surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    rw [F.realComparisonGraphLift_tmul, realificationLieHom_tmul, F.comparisonGraphLift_first]
    rfl
  | add y z hy hz => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hy hz

theorem realComparisonGraphLift_second (a : σ → ℕ) (ha : a ≠ 0)
    (x : (F.layer a).baseChange ℝ) :
    F.realSquarefreeInclusion π
        (realificationLieHom (F.comparisonSecond π) (F.realComparisonGraphLift π a ha x)) =
      (factorialBlockMonomial π a).baseChange ℝ x.val := by
  obtain ⟨y, rfl⟩ := (realificationSubmoduleEquiv (F.layer a)).surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    rw [F.realComparisonGraphLift_tmul, realificationLieHom_tmul, F.comparisonGraphLift_second]
    change r ⊗ₜ[ℚ] (F.blockLayerMap π a ha y).val = r ⊗ₜ[ℚ] factorialBlockMonomial π a y.val
    rw [F.blockLayerMap_coe]
  | add y z hy hz => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hy hz

theorem realComparisonGraphLift_mem_degree (a : σ → ℕ) (ha : a ≠ 0)
    (x : (F.layer a).baseChange ℝ) :
    F.realComparisonGraphLift π a ha x ∈ (F.comparisonFiltration π).realification.layer (∑ i, a i) := by
  change F.realComparisonGraphLift π a ha x ∈ ((F.comparisonFiltration π).layer (∑ i, a i)).baseChange ℝ
  obtain ⟨y, rfl⟩ := (realificationSubmoduleEquiv (F.layer a)).surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    rw [F.realComparisonGraphLift_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem r (F.comparisonGraphLift_mem_degree π a ha y)
  | add y z hy hz =>
    simpa only [map_add] using (((F.comparisonFiltration π).layer (∑ i, a i)).baseChange ℝ).add_mem hy hz

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realComparisonCoefficient (p : F.realification.adaptedLieSubalgebra)
    (a : σ →₀ ℕ) : ℝ ⊗[ℚ] F.comparisonSubalgebra π := by
  classical
  exact if ha : a = 0 then 0 else
    F.realComparisonGraphLift π (fun i => a i)
      (fun h => ha (Finsupp.ext fun i => congrFun h i))
      ⟨coefficients p.val a, p.property a⟩

theorem realComparisonCoefficient_zero_index (p : F.realification.adaptedLieSubalgebra) :
    F.realComparisonCoefficient π p 0 = 0 := by
  simp [realComparisonCoefficient]

theorem realComparisonCoefficient_zero_value (p : F.realification.adaptedLieSubalgebra)
    (a : σ →₀ ℕ) (h : coefficients p.val a = 0) : F.realComparisonCoefficient π p a = 0 := by
  by_cases ha : a = 0
  · subst a
    exact F.realComparisonCoefficient_zero_index π p
  · rw [realComparisonCoefficient, dif_neg ha]
    have hz : (⟨coefficients p.val a, p.property a⟩ :
        (F.layer (fun i => a i)).baseChange ℝ) = 0 := Subtype.ext h
    rw [hz, map_zero]

theorem realComparisonCoefficient_mem (p : F.realification.adaptedLieSubalgebra) (a : σ →₀ ℕ) :
    F.realComparisonCoefficient π p a ∈
      (F.comparisonFiltration π).realification.layer (Finsupp.weight (fun _ => 1) a) := by
  by_cases ha : a = 0
  · subst a
    rw [F.realComparisonCoefficient_zero_index]
    exact Submodule.zero_mem _
  · rw [realComparisonCoefficient, dif_neg ha]
    have h := F.realComparisonGraphLift_mem_degree π (fun i => a i)
      (fun h => ha (Finsupp.ext fun i => congrFun h i))
      ⟨coefficients p.val a, p.property a⟩
    simpa only [Finsupp.weight_eq_sum, smul_eq_mul, mul_one] using h

end Erdos3.MultidegreeLieFiltration

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type v} [Fintype ι] {L₀ H : Type u} {L : ι → Type u}
  [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing H] [LieAlgebra ℚ H]
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem optionProductMap_point_logHeight
    (φ₀ : H →ₗ⁅ℚ⁆ L₀) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i) (x : H) {p : ℝ}
    (h₀ : ∀ i, rationalLogHeight (D₀.basis.repr (φ₀ x) i) ≤ p)
    (hφ : ∀ a i, rationalLogHeight ((D a).basis.repr (φ a x) i) ≤ p) :
    ∀ i, rationalLogHeight
      ((optionProduct D₀ D).basis.repr (optionProductMap φ₀ φ x) i) ≤ p := by
  intro i
  dsimp only [optionProduct]
  rw [productFinBasis_repr]
  generalize hz : (Fintype.equivFin (Σ i : Option ι, Fin (optionDimension d₀ d i))).symm i = z
  rcases z with ⟨a, k⟩
  cases a with
  | none => exact h₀ k
  | some a => exact hφ a k

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem comparisonFirst_real_mem_layer (n : ℕ) (x : ℝ ⊗[ℚ] F.comparisonSubalgebra π)
    (hx : x ∈ (F.comparisonFiltration π).realification.layer n) :
    realificationLieHom (F.comparisonFirst π) x ∈ F.ordinary.realification.layer n :=
  (F.comparisonFiltration π).realificationLieHom_mem_layer F.ordinary (F.comparisonFirst π)
    (fun j _ hj => F.comparisonFirst_mem_layer π j hj) n x hx

theorem comparisonSecond_real_mem_layer (n : ℕ) (x : ℝ ⊗[ℚ] F.comparisonSubalgebra π)
    (hx : x ∈ (F.comparisonFiltration π).realification.layer n) :
    realificationLieHom (F.comparisonSecond π) x ∈
      (F.squarefreeOrdinaryFiltration π).realification.layer n :=
  (F.comparisonFiltration π).realificationLieHom_mem_layer (F.squarefreeOrdinaryFiltration π)
    (F.comparisonSecond π) (fun j _ hj => F.comparisonSecond_mem_layer π j hj) n x hx

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def comparisonAmbient (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) :=
  optionProduct (D.raiseStep (Nat.le_max_left s (Fintype.card (ReplicatedIndex bound))))
    (fun _ : PUnit.{1} => (M.squarefreeModel p B hB hstable).raiseStep
      (Nat.le_max_right s (Fintype.card (ReplicatedIndex bound))))

noncomputable def comparisonToAmbient :=
  optionProductMap (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1))
    (fun _ : PUnit.{1} => M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1))

theorem comparisonToAmbient_injective : Function.Injective M.comparisonToAmbient := by
  intro x y h
  apply Subtype.ext
  exact Prod.ext (congrFun h none) (congrFun h (some PUnit.unit))

theorem comparisonAmbient_geometry {p q : ℝ} (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) (hD : D.GeometryComplexityLE p)
    (hE : (M.squarefreeModel p B hB hstable).GeometryComplexityLE q) :
    (M.comparisonAmbient p B hB hstable).GeometryComplexityLE ((p + q + 4) ^ 2) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hE.1
  have h := optionProduct_geometry
    (D.raiseStep (Nat.le_max_left s (Fintype.card (ReplicatedIndex bound))))
    (fun _ : PUnit.{1} => (M.squarefreeModel p B hB hstable).raiseStep
      (Nat.le_max_right s (Fintype.card (ReplicatedIndex bound))))
    (p := p + q + 1) (by linarith)
    (by simpa only [Fintype.card_punit, Nat.cast_one] using
      (show (1 : ℝ) ≤ p + q + 1 by linarith))
    ((D.raiseStep_geometry _ hD).mono _ (by linarith))
    (fun _ => ((M.squarefreeModel p B hB hstable).raiseStep_geometry _ hE).mono _ (by linarith))
  simpa only [comparisonAmbient, show p + q + 1 + 3 = p + q + 4 by ring] using h

theorem comparisonAmbient_point_logHeight (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B)
    (x : M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))
    {q : ℝ} (hx : ∀ k, rationalLogHeight
      ((D.basis.prod (M.squarefreeFinBasis p)).repr x.val k) ≤ q) :
    ∀ k, rationalLogHeight
      ((M.comparisonAmbient p B hB hstable).basis.repr (M.comparisonToAmbient x) k) ≤ q := by
  apply optionProductMap_point_logHeight
  · exact fun k => hx (Sum.inl k)
  · exact fun _ k => hx (Sum.inr k)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ControlledReplicatedFrequency
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def replicatedFrequency (η : L →ₗ[ℚ] ℚ) :
    F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1) →ₗ[ℚ] ℚ :=
  η.comp ((F.layer bound).subtype.comp F.replicatedTopCoefficient)

theorem replicatedFrequency_apply (η : L →ₗ[ℚ] ℚ)
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    F.replicatedFrequency η x =
      η (squarefreePolynomialEquiv x.val (SquarefreeIndex.full (ReplicatedIndex bound))) := rfl

variable {κ : SquarefreeIndex (ReplicatedIndex bound) → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a))

theorem replicatedFrequency_basis_full (η : L →ₗ[ℚ] ℚ)
    (j : κ (SquarefreeIndex.full (ReplicatedIndex bound))) :
    F.replicatedFrequency η
        (F.squarefreeBasis (fun j : ReplicatedIndex bound => j.1) b ⟨SquarefreeIndex.full _, j⟩) =
      η (b (SquarefreeIndex.full _) j).val := by
  rw [F.replicatedFrequency_apply, F.squarefreeBasis_coefficient_self]

theorem replicatedFrequency_basis_ne (η : L →ₗ[ℚ] ℚ) (a : SquarefreeIndex (ReplicatedIndex bound))
    (ha : a ≠ SquarefreeIndex.full (ReplicatedIndex bound)) (j : κ a) :
    F.replicatedFrequency η (F.squarefreeBasis (fun j : ReplicatedIndex bound => j.1) b ⟨a, j⟩) = 0 := by
  rw [F.replicatedFrequency_apply, F.squarefreeBasis_coefficient_ne _ b a _ ha, map_zero]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem replicatedTopCoefficient_blockLayerMap (hb : bound ≠ 0) (x : F.layer bound) :
    F.replicatedTopCoefficient (F.blockLayerMap (fun j : ReplicatedIndex bound => j.1) bound hb x) =
      (multidegreeFactorial bound : ℚ) • x := by
  classical
  apply Subtype.ext
  rw [F.replicatedTopCoefficient_apply, F.blockLayerMap_coe,
    factorialBlockMonomial_coefficient, replicated_blockDegree_full, if_pos rfl]
  rfl

theorem replicatedFrequency_blockLayerMap_top (η : L →ₗ[ℚ] ℚ)
    (hb : bound ≠ 0) (x : F.layer bound) :
    F.replicatedFrequency η (F.blockLayerMap (fun j : ReplicatedIndex bound => j.1) bound hb x) =
      (multidegreeFactorial bound : ℚ) * η x.val := by
  change η (F.replicatedTopCoefficient (F.blockLayerMap _ bound hb x)).val = _
  rw [F.replicatedTopCoefficient_blockLayerMap hb x]
  exact map_smul η _ x.val

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem comparisonLayer_top_frequency (hstep : s = ∑ i, bound i) (η : L →ₗ[ℚ] ℚ)
    {z : L × F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)}
    (hz : z ∈ F.comparisonLayer (fun j : ReplicatedIndex bound => j.1) s) :
    (multidegreeFactorial bound : ℚ) * η z.1 = F.replicatedFrequency η z.2 := by
  have hterminal : F.comparisonProductLayer (fun j : ReplicatedIndex bound => j.1) (s + 1) = ⊥ := by
    have h := F.comparisonProductLayer_terminal (fun j : ReplicatedIndex bound => j.1)
    simpa only [replicatedIndex_card, ← hstep, max_self] using h
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
  have hu0 : u = 0 := by simpa only [hterminal, Submodule.mem_bot] using hu
  rw [hu0, zero_add]
  refine F.comparisonGraphLayer_induction (fun j : ReplicatedIndex bound => j.1) s
    (P := fun z => (multidegreeFactorial bound : ℚ) * η z.1 = F.replicatedFrequency η z.2) hv ?_ ?_ ?_
  · intro a ha hsa x
    by_cases hab : a ≤ bound
    · have heq : a = bound := by
        funext i
        apply le_antisymm (hab i)
        by_contra hi
        have hlt : a i < bound i := Nat.lt_of_not_ge hi
        have hsum : (∑ j, a j) < ∑ j, bound j :=
          Finset.sum_lt_sum (fun j _ => hab j) ⟨i, Finset.mem_univ i, hlt⟩
        omega
      subst a
      exact (F.replicatedFrequency_blockLayerMap_top η ha x).symm
    · have hx0 : x = 0 := by
        apply Subtype.ext
        have h : x.val ∈ (⊥ : Submodule ℚ L) := F.terminal a hab ▸ x.property
        exact (Submodule.mem_bot ℚ).mp h
      rw [hx0, map_zero]
      simp only [Prod.fst_zero, Prod.snd_zero, map_zero, mul_zero]
  · simp only [Prod.fst_zero, Prod.snd_zero, map_zero, mul_zero]
  · intro x y hx hy
    change (multidegreeFactorial bound : ℚ) * η (x.1 + y.1) = F.replicatedFrequency η (x.2 + y.2)
    rw [map_add, map_add, mul_add, hx, hy]

theorem comparisonTop_frequency (hstep : s = ∑ i, bound i) (η : L →ₗ[ℚ] ℚ)
    {z : F.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1)}
    (hz : z ∈ (F.comparisonFiltration (fun j : ReplicatedIndex bound => j.1)).layer s) :
    (multidegreeFactorial bound : ℚ) * η (F.comparisonFirst (fun j : ReplicatedIndex bound => j.1) z) =
      F.replicatedFrequency η (F.comparisonSecond (fun j : ReplicatedIndex bound => j.1) z) :=
  F.comparisonLayer_top_frequency hstep η hz

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realComparisonTop_frequency (hstep : s = ∑ i, bound i) (η : L →ₗ[ℚ] ℚ)
    {z : ℝ ⊗[ℚ] F.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1)}
    (hz : z ∈ (F.comparisonFiltration (fun j : ReplicatedIndex bound => j.1)).realification.layer s) :
    (multidegreeFactorial bound : ℝ) * realifyFunctional η
        (realificationLieHom (F.comparisonFirst (fun j : ReplicatedIndex bound => j.1)) z) =
      realifyFunctional (F.replicatedFrequency η)
        (realificationLieHom (F.comparisonSecond (fun j : ReplicatedIndex bound => j.1)) z) := by
  change z ∈ ((F.comparisonFiltration (fun j : ReplicatedIndex bound => j.1)).layer s).baseChange ℝ at hz
  obtain ⟨y, rfl⟩ := hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    simp only [LinearMap.baseChange_tmul, realificationLieHom_tmul, realifyFunctional_tmul]
    change (multidegreeFactorial bound : ℝ) *
      (r * (η (F.comparisonFirst (fun j : ReplicatedIndex bound => j.1) y.val) : ℝ)) =
      r * (F.replicatedFrequency η
        (F.comparisonSecond (fun j : ReplicatedIndex bound => j.1) y.val) : ℝ)
    have h := F.comparisonTop_frequency hstep η y.property
    have hr : (multidegreeFactorial bound : ℝ) *
        (η (F.comparisonFirst (fun j : ReplicatedIndex bound => j.1) y.val) : ℝ) =
        (F.replicatedFrequency η
          (F.comparisonSecond (fun j : ReplicatedIndex bound => j.1) y.val) : ℝ) := by
      exact_mod_cast h
    rw [← hr]
    ring
  | add y w hy hw => simp only [map_add, mul_add, hy, hw]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

def replicatedFrequencyHeight (d H : ℕ) : ℕ := (d + 1) * (H * H) ^ d

theorem replicatedFrequencyHeight_pos (d : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    0 < replicatedFrequencyHeight d H := by
  have hHpos : 0 < H := by omega
  unfold replicatedFrequencyHeight
  positivity

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem replicatedFrequency_basis_height {p : ℝ} (hM : M.ComplexityLE p) (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p) (j : M.SquarefreeBasisIndex) :
    RationalHeightLE (M.filtration.replicatedFrequency η (M.squarefreeBasis p j))
      (replicatedFrequencyHeight d ⌈Real.exp p⌉₊) := by
  rcases j with ⟨a, k⟩
  by_cases ha : a = SquarefreeIndex.full (ReplicatedIndex bound)
  · subst a
    change RationalHeightLE (M.filtration.replicatedFrequency η
      (M.filtration.squarefreeBasis _ (M.squarefreeCoefficientBasis p) ⟨_, k⟩)) _
    rw [M.filtration.replicatedFrequency_basis_full]
    have h := linearFunctional_coordinate_height D.basis η
      (fun i => rationalHeightLE_ceil_exp (hη i)) _ (M.squarefreeCoefficientBasis_height hM _ k)
    simp only [Fintype.card_fin] at h
    exact h
  · change RationalHeightLE (M.filtration.replicatedFrequency η
      (M.filtration.squarefreeBasis _ (M.squarefreeCoefficientBasis p) ⟨a, k⟩)) _
    rw [M.filtration.replicatedFrequency_basis_ne (M.squarefreeCoefficientBasis p) η a ha k]
    exact rationalHeightLE_zero (replicatedFrequencyHeight_pos d (one_le_ceil_exp p))

theorem replicatedFrequency_finBasis_height {p : ℝ} (hM : M.ComplexityLE p) (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p) (j) :
    RationalHeightLE (M.filtration.replicatedFrequency η (M.squarefreeFinBasis p j))
      (replicatedFrequencyHeight d ⌈Real.exp p⌉₊) := by
  rw [squarefreeFinBasis, Module.Basis.reindex_apply]
  exact M.replicatedFrequency_basis_height hM η hη _

theorem exists_replicatedFrequency_denominator {p : ℝ} (hM : M.ComplexityLE p) (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p) :
    ∃ l : ℕ, 0 < l ∧
      l ≤ replicatedFrequencyHeight d ⌈Real.exp p⌉₊ ^ Fintype.card M.SquarefreeBasisIndex ∧
      ∀ j : M.SquarefreeBasisIndex, ∃ n : ℤ,
        (l : ℚ) * M.filtration.replicatedFrequency η (M.squarefreeBasis p j) = n := by
  obtain ⟨l, hl, hbound, z, hz, _⟩ := exists_bounded_integer_array
    (fun j => M.filtration.replicatedFrequency η (M.squarefreeBasis p j))
    (M.replicatedFrequency_basis_height hM η hη)
  exact ⟨l, hl, hbound, fun j => ⟨z j, (hz j).symm⟩⟩

end RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3

end

section

namespace Erdos3

noncomputable def replicatedFrequencyDenominatorBudget (t : ℕ) (p : ℝ) : ℝ :=
  (2 : ℝ) ^ t * (p + 3) ^ 5

theorem replicatedFrequencyHeight_le_exp (d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (replicatedFrequencyHeight d H : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  have hprod : ((H * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    calc
      _ ≤ Real.exp p * Real.exp p := by rw [Nat.cast_mul]; gcongr
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  exact rational_sum_cost_le_exp d (H * H) hp 2 1 hprod
    (by simpa only [pow_one] using hd.trans (by linarith))

theorem replicatedFrequencyHeight_ceil_exp (d : ℕ) {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) :
    (replicatedFrequencyHeight d ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp ((p + 3) ^ 4) := by
  have h := replicatedFrequencyHeight_le_exp d ⌈Real.exp p⌉₊
    (p := p + 1) (by linarith) (by linarith) (ceil_exp_le_exp_add_one hp)
  have heq : p + 1 + 2 = p + 3 := by ring
  simpa only [heq] using h

theorem replicatedFrequencyDenominator_le_exp (t N d l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hN : N ≤ 2 ^ t * d)
    (hl : l ≤ replicatedFrequencyHeight d ⌈Real.exp p⌉₊ ^ N) :
    (l : ℝ) ≤ Real.exp (replicatedFrequencyDenominatorBudget t p) := by
  have hNr : (N : ℝ) ≤ (2 : ℝ) ^ t * (p + 3) := by
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast hN
      _ ≤ _ := mul_le_mul_of_nonneg_left (hd.trans (by linarith)) (by positivity)
  calc
    (l : ℝ) ≤ (replicatedFrequencyHeight d ⌈Real.exp p⌉₊ : ℝ) ^ N := by exact_mod_cast hl
    _ ≤ (Real.exp ((p + 3) ^ 4)) ^ N :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (replicatedFrequencyHeight_ceil_exp d hp hd) N
    _ = Real.exp ((N : ℝ) * (p + 3) ^ 4) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (((2 : ℝ) ^ t * (p + 3)) * (p + 3) ^ 4) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hNr (by positivity))
    _ = _ := by congr 1; unfold replicatedFrequencyDenominatorBudget; ring

end Erdos3

end

section

namespace Erdos3

noncomputable def squarefreeFrequencyInputBudget (t : ℕ) (p : ℝ) : ℝ :=
  squarefreeInputBudget t p + replicatedFrequencyDenominatorBudget t p

noncomputable def squarefreeFrequencyModelBudget (t : ℕ) (p : ℝ) : ℝ :=
  squarefreeFrequencyInputBudget t p +
    (squarefreeFrequencyInputBudget t p + (bchIntegralDenominatorBound t + 5 : ℕ)) ^
      (bchIntegralDenominatorBound t + 5)

theorem squarefreeInputBudget_le_frequency (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    squarefreeInputBudget t p ≤ squarefreeFrequencyInputBudget t p := by
  apply le_add_of_nonneg_right
  unfold replicatedFrequencyDenominatorBudget
  positivity

theorem squarefreeFrequencyInputBudget_nonneg (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ squarefreeFrequencyInputBudget t p :=
  (squarefreeInputBudget_nonneg t hp).trans (squarefreeInputBudget_le_frequency t hp)

theorem squarefreeFrequencyInputBudget_le_model (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    squarefreeFrequencyInputBudget t p ≤ squarefreeFrequencyModelBudget t p := by
  exact le_add_of_nonneg_right
    (pow_nonneg (add_nonneg (squarefreeFrequencyInputBudget_nonneg t hp) (Nat.cast_nonneg _)) _)

theorem squarefree_frequency_grid_budget (t N d l B : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hN : N ≤ 2 ^ t * d)
    (hl : (l : ℝ) ≤ Real.exp (replicatedFrequencyDenominatorBudget t p))
    (hB : B ≤ bchIntegralDenominatorBound t *
      squarefreeStructureHeight d ⌈Real.exp p⌉₊ ^ (N ^ 3) * l) :
    (B : ℝ) ≤ Real.exp (squarefreeFrequencyModelBudget t p) := by
  have hq := squarefreeFrequencyInputBudget_nonneg t hp
  have hbase := squarefreeInputBudget_le_frequency t hp
  have hNq : (N : ℝ) ≤ squarefreeFrequencyInputBudget t p := by
    apply le_trans _ hbase
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast hN
      _ ≤ (2 : ℝ) ^ t * p := mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have hHq : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp (squarefreeFrequencyInputBudget t p) :=
    (squarefreeStructureHeight_ceil_exp d hp hd).trans
      (Real.exp_le_exp.mpr ((le_add_of_nonneg_left (mul_nonneg (by positivity) hp)).trans hbase))
  have hlq : (l : ℝ) ≤ Real.exp (squarefreeFrequencyInputBudget t p) :=
    hl.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left (squarefreeInputBudget_nonneg t hp)))
  exact (Nat.cast_le.mpr hB).trans ((integral_grid_allowance_le_exp
    (bchIntegralDenominatorBound t) N _ l hq hNq hHq hlq).trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_left hq)))

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeLattice_frequency_integral (p : ℝ) (η : L →ₗ[ℚ] ℚ) (l B : ℕ)
    (hstable : M.SquarefreeGridStable p B) (hdiv : l ∣ B)
    (hη : ∀ j : M.SquarefreeBasisIndex, ∃ n : ℤ,
      (l : ℚ) * M.filtration.replicatedFrequency η (M.squarefreeBasis p j) = n)
    (g : (M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).Group)
    (hg : g ∈ M.squarefreeLattice p B hstable) :
    ∃ n : ℤ, M.filtration.replicatedFrequency η g.coord = n :=
  coordinateGrid_functional_integral (M.squarefreeBasis p) (M.filtration.replicatedFrequency η)
    l B hdiv hη hg

theorem squarefreeRealLattice_frequency_integral (p : ℝ) (η : L →ₗ[ℚ] ℚ) (l B : ℕ)
    (hB : 0 < B) (hstable : M.SquarefreeGridStable p B) (hdiv : l ∣ B)
    (hη : ∀ j : M.SquarefreeBasisIndex, ∃ n : ℤ,
      (l : ℚ) * M.filtration.replicatedFrequency η (M.squarefreeBasis p j) = n)
    (z : (M.squarefreeModel p B hB hstable).RealGroup)
    (hz : z ∈ (M.squarefreeModel p B hB hstable).realLattice) :
    ∃ n : ℤ, realifyFunctional (M.filtration.replicatedFrequency η) z.coord = n :=
  (M.squarefreeModel p B hB hstable).realLattice_functional_integral
    (M.filtration.replicatedFrequency η)
    (M.squarefreeLattice_frequency_integral p η l B hstable hdiv hη) z hz

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3

theorem exists_squarefreeFrequency_cost (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → squarefreeFrequencyModelBudget t p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let K := bchIntegralDenominatorBound t + 5
  let A := Polynomial.C (2 ^ t) * X + (X + 3) ^ 8 + Polynomial.C (2 ^ t) * (X + 3) ^ 5
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (A + (A + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [X, K, A, squarefreeFrequencyModelBudget, squarefreeFrequencyInputBudget,
    squarefreeInputBudget, replicatedFrequencyDenominatorBudget, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_controlled_replicated_frequency {p : ℝ} (hM : M.ComplexityLE p)
    (η : L →ₗ[ℚ] ℚ) (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p) :
    ∃ (B : ℕ) (hB : 0 < B) (hstable : M.SquarefreeGridStable p B),
      (M.squarefreeModelMultidegree p B hB hstable).ComplexityLE
        (squarefreeFrequencyModelBudget (∑ i, bound i) p) ∧
      (∀ i, rationalLogHeight (M.filtration.replicatedFrequency η
        ((M.squarefreeModel p B hB hstable).basis i)) ≤
          squarefreeFrequencyModelBudget (∑ i, bound i) p) ∧
      ∀ z : (M.squarefreeModel p B hB hstable).RealGroup,
        z ∈ (M.squarefreeModel p B hB hstable).realLattice →
          ∃ n : ℤ, realifyFunctional (M.filtration.replicatedFrequency η) z.coord = n := by
  let t := ∑ i, bound i
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  obtain ⟨l, hl, hlraw, hclear⟩ := M.exists_replicatedFrequency_denominator hM η hη
  have hN := M.squarefreeBasisIndex_card_le p
  have hlexp := replicatedFrequencyDenominator_le_exp t _ d l hp hM.1.1 hN hlraw
  obtain ⟨B, hB, hdiv, hBraw, hstable⟩ := M.exists_squarefree_stable_grid hM l hl
  rw [replicatedIndex_card] at hBraw
  have hbase : squarefreeInputBudget t p ≤ squarefreeFrequencyModelBudget t p :=
    (squarefreeInputBudget_le_frequency t hp).trans (squarefreeFrequencyInputBudget_le_model t hp)
  have hq : 0 ≤ squarefreeFrequencyModelBudget t p := (squarefreeInputBudget_nonneg t hp).trans hbase
  have hdq : (Fintype.card M.SquarefreeBasisIndex : ℝ) ≤ squarefreeFrequencyModelBudget t p := by
    apply le_trans _ hbase
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast hN
      _ ≤ (2 : ℝ) ^ t * p := mul_le_mul_of_nonneg_left hM.1.1 (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have h8 : (p + 3) ^ 8 ≤ squarefreeFrequencyModelBudget t p :=
    (le_add_of_nonneg_left (mul_nonneg (by positivity) hp)).trans hbase
  have hHq : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp (squarefreeFrequencyModelBudget t p) :=
    (squarefreeStructureHeight_ceil_exp d hp hM.1.1).trans (Real.exp_le_exp.mpr h8)
  have hGq : (replicatedFrequencyHeight d ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp (squarefreeFrequencyModelBudget t p) :=
    (replicatedFrequencyHeight_ceil_exp d hp hM.1.1).trans (Real.exp_le_exp.mpr
      ((pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 3) (by decide : 4 ≤ 8)).trans h8))
  refine ⟨B, hB, hstable, ?_, ?_, ?_⟩
  · exact M.squarefreeModel_complexity hM B hB hstable hq hdq
      (squarefree_frequency_grid_budget t _ d l B hp hM.1.1 hN hlexp hBraw) hHq
  · intro i
    exact rationalLogHeight_le_of_height (M.replicatedFrequency_finBasis_height hM η hη i) hGq
  · intro z hz
    exact M.squarefreeRealLattice_frequency_integral p η l B hB hstable hdiv hclear z hz

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ComparisonLattice
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def comparisonLattice (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) : Subgroup
      (M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1)).Group :=
  (M.comparisonAmbient p B hB hstable).lattice.comap
    (NilpotentLieBCHGroup.mapOfSteps M.comparisonToAmbient)

theorem comparisonLattice_first (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) :
    M.comparisonLattice p B hB hstable ≤ D.lattice.comap
      (NilpotentLieBCHGroup.mapOfSteps
        (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1))) := by
  intro g hg
  have hg' : NilpotentLieBCHGroup.mapOfSteps M.comparisonToAmbient g ∈
      (M.comparisonAmbient p B hB hstable).lattice := hg
  have h := (mem_piBCHSubgroup _ _ _).mp hg' none
  exact D.raiseStep_lattice_back (Nat.le_max_left s (Fintype.card (ReplicatedIndex bound))) h

theorem comparisonLattice_second (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) :
    M.comparisonLattice p B hB hstable ≤ (M.squarefreeModel p B hB hstable).lattice.comap
      (NilpotentLieBCHGroup.mapOfSteps
        (M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1))) := by
  intro g hg
  have hg' : NilpotentLieBCHGroup.mapOfSteps M.comparisonToAmbient g ∈
      (M.comparisonAmbient p B hB hstable).lattice := hg
  have h := (mem_piBCHSubgroup _ _ _).mp hg' (some PUnit.unit)
  exact (M.squarefreeModel p B hB hstable).raiseStep_lattice_back
    (Nat.le_max_right s (Fintype.card (ReplicatedIndex bound))) h

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledComparisonModel
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L K : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
  {s t d r : ℕ} (D : RationalFilteredNilmanifold L s d)

theorem exists_model_of_bounded_embedding (F : NilpotentLieFiltration K t)
    (b : Basis (Fin r) ℚ K) (φ : K →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ)
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ j k, RationalHeightLE (D.basis.repr (φ (b j)) k) H)
    (hlayers : ∀ n : Fin (t + 1),
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, RationalHeightLE (D.basis.repr (φ (a j : K)) k) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hr : (r : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hgrid : (D.grid : ℝ) ≤ Real.exp p) :
    ∃ E : RationalFilteredNilmanifold K t r,
      E.filtration = F ∧ E.basis = b ∧
      E.lattice = D.lattice.comap (NilpotentLieBCHGroup.mapOfSteps φ) ∧
      E.GeometryComplexityLE ((p + 2) ^ 11) := by
  classical
  have hd' : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hd
  have hr' : (Fintype.card (Fin r) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hr
  have hmatrix : ∀ i j, RationalHeightLE (LinearMap.toMatrix b D.basis φ.toLinearMap i j) H := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    exact hb j i
  obtain ⟨N, hN, hNb, hin, hout⟩ := exists_bchSubgroup_comap_grid_of_steps
    (hM := F.lowerCentralSeries_eq_bot) b D.basis φ hφ D.lattice hH D.grid_pos
    hmatrix D.inner_grid D.outer_grid hp hd' hr' hHp hgrid
  obtain ⟨_, _, _, hbracket⟩ := exists_bounded_lie_embedding_retraction b D.basis φ hφ hH hc hmatrix
  have hbracketBudget := rationalLieStructureHeight_inverse_budget d r H hp hd hr hHp
  choose a ha using hlayers
  have hLayer (n : Fin (t + 1)) (j) (k) :
      rationalLogHeight (b.repr (a n j : K) k) ≤ (p + 2) ^ 8 := by
    apply rationalLogHeight_le_of_height
      (embedding_basis_coordinate_height b D.basis φ.toLinearMap hφ hH
        (fun i j => hb j i) (a n j : K) (ha n j) k)
    simpa only [Fintype.card_fin] using
      embedding_coordinate_height_budget d r H H hp hd hr hHp hHp
  let E : RationalFilteredNilmanifold K t r :=
    { filtration := F
      basis := b
      layerBasis := a
      lattice := D.lattice.comap (NilpotentLieBCHGroup.mapOfSteps φ)
      grid := N
      grid_pos := hN
      inner_grid := hin
      outer_grid := hout }
  have hp1 : 1 ≤ p + 2 := by linarith
  have h9 : (p + 2) ^ 9 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  have h8 : (p + 2) ^ 8 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  refine ⟨E, rfl, rfl, rfl, hr.trans (le_power_budget hp (by decide)),
    hNb.trans (Real.exp_le_exp.mpr h9), ?_, ?_⟩
  · intro i j k
    apply rationalLogHeight_le_of_height (hbracket i j k)
    simpa only [Fintype.card_fin] using hbracketBudget
  · exact fun n j k => (hLayer n j k).trans h8

include D in
theorem embedding_basis_card_le (b : Basis (Fin r) ℚ K)
    (φ : K →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ) : r ≤ d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  have h := LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) hφ
  simpa only [finrank_eq_card_basis b, finrank_eq_card_basis D.basis, Fintype.card_fin] using h

theorem exists_model_of_embedding_logHeight (F : NilpotentLieFiltration K t)
    (b : Basis (Fin r) ℚ K) (φ : K →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ)
    {p : ℝ} (hD : D.GeometryComplexityLE p)
    (hb : ∀ j k, rationalLogHeight (D.basis.repr (φ (b j)) k) ≤ p)
    (hlayers : ∀ n : Fin (t + 1),
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, rationalLogHeight (D.basis.repr (φ (a j : K)) k) ≤ p) :
    ∃ E : RationalFilteredNilmanifold K t r,
      E.filtration = F ∧ E.basis = b ∧
      E.lattice = D.lattice.comap (NilpotentLieBCHGroup.mapOfSteps φ) ∧
      E.GeometryComplexityLE ((p + 3) ^ 11) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  have hr : (r : ℝ) ≤ p := (Nat.cast_le.mpr (D.embedding_basis_card_le b φ hφ)).trans hD.1
  have hLayer : ∀ n : Fin (t + 1),
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, RationalHeightLE (D.basis.repr (φ (a j : K)) k) ⌈Real.exp p⌉₊ := by
    intro n
    obtain ⟨a, ha⟩ := hlayers n
    exact ⟨a, fun j k => rationalHeightLE_ceil_exp (ha j k)⟩
  obtain ⟨E, hEF, hEb, hEL, hE⟩ := D.exists_model_of_bounded_embedding F b φ hφ
    (one_le_ceil_exp p) (fun j k => rationalHeightLE_ceil_exp (hb j k)) hLayer
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    (by linarith : 0 ≤ p + 1) (hD.1.trans (by linarith)) (hr.trans (by linarith))
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  refine ⟨E, hEF, hEb, hEL, ?_⟩
  convert hE using 1
  ring

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_dilationPair_layer_basis (q : ℚ) (n : ℕ) (hn : 1 ≤ n)
    {p : ℝ} (hD : D.GeometryComplexityLE p) (hq : rationalLogHeight q ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ (D.filtration.dilationPairLayer q n))) ℚ
        (D.filtration.dilationPairLayer q n),
      ∀ j k, rationalLogHeight (D.basis.repr (b j).val.1 k) ≤ (n + 1 : ℝ) * (p + 1) ∧
        rationalLogHeight (D.basis.repr (b j).val.2 k) ≤ (n + 1 : ℝ) * (p + 1) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  obtain ⟨a, ha⟩ := D.exists_positive_layer_basis (n + 1) (by omega) hD
  obtain ⟨b, hb⟩ := D.exists_positive_layer_basis n hn hD
  obtain ⟨c, hc⟩ := exists_scaledPair_basis_height D.basis
    (D.filtration.layer n) (D.filtration.layer (n + 1)) (D.filtration.antitone (Nat.le_succ n))
    a b (q ^ n) hH (one_le_pow₀ hH) ((rationalHeightLE_ceil_exp hq).pow n)
    (fun j k => rationalHeightLE_ceil_exp (ha j k))
    (fun j k => rationalHeightLE_ceil_exp (hb j k))
  have hbound : ((H * H ^ n : ℕ) : ℝ) ≤ Real.exp ((n + 1 : ℝ) * (p + 1)) := by
    rw [← pow_succ']
    simpa only [Nat.cast_add, Nat.cast_one] using ceil_exp_power_le_exp hp (n + 1)
  exact ⟨c, fun j k => ⟨rationalLogHeight_le_of_height (hc j k).1 hbound,
    rationalLogHeight_le_of_height (hc j k).2 hbound⟩⟩

theorem exists_dilationPair_filtration_basis (q : ℚ) (n : ℕ) (hn : 1 ≤ n)
    {p : ℝ} (hD : D.GeometryComplexityLE p) (hq : rationalLogHeight q ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ ((D.filtration.dilationPairFiltration q).layer n))) ℚ
        ((D.filtration.dilationPairFiltration q).layer n),
      ∀ j k, rationalLogHeight (D.basis.repr (b j).val.val.1 k) ≤ (n + 1 : ℝ) * (p + 1) ∧
        rationalLogHeight (D.basis.repr (b j).val.val.2 k) ≤ (n + 1 : ℝ) * (p + 1) := by
  obtain ⟨b, hb⟩ := D.exists_dilationPair_layer_basis q n hn hD hq
  let e := D.filtration.dilationPairFiltrationLayerEquiv q n hn
  let c := (b.map e.symm).reindex (finCongr e.finrank_eq.symm)
  have hval (j) :
      ((c j : D.filtration.dilationPairSubalgebra q) : L × L) =
        (b ((finCongr e.finrank_eq.symm).symm j)).val := by
    simp only [c, Basis.reindex_apply, Basis.map_apply, e,
      NilpotentLieFiltration.dilationPairFiltrationLayerEquiv]
    rfl
  refine ⟨c, fun j k => ?_⟩
  rw [hval]
  exact hb _ k

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

def pairToPi : (L × L) →ₗ⁅ℚ⁆ (Fin 2 → L) :=
  liePiMap ![LieHom.fst ℚ L L, LieHom.snd ℚ L L]

@[simp] theorem pairToPi_zero (x : L × L) : pairToPi x 0 = x.1 := rfl

@[simp] theorem pairToPi_one (x : L × L) : pairToPi x 1 = x.2 := rfl

theorem pairToPi_injective : Function.Injective (pairToPi (L := L)) := by
  intro x y h
  exact Prod.ext (congrFun h 0) (congrFun h 1)

namespace NilpotentLieFiltration

variable {s : ℕ} (F : NilpotentLieFiltration L s)

def dilationPairToPi (q : ℚ) : F.dilationPairSubalgebra q →ₗ⁅ℚ⁆ (Fin 2 → L) :=
  pairToPi.comp (F.dilationPairSubalgebra q).incl

theorem dilationPairToPi_injective (q : ℚ) : Function.Injective (F.dilationPairToPi q) :=
  fun _ _ h => Subtype.ext (pairToPi_injective h)

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {s d : ℕ} (D : RationalFilteredNilmanifold L s d)

theorem pair_product_basis_logHeight (x : L × L) {p : ℝ}
    (hx : ∀ k, rationalLogHeight (D.basis.repr x.1 k) ≤ p ∧
      rationalLogHeight (D.basis.repr x.2 k) ≤ p)
    (k : Fin (Fintype.card (Σ _ : Fin 2, Fin d))) :
    rationalLogHeight ((pi (fun _ : Fin 2 => D)).basis.repr (pairToPi x) k) ≤ p := by
  have h (j : Fin 2) (l : Fin d) : rationalLogHeight (D.basis.repr (pairToPi x j) l) ≤ p := by
    fin_cases j
    · exact (hx l).1
    · exact (hx l).2
  rw [productFinBasis_repr]
  exact h _ _

end RationalFilteredNilmanifold

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

noncomputable def dilationPairLattice (q : ℚ) : Subgroup (D.filtration.dilationPairFiltration q).Group :=
  (pi (fun _ : Fin 2 => D)).lattice.comap
    (NilpotentLieBCHGroup.mapOfSteps (D.filtration.dilationPairToPi q))

noncomputable def dilationPairGeometryBudget (s : ℕ) (p : ℝ) : ℝ :=
  ((p + 4) ^ 2 + (s + 2) * (p + 1) + 6) ^ 11

theorem exists_dilationPair_model (q : ℚ) {p : ℝ}
    (hD : D.GeometryComplexityLE p) (hq : rationalLogHeight q ≤ p) :
    ∃ E : RationalFilteredNilmanifold (D.filtration.dilationPairSubalgebra q) s
        (finrank ℚ (D.filtration.dilationPairSubalgebra q)),
      E.filtration = D.filtration.dilationPairFiltration q ∧
      E.lattice = D.dilationPairLattice q ∧
      E.GeometryComplexityLE (dilationPairGeometryBudget s p) ∧
      finrank ℚ (D.filtration.dilationPairSubalgebra q) ≤ 2 * d ∧
      ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ 2 * (p + 1) ∧
        rationalLogHeight (D.basis.repr (E.basis j).val.2 k) ≤ 2 * (p + 1) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  let P := pi (fun _ : Fin 2 => D)
  let K := D.filtration.dilationPairSubalgebra q
  let F := D.filtration.dilationPairFiltration q
  let φ := D.filtration.dilationPairToPi q
  let C : ℝ := (s + 2) * (p + 1)
  let R : ℝ := (p + 4) ^ 2 + C + 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCR : C ≤ R := by dsimp [R]; nlinarith only [sq_nonneg (p + 4)]
  have hP : P.GeometryComplexityLE R := by
    have hh := pi_geometry (fun _ : Fin 2 => D) (by linarith : 0 ≤ p + 2)
      (by simpa using (show (2 : ℝ) ≤ p + 2 by linarith))
      (fun _ => hD.mono D (by linarith : p ≤ p + 2))
    have hgeom : P.GeometryComplexityLE ((p + 4) ^ 2) := by
      simpa only [show p + 2 + 2 = p + 4 by ring] using hh
    exact hgeom.mono P (by dsimp [R]; linarith)
  obtain ⟨b, hb⟩ := D.exists_dilationPair_layer_basis q 1 (by decide) hD hq
  let bK : Basis (Fin (finrank ℚ K)) ℚ K := b
  have hbase : 2 * (p + 1) ≤ C := by
    apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ p + 1)
    exact le_add_of_nonneg_left (Nat.cast_nonneg s)
  have hbK (j) (k) : rationalLogHeight (P.basis.repr (φ (bK j)) k) ≤ R := by
    apply D.pair_product_basis_logHeight
    intro l
    have hh := hb j l
    norm_num only [Nat.cast_one, one_add_one_eq_two] at hh
    exact ⟨hh.1.trans (hbase.trans hCR), hh.2.trans (hbase.trans hCR)⟩
  have hlayers (n : Fin (s + 1)) :
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, rationalLogHeight (P.basis.repr (φ (a j)) k) ≤ R := by
    obtain ⟨a, ha⟩ := D.exists_dilationPair_filtration_basis q (n.val + 1) (by omega) hD hq
    refine ⟨a, fun j k => ?_⟩
    have hn : ((n.val + 1 : ℕ) + 1 : ℝ) ≤ (s + 2 : ℝ) := by
      exact_mod_cast (show n.val + 1 + 1 ≤ s + 2 by omega)
    have hbound := mul_le_mul_of_nonneg_right hn (show 0 ≤ p + 1 by linarith)
    apply D.pair_product_basis_logHeight
    intro l
    exact ⟨(ha j l).1.trans (hbound.trans hCR), (ha j l).2.trans (hbound.trans hCR)⟩
  have hφ := D.filtration.dilationPairToPi_injective q
  obtain ⟨E, hEF, hEb, hEL, hE⟩ := P.exists_model_of_embedding_logHeight F bK φ hφ hP hbK hlayers
  have hdim : finrank ℚ K ≤ 2 * d := by
    have hh := P.embedding_basis_card_le bK φ hφ
    simpa only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, smul_eq_mul] using hh
  refine ⟨E, hEF, hEL, ?_, hdim, ?_⟩
  · simpa only [R, C, dilationPairGeometryBudget, add_assoc,
      show (3 : ℝ) + 3 = 6 by norm_num] using hE
  · intro j k
    rw [hEb]
    have hh := hb j k
    norm_num only [Nat.cast_one, one_add_one_eq_two] at hh
    exact hh

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_dilationPair_model_of_eq (F : NilpotentLieFiltration L s)
    (hF : F = D.filtration) (q : ℚ) {p : ℝ}
    (hD : D.GeometryComplexityLE p) (hq : rationalLogHeight q ≤ p) :
    ∃ E : RationalFilteredNilmanifold (F.dilationPairSubalgebra q) s
        (finrank ℚ (F.dilationPairSubalgebra q)),
      E.filtration = F.dilationPairFiltration q ∧
      E.lattice = (pi (fun _ : Fin 2 => D)).lattice.comap
        (NilpotentLieBCHGroup.mapOfSteps (F.dilationPairToPi q)) ∧
      E.GeometryComplexityLE (dilationPairGeometryBudget s p) ∧
      finrank ℚ (F.dilationPairSubalgebra q) ≤ 2 * d ∧
      ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ 2 * (p + 1) ∧
        rationalLogHeight (D.basis.repr (E.basis j).val.2 k) ≤ 2 * (p + 1) := by
  subst F
  exact D.exists_dilationPair_model q hD hq

namespace MultidegreeStructure

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ}
  {D : RationalFilteredNilmanifold L s d} (M : D.MultidegreeStructure bound)

noncomputable def dilationPairLattice (q : ℚ) :
    Subgroup (M.filtration.ordinary.dilationPairFiltration q).Group :=
  (pi (fun _ : Fin 2 => D)).lattice.comap
    (NilpotentLieBCHGroup.mapOfSteps (M.filtration.ordinary.dilationPairToPi q))

theorem dilationPairLattice_mem (q : ℚ)
    (x : (M.filtration.ordinary.dilationPairFiltration q).Group) :
    x ∈ M.dilationPairLattice q ↔
      (⟨x.coord.val.1⟩ : D.filtration.Group) ∈ D.lattice ∧
      (⟨x.coord.val.2⟩ : D.filtration.Group) ∈ D.lattice := by
  change (NilpotentLieBCHGroup.mapOfSteps (M.filtration.ordinary.dilationPairToPi q) x) ∈
    piBCHSubgroup (fun _ : Fin 2 => D.filtration) (fun _ : Fin 2 => D.lattice) ↔ _
  rw [mem_piBCHSubgroup]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · intro h j
    fin_cases j
    · exact h.1
    · exact h.2

theorem exists_dilationPair_model (q : ℚ) {p : ℝ}
    (hM : M.ComplexityLE p) (hq : rationalLogHeight q ≤ p) :
    ∃ E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s
        (finrank ℚ (M.filtration.ordinary.dilationPairSubalgebra q)),
      E.filtration = M.filtration.ordinary.dilationPairFiltration q ∧
      E.lattice = M.dilationPairLattice q ∧
      E.GeometryComplexityLE (dilationPairGeometryBudget s p) ∧
      finrank ℚ (M.filtration.ordinary.dilationPairSubalgebra q) ≤ 2 * d ∧
      ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ 2 * (p + 1) ∧
        rationalLogHeight (D.basis.repr (E.basis j).val.2 k) ≤ 2 * (p + 1) :=
  D.exists_dilationPair_model_of_eq M.filtration.ordinary M.ordinary q hM.1 hq

end MultidegreeStructure

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_comparison_layer_basis {p : ℝ} (hM : M.ComplexityLE p) (n : ℕ) :
    ∃ b : Basis (Fin (finrank ℚ
        (M.filtration.comparisonLayer (fun i : ReplicatedIndex bound => i.1) n))) ℚ
        (M.filtration.comparisonLayer (fun i : ReplicatedIndex bound => i.1) n),
      ∀ j k, rationalLogHeight
        ((D.basis.prod (M.squarefreeFinBasis p)).repr (b j).val k) ≤
        comparisonBasisBudget (∑ i, bound i) p := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  obtain ⟨b, hb⟩ := M.exists_comparison_layer_basis_height hM n
  exact ⟨b, fun j k => rationalLogHeight_le_of_height (hb j k)
    (comparisonBasisHeight_le_exp bound hp)⟩

theorem exists_comparison_filtration_basis {p : ℝ} (hM : M.ComplexityLE p)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ b : Basis (Fin (finrank ℚ
        ((M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1)).layer n))) ℚ
        ((M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1)).layer n),
      ∀ j k, rationalLogHeight
        ((D.basis.prod (M.squarefreeFinBasis p)).repr (b j).val.val k) ≤
        comparisonBasisBudget (∑ i, bound i) p := by
  obtain ⟨b, hb⟩ := M.exists_comparison_layer_basis hM n
  let e := M.filtration.comparisonFiltrationLayerEquiv
    (fun i : ReplicatedIndex bound => i.1) n hn
  let c := (b.map e.symm).reindex (finCongr e.finrank_eq.symm)
  have hval (j) : (c j).val.val = (b ((finCongr e.finrank_eq.symm).symm j)).val := by
    simp only [c, Basis.reindex_apply, Basis.map_apply, e,
      MultidegreeLieFiltration.comparisonFiltrationLayerEquiv]
    rfl
  refine ⟨c, fun j k => ?_⟩
  rw [hval]
  exact hb _ k

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def comparisonGeometryBudget (t : ℕ) (p q : ℝ) : ℝ :=
  ((p + q + 4) ^ 2 + comparisonBasisBudget t p + 6) ^ 11

theorem exists_comparison_model {p q : ℝ} (hM : M.ComplexityLE p)
    (B : ℕ) (hB : 0 < B) (hstable : M.SquarefreeGridStable p B)
    (hE : (M.squarefreeModel p B hB hstable).GeometryComplexityLE q) :
    ∃ E : RationalFilteredNilmanifold
        (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))
        (max s (Fintype.card (ReplicatedIndex bound)))
        (finrank ℚ (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))),
      E.filtration = M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1) ∧
      E.lattice = M.comparisonLattice p B hB hstable ∧
      E.GeometryComplexityLE (comparisonGeometryBudget (∑ i, bound i) p q) ∧
      ∀ j k, rationalLogHeight
        ((D.basis.prod (M.squarefreeFinBasis p)).repr (E.basis j).val k) ≤
        comparisonBasisBudget (∑ i, bound i) p := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let P := M.comparisonAmbient p B hB hstable
  let K := M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1)
  let F := M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1)
  let C := comparisonBasisBudget (∑ i, bound i) p
  let R := (p + q + 4) ^ 2 + C + 3
  have hC : 0 ≤ C := by dsimp [C, comparisonBasisBudget]; positivity
  have hCR : C ≤ R := by dsimp [R]; nlinarith only [sq_nonneg (p + q + 4)]
  have hP : P.GeometryComplexityLE R :=
    (M.comparisonAmbient_geometry B hB hstable hM.1 hE).mono P
      (by dsimp [R]; linarith)
  obtain ⟨b, hb⟩ := M.exists_comparison_layer_basis hM 1
  let bK : Basis (Fin (finrank ℚ K)) ℚ K := b
  have hbK (j k) : rationalLogHeight (P.basis.repr (M.comparisonToAmbient (bK j)) k) ≤ R :=
    (M.comparisonAmbient_point_logHeight p B hB hstable (bK j) (hb j) k).trans hCR
  have hlayers (n : Fin (max s (Fintype.card (ReplicatedIndex bound)) + 1)) :
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, rationalLogHeight
          (P.basis.repr (M.comparisonToAmbient (a j : K)) k) ≤ R := by
    obtain ⟨a, ha⟩ := M.exists_comparison_filtration_basis hM (n.val + 1) (by omega)
    exact ⟨a, fun j k =>
      (M.comparisonAmbient_point_logHeight p B hB hstable (a j) (ha j) k).trans hCR⟩
  obtain ⟨E, hEF, hEb, hEL, hgeom⟩ := P.exists_model_of_embedding_logHeight F bK
    M.comparisonToAmbient M.comparisonToAmbient_injective hP hbK hlayers
  refine ⟨E, hEF, hEL, ?_, ?_⟩
  · simpa only [R, C, comparisonGeometryBudget, add_assoc,
      show (3 : ℝ) + 3 = 6 by norm_num] using hgeom
  · intro j k
    rw [hEb]
    exact hb j k

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCrossFactorization
namespace OAI

section

namespace Erdos3

variable {G : Type*} [Add G]

noncomputable def fourPointProduct (f₁ f₂ f₃ f₄ : G → ℂ) (a x : G) : ℂ :=
  star (f₁ x) * f₂ (x + a) * f₃ x * star (f₄ (x + a))

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeVectorCorrelation {I : Type*} (degree N : ℕ) [NeZero N] (p : ℝ)
    (f : I → ZMod N → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest (fun _ : Unit => 1)
  complexity : test.ComplexityLE p
  coordinate : I
  correlation : Real.exp (-p) ≤
    ‖𝔼 x, f coordinate x * star (test.evalCyclic N (fun _ => x))‖

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

namespace NativeVectorCorrelation

noncomputable def mono {I : Type*} {degree N : ℕ} [NeZero N] {p q : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f) (hpq : p ≤ q) :
    NativeVectorCorrelation degree N q f :=
  { W with
    complexity := W.complexity.mono hpq
    correlation := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans W.correlation }

theorem exists_of_mean {I : Type*} (degree N : ℕ) [NeZero N] {p : ℝ}
    (f : I → ZMod N → ℂ) (hp : 2 ≤ p) (h : ∃ i, Real.exp (-p) ≤ ‖𝔼 x, f i x‖) :
    Nonempty (NativeVectorCorrelation degree N p f) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨{
    L := RationalTorus.Algebra 0
    dim := 0
    model := RationalTorus.trivialNilmanifold degree
    test := RationalFilteredNilmanifold.Niltest.const _ (fun _ : Unit => 1) 1
    complexity := RationalTorus.trivialNilmanifold_const_one_complexity degree _ hp
    coordinate := i
    correlation := ?_
  }⟩
  simpa only [RationalFilteredNilmanifold.Niltest.evalCyclic,
    RationalFilteredNilmanifold.Niltest.eval, RationalFilteredNilmanifold.Niltest.const,
    star_one, mul_one] using hi

end NativeVectorCorrelation

end Erdos3

end

section

namespace Erdos3.NativeVectorCorrelation

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_of_mean_approx {I : Type*} {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f)
    (g : I → ZMod N → ℂ)
    (herr : (𝔼 x, ‖f W.coordinate x - g W.coordinate x‖) ≤ Real.exp (-(2 * p)) / 2) :
    Nonempty (NativeVectorCorrelation degree N (p + 1) g) := by
  let b (x : ZMod N) := star (W.test.evalCyclic N (fun _ => x))
  have hb (x : ZMod N) : ‖b x‖ ≤ Real.exp p := by
    simpa only [b, norm_star, RationalFilteredNilmanifold.Niltest.evalCyclic] using W.test.eval_budget W.complexity
      (fun _ : Unit => (x.val : ℤ))
  have he := mean_error_mul_bounded (f W.coordinate) (g W.coordinate) b
    (Real.exp_pos p).le hb herr
  have hexp : Real.exp p * (Real.exp (-(2 * p)) / 2) = Real.exp (-p) / 2 := by
    rw [← mul_div_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hexp] at he
  have hdiff : ‖(𝔼 x, f W.coordinate x * b x) -
      (𝔼 x, g W.coordinate x * b x)‖ ≤ Real.exp (-p) / 2 := by
    rw [← Finset.expect_sub_distrib]
    exact (RCLike.norm_expect_le (K := ℂ)).trans he
  have hretain : Real.exp (-p) / 2 ≤ ‖𝔼 x, g W.coordinate x * b x‖ := by
    have htri := norm_le_norm_add_norm_sub
      (𝔼 x, g W.coordinate x * b x) (𝔼 x, f W.coordinate x * b x)
    rw [norm_sub_rev] at htri
    have hc : Real.exp (-p) ≤ ‖𝔼 x, f W.coordinate x * b x‖ := W.correlation
    linarith
  refine ⟨{ W with complexity := W.complexity.mono (by linarith), correlation := ?_ }⟩
  have ht : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
    simpa only [neg_add, sub_eq_add_neg] using exp_sub_one_le_half_exp (-p)
  exact ht.trans hretain

theorem exists_of_uniform_approx {I : Type*} {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f)
    (g : I → ZMod N → ℂ)
    (herr : ∀ i x, ‖f i x - g i x‖ ≤ Real.exp (-(2 * p)) / 2) :
    Nonempty (NativeVectorCorrelation degree N (p + 1) g) := by
  apply W.exists_of_mean_approx g
  calc
    _ ≤ 𝔼 _x : ZMod N, Real.exp (-(2 * p)) / 2 :=
      Finset.expect_le_expect (fun x _ => herr W.coordinate x)
    _ = _ := by simp

end Erdos3.NativeVectorCorrelation

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

noncomputable def nativeCrossResidual {N : ℕ} (f₀ f₁ : ZMod N → ℂ)
    (m : ZMod N → ZMod N → ℂ) (h : ZMod N) (_ : Unit) (x : ZMod N) : ℂ :=
  f₀ x * star (f₁ (x + h)) * star (m h x)

abbrev NativeCrossWitnesses (s N : ℕ) [NeZero N] (p : ℝ)
    (f₀ f₁ : ZMod N → ℂ) (m : ZMod N → ZMod N → ℂ) (H : Finset (ZMod N)) :=
  ∀ h : H, NativeVectorCorrelation s N p (nativeCrossResidual f₀ f₁ m h.val)

namespace NativeCrossWitnesses

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

noncomputable def product (h : H) (x : ZMod N) : ℂ :=
  m h.val x * (U h).test.evalCyclic N (fun _ => x)

noncomputable def extension (h x : ZMod N) : ℂ :=
  if hh : h ∈ H then U.product ⟨h, hh⟩ x else 0

theorem extension_of_mem (h : ZMod N) (hh : h ∈ H) (x : ZMod N) :
    U.extension h x = U.product ⟨h, hh⟩ x := by
  simp only [extension, dif_pos hh]

theorem extension_of_not_mem (h : ZMod N) (hh : h ∉ H) (x : ZMod N) :
    U.extension h x = 0 := by
  simp only [extension, dif_neg hh]

theorem product_norm (hm : ∀ h x, ‖m h x‖ ≤ 1) (h : H) (x : ZMod N) :
    ‖U.product h x‖ ≤ Real.exp p := by
  have hT := (U h).test.eval_budget (U h).complexity (fun _ : Unit => (x.val : ℤ))
  change ‖(U h).test.evalCyclic N (fun _ => x)‖ ≤ Real.exp p at hT
  rw [product, norm_mul]
  simpa only [one_mul] using mul_le_mul (hm h.val x) hT (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem extension_norm (hm : ∀ h x, ‖m h x‖ ≤ 1) (h x : ZMod N) :
    ‖U.extension h x‖ ≤ Real.exp p := by
  by_cases hh : h ∈ H
  · rw [U.extension_of_mem h hh]
    exact U.product_norm hm ⟨h, hh⟩ x
  · rw [U.extension_of_not_mem h hh, norm_zero]
    exact Real.exp_nonneg _

theorem product_correlation (h : H) :
    Real.exp (-p) ≤
      ‖𝔼 x, (f₀ x * star (f₁ (x + h.val))) * star (U.product h x)‖ := by
  simpa only [product, nativeCrossResidual, star_mul, mul_assoc, mul_left_comm, mul_comm]
    using (U h).correlation

noncomputable def mono (hpq : p ≤ q) : NativeCrossWitnesses s N q f₀ f₁ m H :=
  fun h => (U h).mono hpq

end NativeCrossWitnesses

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_native_two_unit_comparison {A I J : Type*} [Fintype I] [Fintype J]
    {degree N : ℕ} [NeZero N] {p q r : ℝ}
    (f : A → ZMod N → ℂ) (v a : I → ZMod N → ℂ) (b : J → ZMod N → ℂ)
    (ha : ∀ x, ∑ i, ‖a i x‖ ^ 2 = 1) (hb : ∀ x, ∑ j, ‖b j x‖ ^ 2 = 1)
    (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp q) (hJ : (Fintype.card J : ℝ) ≤ Real.exp r)
    (W : NativeVectorCorrelation degree N p (fun ai : A × I => fun x => f ai.1 x * star (v ai.2 x))) :
    Nonempty (NativeVectorCorrelation degree N (p + q + r)
      (fun aij : A × ((I × I) × (I × J)) => fun x =>
        f aij.1 x * star (b aij.2.2.2 x) *
          star (v aij.2.1.1 x * star (a aij.2.1.2 x)) *
          star (a aij.2.2.1 x * star (b aij.2.2.2 x)))) := by
  classical
  let F (x : ZMod N) := f W.coordinate.1 x * star (W.test.evalCyclic N (fun _ => x))
  let P (j : I) (x : ZMod N) := star (a j x)
  let ψ (j : I) (_ : Unit) (x : ZMod N) := star (v W.coordinate.2 x * star (a j x))
  have hcorr : Real.exp (-p) ≤ ‖𝔼 x ∈ (Finset.univ : Finset (ZMod N)), F x * star (v W.coordinate.2 x)‖ := by
    simpa only [F, mul_assoc, mul_left_comm, mul_comm] using W.correlation
  obtain ⟨j, _, hj⟩ := exists_unit_expansion_correlation Finset.univ F
    (fun x => star (v W.coordinate.2 x)) P (fun (_ : I) (_ : Unit) => (1 : ℂ)) ψ
    (fun x _ => by simpa only [P, norm_star] using ha x)
    (fun j x _ => by simp only [P, ψ, star_star, star_mul, Fintype.sum_unique, one_mul, mul_comm])
    (Real.exp_pos (-p)) (Real.exp_pos q) (by norm_num : (0 : ℝ) < 1) hI (fun _ => by simp) hcorr
  have hfrac : Real.exp (-p) / (Real.exp q * 1) = Real.exp (-(p + q)) := by
    rw [mul_one, ← Real.exp_sub]
    congr 1
    ring
  rw [hfrac] at hj
  let F' (x : ZMod N) := F x * ψ j () x
  let P' (k : J) (x : ZMod N) := star (b k x)
  let ψ' (k : J) (_ : Unit) (x : ZMod N) := star (a j x * star (b k x))
  have hj' : Real.exp (-(p + q)) ≤
      ‖𝔼 x ∈ (Finset.univ : Finset (ZMod N)), F' x * star (a j x)‖ := by
    simpa only [F', P, mul_assoc, mul_left_comm, mul_comm] using hj
  obtain ⟨k, _, hk⟩ := exists_unit_expansion_correlation Finset.univ F'
    (fun x => star (a j x)) P' (fun (_ : J) (_ : Unit) => (1 : ℂ)) ψ'
    (fun x _ => by simpa only [P', norm_star] using hb x)
    (fun k x _ => by simp only [P', ψ', star_star, star_mul, Fintype.sum_unique, one_mul, mul_comm])
    (Real.exp_pos (-(p + q))) (Real.exp_pos r) (by norm_num : (0 : ℝ) < 1) hJ (fun _ => by simp) hj'
  have hfrac' : Real.exp (-(p + q)) / (Real.exp r * 1) = Real.exp (-(p + q + r)) := by
    rw [mul_one, ← Real.exp_sub]
    congr 1
    ring
  rw [hfrac'] at hk
  exact ⟨{
    L := W.L
    dim := W.dim
    model := W.model
    test := W.test
    complexity := W.complexity.mono (by linarith)
    coordinate := (W.coordinate.1, (W.coordinate.2, j), (j, k))
    correlation := by simpa only [F, F', P', ψ, ψ', mul_assoc, mul_left_comm, mul_comm] using hk
  }⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem le_productNiltestBudget {p : ℝ} (hp : 0 ≤ p) : p ≤ productNiltestBudget p := by
  apply le_trans _ (productNiltestBudget_geometry hp)
  nlinarith [sq_nonneg p]

namespace NativeVectorCorrelation

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_absorb {I J : Type*} {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d N : ℕ} [NeZero N] {p : ℝ} (D : RationalFilteredNilmanifold L s d)
    (T : J → D.Niltest (fun _ : Unit => 1)) (f : I → ZMod N → ℂ) (hp : 2 ≤ p)
    (hT : ∀ j, (T j).ComplexityLE p)
    (W : NativeVectorCorrelation s N p
      (fun ij : I × J => fun x => f ij.1 x * star ((T ij.2).evalCyclic N (fun _ => x)))) :
    Nonempty (NativeVectorCorrelation s N (productNiltestBudget p) f) := by
  have hp0 : 0 ≤ p := by linarith
  let K : Bool → Type := BoolLieFamily L W.L
  let dims : Bool → ℕ := fun b => Bool.rec W.dim d b
  let models : ∀ b, RationalFilteredNilmanifold (K b) s (dims b) := fun b => by
    cases b
    · exact W.model
    · exact D
  let tests : ∀ b, (models b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact W.test
    · exact T W.coordinate.2
  have htests : ∀ b, (tests b).ComplexityLE p := by
    intro b
    cases b
    · exact W.complexity
    · exact hT _
  have hcard : (Fintype.card Bool : ℝ) ≤ p := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis models)
  let S := RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests
  have heval (x : ZMod N) : S.evalCyclic N (fun _ => x) =
      (T W.coordinate.2).evalCyclic N (fun _ => x) * W.test.evalCyclic N (fun _ => x) := by
    change (RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests).eval
      (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    rfl
  refine ⟨{
    L := ∀ b, K b
    dim := _
    model := RationalFilteredNilmanifold.pi models
    test := S
    complexity := RationalFilteredNilmanifold.piNiltest_complexity models tests hp0 hcard htests
    coordinate := W.coordinate.1
    correlation := ?_
  }⟩
  have hcorr := (Real.exp_le_exp.mpr (neg_le_neg (le_productNiltestBudget hp0))).trans W.correlation
  simpa only [heval, star_mul, mul_assoc, mul_left_comm, mul_comm] using hcorr

end NativeVectorCorrelation

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace NativeVectorCorrelation

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

end NativeVectorCorrelation

end Erdos3

end

section

namespace Erdos3.NativeCrossWitnesses

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

noncomputable def lower (h : H) (x : ZMod N) : ℂ := (U h).test.evalCyclic N (fun _ => x)

end Erdos3.NativeCrossWitnesses

end

end OAI

end


