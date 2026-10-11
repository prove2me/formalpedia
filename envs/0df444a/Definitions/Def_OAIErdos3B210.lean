-- Prove2me | Definitions.Def_OAIErdos3B210
-- name    : OAIErdos3B210
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T18:41:52.633563+00:00
-- url     : https://prove2.me/theorems/671b9d7d-531b-4875-b7a2-95dc23999773
-- title:
--   OpenAI Erdős-3 split, definitions bundle 211 of 228
-- statement:
--   Definitions bundle 211 of 228 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B209`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 211 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartDetectedDecomposition`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartDetectedDecomposition.exists_homogeneous`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.initial`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.invariant_outer`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.noConfusion`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.outer`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.outer_toUncertified`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.toUncertified`, `OAI.Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory.toUncertified_K`, `OAI.Erdos3.NilpotentLieFiltration.FullChartFiniteHistory`, `OAI.Erdos3.NilpotentLieFiltration.FullChartFiniteHistory.outer`, `OAI.Erdos3.NilpotentLieFiltration.certifiedFullChartDetectedDecomposition_of_vector_detection`, `OAI.Erdos3.NilpotentLieFiltration.exists_bufferedSampledCurrentGrade_phase`, `OAI.Erdos3.NilpotentLieFiltration.exists_sampledCurrentGrade_lowTagged_lower_phase`, `OAI.Erdos3.NilpotentLieFiltration.exists_sampledCurrentGrade_lower_phase`, `OAI.Erdos3.NilpotentLieFiltration.fullChart_grade_quotient_of_low_value`, `OAI.Erdos3.NilpotentLieFiltration.fullChart_quotient_identity_homogeneous`, `OAI.Erdos3.NilpotentLieFiltration.quotientFunctional_kills_fast`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeQuotientPolynomial_functional_homogeneous`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeQuotientPolynomial_homogeneousPullback`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolGradeQuotientPolynomial_lowTagged_aeval`, `OAI.Erdos3.NilpotentLieFiltration.restrictedMajorCorrection_fullChart_homogeneous`, `OAI.Erdos3.NilpotentLieFiltration.restrictedMajorCorrection_weightedHomogeneousPart`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial_component_homogeneousPullback`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial_component_quotient`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial_homogeneousComponent_homogeneousPullback`, `OAI.Erdos3.PolynomialPatch.ofTaggedWeightedShearOrbit`, `OAI.Erdos3.PolynomialPatch.ofTaggedWeightedShearOrbit_kernel`, `OAI.Erdos3.PolynomialPatch.ofTaggedWeightedShearOrbit_weight`, `OAI.Erdos3.PolynomialPatch.ofWeightedShearOrbit`, `OAI.Erdos3.PolynomialPatch.ofWeightedShearOrbit_kernel`, `OAI.Erdos3.PolynomialPatch.ofWeightedShearOrbit_weight`, `OAI.Erdos3.PolynomialPatch.weightedSymbolicShearForm`, `OAI.Erdos3.PolynomialPatch.weightedSymbolicShearFullCenter_degree`, `OAI.Erdos3.PolynomialPatch.weightedSymbolicShearPatch`, `OAI.Erdos3.RankPreparationFamily.padCoordEquiv`, `OAI.Erdos3.RankPreparationFamily.padCoordEquiv_coefficients`, `OAI.Erdos3.RankPreparationFamily.padCoordEquiv_eval`, `OAI.Erdos3.RankPreparationFamily.padCoordEquiv_index`, `OAI.Erdos3.RankPreparationFamily.padCoordEquiv_label`, `OAI.Erdos3.RankPreparationFamily.padCoordInclusion`, `OAI.Erdos3.RankPreparationFamily.padCoordInclusion_coefficients`, `OAI.Erdos3.RankPreparationFamily.padCoordInclusion_eval`, `OAI.Erdos3.RankPreparationFamily.padCoordInclusion_label`, `OAI.Erdos3.RankPreparationFamily.padCoordInclusion_restriction`, `OAI.Erdos3.RankPreparationFamily.padCoordRestriction`, `OAI.Erdos3.RankPreparationFamily.padCoordRestriction_inclusion`, `OAI.Erdos3.RankPreparationFamily.padFullTaggedEquiv`, `OAI.Erdos3.RankPreparationFamily.padFullTaggedEquiv_weight`, `OAI.Erdos3.RankPreparationFamily.pad_polynomial`, `OAI.Erdos3.RankPreparationFamily.unpadCenter`, `OAI.Erdos3.RankPreparationFamily.unpadCenter_equiv`, `OAI.Erdos3.RankPreparationFamily.unpadFreezingLifts`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.integerChartPullback`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.integerChartPullback_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.integerChartPullback_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.integerChartPullback_lipBound`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.integerChartPullback_normBound`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.integerChartPullback_observable`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.integerChartPullback_orbit`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.integerChartPullback_orbit_eq_of_orbit_eq`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.integerChartPullback_unitIntervalValued`, `OAI.Erdos3.VectorPolynomial.coordinate_lowTaggedVectorExtend`, `OAI.Erdos3.VectorPolynomial.exists_finite_vector_correction_representatives`, `OAI.Erdos3.VectorPolynomial.fullTaggedAffineMapChart`, `OAI.Erdos3.VectorPolynomial.fullTaggedAffineMapChart_eval_eq`, `OAI.Erdos3.VectorPolynomial.fullTaggedAffineMapChart_eval_eq_of_complement`, `OAI.Erdos3.VectorPolynomial.fullTaggedAffineMapChart_eval_eq_of_quotient`, `OAI.Erdos3.VectorPolynomial.fullTaggedAffineMapChart_eval_tag`, `OAI.Erdos3.VectorPolynomial.fullTaggedAffineMapChart_support`, `OAI.Erdos3.VectorPolynomial.fullTaggedAffineMapChart_top`, `OAI.Erdos3.VectorPolynomial.fullTaggedAffineMapChart_top_mem_set`, `OAI.Erdos3.VectorPolynomial.fullTaggedAffineMatrixChart_eval_eq_of_anchor`, `OAI.Erdos3.VectorPolynomial.fullTaggedAffineMatrixChart_eval_eq_of_complement`, `OAI.Erdos3.VectorPolynomial.fullTaggedGradedBaseIntersection`, `OAI.Erdos3.VectorPolynomial.fullTaggedGradedBaseIntersection_rat_dilation`, `OAI.Erdos3.VectorPolynomial.fullTaggedGradedBaseIntersection_subset`, `OAI.Erdos3.VectorPolynomial.fullTaggedLinearMapChart`, `OAI.Erdos3.VectorPolynomial.fullTaggedLinearMapChart_coefficientGrid`, `OAI.Erdos3.VectorPolynomial.fullTaggedLinearMapChart_eval_tag`, `OAI.Erdos3.VectorPolynomial.fullTaggedLinearMapChart_homogeneous`, `OAI.Erdos3.VectorPolynomial.fullTaggedMajorChart_homogeneous`, `OAI.Erdos3.VectorPolynomial.fullTaggedMajorTopCoordinates`, `OAI.Erdos3.VectorPolynomial.fullTaggedMajorTopCoordinates_coefficients_mem`, `OAI.Erdos3.VectorPolynomial.fullTaggedMajorTopCoordinates_coefficients_mem_tag`, `OAI.Erdos3.VectorPolynomial.fullTaggedVariableWeight`, `OAI.Erdos3.VectorPolynomial.fullTaggedVariableWeight_pos`, `OAI.Erdos3.VectorPolynomial.integerSampledLowTags`, `OAI.Erdos3.VectorPolynomial.integerSampledRealChart`, `OAI.Erdos3.VectorPolynomial.integerSampledRealChart_eval`, `OAI.Erdos3.VectorPolynomial.integerSampledSpatial`, `OAI.Erdos3.VectorPolynomial.lowTaggedIndex_injective`, `OAI.Erdos3.VectorPolynomial.lowTaggedMajorChart_rename`, `OAI.Erdos3.VectorPolynomial.lowTaggedRestrict`, `OAI.Erdos3.VectorPolynomial.lowTaggedRestrict_eq_killCompl`, `OAI.Erdos3.VectorPolynomial.lowTaggedRestrict_rename`, `OAI.Erdos3.VectorPolynomial.lowTaggedRestrict_weightedHomogeneousComponent`, `OAI.Erdos3.VectorPolynomial.lowTaggedRestrictionVariables`, `OAI.Erdos3.VectorPolynomial.lowTaggedRestrictionVariables_isWeightedHomogeneous`, `OAI.Erdos3.VectorPolynomial.lowTaggedVariableEmbedding`, `OAI.Erdos3.VectorPolynomial.lowTaggedVariableEmbedding_eval_coordinates`, `OAI.Erdos3.VectorPolynomial.lowTaggedVariableEmbedding_inl`, `OAI.Erdos3.VectorPolynomial.lowTaggedVariableEmbedding_inr`, `OAI.Erdos3.VectorPolynomial.lowTaggedVariableEmbedding_inr_mem_range_iff`, `OAI.Erdos3.VectorPolynomial.lowTaggedVariableEmbedding_slot`, `OAI.Erdos3.VectorPolynomial.lowTaggedVariableEmbedding_weight`, `OAI.Erdos3.VectorPolynomial.lowTaggedVariableWeight`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorExtend`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorExtend_coefficients_grid`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorExtend_coordinate_coefficient_bound`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorExtend_coordinate_grid`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorExtend_eval₂`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorExtend_majorChart`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorExtend_monomial`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorExtend_restrict`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorExtend_tmul`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorExtend_weightedHomogeneousPart`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorRestrict`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorRestrict_eval_real`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorRestrict_eval₂`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorRestrict_extend`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorRestrict_homogeneous`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorRestrict_tmul`, `OAI.Erdos3.VectorPolynomial.lowTaggedVectorRestrict_weightedHomogeneousPart`, `OAI.Erdos3.VectorPolynomial.majorPhaseNearestLift`, `OAI.Erdos3.VectorPolynomial.majorPhaseNearestLift_close`, `OAI.Erdos3.VectorPolynomial.majorPhaseNearestLift_eq_of_close`, `OAI.Erdos3.VectorPolynomial.majorPhasePlateauSignal`, `OAI.Erdos3.VectorPolynomial.majorPhasePlateauSignal_eq_phase`, `OAI.Erdos3.VectorPolynomial.majorPhasePlateauSignal_integerChart_eq`, `OAI.Erdos3.VectorPolynomial.majorPhasePlateauSignal_norm_le_one`, `OAI.Erdos3.VectorPolynomial.majorPhaseRationalTagConstraint`, `OAI.Erdos3.VectorPolynomial.majorPhaseRationalTagConstraints`, `OAI.Erdos3.VectorPolynomial.majorPhaseRationalTagConstraints_budget`, `OAI.Erdos3.VectorPolynomial.majorPhaseRationalTagConstraints_length`, `OAI.Erdos3.VectorPolynomial.majorPhaseRationalTagConstraints_set_eq`, `OAI.Erdos3.VectorPolynomial.majorPhase_rationalTaggedConstraintCertificate`, `OAI.Erdos3.VectorPolynomial.majorTranslationTopCoordinates_lowTagged_eq`, `OAI.Erdos3.VectorPolynomial.rename_lowTaggedRestrict`, `OAI.Erdos3.VectorPolynomial.rename_lowTaggedRestrictionVariables_of_weight_le`, `OAI.Erdos3.VectorPolynomial.weightedHomogeneousPart_coefficients_grid`, `OAI.Erdos3.VectorPolynomial.weightedHomogeneousPart_coordinate_bound`, `OAI.Erdos3.VectorPolynomial.weightedHomogeneousPart_coordinate_totalDegree_le`, `OAI.Erdos3.VectorPolynomial.weightedHomogeneousPart_idempotent`, `OAI.Erdos3.abs_coeff_rename_le`, `OAI.Erdos3.boundedExponentWindow`, `OAI.Erdos3.boundedExponentWindow_card_le`, `OAI.Erdos3.boundedExponentWindow_mem_iff`, `OAI.Erdos3.exists_finite_primitive_subspace_correction_representatives`, `OAI.Erdos3.exists_finite_vector_subspace_normalized_correction_representatives`, `OAI.Erdos3.majorPhasePlateauKernel`, `OAI.Erdos3.majorPhasePlateauKernel_lip`, `OAI.Erdos3.majorPhasePlateauKernel_one`, `OAI.Erdos3.normalizedChartSubspaceCoordinates`, `OAI.Erdos3.normalizedChartSubspaceCoordinates_coeff`, `OAI.Erdos3.normalizedChartSubspaceCoordinates_eval_mem`, `OAI.Erdos3.normalizedChartSubspaceCoordinates_reconstruct`, `OAI.Erdos3.normalizedChartSubspaceCoordinates_reconstruct_C`, `OAI.Erdos3.normalizedChart_subspace_decomposition`, `OAI.Erdos3.normalizedRealPolynomialChart_linear_restriction`, `OAI.Erdos3.normalizedRealPolynomialChart_linear_restriction_coordinate`, `OAI.Erdos3.polynomialSubspaceRestriction`, `OAI.Erdos3.polynomialSubspaceRestriction_coeff_div`, `OAI.Erdos3.polynomialSubspaceRestriction_coeff_le`, `OAI.Erdos3.polynomialSubspaceRestriction_coefficientGrid`, `OAI.Erdos3.polynomialSubspaceRestriction_eq_of_eval`, `OAI.Erdos3.polynomialSubspaceRestriction_eval`, `OAI.Erdos3.polynomialSubspaceRestriction_eval_basis`, `OAI.Erdos3.polynomialSubspaceRestriction_eval_eq`, `OAI.Erdos3.polynomialSubspaceRestriction_normalizedChart`, `OAI.Erdos3.polynomialSubspaceRestriction_totalDegree_le`, `OAI.Erdos3.polynomialTagLinearEmbedding`, `OAI.Erdos3.polynomialTagLinearEmbedding_coefficientGrid`, `OAI.Erdos3.polynomialTagLinearEmbedding_eval`, `OAI.Erdos3.polynomialTagLinearEmbedding_inl`, `OAI.Erdos3.polynomialTagLinearEmbedding_inr`, `OAI.Erdos3.polynomialTagLinearEmbedding_mass_le`, `OAI.Erdos3.polynomialTagLinearEmbedding_rename`, `OAI.Erdos3.polynomialTagLinearEmbedding_totalDegree_le`, `OAI.Erdos3.polynomialTagRestriction_coeff_le_of_coeff_le`, `OAI.Erdos3.polynomialTagRestriction_coefficientGrid`, `OAI.Erdos3.polynomialTagRestriction_mass_le`, `OAI.Erdos3.polynomialTagRestriction_mass_le_of_coeff_le`, `OAI.Erdos3.polynomialTagRestriction_totalDegree_le`, `OAI.Erdos3.sampledCurrentGrade_sampledCurrentGrade_realifyFunctional_basis_coord`, `OAI.Erdos3.sampledTopPhase_coordinate_homogeneous`, `OAI.Erdos3.sampledTopPhase_remainder`, `OAI.Erdos3.sampledTopPhase_remainder_totalDegree`, `OAI.Erdos3.support_subset_boundedExponentWindow`, `OAI.Erdos3.symbolicShearPrefixSubstitution_weighted_degree`, `OAI.Erdos3.taggedShearOrbitReindexChart`, `OAI.Erdos3.taggedShearOrbitReindexChart_degree`, `OAI.Erdos3.weightedHomogeneousComponent_totalDegree_le_of_positive`, `OAI.Erdos3.weightedPolynomialShearOrbitSymbolicHom`, `OAI.Erdos3.weightedPolynomialShearOrbitSymbolicHom_degree`, `_private.Estimates.VectorSubspaceCorrectionRepresentatives.0.OAI.Erdos3.VectorPolynomial.coordinate_grid_of_vector_grid`, `_private.Estimates.VectorSubspaceCorrectionRepresentatives.0.OAI.Erdos3.boundedExponentWindow_finite`, `_private.Geometry.FullTaggedChartCoefficientRange.0.OAI.Erdos3.normalizedChart_coefficients_mem`, `_private.Linear.RankPreparationPaddedFreezingLifts.0.OAI.Erdos3.RankPreparationFamily.coefficients_cast`, `_private.Linear.RankPreparationPaddedFreezingLifts.0.OAI.Erdos3.RankPreparationFamily.eval_cast`, `_private.Linear.RankPreparationPaddedFreezingLifts.0.OAI.Erdos3.RankPreparationFamily.label_cast`, `_private.Linear.RankPreparationPaddedFreezingLifts.0.OAI.Erdos3.RankPreparationFamily.padCoord_isLt`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B055
import Definitions.Def_OAIErdos3B208

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTaggedConstraintHistory
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem lowTaggedIndex_injective (d : ℕ) :
    Function.Injective (lowTaggedIndex J d) := by
  intro i k h
  apply (Fintype.equivFin (LowTaggedIndex J d)).symm.injective
  apply Subtype.ext
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] {X : Type*}

abbrev fullTaggedVariableWeight : X ⊕ (Σ j, J j) → ℕ :=
  Sum.elim (fun _ => 1) (fun i => i.1.val + 1)

noncomputable abbrev lowTaggedVariableWeight (d : ℕ) :
    X ⊕ Fin (Fintype.card (LowTaggedIndex J d)) → ℕ :=
  Sum.elim (fun _ => 1) (lowTaggedWeight J d)

noncomputable def lowTaggedVariableEmbedding (d : ℕ) :
    (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ↪ (X ⊕ (Σ j, J j)) :=
  (Function.Embedding.refl X).sumMap ⟨lowTaggedIndex J d, lowTaggedIndex_injective J d⟩

@[simp] theorem lowTaggedVariableEmbedding_inl (d : ℕ) (x : X) :
    lowTaggedVariableEmbedding (X := X) J d (Sum.inl x) = Sum.inl x := rfl

@[simp] theorem lowTaggedVariableEmbedding_inr (d : ℕ)
    (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    lowTaggedVariableEmbedding (X := X) J d (Sum.inr i) =
      Sum.inr (lowTaggedIndex J d i) := rfl

@[simp] theorem lowTaggedVariableEmbedding_weight (d : ℕ)
    (v : X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) :
    fullTaggedVariableWeight J (lowTaggedVariableEmbedding J d v) =
      lowTaggedVariableWeight J d v := by
  cases v <;> rfl

omit [∀ j, Fintype (J j)] in
theorem fullTaggedVariableWeight_pos (v : X ⊕ (Σ j, J j)) :
    0 < fullTaggedVariableWeight J v := by
  cases v with
  | inl x => exact Nat.zero_lt_one
  | inr i => exact Nat.succ_pos _

@[simp] theorem lowTaggedVariableEmbedding_slot (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (k : J j) :
    lowTaggedVariableEmbedding (X := X) J d (Sum.inr (lowTaggedSlot J d j hj k)) =
      Sum.inr ⟨j, k⟩ := by
  simp only [lowTaggedVariableEmbedding_inr, lowTaggedIndex_slot]

theorem lowTaggedVariableEmbedding_inr_mem_range_iff (d : ℕ) (i : Σ j, J j) :
    (Sum.inr i : X ⊕ (Σ j, J j)) ∈ Set.range (lowTaggedVariableEmbedding J d) ↔
      i.1.val + 1 ≤ d := by
  constructor
  · rintro ⟨v, hv⟩
    cases v with
    | inl x => simp only [lowTaggedVariableEmbedding_inl, Sum.inl_ne_inr] at hv
    | inr n =>
      have hn : lowTaggedIndex J d n = i := Sum.inr.inj hv
      rw [← hn]
      exact lowTaggedIndex_property J d n
  · intro hi
    exact ⟨Sum.inr (lowTaggedSlot J d i.1 hi i.2), lowTaggedVariableEmbedding_slot J d i.1 hi i.2⟩

theorem lowTaggedVariableEmbedding_eval_coordinates (d : ℕ)
    (u : X → ℝ) (z : ∀ j, J j → ℝ) :
    (Sum.elim u (fun i : Σ j, J j => z i.1 i.2)) ∘ lowTaggedVariableEmbedding J d =
      Sum.elim u (lowTaggedCoordinates J d z) := by
  funext v
  cases v <;> rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R : Type*} [CommRing R]

noncomputable def lowTaggedRestrictionVariables (k : ℕ) :
    X ⊕ (Σ j, J j) → MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R := by
  classical
  exact Sum.elim (fun x => MvPolynomial.X (Sum.inl x))
    (fun a => if h : a.1.val + 1 ≤ k then
      MvPolynomial.X (Sum.inr (lowTaggedSlot J k a.1 h a.2)) else 0)

noncomputable def lowTaggedRestrict (k : ℕ) :
    MvPolynomial (X ⊕ (Σ j, J j)) R →ₐ[R]
      MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R :=
  aeval (lowTaggedRestrictionVariables (X := X) (R := R) J k)

 theorem lowTaggedRestrictionVariables_isWeightedHomogeneous (k : ℕ)
    (i : X ⊕ (Σ j, J j)) :
    (lowTaggedRestrictionVariables (R := R) J k i).IsWeightedHomogeneous
      (lowTaggedVariableWeight J k) (fullTaggedVariableWeight J i) := by
  classical
  cases i with
  | inl x => exact isWeightedHomogeneous_X (R := R) (lowTaggedVariableWeight J k) (Sum.inl x)
  | inr a =>
    by_cases h : a.1.val + 1 ≤ k
    · simp only [lowTaggedRestrictionVariables, Sum.elim_inr, dif_pos h]
      have he : lowTaggedVariableWeight (X := X) J k (Sum.inr (lowTaggedSlot J k a.1 h a.2)) =
          a.1.val + 1 := by
        simp only [lowTaggedVariableWeight, Sum.elim_inr, lowTaggedWeight, lowTaggedIndex_slot]
      exact he ▸ isWeightedHomogeneous_X (R := R) (lowTaggedVariableWeight J k)
        (Sum.inr (lowTaggedSlot J k a.1 h a.2))
    · simp only [lowTaggedRestrictionVariables, Sum.elim_inr, dif_neg h]
      exact isWeightedHomogeneous_zero R _ _

 theorem lowTaggedRestrict_weightedHomogeneousComponent (k n : ℕ)
    (P : MvPolynomial (X ⊕ (Σ j, J j)) R) :
    lowTaggedRestrict J k (weightedHomogeneousComponent (fullTaggedVariableWeight J) n P) =
      weightedHomogeneousComponent (lowTaggedVariableWeight J k) n (lowTaggedRestrict J k P) :=
  aeval_weightedHomogeneousComponent _ _ _ (lowTaggedRestrictionVariables_isWeightedHomogeneous J k) n P

 theorem rename_lowTaggedRestrictionVariables_of_weight_le (k : ℕ)
    (i : X ⊕ (Σ j, J j)) (hi : fullTaggedVariableWeight J i ≤ k) :
    rename (lowTaggedVariableEmbedding J k) (lowTaggedRestrictionVariables (R := R) J k i) = MvPolynomial.X i := by
  classical
  cases i with
  | inl x => simp only [lowTaggedRestrictionVariables, Sum.elim_inl, rename_X,
      lowTaggedVariableEmbedding_inl]
  | inr a =>
    have ha : a.1.val + 1 ≤ k := hi
    simp only [lowTaggedRestrictionVariables, Sum.elim_inr, dif_pos ha, rename_X,
      lowTaggedVariableEmbedding_slot]

theorem rename_lowTaggedRestrict (k : ℕ) (P : MvPolynomial (X ⊕ (Σ j, J j)) R)
    (hP : P ∈ weightedSupportLE (fullTaggedVariableWeight J) k) :
    rename (lowTaggedVariableEmbedding J k) (lowTaggedRestrict J k P) = P := by
  classical
  have hcomp : (rename (R := R) (lowTaggedVariableEmbedding (X := X) J k)).comp
      (lowTaggedRestrict J k) =
      aeval (fun i => rename (lowTaggedVariableEmbedding J k)
        (lowTaggedRestrictionVariables (R := R) J k i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, lowTaggedRestrict, aeval_X]
  change ((rename (lowTaggedVariableEmbedding J k)).comp (lowTaggedRestrict J k)) P = P
  rw [hcomp]
  calc
    _ = aeval (MvPolynomial.X : (X ⊕ (Σ j, J j)) → MvPolynomial (X ⊕ (Σ j, J j)) R) P :=
      aeval_eq_of_weightedSupportLE hP _ _
        (rename_lowTaggedRestrictionVariables_of_weight_le J k)
    _ = P := by simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R : Type*} [CommRing R]

theorem lowTaggedRestrict_eq_killCompl (k : ℕ) :
    lowTaggedRestrict (X := X) (R := R) J k =
      killCompl (lowTaggedVariableEmbedding (X := X) J k).injective := by
  classical
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl x =>
    simp only [lowTaggedRestrict, aeval_X, lowTaggedRestrictionVariables, Sum.elim_inl]
    simpa only [rename_X, lowTaggedVariableEmbedding_inl] using
      (killCompl_rename_app (lowTaggedVariableEmbedding (X := X) J k).injective
        (MvPolynomial.X (Sum.inl x) : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R)).symm
  | inr a =>
    by_cases ha : a.1.val + 1 ≤ k
    · simp only [lowTaggedRestrict, aeval_X, lowTaggedRestrictionVariables,
        Sum.elim_inr, dif_pos ha]
      simpa only [rename_X, lowTaggedVariableEmbedding_slot] using
        (killCompl_rename_app (lowTaggedVariableEmbedding (X := X) J k).injective
          (MvPolynomial.X (Sum.inr (lowTaggedSlot J k a.1 ha a.2)) :
            MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R)).symm
    · have hn : (Sum.inr a : X ⊕ (Σ j, J j)) ∉
          Set.range (lowTaggedVariableEmbedding J k) := by
        rwa [lowTaggedVariableEmbedding_inr_mem_range_iff]
      simp only [lowTaggedRestrict, aeval_X, lowTaggedRestrictionVariables,
        Sum.elim_inr, dif_neg ha, killCompl, aeval_X, dif_neg hn]

@[simp] theorem lowTaggedRestrict_rename (k : ℕ)
    (Q : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R) :
    lowTaggedRestrict J k (rename (lowTaggedVariableEmbedding J k) Q) = Q := by
  rw [lowTaggedRestrict_eq_killCompl, killCompl_rename_app]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R S V : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V]

noncomputable def lowTaggedVectorRestrict (k : ℕ) :
    VectorPolynomial (X ⊕ (Σ j, J j)) R V →ₗ[R]
      VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V :=
  (lowTaggedRestrict (X := X) (R := R) J k).toLinearMap.rTensor V

noncomputable def lowTaggedVectorExtend (k : ℕ) :
    VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V →ₗ[R]
      VectorPolynomial (X ⊕ (Σ j, J j)) R V :=
  (MvPolynomial.rename (R := R) (lowTaggedVariableEmbedding (X := X) J k)).toLinearMap.rTensor V

@[simp] theorem lowTaggedVectorRestrict_tmul (k : ℕ)
    (P : MvPolynomial (X ⊕ (Σ j, J j)) R) (v : V) :
    lowTaggedVectorRestrict J k (P ⊗ₜ[R] v) = lowTaggedRestrict J k P ⊗ₜ[R] v := rfl

@[simp] theorem lowTaggedVectorExtend_tmul (k : ℕ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R) (v : V) :
    lowTaggedVectorExtend J k (P ⊗ₜ[R] v) =
      MvPolynomial.rename (lowTaggedVariableEmbedding J k) P ⊗ₜ[R] v := rfl

theorem lowTaggedVectorExtend_restrict (k : ℕ)
    (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V)
    (hP : DegreeLE (fullTaggedVariableWeight J) k P) :
    lowTaggedVectorExtend J k (lowTaggedVectorRestrict J k P) = P := by
  classical
  rw [← sum_monomial_coefficients P]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro α hα
  have hαk : Finsupp.weight (fullTaggedVariableWeight J) α ≤ k :=
    (degreeLE_iff _ _ P).mp hP α hα
  rw [monomial, lowTaggedVectorRestrict_tmul, lowTaggedVectorExtend_tmul]
  rw [rename_lowTaggedRestrict J k]
  exact weightedSupportLE_mono hαk
    (weightedSupportLE_monomial (fullTaggedVariableWeight J) α (1 : R))

theorem lowTaggedVectorRestrict_weightedHomogeneousPart (k n : ℕ)
    (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V) :
    lowTaggedVectorRestrict J k (weightedHomogeneousPart (fullTaggedVariableWeight J) n P) =
      weightedHomogeneousPart (lowTaggedVariableWeight J k) n (lowTaggedVectorRestrict J k P) := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | tmul P v =>
    rw [weightedHomogeneousPart_tmul, lowTaggedVectorRestrict_tmul,
      lowTaggedVectorRestrict_tmul, weightedHomogeneousPart_tmul,
      lowTaggedRestrict_weightedHomogeneousComponent]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

theorem lowTaggedVectorExtend_weightedHomogeneousPart (k n : ℕ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V) :
    lowTaggedVectorExtend J k (weightedHomogeneousPart (lowTaggedVariableWeight J k) n P) =
      weightedHomogeneousPart (fullTaggedVariableWeight J) n (lowTaggedVectorExtend J k P) := by
  have hX (i : X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) :
      (MvPolynomial.X (lowTaggedVariableEmbedding J k i) :
        MvPolynomial (X ⊕ (Σ j, J j)) R).IsWeightedHomogeneous
        (fullTaggedVariableWeight J) (lowTaggedVariableWeight J k i) := by
    rw [← lowTaggedVariableEmbedding_weight J k i]
    exact MvPolynomial.isWeightedHomogeneous_X (R := R)
      (fullTaggedVariableWeight J) (lowTaggedVariableEmbedding J k i)
  induction P using TensorProduct.induction_on with
  | zero => simp
  | tmul P v =>
    rw [weightedHomogeneousPart_tmul, lowTaggedVectorExtend_tmul,
      lowTaggedVectorExtend_tmul, weightedHomogeneousPart_tmul]
    simp only [MvPolynomial.rename_eq_aeval]
    exact congrArg (fun Q => Q ⊗ₜ[R] v)
      (aeval_weightedHomogeneousComponent (lowTaggedVariableWeight J k)
        (fullTaggedVariableWeight J) (MvPolynomial.X ∘ lowTaggedVariableEmbedding J k)
        hX n P)
  | add P Q hP hQ => simp only [map_add, hP, hQ]

theorem lowTaggedVectorRestrict_homogeneous (k : ℕ)
    (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V)
    (hP : ∀ α, Finsupp.weight (fullTaggedVariableWeight J) α ≠ k → coefficients P α = 0)
    (α : (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) →₀ ℕ)
    (hα : Finsupp.weight (lowTaggedVariableWeight J k) α ≠ k) :
    coefficients (lowTaggedVectorRestrict J k P) α = 0 := by
  have h := lowTaggedVectorRestrict_weightedHomogeneousPart J k k P
  rw [weightedHomogeneousPart_eq_self hP] at h
  rw [h]
  exact weightedHomogeneousPart_homogeneous _ _ _ _ hα

section Evaluation

variable [Algebra R S] [Module S V] [IsScalarTower R S V]

theorem lowTaggedVectorExtend_eval₂ (k : ℕ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V)
    (x : X ⊕ (Σ j, J j) → S) :
    eval₂ x (lowTaggedVectorExtend J k P) =
      eval₂ (x ∘ lowTaggedVariableEmbedding J k) P := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | tmul P v =>
    rw [lowTaggedVectorExtend_tmul, eval₂_tmul, eval₂_tmul, MvPolynomial.aeval_rename]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

theorem lowTaggedVectorRestrict_eval₂ (k : ℕ)
    (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V)
    (hP : DegreeLE (fullTaggedVariableWeight J) k P)
    (x : X ⊕ (Σ j, J j) → S) :
    eval₂ x P = eval₂ (x ∘ lowTaggedVariableEmbedding J k) (lowTaggedVectorRestrict J k P) := by
  rw [← lowTaggedVectorExtend_eval₂, lowTaggedVectorExtend_restrict J k P hP]

end Evaluation

theorem lowTaggedVectorRestrict_eval_real [Algebra R ℝ] [Module ℝ V] [IsScalarTower R ℝ V]
    (k : ℕ) (P : VectorPolynomial (X ⊕ (Σ j, J j)) R V)
    (hP : DegreeLE (fullTaggedVariableWeight J) k P)
    (u : X → ℝ) (z : ∀ j, J j → ℝ) :
    eval₂ (Sum.elim u (fun a : Σ j, J j => z a.1 a.2)) P =
      eval₂ (Sum.elim u (lowTaggedCoordinates J k z)) (lowTaggedVectorRestrict J k P) := by
  rw [lowTaggedVectorRestrict_eval₂ J k P hP, lowTaggedVariableEmbedding_eval_coordinates]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded) (k : ℕ)
    (residual : F.RealPolynomialSymbol (fullTaggedVariableWeight (X := X) J))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R S V : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V]

@[simp] theorem lowTaggedVectorExtend_monomial (k : ℕ)
    (α : (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) →₀ ℕ) (v : V) :
    lowTaggedVectorExtend J k (monomial (R := R) α v) =
      monomial (α.mapDomain (lowTaggedVariableEmbedding J k)) v := by
  rw [monomial, lowTaggedVectorExtend_tmul, MvPolynomial.rename_monomial]
  rfl

theorem coordinate_lowTaggedVectorExtend (k : ℕ) (f : V →+ S)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V) :
    coordinate f (lowTaggedVectorExtend J k P) =
      MvPolynomial.rename (lowTaggedVariableEmbedding J k) (coordinate f P) := by
  classical
  rw [← sum_monomial_coefficients P]
  simp only [Finsupp.sum, map_sum, coordinate_sum, lowTaggedVectorExtend_monomial,
    coordinate_monomial, MvPolynomial.rename_monomial]

@[simp] theorem lowTaggedVectorRestrict_extend (k : ℕ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V) :
    lowTaggedVectorRestrict J k (lowTaggedVectorExtend J k P) = P := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | tmul P v =>
    rw [lowTaggedVectorExtend_tmul, lowTaggedVectorRestrict_tmul, lowTaggedRestrict_rename]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem abs_coeff_rename_le {σ τ : Type*} (e : σ ↪ τ)
    (P : MvPolynomial σ ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ α, |P.coeff α| ≤ C) (β : τ →₀ ℕ) :
    |(MvPolynomial.rename e P).coeff β| ≤ C := by
  by_cases hz : (MvPolynomial.rename e P).coeff β = 0
  · simpa only [hz, abs_zero] using hC
  · obtain ⟨α, hα, _⟩ := MvPolynomial.coeff_rename_ne_zero e P β hz
    rw [← hα, MvPolynomial.coeff_rename_mapDomain e e.injective]
    exact hP α

namespace VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
  {X R V η : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem lowTaggedVectorExtend_coordinate_coefficient_bound (k : ℕ)
    (f : η → V →+ ℝ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ j α, |f j (coefficients P α)| ≤ C) :
    ∀ α j, |f j (coefficients (lowTaggedVectorExtend J k P) α)| ≤ C := by
  intro α j
  rw [← coeff_coordinate, coordinate_lowTaggedVectorExtend]
  exact abs_coeff_rename_le (lowTaggedVariableEmbedding J k) (coordinate (f j) P)
    C hC (fun β => by simpa only [coeff_coordinate] using hP j β) α

theorem lowTaggedVectorExtend_coordinate_grid (k : ℕ)
    (f : η → V →+ ℝ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V)
    (q : ℕ) (hP : ∀ j, realPolynomialCoefficientGrid q (coordinate (f j) P)) :
    ∀ j, realPolynomialCoefficientGrid q (coordinate (f j) (lowTaggedVectorExtend J k P)) := by
  intro j
  rw [coordinate_lowTaggedVectorExtend]
  exact realPolynomialCoefficientGrid_rename (lowTaggedVariableEmbedding J k) (hP j)

theorem lowTaggedVectorExtend_coefficients_grid (k : ℕ)
    (f : η → V →+ ℝ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V)
    (q : ℕ) (hP : ∀ j, realPolynomialCoefficientGrid q (coordinate (f j) P)) :
    ∀ α, (fun j => f j (coefficients (lowTaggedVectorExtend J k P) α)) ∈
      realDenominatorGrid q := by
  intro α
  have hj : ∀ j, ∃ z : ℤ, (z : ℝ) =
      (q : ℝ) * f j (coefficients (lowTaggedVectorExtend J k P) α) := by
    intro j
    obtain ⟨z, hz⟩ := lowTaggedVectorExtend_coordinate_grid J k f P q hP j
    exact ⟨z α, by simpa only [coeff_coordinate, Pi.smul_apply, smul_eq_mul] using congrFun hz α⟩
  choose z hz using hj
  exact ⟨z, funext hz⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {X κ : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

def fullTaggedGradedBaseIntersection (k : ℕ)
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
    (K : κ → Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)) :
    Set (X ⊕ (Σ j, J j) → ℝ) :=
  {t | t ∈ K₀ ∧ ∀ i, (fun b => t (lowTaggedVariableEmbedding J k (Sum.inr b))) ∈ K i}

theorem fullTaggedGradedBaseIntersection_subset (k : ℕ)
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
    (K : κ → Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)) :
    fullTaggedGradedBaseIntersection J k K₀ K ⊆ K₀ := fun _ ht => ht.1

theorem fullTaggedGradedBaseIntersection_rat_dilation (k : ℕ)
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
    (K : κ → Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J k)) → ℝ))
    (hK : ∀ i, BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J k) (K i))
    (hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
      (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈ K₀)
    (t : X ⊕ (Σ j, J j) → ℝ) (ht : t ∈ fullTaggedGradedBaseIntersection J k K₀ K)
    (r : ℚ) :
    (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈
      fullTaggedGradedBaseIntersection J k K₀ K := by
  refine ⟨hK₀ t ht.1 r, ?_⟩
  intro i
  change (fun b => (r : ℝ) ^ fullTaggedVariableWeight J
    (lowTaggedVariableEmbedding J k (Sum.inr b)) *
      t (lowTaggedVariableEmbedding J k (Sum.inr b))) ∈ K i
  simpa only [lowTaggedVariableEmbedding_weight, lowTaggedVariableWeight, Sum.elim_inr] using
    (hK i).coordinate_dilation_mem (lowTaggedWeight J k) (K i) (r : ℝ)
      (fun b => t (lowTaggedVariableEmbedding J k (Sum.inr b))) (ht.2 i)

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)

local notation "w" => lowTaggedWeight J k

variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ) (N : X → ℕ) (budget : ℝ)


end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

open Module RationalFilteredNilmanifold PolynomialTranslationLie

variable {m : ℕ} (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)

noncomputable def majorPhaseRationalTagConstraint {η : Type*} {count : ℕ}
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k)
    (a : η × {j : Fin m // j.val + 1 ≤ k}) : RationalTagConstraint J where
  tag := a.2.val
  count := count
  generators := majorPhaseTaggedGenerators J k (gen a.1) a.2.val a.2.property

noncomputable def majorPhaseRationalTagConstraints {η : Type*} [Fintype η] {count : ℕ}
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k) :
    List (RationalTagConstraint J) := by
  classical
  exact (Finset.univ : Finset (η × {j : Fin m // j.val + 1 ≤ k})).toList.map
    (majorPhaseRationalTagConstraint J k gen)

theorem majorPhaseRationalTagConstraints_length {η : Type*} [Fintype η] {count : ℕ}
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k) :
    (majorPhaseRationalTagConstraints J k gen).length ≤ Fintype.card η * m := by
  classical
  have htag : Fintype.card {j : Fin m // j.val + 1 ≤ k} ≤ m := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun j : Fin m => j.val + 1 ≤ k)
  simpa only [majorPhaseRationalTagConstraints, List.length_map, Finset.length_toList,
    Finset.card_univ, Fintype.card_prod] using Nat.mul_le_mul_left (Fintype.card η) htag

theorem majorPhaseRationalTagConstraints_budget {η : Type*} [Fintype η] {count : ℕ}
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k) (B : ℝ)
    (hcount : ∀ _a : η, (count : ℝ) ≤ B)
    (hheight : ∀ a i j, rationalLogHeight
      ((weightedBasis (lowTaggedWeight J k) k (lowTaggedWeight_pos J k)).repr (gen a i) j) ≤ B) :
    ∀ c ∈ majorPhaseRationalTagConstraints J k gen, c.BudgetLE B := by
  classical
  intro c hc
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  refine ⟨hcount a.1, ?_⟩
  exact majorPhaseTaggedGenerators_logHeight J k (gen a.1) (hheight a.1) a.2.val a.2.property

theorem majorPhaseRationalTagConstraints_set_eq
    {X η : Type*} [Fintype η] {count : ℕ}
    (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k)
    (hspan : ∀ a, Submodule.span ℚ (Set.range (gen a)) = (detectedfast a).toSubmodule)
    (hgraded : ∀ a, BasisGradedSubmodule
      (weightedBasis (lowTaggedWeight J k) k (lowTaggedWeight_pos J k))
      (weightedBasisGrade (lowTaggedWeight J k) k) (detectedfast a).toSubmodule)
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ)) :
    fullTaggedGradedBaseIntersection J k K₀
      (fun a => majorPhaseDetectedRealBase J k (detectedfast a)) =
      K₀ ∩ {t | ∀ c ∈ majorPhaseRationalTagConstraints J k gen, c.member t} := by
  classical
  ext t
  change (t ∈ K₀ ∧ ∀ a,
      lowTaggedCoordinates J k (fun j i => t (Sum.inr ⟨j, i⟩)) ∈
        majorPhaseDetectedRealBase J k (detectedfast a)) ↔
    t ∈ K₀ ∧ ∀ c ∈ majorPhaseRationalTagConstraints J k gen, c.member t
  constructor
  · rintro ⟨ht, hmem⟩
    refine ⟨ht, ?_⟩
    intro c hc
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
    exact (majorPhaseTaggedGenerators_mem_iff J k (detectedfast a.1) (gen a.1)
      (hspan a.1) (hgraded a.1) (fun j i => t (Sum.inr ⟨j, i⟩))).mp
      (hmem a.1) a.2.val a.2.property
  · rintro ⟨ht, hmem⟩
    refine ⟨ht, ?_⟩
    intro a
    apply (majorPhaseTaggedGenerators_mem_iff J k (detectedfast a) (gen a)
      (hspan a) (hgraded a) (fun j i => t (Sum.inr ⟨j, i⟩))).mpr
    intro j hj
    apply hmem (majorPhaseRationalTagConstraint J k gen (a, ⟨j, hj⟩))
    exact List.mem_map.mpr ⟨(a, ⟨j, hj⟩), Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩

theorem majorPhase_rationalTaggedConstraintCertificate
    {X η : Type*} [Fintype η] {count : ℕ}
    (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
    (gen : η → Fin count → weightedSubalgebra (lowTaggedWeight J k) k)
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ)) (B : ℝ)
    (hgen : ∀ a, (count : ℝ) ≤ B ∧
      Submodule.span ℚ (Set.range (gen a)) = (detectedfast a).toSubmodule ∧
      BasisGradedSubmodule (weightedBasis (lowTaggedWeight J k) k (lowTaggedWeight_pos J k))
        (weightedBasisGrade (lowTaggedWeight J k) k) (detectedfast a).toSubmodule ∧
      ∀ i j, rationalLogHeight
        ((weightedBasis (lowTaggedWeight J k) k (lowTaggedWeight_pos J k)).repr (gen a i) j) ≤ B) :
    RationalTaggedConstraintCertificate J K₀
      (fullTaggedGradedBaseIntersection J k K₀
        (fun a => majorPhaseDetectedRealBase J k (detectedfast a))) B (Fintype.card η * m) := by
  refine ⟨majorPhaseRationalTagConstraints J k gen,
    majorPhaseRationalTagConstraints_length J k gen,
    majorPhaseRationalTagConstraints_budget J k gen B (fun a => (hgen a).1)
      (fun a => (hgen a).2.2.2), ?_⟩
  exact majorPhaseRationalTagConstraints_set_eq J k detectedfast gen
    (fun a => (hgen a).2.1) (fun a => (hgen a).2.2.1) K₀

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FullTaggedChartCoefficientRange
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype I]

noncomputable def polynomialTagLinearEmbedding (E : B → I → ℝ) :
    U ⊕ B → MvPolynomial (U ⊕ I) ℝ :=
  Sum.elim (fun u => X (Sum.inl u))
    (fun b => ∑ i, C (E b i) * X (Sum.inr i))

@[simp] theorem polynomialTagLinearEmbedding_inl (E : B → I → ℝ) (u : U) :
    polynomialTagLinearEmbedding E (Sum.inl u) = X (Sum.inl u) := rfl

@[simp] theorem polynomialTagLinearEmbedding_inr (E : B → I → ℝ) (b : B) :
    polynomialTagLinearEmbedding (U := U) E (Sum.inr b) =
      ∑ i, C (E b i) * X (Sum.inr i) := rfl

theorem polynomialTagLinearEmbedding_rename (E : B → I → ℝ)
    (p : MvPolynomial U ℝ) :
    aeval (R := ℝ) (polynomialTagLinearEmbedding E)
      (rename (Sum.inl : U → U ⊕ B) p) = rename (Sum.inl : U → U ⊕ I) p := by
  rw [aeval_rename, rename_eq_aeval]
  rfl

theorem normalizedRealPolynomialChart_linear_restriction_coordinate
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (A' : I → MvPolynomial U ℝ)
    (E : B → I → ℝ) (hA : ∀ b, A b = ∑ i, C (E b i) * A' i)
    (j : U ⊕ B) :
    aeval (R := ℝ) (polynomialTagLinearEmbedding E)
        (normalizedRealPolynomialChart H A j) =
      aeval (R := ℝ) (normalizedRealPolynomialChart H A')
        (polynomialTagLinearEmbedding E j) := by
  classical
  cases j with
  | inl u => simp
  | inr b =>
    simp only [normalizedRealPolynomialChart_inr, map_sub, aeval_X,
      polynomialTagLinearEmbedding_inr, polynomialTagLinearEmbedding_rename,
      map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_eq]
    rw [hA b]
    simp only [map_sum, map_mul, rename_C]
    simp only [mul_sub, Finset.sum_sub_distrib]

theorem normalizedRealPolynomialChart_linear_restriction
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (A' : I → MvPolynomial U ℝ)
    (E : B → I → ℝ) (hA : ∀ b, A b = ∑ i, C (E b i) * A' i)
    (p : MvPolynomial (U ⊕ B) ℝ) :
    aeval (R := ℝ) (polynomialTagLinearEmbedding E)
        (aeval (R := ℝ) (normalizedRealPolynomialChart H A) p) =
      aeval (R := ℝ) (normalizedRealPolynomialChart H A')
        (aeval (R := ℝ) (polynomialTagLinearEmbedding E) p) := by
  have h : (aeval (R := ℝ) (polynomialTagLinearEmbedding E)).comp
      (aeval (R := ℝ) (normalizedRealPolynomialChart H A)) =
      (aeval (R := ℝ) (normalizedRealPolynomialChart H A')).comp
        (aeval (R := ℝ) (polynomialTagLinearEmbedding E)) := by
    ext j : 1
    simpa only [AlgHom.comp_apply, aeval_X] using
      normalizedRealPolynomialChart_linear_restriction_coordinate H A A' E hA j
  exact AlgHom.congr_fun h p

theorem polynomialTagLinearEmbedding_eval (E : B → I → ℝ)
    (u : U → ℝ) (v : I → ℝ) (p : MvPolynomial (U ⊕ B) ℝ) :
    eval (Sum.elim u v) (aeval (R := ℝ) (polynomialTagLinearEmbedding E) p) =
      eval (Sum.elim u (fun b => ∑ i, E b i * v i)) p := by
  change aeval (R := ℝ) (Sum.elim u v)
    (aeval (R := ℝ) (polynomialTagLinearEmbedding E) p) =
      aeval (R := ℝ) (Sum.elim u (fun b => ∑ i, E b i * v i)) p
  rw [comp_aeval_apply]
  congr 1
  ext j : 1
  cases j <;> simp [polynomialTagLinearEmbedding]

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {B I U : Type*} [Fintype B] [Fintype I]
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (A : B → MvPolynomial U ℝ)
    (hA : ∀ α, (fun b => (A b).coeff α) ∈ K)

include hA

theorem normalizedChart_coefficients_mem (α : U →₀ ℕ) :
    coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A) α ∈ K := by
  have heq : coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A) α =
      fun b => (A b).coeff α := by
    funext b
    exact coefficients_ofCoordinates_basisFun A α b
  rw [heq]
  exact hA α

noncomputable def normalizedChartSubspaceCoordinates : I → MvPolynomial U ℝ :=
  fun i => coordinate (e.coord i).toAddMonoidHom
    (restrictCoefficients K (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A)
      (normalizedChart_coefficients_mem K A hA))

omit [Fintype I] in
theorem normalizedChartSubspaceCoordinates_coeff (α : U →₀ ℕ) (i : I) :
    (normalizedChartSubspaceCoordinates K e A hA i).coeff α =
      e.repr ⟨fun b => (A b).coeff α, hA α⟩ i := by
  unfold normalizedChartSubspaceCoordinates
  rw [coeff_coordinate]
  change e.repr (coefficients
    (restrictCoefficients K (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A)
      (normalizedChart_coefficients_mem K A hA)) α) i = _
  congr 1
  apply congrArg e.repr
  apply Subtype.ext
  rw [coefficients_restrictCoefficients]
  funext b
  exact coefficients_ofCoordinates_basisFun A α b

theorem normalizedChartSubspaceCoordinates_reconstruct (b : B) :
    A b = ∑ i, (e i : B → ℝ) b • normalizedChartSubspaceCoordinates K e A hA i := by
  classical
  ext α
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    normalizedChartSubspaceCoordinates_coeff, smul_eq_mul]
  have heq := congrArg (fun z : K => (z : B → ℝ) b)
    (e.sum_repr ⟨fun c => (A c).coeff α, hA α⟩)
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, mul_comm] using heq.symm

theorem normalizedChartSubspaceCoordinates_eval_mem (x : U → ℝ) :
    (fun b => MvPolynomial.eval x (A b)) ∈ K := by
  let P := ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A
  let Q := restrictCoefficients K P (normalizedChart_coefficients_mem K A hA)
  have heval : (eval (V := K) x Q : B → ℝ) = eval x P :=
    eval_restrictCoefficients K P (normalizedChart_coefficients_mem K A hA) x
  have hcoord : eval x P = fun b => MvPolynomial.eval x (A b) := by
    have h := eval₂_ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A x
    have he : eval₂ x P = eval x P := by
      simpa using (eval₂_algebraMap (S := ℝ) x P)
    rw [he] at h
    simpa only [Pi.basisFun_equivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply]
      using h
  rw [← hcoord, ← heval]
  exact (eval (V := K) x Q).property

end Erdos3

end

section

namespace Erdos3
open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype B] [Fintype I]

noncomputable def polynomialSubspaceRestriction (K : Submodule ℝ (B → ℝ))
    (e : Basis I ℝ K) : MvPolynomial (U ⊕ B) ℝ →ₐ[ℝ] MvPolynomial (U ⊕ I) ℝ :=
  aeval (R := ℝ) (polynomialTagLinearEmbedding (fun b i => (e i : B → ℝ) b))

omit [Fintype B] in
theorem polynomialSubspaceRestriction_eval (K : Submodule ℝ (B → ℝ))
    (e : Basis I ℝ K) (p : MvPolynomial (U ⊕ B) ℝ) (u : U → ℝ) (v : I → ℝ) :
    eval (Sum.elim u v) (polynomialSubspaceRestriction K e p) =
      eval (Sum.elim u (fun b => ∑ i, (e i : B → ℝ) b * v i)) p :=
  polynomialTagLinearEmbedding_eval _ u v p

omit [Fintype B] in
theorem polynomialSubspaceRestriction_eq_of_eval (K : Submodule ℝ (B → ℝ))
    (e : Basis I ℝ K) (p q : MvPolynomial (U ⊕ B) ℝ)
    (h : ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b) p = eval (Sum.elim u b) q) :
    polynomialSubspaceRestriction K e p = polynomialSubspaceRestriction K e q := by
  classical
  apply MvPolynomial.funext
  intro x
  let u : U → ℝ := fun a => x (Sum.inl a)
  let v : I → ℝ := fun a => x (Sum.inr a)
  have hx : x = Sum.elim u v := by funext a; cases a <;> rfl
  rw [hx, polynomialSubspaceRestriction_eval, polynomialSubspaceRestriction_eval]
  apply h
  have he : (fun b => ∑ i, (e i : B → ℝ) b * v i) =
      ((∑ i, v i • e i : K) : B → ℝ) := by
    ext b
    simp [mul_comm]
  rw [he]
  exact (∑ i, v i • e i : K).property

omit [Fintype B] in
theorem polynomialSubspaceRestriction_eval_basis (K : Submodule ℝ (B → ℝ))
    (e : Basis I ℝ K) (p : MvPolynomial (U ⊕ B) ℝ) (u : U → ℝ) (b : K) :
    eval (Sum.elim u (fun i => e.repr b i)) (polynomialSubspaceRestriction K e p) =
      eval (Sum.elim u (b : B → ℝ)) p := by
  rw [polynomialSubspaceRestriction_eval]
  have he : (fun c => ∑ i, (e i : B → ℝ) c * e.repr b i) = (b : B → ℝ) := by
    funext c
    have h := congrArg (fun z : K => (z : B → ℝ) c) (e.sum_repr b)
    simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, mul_comm] using h
  rw [he]

omit [Fintype B] in
theorem polynomialSubspaceRestriction_eval_eq (K : Submodule ℝ (B → ℝ))
    (e : Basis I ℝ K) (p q : MvPolynomial (U ⊕ B) ℝ)
    (h : polynomialSubspaceRestriction K e p = polynomialSubspaceRestriction K e q)
    (u : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
    eval (Sum.elim u b) p = eval (Sum.elim u b) q := by
  rw [← polynomialSubspaceRestriction_eval_basis K e p u ⟨b, hb⟩, h,
    polynomialSubspaceRestriction_eval_basis]

theorem normalizedChartSubspaceCoordinates_reconstruct_C
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (A : B → MvPolynomial U ℝ)
    (hA : ∀ α, (fun b => (A b).coeff α) ∈ K) (b : B) :
    A b = ∑ i, C ((e i : B → ℝ) b) * normalizedChartSubspaceCoordinates K e A hA i := by
  simpa only [MvPolynomial.smul_eq_C_mul] using
    normalizedChartSubspaceCoordinates_reconstruct K e A hA b

theorem polynomialSubspaceRestriction_normalizedChart
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (hA : ∀ α, (fun b => (A b).coeff α) ∈ K)
    (p : MvPolynomial (U ⊕ B) ℝ) :
    polynomialSubspaceRestriction K e
        (aeval (R := ℝ) (normalizedRealPolynomialChart H A) p) =
      aeval (R := ℝ) (normalizedRealPolynomialChart H
        (normalizedChartSubspaceCoordinates K e A hA))
        (polynomialSubspaceRestriction K e p) :=
  normalizedRealPolynomialChart_linear_restriction H A _ _
    (normalizedChartSubspaceCoordinates_reconstruct_C K e A hA) p

theorem normalizedChart_subspace_decomposition
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (hA : ∀ α, (fun b => (A b).coeff α) ∈ K)
    (p slow rat : MvPolynomial (U ⊕ B) ℝ)
    (h : ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b) p =
        eval (Sum.elim (fun i => u i / H i)
          (fun i => b i - eval u (A i))) slow + eval (Sum.elim u b) rat) :
    polynomialSubspaceRestriction K e p =
      aeval (R := ℝ) (normalizedRealPolynomialChart H
        (normalizedChartSubspaceCoordinates K e A hA))
        (polynomialSubspaceRestriction K e slow) +
      polynomialSubspaceRestriction K e rat := by
  have he : polynomialSubspaceRestriction K e p =
      polynomialSubspaceRestriction K e
        (aeval (R := ℝ) (normalizedRealPolynomialChart H A) slow + rat) := by
    apply polynomialSubspaceRestriction_eq_of_eval
    intro u b hb
    rw [map_add]
    exact (h u b hb).trans (by
      congr 1
      exact (eval_normalizedRealPolynomialChart_substitution H A u b slow).symm)
  rw [he, map_add, polynomialSubspaceRestriction_normalizedChart]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def fullTaggedMajorTopCoordinates
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (a : Σ j, J j) : MvPolynomial X ℝ :=
  homogeneousComponent (a.1.val + 1)
    (coordinate (LinearMap.proj a.2 : (J a.1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly a.1))

theorem majorTranslationTopCoordinates_lowTagged_eq (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    majorTranslationTopCoordinates (lowTaggedWeight J k)
        (fun i => lowTaggedPolynomial J k poly i - C (c i)) i =
      fullTaggedMajorTopCoordinates J poly (lowTaggedIndex J k i) := by
  have hc : homogeneousComponent (lowTaggedWeight J k i)
      (C (c i) : MvPolynomial X ℝ) = 0 := by
    apply homogeneousComponent_eq_zero
    simpa using lowTaggedWeight_pos J k i
  change homogeneousComponent (lowTaggedWeight J k i)
      (lowTaggedPolynomial J k poly i - C (c i)) =
    homogeneousComponent (lowTaggedWeight J k i) (lowTaggedPolynomial J k poly i)
  rw [map_sub, hc, sub_zero]

theorem lowTaggedMajorChart_rename (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ) (H : X → ℝ)
    (i : X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) :
    rename (lowTaggedVariableEmbedding J k)
      (normalizedRealPolynomialChart H
        (majorTranslationTopCoordinates (lowTaggedWeight J k)
          (fun i => lowTaggedPolynomial J k poly i - C (c i))) i) =
      normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly)
        (lowTaggedVariableEmbedding J k i) := by
  cases i with
  | inl i => simp only [normalizedRealPolynomialChart_inl, lowTaggedVariableEmbedding_inl,
      map_mul, rename_C, rename_X]
  | inr i =>
    simp only [normalizedRealPolynomialChart_inr, lowTaggedVariableEmbedding_inr,
      map_sub, rename_X, rename_rename, majorTranslationTopCoordinates_lowTagged_eq]
    rfl

omit [∀ j, Fintype (J j)] in

theorem fullTaggedMajorChart_homogeneous
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (H : X → ℝ)
    (i : X ⊕ (Σ j, J j)) :
    (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly) i).IsWeightedHomogeneous
      (fullTaggedVariableWeight J) (fullTaggedVariableWeight J i) := by
  cases i with
  | inl x =>
    exact (isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inl x)).C_mul _
  | inr a =>
    apply (isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inr a)).sub
    apply majorParameterRename_homogeneous (fun _ : X => 1)
      (fun a : Σ j, J j => a.1.val + 1)
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]

theorem lowTaggedVectorExtend_majorChart (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ) (H : X → ℝ)
    (slow : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ V) :
    lowTaggedVectorExtend J k
        (realChartSubstitute (normalizedRealPolynomialChart H
          (majorTranslationTopCoordinates (lowTaggedWeight J k)
            (fun i => lowTaggedPolynomial J k poly i - C (c i)))) slow) =
      realChartSubstitute (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly))
        (lowTaggedVectorExtend J k slow) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro x
  rw [map_sub, lowTaggedVectorExtend_eval₂, eval₂_realChartSubstitute,
    eval₂_realChartSubstitute, lowTaggedVectorExtend_eval₂]
  apply sub_eq_zero.mpr
  apply congrArg (fun t => eval₂ t slow)
  funext i
  change MvPolynomial.eval (x ∘ lowTaggedVariableEmbedding J k) _ =
    MvPolynomial.eval x _
  rw [← MvPolynomial.eval_rename, lowTaggedMajorChart_rename]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem fullTaggedMajorTopCoordinates_coefficients_mem_tag
    {m : ℕ} {X : Type*} (J : Fin m → Type*)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (α : X →₀ ℕ) (j : Fin m) :
    (fun i => (fullTaggedMajorTopCoordinates J poly ⟨j, i⟩).coeff α) ∈ U j := by
  classical
  by_cases hα : α.degree = j.val + 1
  · have hne : α ≠ 0 := by
      intro hz
      simp [hz] at hα
    have heq : (fun i => (fullTaggedMajorTopCoordinates J poly ⟨j, i⟩).coeff α) =
        coefficients (poly j) α := by
      funext i
      rw [fullTaggedMajorTopCoordinates, MvPolynomial.coeff_homogeneousComponent,
        if_pos hα, coeff_coordinate]
      rfl
    rw [heq]
    exact hcoeff j α hne
  · have heq : (fun i => (fullTaggedMajorTopCoordinates J poly ⟨j, i⟩).coeff α) = 0 := by
      funext i
      rw [fullTaggedMajorTopCoordinates, MvPolynomial.coeff_homogeneousComponent, if_neg hα]
      rfl
    rw [heq]
    exact (U j).zero_mem

theorem fullTaggedMajorTopCoordinates_coefficients_mem
    {m : ℕ} {X : Type*} (J : Fin m → Type*)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (K : Submodule ℝ ((Σ j, J j) → ℝ))
    (hU : ∀ x, (∀ j, (fun i => x ⟨j, i⟩) ∈ U j) → x ∈ K)
    (α : X →₀ ℕ) :
    (fun a => (fullTaggedMajorTopCoordinates J poly a).coeff α) ∈ K := by
  apply hU
  exact fun j => fullTaggedMajorTopCoordinates_coefficients_mem_tag J poly U hcoeff α j

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTagRestrictionBudget
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype I]

theorem polynomialTagLinearEmbedding_mass_le (E : B → I → ℝ)
    {L : ℝ} (hE : ∀ b i, |E b i| ≤ L) (j : U ⊕ B) :
    realPolynomialMass (polynomialTagLinearEmbedding E j) ≤
      max 1 ((Fintype.card I : ℝ) * L) := by
  classical
  cases j with
  | inl u =>
      simpa only [polynomialTagLinearEmbedding_inl, realPolynomialMass_X]
        using le_max_left 1 ((Fintype.card I : ℝ) * L)
  | inr b =>
      rw [polynomialTagLinearEmbedding_inr]
      apply (realPolynomialMass_sum_le _ _).trans
      apply le_trans (b := ∑ _i : I, L)
      · apply Finset.sum_le_sum
        intro i _
        exact (realPolynomialMass_C_mul_le _ _).trans
          (by simpa only [realPolynomialMass_X, mul_one] using hE b i)
      · simp

theorem polynomialTagLinearEmbedding_totalDegree_le (E : B → I → ℝ)
    (j : U ⊕ B) : (polynomialTagLinearEmbedding E j).totalDegree ≤ 1 := by
  classical
  cases j with
  | inl u => simp
  | inr b =>
      rw [polynomialTagLinearEmbedding_inr]
      apply totalDegree_finsetSum_le
      intro i _
      exact (totalDegree_mul _ _).trans (by simp)

theorem polynomialTagRestriction_mass_le (E : B → I → ℝ)
    (p : MvPolynomial (U ⊕ B) ℝ) {L : ℝ} {s : ℕ}
    (hE : ∀ b i, |E b i| ≤ L) (hp : p.totalDegree ≤ s) :
    realPolynomialMass (aeval (polynomialTagLinearEmbedding E) p) ≤
      realPolynomialMass p * (max 1 ((Fintype.card I : ℝ) * L)) ^ s :=
  realPolynomialMass_substitution_le p (polynomialTagLinearEmbedding E)
    (le_max_left _ _) (polynomialTagLinearEmbedding_mass_le E hE) hp

theorem polynomialTagRestriction_totalDegree_le (E : B → I → ℝ)
    (p : MvPolynomial (U ⊕ B) ℝ) :
    (aeval (polynomialTagLinearEmbedding E) p).totalDegree ≤ p.totalDegree := by
  change (eval₂Hom C (polynomialTagLinearEmbedding E) p).totalDegree ≤ p.totalDegree
  simpa only [mul_one] using polynomial_substitution_totalDegree_le p
    (polynomialTagLinearEmbedding E) (polynomialTagLinearEmbedding_totalDegree_le E) le_rfl

theorem polynomialTagLinearEmbedding_coefficientGrid (E : B → I → ℝ)
    (d : ℕ) (hE : ∀ b i, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * E b i)
    (j : U ⊕ B) :
    realPolynomialCoefficientGrid d (polynomialTagLinearEmbedding E j) := by
  classical
  cases j with
  | inl u => exact realPolynomialCoefficientGrid_X d _
  | inr b =>
      apply (realPolynomialCoefficientGrid_iff d _).mpr
      change C (d : ℝ) * (∑ i, C (E b i) * X (Sum.inr i)) ∈
        integralRealPolynomialSubring (U ⊕ I)
      rw [Finset.mul_sum]
      apply (integralRealPolynomialSubring (U ⊕ I)).sum_mem
      intro i _
      obtain ⟨z, hz⟩ := hE b i
      rw [← mul_assoc, ← map_mul, ← hz]
      exact (integralRealPolynomialSubring (U ⊕ I)).mul_mem
        (C_int_mem_integralRealPolynomialSubring z) (X_mem_integralRealPolynomialSubring _)

theorem polynomialTagRestriction_coefficientGrid (E : B → I → ℝ)
    (p : MvPolynomial (U ⊕ B) ℝ) (q d s : ℕ)
    (hE : ∀ b i, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * E b i)
    (hp : p.totalDegree ≤ s) (hq : realPolynomialCoefficientGrid q p) :
    realPolynomialCoefficientGrid (q * d ^ s)
      (aeval (polynomialTagLinearEmbedding E) p) :=
  realPolynomialCoefficientGrid_substitute p (polynomialTagLinearEmbedding E)
    q d s hp hq (polynomialTagLinearEmbedding_coefficientGrid E d hE)

theorem polynomialTagRestriction_mass_le_of_coeff_le [Fintype U] [Fintype B]
    (E : B → I → ℝ) (p : MvPolynomial (U ⊕ B) ℝ)
    {L M : ℝ} {s : ℕ} (hM : 0 ≤ M)
    (hE : ∀ b i, |E b i| ≤ L) (hp : p.totalDegree ≤ s)
    (hcoeff : ∀ α, |p.coeff α| ≤ M) :
    realPolynomialMass (aeval (polynomialTagLinearEmbedding E) p) ≤
      (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
        (max 1 ((Fintype.card I : ℝ) * L)) ^ s := by
  have hmass : realPolynomialMass p ≤
      ((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M :=
    monomialArray_abs_sum_le p.support id (fun _ _ _ _ h => h) s
      (fun α hα => (le_totalDegree hα).trans hp) (fun α => p.coeff α) hM
      (fun α _ => hcoeff α)
  exact (polynomialTagRestriction_mass_le E p hE hp).trans
    (mul_le_mul_of_nonneg_right hmass
      (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) s))

theorem polynomialTagRestriction_coeff_le_of_coeff_le [Fintype U] [Fintype B]
    (E : B → I → ℝ) (p : MvPolynomial (U ⊕ B) ℝ)
    {L M : ℝ} {s : ℕ} (hM : 0 ≤ M)
    (hE : ∀ b i, |E b i| ≤ L) (hp : p.totalDegree ≤ s)
    (hcoeff : ∀ α, |p.coeff α| ≤ M) (α : (U ⊕ I) →₀ ℕ) :
    |(aeval (polynomialTagLinearEmbedding E) p).coeff α| ≤
      (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
        (max 1 ((Fintype.card I : ℝ) * L)) ^ s :=
  (realPolynomialMass_coeff_le _ α).trans
    (polynomialTagRestriction_mass_le_of_coeff_le E p hM hE hp hcoeff)

theorem polynomialSubspaceRestriction_totalDegree_le
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (p : MvPolynomial (U ⊕ B) ℝ) :
    (polynomialSubspaceRestriction K e p).totalDegree ≤ p.totalDegree :=
  polynomialTagRestriction_totalDegree_le _ p

theorem polynomialSubspaceRestriction_coefficientGrid
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (p : MvPolynomial (U ⊕ B) ℝ) (q d s : ℕ)
    (he : ∀ i b, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (e i : B → ℝ) b)
    (hp : p.totalDegree ≤ s) (hq : realPolynomialCoefficientGrid q p) :
    realPolynomialCoefficientGrid (q * d ^ s) (polynomialSubspaceRestriction K e p) :=
  polynomialTagRestriction_coefficientGrid _ p q d s (fun b i => he i b) hp hq

theorem polynomialSubspaceRestriction_coeff_le [Fintype U] [Fintype B]
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (p : MvPolynomial (U ⊕ B) ℝ) {L M : ℝ} {s : ℕ} (hM : 0 ≤ M)
    (he : ∀ i b, |(e i : B → ℝ) b| ≤ L) (hp : p.totalDegree ≤ s)
    (hcoeff : ∀ α, |p.coeff α| ≤ M) (α : (U ⊕ I) →₀ ℕ) :
    |(polynomialSubspaceRestriction K e p).coeff α| ≤
      (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
        (max 1 ((Fintype.card I : ℝ) * L)) ^ s :=
  polynomialTagRestriction_coeff_le_of_coeff_le _ p hM (fun b i => he i b) hp hcoeff α

theorem polynomialSubspaceRestriction_coeff_div
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (p : MvPolynomial (U ⊕ B) ℝ) (q d s : ℕ) (hq : 0 < q) (hd : 0 < d)
    (he : ∀ i b, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (e i : B → ℝ) b)
    (hp : p.totalDegree ≤ s) (hgrid : realPolynomialCoefficientGrid q p)
    (α : (U ⊕ I) →₀ ℕ) :
    ∃ z : ℤ, (polynomialSubspaceRestriction K e p).coeff α =
      (z : ℝ) / (q * d ^ s : ℕ) := by
  obtain ⟨z, hz⟩ := polynomialSubspaceRestriction_coefficientGrid K e p q d s he hp hgrid
  refine ⟨z α, (eq_div_iff ?_).mpr ?_⟩
  · exact_mod_cast (Nat.mul_pos hq (pow_pos hd s)).ne'
  · simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using (congrFun hz α).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorSubspaceCorrectionRepresentatives
namespace OAI

section

namespace Erdos3

theorem boundedExponentWindow_finite (K : Type*) [Fintype K] (s : ℕ) :
    ({m : K →₀ ℕ | m.sum (fun _ n => n) ≤ s} : Set (K →₀ ℕ)).Finite := by
  classical
  let S := {m : K →₀ ℕ // m.sum (fun _ n => n) ≤ s}
  let f : S → List.Vector (Option K) s := fun m => paddedExponentWord m.val s m.property
  have hf : Function.Injective f := by
    intro m n hmn
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    have hc := congrArg
      (fun v : List.Vector (Option K) s => (v.val : Multiset (Option K)).count (some k)) hmn
    simpa only [f, paddedExponentWord_count] using hc
  let _ : Finite ↥({m : K →₀ ℕ | m.sum (fun _ n => n) ≤ s} : Set (K →₀ ℕ)) :=
    Finite.of_injective f hf
  exact Set.toFinite _

noncomputable def boundedExponentWindow (K : Type*) [Fintype K] (s : ℕ) :
    Finset (K →₀ ℕ) :=
  (boundedExponentWindow_finite K s).toFinset

@[simp] theorem boundedExponentWindow_mem_iff {K : Type*} [Fintype K]
    (s : ℕ) (m : K →₀ ℕ) :
    m ∈ boundedExponentWindow K s ↔ m.sum (fun _ n => n) ≤ s :=
  (boundedExponentWindow_finite K s).mem_toFinset

theorem boundedExponentWindow_card_le (K : Type*) [Fintype K] (s : ℕ) :
    (boundedExponentWindow K s).card ≤ (Fintype.card K + 1) ^ s :=
  boundedExponentSet_card_le _ s (fun m hm => (boundedExponentWindow_mem_iff s m).mp hm)

theorem support_subset_boundedExponentWindow {K R : Type*} [Fintype K] [CommSemiring R]
    (p : MvPolynomial K R) {s : ℕ} (hp : p.totalDegree ≤ s) :
    p.support ⊆ boundedExponentWindow K s := by
  intro m hm
  exact (boundedExponentWindow_mem_iff s m).mpr ((MvPolynomial.le_totalDegree hm).trans hp)

end Erdos3

end

section

namespace Erdos3
open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype B] [Fintype I]

end Erdos3

end

section

namespace Erdos3
open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I η α : Type*} [Fintype B] [Fintype I] [Fintype η]

theorem exists_finite_vector_subspace_normalized_correction_representatives
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : B → MvPolynomial U ℝ)
    (hA : ∀ d, (fun b => (A b).coeff d) ∈ K)
    (P : η → MvPolynomial (U ⊕ B) ℝ)
    (S : Finset ((U ⊕ I) →₀ ℕ)) (bound : ℝ) (hbound : 0 ≤ bound)
    (q : ℕ) (hq : 0 < q)
    (slow rat : α → η → MvPolynomial (U ⊕ B) ℝ) (admissible : α → Prop)
    (hsupport : ∀ a, admissible a → ∀ i,
      (polynomialSubspaceRestriction K e (slow a i)).support ⊆ S ∧
      (polynomialSubspaceRestriction K e (rat a i)).support ⊆ S)
    (hslow : ∀ a, admissible a → ∀ i d,
      |(polynomialSubspaceRestriction K e (slow a i)).coeff d| ≤ bound)
    (hrat : ∀ a, admissible a → ∀ i d,
      ∃ z : ℤ, (polynomialSubspaceRestriction K e (rat a i)).coeff d = (z : ℝ) / q)
    (hidentity : ∀ a, admissible a → ∀ i (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b) (P i) =
        eval (Sum.elim (fun j => u j / H j)
          (fun j => b j - eval u (A j))) (slow a i) + eval (Sum.elim u b) (rat a i)) :
    ∃ m : ℕ, m ≤ ((2 * ⌈(q : ℝ) * bound⌉₊ + 3) ^ S.card) ^ Fintype.card η ∧
      ∃ candidate : Fin m → α,
        (∀ j, admissible (candidate j)) ∧
        ∀ a, admissible a → ∃ j, ∀ i,
          polynomialSubspaceRestriction K e (slow (candidate j) i) =
            polynomialSubspaceRestriction K e (slow a i) ∧
          polynomialSubspaceRestriction K e (rat (candidate j) i) =
            polynomialSubspaceRestriction K e (rat a i) := by
  classical
  let restrict : α → η →
      (MvPolynomial (U ⊕ I) ℝ × MvPolynomial (U ⊕ I) ℝ) :=
    fun a i => (polynomialSubspaceRestriction K e (slow a i),
      polynomialSubspaceRestriction K e (rat a i))
  choose n hn c _hc hcover using fun i : η =>
    exists_finite_normalized_real_grid_corrections H hH
      (normalizedChartSubspaceCoordinates K e A hA) S
      (polynomialSubspaceRestriction K e (P i)) bound hbound q hq
  let Index := ∀ i : η, Fin (n i)
  let enum : Index ≃ Fin (Fintype.card Index) := Fintype.equivFin Index
  let family : Fin (Fintype.card Index) → η →
      (MvPolynomial (U ⊕ I) ℝ × MvPolynomial (U ⊕ I) ℝ) :=
    fun j i => c i (enum.symm j i)
  have hcoverage : ∀ a, admissible a → ∃ j, family j = restrict a := by
    intro a ha
    have each (i : η) : ∃ j, c i j = restrict a i := by
      apply hcover i
      refine ⟨(hsupport a ha i).1, (hsupport a ha i).2,
        hslow a ha i, hrat a ha i, ?_⟩
      exact normalizedChart_subspace_decomposition K e H A hA (P i)
        (slow a i) (rat a i) (hidentity a ha i)
    choose indices hi using each
    refine ⟨enum indices, ?_⟩
    funext i
    simpa only [family, Equiv.symm_apply_apply] using hi i
  obtain ⟨m, hm, candidate, hvalid, hcomplete⟩ :=
    exists_finite_fiber_representatives restrict admissible family hcoverage
  refine ⟨m, hm.trans ?_, candidate, hvalid, ?_⟩
  · change Fintype.card (∀ i : η, Fin (n i)) ≤ _
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    calc
      _ ≤ ∏ _i : η, (2 * ⌈(q : ℝ) * bound⌉₊ + 3) ^ S.card :=
        Finset.prod_le_prod' (fun i _ => hn i)
      _ = _ := by simp
  · intro a ha
    obtain ⟨j, hj⟩ := hcomplete a ha
    refine ⟨j, fun i => ?_⟩
    have hi := congrFun hj i
    exact ⟨congrArg Prod.fst hi, congrArg Prod.snd hi⟩

end Erdos3

end

section

namespace Erdos3
open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I η α : Type*} [Fintype U] [Fintype B] [Fintype I] [Fintype η]

theorem exists_finite_primitive_subspace_correction_representatives
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : B → MvPolynomial U ℝ)
    (hA : ∀ d, (fun b => (A b).coeff d) ∈ K)
    (P : η → MvPolynomial (U ⊕ B) ℝ)
    (s q d : ℕ) (hq : 0 < q) (hd : 0 < d)
    (L M : ℝ) (hM : 0 ≤ M)
    (he : ∀ i b, |(e i : B → ℝ) b| ≤ L)
    (hegrid : ∀ i b, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (e i : B → ℝ) b)
    (slow rat : α → η → MvPolynomial (U ⊕ B) ℝ) (admissible : α → Prop)
    (hdegree : ∀ a, admissible a → ∀ i,
      (slow a i).totalDegree ≤ s ∧ (rat a i).totalDegree ≤ s)
    (hcoeff : ∀ a, admissible a → ∀ i ex, |(slow a i).coeff ex| ≤ M)
    (hgrid : ∀ a, admissible a → ∀ i, realPolynomialCoefficientGrid q (rat a i))
    (hidentity : ∀ a, admissible a → ∀ i (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b) (P i) =
        eval (Sum.elim (fun j => u j / H j)
          (fun j => b j - eval u (A j))) (slow a i) + eval (Sum.elim u b) (rat a i)) :
    let Rcap := (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
      (max 1 ((Fintype.card I : ℝ) * L)) ^ s
    ∃ m : ℕ,
      m ≤ ((2 * ⌈((q * d ^ s : ℕ) : ℝ) * Rcap⌉₊ + 3) ^
        ((Fintype.card (U ⊕ I) + 1) ^ s)) ^ Fintype.card η ∧
      ∃ candidate : Fin m → α,
        (∀ j, admissible (candidate j)) ∧
        ∀ a, admissible a → ∃ j, ∀ i,
          polynomialSubspaceRestriction K e (slow (candidate j) i) =
            polynomialSubspaceRestriction K e (slow a i) ∧
          polynomialSubspaceRestriction K e (rat (candidate j) i) =
            polynomialSubspaceRestriction K e (rat a i) := by
  classical
  dsimp only
  let Rcap := (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
    (max 1 ((Fintype.card I : ℝ) * L)) ^ s
  have hRcap : 0 ≤ Rcap := mul_nonneg
    (mul_nonneg (pow_nonneg (by positivity) s) hM)
    (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) s)
  obtain ⟨m, hm, candidate, hvalid, hcover⟩ :=
    exists_finite_vector_subspace_normalized_correction_representatives
      K e H hH A hA P (boundedExponentWindow (U ⊕ I) s)
      Rcap hRcap (q * d ^ s) (Nat.mul_pos hq (pow_pos hd s))
      slow rat admissible
      (fun a ha i => ⟨support_subset_boundedExponentWindow _
        ((polynomialSubspaceRestriction_totalDegree_le K e _).trans (hdegree a ha i).1),
        support_subset_boundedExponentWindow _
        ((polynomialSubspaceRestriction_totalDegree_le K e _).trans (hdegree a ha i).2)⟩)
      (fun a ha i ex => polynomialSubspaceRestriction_coeff_le K e (slow a i) hM he
        (hdegree a ha i).1 (hcoeff a ha i) ex)
      (fun a ha i ex => polynomialSubspaceRestriction_coeff_div K e (rat a i)
        q d s hq hd hegrid (hdegree a ha i).2 (hgrid a ha i) ex)
      hidentity
  refine ⟨m, hm.trans ?_, candidate, hvalid, hcover⟩
  apply Nat.pow_le_pow_left
  exact Nat.pow_le_pow_right (by omega)
    (boundedExponentWindow_card_le (U ⊕ I) s)

end Erdos3

end

section

namespace Erdos3

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module
open scoped BigOperators

variable {U B I η α V : Type*} [Fintype U] [Fintype B] [Fintype I] [Fintype η]
  [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]

omit [Fintype U] [Fintype B] [Fintype η] [IsScalarTower ℚ ℝ V] in
theorem coordinate_grid_of_vector_grid (basis : Basis η ℝ V)
    (q : ℕ) (P : VectorPolynomial (U ⊕ B) ℚ V)
    (h : ∀ ex, (fun i => basis.coord i (coefficients P ex)) ∈ realDenominatorGrid q)
    (i : η) : realPolynomialCoefficientGrid q (coordinate (basis.coord i).toAddMonoidHom P) := by
  classical
  choose z hz using h
  refine ⟨fun ex => z ex i, funext fun ex => ?_⟩
  simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe, Pi.smul_apply, smul_eq_mul]
    using congrFun (hz ex) i

theorem exists_finite_vector_correction_representatives
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K) (basis : Basis η ℝ V)
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : B → MvPolynomial U ℝ)
    (hA : ∀ ex, (fun b => (A b).coeff ex) ∈ K)
    (P : VectorPolynomial (U ⊕ B) ℚ V)
    (s q d : ℕ) (hq : 0 < q) (hd : 0 < d)
    (L M : ℝ) (hM : 0 ≤ M)
    (he : ∀ i b, |(e i : B → ℝ) b| ≤ L)
    (hegrid : ∀ i b, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (e i : B → ℝ) b)
    (slow rat : α → VectorPolynomial (U ⊕ B) ℚ V) (admissible : α → Prop)
    (hdegree : ∀ a, admissible a → ∀ i,
      (coordinate (basis.coord i).toAddMonoidHom (slow a)).totalDegree ≤ s ∧
      (coordinate (basis.coord i).toAddMonoidHom (rat a)).totalDegree ≤ s)
    (hcoeff : ∀ a, admissible a → ∀ i ex, |basis.coord i (coefficients (slow a) ex)| ≤ M)
    (hgrid : ∀ a, admissible a → ∀ ex,
      (fun i => basis.coord i (coefficients (rat a) ex)) ∈ realDenominatorGrid q)
    (hidentity : ∀ a, admissible a → ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval₂ (Sum.elim u b) P =
        eval₂ (Sum.elim u b) (realChartSubstitute (normalizedRealPolynomialChart H A) (slow a)) +
        eval₂ (Sum.elim u b) (rat a)) :
    let Rcap := (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
      (max 1 ((Fintype.card I : ℝ) * L)) ^ s
    ∃ m : ℕ,
      m ≤ ((2 * ⌈((q * d ^ s : ℕ) : ℝ) * Rcap⌉₊ + 3) ^
        ((Fintype.card (U ⊕ I) + 1) ^ s)) ^ Fintype.card η ∧
      ∃ candidate : Fin m → α,
        (∀ j, admissible (candidate j)) ∧
        ∀ a, admissible a → ∃ j, ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
          eval₂ (Sum.elim u b) (slow (candidate j)) = eval₂ (Sum.elim u b) (slow a) ∧
          eval₂ (Sum.elim u b) (rat (candidate j)) = eval₂ (Sum.elim u b) (rat a) ∧
          eval₂ (Sum.elim u b)
              (realChartSubstitute (normalizedRealPolynomialChart H A) (slow (candidate j))) =
            eval₂ (Sum.elim u b)
              (realChartSubstitute (normalizedRealPolynomialChart H A) (slow a)) := by
  let scalar := fun (p : VectorPolynomial (U ⊕ B) ℚ V) i =>
    coordinate (basis.coord i).toAddMonoidHom p
  obtain ⟨m, hm, candidate, hvalid, hcover⟩ :=
    exists_finite_primitive_subspace_correction_representatives K e H hH A hA
      (scalar P) s q d hq hd L M hM he hegrid
      (fun a => scalar (slow a)) (fun a => scalar (rat a)) admissible hdegree
      (fun a ha i ex => by simpa only [scalar, coeff_coordinate,
        LinearMap.toAddMonoidHom_coe] using hcoeff a ha i ex)
      (fun a ha i => coordinate_grid_of_vector_grid basis q (rat a) (hgrid a ha) i)
      (by
        intro a ha i u b hb
        have h := congrArg (basis.coord i) (hidentity a ha u b hb)
        rw [eval₂_normalizedRealPolynomialChart] at h
        simpa only [map_add, coordinate_eval₂] using h)
  refine ⟨m, hm, candidate, hvalid, ?_⟩
  intro a ha
  obtain ⟨j, hj⟩ := hcover a ha
  have heval (t : α → VectorPolynomial (U ⊕ B) ℚ V)
      (ht : ∀ i, polynomialSubspaceRestriction K e (scalar (t (candidate j)) i) =
        polynomialSubspaceRestriction K e (scalar (t a) i))
      (u : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
      eval₂ (Sum.elim u b) (t (candidate j)) = eval₂ (Sum.elim u b) (t a) := by
    apply basis.repr.injective
    ext i
    change basis.coord i _ = basis.coord i _
    rw [coordinate_eval₂, coordinate_eval₂]
    exact polynomialSubspaceRestriction_eval_eq K e _ _ (ht i) u b hb
  refine ⟨j, ?_⟩
  intro u b hb
  refine ⟨heval slow (fun i => (hj i).1) u b hb,
    heval rat (fun i => (hj i).2) u b hb, ?_⟩
  rw [eval₂_normalizedRealPolynomialChart, eval₂_normalizedRealPolynomialChart]
  exact heval slow (fun i => (hj i).1) _ _
    (K.sub_mem hb (normalizedChartSubspaceCoordinates_eval_mem K A hA u))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FullChartHomogeneousCorrection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)

variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ) (N : X → ℕ) (budget : ℝ)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)


end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)


end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

structure FullChartFiniteHistory
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
    (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
    (Utag : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (N : X → ℕ) (Bphase : ℝ) (n : ℕ) where
  slow : ℕ → VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
  rat : ℕ → VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
  q : ℕ → ℕ
  K : Set (X ⊕ (Σ j, J j) → ℝ)
  subset : K ⊆ Kinitial
  dilation : ∀ t ∈ K, ∀ r : ℚ,
    (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈ K
  retained : ∀ t ∈ Kinitial, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K
  slow_bound : ∀ j < n, ∀ α i, |basis.coord i (coefficients (slow j) α)| ≤ Real.exp Bphase
  q_pos : ∀ j < n, 0 < q j
  q_bound : ∀ j < n, (q j : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * Bphase)
  rat_grid : ∀ j < n, ∀ α,
    (fun i => basis.coord i (coefficients (rat j) α)) ∈ realDenominatorGrid (q j)
  invariant :
    let outer := F.restrictedMajorOuterFactors b ω hF (fullTaggedVariableWeight J) fast lift
      (fun j => realChartSubstitute (normalizedRealPolynomialChart (fun i => (N i : ℝ))
        (fullTaggedMajorTopCoordinates J poly)) (slow j)) rat n
    ∀ t ∈ K, ∀ j ≤ n,
      F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
        (outer.1⁻¹ * Z * outer.2⁻¹).coord ∈ fast.baseChange ℝ

namespace FullChartFiniteHistory

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)]
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (Bphase : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)
local notation "State" => FullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase

noncomputable def outer {n : ℕ} (H : State n) :
    F.RealPolynomialSymbolGroup wt × F.RealPolynomialSymbolGroup wt :=
  F.restrictedMajorOuterFactors b ω hF wt fast lift
    (fun j => realChartSubstitute chart (H.slow j)) H.rat n

variable {F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase}

end FullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X : Type}
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)


end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

def CertifiedFullChartDetectedDecomposition : Prop :=
  ∃ (pS pR : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal)
    (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ)),
    0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget) ∧
    K' ⊆ K₀ ∧
    (∀ t ∈ K', ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K') ∧
    (∀ t ∈ K₀, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K') ∧
    (∀ α i, |basis.coord i (coefficients pS α)| ≤ Real.exp budget) ∧
    (∀ α, (fun i => basis.coord i (coefficients pR α)) ∈ realDenominatorGrid q) ∧
    (∀ t ∈ K', ∀ j ≤ k,
      F.realSymbolGradeEvaluation b ω hF wt j t
        ((left * F.restrictedMajorCorrection b ω hF wt fast lift k
            (realChartSubstitute chart pS))⁻¹ * Z *
          (F.restrictedMajorCorrection b ω hF wt fast lift k pR * right)⁻¹).coord ∈
        fast.baseChange ℝ) ∧
    (∃ (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
      (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ quotientReal),
      pS = lowTaggedVectorExtend J k slow ∧ pR = lowTaggedVectorExtend J k rat ∧
      K' = fullTaggedGradedBaseIntersection J k K₀
        (fun i => majorPhaseDetectedRealBase J k (detectedfast i))) ∧
    RationalTaggedConstraintCertificate J K₀ K' budget (Fintype.card η * m) ∧
    ∀ t ∈ K', fast.mkQ.baseChange ℝ
      (F.realSymbolGradeEvaluation b ω hF wt k t (left⁻¹ * Z * right⁻¹).coord) =
      eval₂ t (realChartSubstitute chart pS) + eval₂ t pR

omit [Fintype η] in

theorem fullChart_grade_quotient_of_low_value
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (K : η → Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J k)) → ℝ))
    (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ quotientReal)
    (hvalue : ∀ (u : X → ℝ) (z : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ),
      (∀ i, z ∈ K i) →
      eval₂ (Sum.elim u z) (lowTaggedVectorRestrict J k
        (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord)) =
        eval₂ (Sum.elim u z) (realChartSubstitute
          (normalizedRealPolynomialChart (fun i => (N i : ℝ))
            (majorTranslationTopCoordinates (lowTaggedWeight J k)
              (fun i => lowTaggedPolynomial J k poly i - MvPolynomial.C (c i)))) slow) +
          eval₂ (Sum.elim u z) rat) :
    ∀ t ∈ fullTaggedGradedBaseIntersection J k K₀ K,
      fast.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation b ω hF wt k t (left⁻¹ * Z * right⁻¹).coord) =
        eval₂ t (realChartSubstitute chart (lowTaggedVectorExtend J k slow)) +
          eval₂ t (lowTaggedVectorExtend J k rat) := by
  let P := F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord
  let lowchart := normalizedRealPolynomialChart (fun i => (N i : ℝ))
    (majorTranslationTopCoordinates (lowTaggedWeight J k)
      (fun i => lowTaggedPolynomial J k poly i - MvPolynomial.C (c i)))
  have hP : DegreeLE wt k P := by
    rw [degreeLE_iff]
    intro α hα
    by_contra hle
    have hz := F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF wt fast k
      (left⁻¹ * Z * right⁻¹).coord α (ne_of_gt (Nat.lt_of_not_ge hle))
    exact Finsupp.mem_support_iff.mp hα hz
  have hquotLow : ∀ t ∈ fullTaggedGradedBaseIntersection J k K₀ K,
      fast.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation b ω hF wt k t (left⁻¹ * Z * right⁻¹).coord) =
        eval₂ t (lowTaggedVectorExtend J k (realChartSubstitute lowchart slow)) +
          eval₂ t (lowTaggedVectorExtend J k rat) := by
    intro t ht
    have h := hvalue (fun i => t (Sum.inl i))
      (fun b => t (lowTaggedVariableEmbedding J k (Sum.inr b))) ht.2
    have hsplit : Sum.elim (fun i => t (Sum.inl i))
        (fun b => t (lowTaggedVariableEmbedding J k (Sum.inr b))) =
        t ∘ lowTaggedVariableEmbedding J k := by
      funext i
      cases i <;> rfl
    rw [hsplit] at h
    rw [← F.realSymbolGradeQuotientPolynomial_eval,
      lowTaggedVectorRestrict_eval₂ J k _ hP, lowTaggedVectorExtend_eval₂,
      lowTaggedVectorExtend_eval₂]
    with_reducible exact h
  intro t ht
  have h := hquotLow t ht
  dsimp only [lowchart] at h
  simp only [lowTaggedVectorExtend_majorChart J k poly c (fun i => (N i : ℝ)) slow] at h
  with_reducible exact h

theorem certifiedFullChartDetectedDecomposition_of_vector_detection
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast)
    (hsection : ∀ y, fast.mkQ (lift y) = y)
    (hK₀ : ∀ t ∈ K₀, ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K₀)
    (hlower : ∀ t ∈ K₀, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF wt j t
        (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
    (hdetected : MajorPhaseVectorDetectedConclusion (L := M) J k Utag poly c N budget basis
      (lowTaggedVectorRestrict J k
        (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord))) :
    CertifiedFullChartDetectedDecomposition F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget := by
  obtain ⟨detectedfast, gen, slow, rat, q, hgen, hgrade, hretain, _, hcoeff,
    hq, hqB, hgrid, _, _, hvalue⟩ := hdetected
  let K := fun i => majorPhaseDetectedRealBase J k (detectedfast i)
  have hquot := fullChart_grade_quotient_of_low_value F b ω hF J k fast
    Z left right K₀ poly N c K slow rat (by with_reducible exact hvalue)
  have hstep := F.restricted_symbol_major_grade_step b ω hF wt fast hfast lift hsection
    k Z left right K₀ (fullTaggedGradedBaseIntersection J k K₀ K)
    (fullTaggedGradedBaseIntersection_subset J k K₀ K)
    (fullTaggedGradedBaseIntersection_rat_dilation J k K₀ K hgrade hK₀)
    (realChartSubstitute chart (lowTaggedVectorExtend J k slow))
    (lowTaggedVectorExtend J k rat) hlower (by with_reducible exact hquot)
  have hcap := lowTaggedVectorExtend_coordinate_coefficient_bound J k
    (fun i => (basis.coord i).toAddMonoidHom) slow (Real.exp budget)
    (Real.exp_pos budget).le hcoeff
  have hden := lowTaggedVectorExtend_coefficients_grid J k
    (fun i => (basis.coord i).toAddMonoidHom) rat q hgrid
  obtain ⟨A, D, hA, hD, _, _, _, _, hnext⟩ := hstep
  have hAc : A = F.restrictedMajorCorrection b ω hF wt fast lift k
      (realChartSubstitute chart (lowTaggedVectorExtend J k slow)) := by
    apply NilpotentLieBCHGroup.ext
    dsimp only [restrictedMajorCorrection]
    with_reducible exact hA
  have hDc : D = F.restrictedMajorCorrection b ω hF wt fast lift k
      (lowTaggedVectorExtend J k rat) := by
    apply NilpotentLieBCHGroup.ext
    dsimp only [restrictedMajorCorrection]
    with_reducible exact hD
  rw [hAc, hDc] at hnext
  have hcertificate := majorPhase_rationalTaggedConstraintCertificate J k
    detectedfast gen K₀ budget hgen
  unfold CertifiedFullChartDetectedDecomposition
  refine ⟨lowTaggedVectorExtend J k slow, lowTaggedVectorExtend J k rat, q,
    fullTaggedGradedBaseIntersection J k K₀ K, hq, hqB,
    fullTaggedGradedBaseIntersection_subset J k K₀ K,
    fullTaggedGradedBaseIntersection_rat_dilation J k K₀ K hgrade hK₀,
    ?_, hcap, hden, ?_, ?_, hcertificate, ?_⟩
  · intro t ht hU
    refine ⟨ht, ?_⟩
    intro i
    change lowTaggedCoordinates J k (fun j a => t (Sum.inr ⟨j, a⟩)) ∈ K i
    apply (lowTaggedCoordinates_mem_iff J k (K i) (hgrade i) _).mpr
    intro j
    exact le_lowTaggedSubspaceFamily J k Utag (K i) (hretain i) j (hU j)
  · with_reducible exact hnext
  · exact ⟨detectedfast, slow, rat, rfl, rfl, rfl⟩
  · with_reducible exact hquot

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

theorem weightedHomogeneousComponent_totalDegree_le_of_positive
    {σ R : Type*} [CommRing R] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (p : MvPolynomial σ R) :
    (MvPolynomial.weightedHomogeneousComponent w k p).totalDegree ≤ k := by
  classical
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro α hα
  rw [MvPolynomial.support_weightedHomogeneousComponent] at hα
  exact (exponentSum_le_positive_weight w hw α).trans (Finset.mem_filter.mp hα).2.le

namespace VectorPolynomial

variable {σ R V η : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem weightedHomogeneousPart_idempotent (w : σ → ℕ) (k : ℕ)
    (p : VectorPolynomial σ R V) :
    weightedHomogeneousPart w k (weightedHomogeneousPart w k p) =
      weightedHomogeneousPart w k p :=
  weightedHomogeneousPart_eq_self (weightedHomogeneousPart_homogeneous w k p)

theorem weightedHomogeneousPart_coordinate_bound (w : σ → ℕ) (k : ℕ)
    (f : η → V →+ ℝ) (p : VectorPolynomial σ R V) {C : ℝ} (hC : 0 ≤ C)
    (hp : ∀ α i, |f i (coefficients p α)| ≤ C) :
    ∀ α i, |f i (coefficients (weightedHomogeneousPart w k p) α)| ≤ C := by
  intro α i
  rw [coefficients_weightedHomogeneousPart]
  split_ifs
  · exact hp α i
  · simpa only [map_zero, abs_zero] using hC

theorem weightedHomogeneousPart_coefficients_grid (w : σ → ℕ) (k : ℕ)
    (f : η → V →+ ℝ) (p : VectorPolynomial σ R V) (q : ℕ)
    (hp : ∀ α, (fun i => f i (coefficients p α)) ∈ realDenominatorGrid q) :
    ∀ α, (fun i => f i (coefficients (weightedHomogeneousPart w k p) α)) ∈
      realDenominatorGrid q := by
  intro α
  simp only [coefficients_weightedHomogeneousPart]
  split_ifs
  · exact hp α
  · refine ⟨fun _ => 0, ?_⟩
    ext i
    simp

theorem weightedHomogeneousPart_coordinate_totalDegree_le
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (k : ℕ) (f : V →+ ℝ)
    (p : VectorPolynomial σ R V) :
    (coordinate f (weightedHomogeneousPart w k p)).totalDegree ≤ k := by
  rw [coordinate_weightedHomogeneousPart]
  exact weightedHomogeneousComponent_totalDegree_le_of_positive w hw k _

end VectorPolynomial

namespace NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (fast : Submodule ℚ F.AssociatedGraded)
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)

theorem restrictedMajorCorrection_weightedHomogeneousPart (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))) :
    F.restrictedMajorCorrection b ω hF w fast lift k (weightedHomogeneousPart w k p) =
      F.restrictedMajorCorrection b ω hF w fast lift k p := by
  simp only [restrictedMajorCorrection, weightedHomogeneousPart_idempotent]

variable {m : ℕ} {X : Type} (J : Fin m → Type)

theorem restrictedMajorCorrection_fullChart_homogeneous (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (H : X → ℝ)
    (p : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
      (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))) :
    F.restrictedMajorCorrection b ω hF (fullTaggedVariableWeight J) fast lift k
      (realChartSubstitute (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly))
        (weightedHomogeneousPart (fullTaggedVariableWeight J) k p)) =
    F.restrictedMajorCorrection b ω hF (fullTaggedVariableWeight J) fast lift k
      (realChartSubstitute (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly)) p) := by
  rw [realChartSubstitute_weightedHomogeneousPart _ _ _
    (fullTaggedMajorChart_homogeneous J poly H),
    restrictedMajorCorrection_weightedHomogeneousPart]

theorem fullChart_quotient_identity_homogeneous (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (H : X → ℝ)
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight J))
    (K : Set (X ⊕ (Σ j, J j) → ℝ))
    (hK : ∀ t ∈ K, ∀ r : ℚ,
      (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈ K)
    (pS pR : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
      (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (hquot : ∀ t ∈ K, fast.mkQ.baseChange ℝ
      (F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) k t
        (left⁻¹ * Z * right⁻¹).coord) =
      eval₂ t (realChartSubstitute
        (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly)) pS) + eval₂ t pR) :
    ∀ t ∈ K, eval₂ t
      (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J) fast k
        (left⁻¹ * Z * right⁻¹).coord) =
      eval₂ t (realChartSubstitute
        (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly))
          (weightedHomogeneousPart (fullTaggedVariableWeight J) k pS)) +
      eval₂ t (weightedHomogeneousPart (fullTaggedVariableWeight J) k pR) := by
  intro t ht
  rw [realChartSubstitute_weightedHomogeneousPart _ _ _
    (fullTaggedMajorChart_homogeneous J poly H)]
  apply eval₂_weightedHomogeneousPart_decomposition_on _ _ _ _ K hK k
    (F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF _ fast k _) _ t ht
  intro x hx
  rw [realSymbolGradeQuotientPolynomial_eval]
  exact hquot x hx

section Certified

variable {η : Type*} [Fintype η] [∀ j, Fintype (J j)] (k : ℕ)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (K₀ : Set (X ⊕ (Σ j, J j) → ℝ)) (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

theorem CertifiedFullChartDetectedDecomposition.exists_homogeneous
    (h : CertifiedFullChartDetectedDecomposition F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget) :
    ∃ (pS pR : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal)
      (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ)),
      (∀ α, Finsupp.weight wt α ≠ k → coefficients pS α = 0) ∧
      (∀ α, Finsupp.weight wt α ≠ k → coefficients pR α = 0) ∧
      (∀ i, (coordinate (basis.coord i).toAddMonoidHom pS).totalDegree ≤ k) ∧
      (∀ i, (coordinate (basis.coord i).toAddMonoidHom pR).totalDegree ≤ k) ∧
      0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget) ∧
      K' ⊆ K₀ ∧
      (∀ t ∈ K', ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K') ∧
      (∀ t ∈ K₀, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K') ∧
      (∀ α i, |basis.coord i (coefficients pS α)| ≤ Real.exp budget) ∧
      (∀ α, (fun i => basis.coord i (coefficients pR α)) ∈ realDenominatorGrid q) ∧
      (∀ t ∈ K', ∀ j ≤ k,
        F.realSymbolGradeEvaluation b ω hF wt j t
          ((left * F.restrictedMajorCorrection b ω hF wt fast lift k
              (realChartSubstitute chart pS))⁻¹ * Z *
            (F.restrictedMajorCorrection b ω hF wt fast lift k pR * right)⁻¹).coord ∈
          fast.baseChange ℝ) ∧
      (∃ (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
        (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ quotientReal),
        pS = lowTaggedVectorExtend J k slow ∧ pR = lowTaggedVectorExtend J k rat ∧
        K' = fullTaggedGradedBaseIntersection J k K₀
          (fun i => majorPhaseDetectedRealBase J k (detectedfast i))) ∧
      RationalTaggedConstraintCertificate J K₀ K' budget (Fintype.card η * m) ∧
      ∀ t ∈ K', eval₂ t
        (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord) =
        eval₂ t (realChartSubstitute chart pS) + eval₂ t pR := by
  obtain ⟨pS, pR, q, K', hq, hqB, hsub, hdilate, hretain, hcap, hgrid,
    hnext, horigin, hcertificate, hquot⟩ := h
  refine ⟨weightedHomogeneousPart wt k pS, weightedHomogeneousPart wt k pR, q, K',
    weightedHomogeneousPart_homogeneous wt k pS,
    weightedHomogeneousPart_homogeneous wt k pR,
    (fun i => weightedHomogeneousPart_coordinate_totalDegree_le wt
      (fullTaggedVariableWeight_pos J) k (basis.coord i).toAddMonoidHom pS),
    (fun i => weightedHomogeneousPart_coordinate_totalDegree_le wt
      (fullTaggedVariableWeight_pos J) k (basis.coord i).toAddMonoidHom pR),
    hq, hqB, hsub, hdilate, hretain,
    weightedHomogeneousPart_coordinate_bound wt k (fun i => (basis.coord i).toAddMonoidHom)
      pS (Real.exp_nonneg budget) hcap,
    weightedHomogeneousPart_coefficients_grid wt k (fun i => (basis.coord i).toAddMonoidHom)
      pR q hgrid, ?_, ?_, hcertificate, ?_⟩
  · intro t ht j hj
    rw [restrictedMajorCorrection_fullChart_homogeneous,
      restrictedMajorCorrection_weightedHomogeneousPart]
    with_reducible exact hnext t ht j hj
  · obtain ⟨detectedfast, slow, rat, hs, hr, hK⟩ := horigin
    refine ⟨detectedfast, weightedHomogeneousPart (lowTaggedVariableWeight J k) k slow,
      weightedHomogeneousPart (lowTaggedVariableWeight J k) k rat, ?_, ?_, hK⟩
    · rw [hs, lowTaggedVectorExtend_weightedHomogeneousPart]
    · rw [hr, lowTaggedVectorExtend_weightedHomogeneousPart]
  · with_reducible
      exact fullChart_quotient_identity_homogeneous F b ω hF fast J k poly
        (fun i => (N i : ℝ)) Z left right K' hdilate pS pR (by with_reducible exact hquot)

end Certified

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoundedCertifiedFullChartMajorIteration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

structure CertifiedFullChartFiniteHistory
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
    (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
    (Utag : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (N : X → ℕ) (Bphase : ℝ) (n : ℕ) where
  slow : ℕ → VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
  rat : ℕ → VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
  q : ℕ → ℕ
  K : Set (X ⊕ (Σ j, J j) → ℝ)
  certificate : RationalTaggedConstraintCertificate J Kinitial K Bphase
    (n * (Fintype.card η * m))
  subset : K ⊆ Kinitial
  dilation : ∀ t ∈ K, ∀ r : ℚ,
    (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈ K
  retained : ∀ t ∈ Kinitial, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K
  slow_bound : ∀ j < n, ∀ α i, |basis.coord i (coefficients (slow j) α)| ≤ Real.exp Bphase
  q_pos : ∀ j < n, 0 < q j
  q_bound : ∀ j < n, (q j : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * Bphase)
  rat_grid : ∀ j < n, ∀ α,
    (fun i => basis.coord i (coefficients (rat j) α)) ∈ realDenominatorGrid (q j)
  invariant :
    let outer := F.restrictedMajorOuterFactors b ω hF (fullTaggedVariableWeight J) fast lift
      (fun j => realChartSubstitute (normalizedRealPolynomialChart (fun i => (N i : ℝ))
        (fullTaggedMajorTopCoordinates J poly)) (slow j)) rat n
    ∀ t ∈ K, ∀ j ≤ n,
      F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
        (outer.1⁻¹ * Z * outer.2⁻¹).coord ∈ fast.baseChange ℝ

namespace CertifiedFullChartFiniteHistory

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)]
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (Bphase : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase

noncomputable def outer {n : ℕ} (H : State n) :
    F.RealPolynomialSymbolGroup wt × F.RealPolynomialSymbolGroup wt :=
  F.restrictedMajorOuterFactors b ω hF wt fast lift
    (fun j => realChartSubstitute chart (H.slow j)) H.rat n

noncomputable def initial
    (hK : ∀ t ∈ Kinitial, ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ Kinitial) :
    State 0 where
  slow := fun _ => 0
  rat := fun _ => 0
  q := fun _ => 1
  K := Kinitial
  certificate := by simpa using RationalTaggedConstraintCertificate.empty (J := J) Kinitial Bphase
  subset := fun _ ht => ht
  dilation := hK
  retained := fun _ ht _ => ht
  slow_bound := fun j hj => (Nat.not_lt_zero j hj).elim
  q_pos := fun j hj => (Nat.not_lt_zero j hj).elim
  q_bound := fun j hj => (Nat.not_lt_zero j hj).elim
  rat_grid := fun j hj => (Nat.not_lt_zero j hj).elim
  invariant := by
    dsimp only
    intro t ht j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rw [F.realSymbolGradeEvaluation_zero]
    exact Submodule.zero_mem _

variable {F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase}

theorem invariant_outer {n : ℕ} (H : State n) :
    ∀ t ∈ H.K, ∀ j ≤ n,
      F.realSymbolGradeEvaluation b ω hF wt j t
        (H.outer.1⁻¹ * Z * H.outer.2⁻¹).coord ∈ fast.baseChange ℝ := by
  dsimp only [outer]
  have h := H.invariant
  dsimp only at h
  with_reducible exact h

noncomputable def toUncertified {n : ℕ} (H : State n) :
    FullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase n where
  slow := H.slow
  rat := H.rat
  q := H.q
  K := H.K
  subset := H.subset
  dilation := H.dilation
  retained := H.retained
  slow_bound := H.slow_bound
  q_pos := H.q_pos
  q_bound := H.q_bound
  rat_grid := H.rat_grid
  invariant := H.invariant

@[simp] theorem outer_toUncertified {n : ℕ} (H : State n) :
    FullChartFiniteHistory.outer F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase
      H.toUncertified = H.outer := by
  dsimp only [FullChartFiniteHistory.outer, outer, toUncertified]

@[simp] theorem toUncertified_K {n : ℕ} (H : State n) : H.toUncertified.K = H.K := rfl

end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedFullChartAffineTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def fullTaggedLinearMapChart
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) :
    X ⊕ (Σ j, J j) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ
  | Sum.inl x => MvPolynomial.X (Sum.inl x)
  | Sum.inr ⟨j, i⟩ => ∑ a : J j,
      (P j (Pi.single a 1) i) • MvPolynomial.X (Sum.inr ⟨j, a⟩)

noncomputable def fullTaggedAffineMapChart
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ) :
    X ⊕ (Σ j, J j) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ
  | Sum.inl x => MvPolynomial.X (Sum.inl x)
  | Sum.inr ⟨j, i⟩ => C (c j i - P j (c j) i) +
      fullTaggedLinearMapChart J P (Sum.inr ⟨j, i⟩)

theorem fullTaggedLinearMapChart_homogeneous
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (v : X ⊕ (Σ j, J j)) :
    (fullTaggedLinearMapChart J P v).IsWeightedHomogeneous
      (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v) := by
  cases v with
  | inl x => exact isWeightedHomogeneous_X (R := ℝ) _ _
  | inr v =>
    apply (weightedHomogeneousSubmodule ℝ _ _).sum_mem
    intro a _
    exact (weightedHomogeneousSubmodule ℝ _ _).smul_mem _
      (isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inr ⟨v.1, a⟩))

theorem fullTaggedAffineMapChart_support
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (v : X ⊕ (Σ j, J j)) :
    fullTaggedAffineMapChart J P c v ∈
      weightedSupportLE (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v) := by
  cases v with
  | inl x => exact weightedSupportLE_X _ _
  | inr v =>
    apply (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    apply (weightedSupportLE _ _).sum_mem
    intro a _
    exact (weightedSupportLE _ _).smul_mem _
      (weightedSupportLE_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inr ⟨v.1, a⟩))

theorem fullTaggedAffineMapChart_top
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (v : X ⊕ (Σ j, J j)) :
    weightedHomogeneousComponent (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v)
      (fullTaggedAffineMapChart J P c v) = fullTaggedLinearMapChart J P v := by
  cases v with
  | inl x => exact weightedHomogeneousComponent_eq_self (isWeightedHomogeneous_X (R := ℝ) _ _)
  | inr v =>
    change weightedHomogeneousComponent _ _ (C _ + _) = _
    rw [map_add, weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_C (R := ℝ) _ _)]
    simp only [fullTaggedVariableWeight, Sum.elim_inr, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ↓reduceIte, zero_add]
    exact weightedHomogeneousComponent_eq_self (fullTaggedLinearMapChart_homogeneous J P _)

theorem fullTaggedLinearMapChart_eval_tag
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (x : X ⊕ (Σ j, J j) → ℝ)
    (j : Fin m) (i : J j) :
    MvPolynomial.eval x (fullTaggedLinearMapChart J P (Sum.inr ⟨j, i⟩)) =
      P j (fun a => x (Sum.inr ⟨j, a⟩)) i := by
  have hsum : ∑ a : J j, x (Sum.inr ⟨j, a⟩) • Pi.single a (1 : ℝ) =
      (fun a => x (Sum.inr ⟨j, a⟩)) := by
    ext a
    simp [Pi.smul_apply, Pi.single_apply]
  rw [fullTaggedLinearMapChart]
  simp only [map_sum, smul_eq_C_mul, map_mul, eval_C, eval_X]
  rw [← hsum, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem fullTaggedAffineMapChart_eval_tag
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X ⊕ (Σ j, J j) → ℝ) (j : Fin m) (i : J j) :
    MvPolynomial.eval x (fullTaggedAffineMapChart J P c (Sum.inr ⟨j, i⟩)) =
      c j i + P j ((fun a => x (Sum.inr ⟨j, a⟩)) - c j) i := by
  rw [fullTaggedAffineMapChart, map_add, eval_C, fullTaggedLinearMapChart_eval_tag,
    map_sub, Pi.sub_apply]
  ring

theorem fullTaggedAffineMapChart_top_mem_set
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (hP : ∀ j x, P j x ∈ U j)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ))
    (hK : ∀ y, (∀ j, (fun i => y (Sum.inr ⟨j, i⟩)) ∈ U j) → y ∈ K)
    (x : X ⊕ (Σ j, J j) → ℝ) :
    (fun v => MvPolynomial.eval x
      (weightedHomogeneousComponent (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v)
        (fullTaggedAffineMapChart J P c v))) ∈ K := by
  apply hK
  intro j
  simp_rw [fullTaggedAffineMapChart_top, fullTaggedLinearMapChart_eval_tag]
  exact hP j _

theorem fullTaggedAffineMapChart_eval_eq
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (hP : ∀ j y, y ∈ U j → P j y = y)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hx : ∀ j, (fun a => x (Sum.inr ⟨j, a⟩)) - c j ∈ U j) :
    (fun v => MvPolynomial.eval x (fullTaggedAffineMapChart J P c v)) = x := by
  funext v
  cases v with
  | inl a => exact MvPolynomial.eval_X _
  | inr v =>
    rw [fullTaggedAffineMapChart_eval_tag, hP _ _ (hx _), Pi.sub_apply]
    ring

theorem fullTaggedAffineMapChart_eval_eq_of_quotient
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (hP : ∀ j y, y ∈ U j → P j y = y)
    {D : Fin m → Type*} [∀ j, AddCommGroup (D j)] [∀ j, Module ℝ (D j)]
    (Q : ∀ j, (J j → ℝ) →ₗ[ℝ] D j) (hQ : ∀ j, LinearMap.ker (Q j) = U j)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hx : ∀ j, Q j (fun a => x (Sum.inr ⟨j, a⟩)) = Q j (c j)) :
    (fun v => MvPolynomial.eval x (fullTaggedAffineMapChart J P c v)) = x := by
  apply fullTaggedAffineMapChart_eval_eq J P c U hP x
  intro j
  rw [← hQ j, LinearMap.mem_ker, map_sub, hx j, sub_self]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

namespace CertifiedFullChartFiniteHistory

variable {m s : ℕ} {X ι η L : Type} [Fintype ι] [Fintype η]
  [LieRing L] [LieAlgebra ℚ L]
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {W : LieSubalgebra ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ W.toSubmodule))}
  {lift : (F.AssociatedGraded ⧸ W.toSubmodule) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}


end CertifiedFullChartFiniteHistory

namespace GlobalMarkedNativeFactors

variable {m s : ℕ} {X ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type*} [∀ j, Fintype (J j)]
  {W : LieSubalgebra ℚ F.AssociatedGraded}
  {Ktag : ∀ j, Submodule ℝ (J j → ℝ)} {c : ∀ j, J j → ℝ}


end GlobalMarkedNativeFactors
end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FullTaggedAffineComplementAgreement
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedAffineMapChart_eval_eq_of_complement
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hvalue : ∀ j, ((LinearMap.id : (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) - P j) (fun a => x (Sum.inr ⟨j, a⟩)) = c j)
    (hconstant : ∀ j, ((LinearMap.id : (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) - P j) (c j) = c j) :
    (fun v => MvPolynomial.eval x (fullTaggedAffineMapChart J P c v)) = x := by
  have hfixed : ∀ j y, y ∈ LinearMap.ker
      ((LinearMap.id : (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) - P j) → P j y = y := by
    intro j y hy
    change y - P j y = 0 at hy
    exact (sub_eq_zero.mp hy).symm
  apply fullTaggedAffineMapChart_eval_eq_of_quotient J P c
    (fun j => LinearMap.ker ((LinearMap.id : (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) - P j)) hfixed
    (fun j => (LinearMap.id : (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) - P j) (fun _ => rfl) x
  intro j
  rw [hvalue j, hconstant j]

theorem fullTaggedAffineMatrixChart_eval_eq_of_complement
    (P : ∀ j, Matrix (J j) (J j) ℚ) (c : ∀ j, J j → ℝ)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hvalue : ∀ j, rationalTagProjectionComplement (P j)
      (fun a => x (Sum.inr ⟨j, a⟩)) = c j)
    (hconstant : ∀ j, rationalTagProjectionComplement (P j) (c j) = c j) :
    (fun v => MvPolynomial.eval x
      (fullTaggedAffineMapChart J (fullTaggedRealMatrixProjection J P) c v)) = x := by
  exact fullTaggedAffineMapChart_eval_eq_of_complement J
    (fullTaggedRealMatrixProjection J P) c x hvalue hconstant

theorem fullTaggedAffineMatrixChart_eval_eq_of_anchor
    (P : ∀ j, Matrix (J j) (J j) ℚ) (c anchor : ∀ j, J j → ℝ)
    (x : X ⊕ (Σ j, J j) → ℝ)
    (hdisplacement : ∀ j, rationalTagProjectionComplement (P j)
      ((fun a => x (Sum.inr ⟨j, a⟩)) - anchor j) = 0)
    (hanchor : ∀ j, rationalTagProjectionComplement (P j) (anchor j) = c j)
    (hconstant : ∀ j, rationalTagProjectionComplement (P j) (c j) = c j) :
    (fun v => MvPolynomial.eval x
      (fullTaggedAffineMapChart J (fullTaggedRealMatrixProjection J P) c v)) = x := by
  apply fullTaggedAffineMatrixChart_eval_eq_of_complement J P c x ?_ hconstant
  intro j
  have h := hdisplacement j
  rw [map_sub, sub_eq_zero, hanchor j] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial
section ScalarTop
variable {σ τ R : Type*} [CommRing R]

theorem sampledTopPhase_remainder (w : σ → ℕ) (v : τ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    {P : MvPolynomial σ R} {k : ℕ}
    (hP : P.IsWeightedHomogeneous w k) :
    aeval β P - aeval (fun i => weightedHomogeneousComponent v (w i) (β i)) P ∈
      weightedSupportLT v k := by
  apply weightedComparison_difference w v
    (aeval β) (aeval (fun i => weightedHomogeneousComponent v (w i) (β i)))
  · intro i
    simpa only [aeval_X] using hβ i
  · intro i
    simpa only [aeval_X] using weightedTopPart_preserves_degree v v (w i) (hβ i)
  · intro i
    simpa only [aeval_X] using weightedTopPart_remainder_lt v (hβ i)
  · exact fun _ ha => (hP (mem_support_iff.mp ha)).le

theorem sampledTopPhase_remainder_totalDegree (w : σ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    {P : MvPolynomial σ R} {n : ℕ}
    (hP : P.IsWeightedHomogeneous w (n + 1)) :
    (aeval β P - aeval (fun i => homogeneousComponent (w i) (β i)) P).totalDegree ≤ n := by
  apply (mem_weightedSupportLE_one_iff _ _).mp
  exact weightedSupportLT_succ_le
    (sampledTopPhase_remainder w (fun _ : τ => 1) β hβ hP)
theorem sampledTopPhase_coordinate_homogeneous (k : ℕ) (P : MvPolynomial τ R) :
    (homogeneousComponent k P).IsWeightedHomogeneous (fun _ : τ => 1) k :=
  weightedHomogeneousComponent_isWeightedHomogeneous _ _

end ScalarTop

theorem sampledCurrentGrade_sampledCurrentGrade_realifyFunctional_basis_coord {V η : Type*} [AddCommGroup V] [Module ℚ V]
    (e : Module.Basis η ℚ V) (j : η) :
    realifyFunctional (e.coord j) = (e.baseChange ℝ).coord j := by
  classical
  apply (e.baseChange ℝ).ext
  intro i
  rw [Module.Basis.baseChange_apply, realifyFunctional_tmul, one_mul]
  simp

namespace NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem quotientFunctional_kills_fast (U : Submodule ℚ F.AssociatedGraded)
    (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ) (x : F.AssociatedGraded) (hx : x ∈ U) :
    (ℓ.comp U.mkQ) x = 0 := by
  have hz : U.mkQ x = 0 := by
    change x ∈ LinearMap.ker U.mkQ
    rwa [Submodule.ker_mkQ]
  simp only [LinearMap.comp_apply, hz, map_zero]

theorem scalarSymbolPolynomial_component_quotient (w : σ → ℕ)
    (U : Submodule ℚ F.AssociatedGraded) (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ)
    (k : ℕ) (g : F.RealPolynomialSymbolGroup w) :
    weightedHomogeneousComponent w k (F.scalarSymbolPolynomial b ω hF w (ℓ.comp U.mkQ) g) =
      coordinate (realifyFunctional ℓ).toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w U k g.coord) := by
  rw [scalarSymbolPolynomial, realSymbolGradeQuotientPolynomial,
    F.realGradedSymbolPolynomial_gradeProjection_eq_weightedHomogeneousPart,
    ← coordinate_weightedHomogeneousPart]
  ext α
  simp only [coeff_coordinate, coefficients_map, LinearMap.toAddMonoidHom_coe,
    LinearMap.restrictScalars_apply]
  exact realifyFunctional_comp ℓ U.mkQ _

theorem realSymbolGradeQuotientPolynomial_homogeneousPullback
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : Submodule ℚ F.AssociatedGraded) (k : ℕ) (x : F.RealPolynomialSymbol w) :
    F.realSymbolGradeQuotientPolynomial b ω hF v U k
        (F.realSymbolHomogeneousPullback b ω hF w v β x) =
      realChartSubstitute β (F.realSymbolGradeQuotientPolynomial b ω hF w U k x) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro u
  rw [map_sub, eval₂_realChartSubstitute, F.realSymbolGradeQuotientPolynomial_eval,
    F.realSymbolGradeQuotientPolynomial_eval,
    F.realSymbolGradeEvaluation_homogeneousPullback b ω hF w v β hβ, sub_self]

theorem scalarSymbolPolynomial_component_homogeneousPullback
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : Submodule ℚ F.AssociatedGraded) (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ)
    (k : ℕ) (Z left right : F.RealPolynomialSymbolGroup w) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
    weightedHomogeneousComponent v k
        (F.scalarSymbolPolynomial b ω hF v (ℓ.comp U.mkQ)
          ((pull left)⁻¹ * pull Z * (pull right)⁻¹)) =
      aeval β (coordinate (realifyFunctional ℓ).toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w U k (left⁻¹ * Z * right⁻¹).coord)) := by
  dsimp only
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul,
    F.scalarSymbolPolynomial_component_quotient,
    F.realSymbolHomogeneousPullbackHom_coord,
    F.realSymbolGradeQuotientPolynomial_homogeneousPullback b ω hF w v β hβ]
  apply MvPolynomial.funext
  intro u
  rw [← coordinate_eval₂, eval₂_realChartSubstitute, coordinate_eval₂]
  exact (MvPolynomial.comp_aeval_apply β (MvPolynomial.aeval u) _).symm

theorem scalarSymbolPolynomial_homogeneousComponent_homogeneousPullback
    (w : σ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous (fun _ : τ => 1) (w i))
    (U : Submodule ℚ F.AssociatedGraded) (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ)
    (k : ℕ) (Z left right : F.RealPolynomialSymbolGroup w) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w (fun _ : τ => 1) β hβ
    homogeneousComponent k
        (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1) (ℓ.comp U.mkQ)
          ((pull left)⁻¹ * pull Z * (pull right)⁻¹)) =
      aeval β (coordinate (realifyFunctional ℓ).toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w U k (left⁻¹ * Z * right⁻¹).coord)) :=
  F.scalarSymbolPolynomial_component_homogeneousPullback b ω hF w (fun _ : τ => 1)
    β hβ U ℓ k Z left right

theorem realSymbolGradeQuotientPolynomial_functional_homogeneous (w : σ → ℕ)
    (U : Submodule ℚ F.AssociatedGraded)
    (ℓ : (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)) →ₗ[ℝ] ℝ)
    (k : ℕ) (x : F.RealPolynomialSymbol w) :
    (coordinate ℓ.toAddMonoidHom
      (F.realSymbolGradeQuotientPolynomial b ω hF w U k x)).IsWeightedHomogeneous w k := by
  intro α hα
  by_contra hweight
  apply hα
  rw [coeff_coordinate,
    F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF w U k x α hweight, map_zero]

theorem exists_sampledCurrentGrade_lower_phase (w : σ → ℕ)
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (U : Submodule ℚ F.AssociatedGraded) (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ)
    (n : ℕ) (Z left right : F.RealPolynomialSymbolGroup w) :
    let topβ := fun i => homogeneousComponent (w i) (β i)
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w (fun _ : τ => 1) topβ
      (fun i => sampledTopPhase_coordinate_homogeneous (w i) (β i))
    ∃ lower : MvPolynomial τ ℝ, lower.totalDegree ≤ n ∧
      aeval β (coordinate (realifyFunctional ℓ).toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w U (n + 1) (left⁻¹ * Z * right⁻¹).coord)) =
      homogeneousComponent (n + 1)
        (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1) (ℓ.comp U.mkQ)
          ((pull left)⁻¹ * pull Z * (pull right)⁻¹)) + lower := by
  dsimp only
  let P := coordinate (realifyFunctional ℓ).toAddMonoidHom
    (F.realSymbolGradeQuotientPolynomial b ω hF w U (n + 1) (left⁻¹ * Z * right⁻¹).coord)
  have hP : P.IsWeightedHomogeneous w (n + 1) :=
    F.realSymbolGradeQuotientPolynomial_functional_homogeneous b ω hF w U
      (realifyFunctional ℓ) (n + 1) _
  refine ⟨aeval β P - aeval (fun i => homogeneousComponent (w i) (β i)) P,
    sampledTopPhase_remainder_totalDegree w β hβ hP, ?_⟩
  rw [F.scalarSymbolPolynomial_homogeneousComponent_homogeneousPullback]
  change aeval β P = aeval (fun i => homogeneousComponent (w i) (β i)) P +
    (aeval β P - aeval (fun i => homogeneousComponent (w i) (β i)) P)
  abel

theorem realSymbolGradeQuotientPolynomial_lowTagged_aeval {m : ℕ} {X : Type}
    (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℝ)
    (U : Submodule ℚ F.AssociatedGraded)
    (ℓ : (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)) →ₗ[ℝ] ℝ)
    (x : F.RealPolynomialSymbol (fullTaggedVariableWeight (X := X) J)) :
    aeval β (coordinate ℓ.toAddMonoidHom
      (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J) U k x)) =
    aeval (β ∘ lowTaggedVariableEmbedding J k) (coordinate ℓ.toAddMonoidHom
      (lowTaggedVectorRestrict J k
        (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J) U k x))) := by
  let P := F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J) U k x
  have hP : DegreeLE (fullTaggedVariableWeight J) k P := by
    intro α hα
    exact F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF
      (fullTaggedVariableWeight J) U k x α (Nat.ne_of_gt hα)
  have hc := congrArg (coordinate ℓ.toAddMonoidHom) (lowTaggedVectorExtend_restrict J k P hP)
  rw [coordinate_lowTaggedVectorExtend] at hc
  change aeval β (coordinate ℓ.toAddMonoidHom P) = _
  rw [← hc, MvPolynomial.aeval_rename]

theorem exists_sampledCurrentGrade_lowTagged_lower_phase {m : ℕ} {X η : Type}
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (fullTaggedVariableWeight J i))
    (U : Submodule ℚ F.AssociatedGraded)
    (eQ : Basis η ℚ (F.AssociatedGraded ⧸ U)) (j : η)
    (n : ℕ) (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)) :
    let topβ := fun i => homogeneousComponent (fullTaggedVariableWeight J i) (β i)
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
      (fun _ : τ => 1) topβ
      (fun i => sampledTopPhase_coordinate_homogeneous (fullTaggedVariableWeight J i) (β i))
    ∃ lower : MvPolynomial τ ℝ, lower.totalDegree ≤ n ∧
      aeval (β ∘ lowTaggedVariableEmbedding J (n + 1))
        (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
          (lowTaggedVectorRestrict J (n + 1) (F.realSymbolGradeQuotientPolynomial b ω hF
            (fullTaggedVariableWeight J) U (n + 1) (left⁻¹ * Z * right⁻¹).coord))) =
      homogeneousComponent (n + 1)
        (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1) ((eQ.coord j).comp U.mkQ)
          ((pull left)⁻¹ * pull Z * (pull right)⁻¹)) + lower := by
  obtain ⟨lower, hdegree, hphase⟩ := F.exists_sampledCurrentGrade_lower_phase b ω hF
    (fullTaggedVariableWeight J) β hβ U (eQ.coord j) n Z left right
  refine ⟨lower, hdegree, ?_⟩
  rw [sampledCurrentGrade_sampledCurrentGrade_realifyFunctional_basis_coord,
    F.realSymbolGradeQuotientPolynomial_lowTagged_aeval b ω hF J (n + 1)] at hphase
  with_reducible exact hphase

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def majorPhasePlateauKernel (d : ℕ) : PatchKernel d where
  value x := linearCutoff (1 / 8) (1 / 8) ‖x‖
  nonneg x := (linearCutoff_range _ _ _).1
  le_one x := (linearCutoff_range _ _ _).2
  support x hx i := by
    have hnorm : ‖x‖ < (1 / 4 : ℝ) := by
      by_contra h
      apply hx
      apply linearCutoff_eq_zero
      norm_num at h ⊢
      exact h
    have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    exact hi.trans hnorm.le
  lip := 8
  lipschitz := by
    have h := (linearCutoff_lipschitz (1 / 8) (1 / 8) (by norm_num)).comp
      (lipschitzWith_one_norm : LipschitzWith 1 (fun x : Fin d → ℝ => ‖x‖))
    simpa only [Function.comp_def, one_div, inv_inv, mul_one] using h

@[simp] theorem majorPhasePlateauKernel_lip (d : ℕ) :
    (majorPhasePlateauKernel d).lip = 8 := rfl

theorem majorPhasePlateauKernel_one {d : ℕ} (x : Fin d → ℝ)
    (hx : ∀ i, |x i| ≤ 1 / 8) : (majorPhasePlateauKernel d).value x = 1 := by
  apply linearCutoff_eq_one _ _ (by norm_num)
  exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (by
    simpa only [Real.norm_eq_abs] using hx)

namespace VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} {X : Type} (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)

noncomputable def majorPhaseNearestLift (u : X → ℤ) :
    Fin (Fintype.card (LowTaggedIndex J k)) → ℤ :=
  nearestIntegerLift (fun i => MvPolynomial.eval (fun x => (u x : ℝ))
    (lowTaggedPolynomial J k poly i) - c i)

theorem majorPhaseNearestLift_close (u : X → ℤ)
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) - c i -
      (majorPhaseNearestLift J k poly c u i : ℝ)| ≤ 1 / 2 :=
  by
    unfold majorPhaseNearestLift
    exact nearestIntegerLift_close
      (fun j => MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly j) - c j) i

noncomputable def majorPhasePlateauSignal
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ) (u : X → ℤ) : ℂ :=
  majorPhaseSample J k poly (majorPhasePlateauKernel _) c P
    (majorPhaseNearestLift J k poly c) (fun _ => 1) u

theorem majorPhasePlateauSignal_norm_le_one
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ) (u : X → ℤ) :
    ‖majorPhasePlateauSignal J k poly c P u‖ ≤ 1 := by
  unfold majorPhasePlateauSignal majorPhaseSample
  rw [mul_one, norm_mul]
  simp only [Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg ((majorPhasePlateauKernel _).nonneg _)]
  exact (majorPhasePlateauKernel _).le_one _

theorem majorPhaseNearestLift_eq_of_close
    (u : X → ℤ) (b : Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
    (hb : ∀ i, |MvPolynomial.eval (fun x => (u x : ℝ))
      (lowTaggedPolynomial J k poly i) - c i - (b i : ℝ)| ≤ 1 / 8) :
    majorPhaseNearestLift J k poly c u = b := by
  apply Eq.symm
  apply (majorPhasePlateauKernel _).buffered_lift_unique
    (fun i => MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) - c i)
    (majorPhaseNearestLift J k poly c u) b
    (majorPhaseNearestLift_close J k poly c u)
  rw [majorPhasePlateauKernel_one _ hb]
  norm_num

theorem majorPhasePlateauSignal_eq_phase
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (u : X → ℤ) (b : Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
    (hb : ∀ i, |MvPolynomial.eval (fun x => (u x : ℝ))
      (lowTaggedPolynomial J k poly i) - c i - (b i : ℝ)| ≤ 1 / 8) :
    majorPhasePlateauSignal J k poly c P u =
      (Real.fourierChar (MvPolynomial.eval (fun i => ((Sum.elim u b i : ℤ) : ℝ)) P) : ℂ) := by
  unfold majorPhasePlateauSignal majorPhaseSample
  rw [majorPhaseNearestLift_eq_of_close J k poly c u b hb]
  rw [majorPhasePlateauKernel_one _ hb]
  simp only [Complex.ofReal_one, one_mul, mul_one]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

noncomputable def integerSampledRealChart {σ τ : Type*}
    (β : σ → MvPolynomial τ ℤ) : σ → MvPolynomial τ ℝ :=
  fun i => MvPolynomial.map (Int.castRingHom ℝ) (β i)

theorem integerSampledRealChart_eval {σ τ : Type*}
    (β : σ → MvPolynomial τ ℤ) (u : τ → ℤ) (i : σ) :
    MvPolynomial.eval (fun x => (u x : ℝ)) (integerSampledRealChart β i) =
      (MvPolynomial.eval u (β i) : ℝ) :=
  (MvPolynomial.map_eval (Int.castRingHom ℝ) u (β i)).symm

noncomputable def integerSampledSpatial {m : ℕ} {X τ : Type*} {J : Fin m → Type*}
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℤ) (u : τ → ℤ) : X → ℤ :=
  fun x => MvPolynomial.eval u (β (Sum.inl x))

noncomputable def integerSampledLowTags {m : ℕ} {X τ : Type*}
    (J : Fin m → Type*) [∀ j, Fintype (J j)] (k : ℕ)
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℤ) (u : τ → ℤ) :
    Fin (Fintype.card (LowTaggedIndex J k)) → ℤ :=
  fun i => MvPolynomial.eval u (β (Sum.inr (lowTaggedIndex J k i)))

theorem majorPhasePlateauSignal_integerChart_eq {m : ℕ} {X : Type} {τ : Type*}
    (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℤ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (u : τ → ℤ)
    (hb : ∀ i, |MvPolynomial.eval (fun x => (integerSampledSpatial β u x : ℝ))
      (lowTaggedPolynomial J k poly i) - c i - (integerSampledLowTags J k β u i : ℝ)| ≤ 1 / 8) :
    majorPhasePlateauSignal J k poly c P (integerSampledSpatial β u) =
      (Real.fourierChar (MvPolynomial.eval (fun x => (u x : ℝ))
        (aeval (integerSampledRealChart β ∘ lowTaggedVariableEmbedding J k) P)) : ℂ) := by
  rw [majorPhasePlateauSignal_eq_phase J k poly c P
    (integerSampledSpatial β u) (integerSampledLowTags J k β u) hb]
  have he : MvPolynomial.eval (fun x => (u x : ℝ))
      (aeval (integerSampledRealChart β ∘ lowTaggedVariableEmbedding J k) P) =
      MvPolynomial.eval
        (fun i => ((Sum.elim (integerSampledSpatial β u) (integerSampledLowTags J k β u) i : ℤ) : ℝ)) P := by
    calc
      _ = MvPolynomial.eval (fun i => MvPolynomial.eval (fun x => (u x : ℝ))
          (integerSampledRealChart β (lowTaggedVariableEmbedding J k i))) P :=
        MvPolynomial.comp_aeval_apply _ (MvPolynomial.aeval (fun x => (u x : ℝ))) P
      _ = _ := by
        apply congrArg (fun z => MvPolynomial.eval z P)
        funext i
        rw [integerSampledRealChart_eval]
        cases i <;> rfl
  rw [he]

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

theorem exists_bufferedSampledCurrentGrade_phase
    {m : ℕ} {X η : Type} {τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℤ)
    (hβ : ∀ i, integerSampledRealChart β i ∈
      weightedSupportLE (fun _ : τ => 1) (fullTaggedVariableWeight J i))
    (U : Submodule ℚ F.AssociatedGraded)
    (eQ : Basis η ℚ (F.AssociatedGraded ⧸ U)) (j : η)
    (n : ℕ) (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J (n + 1))) → ℝ) :
    let topβ := fun i => homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i)
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
      (fun _ : τ => 1) topβ
      (fun i => sampledTopPhase_coordinate_homogeneous (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
    ∃ lower : MvPolynomial τ ℝ, lower.totalDegree ≤ n ∧
      ∀ u : τ → ℤ,
      (∀ i, |MvPolynomial.eval (fun x => (integerSampledSpatial β u x : ℝ))
        (lowTaggedPolynomial J (n + 1) poly i) - c i -
        (integerSampledLowTags J (n + 1) β u i : ℝ)| ≤ 1 / 8) →
      majorPhasePlateauSignal J (n + 1) poly c
        (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
          (lowTaggedVectorRestrict J (n + 1) (F.realSymbolGradeQuotientPolynomial b ω hF
            (fullTaggedVariableWeight J) U (n + 1) (left⁻¹ * Z * right⁻¹).coord)))
        (integerSampledSpatial β u) =
      (Real.fourierChar (MvPolynomial.eval (fun x => (u x : ℝ))
        (homogeneousComponent (n + 1)
          (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1) ((eQ.coord j).comp U.mkQ)
            ((pull left)⁻¹ * pull Z * (pull right)⁻¹)) + lower)) : ℂ) := by
  obtain ⟨lower, hdegree, hphase⟩ := F.exists_sampledCurrentGrade_lowTagged_lower_phase
    b ω hF J (integerSampledRealChart β) hβ U eQ j n Z left right
  refine ⟨lower, hdegree, ?_⟩
  intro u hb
  rw [majorPhasePlateauSignal_integerChart_eq J (n + 1) poly c β _ u hb, hphase]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeIntegerChartNiltest
namespace OAI

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute polynomialOrbitRealChart weightedAdaptedRealChartHom realPolynomialSymbolHom

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (Q : D.Niltest w) (v : τ → ℕ) (β : σ → MvPolynomial τ ℤ)
  (hβ : ∀ i, integerSampledRealChart β i ∈ weightedSupportLE v (w i))

noncomputable def integerChartPullback : D.Niltest v :=
  Q.withOrbit (D.filtration.polynomialOrbitRealChart w v (integerSampledRealChart β) hβ Q.orbit)

@[simp] theorem integerChartPullback_orbit :
    (Q.integerChartPullback v β hβ).orbit =
      D.filtration.polynomialOrbitRealChart w v (integerSampledRealChart β) hβ Q.orbit := rfl

@[simp] theorem integerChartPullback_observable :
    (Q.integerChartPullback v β hβ).observable = Q.observable := rfl

@[simp] theorem integerChartPullback_normBound :
    (Q.integerChartPullback v β hβ).normBound = Q.normBound := rfl

@[simp] theorem integerChartPullback_lipBound :
    (Q.integerChartPullback v β hβ).lipBound = Q.lipBound := rfl

@[simp] theorem integerChartPullback_complexity (p : ℝ) :
    (Q.integerChartPullback v β hβ).ComplexityLE p ↔ Q.ComplexityLE p := Iff.rfl

@[simp] theorem integerChartPullback_unitIntervalValued :
    (Q.integerChartPullback v β hβ).UnitIntervalValued ↔ Q.UnitIntervalValued := Iff.rfl

@[simp] theorem integerChartPullback_eval (t : τ → ℤ) :
    (Q.integerChartPullback v β hβ).eval t =
      Q.eval (fun i => MvPolynomial.eval t (β i)) := by
  change Q.observable (QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval v t
      (D.filtration.polynomialOrbitRealChart w v (integerSampledRealChart β) hβ Q.orbit))) = _
  rw [← D.filtration.realification.polynomialOrbitRealEval_integer,
    D.filtration.polynomialOrbitRealChart_realEval]
  simp only [integerSampledRealChart_eval]
  rw [D.filtration.realification.polynomialOrbitRealEval_integer]
  rfl

theorem integerChartPullback_orbit_eq_of_orbit_eq (R : D.Niltest w)
    (hQR : Q.orbit = R.orbit) :
    (Q.integerChartPullback v β hβ).orbit = (R.integerChartPullback v β hβ).orbit := by
  simp only [integerChartPullback_orbit, hQR]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationPaddedFreezingLifts
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {X J : Type} {m q : ℕ} (L : RankPreparationFamily X J m)

@[simp] theorem pad_polynomial [DecidableEq J] (hmq : m ≤ q) :
    (L.pad q).polynomial = L.polynomial := by
  apply L.pad_sum hmq (fun layer => map (coordinateCopySum layer.label) layer.poly)
  change map (coordinateCopySum (R := ℝ) (PEmpty.elim : PEmpty → J))
    (0 : VectorPolynomial X ℝ (PEmpty → ℝ)) = 0
  exact map_zero _

noncomputable def padCoordInclusion (hmq : m ≤ q) :
    (Σ j, (L j).Coord) → Σ j, (L.pad q j).Coord := fun a =>
  ⟨a.1.castLE hmq, cast (congrArg RankPreparationLayer.Coord
    (L.pad_apply_castLE hmq a.1).symm) a.2⟩

theorem padCoord_isLt (a : Σ j, (L.pad q j).Coord) : a.1.val < m := by
  rcases a with ⟨j, i⟩
  by_cases hj : j.val < m
  · exact hj
  · exact PEmpty.elim (cast (congrArg RankPreparationLayer.Coord
      (L.pad_apply_ge j (by omega))) i)

noncomputable def padCoordRestriction (a : Σ j, (L.pad q j).Coord) :
    Σ j, (L j).Coord :=
  ⟨⟨a.1.val, L.padCoord_isLt a⟩, cast (congrArg RankPreparationLayer.Coord
    (L.pad_apply_lt a.1 (L.padCoord_isLt a))) a.2⟩

@[simp] theorem padCoordRestriction_inclusion (hmq : m ≤ q)
    (a : Σ j, (L j).Coord) :
    L.padCoordRestriction (L.padCoordInclusion hmq a) = a := by
  rcases a with ⟨j, i⟩
  dsimp only [padCoordInclusion, padCoordRestriction]
  apply Sigma.ext
  · exact Fin.ext rfl
  exact (cast_heq _ _).trans (cast_heq _ _)

@[simp] theorem padCoordInclusion_restriction (hmq : m ≤ q)
    (a : Σ j, (L.pad q j).Coord) :
    L.padCoordInclusion hmq (L.padCoordRestriction a) = a := by
  rcases a with ⟨j, i⟩
  dsimp only [padCoordInclusion, padCoordRestriction]
  apply Sigma.ext
  · exact Fin.ext rfl
  exact (cast_heq _ _).trans (cast_heq _ _)

noncomputable def padCoordEquiv (hmq : m ≤ q) :
    (Σ j, (L.pad q j).Coord) ≃ Σ j, (L j).Coord where
  toFun := L.padCoordRestriction
  invFun := L.padCoordInclusion hmq
  left_inv := L.padCoordInclusion_restriction hmq
  right_inv := L.padCoordRestriction_inclusion hmq

theorem label_cast {A B : RankPreparationLayer X J} (h : A = B)
    (i : A.Coord) : B.label (cast (congrArg RankPreparationLayer.Coord h) i) = A.label i := by
  cases h
  rfl

theorem eval_cast {A B : RankPreparationLayer X J} (h : A = B)
    (x : X → ℝ) (i : A.Coord) :
    eval x B.poly (cast (congrArg RankPreparationLayer.Coord h) i) = eval x A.poly i := by
  cases h
  rfl

theorem coefficients_cast {A B : RankPreparationLayer X J} (h : A = B)
    (α : X →₀ ℕ) (i : A.Coord) :
    coefficients B.poly α (cast (congrArg RankPreparationLayer.Coord h) i) =
      coefficients A.poly α i := by
  cases h
  rfl

@[simp] theorem padCoordInclusion_label (hmq : m ≤ q) (a : Σ j, (L j).Coord) :
    (L.pad q (L.padCoordInclusion hmq a).1).label (L.padCoordInclusion hmq a).2 =
      (L a.1).label a.2 :=
  label_cast (L.pad_apply_castLE hmq a.1).symm a.2

@[simp] theorem padCoordEquiv_index (hmq : m ≤ q) (a : Σ j, (L.pad q j).Coord) :
    ((L.padCoordEquiv hmq a).1 : ℕ) = a.1.val := rfl

@[simp] theorem padCoordEquiv_label (hmq : m ≤ q) (a : Σ j, (L.pad q j).Coord) :
    (L (L.padCoordEquiv hmq a).1).label (L.padCoordEquiv hmq a).2 =
      (L.pad q a.1).label a.2 := by
  have h := L.padCoordInclusion_label hmq (L.padCoordRestriction a)
  rw [L.padCoordInclusion_restriction hmq a] at h
  exact h.symm

@[simp] theorem padCoordInclusion_eval (hmq : m ≤ q) (x : X → ℝ)
    (a : Σ j, (L j).Coord) :
    eval x (L.pad q (L.padCoordInclusion hmq a).1).poly (L.padCoordInclusion hmq a).2 =
      eval x (L a.1).poly a.2 :=
  eval_cast (L.pad_apply_castLE hmq a.1).symm x a.2

@[simp] theorem padCoordEquiv_eval (hmq : m ≤ q) (x : X → ℝ)
    (a : Σ j, (L.pad q j).Coord) :
    eval x (L (L.padCoordEquiv hmq a).1).poly (L.padCoordEquiv hmq a).2 =
      eval x (L.pad q a.1).poly a.2 := by
  have h := L.padCoordInclusion_eval hmq x (L.padCoordRestriction a)
  rw [L.padCoordInclusion_restriction hmq a] at h
  exact h.symm

@[simp] theorem padCoordInclusion_coefficients (hmq : m ≤ q) (α : X →₀ ℕ)
    (a : Σ j, (L j).Coord) :
    coefficients (L.pad q (L.padCoordInclusion hmq a).1).poly α
        (L.padCoordInclusion hmq a).2 = coefficients (L a.1).poly α a.2 :=
  coefficients_cast (L.pad_apply_castLE hmq a.1).symm α a.2

@[simp] theorem padCoordEquiv_coefficients (hmq : m ≤ q) (α : X →₀ ℕ)
    (a : Σ j, (L.pad q j).Coord) :
    coefficients (L (L.padCoordEquiv hmq a).1).poly α (L.padCoordEquiv hmq a).2 =
      coefficients (L.pad q a.1).poly α a.2 := by
  have h := L.padCoordInclusion_coefficients hmq α (L.padCoordRestriction a)
  rw [L.padCoordInclusion_restriction hmq a] at h
  exact h.symm

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial

variable {X J : Type} {m q : ℕ} (L : RankPreparationFamily X J m)

noncomputable def unpadCenter (hmq : m ≤ q)
    (c : ∀ j, (L.pad q j).Coord → ℝ) : ∀ j, (L j).Coord → ℝ := fun j i =>
  c ((L.padCoordEquiv hmq).symm ⟨j, i⟩).1 ((L.padCoordEquiv hmq).symm ⟨j, i⟩).2

@[simp] theorem unpadCenter_equiv (hmq : m ≤ q)
    (c : ∀ j, (L.pad q j).Coord → ℝ) (a : Σ j, (L.pad q j).Coord) :
    L.unpadCenter hmq c (L.padCoordEquiv hmq a).1 (L.padCoordEquiv hmq a).2 =
      c a.1 a.2 := by
  exact congrArg (fun b : Σ j, (L.pad q j).Coord => c b.1 b.2)
    ((L.padCoordEquiv hmq).symm_apply_apply a)

noncomputable def padFullTaggedEquiv (hmq : m ≤ q) :
    (X ⊕ (Σ j, (L.pad q j).Coord)) ≃ (X ⊕ (Σ j, (L j).Coord)) :=
  (Equiv.refl X).sumCongr (L.padCoordEquiv hmq)

@[simp] theorem padFullTaggedEquiv_weight (hmq : m ≤ q)
    (a : X ⊕ (Σ j, (L.pad q j).Coord)) :
    fullTaggedVariableWeight (fun j => (L j).Coord) (L.padFullTaggedEquiv hmq a) =
      fullTaggedVariableWeight (fun j => (L.pad q j).Coord) a := by
  cases a with
  | inl x => rfl
  | inr a =>
    change (L.padCoordEquiv hmq a).1.val + 1 = a.1.val + 1
    rw [L.padCoordEquiv_index]

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

variable {X J : Type} {Vars : Type*} {m q : ℕ}
    (L : RankPreparationFamily X J m)

noncomputable def unpadFreezingLifts (hmq : m ≤ q)
    (β : ∀ j, (L.pad q j).Coord → MvPolynomial Vars ℤ) :
    ∀ j, (L j).Coord → MvPolynomial Vars ℤ := fun j i =>
  β (L.padCoordInclusion hmq ⟨j, i⟩).1 (L.padCoordInclusion hmq ⟨j, i⟩).2

end Erdos3.RankPreparationFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchTaggedBufferedScore
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial
variable {σ τ : Type*} {s d : ℕ}

theorem symbolicShearPrefixSubstitution_weighted_degree (p : τ → ℕ) (w : Fin d → ℕ) (i : Fin d)
    (v : τ ⊕ Fin d) :
    symbolicShearPrefixSubstitution i v ∈
      weightedSupportLE (weightedPatchVariableWeight p w i) (Sum.elim p w v) := by
  classical
  cases v with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
      dsimp only [symbolicShearPrefixSubstitution, Sum.elim_inr]
      split_ifs with h
      · have hj : earlierSlot i ⟨j.val, h⟩ = j := Fin.ext rfl
        have hx := weightedSupportLE_X (R := ℝ)
          (weightedPatchVariableWeight p w i) (Sum.inr ⟨j.val, h⟩)
        change _ ∈ weightedSupportLE _ (w (earlierSlot i ⟨j.val, h⟩)) at hx
        rw [hj] at hx
        exact hx
      · exact Submodule.zero_mem _

namespace PolynomialPatch
variable (A : PolynomialPatch σ s d) (p : τ → ℕ)
  (f : MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ)

variable
  (hdegree : ∀ {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ},
    P ∈ weightedSupportLE (Sum.elim p A.weight) n →
    f P ∈ weightedSupportLE (Sum.elim p A.weight) n)

include hdegree in
theorem weightedSymbolicShearFullCenter_degree (i : Fin d) :
    A.symbolicShearFullCenter f i ∈
      weightedSupportLE (Sum.elim p A.weight) (A.weight i) := by
  apply (weightedSupportLE _ _).sub_mem (weightedSupportLE_X _ (Sum.inr i))
  apply hdegree
  apply polynomialHom_preserves_weightedDegree A.weight _ (rename Sum.inr) _
    (A.form.topResidualEquiv_degree (weightedSupportLE_X A.weight i))
  intro j
  rw [rename_X]
  exact weightedSupportLE_X _ (Sum.inr j)

noncomputable def weightedSymbolicShearForm : WeightedParameterSlots τ p d A.weight where
  center i := aeval (symbolicShearPrefixSubstitution i) (A.symbolicShearFullCenter f i)
  degree i := weightedSupportLE_aeval _ _ _
    (symbolicShearPrefixSubstitution_weighted_degree p A.weight i)
    (A.weightedSymbolicShearFullCenter_degree p f hdegree i)

noncomputable def weightedSymbolicShearPatch : WeightedParameterPatch τ p s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := A.weightedSymbolicShearForm p f hdegree
  kernel := A.kernel

variable (e : (τ → ℝ) → WeightedLoweringAut A.weight ℝ)
  (hspecialize : ∀ t P, patchParameterSpecialization t (f P) =
    (e t).val (patchParameterSpecialization t P))

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {τ : Type*} (p : τ → ℕ) {d s : ℕ} {w : Fin d → ℕ}
variable [Fintype (PolynomialShearIndex w)]

noncomputable def weightedPolynomialShearOrbitSymbolicHom (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit p) :
    MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ :=
  polynomialShearExpHom (polynomialSymbolicShearDerivation w
    (weightedPolynomialShearOrbitParameterCoordinates s hw p g))

theorem weightedPolynomialShearOrbitSymbolicHom_degree (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit p)
    {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim p w) n) :
    weightedPolynomialShearOrbitSymbolicHom p hw g P ∈
      weightedSupportLE (Sum.elim p w) n :=
  polynomialSymbolicShearExp_weighted_degree p w _
    (weightedPolynomialShearOrbitParameterCoordinates_degree s hw p g) hP

namespace PolynomialPatch
variable {σ : Type*} (A : PolynomialPatch σ s d)

noncomputable def ofWeightedShearOrbit
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      p) : WeightedParameterPatch τ p s d := by
  letI := polynomialShearIndexFintype A.weight (fun i => A.weight_pos i)
  exact A.weightedSymbolicShearPatch p (weightedPolynomialShearOrbitSymbolicHom p A.weight_le g⁻¹)
    (weightedPolynomialShearOrbitSymbolicHom_degree p A.weight_le g⁻¹)

@[simp] theorem ofWeightedShearOrbit_weight
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      p) : (A.ofWeightedShearOrbit p g).weight = A.weight := rfl

@[simp] theorem ofWeightedShearOrbit_kernel
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      p) : (A.ofWeightedShearOrbit p g).kernel = A.kernel := rfl

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open VectorPolynomial

variable {X : Type*} {m n : ℕ} {J : Fin m → Type*}

noncomputable def taggedShearOrbitReindexChart (e : Fin n ≃ Sigma J) :
    X ⊕ Sigma J → MvPolynomial (X ⊕ Fin n) ℝ :=
  fun v => MvPolynomial.X (Sum.map id e.symm v)

theorem taggedShearOrbitReindexChart_degree (e : Fin n ≃ Sigma J)
    (v : X ⊕ Sigma J) :
    taggedShearOrbitReindexChart e v ∈
      weightedSupportLE (Sum.elim (fun _ : X => 1) (fun i => (e i).1.val + 1))
        (fullTaggedVariableWeight J v) := by
  have h := weightedSupportLE_X (R := ℝ)
    (Sum.elim (fun _ : X => 1) (fun i => (e i).1.val + 1)) (Sum.map id e.symm v)
  cases v with
  | inl x => exact h
  | inr a => simpa only [taggedShearOrbitReindexChart, Sum.map_inr, Sum.elim_inr,
      Equiv.apply_symm_apply] using h

namespace PolynomialPatch
variable {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)

noncomputable def ofTaggedWeightedShearOrbit (e : Fin n ≃ Sigma J)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    WeightedParameterPatch (X ⊕ Fin n)
      (Sum.elim (fun _ => 1) (fun i => (e i).1.val + 1)) s d :=
  A.ofWeightedShearOrbit (Sum.elim (fun _ => 1) (fun i => (e i).1.val + 1))
    ((polynomialShearFiltration A.weight s A.weight_le).polynomialOrbitRealChart
      (fullTaggedVariableWeight J)
      (Sum.elim (fun _ => 1) (fun i => (e i).1.val + 1))
      (taggedShearOrbitReindexChart e) (taggedShearOrbitReindexChart_degree e) g)

@[simp] theorem ofTaggedWeightedShearOrbit_weight (e : Fin n ≃ Sigma J)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    (A.ofTaggedWeightedShearOrbit e g).weight = A.weight := rfl

@[simp] theorem ofTaggedWeightedShearOrbit_kernel (e : Fin n ≃ Sigma J)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    (A.ofTaggedWeightedShearOrbit e g).kernel = A.kernel := rfl

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open VectorPolynomial

variable {σ X : Type*} {s d m n : ℕ} {J : Fin m → Type*}
    (A : PolynomialPatch σ s d) (e : Fin n ≃ Σ j, J j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

end Erdos3.PolynomialPatch

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FullTaggedRationalChartGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical Matrix

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedLinearMapChart_coefficientGrid
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (D : ℕ)
    (hP : ∀ j i a, ∃ z : ℤ, (D : ℝ) * P j (Pi.single a 1) i = (z : ℝ))
    (v : X ⊕ (Σ j, J j)) :
    realPolynomialCoefficientGrid D (fullTaggedLinearMapChart J P v) := by
  cases v with
  | inl x => exact realPolynomialCoefficientGrid_X D _
  | inr v =>
    apply (realPolynomialCoefficientGrid_iff D _).mpr
    change C (D : ℝ) * (∑ a : J v.1, P v.1 (Pi.single a 1) v.2 •
      MvPolynomial.X (Sum.inr ⟨v.1, a⟩ : X ⊕ (Σ j, J j))) ∈
        integralRealPolynomialSubring (X ⊕ (Σ j, J j))
    simp only [smul_eq_C_mul, Finset.mul_sum]
    apply (integralRealPolynomialSubring _).sum_mem
    intro a _
    obtain ⟨z, hz⟩ := hP v.1 v.2 a
    rw [← mul_assoc, ← map_mul, hz]
    exact (integralRealPolynomialSubring _).mul_mem
      (C_int_mem_integralRealPolynomialSubring z) (X_mem_integralRealPolynomialSubring _)

end Erdos3.VectorPolynomial

end

end OAI

end


