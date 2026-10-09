-- Prove2me | Definitions.Def_OAIErdos3B033
-- name    : OAIErdos3B033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T23:33:15.880732+00:00
-- url     : https://prove2.me/theorems/9f2b3425-1c0e-41d7-b4d1-176c379df9f6
-- title:
--   OpenAI Erdős-3 split, definitions bundle 34 of 131
-- statement:
--   Definitions bundle 34 of 131 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B032`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 34 available.
--
--   Modules: `OAI.Erdos3.AuxiliaryBoxLabels`, `OAI.Erdos3.DegreeRankLieFiltration.projectedHorizontalSymbolCoefficient_mem`, `OAI.Erdos3.DegreeRankLieFiltration.projectedHorizontal_factorization`, `OAI.Erdos3.DegreeRankLieFiltration.real_projectedHorizontalSymbolCoefficient_mem`, `OAI.Erdos3.FreimanModel.coordinatePolynomial`, `OAI.Erdos3.FreimanModel.coordinatePolynomial_coeff`, `OAI.Erdos3.FreimanModel.coordinatePolynomial_injective`, `OAI.Erdos3.FreimanModel.exists_fin_integer_embedding`, `OAI.Erdos3.FreimanModel.exists_integer_freiman_embedding`, `OAI.Erdos3.FreimanModel.exists_integer_vector_embedding`, `OAI.Erdos3.FreimanModel.isAddFreimanIso_of_injOn_iterated_sums`, `OAI.Erdos3.FreimanModel.multiset_sum_mem_iterated_sumset`, `OAI.Erdos3.LayerResetScales.recOn`, `OAI.Erdos3.LeadingWeylBound`, `OAI.Erdos3.NilpotentLieFiltration.CompatibleReducedFastResetSpec`, `OAI.Erdos3.NilpotentLieFiltration.ControlledReducedFastResetSpec`, `OAI.Erdos3.NilpotentLieFiltration.ControlledSymbolCompositionSpec`, `OAI.Erdos3.NilpotentLieFiltration.ControlledSymbolFactorization`, `OAI.Erdos3.NilpotentLieFiltration.ControlledSymbolFactorization.exists_fastWitness`, `OAI.Erdos3.NilpotentLieFiltration.ControlledSymbolFactorization.exists_in`, `OAI.Erdos3.NilpotentLieFiltration.ControlledSymbolFactorization.mono`, `OAI.Erdos3.NilpotentLieFiltration.ControlledSymbolFactorization.rescale`, `OAI.Erdos3.NilpotentLieFiltration.ControlledSymbolFactorizationAtFast`, `OAI.Erdos3.NilpotentLieFiltration.ReducedFastResetSpec`, `OAI.Erdos3.NilpotentLieFiltration.SymbolFactorizationIn`, `OAI.Erdos3.NilpotentLieFiltration.SymbolFactorizationIn.exists_fast_factors`, `OAI.Erdos3.NilpotentLieFiltration.SymbolFactorizationIn.mono`, `OAI.Erdos3.NilpotentLieFiltration.SymbolFastIn`, `OAI.Erdos3.NilpotentLieFiltration.adaptedWeightedDilation_coe`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedBasis_reindex`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedMap_basis_repr`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedMap_gradeProjection`, `OAI.Erdos3.NilpotentLieFiltration.basisGradeProjection_top`, `OAI.Erdos3.NilpotentLieFiltration.exists_common_polynomial_step_drop_factors`, `OAI.Erdos3.NilpotentLieFiltration.exists_compatible_reduced_fast_reset`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_reduced_fast_reset`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_symbol_composition`, `OAI.Erdos3.NilpotentLieFiltration.exists_pointwise_polynomial_symbol_splitting`, `OAI.Erdos3.NilpotentLieFiltration.exists_realPolynomial_controlled_symbol_factorization`, `OAI.Erdos3.NilpotentLieFiltration.exists_realPolynomial_symbol_factorization`, `OAI.Erdos3.NilpotentLieFiltration.exists_reduced_fast_reset`, `OAI.Erdos3.NilpotentLieFiltration.exists_refiltered_polynomial_of_coefficients`, `OAI.Erdos3.NilpotentLieFiltration.exists_simultaneous_polynomial_symbol_splitting`, `OAI.Erdos3.NilpotentLieFiltration.gradedFrequency`, `OAI.Erdos3.NilpotentLieFiltration.gradedFrequency_comap_top_zero`, `OAI.Erdos3.NilpotentLieFiltration.gradedFrequency_projection`, `OAI.Erdos3.NilpotentLieFiltration.gradedFrequency_reindex`, `OAI.Erdos3.NilpotentLieFiltration.gradedFrequency_top_natural`, `OAI.Erdos3.NilpotentLieFiltration.gradedFrequency_top_piece`, `OAI.Erdos3.NilpotentLieFiltration.gradedPolynomialSymbol`, `OAI.Erdos3.NilpotentLieFiltration.gradedPolynomialSymbol_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.gradedPolynomialSymbol_gradedSymbolPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.gradedSymbolPolynomial_coefficient_symbol`, `OAI.Erdos3.NilpotentLieFiltration.gradedSymbolPolynomial_filteredMap`, `OAI.Erdos3.NilpotentLieFiltration.gradedSymbolPolynomial_filteredMap_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.gradedSymbolPolynomial_homogeneousSymbolLift`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousAssociatedGradedEquiv_pieceMap`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousAssociatedGradedEquiv_top_piece`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousGradedProjection`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousGradedProjection_basis_repr`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousGradedProjection_coordinate_ceil_height`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousGradedProjection_coordinate_logHeight`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousGradedProjection_gradeProjection`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousGradedProjection_image_graded`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousGradedProjection_repr`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousGradedProjection_span`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousGradedProjection_top_frequency`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousGradedProjection_top_frequency_zero`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousSymbolLift`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousSymbolLift_apply`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousSymbolLift_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousSymbolLift_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousSymbolLift_filteredMap`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousSymbolLift_mem_pointwise`, `OAI.Erdos3.NilpotentLieFiltration.mem_realGradedRefiltrationLayer_iff`, `OAI.Erdos3.NilpotentLieFiltration.mem_realGradedRefiltrationSubalgebra`, `OAI.Erdos3.NilpotentLieFiltration.mem_realGradedRefiltration_layer`, `OAI.Erdos3.NilpotentLieFiltration.normalized_refiltration_coefficients_mem_first`, `OAI.Erdos3.NilpotentLieFiltration.ordinarySymbolBasisFintype`, `OAI.Erdos3.NilpotentLieFiltration.pointwiseFastSectionInput`, `OAI.Erdos3.NilpotentLieFiltration.pointwiseFastSectionInput_ge`, `OAI.Erdos3.NilpotentLieFiltration.pointwiseSymbolSpanningFamily`, `OAI.Erdos3.NilpotentLieFiltration.pointwiseSymbolSpanningFamily_height`, `OAI.Erdos3.NilpotentLieFiltration.pointwiseSymbolSpanningFamily_span`, `OAI.Erdos3.NilpotentLieFiltration.pointwiseSymbolSpanning_section_counts`, `OAI.Erdos3.NilpotentLieFiltration.pointwise_refiltered_values_mem`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolDilation_repr`, `OAI.Erdos3.NilpotentLieFiltration.realGradedRefiltration`, `OAI.Erdos3.NilpotentLieFiltration.realGradedRefiltrationLayer`, `OAI.Erdos3.NilpotentLieFiltration.realGradedRefiltrationLayer_antitone`, `OAI.Erdos3.NilpotentLieFiltration.realGradedRefiltrationLayer_le`, `OAI.Erdos3.NilpotentLieFiltration.realGradedRefiltrationLayer_lie_mem`, `OAI.Erdos3.NilpotentLieFiltration.realGradedRefiltrationLayer_terminal`, `OAI.Erdos3.NilpotentLieFiltration.realGradedRefiltrationSubalgebra`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_dilation_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolDilation`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolDilationHom`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolDilationHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolDilation_mul`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolDilation_one`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolDilation_repr`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolDilation_tmul`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolLift_log`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolDilation_mem_pointwise`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfPolynomial_affine`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfPolynomial_dilation`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfPolynomial_translate`, `OAI.Erdos3.NilpotentLieFiltration.real_symbol_values_iff_refiltration_coefficients`, `OAI.Erdos3.NilpotentLieFiltration.symbolBasisIndex_card_le_spanning_budget`, `OAI.Erdos3.NilpotentLieFiltration.symbolRationalGrid_dilation_ratio`, `OAI.Erdos3.NilpotentLieFiltration.symbolSlowBound_dilation_inverse_scale`, `OAI.Erdos3.NilpotentLieFiltration.symbolSlowBound_dilation_physical`, `OAI.Erdos3.NilpotentLieFiltration.symbolSlowBound_rescale`, `OAI.Erdos3.NilpotentLieFiltration.symbol_mem_pointwise_iff_refiltered_coefficients`, `OAI.Erdos3.PolynomialIntervalPowerBound`, `OAI.Erdos3.PolynomialPatch.coordinateEquiv`, `OAI.Erdos3.PolynomialPatch.coordinateEquiv_complexity`, `OAI.Erdos3.PolynomialPatch.coordinateEquiv_distinctWeights`, `OAI.Erdos3.PolynomialPatch.coordinateEquiv_kernel`, `OAI.Erdos3.PolynomialPatch.coordinateEquiv_weight`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationGradedProjection`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationGradedProjection_basis_base`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationGradedProjection_image_graded`, `OAI.Erdos3.RationalFilteredNilmanifold.frozenComplexNiltest`, `OAI.Erdos3.RationalFilteredNilmanifold.frozenComplexNiltest_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.frozenComplexNiltest_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.frozenComplexNiltest_top_invariant`, `OAI.Erdos3.RelativePatchFinInductionRule`, `OAI.Erdos3.ResidueBoxSlice.coordinateReturn`, `OAI.Erdos3.ResiduePairDimensionDrop`, `OAI.Erdos3.SlicedProductBlock.fourBoxPacking`, `OAI.Erdos3.SlicedProductBlock.fourBoxValue`, `OAI.Erdos3.SlicedProductBlock.packFour`, `OAI.Erdos3.SlicedProductBlock.packPair`, `OAI.Erdos3.affinePhaseRemainder`, `OAI.Erdos3.affineSelectedInjection`, `OAI.Erdos3.basisGradeProjection_reindex`, `OAI.Erdos3.basisGradedSubmodule_reindex_iff`, `OAI.Erdos3.boxAuxiliaryCell`, `OAI.Erdos3.boxAuxiliaryCellEquiv`, `OAI.Erdos3.canonicalSlicedPrincipalDensity`, `OAI.Erdos3.dependentPiProd`, `OAI.Erdos3.euclideanDerivativeLattice_shortSpan_projection`, `OAI.Erdos3.euclideanVerticalProjection`, `OAI.Erdos3.euclideanVerticalProjection_apply`, `OAI.Erdos3.euclideanVerticalProjection_norm_le`, `OAI.Erdos3.exists_controlled_kernel_split_equiv`, `OAI.Erdos3.exists_correlated_integer_residue_box`, `OAI.Erdos3.exists_correlated_residue_progression_box`, `OAI.Erdos3.exists_measurable_representative_zspan`, `OAI.Erdos3.exists_positive_lipschitz_reconstruction`, `OAI.Erdos3.exists_reduced_reset_budget`, `OAI.Erdos3.exists_submoduleQuotientSectionBasis_with_coordinates`, `OAI.Erdos3.fourBlockDecomposition`, `OAI.Erdos3.graded_image_frequency_zero`, `OAI.Erdos3.haarShiftDensity_image_law`, `OAI.Erdos3.haarShiftDensity_map_eq`, `OAI.Erdos3.intervalPolynomialPhase`, `OAI.Erdos3.jointAffineBooleanInjection`, `OAI.Erdos3.jointAffineBooleanSampler`, `OAI.Erdos3.jointBooleanSource`, `OAI.Erdos3.jointBooleanSource_probability`, `OAI.Erdos3.jointSlicedInjection`, `OAI.Erdos3.jointSlicedPrincipal`, `OAI.Erdos3.lattice_exists_measurable_representative`, `OAI.Erdos3.layerResetCellScale`, `OAI.Erdos3.layerResetCellScale_ge`, `OAI.Erdos3.layerResetCellScale_power`, `OAI.Erdos3.layerResetCellScale_sq`, `OAI.Erdos3.layerResetThreshold`, `OAI.Erdos3.layerResetThreshold_ge`, `OAI.Erdos3.layerResetThreshold_initial`, `OAI.Erdos3.layerResetThreshold_pos`, `OAI.Erdos3.layerResetThreshold_terminal`, `OAI.Erdos3.le_reducedResetParameter`, `OAI.Erdos3.monomialScale_const_mul`, `OAI.Erdos3.monomialScale_div_const`, `OAI.Erdos3.monomialScale_le_exp_mul`, `OAI.Erdos3.norm_positiveClip_le_one`, `OAI.Erdos3.polynomialExponentialSum`, `OAI.Erdos3.polynomialShiftDifference`, `OAI.Erdos3.positiveClip`, `OAI.Erdos3.positiveClip_eq_self`, `OAI.Erdos3.positiveClip_lipschitz`, `OAI.Erdos3.positiveClip_unit_interval`, `OAI.Erdos3.powerLayerResetScales`, `OAI.Erdos3.principalFourRemainderDensity`, `OAI.Erdos3.principalSliceBlock`, `OAI.Erdos3.principalSliceSingleton`, `OAI.Erdos3.principalSliceSlope`, `OAI.Erdos3.principalSliceValue`, `OAI.Erdos3.principalSumBoxSplit`, `OAI.Erdos3.realDensityMeasure_map_add_right`, `OAI.Erdos3.reducedResetParameter`, `OAI.Erdos3.reducedResetParameter_controls`, `OAI.Erdos3.reducedResetParameter_nonneg`, `OAI.Erdos3.reindexedSlicedPrincipalDensity`, `OAI.Erdos3.relativePatchComplexity_coordinateFiber`, `OAI.Erdos3.relativePatchDistinctWeights_castRank`, `OAI.Erdos3.relativePatchDistinctWeights_coordinateFiber`, `OAI.Erdos3.residuePairMean`, `OAI.Erdos3.residuePairMean_false`, `OAI.Erdos3.residuePairMean_true`, `OAI.Erdos3.residuePairStep`, `OAI.Erdos3.residuePairValue`, `OAI.Erdos3.sigmaAxisMeasure`, `OAI.Erdos3.sigmaAxisMeasure_probability`, `OAI.Erdos3.translationPhaseArgument_left_increment_point_bound`, `OAI.Erdos3.translationPhaseArgument_left_increment_point_mass_bound`, `OAI.Erdos3.translationPhaseCharacter_left_increment_point_bound`, `OAI.Erdos3.translationPhaseCharacter_left_increment_quarter_point_bound`, `OAI.Erdos3.translation_residual_unit_boxes_of_quarter`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B100

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {T G : Type*} [MeasurableSpace T] [AddCommGroup G]
  [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]

omit [MeasurableNeg G] in
theorem realDensityMeasure_map_add_right (μ : Measure G) [μ.IsAddLeftInvariant]
    (f : G → ℝ) (a : G) :
    (realDensityMeasure μ f).map (fun u => u + a) =
      realDensityMeasure μ (fun y => f (y - a)) := by
  have h := realDensityMeasure_map_equiv (MeasurableEquiv.addRight a) μ f
  simpa only [MeasurableEquiv.symm_addRight, MeasurableEquiv.coe_addRight,
    map_add_right_eq_self, sub_eq_add_neg] using h

theorem haarShiftDensity_image_law (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ]
    (ν : Measure T) [IsProbabilityMeasure ν]
    {z : T → G} {f : G → ℝ} (hz : Measurable z) (hf : Measurable f)
    (hfi : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1) :
    (ν.prod (realDensityMeasure μ f)).map (fun p => p.2 + z p.1) =
      realDensityMeasure μ (haarShiftDensity ν z f) := by
  let _ := realDensityMeasure_probability μ f hfi hf0 hmass
  apply densityMixture_image_law ν (realDensityMeasure μ f) μ _
    (measurable_snd.add (hz.comp measurable_fst)) (fun t y => f (y - z t))
  · exact hf.comp (measurable_snd.sub (hz.comp measurable_fst))
  · exact fun t => ⟨fun y => hf0 _, hfi.comp_sub_right (z t),
      (integral_sub_right_eq_self f (z t)).trans hmass⟩
  · exact fun t => realDensityMeasure_map_add_right μ f (z t)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

noncomputable def sigmaAxisMeasure (μ : ∀ d, Measure (I d → ℝ)) : Measure ((Σ d, I d) → ℝ) :=
  Measure.map (sigmaAxisCoordinates I).symm (Measure.pi μ)

instance sigmaAxisMeasure_probability (μ : ∀ d, Measure (I d → ℝ))
    [∀ d, IsProbabilityMeasure (μ d)] : IsProbabilityMeasure (sigmaAxisMeasure μ) := by
  unfold sigmaAxisMeasure
  exact Measure.isProbabilityMeasure_map (sigmaAxisCoordinates I).symm.continuous.measurable.aemeasurable

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointBooleanSource (h : D → ℕ) : Measure (JointBlockParameter B h α → ℝ) :=
  sigmaAxisMeasure (fun d => blockCubeMeasure (B d) (Fin (h d)) α)

instance jointBooleanSource_probability (h : D → ℕ) :
    IsProbabilityMeasure (jointBooleanSource (B := B) (α := α) h) := by
  unfold jointBooleanSource
  infer_instance

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

noncomputable def principalSliceValue (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) : ℝ :=
  ∑ b, c b * ∏ k, (lower (b, k) + width (b, k) * x (b, k))

end Erdos3

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def packPair (x : Fin 2 → (ι → ℝ) × ℝ) : PairInput ι :=
  (((x 0).1, (x 1).1), ((x 0).2, (x 1).2))

def packFour (x : Fin 4 → (ι → ℝ) × ℝ) : FourInput ι :=
  (packPair ![x 2, x 3], packPair ![x 0, x 1])

def fourBoxPacking (x : Fin 4 × Option ι → ℝ) : FourInput ι :=
  packFour (fun b => ((fun i => x (b, some i)), x (b, none)))

noncomputable def fourBoxValue (B : Fin 4 → SlicedProductBlock ι)
    (x : Fin 4 × Option ι → ℝ) : ℝ :=
  ∑ b, (B b).value (fun i => x (b, some i)) (x (b, none))

end Erdos3.SlicedProductBlock

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B ι : Type*} [Fintype B] [Fintype ι] [DecidableEq B] [DecidableEq ι]

def principalSliceBlock (c : B → ℝ) (lower width : B × Option ι → ℝ) (b : B) :
    SlicedProductBlock ι where
  coefficient := c b
  lower i := lower (b, some i)
  width i := width (b, some i)
  lastLower := lower (b, none)
  lastWidth := width (b, none)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {J ι : Type*} [Fintype J] [Fintype ι] [DecidableEq J] [DecidableEq ι]

def principalSumBoxSplit (x : (Fin 4 ⊕ J) × Option ι → ℝ) :
    (Fin 4 × Option ι → ℝ) × (J × Option ι → ℝ) :=
  ((fun p => x (.inl p.1, p.2)), (fun p => x (.inr p.1, p.2)))

noncomputable def principalFourRemainderDensity (c : Fin 4 ⊕ J → ℝ)
    (lower width : (Fin 4 ⊕ J) × Option ι → ℝ) : ℝ → ℝ :=
  independentShiftDensity (unitBoxMeasure (J × Option ι))
    (principalSliceValue (fun b => c (.inr b))
      (fun p => lower (.inr p.1, p.2)) (fun p => width (.inr p.1, p.2)))
    (SlicedProductBlock.fourDensity
      (principalSliceBlock c lower width (.inl 0))
      (principalSliceBlock c lower width (.inl 1))
      (principalSliceBlock c lower width (.inl 2))
      (principalSliceBlock c lower width (.inl 3)))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def reindexedSlicedPrincipalDensity
    {B F J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]
    (eB : Fin 4 ⊕ J ≃ B) (eF : Option I ≃ F)
    (c : B → ℝ) (lower width : B × F → ℝ) : ℝ → ℝ :=
  principalFourRemainderDensity (fun b => c (eB b))
    (fun p => lower (eB p.1, eF p.2)) (fun p => width (eB p.1, eF p.2))

noncomputable def fourBlockDecomposition (B : Type*) [Fintype B] (hB : 4 ≤ Fintype.card B) :
    Fin 4 ⊕ Fin (Fintype.card B - 4) ≃ B :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)

noncomputable def canonicalSlicedPrincipalDensity
    {B F : Type*} [Fintype B] [Fintype F] [DecidableEq F]
    (hB : 4 ≤ Fintype.card B) (i : F) (c : B → ℝ) (lower width : B × F → ℝ) : ℝ → ℝ :=
  reindexedSlicedPrincipalDensity (fourBlockDecomposition B hB) (Equiv.optionSubtypeNe i) c lower width

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CompatibleReducedFastReset
namespace OAI

section

namespace Erdos3

def reducedResetParameter (a : ℕ) (p : ℝ) : ℝ :=
  ((p + 2) ^ 10 + 2) ^ 36 + (p + 2) ^ a + p + 2

theorem reducedResetParameter_nonneg (a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ reducedResetParameter a p := by
  unfold reducedResetParameter
  positivity

theorem le_reducedResetParameter (a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ reducedResetParameter a p := by
  have h₁ : 0 ≤ ((p + 2) ^ 10 + 2) ^ 36 := by positivity
  have h₂ : 0 ≤ (p + 2) ^ a := by positivity
  exact (le_add_of_nonneg_left (add_nonneg h₁ h₂)).trans
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))

theorem reducedResetParameter_controls (a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + 2) ^ a ≤ reducedResetParameter a p + 2 ∧
      ((p + 2) ^ 10 + 2) ^ 36 ≤ reducedResetParameter a p ∧
      ((p + 2) ^ 10 + 2) ^ 18 + (p + 2) ^ a ≤ reducedResetParameter a p + 2 := by
  have h₁ : 0 ≤ ((p + 2) ^ 10 + 2) ^ 36 := by positivity
  have h₂ : 0 ≤ (p + 2) ^ a := by positivity
  have hbase : 1 ≤ (p + 2) ^ 10 + 2 := by
    exact (by norm_num : (1 : ℝ) ≤ 2).trans
      (le_add_of_nonneg_left (by positivity : 0 ≤ (p + 2) ^ 10))
  have hpow := pow_le_pow_right₀ hbase (by decide : 18 ≤ 36)
  have hsum : ((p + 2) ^ 10 + 2) ^ 36 + (p + 2) ^ a ≤ reducedResetParameter a p :=
    (le_add_of_nonneg_right hp).trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  have hplus : reducedResetParameter a p ≤ reducedResetParameter a p + 2 :=
    le_add_of_nonneg_right (by norm_num)
  exact ⟨(le_add_of_nonneg_left h₁).trans (hsum.trans hplus),
    (le_add_of_nonneg_right h₂).trans hsum,
    (add_le_add hpow (le_refl ((p + 2) ^ a))).trans (hsum.trans hplus)⟩

theorem exists_reduced_reset_budget (a cs cr : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (reducedResetParameter a p + cs) ^ cs ≤ (p + C) ^ C ∧
      (reducedResetParameter a p + cr) ^ cr ≤ (p + C) ^ C := by
  let Z : Polynomial ℕ := ((Polynomial.X + 2) ^ 10 + 2) ^ 36 +
    (Polynomial.X + 2) ^ a + Polynomial.X + 2
  let B := (Z + Polynomial.C cs) ^ cs + (Z + Polynomial.C cr) ^ cr
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hz := reducedResetParameter_nonneg a hp
  have hs : 0 ≤ (reducedResetParameter a p + cs) ^ cs := by positivity
  have hr : 0 ≤ (reducedResetParameter a p + cr) ^ cr := by positivity
  have hh : (reducedResetParameter a p + cs) ^ cs +
      (reducedResetParameter a p + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [B, Z, reducedResetParameter, Polynomial.eval₂_pow] using hbound p hp
  exact ⟨(le_add_of_nonneg_right hr).trans hh, (le_add_of_nonneg_left hs).trans hh⟩

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def ControlledReducedFastResetSpec (s a C : ℕ) : Prop :=
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
      (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
      (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1) U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      2 * (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card (ReducedSquareSymbolIndex s w ω ⊕ QuotientTopSymbolIndex s w ω) : ℝ) ≤ p →
      ((Fintype.card (ReducedSquareSymbolIndex s w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      (∀ j i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v j) i) H) →
      ∃ (S : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
        (m : ℕ), 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
        ∀ (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
          (A D : F.quotientTop.RealPolynomialSymbolGroup w),
        P.coord ∈ realificationLieSubalgebra U →
        (A⁻¹ * F.reducedSquareRealSymbolHom w E).coord ∈
          realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
        (F.reducedSquareRealSymbolHom w R * D⁻¹).coord ∈
          realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
        F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) E →
        F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l R →
        F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) (A⁻¹ * F.reducedSquareRealSymbolHom w E) →
        F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l
          (F.reducedSquareRealSymbolHom w R * D⁻¹) →
        let c := F.reducedSquareRealLinearLift w S (A⁻¹ * F.reducedSquareRealSymbolHom w E)
        let d := F.reducedSquareRealLinearLift w S (F.reducedSquareRealSymbolHom w R * D⁻¹)
        (E * c⁻¹) * (c * P * d) * (d⁻¹ * R) = E * P * R ∧
          (c * P * d).coord ∈ realificationLieSubalgebra U ∧
          F.reducedSquareRealSymbolHom w (E * c⁻¹) = A ∧
          F.reducedSquareRealSymbolHom w (d⁻¹ * R) = D ∧
          F.reducedSquareRealSymbolHom w (c * P * d) =
            A⁻¹ * F.reducedSquareRealSymbolHom w (E * P * R) * D⁻¹ ∧
          F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
            (Real.exp ((p + C) ^ C)) (E * c⁻¹) ∧
          F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w m (d⁻¹ * R)

def ReducedFastResetSpec (s a C : ℕ) : Prop :=
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
      (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1) U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      (∀ j i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v j) i) H) →
      ∃ (S : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
        (m : ℕ), 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
        ∀ (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
          (A D : F.quotientTop.RealPolynomialSymbolGroup w),
        P.coord ∈ realificationLieSubalgebra U →
        (A⁻¹ * F.reducedSquareRealSymbolHom w E).coord ∈
          realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
        (F.reducedSquareRealSymbolHom w R * D⁻¹).coord ∈
          realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
        F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) E →
        F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l R →
        F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) (A⁻¹ * F.reducedSquareRealSymbolHom w E) →
        F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l
          (F.reducedSquareRealSymbolHom w R * D⁻¹) →
        let c := F.reducedSquareRealLinearLift w S (A⁻¹ * F.reducedSquareRealSymbolHom w E)
        let d := F.reducedSquareRealLinearLift w S (F.reducedSquareRealSymbolHom w R * D⁻¹)
        (E * c⁻¹) * (c * P * d) * (d⁻¹ * R) = E * P * R ∧
          (c * P * d).coord ∈ realificationLieSubalgebra U ∧
          F.reducedSquareRealSymbolHom w (E * c⁻¹) = A ∧
          F.reducedSquareRealSymbolHom w (d⁻¹ * R) = D ∧
          F.reducedSquareRealSymbolHom w (c * P * d) =
            A⁻¹ * F.reducedSquareRealSymbolHom w (E * P * R) * D⁻¹ ∧
          F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
            (Real.exp ((p + C) ^ C)) (E * c⁻¹) ∧
          F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w m (d⁻¹ * R)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_controlled_reduced_fast_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ControlledReducedFastResetSpec s a C := by
  obtain ⟨cs, _, hprodSlow⟩ := exists_symbol_slow_mul_inv_bound s
  obtain ⟨cr, _, hprodRat⟩ := exists_symbol_rational_inv_mul_bound s
  obtain ⟨C, hC, hbudget⟩ := exists_reduced_reset_budget a cs cr
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw _ _ U v hspan hU H l p hH hl hp
    hdim hσ hrows hcols hHp hlp hc hv
  let G := F.squareFiltration.quotientTop
  let b := F.reducedSquareBasis e ω hF
  let ν : ReducedSquareBasisIndex s ω → ℕ := fun i => squareBasisWeight ω i.val
  have hG := F.reducedSquareBasis_layers e ω hF
  have hstruct := F.reducedSquareBasis_structure_height e ω hF hH hc
  have hcard : Fintype.card (ReducedSquareBasisIndex s ω) ≤ 2 * Fintype.card ι :=
    (Fintype.card_subtype_le _).trans (card_squareBasis_index_le ω)
  have hd : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ p :=
    (Nat.cast_le.mpr hcard).trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hdim)
  let z := reducedResetParameter a p
  have hz : 0 ≤ z := reducedResetParameter_nonneg a hp
  have hpz : p ≤ z := le_reducedResetParameter a hp
  have hinput := (reducedResetParameter_controls a hp).1
  have hden := (reducedResetParameter_controls a hp).2.1
  have hgain := (reducedResetParameter_controls a hp).2.2
  have hlifts := F.exists_controlled_reduced_fast_lift w e ω hF U v hspan hU hH hl hv hp hrows hcols hHp hlp
  obtain ⟨S, n, hn, hnp, hln, hlift, hliftSlow, hliftRat⟩ := hlifts
  have hnz : (n : ℝ) ≤ Real.exp z := hnp.trans (Real.exp_le_exp.mpr hden)
  have hRats := hprodRat G b ν hG w hw H z hH hz
    (hd.trans hpz) (hσ.trans hpz) (hHp.trans (Real.exp_le_exp.mpr hpz)) hstruct n hn hnz
  obtain ⟨m, hmdata⟩ := hRats
  have hm := hmdata.1
  have hmp := hmdata.2.1
  have hnm := hmdata.2.2.1
  have hRat := hmdata.2.2.2
  have hbud := hbudget p hp
  refine ⟨S, m, hm, hmp.trans (Real.exp_le_exp.mpr hbud.2), hln.trans hnm, ?_⟩
  intro T hT E P R A D hP hleft hright hE hR hLeftSlow hRightRat
  let c := F.reducedSquareRealLinearLift w S (A⁻¹ * F.reducedSquareRealSymbolHom w E)
  let d := F.reducedSquareRealLinearLift w S (F.reducedSquareRealSymbolHom w R * D⁻¹)
  have hc := (hlift _ hleft).1
  have hcq := (hlift _ hleft).2
  have hdmem := (hlift _ hright).1
  have hdq := (hlift _ hright).2
  have hreset := synchronize_splitting_projection (F.reducedSquareRealSymbolHom w)
    (NilpotentLieBCHGroup.realificationSubgroup
      (hnil := G.polynomialSymbol_lowerCentralSeries_eq_bot w) U) E P R c d A D hP hc hdmem hcq hdq
  refine ⟨hreset.1, hreset.2.1, hreset.2.2.1, hreset.2.2.2.1, hreset.2.2.2.2, ?_, ?_⟩
  · have hE' : G.SymbolSlowBound b ν hG w T (Real.exp (z + 2)) E := by
      apply G.symbolSlowBound_mono b ν hG w T hT _ E hE
      exact Real.exp_le_exp.mpr hinput
    have hcSlow := hliftSlow T hT (Real.exp ((p + 2) ^ a)) (Real.exp_nonneg _) _ hLeftSlow
    have hc' : G.SymbolSlowBound b ν hG w T (Real.exp (z + 2)) c := by
      apply G.symbolSlowBound_mono b ν hG w T hT _ c hcSlow
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hgain
    have hproduct := hprodSlow G b ν hG w hw H z hH hz (hd.trans hpz) (hσ.trans hpz)
      (hHp.trans (Real.exp_le_exp.mpr hpz)) hstruct T hT E c hE' hc'
    exact G.symbolSlowBound_mono b ν hG w T hT (Real.exp_le_exp.mpr hbud.1) _ hproduct
  · have hRn : G.SymbolRationalGrid b ν hG w n R :=
      G.symbolRationalGrid_mono b ν hG w hl hln R hR
    have hdn : G.SymbolRationalGrid b ν hG w n d := hliftRat _ hRightRat
    exact hRat d R hdn hRn

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_reduced_fast_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ReducedFastResetSpec s a C := by
  have hresetExists := exists_controlled_reduced_fast_reset s a
  obtain ⟨c, _, hreset⟩ := hresetExists
  let Q : Polynomial ℕ := 3 * (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) *
    (Polynomial.X + 1) + 2 * Polynomial.X + 2
  let B := (Q + Polynomial.C c) ^ c
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U v hspan hU H l p hH hl hp hι hσ hκ hHp hlp hc hv
  let : Finite (ReducedSquareSymbolIndex s w ω) := F.reducedSquareSymbolIndex_finite e ω hF w hw
  let : Fintype (ReducedSquareSymbolIndex s w ω) := Fintype.ofFinite _
  let : Finite (QuotientTopSymbolIndex s w ω) := F.quotientTopSymbolIndex_finite e ω hF w hw
  let : Fintype (QuotientTopSymbolIndex s w ω) := Fintype.ofFinite _
  let q := reducedMatrixParameter s p
  have hq : 0 ≤ q := reducedMatrixParameter_nonneg s hp
  have hpq : p ≤ q := le_reducedMatrixParameter s hp
  have hdims := F.reduced_lift_matrix_dimensions e ω hF w hw hp hι hσ hκ
  have hfinal : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [B, Q, q, reducedMatrixParameter, Polynomial.eval₂_pow] using hbound p hp
  have hrawExists := hreset F e ω hF w hw U v hspan hU H l q hH hl hq
    hdims.1 (hσ.trans hpq) hdims.2.1 hdims.2.2 (hHp.trans (Real.exp_le_exp.mpr hpq))
    (hlp.trans (Real.exp_le_exp.mpr hpq)) hc hv
  obtain ⟨S, m, hm, hmp, hlm, hraw⟩ := hrawExists
  refine ⟨S, m, hm, hmp.trans (Real.exp_le_exp.mpr hfinal), hlm, ?_⟩
  intro T hT E P R A D hP hleft hright hE hR hLeftSlow hRightRat
  have hinput : Real.exp ((p + 2) ^ a) ≤ Real.exp ((q + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a)
  have hE' := F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T hT hinput E hE
  have hLeftSlow' := F.quotientTop.symbolSlowBound_mono (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T hT hinput _ hLeftSlow
  have hresult := hraw T hT E P R A D hP hleft hright hE' hR hLeftSlow' hRightRat
  obtain ⟨hprod, hfast, hA, hD, hmid, hslow, hgrid⟩ := hresult
  refine ⟨hprod, hfast, hA, hD, hmid, ?_, hgrid⟩
  exact F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T hT
    (Real.exp_le_exp.mpr hfinal) _ hslow

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def CompatibleReducedFastResetSpec (s a C : ℕ) : Prop :=
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
      (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1) U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      (∀ j i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v j) i) H) →
      ∃ (S : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
        (m : ℕ), 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (T : σ → ℝ), (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
        ∀ (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
          (A B D : F.quotientTop.RealPolynomialSymbolGroup w),
        P.coord ∈ realificationLieSubalgebra U →
        B.coord ∈ realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
        A * B * D = F.reducedSquareRealSymbolHom w (E * P * R) →
        F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) E →
        F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l R →
        F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) A →
        F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l D →
        let c := F.reducedSquareRealLinearLift w S (A⁻¹ * F.reducedSquareRealSymbolHom w E)
        let d := F.reducedSquareRealLinearLift w S (F.reducedSquareRealSymbolHom w R * D⁻¹)
        (E * c⁻¹) * (c * P * d) * (d⁻¹ * R) = E * P * R ∧
          (c * P * d).coord ∈ realificationLieSubalgebra U ∧
          F.reducedSquareRealSymbolHom w (E * c⁻¹) = A ∧
          F.reducedSquareRealSymbolHom w (d⁻¹ * R) = D ∧
          F.reducedSquareRealSymbolHom w (c * P * d) = B ∧
          F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
            (Real.exp ((p + C) ^ C)) (E * c⁻¹) ∧
          F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w m (d⁻¹ * R)

theorem exists_compatible_reduced_fast_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CompatibleReducedFastResetSpec s a C := by
  have hcomparisonExists := exists_reduced_projected_comparison s a
  obtain ⟨cc, _, hcomparison⟩ := hcomparisonExists
  have hresetExists := exists_reduced_fast_reset s 1
  obtain ⟨cr, _, hreset⟩ := hresetExists
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C cc) ^ cc +
    (Polynomial.X + 2) ^ a + Polynomial.X + 2
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C cc) ^ cc +
    (Q + Polynomial.C cr) ^ cr
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U v hspan hU H l p hH hl hp hι hσ hκ hHp hlp hc hv
  let q := (p + cc) ^ cc + (p + 2) ^ a + p + 2
  have hc0 : 0 ≤ (p + cc) ^ cc := by positivity
  have ha0 : 0 ≤ (p + 2) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hcq : (p + cc) ^ cc ≤ q := by dsimp [q]; linarith
  have haq : (p + 2) ^ a ≤ q + 2 := by dsimp [q]; linarith
  have hsum : (p + cc) ^ cc + (q + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hbound p hp
  have hr0 : 0 ≤ (q + cr) ^ cr := by positivity
  have hcb : (p + cc) ^ cc ≤ (p + C) ^ C := (le_add_of_nonneg_right hr0).trans hsum
  have hrb : (q + cr) ^ cr ≤ (p + C) ^ C := (le_add_of_nonneg_left hc0).trans hsum
  have hcompdata := hcomparison F e ω hF w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hc hv
  obtain ⟨n, hn, hnp, hln, hcompare⟩ := hcompdata
  have hresetdata := hreset F e ω hF w hw U v hspan hU H n q hH hn hq
    (hι.trans hpq) (hσ.trans hpq) (hκ.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq))
    (hnp.trans (Real.exp_le_exp.mpr hcq)) hc hv
  obtain ⟨S, m, hm, hmp, hnm, hresetFactors⟩ := hresetdata
  refine ⟨S, m, hm, hmp.trans (Real.exp_le_exp.mpr hrb), hln.trans hnm, ?_⟩
  intro T hT E P R A B D hP hB heq hE hR hA hD
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hcomp := hcompare T (fun i => (Real.exp_le_exp.mpr hcb).trans (hT i))
    E P R A B D hP hB heq hE hA hR hD
  have hE' := F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T hTpos
    (Real.exp_le_exp.mpr haq) E hE
  have hA' := F.quotientTop.symbolSlowBound_mono (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T hTpos
    (Real.exp_le_exp.mpr (hcq.trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2)))) _ hcomp.2.2.1
  have hR' := F.squareFiltration.quotientTop.symbolRationalGrid_mono (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w hl hln R hR
  have hresult := hresetFactors T hTpos E P R A D hP hcomp.1 hcomp.2.1
    (by simpa only [pow_one] using hE') hR' (by simpa only [pow_one] using hA') hcomp.2.2.2
  refine ⟨hresult.1, hresult.2.1, hresult.2.2.1, hresult.2.2.2.1, ?_, ?_, hresult.2.2.2.2.2.2⟩
  · rw [hresult.2.2.2.2.1, ← heq]
    group
  · exact F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T hTpos
      (Real.exp_le_exp.mpr hrb) _ hresult.2.2.2.2.2.1

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtShortDualVector
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped NNReal

noncomputable def affinePhaseRemainder (P : Polynomial ℝ) (k : ℕ) (a q : ℝ) :
    Polynomial ℝ := (P.comp (C q * X + C a)).erase k

end Erdos3

end

section

namespace Erdos3

open Polynomial

noncomputable def polynomialShiftDifference (P : Polynomial ℝ) (h : ℝ) : Polynomial ℝ :=
  P - P.comp (X + C h)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

noncomputable def intervalPolynomialPhase (N : ℕ) (P : Polynomial ℝ) (x : ℤ) : ℂ :=
  if x ∈ Finset.Ico (0 : ℤ) (N : ℤ) then character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle) else 0

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open Polynomial CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

noncomputable def polynomialExponentialSum (P : Polynomial ℝ) (N : ℕ) : ℂ :=
  ∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle)

def LeadingWeylBound (k B K : ℕ) : Prop :=
  ∀ (P : Polynomial ℝ), P.natDegree ≤ k → ∀ N : ℕ, 0 < N → K ≤ N →
    (N : ℝ) / B ≤ ‖polynomialExponentialSum P N‖ →
    ∃ q : ℕ, 0 < q ∧ q ≤ K ∧ ∃ p : ℤ,
      |(q : ℝ) * P.coeff k - p| ≤ (K : ℝ) / (N : ℝ) ^ k

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open Polynomial CircleFourier

def PolynomialIntervalPowerBound (k C d : ℕ) : Prop :=
      ∀ (P : Polynomial ℝ) (u v : ℤ) (δ : ℝ),
        P.natDegree ≤ k → 0 < (v - u).toNat → 0 < δ → δ ≤ 1 →
        (C : ℝ) ≤ δ ^ d * (v - u).toNat →
        δ * (v - u).toNat ≤
          ‖∑ n ∈ Finset.Ico u v, character ((P.eval (n : ℝ) : ℝ) : CircleFourier.Circle)‖ →
        ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C / δ ^ d ∧ ∃ p : ℤ,
          |(q : ℝ) * P.coeff k - p| ≤ C / (δ ^ d * ((v - u).toNat : ℝ) ^ k)

end Erdos3

end

section

namespace Erdos3

open Polynomial CircleFourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProjectedPointwiseCoefficient
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def gradedPolynomialSymbol :
    VectorPolynomial σ ℚ F.AssociatedGraded →ₗ[ℚ] F.PolynomialSymbol w :=
  (F.polynomialSymbolBasis b ω hlayers w).repr.symm.toLinearMap.comp
    (supportedCoordinates (F.associatedGradedBasis b ω hlayers)
      {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2})

theorem gradedPolynomialSymbol_coordinate
    (p : VectorPolynomial σ ℚ F.AssociatedGraded) (z : SymbolBasisIndex w ω) :
    (F.polynomialSymbolBasis b ω hlayers w).repr (F.gradedPolynomialSymbol b ω hlayers w p) z =
      (F.associatedGradedBasis b ω hlayers).repr (coefficients p z.val.1) z.val.2 := by
  change ((F.polynomialSymbolBasis b ω hlayers w).repr
    ((F.polynomialSymbolBasis b ω hlayers w).repr.symm _)) z = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem gradedPolynomialSymbol_gradedSymbolPolynomial (x : F.PolynomialSymbol w) :
    F.gradedPolynomialSymbol b ω hlayers w (F.gradedSymbolPolynomial b ω hlayers w x) = x := by
  apply (F.polynomialSymbolBasis b ω hlayers w).repr.injective
  ext z
  rw [F.gradedPolynomialSymbol_coordinate, F.gradedSymbolPolynomial_coefficient]

noncomputable def homogeneousSymbolLift (α : σ →₀ ℕ) :
    F.AssociatedGraded →ₗ[ℚ] F.PolynomialSymbol w :=
  (F.gradedPolynomialSymbol b ω hlayers w).comp
    (coefficients.symm.toLinearMap.comp (Finsupp.lsingle α))

@[simp] theorem homogeneousSymbolLift_apply (α : σ →₀ ℕ) (v : F.AssociatedGraded) :
    F.homogeneousSymbolLift b ω hlayers w α v =
      F.gradedPolynomialSymbol b ω hlayers w (monomial α v) := by
  simp only [homogeneousSymbolLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Finsupp.lsingle_apply, coefficients_symm_single]

theorem homogeneousSymbolLift_coordinate [DecidableEq σ] (α : σ →₀ ℕ)
    (v : F.AssociatedGraded) (z : SymbolBasisIndex w ω) :
    (F.polynomialSymbolBasis b ω hlayers w).repr (F.homogeneousSymbolLift b ω hlayers w α v) z =
      if α = z.val.1 then (F.associatedGradedBasis b ω hlayers).repr v z.val.2 else 0 := by
  rw [F.homogeneousSymbolLift_apply, F.gradedPolynomialSymbol_coordinate, coefficients_monomial]
  by_cases h : α = z.val.1 <;> simp [h]

theorem gradedSymbolPolynomial_homogeneousSymbolLift (α : σ →₀ ℕ) (v : F.AssociatedGraded) :
    F.gradedSymbolPolynomial b ω hlayers w (F.homogeneousSymbolLift b ω hlayers w α v) =
      monomial α (basisGradeProjection (F.associatedGradedBasis b ω hlayers) ω (Finsupp.weight w α) v) := by
  classical
  apply coefficients.injective
  ext β
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  rw [coefficients_monomial]
  by_cases hα : α = β
  · subst β
    rw [Finsupp.single_eq_same, basisGradeProjection_repr]
    by_cases hd : Finsupp.weight w α = ω i
    · rw [F.gradedSymbolPolynomial_coefficient b ω hlayers w _ ⟨(α, i), hd⟩,
        F.homogeneousSymbolLift_coordinate]
      simp only [hd, ite_true]
    · rw [F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ α i hd]
      exact (if_neg (Ne.symm hd)).symm
  · rw [Finsupp.single_eq_of_ne (Ne.symm hα), map_zero, Finsupp.zero_apply]
    by_cases hd : Finsupp.weight w β = ω i
    · rw [F.gradedSymbolPolynomial_coefficient b ω hlayers w _ ⟨(β, i), hd⟩,
        F.homogeneousSymbolLift_coordinate]
      exact if_neg hα
    · exact F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ β i hd

theorem homogeneousSymbolLift_coefficient (α : σ →₀ ℕ) (x : F.PolynomialSymbol w) :
    F.homogeneousSymbolLift b ω hlayers w α (coefficients (F.gradedSymbolPolynomial b ω hlayers w x) α) =
      basisCoordinateProjection (F.polynomialSymbolBasis b ω hlayers w) {z | z.val.1 = α} x := by
  classical
  apply (F.polynomialSymbolBasis b ω hlayers w).repr.injective
  ext z
  rw [F.homogeneousSymbolLift_coordinate, basisCoordinateProjection_repr]
  simp only [Set.mem_ofPred_eq]
  by_cases h : z.val.1 = α
  · rw [if_pos h, if_pos h.symm, ← h]
    exact F.gradedSymbolPolynomial_coefficient b ω hlayers w x z
  · rw [if_neg h, if_neg (Ne.symm h)]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

section Coefficients

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem gradedSymbolPolynomial_coefficient_symbol (p : F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.gradedSymbolPolynomial e ω hF w (F.polynomialSymbolMap w p)) α =
      F.associatedGradedPieceMap (Finsupp.weight w α) ⟨coefficients p.val α, p.property α⟩ := by
  apply (F.associatedGradedBasis e ω hF).repr.injective
  ext i
  rw [F.associatedGradedPieceMap_coordinate]
  by_cases hi : Finsupp.weight w α = ω i
  · rw [if_pos hi]
    exact (F.gradedSymbolPolynomial_coefficient e ω hF w _ ⟨(α, i), hi⟩).trans
      (F.polynomialSymbolBasis_repr_map e ω hF w p ⟨(α, i), hi⟩)
  · rw [if_neg hi]
    exact F.gradedSymbolPolynomial_coefficient_of_ne e ω hF w _ α i hi

end Coefficients

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

theorem gradedSymbolPolynomial_filteredMap_coefficient (x : F.PolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (G.gradedSymbolPolynomial f ν hG w (F.filteredPolynomialSymbolMap G φ hφ w x)) α =
      F.associatedGradedMap G φ hφ (coefficients (F.gradedSymbolPolynomial e ω hF w x) α) := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.filteredPolynomialSymbolMap_symbol, G.gradedSymbolPolynomial_coefficient_symbol,
    F.gradedSymbolPolynomial_coefficient_symbol, F.associatedGradedMap_piece]
  congr 1
  apply Subtype.ext
  exact F.filteredPolynomialMap_coefficient G φ hφ w p α

theorem gradedSymbolPolynomial_filteredMap (x : F.PolynomialSymbol w) :
    G.gradedSymbolPolynomial f ν hG w (F.filteredPolynomialSymbolMap G φ hφ w x) =
      VectorPolynomial.map (F.associatedGradedMap G φ hφ).toLinearMap
        (F.gradedSymbolPolynomial e ω hF w x) := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  exact F.gradedSymbolPolynomial_filteredMap_coefficient G e ω hF f ν hG φ hφ w x α

theorem associatedGradedMap_basis_repr (i : ι) (j : κ) :
    (G.associatedGradedBasis f ν hG).repr
      (F.associatedGradedMap G φ hφ (F.associatedGradedBasis e ω hF i)) j =
      if ω i = ν j then f.repr (φ (e i)) j else 0 := by
  rw [G.associatedGradedBasis_repr, F.associatedGradedBasis_apply]
  change (G.polynomialSymbolBasis f ν hG (fun _ : Unit => 1)).repr
    (F.filteredPolynomialSymbolMap G φ hφ (fun _ : Unit => 1)
      (F.polynomialSymbolBasis e ω hF (fun _ : Unit => 1) _)) _ = _
  rw [F.filteredPolynomialSymbolMap_basis_repr G e ω hF f ν hG φ hφ]
  simp only [unitMonomial_injective.eq_iff]

theorem associatedGradedMap_gradeProjection (j : ℕ) (x : F.AssociatedGraded) :
    F.associatedGradedMap G φ hφ (basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x) =
      basisGradeProjection (G.associatedGradedBasis f ν hG) ν j (F.associatedGradedMap G φ hφ x) := by
  apply basisBlockMap_commutes (F.associatedGradedBasis e ω hF) (G.associatedGradedBasis f ν hG)
    ω ν (F.associatedGradedMap G φ hφ).toLinearMap
  intro i k hik
  change (G.associatedGradedBasis f ν hG).repr
    (F.associatedGradedMap G φ hφ (F.associatedGradedBasis e ω hF i)) k = 0
  rw [F.associatedGradedMap_basis_repr G e ω hF f ν hG φ hφ, if_neg (Ne.symm hik)]

theorem homogeneousSymbolLift_filteredMap (α : σ →₀ ℕ) (x : F.AssociatedGraded) :
    F.filteredPolynomialSymbolMap G φ hφ w (F.homogeneousSymbolLift e ω hF w α x) =
      G.homogeneousSymbolLift f ν hG w α (F.associatedGradedMap G φ hφ x) := by
  apply G.gradedSymbolPolynomial_injective f ν hG w
  rw [F.gradedSymbolPolynomial_filteredMap G e ω hF f ν hG φ hφ w,
    F.gradedSymbolPolynomial_homogeneousSymbolLift, G.gradedSymbolPolynomial_homogeneousSymbolLift,
    VectorPolynomial.map_monomial]
  apply congrArg (monomial α)
  exact F.associatedGradedMap_gradeProjection G e ω hF f ν hG φ hφ (Finsupp.weight w α) x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ ι M : Type*} [LieRing M] [LieAlgebra ℚ M] {t : ℕ}
  (F : NilpotentLieFiltration M t)

theorem symbol_mem_pointwise_iff_refiltered_coefficients (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded) (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w p ∈ F.symbolPointwiseSubalgebra b ω hF w U ↔
      ∀ α, coefficients p.val α ∈ F.gradedRefiltrationLayer U (Finsupp.weight w α) := by
  rw [F.mem_symbolPointwiseSubalgebra_iff]
  apply forall_congr'
  intro α
  rw [F.gradedSymbolPolynomial_coefficient_symbol]
  exact (F.mem_gradedRefiltrationLayer_iff U (Finsupp.weight w α)
    ⟨coefficients p.val α, p.property α⟩).symm

end NilpotentLieFiltration

namespace DegreeRankLieFiltration

variable {σ ι L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

theorem projectedHorizontalSymbolCoefficient_mem (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.PolynomialSymbol w) (hx : x ∈ F.symbolPointwiseSubalgebra b ω hF w U)
    (α : σ →₀ ℕ) :
    G.projectedHorizontalSymbolCoefficient F φ hφ w α x ∈
      G.layerHorizontalImage (F.gradedRefiltrationLayer U) φ
        (fun d x hx => hφ d x (F.gradedRefiltrationLayer_le U d hx)) (Finsupp.weight w α) := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  have hcoef := (F.symbol_mem_pointwise_iff_refiltered_coefficients b ω hF w U p).mp hx α
  apply (G.mem_layerHorizontalImage _ _ _ _ _).mpr
  refine ⟨⟨coefficients p.val α, hcoef⟩, ?_⟩
  rw [G.projectedHorizontalSymbolCoefficient_symbol]
  rfl

theorem real_projectedHorizontalSymbolCoefficient_mem (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : ℝ ⊗[ℚ] F.PolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U))
    (α : σ →₀ ℕ) :
    (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ x ∈
      (G.layerHorizontalImage (F.gradedRefiltrationLayer U) φ
        (fun d x hx => hφ d x (F.gradedRefiltrationLayer_le U d hx))
          (Finsupp.weight w α)).baseChange ℝ := by
  let K := (F.symbolPointwiseSubalgebra b ω hF w U).toSubmodule
  let V := G.layerHorizontalImage (F.gradedRefiltrationLayer U) φ
    (fun d x hx => hφ d x (F.gradedRefiltrationLayer_le U d hx)) (Finsupp.weight w α)
  let f := G.projectedHorizontalSymbolCoefficient F φ hφ w α
  have hmap : K.map f ≤ V := by
    rintro y ⟨z, hz, rfl⟩
    exact G.projectedHorizontalSymbolCoefficient_mem F φ hφ b ω hF w U z hz α
  apply Submodule.baseChange_mono ℝ hmap
  rw [realification_map]
  exact ⟨x, hx, rfl⟩

end DegreeRankLieFiltration

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.HomogeneousGradedProjectionBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module
variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

noncomputable def homogeneousGradedProjection : F.AssociatedGraded →ₗ⁅ℚ⁆ M :=
  (G.homogeneousAssociatedGradedEquiv c ν hG hc).toLieHom.comp
    (F.associatedGradedMap G φ hφ)

@[simp] theorem homogeneousGradedProjection_repr (x : F.AssociatedGraded) (j : κ) :
    c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ x) j =
      (G.associatedGradedBasis c ν hG).repr (F.associatedGradedMap G φ hφ x) j :=
  G.homogeneousAssociatedGradedEquiv_repr c ν hG hc _ j

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem homogeneousGradedProjection_basis_repr (i : ι) (j : κ) :
    c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ
      (F.associatedGradedBasis b ω hF i)) j =
      if ω i = ν j then c.repr (φ (b i)) j else 0 := by
  rw [F.homogeneousGradedProjection_repr,
    F.associatedGradedMap_basis_repr G b ω hF c ν hG φ hφ]

theorem homogeneousGradedProjection_gradeProjection (r : ℕ) (x : F.AssociatedGraded) :
    F.homogeneousGradedProjection G c ν hG hc φ hφ
      (basisGradeProjection (F.associatedGradedBasis b ω hF) ω r x) =
      basisGradeProjection c ν r (F.homogeneousGradedProjection G c ν hG hc φ hφ x) := by
  apply basisBlockMap_commutes (F.associatedGradedBasis b ω hF) c ω ν
    (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap
  intro i j hij
  change c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ
    (F.associatedGradedBasis b ω hF i)) j = 0
  rw [F.homogeneousGradedProjection_basis_repr G c ν hG hc φ hφ b ω hF]
  exact if_neg (Ne.symm hij)

theorem homogeneousGradedProjection_image_graded
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule) :
    BasisGradedSubmodule c ν
      (W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ)).toSubmodule := by
  rintro r y ⟨x, hx, rfl⟩
  exact ⟨basisGradeProjection (F.associatedGradedBasis b ω hF) ω r x, hW r x hx,
    F.homogeneousGradedProjection_gradeProjection G c ν hG hc φ hφ b ω hF r x⟩

 theorem homogeneousGradedProjection_span {J : Type*}
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : J → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (fun j => F.homogeneousGradedProjection G c ν hG hc φ hφ (v j))) =
      (W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ)).toSubmodule := by
  change _ = W.toSubmodule.map (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap
  rw [← hv, Submodule.map_span]
  congr 1
  exact Set.range_comp _ _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped BigOperators

variable {ι κ L M : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem homogeneousGradedProjection_coordinate_logHeight {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ i j, rationalLogHeight (c.repr (φ (b i)) j) ≤ p)
    (x : F.AssociatedGraded)
    (hx : ∀ i, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr x i) ≤ p) (j : κ) :
    rationalLogHeight (c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ x) j) ≤
      (p + 2) ^ 4 := by
  apply rational_functional_value_logHeight (F.associatedGradedBasis b ω hF)
    ((c.coord j).comp (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap)
    hp hι _ x hx
  intro i
  change rationalLogHeight (c.repr
    (F.homogeneousGradedProjection G c ν hG hc φ hφ (F.associatedGradedBasis b ω hF i)) j) ≤ p
  rw [F.homogeneousGradedProjection_basis_repr G c ν hG hc φ hφ b ω hF]
  split_ifs
  · exact hentries i j
  · simpa [rationalLogHeight] using hp

theorem homogeneousGradedProjection_coordinate_ceil_height {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ i j, rationalLogHeight (c.repr (φ (b i)) j) ≤ p)
    (x : F.AssociatedGraded)
    (hx : ∀ i, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr x i) ≤ p) (j : κ) :
    RationalHeightLE (c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ x) j)
      ⌈Real.exp ((p + 2) ^ 4)⌉₊ :=
  rationalHeightLE_ceil_exp
    (F.homogeneousGradedProjection_coordinate_logHeight G c ν hG hc φ hφ b ω hF
      hp hι hentries x hx j)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.HomogeneousGradedProjectionFrequency
namespace OAI

section

namespace Erdos3

open Module

variable {K V W ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

theorem graded_image_frequency_zero
    (b : Basis ι K V) (ω : ι → ℕ) (c : Basis κ K W) (ν : κ → ℕ)
    (T : V →ₗ[K] W) (s : ℕ)
    (hT : ∀ x, T (basisGradeProjection b ω s x) = basisGradeProjection c ν s (T x))
    (U : Submodule K V) (hU : BasisGradedSubmodule b ω U) (η : W →ₗ[K] K)
    (hsource : ∀ x ∈ U, basisGradeProjection b ω s x = x → η (T x) = 0)
    {y : W} (hy : y ∈ U.map T) (hgrade : basisGradeProjection c ν s y = y) :
    η y = 0 := by
  obtain ⟨x, hx, rfl⟩ := hy
  have h := hsource (basisGradeProjection b ω s x) (hU s x hx)
    (basisCoordinateProjection_idempotent b {i | ω i = s} x)
  rwa [hT, hgrade] at h

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def gradedFrequency (η : L →ₗ[ℚ] ℚ) : F.AssociatedGraded →ₗ[ℚ] ℚ :=
  η.comp (b.repr.symm.toLinearMap.comp (F.associatedGradedBasis b ω hF).repr.toLinearMap)

theorem gradedFrequency_projection (η : L →ₗ[ℚ] ℚ) (j : ℕ) (x : L) :
    F.gradedFrequency b ω hF η (F.gradedPieceProjection b ω hF j x) =
      η (basisGradeProjection b ω j x) := by
  change η (b.repr.symm ((F.associatedGradedBasis b ω hF).repr
    ((F.associatedGradedBasis b ω hF).repr.symm (b.repr (basisGradeProjection b ω j x))))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

include hF in
theorem basisGradeProjection_top (x : F.layer s) : basisGradeProjection b ω s (x : L) = x := by
  have he : {i | ω i = s} = {i | s ≤ ω i} := by
    ext i
    exact ⟨fun h => h.ge, fun h => le_antisymm (F.adaptedBasis_weight_le_step b ω hF i) h⟩
  change basisCoordinateProjection b {i | ω i = s} (x : L) = x
  rw [he]
  exact basisCoordinateProjection_eq_self b _ _ ((hF s) ▸ x.property)

theorem gradedFrequency_top_piece (η : L →ₗ[ℚ] ℚ) (x : F.layer s) :
    F.gradedFrequency b ω hF η (F.associatedGradedPieceMap s x) = η x := by
  rw [← F.gradedPieceProjection_eq_pieceMap b ω hF, F.gradedFrequency_projection,
    F.basisGradeProjection_top b ω hF x]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem gradedFrequency_top_natural (η : M →ₗ[ℚ] ℚ) (x : F.AssociatedGraded)
    (hx : basisGradeProjection (F.associatedGradedBasis e ω hF) ω s x = x) :
    F.gradedFrequency e ω hF (η.comp φ.toLinearMap) x =
      G.gradedFrequency f ν hG η (F.associatedGradedMap G φ hφ x) := by
  obtain ⟨v, rfl⟩ := F.exists_associatedGradedPieceMap_of_pure e ω hF s x hx
  rw [F.associatedGradedMap_piece, F.gradedFrequency_top_piece,
    G.gradedFrequency_top_piece]
  rfl

theorem gradedFrequency_comap_top_zero (η : M →ₗ[ℚ] ℚ)
    (U : LieSubalgebra ℚ G.AssociatedGraded)
    (hzero : ∀ y ∈ U, basisGradeProjection (G.associatedGradedBasis f ν hG) ν s y = y →
      G.gradedFrequency f ν hG η y = 0) :
    ∀ x ∈ U.comap (F.associatedGradedMap G φ hφ),
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω s x = x →
        F.gradedFrequency e ω hF (η.comp φ.toLinearMap) x = 0 := by
  intro x hx hpure
  rw [F.gradedFrequency_top_natural G e ω hF f ν hG φ hφ η x hpure]
  apply hzero _ hx
  exact (F.associatedGradedMap_gradeProjection G e ω hF f ν hG φ hφ s x).symm.trans
    (congrArg (F.associatedGradedMap G φ hφ) hpure)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}

theorem homogeneousAssociatedGradedEquiv_pieceMap
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hb : BasisHomogeneousBrackets b ω) (j : ℕ) (x : F.layer j) :
    F.homogeneousAssociatedGradedEquiv b ω hF hb (F.associatedGradedPieceMap j x) =
      basisGradeProjection b ω j x.val :=
  F.associatedGradedPieceMap_repr_symm b ω hF j x

theorem homogeneousAssociatedGradedEquiv_top_piece
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hb : BasisHomogeneousBrackets b ω) (x : F.layer s) :
    F.homogeneousAssociatedGradedEquiv b ω hF hb (F.associatedGradedPieceMap s x) = x.val := by
  rw [F.homogeneousAssociatedGradedEquiv_pieceMap b ω hF hb,
    F.basisGradeProjection_top b ω hF x]

variable (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem homogeneousGradedProjection_top_frequency (η : M →ₗ[ℚ] ℚ)
    (x : F.AssociatedGraded)
    (hx : basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x) :
    η (F.homogeneousGradedProjection G c ν hG hc φ hφ x) =
      F.gradedFrequency b ω hF (η.comp φ.toLinearMap) x := by
  obtain ⟨v, hv⟩ := F.exists_associatedGradedPieceMap_of_pure b ω hF s x hx
  rw [← hv, F.gradedFrequency_top_piece]
  change η (G.homogeneousAssociatedGradedEquiv c ν hG hc
    (F.associatedGradedMap G φ hφ (F.associatedGradedPieceMap s v))) = η (φ v.val)
  rw [F.associatedGradedMap_piece G φ hφ,
    G.homogeneousAssociatedGradedEquiv_top_piece c ν hG hc]

theorem homogeneousGradedProjection_top_frequency_zero
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (η : M →ₗ[ℚ] ℚ)
    (hη : ∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF (η.comp φ.toLinearMap) x = 0)
    {y : M} (hy : y ∈ W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ))
    (htop : y ∈ G.layer s) : η y = 0 := by
  apply graded_image_frequency_zero (F.associatedGradedBasis b ω hF) ω c ν
    (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap s
    (F.homogeneousGradedProjection_gradeProjection G c ν hG hc φ hφ b ω hF s)
    W.toSubmodule hW η ?_ hy (G.basisGradeProjection_top c ν hG ⟨y, htop⟩)
  intro x hx hpure
  exact (F.homogeneousGradedProjection_top_frequency G c ν hG hc φ hφ b ω hF η x hpure).trans
    (hη x hx hpure)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolFastMembership
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

@[simp] theorem adaptedWeightedDilation_coe (w : σ → ℕ) (r : ℚ)
    (p : F.adaptedLieSubalgebra w) :
    (F.adaptedWeightedDilation w r p : VectorPolynomial σ ℚ L) =
      weightedDilation w r (p : VectorPolynomial σ ℚ L) := rfl

theorem polynomialSymbolDilation_repr (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (r : ℚ) (x : F.PolynomialSymbol w) (z : SymbolBasisIndex w ω) :
    (F.polynomialSymbolBasis b ω hF w).repr (F.polynomialSymbolDilation w r x) z =
      r ^ Finsupp.weight w z.val.1 * (F.polynomialSymbolBasis b ω hF w).repr x z := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.polynomialSymbolDilation_map, F.polynomialSymbolBasis_repr_map,
    F.polynomialSymbolBasis_repr_map]
  change b.repr (coefficients (weightedDilation w r (p : VectorPolynomial σ ℚ L)) z.val.1) z.val.2 = _
  rw [coefficients_weightedDilation, map_smul, Finsupp.smul_apply, smul_eq_mul]

noncomputable def realPolynomialSymbolDilation (w : σ → ℕ) (r : ℚ) :
    F.RealPolynomialSymbol w →ₗ⁅ℚ⁆ F.RealPolynomialSymbol w :=
  LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) (F.polynomialSymbolDilation w r)

@[simp] theorem realPolynomialSymbolDilation_tmul (w : σ → ℕ) (r : ℚ)
    (a : ℝ) (x : F.PolynomialSymbol w) :
    F.realPolynomialSymbolDilation w r (a ⊗ₜ[ℚ] x) =
      a ⊗ₜ[ℚ] F.polynomialSymbolDilation w r x := by
  simp only [realPolynomialSymbolDilation, LieAlgebra.ExtendScalars.map_apply_tmul, AlgHom.id_apply]

theorem realPolynomialSymbolDilation_repr (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (r : ℚ) (x : F.RealPolynomialSymbol w) (z : SymbolBasisIndex w ω) :
    ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr (F.realPolynomialSymbolDilation w r x) z =
      (r : ℝ) ^ Finsupp.weight w z.val.1 * ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr x z := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [F.realPolynomialSymbolDilation_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, F.polynomialSymbolDilation_repr]
    simp only [Rat.smul_def, Rat.cast_mul, Rat.cast_pow]
    ring
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, mul_add]

@[simp] theorem realPolynomialSymbolDilation_one (w : σ → ℕ) (x : F.RealPolynomialSymbol w) :
    F.realPolynomialSymbolDilation w 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp only [F.realPolynomialSymbolDilation_tmul, F.polynomialSymbolDilation_one]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realPolynomialSymbolDilation_mul (w : σ → ℕ) (a b : ℚ) (x : F.RealPolynomialSymbol w) :
    F.realPolynomialSymbolDilation w (a * b) x =
      F.realPolynomialSymbolDilation w a (F.realPolynomialSymbolDilation w b x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c x => simp only [F.realPolynomialSymbolDilation_tmul, F.polynomialSymbolDilation_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def realPolynomialSymbolDilationHom (w : σ → ℕ) (r : ℚ) :
    F.RealPolynomialSymbolGroup w →* F.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.realPolynomialSymbolDilation w r)

@[simp] theorem realPolynomialSymbolDilationHom_coord (w : σ → ℕ) (r : ℚ)
    (g : F.RealPolynomialSymbolGroup w) :
    (F.realPolynomialSymbolDilationHom w r g).coord = F.realPolynomialSymbolDilation w r g.coord := rfl

theorem realSymbolOfPolynomial_dilation (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (r : ℚ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    F.realSymbolOfPolynomial b ω hF w (weightedDilation w r p) =
      F.realPolynomialSymbolDilation w r (F.realSymbolOfPolynomial b ω hF w p) := by
  apply ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr.injective
  ext z
  rw [F.realPolynomialSymbolDilation_repr, F.realSymbolOfPolynomial_coordinate,
    F.realSymbolOfPolynomial_coordinate]
  simp only [coefficients_weightedDilation, map_rat_smul, Finsupp.smul_apply,
    Rat.smul_def, Rat.cast_pow]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

def ControlledSymbolFactorization (η : L →ₗ[ℚ] ℚ) (T : σ → ℝ)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) : Prop :=
  ∃ (m : ℕ) (E P R : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : ι → F.AssociatedGraded),
    0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ E * P * R = X ∧
    F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) E ∧
    F.SymbolRationalGrid b ω hF (fun _ => 1) m R ∧
    Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
    BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule ∧
    (∀ i j, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v i) j) ≤ p) ∧
    (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF η x = 0) ∧
    P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF (fun _ => 1) W)

theorem ControlledSymbolFactorization.mono {η : L →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q : ℝ}
    (h : F.ControlledSymbolFactorization b ω hF η T X p) (hpq : p ≤ q)
    (hT : ∀ i, 0 < T i) : F.ControlledSymbolFactorization b ω hF η T X q := by
  obtain ⟨m, E, P, R, W, v, hm, hmp, hprod, hE, hR, hv, hW, hh, hη, hP⟩ := h
  exact ⟨m, E, P, R, W, v, hm, hmp.trans (Real.exp_le_exp.mpr hpq), hprod,
    F.symbolSlowBound_mono b ω hF (fun _ => 1) T hT (Real.exp_le_exp.mpr hpq) E hE,
    hR, hv, hW, (fun i j => (hh i j).trans hpq), hη, hP⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def ControlledSymbolCompositionSpec (s C : ℕ) : Prop :=
  ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i) (η : L →ₗ[ℚ] ℚ)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (A X R : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (_hA : F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) A)
    (_hR : F.SymbolRationalGrid b ω hF (fun _ => 1) l R)
    (_hX : F.ControlledSymbolFactorization b ω hF η T X p),
    F.ControlledSymbolFactorization b ω hF η T (A * X * R) ((p + C) ^ C)

theorem exists_controlled_symbol_composition (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ControlledSymbolCompositionSpec s C := by
  obtain ⟨a, _, hslow⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨b, _, hgrid⟩ := exists_symbol_rational_product_bound s 2
  let P : Polynomial ℕ := Polynomial.X + (2 * Polynomial.X + Polynomial.C a) ^ a +
    (2 * Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF H p hH hp hι hσ hHp hc T hT η l hl hlp A X R hA hR hX
  have hpa : 0 ≤ (2 * p + a) ^ a := by positivity
  have hpb : 0 ≤ (2 * p + b) ^ b := by positivity
  have hbound : p + (2 * p + a) ^ a + (2 * p + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hfinal p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have haC : (2 * p + a) ^ a ≤ (p + C) ^ C := by linarith
  have hbC : (2 * p + b) ^ b ≤ (p + C) ^ C := by linarith
  have h2p : 0 ≤ 2 * p := by positivity
  have hp2 : p ≤ 2 * p := by linarith
  have he2 := Real.exp_le_exp.mpr hp2
  have he : Real.exp p ≤ Real.exp ((2 * p + 2) ^ 1) := Real.exp_le_exp.mpr (by rw [pow_one]; linarith)
  obtain ⟨m, E, Q, B, Z, v, hm, hmp, hprod, hE, hB, hv, hZ, hh, hη, hQ⟩ := hX
  have hleft := hslow F e ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    H (2 * p) hH h2p (hι.trans hp2) (hσ.trans hp2) (hHp.trans he2) hc T hT [A, E] (by simp) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact F.symbolSlowBound_mono e ω hF (fun _ => 1) T hT he _ hA
      · exact F.symbolSlowBound_mono e ω hF (fun _ => 1) T hT he _ hE)
  have hleft' : F.SymbolSlowBound e ω hF (fun _ => 1) T (Real.exp ((2 * p + a) ^ a)) (A * E) := by
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hleft
  have hdenom : ((l * m : ℕ) : ℝ) ≤ Real.exp (2 * p) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hlp hmp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨n, hn, hnp, _, hproducts⟩ := hgrid F e ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    H (2 * p) hH h2p (hι.trans hp2) (hσ.trans hp2) (hHp.trans he2) hc (l * m) (Nat.mul_pos hl hm) hdenom
  have hright := hproducts [B, R] (by simp) (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact F.symbolRationalGrid_mono e ω hF (fun _ => 1) hm (dvd_mul_left m l) _ hB
    · exact F.symbolRationalGrid_mono e ω hF (fun _ => 1) hl (dvd_mul_right l m) _ hR)
  have hright' : F.SymbolRationalGrid e ω hF (fun _ => 1) n (B * R) := by
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hright
  refine ⟨n, A * E, Q, B * R, Z, v, hn, hnp.trans (Real.exp_le_exp.mpr hbC), ?_,
    F.symbolSlowBound_mono e ω hF (fun _ => 1) T hT (Real.exp_le_exp.mpr haC) (A * E) hleft',
    hright', hv, hZ, (fun i j => (hh i j).trans hpC), hη, hQ⟩
  calc
    (A * E) * Q * (B * R) = A * (E * Q * B) * R := by group
    _ = A * X * R := by rw [hprod]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem monomialScale_const_mul {σ : Type*} (S : σ → ℝ) (c : ℝ) (α : σ →₀ ℕ) :
    monomialScale (fun i => c * S i) α =
      c ^ Finsupp.weight (fun _ => 1) α * monomialScale S α := by
  classical
  simp only [monomialScale, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, mul_one]

theorem monomialScale_le_exp_mul {σ : Type*} (S T : σ → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) {q : ℝ} (hq : 0 ≤ q)
    (hST : ∀ i, T i ≤ Real.exp q * S i) (α : σ →₀ ℕ) {s : ℕ}
    (hα : Finsupp.weight (fun _ => 1) α ≤ s) :
    monomialScale T α ≤ Real.exp ((s : ℝ) * q) * monomialScale S α := by
  classical
  calc
    monomialScale T α ≤ monomialScale (fun i => Real.exp q * S i) α := by
      apply Finset.prod_le_prod
      · intro i _
        exact pow_nonneg (hT i).le _
      · intro i _
        exact pow_le_pow_left₀ (hT i).le (hST i) _
    _ = Real.exp q ^ Finsupp.weight (fun _ => 1) α * monomialScale S α :=
      monomialScale_const_mul S (Real.exp q) α
    _ ≤ Real.exp q ^ s * monomialScale S α :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (Real.one_le_exp hq) hα)
        (monomialScale_pos S hS α).le
    _ = Real.exp ((s : ℝ) * q) * monomialScale S α := by rw [Real.exp_nat_mul]

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem symbolSlowBound_rescale (S T : σ → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i)
    {p q : ℝ} (hq : 0 ≤ q) (hST : ∀ i, Real.exp (-q) * T i ≤ S i)
    (E : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hE : F.SymbolSlowBound b ω hF (fun _ => 1) S (Real.exp p) E) :
    F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp (p + (s : ℝ) * q)) E := by
  have hratio (i : σ) : T i ≤ Real.exp q * S i := by
    calc
      T i = Real.exp q * (Real.exp (-q) * T i) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp q * S i := mul_le_mul_of_nonneg_left (hST i) (Real.exp_pos _).le
  intro z
  apply (hE z).trans
  apply (div_le_div_iff₀ (monomialScale_pos S hS z.val.1)
    (monomialScale_pos T hT z.val.1)).mpr
  have hscale := monomialScale_le_exp_mul S T hS hT hq hratio z.val.1
    (z.property.le.trans (F.adaptedBasis_weight_le_step b ω hF z.val.2))
  calc
    Real.exp p * monomialScale T z.val.1 ≤
        Real.exp p * (Real.exp ((s : ℝ) * q) * monomialScale S z.val.1) :=
      mul_le_mul_of_nonneg_left hscale (Real.exp_pos _).le
    _ = Real.exp (p + (s : ℝ) * q) * monomialScale S z.val.1 := by
      rw [Real.exp_add, mul_assoc]

theorem ControlledSymbolFactorization.rescale {η : L →ₗ[ℚ] ℚ} {S T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q : ℝ}
    (h : F.ControlledSymbolFactorization b ω hF η S X p)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i)
    (hq : 0 ≤ q) (hST : ∀ i, Real.exp (-q) * T i ≤ S i) :
    F.ControlledSymbolFactorization b ω hF η T X (p + (s : ℝ) * q) := by
  obtain ⟨m, E, P, R, W, v, hm, hmp, hprod, hE, hR, hv, hW, hh, hη, hP⟩ := h
  have hpq : p ≤ p + (s : ℝ) * q := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg s) hq)
  exact ⟨m, E, P, R, W, v, hm, hmp.trans (Real.exp_le_exp.mpr hpq), hprod,
    F.symbolSlowBound_rescale b ω hF S T hS hT hq hST E hE,
    hR, hv, hW, (fun i j => (hh i j).trans hpq), hη, hP⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

def SymbolFactorizationIn (T : σ → ℝ)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) (l : ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded) : Prop :=
  ∃ E P R : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
    E * P * R = X ∧ F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) E ∧
    F.SymbolRationalGrid b ω hF (fun _ => 1) l R ∧
    P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF (fun _ => 1) W)

theorem ControlledSymbolFactorization.exists_in {η : L →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ}
    (h : F.ControlledSymbolFactorization b ω hF η T X p) :
    ∃ (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded) (u : ι → F.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧ Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule ∧
      (∀ i j, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (u i) j) ≤ p) ∧
      (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
        F.gradedFrequency b ω hF η x = 0) ∧
      F.SymbolFactorizationIn b ω hF T X p l W := by
  obtain ⟨l, E, P, R, W, u, hl, hlp, hprod, hE, hR, hu, hW, hh, hη, hP⟩ := h
  exact ⟨l, W, u, hl, hlp, hu, hW, hh, hη, E, P, R, hprod, hE, hR, hP⟩

theorem SymbolFactorizationIn.mono {T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q : ℝ} {l : ℕ}
    {W : LieSubalgebra ℚ F.AssociatedGraded}
    (h : F.SymbolFactorizationIn b ω hF T X p l W) (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.SymbolFactorizationIn b ω hF T X q l W := by
  obtain ⟨E, P, R, hprod, hE, hR, hP⟩ := h
  exact ⟨E, P, R, hprod,
    F.symbolSlowBound_mono b ω hF (fun _ => 1) T hT (Real.exp_le_exp.mpr hpq) E hE, hR, hP⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

theorem monomialScale_div_const {σ : Type*} (S : σ → ℝ) (c : ℝ) (α : σ →₀ ℕ) :
    monomialScale (fun i => S i / c) α =
      monomialScale S α / c ^ Finsupp.weight (fun _ => 1) α := by
  calc
    _ = monomialScale (fun i => c⁻¹ * S i) α := by
      congr 1
      funext i
      simp only [div_eq_mul_inv, mul_comm]
    _ = c⁻¹ ^ Finsupp.weight (fun _ => 1) α * monomialScale S α := monomialScale_const_mul S c⁻¹ α
    _ = _ := by rw [inv_pow, div_eq_mul_inv, mul_comm]

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem symbolRationalGrid_dilation_ratio (w : σ → ℕ) (D d : ℕ) (a : ℤ) (hd : 0 < d)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w D g) :
    F.SymbolRationalGrid b ω hF w (D * d ^ s)
      (F.realPolynomialSymbolDilationHom w ((a : ℚ) / d) g) := by
  change (fun z => ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
    (F.realPolynomialSymbolDilationHom w ((a : ℚ) / d) g).coord z) ∈ _
  simp_rw [F.realPolynomialSymbolDilationHom_coord, F.realPolynomialSymbolDilation_repr,
    Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  exact realDenominatorGrid_rational_power_scale (fun z : SymbolBasisIndex w ω => Finsupp.weight w z.val.1)
    D d s a hd (fun z => z.property.le.trans (F.adaptedBasis_weight_le_step b ω hF z.val.2)) _ hg

theorem symbolSlowBound_dilation_inverse_scale (S : σ → ℝ) (hS : ∀ i, 0 < S i)
    (p : ℝ) (r : ℚ) (hr : r ≠ 0) (E : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hE : F.SymbolSlowBound b ω hF (fun _ => 1) S (Real.exp p) E) :
    F.SymbolSlowBound b ω hF (fun _ => 1) (fun i => S i / |(r : ℝ)|) (Real.exp p)
      (F.realPolynomialSymbolDilationHom (fun _ => 1) r E) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have habs : 0 < |(r : ℝ)| := abs_pos.mpr hrR
  intro z
  rw [F.realPolynomialSymbolDilationHom_coord, F.realPolynomialSymbolDilation_repr, abs_mul, abs_pow]
  apply (mul_le_mul_of_nonneg_left (hE z) (pow_nonneg habs.le _)).trans_eq
  rw [monomialScale_div_const]
  field_simp [(monomialScale_pos S hS z.val.1).ne', habs.ne']

theorem symbolSlowBound_dilation_physical (S T : σ → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) (p q : ℝ) (hq : 0 ≤ q)
    (r : ℚ) (hr : r ≠ 0)
    (hphysical : ∀ i, Real.exp (-q) * (|(r : ℝ)| * T i) ≤ S i)
    (E : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hE : F.SymbolSlowBound b ω hF (fun _ => 1) S (Real.exp p) E) :
    F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp (p + (s : ℝ) * q))
      (F.realPolynomialSymbolDilationHom (fun _ => 1) r E) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have habs : 0 < |(r : ℝ)| := abs_pos.mpr hrR
  have hscaled := F.symbolSlowBound_dilation_inverse_scale b ω hF S hS p r hr E hE
  apply F.symbolSlowBound_rescale b ω hF (fun i => S i / |(r : ℝ)|) T
    (fun i => div_pos (hS i) habs) hT hq _ _ hscaled
  intro i
  apply (le_div_iff₀ habs).mpr
  calc
    Real.exp (-q) * T i * |(r : ℝ)| = Real.exp (-q) * (|(r : ℝ)| * T i) := by ring
    _ ≤ S i := hphysical i

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def SymbolFastIn {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (g : F.RealPolynomialSymbolGroup w) : Prop :=
  g.coord ∈ realificationLieSubalgebra U

theorem SymbolFactorizationIn.exists_fast_factors {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {T : σ → ℝ} {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ} {l : ℕ}
    {W : LieSubalgebra ℚ F.AssociatedGraded}
    (h : F.SymbolFactorizationIn b ω hF T X p l W) :
    ∃ E P R : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
      E * P * R = X ∧ F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) E ∧
      F.SymbolRationalGrid b ω hF (fun _ => 1) l R ∧
      F.SymbolFastIn (fun _ => 1) (F.symbolPointwiseSubalgebra b ω hF (fun _ => 1) W) P := h

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RealSymbolAffine
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realSymbolOfPolynomial_translate (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hp : F.realification.Adapted w p) :
    F.realSymbolOfPolynomial b ω hF w (translate h p) = F.realSymbolOfPolynomial b ω hF w p := by
  let q : F.realification.adaptedLieSubalgebra w :=
    ⟨p, (F.realification.mem_adaptedSubmodule w p).mpr hp⟩
  let q' : F.realification.adaptedLieSubalgebra w :=
    ⟨translate h p, (F.realification.mem_adaptedSubmodule w _).mpr
      (F.realification.adapted_translate w hw h hp)⟩
  exact (F.realSymbolOfPolynomial_eq_iff_symbolMap_eq b ω hF w q' q).mpr
    (F.realification.polynomialSymbolMap_translate w hw h q)

theorem realSymbolOfPolynomial_affine (hw : ∀ i, 0 < w i) (h : σ → ℚ) (r : ℚ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hp : F.realification.Adapted w p) :
    F.realSymbolOfPolynomial b ω hF w (weightedDilation w r (translate h p)) =
      F.realPolynomialSymbolDilation w r (F.realSymbolOfPolynomial b ω hF w p) := by
  rw [F.realSymbolOfPolynomial_dilation, F.realSymbolOfPolynomial_translate b ω hF w hw h p hp]

theorem realGradedSymbolPolynomial_dilation_coefficient (r : ℚ)
    (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (F.realGradedSymbolPolynomial b ω hF w (F.realPolynomialSymbolDilation w r x)) α =
      (r : ℝ) ^ Finsupp.weight w α • coefficients (F.realGradedSymbolPolynomial b ω hF w x) α := by
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [map_smul, Finsupp.smul_apply]
  by_cases h : Finsupp.weight w α = ω i
  · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(α, i), h⟩,
      F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(α, i), h⟩,
      F.realPolynomialSymbolDilation_repr]
    rfl
  · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w _ α i h,
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w _ α i h, smul_zero]

theorem realSymbolDilation_mem_pointwise (U : LieSubalgebra ℚ F.AssociatedGraded)
    (r : ℚ) (x : F.RealPolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U)) :
    F.realPolynomialSymbolDilation w r x ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) := by
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients b ω hF w U _).mpr
  intro α
  rw [F.realGradedSymbolPolynomial_dilation_coefficient]
  exact (realificationLieSubalgebra U).smul_mem _
    ((F.mem_real_symbolPointwiseSubalgebra_iff_coefficients b ω hF w U x).mp hx α)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveReconstruction
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def positiveClip (z : ℂ) : ℂ := (max 0 (min 1 z.re) : ℝ)

theorem positiveClip_unit_interval (z : ℂ) :
    (positiveClip z).im = 0 ∧ 0 ≤ (positiveClip z).re ∧ (positiveClip z).re ≤ 1 := by
  refine ⟨rfl, le_max_left _ _, ?_⟩
  exact max_le (by norm_num) (min_le_left _ _)

theorem positiveClip_eq_self (z : ℂ) (hz : z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1) :
    positiveClip z = z := by
  apply Complex.ext
  · change max 0 (min 1 z.re) = z.re
    rw [min_eq_right hz.2.2, max_eq_right hz.2.1]
  · exact hz.1.symm

theorem positiveClip_lipschitz : LipschitzWith 1 positiveClip := by
  change LipschitzWith 1 (fun z : ℂ => ((max 0 (min 1 z.re) : ℝ) : ℂ))
  have h : LipschitzWith 1 (fun z : ℂ => max 0 (min 1 z.re)) :=
    ((RCLike.lipschitzWith_re (K := ℂ)).const_min 1).const_max 0
  simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitz.comp h

theorem norm_positiveClip_le_one (z : ℂ) : ‖positiveClip z‖ ≤ 1 := by
  change ‖((max 0 (min 1 z.re) : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
  exact (positiveClip_unit_interval z).2.2

theorem exists_positive_lipschitz_reconstruction {X Y : Type*} [PseudoMetricSpace Y]
    (f : X → ℂ) (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1)
    (φ : X → Y) (v : Y → ℂ) {K : ℝ≥0} (hv : LipschitzWith K v)
    (heval : ∀ x, v (φ x) = f x) :
    ∃ u : Y → ℂ, LipschitzWith K u ∧
      (∀ y, (u y).im = 0 ∧ 0 ≤ (u y).re ∧ (u y).re ≤ 1) ∧
      (∀ y, ‖u y‖ ≤ 1) ∧ ∀ x, u (φ x) = f x := by
  refine ⟨fun y => positiveClip (v y), ?_, fun y => positiveClip_unit_interval (v y),
    fun y => norm_positiveClip_le_one (v y), ?_⟩
  · simpa only [one_mul, Function.comp_def] using positiveClip_lipschitz.comp hv
  · intro x
    change positiveClip (v (φ x)) = f x
    rw [heval, positiveClip_eq_self _ (hf x)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPhasePointBounds
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {B : Type*} [Fintype B]

theorem translationPhaseArgument_left_increment_point_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hdegree : D₀.totalDegree ≤ d)
    (hres : ∀ i, |β i - g.base i| ≤ 1)
    (hnew : ∀ i, |β i - g.base i - z.base i| ≤ 1)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (hp : |eval (β - g.base) z.polynomial| ≤ ε) :
    |translationPhaseArgument D₀ (z * g) β - translationPhaseArgument D₀ g β| ≤
      (1 + realPolynomialMass D₀ * Fintype.card B * d) * ε := by
  rw [translationPhaseArgument_left_increment]
  have hdiff (i : B) : |(β - g.base - z.base) i - (β - g.base) i| ≤ ε := by
    change |β i - g.base i - z.base i - (β i - g.base i)| ≤ ε
    rw [show β i - g.base i - z.base i - (β i - g.base i) = -z.base i by ring,
      abs_neg]
    exact hbase i
  have hD : |eval (β - g.base - z.base) D₀ - eval (β - g.base) D₀| ≤
      realPolynomialMass D₀ * Fintype.card B * d * ε := by
    have h := abs_aeval_sub_aeval_mass_box_bound D₀
      (β - g.base - z.base) (β - g.base) (B := 1)
      le_rfl hε hnew hres hdiff hdegree
    simpa only [MvPolynomial.aeval_eq_eval, one_pow, mul_one] using h
  calc
    _ ≤ |eval (β - g.base) z.polynomial| +
      |eval (β - g.base - z.base) D₀ - eval (β - g.base) D₀| := abs_add_le _ _
    _ ≤ ε + realPolynomialMass D₀ * Fintype.card B * d * ε := add_le_add hp hD
    _ = _ := by ring

theorem translationPhaseArgument_left_increment_point_mass_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε M : ℝ} (hε : 0 ≤ ε)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (hres : ∀ i, |β i - g.base i| ≤ 1)
    (hnew : ∀ i, |β i - g.base i - z.base i| ≤ 1)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (hp : |eval (β - g.base) z.polynomial| ≤ ε) :
    |translationPhaseArgument D₀ (z * g) β - translationPhaseArgument D₀ g β| ≤
      (1 + M * Fintype.card B * d) * ε := by
  apply (translationPhaseArgument_left_increment_point_bound D₀ z g β hε hdegree
    hres hnew hbase hp).trans
  gcongr

theorem translationPhaseCharacter_left_increment_point_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε M : ℝ} (hε : 0 ≤ ε)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (hres : ∀ i, |β i - g.base i| ≤ 1)
    (hnew : ∀ i, |β i - g.base i - z.base i| ≤ 1)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (hp : |eval (β - g.base) z.polynomial| ≤ ε) :
    ‖(Real.fourierChar (translationPhaseArgument D₀ (z * g) β) : ℂ) -
      (Real.fourierChar (translationPhaseArgument D₀ g β) : ℂ)‖ ≤
      (2 * Real.pi) * (1 + M * Fintype.card B * d) * ε := by
  have hphase := translationPhaseArgument_left_increment_point_mass_bound D₀ z g β
    hε hdegree hD hres hnew hbase hp
  exact (real_fourierChar_norm_sub_le _ _).trans
    ((mul_le_mul_of_nonneg_left hphase (by positivity)).trans_eq (by ring))

omit [Fintype B] in

theorem translation_residual_unit_boxes_of_quarter
    (z g : PolynomialTranslationGroupOver ℝ B) (β : B → ℝ) {ε : ℝ}
    (hε : ε ≤ 1 / 4) (hres : ∀ i, |β i - g.base i| ≤ 1 / 4)
    (hbase : ∀ i, |z.base i| ≤ ε) :
    (∀ i, |β i - g.base i| ≤ 1) ∧
      ∀ i, |β i - g.base i - z.base i| ≤ 1 := by
  constructor
  · intro i
    exact (hres i).trans (by norm_num)
  · intro i
    apply (abs_sub _ _).trans
    have hr := hres i
    have hz := hbase i
    linarith

theorem translationPhaseCharacter_left_increment_quarter_point_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε M : ℝ} (hε : 0 ≤ ε) (hεquarter : ε ≤ 1 / 4)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (hres : ∀ i, |β i - g.base i| ≤ 1 / 4)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (hp : |eval (β - g.base) z.polynomial| ≤ ε) :
    ‖(Real.fourierChar (translationPhaseArgument D₀ (z * g) β) : ℂ) -
      (Real.fourierChar (translationPhaseArgument D₀ g β) : ℂ)‖ ≤
      (2 * Real.pi) * (1 + M * Fintype.card B * d) * ε := by
  obtain ⟨hres', hnew⟩ := translation_residual_unit_boxes_of_quarter z g β hεquarter hres hbase
  exact translationPhaseCharacter_left_increment_point_bound D₀ z g β
    hε hdegree hD hres' hnew hbase hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.OrdinarySymbolBasisDimension
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem homogeneousSymbolLift_mem_pointwise (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω U.toSubmodule)
    (α : σ →₀ ℕ) (v : F.AssociatedGraded) (hv : v ∈ U) :
    F.homogeneousSymbolLift b ω hlayers w α v ∈ F.symbolPointwiseSubalgebra b ω hlayers w U := by
  classical
  rw [F.mem_symbolPointwiseSubalgebra_iff]
  intro β
  rw [F.gradedSymbolPolynomial_homogeneousSymbolLift, coefficients_monomial]
  by_cases h : α = β
  · subst β
    rw [Finsupp.single_eq_same]
    exact hU (Finsupp.weight w α) v hv
  · rw [Finsupp.single_eq_of_ne (Ne.symm h)]
    exact U.zero_mem

noncomputable def pointwiseSymbolSpanningFamily (v : κ → F.AssociatedGraded) :
    SymbolBasisIndex w ω × κ → F.PolynomialSymbol w :=
  fun z => F.homogeneousSymbolLift b ω hlayers w z.1.val.1 (v z.2)

theorem pointwiseSymbolSpanningFamily_span [Fintype (SymbolBasisIndex w ω)]
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω U.toSubmodule)
    (v : κ → F.AssociatedGraded) (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) :
    Submodule.span ℚ (Set.range (F.pointwiseSymbolSpanningFamily b ω hlayers w v)) =
      (F.symbolPointwiseSubalgebra b ω hlayers w U).toSubmodule := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    apply F.homogeneousSymbolLift_mem_pointwise b ω hlayers w U hU
    change v z.2 ∈ U.toSubmodule
    rw [← hspan]
    exact Submodule.subset_span ⟨z.2, rfl⟩
  · intro x hx
    rw [← sum_basisBlockProjection (F.polynomialSymbolBasis b ω hlayers w) (fun z => z.val.1) x]
    apply Submodule.sum_mem
    intro α hα
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hα
    rw [← F.homogeneousSymbolLift_coefficient]
    let W := Submodule.span ℚ (Set.range (F.pointwiseSymbolSpanningFamily b ω hlayers w v))
    have hmap : U.toSubmodule ≤ W.comap (F.homogeneousSymbolLift b ω hlayers w z.val.1) := by
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨(z, j), rfl⟩
    exact hmap ((F.mem_symbolPointwiseSubalgebra_iff b ω hlayers w U x).mp hx z.val.1)

theorem pointwiseSymbolSpanningFamily_height (v : κ → F.AssociatedGraded) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hlayers).repr (v j) i) H) :
    ∀ z i, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr
      (F.pointwiseSymbolSpanningFamily b ω hlayers w v z) i) H := by
  classical
  intro z i
  change RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr
    (F.homogeneousSymbolLift b ω hlayers w z.1.val.1 (v z.2)) i) H
  rw [F.homogeneousSymbolLift_coordinate]
  split_ifs
  · exact hv z.2 i.val.2
  · exact rationalHeightLE_zero hH

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def pointwiseFastSectionInput (s : ℕ) (p : ℝ) : ℝ :=
  2 * (p + (s + 3)) ^ (s + 3) + ((p + (s + 3)) ^ (s + 3)) ^ 2 + p

theorem pointwiseFastSectionInput_ge (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ pointwiseFastSectionInput s p := by
  unfold pointwiseFastSectionInput
  exact le_add_of_nonneg_left (by positivity)

theorem symbolBasisIndex_card_le_spanning_budget
    {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) [Fintype (SymbolBasisIndex w ω)]
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) :
    (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ (p + (s + 3)) ^ (s + 3) := by
  apply (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
    (F.adaptedBasis_weight_le_step b ω hF))).trans
  apply (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ).trans
  apply (pow_le_pow_left₀ (by positivity : 0 ≤ p + (s + 2))
    (by linarith : p + (s + 2 : ℝ) ≤ p + (s + 3)) (s + 2)).trans
  exact pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) s; linarith) (by omega)

theorem pointwiseSymbolSpanning_section_counts
    {σ ι κ ξ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype ξ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (SymbolBasisIndex w ω)] [Fintype (SymbolBasisIndex w τ)]
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hξ : (Fintype.card ξ : ℝ) ≤ p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) :
    (Fintype.card (SymbolBasisIndex w ω × ξ) : ℝ) ≤ pointwiseFastSectionInput s p ∧
    (Fintype.card (SymbolBasisIndex w ω ⊕ SymbolBasisIndex w τ) : ℝ) ≤
      pointwiseFastSectionInput s p ∧
    ((Fintype.card (SymbolBasisIndex w ω) *
      Fintype.card (SymbolBasisIndex w ω × ξ) : ℕ) : ℝ) ≤ pointwiseFastSectionInput s p := by
  let A : ℝ := (p + (s + 3)) ^ (s + 3)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb := F.symbolBasisIndex_card_le_spanning_budget b ω hF w hw hp hι hσ
  have hc := G.symbolBasisIndex_card_le_spanning_budget c τ hG w hw hp hκ hσ
  have hv : (Fintype.card (SymbolBasisIndex w ω × ξ) : ℝ) ≤ A := by
    have hnat : Fintype.card (SymbolBasisIndex w ω × ξ) ≤
        Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s * Fintype.card ξ := by
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul_right _ (symbolBasisIndex_card_le w ω s hw
        (F.adaptedBasis_weight_le_step b ω hF))
    exact (Nat.cast_le.mpr hnat).trans (symbol_spanning_count_bound s _ _ _ hp hι hσ hξ)
  have hrows : (Fintype.card (SymbolBasisIndex w ω ⊕ SymbolBasisIndex w τ) : ℝ) ≤ 2 * A := by
    rw [Fintype.card_sum, Nat.cast_add]
    dsimp only [A]
    linarith
  have hcols : ((Fintype.card (SymbolBasisIndex w ω) *
      Fintype.card (SymbolBasisIndex w ω × ξ) : ℕ) : ℝ) ≤ A ^ 2 := by
    rw [Nat.cast_mul, pow_two]
    exact mul_le_mul hb hv (Nat.cast_nonneg _) hA
  change _ ≤ 2 * A + A ^ 2 + p ∧ _ ≤ 2 * A + A ^ 2 + p ∧ _ ≤ 2 * A + A ^ 2 + p
  refine ⟨hv.trans ?_, hrows.trans ?_, hcols.trans ?_⟩ <;> nlinarith [sq_nonneg A]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype σ] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

@[instance_reducible] noncomputable def ordinarySymbolBasisFintype :
    Fintype (SymbolBasisIndex (fun _ : σ => 1) ω) :=
  symbolBasisIndexFintype (fun _ : σ => 1) ω s (fun _ => Nat.zero_lt_one)
    (F.adaptedBasis_weight_le_step b ω hF)

include hF

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SimultaneousPolynomialSymbolSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

@[simp] theorem realPolynomialSymbolLift_log (g : F.RealPolynomialSymbolGroup w) :
    ((F.realPolynomialSymbolLift b ω hlayers w g).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) = F.realSymbolRepresentative b ω hlayers w g.coord := rfl

theorem exists_realPolynomial_symbol_factorization
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E P R : F.RealPolynomialSymbolGroup w)
    (h : E * P * R = F.realPolynomialSymbolHom b ω hlayers w g) :
    ∃ e p r : (F.realification.adaptedPolynomialFiltration w).Group,
      e * p * r = g ∧
      (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) = F.realSymbolRepresentative b ω hlayers w E.coord ∧
      (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) = F.realSymbolRepresentative b ω hlayers w R.coord ∧
      F.realPolynomialSymbolHom b ω hlayers w p = P := by
  let e := F.realPolynomialSymbolLift b ω hlayers w E
  let r := F.realPolynomialSymbolLift b ω hlayers w R
  refine ⟨e, e⁻¹ * g * r⁻¹, r, ?_, rfl, rfl, ?_⟩
  · simp [mul_assoc]
  · rw [map_mul, map_mul, map_inv, map_inv, ← h]
    simp [e, r, mul_assoc]

theorem exists_realPolynomial_controlled_symbol_factorization
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M) (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E P R : F.RealPolynomialSymbolGroup w)
    (h : E * P * R = F.realPolynomialSymbolHom b ω hlayers w g)
    (hE : F.SymbolSlowBound b ω hlayers w T M E)
    (hR : F.SymbolRationalGrid b ω hlayers w l R) :
    ∃ e p r : (F.realification.adaptedPolynomialFiltration w).Group,
      e * p * r = g ∧
      F.realPolynomialSymbolHom b ω hlayers w p = P ∧
      (∀ α i, |(b.baseChange ℝ).repr
        (coefficients (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
          M / monomialScale T α) ∧
      ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
        (coefficients (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈
          realDenominatorGrid l) ∧
      coefficients (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
      coefficients (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
      coefficients (p.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
        coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  obtain ⟨e, p, r, hepr, he, hr, hp⟩ :=
    F.exists_realPolynomial_symbol_factorization b ω hlayers w g E P R h
  have he0 : coefficients (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
    rw [he]
    exact F.realSymbolRepresentative_constant b ω hlayers w E.coord
  have hr0 : coefficients (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
    rw [hr]
    exact F.realSymbolRepresentative_constant b ω hlayers w R.coord
  refine ⟨e, p, r, hepr, hp, ?_, ?_, he0, hr0,
    F.realification.polynomial_factor_middle_constant w g e p r hepr he0 hr0⟩
  · rw [he]
    exact F.realSymbolRepresentative_slow_coefficients b ω hlayers w T hT hM E hE
  · rw [hr]
    exact F.realSymbolRepresentative_rational_coefficients b ω hlayers w l R hR

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_simultaneous_polynomial_symbol_splitting (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ η L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : η → LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : η → κ → F.PolynomialSymbol w),
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisBlockInvariant (F.polynomialSymbolBasis b ω hlayers w)
        (fun z => z.val.1) (U j).toSubmodule) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p → (Fintype.card η : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      (∀ j i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v j i) z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
        (E P R : η → F.RealPolynomialSymbolGroup w),
      (∀ j, E j * P j * R j = F.realPolynomialSymbolHom b ω hlayers w g) →
      (∀ j, (P j).coord ∈ realificationLieSubalgebra (U j)) →
      (∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) (E j)) →
      (∀ j, F.SymbolRationalGrid b ω hlayers w l (R j)) →
      ∃ (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration w).Group),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ l ∣ m ∧
        e₀ * p₀ * r₀ = g ∧
        (F.realPolynomialSymbolHom b ω hlayers w p₀).coord ∈
          realificationLieSubalgebra (⨅ j, U j) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈
            realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  obtain ⟨C, hC, hsplit⟩ := exists_simultaneous_symbol_splitting s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ η L _ _ _ _ _ _ F b ω hlayers w hw U v hspan hblock H l p hH hl hp
    hι hσ hκ hη hHp hlp hb hv T hT g E P R hX hP hE hR
  obtain ⟨m, E₀, P₀, R₀, hm, hmp, hlm, hprod, hmid, hslow, hrat⟩ :=
    hsplit F b ω hlayers w hw U v hspan hblock H l p hH hl hp
      hι hσ hκ hη hHp hlp hb hv T hT (F.realPolynomialSymbolHom b ω hlayers w g)
      E P R hX hP hE hR
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  obtain ⟨e₀, p₀, r₀, hepr, hp₀, he, hr, he0, hr0, hp0⟩ :=
    F.exists_realPolynomial_controlled_symbol_factorization b ω hlayers w T hTpos
      (Real.exp_nonneg _) m g E₀ P₀ R₀ hprod hslow hrat
  refine ⟨m, e₀, p₀, r₀, hm, hmp, hlm, hepr, ?_, he, hr, he0, hr0, hp0⟩
  rw [hp₀]
  exact hmid

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefilteredPointwiseSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (U : LieSubalgebra ℚ F.AssociatedGraded)

noncomputable def realGradedRefiltrationLayer (j : ℕ) : Submodule ℝ (ℝ ⊗[ℚ] L) :=
  (F.gradedRefiltrationLayer U j).baseChange ℝ

theorem realGradedRefiltrationLayer_antitone : Antitone (F.realGradedRefiltrationLayer U) :=
  fun _ _ hij => Submodule.baseChange_mono ℝ (F.gradedRefiltrationLayer_antitone U hij)

theorem realGradedRefiltrationLayer_le (j : ℕ) :
    F.realGradedRefiltrationLayer U j ≤ (F.realLayer j).toSubmodule :=
  Submodule.baseChange_mono ℝ (F.gradedRefiltrationLayer_le U j)

theorem realGradedRefiltrationLayer_lie_mem {i j : ℕ} {v z : ℝ ⊗[ℚ] L}
    (hv : v ∈ F.realGradedRefiltrationLayer U i) (hz : z ∈ F.realGradedRefiltrationLayer U j) :
    ⁅v, z⁆ ∈ F.realGradedRefiltrationLayer U (i + j) :=
  lie_mem_real_baseChange _ _ _ (fun _ ha _ hb => F.gradedRefiltrationLayer_lie_mem U ha hb) hv hz

theorem realGradedRefiltrationLayer_terminal : F.realGradedRefiltrationLayer U (s + 1) = ⊥ := by
  rw [realGradedRefiltrationLayer, F.gradedRefiltrationLayer_terminal, Submodule.baseChange_bot]

noncomputable def realGradedRefiltrationSubalgebra : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
  realLieSubalgebraOverRat (realificationLieSubalgebra (F.gradedRefiltrationSubalgebra U))

theorem mem_realGradedRefiltrationSubalgebra (v : ℝ ⊗[ℚ] L) :
    v ∈ F.realGradedRefiltrationSubalgebra U ↔ v ∈ F.realGradedRefiltrationLayer U 1 := Iff.rfl

noncomputable def realGradedRefiltration :
    NilpotentLieFiltration (F.realGradedRefiltrationSubalgebra U) s where
  layer j := ((F.realGradedRefiltrationLayer U j).restrictScalars ℚ).comap
    (F.realGradedRefiltrationSubalgebra U).incl.toLinearMap
  antitone := fun _ _ hij _ hv => F.realGradedRefiltrationLayer_antitone U hij hv
  one_eq_top := by
    apply top_unique
    intro v _
    exact v.property
  lie_mem := fun hv hz => F.realGradedRefiltrationLayer_lie_mem U hv hz
  terminal := by
    apply bot_unique
    intro v hv
    change v = 0
    apply Subtype.ext
    exact (Submodule.mem_bot ℝ).mp ((F.realGradedRefiltrationLayer_terminal U) ▸ hv)

@[simp] theorem mem_realGradedRefiltration_layer (j : ℕ)
    (v : F.realGradedRefiltrationSubalgebra U) :
    v ∈ (F.realGradedRefiltration U).layer j ↔
      (v : ℝ ⊗[ℚ] L) ∈ F.realGradedRefiltrationLayer U j := Iff.rfl

theorem mem_realGradedRefiltrationLayer_iff {ι : Type*} (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (j : ℕ) (v : ℝ ⊗[ℚ] L) :
    v ∈ F.realGradedRefiltrationLayer U j ↔ v ∈ F.realification.layer j ∧
      (F.gradedPieceProjection b ω hlayers j).baseChange ℝ v ∈ realificationLieSubalgebra U := by
  rw [realGradedRefiltrationLayer, F.gradedRefiltrationLayer_eq_inf_comap b ω hlayers,
    realification_inf, realification_comap, Submodule.mem_inf, Submodule.mem_comap]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)

theorem real_symbol_values_iff_refiltration_coefficients
    (p : F.realification.adaptedLieSubalgebra w) :
    (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realPolynomialSymbolMap b ω hlayers w p)) ∈ realificationLieSubalgebra U) ↔
    ∀ α, coefficients (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      F.realGradedRefiltrationLayer U (Finsupp.weight w α) := by
  refine (eval₂_mem_iff_coefficients (realificationLieSubalgebra U).toSubmodule _).trans ?_
  apply forall_congr'
  intro α
  rw [F.mem_realGradedRefiltrationLayer_iff U b ω hlayers,
    F.realPolynomialSymbolMap_apply, F.realGradedSymbolPolynomial_coefficient_of_polynomial]
  exact (and_iff_right (p.property α)).symm

theorem normalized_refiltration_coefficients_mem_first
    (hw : ∀ i, 0 < w i) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer U (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) :
    ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer U 1 := by
  intro α
  by_cases hα : α = 0
  · rw [hα, hzero]
    exact (F.realGradedRefiltrationLayer U 1).zero_mem
  · exact F.realGradedRefiltrationLayer_antitone U (positive_weight_of_ne_zero w hw hα) (hp α)

theorem exists_refiltered_polynomial_of_coefficients (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer U (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) :
    ∃ q : VectorPolynomial σ ℚ (F.realGradedRefiltrationSubalgebra U),
      (F.realGradedRefiltration U).Adapted w q ∧
      VectorPolynomial.map (F.realGradedRefiltrationSubalgebra U).incl.toLinearMap q = p ∧
      coefficients q 0 = 0 := by
  have hfirst := F.normalized_refiltration_coefficients_mem_first w U hw p hp hzero
  have hcoeff : ∀ α, coefficients p α ∈ (F.realGradedRefiltrationSubalgebra U).toSubmodule := by
    intro α
    exact (F.mem_realGradedRefiltrationSubalgebra U _).mpr (hfirst α)
  let q := restrictCoefficients (F.realGradedRefiltrationSubalgebra U).toSubmodule p hcoeff
  have hq (α : σ →₀ ℕ) : (coefficients q α : ℝ ⊗[ℚ] L) = coefficients p α :=
    coefficients_restrictCoefficients (F.realGradedRefiltrationSubalgebra U).toSubmodule p hcoeff α
  refine ⟨q, ?_, map_restrictCoefficients (F.realGradedRefiltrationSubalgebra U).toSubmodule p hcoeff, ?_⟩
  · apply ((F.realGradedRefiltration U).adapted_iff_coefficients w q).mpr
    intro α
    rw [F.mem_realGradedRefiltration_layer, hq]
    exact hp α
  · apply Subtype.ext
    exact (hq 0).trans hzero

theorem pointwise_refiltered_values_mem (hw : ∀ i, 0 < w i)
    (p : F.realification.adaptedLieSubalgebra w)
    (hzero : coefficients (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0)
    (hU : ∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realPolynomialSymbolMap b ω hlayers w p)) ∈ realificationLieSubalgebra U) :
    ∀ t : σ → ℝ, eval₂ t (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
      realificationLieSubalgebra (F.gradedRefiltrationSubalgebra U) := by
  apply (eval₂_mem_iff_coefficients
    (realificationLieSubalgebra (F.gradedRefiltrationSubalgebra U)).toSubmodule _).mpr
  exact F.normalized_refiltration_coefficients_mem_first w U hw p
    ((F.real_symbol_values_iff_refiltration_coefficients b ω hlayers w U p).mp hU) hzero

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_pointwise_polynomial_symbol_splitting (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ η L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : η → LieSubalgebra ℚ F.AssociatedGraded) (v : η → κ → F.AssociatedGraded),
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω (U j).toSubmodule) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p → (Fintype.card η : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ j i k, RationalHeightLE ((F.associatedGradedBasis b ω hlayers).repr (v j i) k) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
        (E P R : η → F.RealPolynomialSymbolGroup w),
      (∀ j, E j * P j * R j = F.realPolynomialSymbolHom b ω hlayers w g) →
      (∀ j, ∀ t : σ → ℝ,
        eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w (P j).coord) ∈ realificationLieSubalgebra (U j)) →
      (∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) (E j)) →
      (∀ j, F.SymbolRationalGrid b ω hlayers w l (R j)) →
      ∃ (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration w).Group),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ l ∣ m ∧
        e₀ * p₀ * r₀ = g ∧
        (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
          (F.realPolynomialSymbolHom b ω hlayers w p₀).coord) ∈ realificationLieSubalgebra (⨅ j, U j)) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  obtain ⟨K, hK, hsplit⟩ := exists_simultaneous_polynomial_symbol_splitting s a
  let C := max 2 (((s + 4) * (s + 3) + 2) * K)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro σ ι κ η L _ _ _ _ _ _ F b ω hlayers w hw U v hspan hgraded H l p hH hl hp
    hι hσ hκ hη hHp hlp hb hv T hT g E P R hX hP hE hR
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let V := fun j => F.symbolPointwiseSubalgebra b ω hlayers w (U j)
  let v' := fun j => F.pointwiseSymbolSpanningFamily b ω hlayers w (v j)
  let q : ℝ := (p + (s + 3)) ^ (s + 3)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := symbol_spanning_parameter_ge s hp
  have hcount : (Fintype.card (SymbolBasisIndex w ω × κ) : ℝ) ≤ q := by
    have hnat : Fintype.card (SymbolBasisIndex w ω × κ) ≤
        Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s * Fintype.card κ := by
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul_right _ (symbolBasisIndex_card_le w ω s hw
        (F.adaptedBasis_weight_le_step b ω hlayers))
    exact (Nat.cast_le.mpr hnat).trans
      (symbol_spanning_count_bound s _ _ _ hp hι hσ hκ)
  have hcost : (q + 2) ^ K ≤ (p + 2) ^ C := by
    apply (symbol_spanning_parameter_power_bound s K hp).trans
    apply pow_le_pow_right₀ (by linarith only [hp] : 1 ≤ p + 2)
    exact le_max_right _ _
  have hcostexp := Real.exp_le_exp.mpr hcost
  have hTq : ∀ i, Real.exp ((q + 2) ^ K) ≤ T i := fun i => hcostexp.trans (hT i)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hP' : ∀ j, (P j).coord ∈ realificationLieSubalgebra (V j) := by
    intro j
    exact (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hlayers w (U j) _).mpr (hP j)
  have hE' : ∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((q + 2) ^ a)) (E j) := by
    intro j
    apply F.symbolSlowBound_mono b ω hlayers w T hTpos _ (E j) (hE j)
    exact Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (add_le_add hpq (le_refl 2)) a)
  obtain ⟨m, e₀, p₀, r₀, hm, hmp, hlm, hepr, hmid, he, hr, he0, hr0, hp0⟩ :=
    hsplit F b ω hlayers w hw V v'
      (fun j => F.pointwiseSymbolSpanningFamily_span b ω hlayers w (U j) (hgraded j) (v j) (hspan j))
      (fun j => F.symbolPointwiseSubalgebra_blockInvariant b ω hlayers w (U j))
      H l q hH hl hq (hι.trans hpq) (hσ.trans hpq) hcount (hη.trans hpq)
      (hHp.trans (Real.exp_le_exp.mpr hpq)) (hlp.trans (Real.exp_le_exp.mpr hpq)) hb
      (fun j => F.pointwiseSymbolSpanningFamily_height b ω hlayers w (v j) hH (hv j))
      T hTq g E P R hX hP' hE' hR
  refine ⟨m, e₀, p₀, r₀, hm, hmp.trans hcostexp, hlm, hepr, ?_, ?_, hr, he0, hr0, hp0⟩
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hlayers w (⨅ j, U j) _).mp
    rw [F.symbolPointwiseSubalgebra_iInf]
    exact hmid
  · intro α i
    exact (he α i).trans
      (div_le_div_of_nonneg_right hcostexp (monomialScale_pos T hTpos α).le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_common_polynomial_step_drop_factors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J L : Type*} [Fintype σ] [Fintype ι] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (eta : J → L →ₗ[ℚ] ℚ) (p : ℝ), 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (b.repr ⁅b i, b j⁆ k) ≤ p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, F.ControlledSymbolFactorization b ω hF (eta j) T
        (F.realPolynomialSymbolHom b ω hF (fun _ => 1) g) p) →
      ∃ (U : J → LieSubalgebra ℚ F.AssociatedGraded) (v : J → ι → F.AssociatedGraded)
        (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) ∧
        (∀ j, BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω (U j).toSubmodule) ∧
        (∀ j i k, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v j i) k) ≤ p) ∧
        (∀ j x, x ∈ (⨅ j, U j) → basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
          F.gradedFrequency b ω hF (eta j) x = 0) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ e₀ * p₀ * r₀ = g ∧
        (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hF (fun _ => 1)
          (F.realPolynomialSymbolHom b ω hF (fun _ => 1) p₀).coord) ∈
            realificationLieSubalgebra (⨅ j, U j)) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  obtain ⟨K, hK, hsplit⟩ := exists_pointwise_polynomial_symbol_splitting s 1
  refine ⟨2 * K, by omega, ?_⟩
  intro σ ι J L _ _ _ _ _ F b ω hF eta p hp hι hσ hJ hstructure T hT g hfactor
  classical
  choose m E P R U v hm hmp hprod hE hR hv hU hheight hfreq hP using hfactor
  let l := ∏ j, m j
  have hl : 0 < l := Finset.prod_pos (fun j _ => hm j)
  have hdvd (j : J) : m j ∣ l := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  let q := p ^ 2 + p + 2
  have hpq : p ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hq : 0 ≤ q := hp.trans hpq
  have hq1 : p + 1 ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hcost : (q + 2) ^ K ≤ (p + 2) ^ (2 * K) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    dsimp [q]
    nlinarith
  have hlq : (l : ℝ) ≤ Real.exp q :=
    (product_denominator_le_budget m hp hJ hmp).trans
      (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHq : (H : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hq1)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hslow : ∀ j, F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp ((q + 2) ^ 1)) (E j) := by
    intro j
    apply F.symbolSlowBound_mono b ω hF (fun _ => 1) T hTpos _ (E j) (hE j)
    exact Real.exp_le_exp.mpr (by simpa only [pow_one] using hpq.trans (by linarith : q ≤ q + 2))
  have hrat : ∀ j, F.SymbolRationalGrid b ω hF (fun _ => 1) l (R j) :=
    fun j => F.symbolRationalGrid_mono b ω hF (fun _ => 1) (hm j) (hdvd j) (R j) (hR j)
  obtain ⟨m₀, e₀, p₀, r₀, hm₀, hm₀q, _, hepr, hmid, he, hr, he0, hr0, hp0⟩ :=
    hsplit F b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) U v hv hU H l q hH hl hq
      (hι.trans hpq) (hσ.trans hpq) (hι.trans hpq) (hJ.trans hpq) hHq hlq
      (fun i j k => rationalHeightLE_ceil_exp (hstructure i j k))
      (fun j i k => rationalHeightLE_ceil_exp (hheight j i k)) T
      (fun i => (Real.exp_le_exp.mpr hcost).trans (hT i)) g E P R hprod
      (fun j => (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF (fun _ => 1) (U j) _).mp (hP j))
      hslow hrat
  refine ⟨U, v, m₀, e₀, p₀, r₀, hv, hU, hheight, ?_, hm₀,
    hm₀q.trans (Real.exp_le_exp.mpr hcost), hepr, hmid, ?_, hr, he0, hr0, hp0⟩
  · intro j x hx hxgrade
    exact hfreq j x ((lieSubalgebra_mem_iInf U x).mp hx j) hxgrade
  · intro α i
    exact (he α i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hcost)
      (monomialScale_pos T hTpos α).le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HaarShiftImage
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem haarShiftDensity_map_eq {T G Y : Type*} [MeasurableSpace T] [AddCommGroup G]
    [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G] [MeasurableSpace Y]
    (μ : Measure G) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] (z : T → G) (hz : Measurable z)
    (f : G → ℝ) (hfm : Measurable f) (hfi : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1)
    (π : G → Y) (hπ : Measurable π) (hinv : ∀ t x, π (x + z t) = π x) :
    (realDensityMeasure μ (haarShiftDensity ν z f)).map π = (realDensityMeasure μ f).map π := by
  let _ := realDensityMeasure_probability μ f hfi hf0 hmass
  have hU : Measurable (fun p : T × G => p.2 + z p.1) :=
    measurable_snd.add (hz.comp measurable_fst)
  rw [← haarShiftDensity_image_law μ ν hz hfm hfi hf0 hmass,
    Measure.map_map hπ hU]
  have he : (π ∘ fun p : T × G => p.2 + z p.1) = π ∘ Prod.snd := by
    funext p
    exact hinv p.1 p.2
  rw [he, ← Measure.map_map hπ measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedPrincipalInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff NNReal

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

noncomputable def principalSliceSlope (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) (b : B) (i : F) : ℝ :=
  c b * width (b, i) * ∏ j ∈ Finset.univ.erase i,
    (lower (b, j) + width (b, j) * x (b, j))

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ContDiff BigOperators

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

noncomputable def principalSliceSingleton (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) : Unit → ℝ := fun _ => principalSliceValue c lower width x

section Joint

variable {D : Type*} [Fintype D]
variable {B F : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]

noncomputable def jointSlicedPrincipal (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) :=
  sigmaAxisSampler (fun d => principalSliceSingleton (c d) (lower d) (width d))

noncomputable def jointSlicedInjection (b : ∀ d, B d) (i : ∀ d, F d) :=
  sigmaAxisOperator (fun d => coordinateInjection (fun _ : Unit => (b d, i d)))

end Joint

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AuxiliaryBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

abbrev AuxiliaryBoxLabels {I : Type*} {N : I → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i)) (M d : I → ℕ) (u : I → ℤ) :=
  ∀ i, (P i).Label × CompatibleAuxResidue (M i) (d i) (u i)

noncomputable def boxAuxiliaryCell {I : Type*} (a : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (M d : I → ℕ) (hd : ∀ i, 0 < d i)
    (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (x : IntegerResidueBox a (fun i => a i + N i) r b) : AuxiliaryBoxLabels P M d u :=
  fun i => intervalAuxiliaryCell (a i) (P i) (M i) (d i) (hd i) (u i) (r i) (b i) (hbase i) (x i)

noncomputable def boxAuxiliaryCellEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (k : AuxiliaryBoxLabels P M d u) (R c : I → ℤ)
    (hcombine : ∀ i (x : ℤ),
      (x ≡ b i [ZMOD r i] ∧ x ≡ ((k i).2.val.val : ℤ) [ZMOD (d i : ℤ)]) ↔ x ≡ c i [ZMOD R i]) :
    ↥(partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k) ≃
      IntegerResidueBox (fun i => intervalCellLower (a i) (P i) (k i).1)
        (fun i => intervalCellUpper (a i) (P i) (k i).1) R c := by
  let e₁ : ↥(partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k) ≃
      {x : IntegerResidueBox a (fun i => a i + N i) r b //
        ∀ i, intervalAuxiliaryCell (a i) (P i) (M i) (d i) (hd i)
          (u i) (r i) (b i) (hbase i) (x i) = k i} :=
    Equiv.subtypeEquivRight (fun x => by
      simp only [mem_partitionCell, boxAuxiliaryCell, funext_iff])
  exact e₁.trans (Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight (fun i =>
    intervalAuxiliaryCellEquiv (a i) (P i) (hstep i) (hpos i) (M i) (d i) (hd i)
      (u i) (r i) (b i) (hbase i) (k i) (R i) (c i) (hcombine i))))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FrozenComplexNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
  (φ : L →ₗ⁅ℚ⁆ M) (a r : E.RealGroup)
  (h : ∀ γ ∈ D.realLattice,
    r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice)
  {w : σ → ℕ} (T : E.Niltest w) (g : D.filtration.realification.PolynomialOrbit w)
  (K : ℝ≥0)
  (hK : letI := D.metricSpace
    letI := E.metricSpace
    LipschitzWith K (frozenCosetMap D.realLattice E.realLattice
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h))

noncomputable def frozenComplexNiltest : D.Niltest w where
  orbit := g
  observable := T.observable ∘ frozenCosetMap D.realLattice E.realLattice
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h
  normBound := T.normBound
  lipBound := T.lipBound * K
  norm_le x := T.norm_le _
  lipschitz := by
    let := D.metricSpace
    let := E.metricSpace
    exact T.lipschitz.comp hK

theorem frozenComplexNiltest_eval (x : σ → ℤ) :
    (D.frozenComplexNiltest E φ a r h T g K hK).eval x =
      T.observable (QuotientGroup.mk
        (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ
          (D.filtration.realification.polynomialOrbitEval w x g) * r)) := rfl

theorem frozenComplexNiltest_complexity {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hD : D.GeometryComplexityLE q) (hT : T.ComplexityLE p)
    (hbound : (K : ℝ) ≤ Real.exp q) :
    (D.frozenComplexNiltest E φ a r h T g K hK).ComplexityLE (p + q + 4) := by
  have hb := T.observable_budget hT
  have hnorm : (T.normBound : ℝ) ≤ Real.exp (p + q) :=
    (by linarith [T.lipBound.coe_nonneg] : (T.normBound : ℝ) ≤ Real.exp p).trans
      (Real.exp_le_exp.mpr (by linarith))
  have hlip : (T.lipBound : ℝ) * K ≤ Real.exp (p + q) := by
    rw [Real.exp_add]
    exact mul_le_mul (by linarith [T.normBound.coe_nonneg]) hbound K.coe_nonneg (Real.exp_pos _).le
  refine ⟨hD.mono D (by linarith), ?_⟩
  change Real.log (2 + (T.normBound : ℝ) + ((T.lipBound * K : ℝ≥0) : ℝ)) ≤ p + q + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    _ ≤ 4 * Real.exp (p + q) := by
      simp only [NNReal.coe_mul]
      linarith [Real.one_le_exp (show 0 ≤ p + q by linarith)]
    _ ≤ Real.exp 4 * Real.exp (p + q) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem frozenComplexNiltest_top_invariant
    (hinv : ∀ z ∈ D.filtration.realification.subgroup s, ∀ x : D.RealGroup,
      T.observable (QuotientGroup.mk
        (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r)) =
      T.observable (QuotientGroup.mk
        (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r)))
    (z : D.RealGroup) (hz : z ∈ D.filtration.realification.subgroup s) (x : D.Space) :
    (D.frozenComplexNiltest E φ a r h T g K hK).observable (z • x) =
      (D.frozenComplexNiltest E φ a r h T g K hK).observable x := by
  induction x using Quotient.inductionOn with
  | h x => exact hinv z hz x

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProjectedHorizontalFactorization
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

theorem projectedHorizontal_factorization (ht : 1 ≤ t) (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : σ → ℝ) (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) (l : ℕ)
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hfactor : F.SymbolFactorizationIn b ω hF T X p l U) :
    ∃ E R : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
      F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) E ∧
      F.SymbolRationalGrid b ω hF (fun _ => 1) l R ∧
      ∀ α : σ →₀ ℕ,
        (G.projectedHorizontalSymbolCoefficient F φ hφ (fun _ => 1) α).baseChange ℝ X.coord -
          (G.projectedHorizontalSymbolCoefficient F φ hφ (fun _ => 1) α).baseChange ℝ E.coord -
          (G.projectedHorizontalSymbolCoefficient F φ hφ (fun _ => 1) α).baseChange ℝ R.coord ∈
        (G.layerHorizontalImage (F.gradedRefiltrationLayer U) φ
          (fun d x hx => hφ d x (F.gradedRefiltrationLayer_le U d hx))
            (Finsupp.weight (fun _ => 1) α)).baseChange ℝ := by
  obtain ⟨E, P, R, hprod, hE, hR, hP⟩ := hfactor
  refine ⟨E, R, hE, hR, ?_⟩
  intro α
  let f := (G.projectedHorizontalSymbolCoefficient F φ hφ (fun _ : σ => 1) α).baseChange ℝ
  have hsum := congrArg (G.realProjectedHorizontalSymbolHom F φ hφ ht (fun _ : σ => 1) α) hprod
  rw [map_mul, map_mul] at hsum
  have hsum' := congrArg Multiplicative.toAdd hsum
  change f E.coord + f P.coord + f R.coord = f X.coord at hsum'
  have hres : f X.coord - f E.coord - f R.coord = f P.coord := by
    rw [← hsum']
    abel
  change f X.coord - f E.coord - f R.coord ∈ _
  rw [hres]
  exact G.real_projectedHorizontalSymbolCoefficient_mem F φ hφ b ω hF (fun _ => 1) U P.coord hP α

end Erdos3.DegreeRankLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.EuclideanDerivativeProjection
namespace OAI

section

namespace Erdos3

theorem euclideanDerivativeLattice_shortSpan_projection
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → κ → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i) :
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T
      (fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne') scale hscale Y A l hl
    (shortVectorSpan Λ ρ).map ((LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp
      productEuclideanEquiv.symm.toLinearMap) = ⊤ := by
  let hT0 : ∀ i, 0 < T i := fun i => lt_of_lt_of_le zero_lt_one (hT i)
  let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T (fun i => (hT0 i).ne') scale hscale Y A l hl
  let π₀ := (LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp productEuclideanEquiv.symm.toLinearMap
  let e := coordinateScaleEquiv T (fun i => (hT0 i).ne')
  let π := e.toLinearMap.comp π₀
  have hspan := integer_points_span_eq_top_of_density H T R δ hT hR
    (fun h hh => derivativeGridPoint_shift_bound T hT0 scale Y _ h (r h) R (hnorm h hh))
    hdense hlarge
  have hmap : (shortVectorSpan Λ ρ).map π = ⊤ := by
    apply shortVectorSpan_map_eq_top_of_spanning_integer_images Λ π H ρ hspan
    intro h hh
    let v := derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)
    refine ⟨productEuclideanEquiv v, ?_, ?_, ?_⟩
    · apply (productEuclideanEquiv_mem_derivativeLattice T
        (fun i => (hT0 i).ne') scale hscale Y A l hl v).mpr
      rw [← SetLike.mem_coe, derivativeLattice_carrier]
      exact derivativeGridPoint_mem T scale Y _ l h (r h) (hr h hh)
    · exact (productEuclideanEquiv_norm_le v).trans
        (mul_le_mul_of_nonneg_left (hnorm h hh) (Nat.cast_nonneg _))
    · change e (LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)
        (productEuclideanEquiv.symm (productEuclideanEquiv v))) = _
      rw [LinearEquiv.symm_apply_apply]
      funext i
      exact mul_div_cancel₀ (h i : ℝ) (hT0 i).ne'
  have hmap' : ((shortVectorSpan Λ ρ).map π₀).map e.toLinearMap = ⊤ := by
    simpa only [← Submodule.map_comp] using hmap
  exact (Submodule.map_eq_top_iff (e := e)).mp hmap'

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.EuclideanVerticalProjection
namespace OAI

section

namespace Erdos3

noncomputable def euclideanVerticalProjection {σ κ : Type*} :
    EuclideanSpace ℝ (σ ⊕ κ) →ₗ[ℝ] EuclideanSpace ℝ κ :=
  (EuclideanSpace.equiv κ ℝ).symm.toLinearMap.comp
    ((LinearMap.snd ℝ (σ → ℝ) (κ → ℝ)).comp productEuclideanEquiv.symm.toLinearMap)

@[simp] theorem euclideanVerticalProjection_apply {σ κ : Type*}
    (x : EuclideanSpace ℝ (σ ⊕ κ)) (j : κ) :
    euclideanVerticalProjection x j = x (Sum.inr j) := rfl

theorem euclideanVerticalProjection_norm_le {σ κ : Type*} [Fintype σ] [Fintype κ]
    (x : EuclideanSpace ℝ (σ ⊕ κ)) : ‖euclideanVerticalProjection x‖ ≤ ‖x‖ := by
  have hs : ‖euclideanVerticalProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
    simp only [euclideanVerticalProjection_apply]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ => sq_nonneg ‖x (Sum.inl i)‖))
  nlinarith [norm_nonneg (euclideanVerticalProjection x), norm_nonneg x]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledKernelSplitTransport
namespace OAI

section

namespace Erdos3

theorem exists_controlled_kernel_split_equiv {H ι κ ν τ : Type*}
    [AddCommGroup H] [Module ℝ H] [Fintype ι] [Fintype κ] [Fintype ν]
    (e : H ≃ₗ[ℝ] (ι → ℝ)) (U K : Submodule ℝ H)
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ)
    (hAspan : Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) = U.map e.toLinearMap)
    (hBspan : Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) = K.map e.toLinearMap)
    (b : ν → K) (hb : ∀ j, e (b j).val = (B.map (Rat.castHom ℝ)).col j)
    (R : K →ₗ[ℝ] (τ → ℝ)) (n : ℕ) (hR : ∀ j, R (b j) ∈ realDenominatorGrid n)
    {J l : ℕ} (hJ : 1 ≤ J) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) J) (hB : ∀ i j, RationalHeightLE (B i j) J)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hJp : (J : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ split : H →ₗ[ℝ] K,
        (∀ x, x ∈ U ⊔ K → x - (split x).val ∈ U) ∧
        (∀ x, ‖e (split x).val‖ ≤ Real.exp ((p + 2) ^ 19) * ‖e x‖) ∧
        ∀ x, e x ∈ realDenominatorGrid l → R (split x) ∈ realDenominatorGrid (n * m) := by
  let eK : K ≃ₗ[ℝ] K.map e.toLinearMap := e.submoduleMap K
  let R' := R.comp eK.symm.toLinearMap
  have hb' : ∀ j, (eK (b j)).val = (B.map (Rat.castHom ℝ)).col j := hb
  have hR' : ∀ j, R' (eK (b j)) ∈ realDenominatorGrid n := by
    intro j
    simpa only [R', LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply] using hR j
  obtain ⟨m, hm, hmp, split', hsplit', hnorm, hgrid⟩ :=
    exists_controlled_kernel_split (U.map e.toLinearMap) (K.map e.toLinearMap)
      A B hAspan hBspan (fun j => eK (b j)) hb' R' n hR' hJ hl hA hB hp hι hcols hJp hlp
  let split : H →ₗ[ℝ] K := eK.symm.toLinearMap.comp (split'.comp e.toLinearMap)
  have hsplit (x : H) : e (split x).val = (split' (e x)).val :=
    congrArg Subtype.val (eK.apply_symm_apply (split' (e x)))
  refine ⟨m, hm, hmp, split, ?_, ?_, ?_⟩
  · intro x hx
    have hex : e x ∈ U.map e.toLinearMap ⊔ K.map e.toLinearMap := by
      rw [← Submodule.map_sup]
      exact ⟨x, hx, rfl⟩
    have hmem : e (x - (split x).val) ∈ U.map e.toLinearMap := by
      rw [map_sub, hsplit]
      exact hsplit' (e x) hex
    simpa only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] using hmem
  · intro x
    rw [hsplit]
    exact hnorm (e x)
  · intro x hx
    exact hgrid (e x) hx

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ReindexGradedBasis
namespace OAI

section

namespace Erdos3

open Module

theorem basisGradeProjection_reindex {K V ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (ω : ι → ℕ) (e : ι ≃ κ) (j : ℕ) :
    basisGradeProjection (b.reindex e) (fun k => ω (e.symm k)) j = basisGradeProjection b ω j := by
  apply LinearMap.ext
  intro x
  apply (b.reindex e).repr.injective
  ext k
  simp only [basisGradeProjection_repr, Basis.repr_reindex_apply]

theorem basisGradedSubmodule_reindex_iff {K V ι κ : Type*} [Field K]
    [AddCommGroup V] [Module K V] (b : Basis ι K V) (ω : ι → ℕ) (e : ι ≃ κ)
    (U : Submodule K V) :
    BasisGradedSubmodule (b.reindex e) (fun k => ω (e.symm k)) U ↔ BasisGradedSubmodule b ω U := by
  simp only [BasisGradedSubmodule, basisGradeProjection_reindex]

namespace NilpotentLieFiltration

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (e : ι ≃ κ)
  (hF' : ∀ j, F.layer j = Submodule.span ℚ ((b.reindex e) '' {k | j ≤ ω (e.symm k)}))

theorem associatedGradedBasis_reindex :
    F.associatedGradedBasis (b.reindex e) (fun k => ω (e.symm k)) hF' =
      (F.associatedGradedBasis b ω hF).reindex e := by
  apply DFunLike.ext
  intro k
  rw [Basis.reindex_apply]
  rw [← F.associatedGradedPieceMap_basis (b.reindex e) (fun k => ω (e.symm k)) hF'
      (ω (e.symm k)) k le_rfl rfl,
    ← F.associatedGradedPieceMap_basis b ω hF (ω (e.symm k)) (e.symm k) le_rfl rfl]
  congr 1
  apply Subtype.ext
  exact Basis.reindex_apply b e k

theorem gradedFrequency_reindex (η : L →ₗ[ℚ] ℚ) :
    F.gradedFrequency (b.reindex e) (fun k => ω (e.symm k)) hF' η =
      F.gradedFrequency b ω hF η := by
  apply LinearMap.ext
  intro x
  change η ((b.reindex e).repr.symm
      ((F.associatedGradedBasis (b.reindex e) (fun k => ω (e.symm k)) hF').repr x)) =
    η (b.repr.symm ((F.associatedGradedBasis b ω hF).repr x))
  rw [F.associatedGradedBasis_reindex b ω hF e hF']
  apply congrArg η
  apply (b.reindex e).repr.injective
  ext k
  simp only [LinearEquiv.apply_symm_apply, Basis.repr_reindex_apply]

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerVectorFreimanEmbedding
namespace OAI

section

namespace Erdos3.FreimanModel

open scoped BigOperators Pointwise

noncomputable def coordinatePolynomial (n : ℕ) : (Fin n → ℤ) →+ Polynomial ℤ where
  toFun x := ∑ i : Fin n, Polynomial.monomial (i : ℕ) (x i)
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

theorem coordinatePolynomial_coeff {n : ℕ} (x : Fin n → ℤ) (i : Fin n) :
    (coordinatePolynomial n x).coeff (i : ℕ) = x i := by
  change (∑ j : Fin n, Polynomial.monomial (j : ℕ) (x j)).coeff (i : ℕ) = x i
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Polynomial.coeff_monomial, Fin.val_inj.ne.mpr hji]
  · simp

theorem coordinatePolynomial_injective (n : ℕ) :
    Function.Injective (coordinatePolynomial n) := by
  intro x y h
  funext i
  simpa only [coordinatePolynomial_coeff] using
    congrArg (fun p : Polynomial ℤ => p.coeff (i : ℕ)) h

theorem exists_fin_integer_embedding {n : ℕ} (A : Finset (Fin n → ℤ)) :
    ∃ f : (Fin n → ℤ) →+ ℤ, Set.InjOn f (A : Set _) := by
  classical
  let P := coordinatePolynomial n
  let R := (A ×ˢ A).biUnion fun xy => (P xy.1 - P xy.2).roots.toFinset
  obtain ⟨t, ht⟩ := R.exists_notMem
  let f := (Polynomial.evalRingHom t).toAddMonoidHom.comp P
  refine ⟨f, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  have hP : P x - P y ≠ 0 :=
    sub_ne_zero.mpr (fun h => hne (coordinatePolynomial_injective n h))
  apply ht
  apply Finset.mem_biUnion.mpr
  refine ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
  change (P x - P y).eval t = 0
  rw [Polynomial.eval_sub, sub_eq_zero]
  exact hxy

theorem exists_integer_vector_embedding {I : Type*} [Fintype I]
    (A : Finset (I → ℤ)) : ∃ f : (I → ℤ) →+ ℤ, Set.InjOn f (A : Set _) := by
  classical
  let e := Fintype.equivFin I
  let r : (I → ℤ) →+ (Fin (Fintype.card I) → ℤ) :=
    { toFun := fun x j => x (e.symm j)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hr : Function.Injective r := by
    intro x y h
    funext i
    simpa only [r, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.symm_apply_apply] using
      congrFun h (e i)
  obtain ⟨f, hf⟩ := exists_fin_integer_embedding (A.image r)
  refine ⟨f.comp r, ?_⟩
  intro x hx y hy hxy
  exact hr (hf (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    (Finset.mem_image.mpr ⟨y, hy, rfl⟩) hxy)

theorem multiset_sum_mem_iterated_sumset {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (A : Finset G) {T : Multiset G} (hT : ∀ x ∈ T, x ∈ A) :
    T.sum ∈ T.card • A := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons a T ih =>
      rw [Multiset.card_cons, succ_nsmul, Finset.mem_add]
      refine ⟨T.sum, ih ?_, a, hT a (by simp), ?_⟩
      · intro x hx
        exact hT x (by simp [hx])
      · simp [add_comm]

theorem isAddFreimanIso_of_injOn_iterated_sums
    {G H : Type*} [AddCommMonoid G] [AddCommMonoid H] [DecidableEq G] [DecidableEq H]
    (f : G →+ H) (A : Finset G) (s : ℕ) (hinj : Set.InjOn f (A : Set G))
    (hsinj : Set.InjOn f (s • A : Finset G)) :
    IsAddFreimanIso s (A : Set G) (A.image f : Set H) f := by
  refine ⟨⟨?_, hinj, ?_⟩, ?_⟩
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro y hy
    exact Finset.mem_image.mp hy
  · intro T U hT hU hTc hUc
    rw [← map_multiset_sum, ← map_multiset_sum]
    have hTs : T.sum ∈ s • A := by
      simpa only [hTc] using multiset_sum_mem_iterated_sumset A (fun x hx => hT hx)
    have hUs : U.sum ∈ s • A := by
      simpa only [hUc] using multiset_sum_mem_iterated_sumset A (fun x hx => hU hx)
    exact ⟨fun h => hsinj hTs hUs h, congrArg f⟩

theorem exists_integer_freiman_embedding {I : Type*} [Fintype I]
    (A : Finset (I → ℤ)) (s : ℕ) :
    ∃ f : (I → ℤ) →+ ℤ, IsAddFreimanIso s (A : Set _)
      (A.image f : Set ℤ) f := by
  classical
  obtain ⟨f, hf⟩ := exists_integer_vector_embedding (A ∪ s • A)
  refine ⟨f, isAddFreimanIso_of_injOn_iterated_sums f A s ?_ ?_⟩
  · exact hf.mono (fun _ hx => Finset.mem_union_left _ hx)
  · exact hf.mono (fun _ hx => Finset.mem_union_right _ hx)

end Erdos3.FreimanModel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPiProduct
namespace OAI

section

namespace Erdos3

open MeasureTheory MeasureTheory.Measure MeasurableSpace

def dependentPiProd (I : Type*) (X Y : I → Type*)
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)] :
    (∀ i, X i × Y i) ≃ᵐ ((∀ i, X i) × (∀ i, Y i)) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun x i := (x.1 i, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (measurable_pi_iff.mpr (fun index =>
    measurable_fst.comp (measurable_pi_apply index))).prodMk
      (measurable_pi_iff.mpr (fun index => measurable_snd.comp (measurable_pi_apply index)))
  measurable_invFun := measurable_pi_iff.mpr (fun index =>
    ((measurable_pi_apply index).comp measurable_fst).prodMk
      ((measurable_pi_apply index).comp measurable_snd))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ConstructLayerResetScales
namespace OAI

section

namespace Erdos3

structure LayerResetScales (s r : ℕ) (L : ℝ) where
  threshold : ℕ → ℕ
  cellScale : ℕ → ℕ
  score : ℕ → ℝ
  constant : ℕ → ℝ
  exponent : ℕ → ℕ
  score_pos : ∀ h ≤ s + 1, 0 < score h
  constant_nonneg : ∀ h ≤ s, 0 ≤ constant h
  partition : ∀ h ≤ s, PolynomialCoordinatePartitionBound.{0} h (constant h) (exponent h)
  cell_pos : ∀ h ≤ s, 0 < cellScale h
  scale_bound : ∀ h ≤ s, constant h * ((r : ℝ) + 1) ≤ cellScale h
  power_bound : ∀ h ≤ s, cellScale h ^ (exponent h * (r + 1) ^ (2 * h)) ≤ threshold h
  lift_error : ∀ h ≤ s, (2 : ℝ) ^ (h + 1) * ((h : ℝ) / cellScale h) < 1
  freeze_error : ∀ h ≤ s, (r : ℝ) * (2 * ((h : ℝ) / cellScale h)) < 1 / 12
  score_error : ∀ h ≤ s, 8 * L * r * h ≤ score h * cellScale h
  score_next : ∀ h ≤ s, score (h + 1) ≤ score h / 2
  length_bound : ∀ h ≤ s, (threshold (h + 1) : ℝ) ≤
    score h * cellScale h / (2 : ℝ) ^ (h + 3)

end Erdos3

end

section

namespace Erdos3

def layerResetThreshold (s B T h : ℕ) : ℕ := T ^ ((2 * B) ^ (s + 1 - h))

def layerResetCellScale (s B T h : ℕ) : ℕ := T ^ (2 * (2 * B) ^ (s - h))

@[simp] theorem layerResetThreshold_terminal (s B T : ℕ) :
    layerResetThreshold s B T (s + 1) = T := by simp [layerResetThreshold]

@[simp] theorem layerResetThreshold_initial (s B T : ℕ) :
    layerResetThreshold s B T 1 = T ^ ((2 * B) ^ s) := by simp [layerResetThreshold]

theorem layerResetThreshold_pos {s B T h : ℕ} (hT : 0 < T) :
    0 < layerResetThreshold s B T h := pow_pos hT _

theorem layerResetThreshold_ge {s B T h : ℕ} (hB : 0 < B) (hT : 0 < T) :
    T ≤ layerResetThreshold s B T h := by
  exact (Nat.pow_one T).symm.trans_le
    (Nat.pow_le_pow_right hT (by exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (pow_pos (by omega) _))))

theorem layerResetCellScale_sq {s B T h : ℕ} :
    layerResetCellScale s B T h = (layerResetThreshold s B T (h + 1)) ^ 2 := by
  have heq : s + 1 - (h + 1) = s - h := by omega
  simp only [layerResetCellScale, layerResetThreshold, heq, ← pow_mul]
  congr 1
  omega

theorem layerResetCellScale_ge {s B T h : ℕ} (hB : 0 < B) (hT : 0 < T) :
    T ≤ layerResetCellScale s B T h := by
  rw [layerResetCellScale_sq]
  exact (layerResetThreshold_ge hB hT).trans
    ((Nat.pow_one _).symm.trans_le (Nat.pow_le_pow_right (layerResetThreshold_pos hT) (by omega)))

theorem layerResetCellScale_power {s B T h : ℕ} (hh : h ≤ s) :
    layerResetCellScale s B T h ^ B = layerResetThreshold s B T h := by
  have heq : s + 1 - h = (s - h) + 1 := by omega
  simp only [layerResetCellScale, layerResetThreshold, heq, ← pow_mul, pow_succ]
  congr 1
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace LayerResetScales

end LayerResetScales
end Erdos3

end

section

namespace Erdos3

noncomputable def powerLayerResetScales {s r T p : ℕ} {K L σ : ℝ}
    (hp : 0 < p) (hK : 0 ≤ K) (hL : 0 ≤ L) (hT : 0 < T) (hσ : 0 < σ)
    (hpartition : ∀ h ≤ s, PolynomialCoordinatePartitionBound.{0} h K p)
    (hscale : K * ((r : ℝ) + 1) ≤ T)
    (hlift : (2 : ℝ) ^ (s + 1) * s < T)
    (hfreeze : 24 * (r : ℝ) * s < T)
    (hroom : 8 * L * r * s * (2 : ℝ) ^ s ≤ σ * T)
    (hlength : (2 : ℝ) ^ (2 * s + 3) ≤ σ * T) : LayerResetScales s r L := by
  let B := p * (r + 1) ^ (2 * s)
  have hB : 0 < B := Nat.mul_pos hp (pow_pos (by omega) _)
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hge (h : ℕ) : (T : ℝ) ≤ layerResetCellScale s B T h := by
    exact_mod_cast layerResetCellScale_ge (h := h) hB hT
  have hcell (h : ℕ) : (0 : ℝ) < layerResetCellScale s B T h := hT0.trans_le (hge h)
  have hprod (h : ℕ) (hh : h ≤ s) (x : ℝ) (hx : (T : ℝ) ≤ x) :
      σ * T / (2 : ℝ) ^ s ≤ (σ / (2 : ℝ) ^ h) * x := by
    have hdiv : σ / (2 : ℝ) ^ s ≤ σ / (2 : ℝ) ^ h :=
      div_le_div_of_nonneg_left hσ.le (by positivity)
        (pow_le_pow_right₀ (by norm_num) hh)
    calc
      _ = (σ / (2 : ℝ) ^ s) * T := by ring
      _ ≤ _ := mul_le_mul hdiv hx hT0.le (by positivity)
  refine {
    threshold := layerResetThreshold s B T
    cellScale := layerResetCellScale s B T
    score := fun h => σ / (2 : ℝ) ^ h
    constant := fun _ => K
    exponent := fun _ => p
    score_pos := fun h _ => div_pos hσ (by positivity)
    constant_nonneg := fun _ _ => hK
    partition := hpartition
    cell_pos := fun h _ => hT.trans_le (layerResetCellScale_ge hB hT)
    scale_bound := fun h _ => hscale.trans (hge h)
    power_bound := ?_
    lift_error := ?_
    freeze_error := ?_
    score_error := ?_
    score_next := ?_
    length_bound := ?_
  }
  · intro h hh
    have he : p * (r + 1) ^ (2 * h) ≤ B :=
      Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by omega) (by omega))
    exact (Nat.pow_le_pow_right (hT.trans_le (layerResetCellScale_ge hB hT)) he).trans_eq
      (layerResetCellScale_power hh)
  · intro h hh
    rw [← mul_div_assoc]
    apply (div_lt_one (hcell h)).mpr
    calc
      _ ≤ (2 : ℝ) ^ (s + 1) * s := mul_le_mul
        (pow_le_pow_right₀ (by norm_num) (by omega)) (by exact_mod_cast hh)
        (by positivity) (by positivity)
      _ < T := hlift
      _ ≤ _ := hge h
  · intro h hh
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 12)).mpr
    rw [show (r : ℝ) * (2 * ((h : ℝ) / layerResetCellScale s B T h)) * 12 =
      (24 * r * h) / layerResetCellScale s B T h by ring]
    apply (div_lt_one (hcell h)).mpr
    calc
      _ ≤ 24 * (r : ℝ) * s := mul_le_mul_of_nonneg_left (by exact_mod_cast hh) (by positivity)
      _ < T := hfreeze
      _ ≤ _ := hge h
  · intro h hh
    calc
      _ ≤ 8 * L * r * s := mul_le_mul_of_nonneg_left (by exact_mod_cast hh) (by positivity)
      _ ≤ σ * T / (2 : ℝ) ^ s := (le_div_iff₀ (by positivity)).mpr hroom
      _ ≤ _ := hprod h hh _ (hge h)
  · intro h _
    simp only [pow_succ, div_div]
    exact le_rfl
  · intro h hh
    let A := layerResetThreshold s B T (h + 1)
    have hA : (T : ℝ) ≤ A := by exact_mod_cast layerResetThreshold_ge (h := h + 1) hB hT
    have hc : (2 : ℝ) ^ (h + 3) ≤ (σ / (2 : ℝ) ^ h) * A := by
      calc
        _ ≤ (2 : ℝ) ^ (s + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ σ * T / (2 : ℝ) ^ s := by
          apply (le_div_iff₀ (by positivity)).mpr
          simpa only [← pow_add, show s + 3 + s = 2 * s + 3 by omega] using hlength
        _ ≤ _ := hprod h hh _ hA
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (h + 3))).mpr
    rw [layerResetCellScale_sq, Nat.cast_pow]
    change (A : ℝ) * 2 ^ (h + 3) ≤ (σ / 2 ^ h) * A ^ 2
    nlinarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (α := ℝ) A)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JoinedPairQuotientRefiltration
namespace OAI

universe u

section

namespace Erdos3.NilpotentLieFiltration

open Module
open RationalFilteredNilmanifold

section ControlledWitness

variable {σ ι V : Type*} [LieRing V] [LieAlgebra ℚ V] {s : ℕ}
  (H : NilpotentLieFiltration V s) (b : Basis ι ℚ V) (ω : ι → ℕ)
  (hH : ∀ k, H.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))

def ControlledSymbolFactorizationAtFast (η : V →ₗ[ℚ] ℚ) (side : σ → ℝ)
    (X : H.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ)
    (U : LieSubalgebra ℚ H.AssociatedGraded) : Prop :=
  ∃ (m : ℕ) (E P R : H.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (v : ι → H.AssociatedGraded),
    0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ E * P * R = X ∧
    H.SymbolSlowBound b ω hH (fun _ => 1) side (Real.exp p) E ∧
    H.SymbolRationalGrid b ω hH (fun _ => 1) m R ∧
    Submodule.span ℚ (Set.range v) = U.toSubmodule ∧
    BasisGradedSubmodule (H.associatedGradedBasis b ω hH) ω U.toSubmodule ∧
    (∀ i j, rationalLogHeight ((H.associatedGradedBasis b ω hH).repr (v i) j) ≤ p) ∧
    (∀ x ∈ U, basisGradeProjection (H.associatedGradedBasis b ω hH) ω s x = x →
      H.gradedFrequency b ω hH η x = 0) ∧
    P.coord ∈ realificationLieSubalgebra (H.symbolPointwiseSubalgebra b ω hH (fun _ => 1) U)

theorem ControlledSymbolFactorization.exists_fastWitness
    {η : V →ₗ[ℚ] ℚ} {side : σ → ℝ}
    {X : H.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ}
    (h : H.ControlledSymbolFactorization b ω hH η side X p) :
    ∃ U, H.ControlledSymbolFactorizationAtFast b ω hH η side X p U := by
  obtain ⟨m, E, P, R, U, v, hdata⟩ := h
  exact ⟨U, m, E, P, R, v, hdata⟩

end ControlledWitness

section GradedIntersection

variable {V J : Type*} {P : J → Type*} [LieRing V] [LieAlgebra ℚ V]
  [∀ j, LieRing (P j)] [∀ j, LieAlgebra ℚ (P j)] {s : ℕ}
  (H : NilpotentLieFiltration V s) (G : ∀ j, NilpotentLieFiltration (P j) s)
  (φ : ∀ j, V →ₗ⁅ℚ⁆ P j)
  (hφ : ∀ j k, ∀ x ∈ H.layer k, φ j x ∈ (G j).layer k)

end GradedIntersection

section PairConstraints

variable {L W : Type u} {J Y : Type*} {M : J → Type u}
  [LieRing L] [LieAlgebra ℚ L] [LieRing W] [LieAlgebra ℚ W]
  [LieRing Y] [LieAlgebra ℚ Y]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {s : ℕ}
  (F : NilpotentLieFiltration L s) (H : NilpotentLieFiltration (L × W) s)
  
  (ρ : ∀ j, W →ₗ⁅ℚ⁆ M j)
  
  {ι : J → Type*} 
  (ω : ∀ j, ι j → ℕ)
  
   (js : List J)
   (theta : ∀ j, M j →ₗ[ℚ] ℚ)
  
  (hfst : ∀ x ∈ H.layer s, x.1 ∈ F.layer s)



include ω hfst

end PairConstraints

section ActualFactorizations

end ActualFactorizations

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module RationalFilteredNilmanifold

section GradedIntersection

variable {V J κ : Type*} {P : J → Type*} [LieRing V] [LieAlgebra ℚ V]
  [∀ j, LieRing (P j)] [∀ j, LieAlgebra ℚ (P j)] {s : ℕ}
  (H : NilpotentLieFiltration V s) (G : ∀ j, NilpotentLieFiltration (P j) s)
  (e : Basis κ ℚ V) (μ : κ → ℕ)
  (hH : ∀ k, H.layer k = Submodule.span ℚ (e '' {i | k ≤ μ i}))
  (φ : ∀ j, V →ₗ⁅ℚ⁆ P j)
  (hφ : ∀ j k, ∀ x ∈ H.layer k, φ j x ∈ (G j).layer k)
  {ι : J → Type*} (b : ∀ j, Basis (ι j) ℚ (P j)) (ω : ∀ j, ι j → ℕ)
  (hG : ∀ j k, (G j).layer k = Submodule.span ℚ (b j '' {i | k ≤ ω j i}))
  (U : ∀ j, LieSubalgebra ℚ (G j).AssociatedGraded) (js : List J)

end GradedIntersection

section ActualPivotQuotient

variable {L W : Type u} {J Y κ κQ : Type*} {M : J → Type u}
  [LieRing L] [LieAlgebra ℚ L] [LieRing W] [LieAlgebra ℚ W]
  [LieRing Y] [LieAlgebra ℚ Y]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {s : ℕ}
  (F : NilpotentLieFiltration L s) (P : NilpotentLieFiltration W s)
  
  (ρ : ∀ j, W →ₗ⁅ℚ⁆ M j)
  
   (μ : κ → ℕ)
  
   
  
  
   (js : List J)
  
  (eta : J → L →ₗ[ℚ] ℚ) (theta : ∀ j, M j →ₗ[ℚ] ℚ)
  (π : L →ₗ⁅ℚ⁆ Y)
   (ν : κQ → ℕ)

  



end ActualPivotQuotient

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchWeightDescent
namespace OAI

section

namespace Erdos3

namespace PolynomialPatch

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3
open scoped Classical

@[simp] theorem relativePatchDistinctWeights_castRank {X : Type*} {s d e : ℕ}
    (A : PolynomialPatch X s d) (h : d = e) :
    relativePatchDistinctWeights (A.castRank h) = relativePatchDistinctWeights A := by
  subst e
  rfl

@[simp] theorem relativePatchDistinctWeights_coordinateFiber {X : Type*}
    [Fintype X] [DecidableEq X] {s d : ℕ} (A : PolynomialPatch X s d)
    (keep : X → Prop) (fixed : {i // ¬keep i} → ℤ) :
    relativePatchDistinctWeights (A.coordinateFiber keep fixed) = relativePatchDistinctWeights A := rfl

@[simp] theorem relativePatchComplexity_coordinateFiber {X : Type*}
    [Fintype X] [DecidableEq X] {s d : ℕ} (A : PolynomialPatch X s d)
    (keep : X → Prop) (fixed : {i // ¬keep i} → ℤ) :
    relativePatchComplexity (A.coordinateFiber keep fixed) = relativePatchComplexity A := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchFiniteCoordinateReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace PolynomialPatch

variable {X Y : Type*} {s d : ℕ}

noncomputable def coordinateEquiv (A : PolynomialPatch X s d) (e : X ≃ Y) :
    PolynomialPatch Y s d :=
  A.reparam (fun i => MvPolynomial.X (e i)) (fun i => weightedSupportLE_X _ (e i))

@[simp] theorem coordinateEquiv_kernel (A : PolynomialPatch X s d) (e : X ≃ Y) :
    (A.coordinateEquiv e).kernel = A.kernel := rfl

@[simp] theorem coordinateEquiv_weight (A : PolynomialPatch X s d) (e : X ≃ Y) :
    (A.coordinateEquiv e).weight = A.weight := rfl

@[simp] theorem coordinateEquiv_complexity (A : PolynomialPatch X s d) (e : X ≃ Y) :
    relativePatchComplexity (A.coordinateEquiv e) = relativePatchComplexity A := rfl

@[simp] theorem coordinateEquiv_distinctWeights (A : PolynomialPatch X s d) (e : X ≃ Y) :
    relativePatchDistinctWeights (A.coordinateEquiv e) = relativePatchDistinctWeights A := rfl

end PolynomialPatch

namespace ResidueBoxSlice

variable {X Y : Type*} {N : X → ℕ} {q : ℕ}

def coordinateReturn (e : X ≃ Y) (S : ResidueBoxSlice (coordinateReindexedSides e N) q) :
    ResidueBoxSlice N q where
  start i := S.start (e i)
  length i := S.length (e i)
  inside i j hj := by
    simpa only [coordinateReindexedSides, Equiv.symm_apply_apply] using S.inside (e i) j hj

end ResidueBoxSlice

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def RelativePatchFinInductionRule (s n₀ stage : ℕ) (τ : ℝ)
    (cutoff cost : ℝ → ℝ) : Prop :=
  ∀ (p a Λ : ℝ) (d₀ : ℕ), 2 ≤ p → Real.exp (-p) ≤ a → a ≤ Λ → Λ ≤ 1 →
    RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
    ∀ (n : ℕ), 0 < n → (n : ℝ) ≤ p →
      ∀ (N : Fin n → ℕ), (∀ i, Real.exp (cutoff p) ≤ (N i : ℝ)) →
      ∀ (f : (Fin n → ℤ) → ℝ),
        (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
        IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
        ∀ (d : ℕ) (A : PolynomialPatch (Fin n) s d),
          relativePatchComplexity A ≤ p → relativePatchDistinctWeights A ≤ stage →
          Real.exp (-p) ≤ relativePatchBoxScore N f a A →
          RelativePatchSliceConclusion s N f ((1 - τ) ^ (stage + 1) * Λ)
            (d₀ + s * d) (cost p)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ActualResidueSpatialFreezing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_correlated_residue_progression_box {I : Type*} [Fintype I]
    [DecidableEq I] (N : I → ℕ) (q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hqexp : (q : ℝ) ≤ Real.exp p)
    (hN : ∀ i, Real.exp (3 * p + 16) ≤ (N i : ℝ)) (f : (I → ℕ) → ℂ) :
    ∃ start length : I → ℕ,
      (∀ i, 0 < length i) ∧
      (∀ i, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ length i) ∧
      (∀ i (j : Fin (length i)), start i + q * j.val < N i) ∧
      (∀ i (j : Fin (length i)), (start i + q * j.val) % q = start i % q) ∧
      (∀ i (j : Fin (length i)),
        |((start i + q * j.val : ℕ) : ℝ) / N i - (start i : ℝ) / N i| ≤
          Real.exp (-(2 * p)) / 4) ∧
      (∀ i (j k : Fin (length i)),
        |((start i + q * j.val : ℕ) : ℝ) / N i -
          ((start i + q * k.val : ℕ) : ℝ) / N i| ≤ Real.exp (-(2 * p)) / 4) ∧
      ‖𝔼 x : (∀ i, Fin (N i)), f (fun i => (x i).val)‖ ≤
        ‖𝔼 j : (∀ i, Fin (length i)), f (fun i => start i + q * (j i).val)‖ := by
  classical
  let H : I → ℕ := fun i => exponentialProgressionScale (N i) q p
  have hscale (i : I) := exponentialProgressionScale_bounds (N i) q p hp hq hqexp (hN i)
  let P : ∀ i, FiniteProgressionPartition (N i) := fun i =>
    FiniteProgressionPartition.comparableResidueProgressions (N i) q (H i) hq
      (hscale i).1 (hscale i).2.1
  have hstep (i : I) (a : (P i).Label) : (P i).step a = q :=
    FiniteProgressionPartition.comparableResidueProgressions_step _ _ _ _ _ _ _
  have hlength (i : I) (a : (P i).Label) :
      H i ≤ (P i).length a ∧ (P i).length a < 2 * H i :=
    FiniteProgressionPartition.comparableResidueProgressions_length_bounds _ _ _ _ _ _ _
  have hNpos (i : I) : 0 < N i := by
    have : (0 : ℝ) < N i := (Real.exp_pos _).trans_le (hN i)
    exact_mod_cast this
  obtain ⟨a, hpositive, hmean⟩ :=
    BoxProgressionPartition.exists_positive_box_norm_mean_le P hNpos f
  refine ⟨fun i => (P i).start (a i), fun i => (P i).length (a i), hpositive,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hscale i).2.2.1.trans (by exact_mod_cast (hlength i (a i)).1)
  · intro i j
    simpa only [hstep] using (P i).point_lt (a i) j.isLt
  · intro i j
    exact Nat.add_mul_mod_self_left _ _ _
  · intro i j
    simpa only [FiniteProgressionPartition.point_val, hstep] using
      (P i).normalized_point_sub_start_le_of_bound (a i) (hstep i (a i))
        (hlength i (a i)).2 (hNpos i) (hscale i).2.2.2 j
  · intro i j k
    simpa only [FiniteProgressionPartition.point_val, hstep] using
      (P i).normalized_point_sub_point_le_of_bound (a i) (hstep i (a i))
        (hlength i (a i)).2 (hNpos i) (hscale i).2.2.2 j k
  · simpa only [hstep] using hmean

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_correlated_integer_residue_box {I : Type*} [Fintype I]
    [DecidableEq I] (N : I → ℕ) (q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hqexp : (q : ℝ) ≤ Real.exp p)
    (hN : ∀ i, Real.exp (3 * p + 16) ≤ (N i : ℝ)) (f : (I → ℤ) → ℂ) :
    ∃ start length : I → ℕ,
      (∀ i, 0 < length i) ∧
      (∀ i, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ length i) ∧
      (∀ i, (N i : ℝ) ≤ Real.exp (3 * p + 16) * q * length i) ∧
      (∀ v ∈ integerBox length,
        (fun i => (start i : ℤ) + (q : ℤ) * v i) ∈ integerBox N) ∧
      (∀ v ∈ integerBox length, ∀ i,
        ((start i : ℤ) + (q : ℤ) * v i) % q = (start i : ℤ) % q) ∧
      (∀ v ∈ integerBox length, ∀ i,
        |((start i : ℝ) + (q : ℝ) * v i) / N i - (start i : ℝ) / N i| ≤
          Real.exp (-(2 * p)) / 4) ∧
      (∀ v ∈ integerBox length, ∀ w ∈ integerBox length, ∀ i,
        |((start i : ℝ) + (q : ℝ) * v i) / N i -
          ((start i : ℝ) + (q : ℝ) * w i) / N i| ≤ Real.exp (-(2 * p)) / 4) ∧
      ‖𝔼 u ∈ integerBox N, f u‖ ≤
        ‖𝔼 v ∈ integerBox length, f (fun i => (start i : ℤ) + (q : ℤ) * v i)‖ := by
  obtain ⟨start, length, hpos, hlength, hinside, _, hdiam, hpair, hmean⟩ :=
    exists_correlated_residue_progression_box N q p hp hq hqexp hN
      (fun u => f (fun i => (u i : ℤ)))
  have hrepr (v : I → ℤ) (hv : v ∈ integerBox length) :
      ∃ j : ∀ i, Fin (length i), ∀ i, ((j i).val : ℤ) = v i := by
    have hb := (mem_integerBox length v).mp hv
    refine ⟨fun i => ⟨(v i).toNat, by have := hb i; omega⟩, ?_⟩
    exact fun i => Int.toNat_of_nonneg (hb i).1
  refine ⟨start, length, hpos, hlength, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hbase : (N i : ℝ) ≤ (length i : ℝ) * Real.exp (3 * p + 16) := by
      apply (div_le_iff₀ (Real.exp_pos _)).mp
      simpa only [Real.exp_neg, div_eq_mul_inv] using hlength i
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
    calc
      (N i : ℝ) ≤ Real.exp (3 * p + 16) * length i := by simpa only [mul_comm] using hbase
      _ ≤ Real.exp (3 * p + 16) * q * length i := by
        gcongr
        exact le_mul_of_one_le_right (Real.exp_pos _).le hqone
  · intro v hv
    obtain ⟨j, hj⟩ := hrepr v hv
    rw [mem_integerBox]
    intro i
    rw [← hj i]
    constructor
    · positivity
    · exact_mod_cast hinside i (j i)
  · intro v _ i
    exact Int.add_mul_emod_self_left _ _ _
  · intro v hv i
    obtain ⟨j, hj⟩ := hrepr v hv
    have hjR : ((j i).val : ℝ) = v i := by exact_mod_cast hj i
    simpa only [Nat.cast_add, Nat.cast_mul, hjR] using hdiam i (j i)
  · intro v hv w hw i
    obtain ⟨j, hj⟩ := hrepr v hv
    obtain ⟨k, hk⟩ := hrepr w hw
    have hjR : ((j i).val : ℝ) = v i := by exact_mod_cast hj i
    have hkR : ((k i).val : ℝ) = w i := by exact_mod_cast hk i
    simpa only [Nat.cast_add, Nat.cast_mul, hjR, hkR] using hpair i (j i) (k i)
  · rw [integerBox_expect_eq_fin, integerBox_expect_eq_fin]
    simpa only [Nat.cast_add, Nat.cast_mul] using hmean

end Erdos3

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped NNReal BigOperators

variable {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*}
  [∀ j, Fintype (J j)] {periodCap coverCap : ℝ} {L : ℝ≥0}

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBooleanCubeComparison
namespace OAI

section

namespace Erdos3

variable {I O : Type*} [Fintype I] [fintypeO : Fintype O]

noncomputable def affineSelectedInjection (L : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) (δ : ℝ) : (O → ℝ) →L[ℝ] (I → ℝ) :=
  δ • (L.symm.toContinuousLinearMap.comp J)

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [decidableEqB : ∀ d, DecidableEq (B d)] [decidableEqO : ∀ d, DecidableEq (O d)] {h : D → ℕ}

noncomputable def jointAffineBooleanSampler (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ) :
    (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ) :=
  sigmaAxisSampler (fun d x => booleanSamplerMap (c d) (sets d) (b d + L d x))

noncomputable def jointAffineBooleanInjection
    (block : ∀ d, O d → B d) (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ)) (δ : D → ℝ) :
    ((Σ d, O d) → ℝ) →L[ℝ] (JointBlockParameter B h α → ℝ) :=
  sigmaAxisOperator (fun d => affineSelectedInjection (L d)
    (booleanSelectedInjection (block d) (v d) (sel d)) (δ d))

variable (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
  (block : ∀ d, O d → B d) (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
  (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
    (BlockParameter (B d) (Fin (h d)) α → ℝ))
  (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ) (δ : D → ℝ)

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [decidableEqB : ∀ d, DecidableEq (B d)] [decidableEqO : ∀ d, DecidableEq (O d)] {h : D → ℕ}

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators NNReal

variable {B O α : Type*} [Fintype B] [Fintype O] [Fintype α]
  [DecidableEq B] [DecidableEq O] [DecidableEq α] {h : ℕ}

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeMeasurableRepresentative
namespace OAI

section

open MeasureTheory Module

namespace Erdos3

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem exists_measurable_representative_zspan (b : Basis I ℝ E) :
    ∃ r : E ⧸ (Submodule.span ℤ (Set.range b)).toAddSubgroup → E,
      Measurable r ∧ ∀ x,
        QuotientAddGroup.mk' (Submodule.span ℤ (Set.range b)).toAddSubgroup (r x) = x := by
  let e : E ⧸ (Submodule.span ℤ (Set.range b)).toAddSubgroup ≃
      ZSpan.fundamentalDomain b := ZSpan.quotientEquiv b
  have hsymm (x : ZSpan.fundamentalDomain b) :
      e.symm x = QuotientAddGroup.mk' (Submodule.span ℤ (Set.range b)).toAddSubgroup (x : E) := by
    exact ZSpan.quotientEquiv.symm_apply b x
  have hcont : Continuous (fun x : E =>
      (QuotientAddGroup.mk' (Submodule.span ℤ (Set.range b)).toAddSubgroup) x) :=
    QuotientAddGroup.continuous_mk
  have hinj : Set.InjOn
      (QuotientAddGroup.mk' (Submodule.span ℤ (Set.range b)).toAddSubgroup)
      (ZSpan.fundamentalDomain b) := by
    intro x hx y hy hxy
    have he : e.symm ⟨x, hx⟩ = e.symm ⟨y, hy⟩ := by
      simpa only [hsymm] using hxy
    exact congrArg Subtype.val (e.symm.injective he)
  have hfun : (e.symm : ZSpan.fundamentalDomain b → _) =
      (ZSpan.fundamentalDomain b).domRestrict
        (QuotientAddGroup.mk' (Submodule.span ℤ (Set.range b)).toAddSubgroup) :=
    funext hsymm
  have hem : MeasurableEmbedding (e.symm : ZSpan.fundamentalDomain b → _) := by
    rw [hfun]
    exact hcont.continuousOn.measurableEmbedding (ZSpan.fundamentalDomain_measurableSet b) hinj
  have he : Measurable e := hem.measurable_comp_iff.mp (by simpa using measurable_id)
  refine ⟨fun x => (e x : E), measurable_subtype_coe.comp he, ?_⟩
  intro x
  simpa only [hsymm] using e.symm_apply_apply x

theorem lattice_exists_measurable_representative (Λ : Submodule ℤ E)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis I ℤ Λ) :
    ∃ r : E ⧸ Λ.toAddSubgroup → E,
      Measurable r ∧ ∀ x, QuotientAddGroup.mk' Λ.toAddSubgroup (r x) = x := by
  have hspan : Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ Λ : I → E)) = Λ :=
    b.ofZLatticeBasis_span ℝ Λ
  rw [← hspan]
  exact exists_measurable_representative_zspan (b.ofZLatticeBasis ℝ Λ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueEventOrDescent
namespace OAI

section

namespace Erdos3

open Module CircleFourier NilpotentLieFiltration
open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open Module CircleFourier NilpotentLieFiltration
open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

def residuePairStep {I : Type*} (J : I → ℕ) (flag : Bool) : I → ℕ :=
  if flag then J else fun _ => 1

def residuePairValue {I : Type*} (u v : I → ℤ) (flag : Bool) : I → ℤ :=
  if flag then v else u

noncomputable def residuePairMean {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℤ) → ℂ) (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (u v : I → ℤ)
    (J : I → ℕ) (flag : Bool) : ℂ :=
  𝔼 x : IntegerResidueBox lo (fun i => lo i + N i)
    (fun i => (M * residuePairStep J flag i : ℕ)) (residuePairValue u v flag),
    residueBoxStrideValue f u M x

@[simp] theorem residuePairMean_false {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℤ) → ℂ) (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (u v : I → ℤ) (J : I → ℕ) :
    residuePairMean f lo N M u v J false =
      𝔼 x : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u,
        residueBoxStrideValue f u M x := by
  exact congrArg
    (fun r : I → ℤ => 𝔼 x : IntegerResidueBox lo (fun i => lo i + N i) r u,
      residueBoxStrideValue f u M x)
    (show (fun _ : I => ((M * 1 : ℕ) : ℤ)) = (fun _ => (M : ℤ)) by
      funext i
      rw [Nat.mul_one])

@[simp] theorem residuePairMean_true {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℤ) → ℂ) (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (u v : I → ℤ) (J : I → ℕ) :
    residuePairMean f lo N M u v J true =
      𝔼 x : IntegerResidueBox lo (fun i => lo i + N i) (fun i => (M * J i : ℕ)) v,
        residueBoxStrideValue f u M x := rfl

noncomputable def ResiduePairDimensionDrop {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T : D.Niltest (fun _ : σ => 1)) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u v : σ → ℤ) (J : σ → ℕ) (B : ℝ) : Prop :=
  ∃ (flag : Bool) (l : ℕ) (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (z : Fin d → D.filtration.AssociatedGraded),
    0 < l ∧ (l : ℝ) ≤ Real.exp B ∧
    Submodule.span ℚ (Set.range z) = U.toSubmodule ∧
    BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
    (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (z i) j) ≤ B) ∧
    finrank ℚ ↥(W ⊓ U) < finrank ℚ W ∧
    D.filtration.SymbolFactorizationIn D.basis ω hF
      (fun i => (residueIndexLength (lo i) (lo i + N i) (M * residuePairStep J flag i : ℕ)
        (residuePairValue u v flag i) : ℝ))
      ((T.affinePullback (residueStepMatrix (residuePairStep J flag))
        (commonStrideIndex u M (residuePairValue u v flag))).symbol D.basis ω hF) B l U

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup NilpotentLieFiltration RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SubmoduleQuotientSectionBasis
namespace OAI

section

namespace Erdos3
open Module
open scoped Matrix TensorProduct

theorem exists_submoduleQuotientSectionBasis_with_coordinates
    {ι κ V : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (U : Submodule ℚ V) (D : Matrix κ ι ℚ) (T : Matrix ι κ ℚ)
    (hker : LinearMap.ker D.mulVecLin = U.map b.equivFun.toLinearMap)
    (hDT : D * T = 1) :
    ∃ (eQ : Basis κ ℚ (V ⧸ U)) (S : (V ⧸ U) →ₗ[ℚ] V),
      Function.RightInverse S U.mkQ ∧
      Function.RightInverse (S.baseChange ℝ) (U.mkQ.baseChange ℝ) ∧
      (∀ i j, b.repr (S (eQ j)) i = T i j) ∧
      (∀ i j, (b.baseChange ℝ).repr (S.baseChange ℝ ((eQ.baseChange ℝ) j)) i =
        (T i j : ℝ)) ∧
      ∀ j i, eQ.repr (U.mkQ (b i)) j = D j i := by
  have hsurj : Function.Surjective D.mulVec := by
    intro y
    refine ⟨T *ᵥ y, ?_⟩
    rw [Matrix.mulVec_mulVec, hDT, Matrix.one_mulVec]
  let eQ := submoduleQuotientCoordinateBasis b U D hker hsurj
  let S : (V ⧸ U) →ₗ[ℚ] V := b.equivFun.symm.toLinearMap.comp
    (T.mulVecLin.comp eQ.equivFun.toLinearMap)
  have hright : Function.RightInverse S U.mkQ := by
    intro y
    change U.mkQ (b.equivFun.symm (T *ᵥ eQ.equivFun y)) = y
    rw [← submoduleQuotientCoordinateEquiv_symm b U D hker hsurj T hDT]
    exact (submoduleQuotientCoordinateEquiv b U D hker hsurj).symm_apply_apply y
  have hentry (i : ι) (j : κ) : b.repr (S (eQ j)) i = T i j := by
    change b.equivFun (b.equivFun.symm (T *ᵥ eQ.equivFun (eQ j))) i = T i j
    rw [LinearEquiv.apply_symm_apply]
    simp [Matrix.mulVec, dotProduct, Basis.equivFun_self]
  refine ⟨eQ, S, hright, ?_, hentry, ?_, ?_⟩
  · have heq : U.mkQ.comp S = LinearMap.id := LinearMap.ext hright
    have heqR := congrArg (fun f : (V ⧸ U) →ₗ[ℚ] (V ⧸ U) => f.baseChange ℝ) heq
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at heqR
    intro x
    exact DFunLike.congr_fun heqR x
  · intro i j
    rw [scalarExtension_basis_coordinates, hentry]
  · intro j i
    have hmatrix := submoduleQuotientCoordinateBasis_matrix b U D hker hsurj
    have h := congrFun (congrFun hmatrix j) i
    simpa only [LinearMap.toMatrix_apply] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationAssociatedGradedProjection
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open Module _root_.MvPolynomial

variable {σ L ι : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s)
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra w d)
    (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ (weightedFiltration w d hwd).layer j)

noncomputable def weightedTranslationGradedProjection :
    F.AssociatedGraded →ₗ⁅ℚ⁆ weightedSubalgebra w d :=
  F.homogeneousGradedProjection (weightedFiltration w d hwd)
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem weightedTranslationGradedProjection_basis_base (i : ι) (a : σ) :
    (weightedTranslationGradedProjection F w d hw hwd φ hφ
      (F.associatedGradedBasis b ω hF i)).val.base a =
      if ω i = w a then (φ (b i)).val.base a else 0 := by
  simpa only [weightedTranslationGradedProjection, weightedBasis_repr_inl, weightedBasisGrade_inl] using
    F.homogeneousGradedProjection_basis_repr (weightedFiltration w d hwd)
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd)
      (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF i (Sum.inl a)

theorem weightedTranslationGradedProjection_image_graded
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule) :
    BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)).toSubmodule :=
  F.homogeneousGradedProjection_image_graded (weightedFiltration w d hwd)
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF W hW

end Erdos3.PolynomialTranslationLie

end

end OAI

end


