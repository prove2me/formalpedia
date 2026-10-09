-- Prove2me | Definitions.Def_OAIErdos3B025
-- name    : OAIErdos3B025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T15:55:55.808671+00:00
-- url     : https://prove2.me/theorems/dad6d89f-7971-4614-ba6c-6f530325240e
-- title:
--   OpenAI Erdős-3 split, definitions bundle 26 of 101
-- statement:
--   Definitions bundle 26 of 101 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B024`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 26 available.
--
--   Modules: `OAI.Erdos3.DegreeRankLieFiltration.bracket_coefficient_mem_rank_two`, `OAI.Erdos3.DegreeRankLieFiltration.exists_polynomialOrbit_factorization_rank_two`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalCoefficient`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalCoefficient_lie`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalSymbolCoefficient`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalSymbolCoefficient_lie`, `OAI.Erdos3.DegreeRankLieFiltration.higherHorizontalSymbolCoefficient_map`, `OAI.Erdos3.DegreeRankLieFiltration.polynomialOrbit_mul_coefficient_sub_mem_rank_two`, `OAI.Erdos3.DegreeRankLieFiltration.rankCoefficientOrbitHom`, `OAI.Erdos3.DegreeRankLieFiltration.rankCoefficientOrbitHom_eq_iff`, `OAI.Erdos3.DegreeRankLieFiltration.rankCoefficientOrbitHom_eq_one_iff`, `OAI.Erdos3.DegreeRankLieFiltration.rankLayerCoefficient`, `OAI.Erdos3.DegreeRankLieFiltration.rankLayerCoefficient_coe`, `OAI.Erdos3.MultidegreeLieFiltration.adapted_rationalDilation`, `OAI.Erdos3.MultidegreeLieFiltration.additiveTriple_coefficients_mem`, `OAI.Erdos3.MultidegreeLieFiltration.constantMultidegreeOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.constantMultidegreeOrbit_eval`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairLayer_zero`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairLog`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairLog_adapted`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairLog_eval`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairMultidegree`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairMultidegree_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairPolynomialOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairPolynomialOrbit_eval`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPairPolynomialOrbit_zero`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPair_degree_comap`, `OAI.Erdos3.MultidegreeLieFiltration.dilationPair_top_group_relation`, `OAI.Erdos3.MultidegreeLieFiltration.exists_additiveTripleOrbit_of_coefficients`, `OAI.Erdos3.MultidegreeLieFiltration.exists_coordinateAddition_orbit`, `OAI.Erdos3.MultidegreeLieFiltration.exists_integer_dilationPair_orbit`, `OAI.Erdos3.MultidegreeLieFiltration.exists_normalizedCoordinateAddition_orbit`, `OAI.Erdos3.MultidegreeLieFiltration.exists_normalized_dilationPair_orbit`, `OAI.Erdos3.MultidegreeLieFiltration.exists_normalized_frozen_orbit`, `OAI.Erdos3.MultidegreeLieFiltration.exists_splitTriple_orbit`, `OAI.Erdos3.MultidegreeLieFiltration.normalizeMultidegreeOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.normalizeMultidegreeOrbit_eval`, `OAI.Erdos3.MultidegreeLieFiltration.normalizeMultidegreeOrbit_zero`, `OAI.Erdos3.MultidegreeLieFiltration.normalizedWeightedOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.normalizedWeightedOrbit_eval`, `OAI.Erdos3.MultidegreeLieFiltration.normalizedWeightedOrbit_zero`, `OAI.Erdos3.MultidegreeLieFiltration.polynomialOrbitOfLog`, `OAI.Erdos3.MultidegreeLieFiltration.polynomialOrbitOfLog_eval`, `OAI.Erdos3.MultidegreeLieFiltration.rationalDilationOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.rationalDilationOrbit_eval`, `OAI.Erdos3.MultidegreeLieFiltration.rationalDilationOrbit_rescaled`, `OAI.Erdos3.MultidegreeLieFiltration.restrictAdditiveTripleOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.restrictAdditiveTripleOrbit_eval`, `OAI.Erdos3.MultidegreeLieFiltration.restrictAdditiveTripleOrbit_zero`, `OAI.Erdos3.MultidegreeLieFiltration.restrictAdditiveTriplePolynomial`, `OAI.Erdos3.MultidegreeLieFiltration.restrictAdditiveTriplePolynomial_adapted`, `OAI.Erdos3.MultidegreeLieFiltration.restrictAdditiveTriplePolynomial_eval`, `OAI.Erdos3.MultidegreeLieFiltration.splitTriple_coefficient_mem`, `OAI.Erdos3.MultidegreeLieFiltration.splitTriple_left`, `OAI.Erdos3.MultidegreeLieFiltration.splitTriple_neutral`, `OAI.Erdos3.MultidegreeLieFiltration.splitTriple_right`, `OAI.Erdos3.MultidegreeLieFiltration.strictUpperLayer_zero`, `OAI.Erdos3.MultidegreeLieFiltration.weightedGroupInclusion`, `OAI.Erdos3.MultidegreeLieFiltration.weightedGroupInclusion_injective`, `OAI.Erdos3.MultidegreeLieFiltration.weightedNormalizationLog`, `OAI.Erdos3.MultidegreeLieFiltration.weightedNormalizationLog_adapted`, `OAI.Erdos3.MultidegreeLieFiltration.weightedNormalizationLog_eval`, `OAI.Erdos3.MultidegreeLieFiltration.weightedNormalizationLog_zero`, `OAI.Erdos3.NilpotentLieFiltration.AdaptedBasisIndex`, `OAI.Erdos3.NilpotentLieFiltration.AssociatedGraded`, `OAI.Erdos3.NilpotentLieFiltration.PolynomialSymbol`, `OAI.Erdos3.NilpotentLieFiltration.PolynomialSymbolGroup`, `OAI.Erdos3.NilpotentLieFiltration.ShiftedMonomialIndex`, `OAI.Erdos3.NilpotentLieFiltration.SymbolBasisIndex`, `OAI.Erdos3.NilpotentLieFiltration.adaptedBasisCode`, `OAI.Erdos3.NilpotentLieFiltration.adaptedBasisCode_injective`, `OAI.Erdos3.NilpotentLieFiltration.adaptedBasisIndexFintype`, `OAI.Erdos3.NilpotentLieFiltration.adaptedBasisIndex_card_le`, `OAI.Erdos3.NilpotentLieFiltration.adaptedBasisIndex_degree_le`, `OAI.Erdos3.NilpotentLieFiltration.adaptedBasisIndex_finite`, `OAI.Erdos3.NilpotentLieFiltration.adaptedBasis_weight_le_step`, `OAI.Erdos3.NilpotentLieFiltration.adaptedBasis_weight_pos`, `OAI.Erdos3.NilpotentLieFiltration.adaptedCoefficientMap`, `OAI.Erdos3.NilpotentLieFiltration.adaptedCoefficientMap_apply`, `OAI.Erdos3.NilpotentLieFiltration.adaptedMonomialBasis`, `OAI.Erdos3.NilpotentLieFiltration.adaptedMonomialBasis_bracket`, `OAI.Erdos3.NilpotentLieFiltration.adaptedMonomialBasis_bracket_height`, `OAI.Erdos3.NilpotentLieFiltration.adaptedMonomialBasis_coe`, `OAI.Erdos3.NilpotentLieFiltration.adaptedMonomialBasis_repr`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialFiltration_layer`, `OAI.Erdos3.NilpotentLieFiltration.adaptedSubmodule_eq_span_tensorBasis`, `OAI.Erdos3.NilpotentLieFiltration.adaptedWeightedDilation`, `OAI.Erdos3.NilpotentLieFiltration.adaptedWeightedDilation_mem_shiftedIdeal`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedBasis`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedBasis_apply`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedBasis_bracket`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedBasis_repr`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedFiltration`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedFiltration_layer`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedIndexEquiv`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedPieceMap`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedPieceMap_apply`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedPieceMap_basis`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedPieceMap_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedPieceMap_eq_zero_iff`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedPieceMap_lie`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedPieceMap_range`, `OAI.Erdos3.NilpotentLieFiltration.dilationPair_coefficients_mem`, `OAI.Erdos3.NilpotentLieFiltration.dilationPair_top_group_relation`, `OAI.Erdos3.NilpotentLieFiltration.exists_normalized_shift_square`, `OAI.Erdos3.NilpotentLieFiltration.exists_square_polynomial`, `OAI.Erdos3.NilpotentLieFiltration.gradedMonomialLinear`, `OAI.Erdos3.NilpotentLieFiltration.gradedMonomialLinear_coe`, `OAI.Erdos3.NilpotentLieFiltration.gradedRefiltration`, `OAI.Erdos3.NilpotentLieFiltration.gradedRefiltrationLayer`, `OAI.Erdos3.NilpotentLieFiltration.gradedRefiltrationLayer_antitone`, `OAI.Erdos3.NilpotentLieFiltration.gradedRefiltrationLayer_le`, `OAI.Erdos3.NilpotentLieFiltration.gradedRefiltrationLayer_lie_mem`, `OAI.Erdos3.NilpotentLieFiltration.gradedRefiltrationLayer_terminal`, `OAI.Erdos3.NilpotentLieFiltration.gradedRefiltrationSubalgebra`, `OAI.Erdos3.NilpotentLieFiltration.horizontalLog`, `OAI.Erdos3.NilpotentLieFiltration.horizontalLog_inv`, `OAI.Erdos3.NilpotentLieFiltration.horizontalLog_mul`, `OAI.Erdos3.NilpotentLieFiltration.horizontal_bch`, `OAI.Erdos3.NilpotentLieFiltration.layer_succ_le_gradedRefiltrationLayer`, `OAI.Erdos3.NilpotentLieFiltration.mem_gradedRefiltrationLayer`, `OAI.Erdos3.NilpotentLieFiltration.mem_gradedRefiltrationLayer_iff`, `OAI.Erdos3.NilpotentLieFiltration.mem_gradedRefiltration_layer`, `OAI.Erdos3.NilpotentLieFiltration.mem_layer_iff_basis_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.normalizedShiftLog_adapted`, `OAI.Erdos3.NilpotentLieFiltration.normalizedShiftLog_sub_coefficient_mem`, `OAI.Erdos3.NilpotentLieFiltration.normalizedShift_horizontal_zero`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitCoordinates`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitCoordinates_log`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitCoordinates_symm_log`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolBasis`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolBasis_apply`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolBasis_bracket`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolBasis_bracket_height`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolBasis_repr_map`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolCoefficient`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolCoefficient_dilation`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolCoefficient_map`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolDilation`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolDilation_map`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolDilation_mul`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolDilation_one`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolFiltration`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolFiltration_layer`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolHom`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolMap`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolMap_constant`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolMap_eq_iff`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolMap_eq_zero_iff`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolMap_surjective`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolMap_translate`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbol_ext`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbol_lowerCentralSeries_eq_bot`, `OAI.Erdos3.NilpotentLieFiltration.positive_weight_of_ne_zero`, `OAI.Erdos3.NilpotentLieFiltration.realTotalDegreeOrbit`, `OAI.Erdos3.NilpotentLieFiltration.realTotalDegreeOrbit_eval`, `OAI.Erdos3.NilpotentLieFiltration.real_totalDegree_adapted`, `OAI.Erdos3.NilpotentLieFiltration.restrictDilationPairPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.restrictDilationPairPolynomial_eval`, `OAI.Erdos3.NilpotentLieFiltration.shiftedAdaptedIdeal_eq_span_monomialBasis`, `OAI.Erdos3.NilpotentLieFiltration.shiftedMonomialBasis`, `OAI.Erdos3.NilpotentLieFiltration.shiftedMonomialBasis_coe`, `OAI.Erdos3.NilpotentLieFiltration.shiftedMonomialBasis_repr`, `OAI.Erdos3.NilpotentLieFiltration.shiftedPolynomialIdeal_eq_span_monomialBasis`, `OAI.Erdos3.NilpotentLieFiltration.shiftedPolynomial_next_eq_span`, `OAI.Erdos3.NilpotentLieFiltration.squareDiagonalLayer`, `OAI.Erdos3.NilpotentLieFiltration.squareGradedDiagonalPiece`, `OAI.Erdos3.NilpotentLieFiltration.squareGradedDiagonalPiece_eq_zero_iff`, `OAI.Erdos3.NilpotentLieFiltration.squareGradedPiece_decomposition`, `OAI.Erdos3.NilpotentLieFiltration.squareGradedRelativePiece`, `OAI.Erdos3.NilpotentLieFiltration.squareRelativeLayer`, `OAI.Erdos3.NilpotentLieFiltration.symbolBasisCode`, `OAI.Erdos3.NilpotentLieFiltration.symbolBasisCode_injective`, `OAI.Erdos3.NilpotentLieFiltration.symbolBasisIndexFintype`, `OAI.Erdos3.NilpotentLieFiltration.symbolBasisIndex_card_le`, `OAI.Erdos3.NilpotentLieFiltration.symbolBasisIndex_degree_le`, `OAI.Erdos3.NilpotentLieFiltration.symbolBasisIndex_finite`, `OAI.Erdos3.NilpotentLieFiltration.symbolSurvivorEquiv`, `OAI.Erdos3.NilpotentLieFiltration.symbol_dimension_bound_le_power`, `OAI.Erdos3.NilpotentLieFiltration.totalDegreeMultifiltration`, `OAI.Erdos3.NilpotentLieFiltration.totalDegree_zero_layer`, `OAI.Erdos3.VectorPolynomial.eq_affine_of_degreeLE_one`, `OAI.Erdos3.VectorPolynomial.eval_normalizedShiftLog`, `OAI.Erdos3.VectorPolynomial.eval_splitTriple`, `OAI.Erdos3.VectorPolynomial.eval_zero_eq_coefficient`, `OAI.Erdos3.VectorPolynomial.eval₂_affine_of_degreeLE_one`, `OAI.Erdos3.VectorPolynomial.exponent_of_weight_le_one`, `OAI.Erdos3.VectorPolynomial.normalizedShiftLog`, `OAI.Erdos3.VectorPolynomial.splitTriple`, `OAI.Erdos3.VectorPolynomial.splitTriple_zero`, `OAI.Erdos3.exists_controlled_rational_image_reconstruction`, `OAI.Erdos3.exists_symbol_extension_budget`, `OAI.Erdos3.freezeCoordinates`, `OAI.Erdos3.freezingPolynomial`, `OAI.Erdos3.freezingPolynomial_eval`, `OAI.Erdos3.freezingPolynomial_support`, `OAI.Erdos3.integralOrderedBasisProduct`, `OAI.Erdos3.mem_totalDegreeSplitDownset_false`, `OAI.Erdos3.mem_totalDegreeSplitDownset_true`, `OAI.Erdos3.realIntegralOrderedBasisProduct`, `OAI.Erdos3.realification_liePiEval_liePiMap`, `OAI.Erdos3.realification_pi_basis_repr`, `OAI.Erdos3.retainedCoordinateWeight`, `OAI.Erdos3.retainedCoordinate_degree`, `OAI.Erdos3.shift_le_power_succ`, `OAI.Erdos3.shifted_self_power_le_base_power`, `OAI.Erdos3.symbol_spanning_count_bound`, `OAI.Erdos3.symbol_spanning_parameter_ge`, `OAI.Erdos3.symbol_spanning_parameter_power_bound`, `OAI.Erdos3.totalDegreeSplitBound`, `OAI.Erdos3.totalDegreeSplitBound_le`, `OAI.Erdos3.totalDegreeSplitDownset`, `OAI.Erdos3.totalDegreeSplitDownset_covers`, `OAI.Erdos3.totalDegreeSplitDownset_lower`, `OAI.Erdos3.totalDegreeSplitDownset_terminal`, `OAI.Erdos3.unitMonomial`, `OAI.Erdos3.unitMonomial_add`, `OAI.Erdos3.unitMonomial_injective`, `OAI.Erdos3.unitMonomial_weight`, `OAI.Erdos3.weight_unitMonomial`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B094

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedPolynomialBasis
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def normalizedShiftLog (s : ℕ) (h : σ → ℚ) (a b : L)
    (p : VectorPolynomial σ ℚ L) : VectorPolynomial σ ℚ L :=
  lieBCH s (monomial 0 a) (lieBCH s (translate h p) (monomial 0 b))

theorem eval_normalizedShiftLog (s : ℕ) (h x : σ → ℚ) (a b : L)
    (p : VectorPolynomial σ ℚ L) :
    eval x (normalizedShiftLog s h a b p) = lieBCH s a (lieBCH s (eval (fun i => x i + h i) p) b) := by
  simp only [normalizedShiftLog, eval_lieBCH, eval_translate, eval_monomial,
    Finsupp.prod_zero_index, one_smul]

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem normalizedShiftLog_adapted (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (h : σ → ℚ) (a b : L) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) :
    F.Adapted w (normalizedShiftLog s h a b p) :=
  F.adapted_bch w (F.adapted_constant w a)
    (F.adapted_bch w (F.adapted_translate w hw h hp) (F.adapted_constant w b))

theorem normalizedShiftLog_sub_coefficient_mem (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (h : σ → ℚ) (a b : L) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) (α : σ →₀ ℕ) :
    coefficients (normalizedShiftLog s h a b p - p) α ∈ F.layer (Finsupp.weight w α + 1) := by
  let p₀ : F.adaptedLieSubalgebra w := ⟨p, (F.mem_adaptedSubmodule w p).mpr hp⟩
  let p₁ : F.adaptedLieSubalgebra w :=
    ⟨translate h p, (F.mem_adaptedSubmodule w _).mpr (F.adapted_translate w hw h hp)⟩
  let c₁ := F.adaptedConstant w a
  let c₂ := F.adaptedConstant w b
  let I := F.shiftedAdaptedIdeal w
  let z := lieBCH s c₁ (lieBCH s p₁ c₂)
  have hz₁ : z - lieBCH s p₁ c₂ ∈ I :=
    lieBCH_sub_right_mem_of_mem_ideal (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot I
      (F.adaptedConstant_mem_shiftedIdeal w a) _
  have hz₂ : lieBCH s p₁ c₂ - p₁ ∈ I :=
    lieBCH_sub_left_mem_of_mem_ideal (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot I _
      (F.adaptedConstant_mem_shiftedIdeal w b)
  have hz₃ : p₁ - p₀ ∈ I := F.translate_sub_coefficient_mem w hw h hp
  have hz : z - p₀ ∈ I := by
    have hh := I.add_mem (I.add_mem hz₁ hz₂) hz₃
    have he : (z - lieBCH s p₁ c₂ + (lieBCH s p₁ c₂ - p₁)) + (p₁ - p₀) = z - p₀ := by abel
    rw [he] at hh
    exact hh
  have he : (F.adaptedLieSubalgebra w).incl z = normalizedShiftLog s h a b p := by
    dsimp only [z]
    rw [map_lieBCH, map_lieBCH]
    rfl
  have hh := hz α
  change coefficients ((F.adaptedLieSubalgebra w).incl (z - p₀)) α ∈ _ at hh
  rw [map_sub, he] at hh
  exact hh

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem positive_weight_of_ne_zero (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    {α : σ →₀ ℕ} (hα : α ≠ 0) : 0 < Finsupp.weight w α := by
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hα
  exact (hw i).trans_le (Finsupp.le_weight_of_ne_zero' w hi)

theorem exists_square_polynomial (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p q : VectorPolynomial σ ℚ L) (hp : F.Adapted w p) (hq : F.Adapted w q)
    (hdiff : ∀ α, coefficients (p - q) α ∈ F.layer (Finsupp.weight w α + 1))
    (hzero : coefficients (p - q) 0 ∈ F.layer 2) :
    ∃ r : VectorPolynomial σ ℚ F.squareLieSubalgebra,
      F.squareFiltration.Adapted w r ∧
      VectorPolynomial.map F.squareFst.toLinearMap r = p ∧
      VectorPolynomial.map F.squareSnd.toLinearMap r = q := by
  simp only [map_sub, Finsupp.sub_apply] at hdiff hzero
  have hcoeff (α : σ →₀ ℕ) : coefficients (pair p q) α ∈ F.squareLieSubalgebra.toSubmodule := by
    rw [coefficients_pair]
    change (coefficients p α, coefficients q α) ∈ F.squareLieSubalgebra
    rw [F.mem_squareLieSubalgebra]
    change coefficients p α - coefficients q α ∈ F.layer 2
    by_cases hα : α = 0
    · simpa only [hα] using hzero
    · exact F.antitone (by have := positive_weight_of_ne_zero w hw hα; omega) (hdiff α)
  let r := restrictCoefficients F.squareLieSubalgebra.toSubmodule (pair p q) hcoeff
  have hr (α : σ →₀ ℕ) : (coefficients r α : L × L) = (coefficients p α, coefficients q α) := by
    rw [coefficients_restrictCoefficients, coefficients_pair]
  refine ⟨r, ?_, ?_, ?_⟩
  · apply (F.squareFiltration.adapted_iff_coefficients w r).mpr
    intro α
    rw [F.mem_squareFiltration_layer, hr, F.mem_squareLayer]
    exact ⟨(F.adapted_iff_coefficients w p).mp hp α,
      (F.adapted_iff_coefficients w q).mp hq α, hdiff α⟩
  · apply coefficients.injective
    ext α
    rw [coefficients_map]
    change (coefficients r α).val.1 = coefficients p α
    rw [hr]
  · apply coefficients.injective
    ext α
    rw [coefficients_map]
    change (coefficients r α).val.2 = coefficients q α
    rw [hr]

theorem exists_normalized_shift_square (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (h : σ → ℚ) (a b : L) (p : VectorPolynomial σ ℚ L) (hp : F.Adapted w p)
    (hzero : coefficients (normalizedShiftLog s h a b p - p) 0 ∈ F.layer 2) :
    ∃ r : VectorPolynomial σ ℚ F.squareLieSubalgebra,
      F.squareFiltration.Adapted w r ∧
      VectorPolynomial.map F.squareFst.toLinearMap r = normalizedShiftLog s h a b p ∧
      VectorPolynomial.map F.squareSnd.toLinearMap r = p :=
  F.exists_square_polynomial w hw _ _ (F.normalizedShiftLog_adapted w hw h a b hp) hp
    (F.normalizedShiftLog_sub_coefficient_mem w hw h a b hp) hzero

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

abbrev PolynomialSymbol (w : σ → ℕ) :=
  F.adaptedLieSubalgebra w ⧸ F.shiftedAdaptedIdeal w

noncomputable def polynomialSymbolMap (w : σ → ℕ) :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.PolynomialSymbol w :=
  lieQuotientMap (F.shiftedAdaptedIdeal w)

theorem polynomialSymbolMap_surjective (w : σ → ℕ) :
    Function.Surjective (F.polynomialSymbolMap w) :=
  lieQuotientMap_surjective (F.shiftedAdaptedIdeal w)

theorem polynomialSymbolMap_eq_zero_iff (w : σ → ℕ) (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w p = 0 ↔
      ∀ α, coefficients (p : VectorPolynomial σ ℚ L) α ∈ F.layer (Finsupp.weight w α + 1) :=
  lieQuotientMap_eq_zero (F.shiftedAdaptedIdeal w) p

theorem polynomialSymbolMap_eq_iff (w : σ → ℕ) (p q : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w p = F.polynomialSymbolMap w q ↔
      ∀ α, coefficients ((p : VectorPolynomial σ ℚ L) - (q : VectorPolynomial σ ℚ L)) α ∈
        F.layer (Finsupp.weight w α + 1) := by
  rw [← sub_eq_zero, ← map_sub, F.polynomialSymbolMap_eq_zero_iff]
  rfl

theorem polynomialSymbol_lowerCentralSeries_eq_bot (w : σ → ℕ) :
    LieModule.lowerCentralSeries ℚ (F.PolynomialSymbol w) (F.PolynomialSymbol w) s = ⊥ :=
  lie_quotient_lowerCentralSeries_eq_bot (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot
    (F.shiftedAdaptedIdeal w)

abbrev PolynomialSymbolGroup (w : σ → ℕ) :=
  NilpotentLieBCHGroup (F.PolynomialSymbol w) s (F.polynomialSymbol_lowerCentralSeries_eq_bot w)

noncomputable def polynomialSymbolHom (w : σ → ℕ) :
    (F.adaptedPolynomialFiltration w).Group →* F.PolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.polynomialSymbolMap w)

@[simp] theorem polynomialSymbolHom_coord (w : σ → ℕ)
    (g : (F.adaptedPolynomialFiltration w).Group) :
    (F.polynomialSymbolHom w g).coord = F.polynomialSymbolMap w g.coord := rfl

@[simp] theorem polynomialSymbolMap_constant (w : σ → ℕ) (a : L) :
    F.polynomialSymbolMap w (F.adaptedConstant w a) = 0 :=
  (lieQuotientMap_eq_zero (F.shiftedAdaptedIdeal w) _).mpr
    (F.adaptedConstant_mem_shiftedIdeal w a)

theorem polynomialSymbolMap_translate (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (h : σ → ℚ) (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w
      ⟨translate h (p : VectorPolynomial σ ℚ L),
        (F.mem_adaptedSubmodule w _).mpr (F.adapted_translate w hw h
          ((F.mem_adaptedSubmodule w _).mp p.property))⟩ =
      F.polynomialSymbolMap w p := by
  apply (F.polynomialSymbolMap_eq_iff w _ p).mpr
  exact F.translate_sub_coefficient_mem w hw h ((F.mem_adaptedSubmodule w _).mp p.property)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

theorem exponent_of_weight_le_one {σ : Type*} (α : σ →₀ ℕ)
    (hα : Finsupp.weight (fun _ : σ => 1) α ≤ 1) :
    α = 0 ∨ ∃ i, α = Finsupp.single i 1 := by
  by_cases hz : α = 0
  · exact Or.inl hz
  · right
    have hp := NilpotentLieFiltration.positive_weight_of_ne_zero (fun _ : σ => 1) (by simp) hz
    have he : Finsupp.weight (fun _ : σ => 1) α = 1 := by omega
    apply (Finsupp.sum_eq_one_iff α).mp
    simpa only [Finsupp.weight_apply, smul_eq_mul, mul_one] using he

theorem eq_affine_of_degreeLE_one {σ R V : Type*} [Fintype σ]
    [CommRing R] [AddCommGroup V] [Module R V]
    (p : VectorPolynomial σ R V) (hp : DegreeLE (fun _ : σ => 1) 1 p) :
    p = monomial 0 (coefficients p 0) +
      linearPolynomial (fun i => coefficients p (Finsupp.single i 1)) := by
  classical
  apply coefficients.injective
  ext α
  rw [map_add, Finsupp.add_apply, coefficients_monomial]
  by_cases hz : α = 0
  · subst α
    rw [Finsupp.single_eq_same, coefficients_linearPolynomial_zero, add_zero]
  · rw [Finsupp.single_eq_of_ne hz, zero_add]
    by_cases hα : Finsupp.weight (fun _ : σ => 1) α ≤ 1
    · obtain hzero | ⟨i, rfl⟩ := exponent_of_weight_le_one α hα
      · exact (hz hzero).elim
      · rw [coefficients_linearPolynomial_single]
    · rw [hp α (Nat.lt_of_not_ge hα)]
      symm
      apply coefficients_linearPolynomial_of_ne
      intro i hi
      apply hα
      rw [← hi]
      simp only [Finsupp.weight_single, one_smul, le_refl]

theorem eval₂_affine_of_degreeLE_one {σ R S V : Type*} [Fintype σ]
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]
    (p : VectorPolynomial σ R V) (hp : DegreeLE (fun _ : σ => 1) 1 p) (t : σ → S) :
    eval₂ t p = coefficients p 0 + ∑ i, t i • coefficients p (Finsupp.single i 1) := by
  conv_lhs => rw [eq_affine_of_degreeLE_one p hp]
  rw [map_add, eval₂_monomial, Finsupp.prod_zero_index, one_smul, eval₂_linearPolynomial]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedCoefficientMap (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.adaptedLieSubalgebra w →ₗ[ℚ] L :=
  (Finsupp.lapply α).comp
    (coefficients.toLinearMap.comp (F.adaptedLieSubalgebra w).incl.toLinearMap)

@[simp] theorem adaptedCoefficientMap_apply (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.adaptedLieSubalgebra w) :
    F.adaptedCoefficientMap w α p = coefficients (p : VectorPolynomial σ ℚ L) α := rfl

noncomputable def polynomialSymbolCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.PolynomialSymbol w →ₗ[ℚ] L ⧸ F.layer (Finsupp.weight w α + 1) :=
  (F.shiftedAdaptedIdeal w).toSubmodule.liftQ
    ((F.layer (Finsupp.weight w α + 1)).mkQ.comp (F.adaptedCoefficientMap w α)) (by
      intro p hp
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hp α))

@[simp] theorem polynomialSymbolCoefficient_map (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolCoefficient w α (F.polynomialSymbolMap w p) =
      (F.layer (Finsupp.weight w α + 1)).mkQ (coefficients (p : VectorPolynomial σ ℚ L) α) := rfl

theorem polynomialSymbol_ext (w : σ → ℕ) (x y : F.PolynomialSymbol w)
    (h : ∀ α, F.polynomialSymbolCoefficient w α x = F.polynomialSymbolCoefficient w α y) :
    x = y := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  obtain ⟨q, rfl⟩ := F.polynomialSymbolMap_surjective w y
  apply (F.polynomialSymbolMap_eq_iff w p q).mpr
  intro α
  have he := h α
  rw [F.polynomialSymbolCoefficient_map, F.polynomialSymbolCoefficient_map] at he
  have hzero : (F.layer (Finsupp.weight w α + 1)).mkQ
      (coefficients (p : VectorPolynomial σ ℚ L) α - coefficients (q : VectorPolynomial σ ℚ L) α) = 0 := by
    rw [map_sub, he, sub_self]
  simpa only [map_sub, Finsupp.sub_apply] using (Submodule.Quotient.mk_eq_zero _).mp hzero

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hlayers

theorem mem_layer_iff_basis_coordinates (j : ℕ) (v : L) :
    v ∈ F.layer j ↔ ∀ i, ¬ j ≤ ω i → b.repr v i = 0 := by
  rw [hlayers, basis_mem_span_image_iff]
  rfl

theorem adaptedSubmodule_eq_span_tensorBasis (w : σ → ℕ) :
    F.adaptedSubmodule w = Submodule.span ℚ
      (coefficientTensorBasis b '' {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 ≤ ω z.2}) := by
  ext p
  change (∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α)) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [F.mem_layer_iff_basis_coordinates b ω hlayers]
  constructor
  · intro h z hz
    rcases z with ⟨α, i⟩
    rw [coefficientTensorBasis_repr]
    exact h α i hz
  · intro h α i hi
    have hh := h (α, i) hi
    simpa only [coefficientTensorBasis_repr] using hh

noncomputable def adaptedMonomialBasis (w : σ → ℕ) :
    Basis {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2} ℚ (F.adaptedLieSubalgebra w) :=
  supportedSubmoduleBasis (coefficientTensorBasis b) (F.adaptedSubmodule w)
    {z | Finsupp.weight w z.1 ≤ ω z.2} (F.adaptedSubmodule_eq_span_tensorBasis b ω hlayers w)

@[simp] theorem adaptedMonomialBasis_coe (w : σ → ℕ)
    (z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}) :
    (F.adaptedMonomialBasis b ω hlayers w z : VectorPolynomial σ ℚ L) =
      monomial z.val.1 (b z.val.2) := by
  exact (supportedSubmoduleBasis_coe (coefficientTensorBasis b) (F.adaptedSubmodule w)
    {z | Finsupp.weight w z.1 ≤ ω z.2}
    (F.adaptedSubmodule_eq_span_tensorBasis b ω hlayers w) z).trans
      (coefficientTensorBasis_apply b _ _)

theorem adaptedMonomialBasis_repr (w : σ → ℕ) (p : F.adaptedLieSubalgebra w)
    (z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}) :
    (F.adaptedMonomialBasis b ω hlayers w).repr p z =
      b.repr (coefficients (p : VectorPolynomial σ ℚ L) z.val.1) z.val.2 := by
  exact (supportedSubmoduleBasis_repr (coefficientTensorBasis b) (F.adaptedSubmodule w)
    {z | Finsupp.weight w z.1 ≤ ω z.2}
    (F.adaptedSubmodule_eq_span_tensorBasis b ω hlayers w) p z).trans
      (coefficientTensorBasis_repr b _ _ _)

theorem shiftedAdaptedIdeal_eq_span_monomialBasis (w : σ → ℕ) :
    (F.shiftedAdaptedIdeal w).toSubmodule = Submodule.span ℚ
      (F.adaptedMonomialBasis b ω hlayers w ''
        {z | Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2}) := by
  ext p
  change (∀ α, coefficients (p : VectorPolynomial σ ℚ L) α ∈
    F.layer (Finsupp.weight w α + 1)) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [F.mem_layer_iff_basis_coordinates b ω hlayers]
  constructor
  · intro h z hz
    rw [F.adaptedMonomialBasis_repr]
    exact h z.val.1 z.val.2 hz
  · intro h α i hi
    by_cases hdeg : Finsupp.weight w α ≤ ω i
    · have hz := h ⟨(α, i), hdeg⟩ hi
      simpa only [F.adaptedMonomialBasis_repr] using hz
    · exact (F.mem_layer_iff_basis_coordinates b ω hlayers _ _).mp (p.property α) i hdeg

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedWeightedDilation (w : σ → ℕ) (r : ℚ) :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.adaptedLieSubalgebra w :=
  { ((weightedDilation w r).comp (F.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
      (F.adaptedLieSubalgebra w).toSubmodule (by
        intro p α
        change coefficients (weightedDilation w r (p : VectorPolynomial σ ℚ L)) α ∈ _
        rw [coefficients_weightedDilation]
        exact (F.layer _).smul_mem _ (p.property α)) with
    map_lie' := by
      intro p q
      apply Subtype.ext
      exact weightedDilation_lie w r (p : VectorPolynomial σ ℚ L) (q : VectorPolynomial σ ℚ L) }

theorem adaptedWeightedDilation_mem_shiftedIdeal (w : σ → ℕ) (r : ℚ)
    {p : F.adaptedLieSubalgebra w} (hp : p ∈ F.shiftedAdaptedIdeal w) :
    F.adaptedWeightedDilation w r p ∈ F.shiftedAdaptedIdeal w := by
  intro α
  change coefficients (weightedDilation w r (p : VectorPolynomial σ ℚ L)) α ∈ _
  rw [coefficients_weightedDilation]
  exact (F.layer _).smul_mem _ (hp α)

noncomputable def polynomialSymbolDilation (w : σ → ℕ) (r : ℚ) :
    F.PolynomialSymbol w →ₗ⁅ℚ⁆ F.PolynomialSymbol w :=
  { toLinearMap := (F.shiftedAdaptedIdeal w).toSubmodule.liftQ
      ((F.polynomialSymbolMap w).toLinearMap.comp (F.adaptedWeightedDilation w r).toLinearMap) (by
        intro p hp
        exact (lieQuotientMap_eq_zero (F.shiftedAdaptedIdeal w) _).mpr
          (F.adaptedWeightedDilation_mem_shiftedIdeal w r hp))
    map_lie' := by
      intro x y
      obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
      obtain ⟨q, rfl⟩ := F.polynomialSymbolMap_surjective w y
      change F.polynomialSymbolMap w (F.adaptedWeightedDilation w r ⁅p, q⁆) =
        ⁅F.polynomialSymbolMap w (F.adaptedWeightedDilation w r p),
          F.polynomialSymbolMap w (F.adaptedWeightedDilation w r q)⁆
      rw [LieHom.map_lie, LieHom.map_lie] }

@[simp] theorem polynomialSymbolDilation_map (w : σ → ℕ) (r : ℚ)
    (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolDilation w r (F.polynomialSymbolMap w p) =
      F.polynomialSymbolMap w (F.adaptedWeightedDilation w r p) := rfl

theorem polynomialSymbolCoefficient_dilation (w : σ → ℕ) (r : ℚ)
    (α : σ →₀ ℕ) (x : F.PolynomialSymbol w) :
    F.polynomialSymbolCoefficient w α (F.polynomialSymbolDilation w r x) =
      r ^ Finsupp.weight w α • F.polynomialSymbolCoefficient w α x := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.polynomialSymbolDilation_map, F.polynomialSymbolCoefficient_map,
    F.polynomialSymbolCoefficient_map]
  change (F.layer (Finsupp.weight w α + 1)).mkQ
    (coefficients (weightedDilation w r (p : VectorPolynomial σ ℚ L)) α) = _
  rw [coefficients_weightedDilation, map_smul]

@[simp] theorem polynomialSymbolDilation_one (w : σ → ℕ) (x : F.PolynomialSymbol w) :
    F.polynomialSymbolDilation w 1 x = x := by
  apply F.polynomialSymbol_ext w
  intro α
  simp only [F.polynomialSymbolCoefficient_dilation, one_pow, one_smul]

theorem polynomialSymbolDilation_mul (w : σ → ℕ) (a b : ℚ) (x : F.PolynomialSymbol w) :
    F.polynomialSymbolDilation w (a * b) x =
      F.polynomialSymbolDilation w a (F.polynomialSymbolDilation w b x) := by
  apply F.polynomialSymbol_ext w
  intro α
  simp only [F.polynomialSymbolCoefficient_dilation, mul_pow, smul_smul]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem adaptedPolynomialFiltration_layer (w : σ → ℕ) (j : ℕ) :
    (F.adaptedPolynomialFiltration w).layer j = Submodule.span ℚ
      (F.adaptedMonomialBasis b ω hF w '' {z | j ≤ ω z.val.2}) := by
  ext p
  change (∀ α, coefficients (p : VectorPolynomial σ ℚ L) α ∈ F.layer j) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [F.mem_layer_iff_basis_coordinates b ω hF]
  constructor
  · intro h z hz
    rw [F.adaptedMonomialBasis_repr]
    exact h z.val.1 z.val.2 hz
  · intro h α i hi
    by_cases hdeg : Finsupp.weight w α ≤ ω i
    · have hz := h ⟨(α, i), hdeg⟩ hi
      simpa only [F.adaptedMonomialBasis_repr] using hz
    · exact (F.mem_layer_iff_basis_coordinates b ω hF _ _).mp (p.property α) i hdeg

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev SymbolBasisIndex (w : σ → ℕ) (ω : ι → ℕ) :=
  {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 = ω z.2}

def symbolSurvivorEquiv (w : σ → ℕ) (ω : ι → ℕ) :
    ↥({z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2} |
      Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2}ᶜ) ≃ SymbolBasisIndex w ω where
  toFun z := ⟨z.val.val, by
    have hle := z.val.property
    have hlt := z.property
    change ¬ Finsupp.weight w z.val.val.1 + 1 ≤ ω z.val.val.2 at hlt
    omega⟩
  invFun z := ⟨⟨z.val, z.property.le⟩, by
    change ¬ Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2
    have hz := z.property
    omega⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def polynomialSymbolBasis (w : σ → ℕ) :
    Basis (SymbolBasisIndex w ω) ℚ (F.PolynomialSymbol w) :=
  (supportedQuotientBasis (F.adaptedMonomialBasis b ω hlayers w)
    (F.shiftedAdaptedIdeal w).toSubmodule
    {z | Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2}
    (F.shiftedAdaptedIdeal_eq_span_monomialBasis b ω hlayers w)).reindex (symbolSurvivorEquiv w ω)

@[simp] theorem polynomialSymbolBasis_apply (w : σ → ℕ) (z : SymbolBasisIndex w ω) :
    F.polynomialSymbolBasis b ω hlayers w z =
      F.polynomialSymbolMap w (F.adaptedMonomialBasis b ω hlayers w ⟨z.val, z.property.le⟩) := by
  rw [polynomialSymbolBasis, Basis.reindex_apply, supportedQuotientBasis_apply]
  rfl

theorem polynomialSymbolBasis_repr_map (w : σ → ℕ) (p : F.adaptedLieSubalgebra w)
    (z : SymbolBasisIndex w ω) :
    (F.polynomialSymbolBasis b ω hlayers w).repr (F.polynomialSymbolMap w p) z =
      b.repr (coefficients (p : VectorPolynomial σ ℚ L) z.val.1) z.val.2 := by
  rw [polynomialSymbolBasis, Basis.repr_reindex_apply]
  change (supportedQuotientBasis _ _ _ _).repr
    ((F.shiftedAdaptedIdeal w).toSubmodule.mkQ p) _ = _
  rw [supportedQuotientBasis_repr_mk, F.adaptedMonomialBasis_repr]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem shiftedPolynomialIdeal_eq_span_monomialBasis (w : σ → ℕ) (k : ℕ) :
    (F.shiftedPolynomialIdeal w k).toSubmodule = Submodule.span ℚ
      (F.adaptedMonomialBasis b ω hF w ''
        {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}) := by
  ext p
  change (∀ α, coefficients (p : VectorPolynomial σ ℚ L) α ∈
    F.layer (Finsupp.weight w α + k)) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [F.mem_layer_iff_basis_coordinates b ω hF]
  constructor
  · intro h z hz
    rw [F.adaptedMonomialBasis_repr]
    exact h z.val.1 z.val.2 hz
  · intro h α i hi
    by_cases hdeg : Finsupp.weight w α ≤ ω i
    · have hz := h ⟨(α, i), hdeg⟩ hi
      simpa only [F.adaptedMonomialBasis_repr] using hz
    · exact (F.mem_layer_iff_basis_coordinates b ω hF _ _).mp (p.property α) i hdeg

abbrev ShiftedMonomialIndex (w : σ → ℕ) (ω : ι → ℕ) (k : ℕ) :=
  {z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2} |
    Finsupp.weight w z.val.1 + k ≤ ω z.val.2}

noncomputable def shiftedMonomialBasis (w : σ → ℕ) (k : ℕ) :
    Basis (ShiftedMonomialIndex w ω k) ℚ (F.shiftedPolynomialIdeal w k) :=
  supportedSubmoduleBasis (F.adaptedMonomialBasis b ω hF w)
    (F.shiftedPolynomialIdeal w k).toSubmodule
    {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}
    (F.shiftedPolynomialIdeal_eq_span_monomialBasis b ω hF w k)

@[simp] theorem shiftedMonomialBasis_coe (w : σ → ℕ) (k : ℕ) (z : ShiftedMonomialIndex w ω k) :
    (F.shiftedMonomialBasis b ω hF w k z : F.adaptedLieSubalgebra w) =
      F.adaptedMonomialBasis b ω hF w z.val :=
  supportedSubmoduleBasis_coe _ _ _ _ z

theorem shiftedMonomialBasis_repr (w : σ → ℕ) (k : ℕ)
    (p : F.shiftedPolynomialIdeal w k) (z : ShiftedMonomialIndex w ω k) :
    (F.shiftedMonomialBasis b ω hF w k).repr p z =
      b.repr (coefficients (p.val : VectorPolynomial σ ℚ L) z.val.val.1) z.val.val.2 := by
  rw [shiftedMonomialBasis, supportedSubmoduleBasis_repr, F.adaptedMonomialBasis_repr]

theorem shiftedPolynomial_next_eq_span (w : σ → ℕ) (k : ℕ) :
    (F.shiftedPolynomialIdeal w (k + 1)).toSubmodule.comap
        (F.shiftedPolynomialIdeal w k).toSubmodule.subtype =
      Submodule.span ℚ (F.shiftedMonomialBasis b ω hF w k ''
        {z | Finsupp.weight w z.val.val.1 + (k + 1) ≤ ω z.val.val.2}) := by
  ext p
  change (∀ α, coefficients (p.val : VectorPolynomial σ ℚ L) α ∈
    F.layer (Finsupp.weight w α + (k + 1))) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [F.mem_layer_iff_basis_coordinates b ω hF]
  constructor
  · intro h z hz
    rw [F.shiftedMonomialBasis_repr]
    exact h z.val.val.1 z.val.val.2 hz
  · intro h α i hi
    by_cases hdeg : Finsupp.weight w α + k ≤ ω i
    · have ha : Finsupp.weight w α ≤ ω i := (Nat.le_add_right _ _).trans hdeg
      have hz := h ⟨⟨(α, i), ha⟩, hdeg⟩ hi
      simpa only [F.shiftedMonomialBasis_repr] using hz
    · exact (F.mem_layer_iff_basis_coordinates b ω hF _ _).mp (p.property α) i hdeg

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankHorizontalSymbol
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def rankLayerCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.adaptedLieSubalgebra w →ₗ[ℚ] F.layer (Finsupp.weight w α) 1 :=
  (F.associatedDegree.adaptedCoefficientMap w α).codRestrict (F.layer (Finsupp.weight w α) 1) (by
    intro p
    rw [← F.rank_zero_eq_one]
    exact p.property α)

@[simp] theorem rankLayerCoefficient_coe (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.associatedDegree.adaptedLieSubalgebra w) :
    (F.rankLayerCoefficient w α p : L) = coefficients p.val α := rfl

noncomputable def higherHorizontalCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.adaptedLieSubalgebra w →ₗ[ℚ] F.HigherHorizontal (Finsupp.weight w α) :=
  (F.higherHorizontalMk (Finsupp.weight w α)).comp (F.rankLayerCoefficient w α)

theorem bracket_coefficient_mem_rank_two (w : σ → ℕ)
    (p q : F.associatedDegree.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients ⁅p.val, q.val⁆ α ∈ F.layer (Finsupp.weight w α) 2 := by
  classical
  have hmono (β : σ →₀ ℕ) (x : L) (hx : x ∈ F.layer (Finsupp.weight w β) 2) :
      coefficients (monomial (R := ℚ) β x) α ∈ F.layer (Finsupp.weight w α) 2 := by
    by_cases hβα : β = α
    · subst β
      simpa using hx
    · simp [hβα]
  rw [← sum_monomial_coefficients p.val, ← sum_monomial_coefficients q.val]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients p.val).support (coefficients q.val).support
    (fun β => monomial (R := ℚ) β (coefficients p.val β))
    (fun γ => monomial (R := ℚ) γ (coefficients q.val γ))]
  simp only [map_sum, Finsupp.finsetSum_apply]
  apply Submodule.sum_mem
  intro β _
  apply Submodule.sum_mem
  intro γ _
  rw [lie_monomial]
  apply hmono
  rw [map_add]
  exact F.lie_mem (F.rankLayerCoefficient w β p).property (F.rankLayerCoefficient w γ q).property

theorem higherHorizontalCoefficient_lie (w : σ → ℕ) (α : σ →₀ ℕ)
    (p q : F.associatedDegree.adaptedLieSubalgebra w) :
    F.higherHorizontalCoefficient w α ⁅p, q⁆ = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact F.bracket_coefficient_mem_rank_two w p q α

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def higherHorizontalSymbolCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.PolynomialSymbol w →ₗ[ℚ] F.HigherHorizontal (Finsupp.weight w α) :=
  (F.associatedDegree.shiftedAdaptedIdeal w).toSubmodule.liftQ
    (F.higherHorizontalCoefficient w α) (by
      intro p hp
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact F.lex_antitone (Or.inl (Nat.lt_succ_self (Finsupp.weight w α))) (hp α))

@[simp] theorem higherHorizontalSymbolCoefficient_map (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.associatedDegree.adaptedLieSubalgebra w) :
    F.higherHorizontalSymbolCoefficient w α (F.associatedDegree.polynomialSymbolMap w p) =
      F.higherHorizontalCoefficient w α p := rfl

theorem higherHorizontalSymbolCoefficient_lie (w : σ → ℕ) (α : σ →₀ ℕ)
    (p q : F.associatedDegree.PolynomialSymbol w) :
    F.higherHorizontalSymbolCoefficient w α ⁅p, q⁆ = 0 := by
  obtain ⟨p, rfl⟩ := F.associatedDegree.polynomialSymbolMap_surjective w p
  obtain ⟨q, rfl⟩ := F.associatedDegree.polynomialSymbolMap_surjective w q
  rw [← LieHom.map_lie, F.higherHorizontalSymbolCoefficient_map]
  exact F.higherHorizontalCoefficient_lie w α p q

end Erdos3.DegreeRankLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RankPolynomialFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hlayers

theorem adaptedBasis_weight_pos (i : ι) : 0 < ω i := by
  by_contra hi
  have hb : b i ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hz := (F.mem_layer_iff_basis_coordinates b ω hlayers 1 (b i)).mp hb i (by omega)
  simp at hz

theorem adaptedBasis_weight_le_step (i : ι) : ω i ≤ s := by
  by_contra hi
  have hb : b i ∈ F.layer (s + 1) := by
    rw [hlayers]
    exact Submodule.subset_span ⟨i, (show s + 1 ≤ ω i by omega), rfl⟩
  rw [F.terminal, Submodule.mem_bot] at hb
  exact b.ne_zero i hb

theorem polynomialSymbolBasis_bracket [DecidableEq σ] (w : σ → ℕ) (u v z : SymbolBasisIndex w ω) :
    (F.polynomialSymbolBasis b ω hlayers w).repr
      ⁅F.polynomialSymbolBasis b ω hlayers w u, F.polynomialSymbolBasis b ω hlayers w v⁆ z =
      if u.val.1 + v.val.1 = z.val.1 then b.repr ⁅b u.val.2, b v.val.2⁆ z.val.2 else 0 := by
  classical
  let lift (x : SymbolBasisIndex w ω) : F.adaptedLieSubalgebra w :=
    F.adaptedMonomialBasis b ω hlayers w ⟨x.val, x.property.le⟩
  have hlift (x : SymbolBasisIndex w ω) :
      (lift x : VectorPolynomial σ ℚ L) = monomial x.val.1 (b x.val.2) :=
    F.adaptedMonomialBasis_coe b ω hlayers w _
  have hbracket : (⁅lift u, lift v⁆ : F.adaptedLieSubalgebra w).val =
      monomial (u.val.1 + v.val.1) ⁅b u.val.2, b v.val.2⁆ := by
    change ⁅(lift u : VectorPolynomial σ ℚ L), (lift v : VectorPolynomial σ ℚ L)⁆ = _
    rw [hlift, hlift, lie_monomial]
  rw [F.polynomialSymbolBasis_apply b ω hlayers w u,
    F.polynomialSymbolBasis_apply b ω hlayers w v, ← LieHom.map_lie,
    F.polynomialSymbolBasis_repr_map]
  change b.repr (coefficients ((⁅lift u, lift v⁆ : F.adaptedLieSubalgebra w) :
    VectorPolynomial σ ℚ L) z.val.1) z.val.2 = _
  rw [hbracket, coefficients_monomial]
  by_cases h : u.val.1 + v.val.1 = z.val.1 <;> simp [h]

theorem polynomialSymbolBasis_bracket_height (w : σ → ℕ) {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (u v z : SymbolBasisIndex w ω) :
    RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr
      ⁅F.polynomialSymbolBasis b ω hlayers w u, F.polynomialSymbolBasis b ω hlayers w v⁆ z) H := by
  classical
  rw [F.polynomialSymbolBasis_bracket]
  split_ifs
  · exact hb _ _ _
  · exact rationalHeightLE_zero hH

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped BigOperators

variable {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ) (s : ℕ)
  (hw : ∀ i, 0 < w i) (hω : ∀ i, ω i ≤ s)

include hw hω

theorem symbolBasisIndex_degree_le (z : SymbolBasisIndex w ω) :
    z.val.1.sum (fun _ n => n) ≤ s := by
  apply le_trans ?_ (z.property.le.trans (hω z.val.2))
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right _ (hw i))

noncomputable def symbolBasisCode (z : SymbolBasisIndex w ω) :
    (Σ n : Fin (s + 1), Fin n.val → σ) × ι :=
  (⟨⟨z.val.1.toMultiset.toList.length, by
      rw [Multiset.length_toList, Finsupp.card_toMultiset]
      exact Nat.lt_succ_of_le (symbolBasisIndex_degree_le w ω s hw hω z)⟩,
    z.val.1.toMultiset.toList.get⟩, z.val.2)

theorem symbolBasisCode_injective : Function.Injective (symbolBasisCode w ω s hw hω) := by
  classical
  intro z u h
  have hi := congrArg (fun t : (Σ n : Fin (s + 1), Fin n.val → σ) × ι => t.2) h
  change z.val.2 = u.val.2 at hi
  have hl := congrArg (fun t : (Σ n : Fin (s + 1), Fin n.val → σ) × ι => List.ofFn t.1.2) h
  change List.ofFn z.val.1.toMultiset.toList.get = List.ofFn u.val.1.toMultiset.toList.get at hl
  rw [List.ofFn_get, List.ofFn_get] at hl
  have hm := congrArg (fun t : List σ => (t : Multiset σ)) hl
  rw [Multiset.coe_toList, Multiset.coe_toList] at hm
  apply Subtype.ext
  apply Prod.ext _ hi
  ext i
  have hh := congrArg (fun t : Multiset σ => t.count i) hm
  simpa only [Finsupp.count_toMultiset] using hh

variable [Fintype σ] [Fintype ι]

theorem symbolBasisIndex_finite : Finite (SymbolBasisIndex w ω) :=
  Finite.of_injective (symbolBasisCode w ω s hw hω) (symbolBasisCode_injective w ω s hw hω)

@[instance_reducible] noncomputable def symbolBasisIndexFintype : Fintype (SymbolBasisIndex w ω) := by
  let : Finite (SymbolBasisIndex w ω) := symbolBasisIndex_finite w ω s hw hω
  exact Fintype.ofFinite _

theorem symbolBasisIndex_card_le [Fintype (SymbolBasisIndex w ω)] :
    Fintype.card (SymbolBasisIndex w ω) ≤ Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s := by
  have hc := Fintype.card_le_of_injective (symbolBasisCode w ω s hw hω)
    (symbolBasisCode_injective w ω s hw hω)
  simp only [Fintype.card_prod, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hc
  apply hc.trans
  calc
    (∑ n : Fin (s + 1), Fintype.card σ ^ n.val) * Fintype.card ι ≤
        (∑ _ : Fin (s + 1), (Fintype.card σ + 1) ^ s) * Fintype.card ι := by
      apply Nat.mul_le_mul_right
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = _ := by simp; ring

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hlayers

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def polynomialSymbolFiltration (w : σ → ℕ) :
    NilpotentLieFiltration (F.PolynomialSymbol w) s :=
  (F.adaptedPolynomialFiltration w).quotientLie (F.shiftedAdaptedIdeal w) (by
    rw [(F.adaptedPolynomialFiltration w).terminal]
    exact bot_le)

theorem polynomialSymbolFiltration_layer (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (j : ℕ) :
    (F.polynomialSymbolFiltration w).layer j =
      Submodule.span ℚ (F.polynomialSymbolBasis b ω hlayers w ''
        {z : SymbolBasisIndex w ω | j ≤ ω z.val.2}) := by
  apply le_antisymm
  · rintro x ⟨p, hp, rfl⟩
    rw [basis_mem_span_image_iff]
    intro z hz
    change (F.polynomialSymbolBasis b ω hlayers w).repr (F.polynomialSymbolMap w p) z = 0
    rw [F.polynomialSymbolBasis_repr_map]
    exact (F.mem_layer_iff_basis_coordinates b ω hlayers j _).mp (hp z.val.1) z.val.2 hz
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, hz, rfl⟩
    let p := F.adaptedMonomialBasis b ω hlayers w ⟨z.val, z.property.le⟩
    refine ⟨p, ?_, ?_⟩
    · change (p : VectorPolynomial σ ℚ L) ∈ F.polynomialLayer j
      change (F.adaptedMonomialBasis b ω hlayers w ⟨z.val, z.property.le⟩ :
        VectorPolynomial σ ℚ L) ∈ F.polynomialLayer j
      rw [F.adaptedMonomialBasis_coe]
      apply F.monomial_mem_polynomialLayer
      rw [hlayers]
      exact Submodule.subset_span ⟨z.val.2, hz, rfl⟩
    · exact (F.polynomialSymbolBasis_apply b ω hlayers w z).symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

abbrev AdaptedBasisIndex {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ) :=
  {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}

section Structure

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem adaptedMonomialBasis_bracket [DecidableEq σ] (u v z : AdaptedBasisIndex w ω) :
    (F.adaptedMonomialBasis b ω hlayers w).repr
      ⁅F.adaptedMonomialBasis b ω hlayers w u, F.adaptedMonomialBasis b ω hlayers w v⁆ z =
      if u.val.1 + v.val.1 = z.val.1 then b.repr ⁅b u.val.2, b v.val.2⁆ z.val.2 else 0 := by
  classical
  rw [F.adaptedMonomialBasis_repr]
  change b.repr (coefficients
    ⁅(F.adaptedMonomialBasis b ω hlayers w u : VectorPolynomial σ ℚ L),
      (F.adaptedMonomialBasis b ω hlayers w v : VectorPolynomial σ ℚ L)⁆ z.val.1) z.val.2 = _
  rw [F.adaptedMonomialBasis_coe, F.adaptedMonomialBasis_coe, lie_monomial, coefficients_monomial]
  by_cases h : u.val.1 + v.val.1 = z.val.1
  · simp only [h, Finsupp.single_eq_same, ite_true]
  · simp only [Finsupp.single_eq_of_ne (Ne.symm h), map_zero, Finsupp.zero_apply, h, ite_false]

theorem adaptedMonomialBasis_bracket_height {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) :
    ∀ i j k, RationalHeightLE ((F.adaptedMonomialBasis b ω hlayers w).repr
      ⁅F.adaptedMonomialBasis b ω hlayers w i, F.adaptedMonomialBasis b ω hlayers w j⁆ k) H := by
  classical
  intro i j k
  rw [F.adaptedMonomialBasis_bracket]
  split_ifs
  · exact hb _ _ _
  · exact rationalHeightLE_zero hH

end Structure

section Dimension

variable {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ) (s : ℕ)
  (hw : ∀ i, 0 < w i) (hω : ∀ i, ω i ≤ s)

include hw hω

theorem adaptedBasisIndex_degree_le (z : AdaptedBasisIndex w ω) :
    z.val.1.sum (fun _ n => n) ≤ s := by
  apply le_trans ?_ (z.property.trans (hω z.val.2))
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right _ (hw i))

noncomputable def adaptedBasisCode (z : AdaptedBasisIndex w ω) :
    (Σ n : Fin (s + 1), Fin n.val → σ) × ι :=
  (⟨⟨z.val.1.toMultiset.toList.length, by
      rw [Multiset.length_toList, Finsupp.card_toMultiset]
      exact Nat.lt_succ_of_le (adaptedBasisIndex_degree_le w ω s hw hω z)⟩,
    z.val.1.toMultiset.toList.get⟩, z.val.2)

theorem adaptedBasisCode_injective : Function.Injective (adaptedBasisCode w ω s hw hω) := by
  classical
  intro z u h
  have hi := congrArg (fun t : (Σ n : Fin (s + 1), Fin n.val → σ) × ι => t.2) h
  change z.val.2 = u.val.2 at hi
  have hl := congrArg (fun t : (Σ n : Fin (s + 1), Fin n.val → σ) × ι => List.ofFn t.1.2) h
  change List.ofFn z.val.1.toMultiset.toList.get = List.ofFn u.val.1.toMultiset.toList.get at hl
  rw [List.ofFn_get, List.ofFn_get] at hl
  have hm := congrArg (fun t : List σ => (t : Multiset σ)) hl
  rw [Multiset.coe_toList, Multiset.coe_toList] at hm
  apply Subtype.ext
  apply Prod.ext _ hi
  ext i
  have hh := congrArg (fun t : Multiset σ => t.count i) hm
  simpa only [Finsupp.count_toMultiset] using hh

variable [Fintype σ] [Fintype ι]

theorem adaptedBasisIndex_finite : Finite (AdaptedBasisIndex w ω) :=
  Finite.of_injective (adaptedBasisCode w ω s hw hω) (adaptedBasisCode_injective w ω s hw hω)

@[instance_reducible] noncomputable def adaptedBasisIndexFintype : Fintype (AdaptedBasisIndex w ω) := by
  let : Finite (AdaptedBasisIndex w ω) := adaptedBasisIndex_finite w ω s hw hω
  exact Fintype.ofFinite _

theorem adaptedBasisIndex_card_le [Fintype (AdaptedBasisIndex w ω)] :
    Fintype.card (AdaptedBasisIndex w ω) ≤ Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s := by
  have hc := Fintype.card_le_of_injective (adaptedBasisCode w ω s hw hω)
    (adaptedBasisCode_injective w ω s hw hω)
  simp only [Fintype.card_prod, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hc
  apply hc.trans
  calc
    (∑ n : Fin (s + 1), Fintype.card σ ^ n.val) * Fintype.card ι ≤
        (∑ _ : Fin (s + 1), (Fintype.card σ + 1) ^ s) * Fintype.card ι := by
      apply Nat.mul_le_mul_right
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = _ := by simp; ring

end Dimension
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem symbol_dimension_bound_le_power (s d m : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) :
    ((d * (s + 1) * (m + 1) ^ s : ℕ) : ℝ) ≤ (p + (s + 2)) ^ (s + 2) := by
  push_cast
  have ht : 0 ≤ p + ((s : ℝ) + 2) := by positivity
  calc
    (d : ℝ) * ((s : ℝ) + 1) * ((m : ℝ) + 1) ^ s ≤
        (p + ((s : ℝ) + 2)) * (p + ((s : ℝ) + 2)) * (p + ((s : ℝ) + 2)) ^ s := by
      apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) (by linarith) s) (by positivity)
        (mul_nonneg ht ht)
      exact mul_le_mul (by linarith) (by linarith) (by positivity) ht
    _ = (p + ((s : ℝ) + 2)) ^ (s + 2) := by ring

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def polynomialOrbitCoordinates (w : σ → ℕ) :
    F.PolynomialOrbit w ≃* (F.adaptedPolynomialFiltration w).Group where
  toFun g := ⟨⟨g.log, g.property⟩⟩
  invFun g := ⟨⟨g.coord.val⟩, g.coord.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' g h := by
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact (map_lieBCH (F.adaptedLieSubalgebra w).incl s
      (⟨g.log, g.property⟩ : F.adaptedLieSubalgebra w)
      (⟨h.log, h.property⟩ : F.adaptedLieSubalgebra w)).symm

@[simp] theorem polynomialOrbitCoordinates_log (w : σ → ℕ) (g : F.PolynomialOrbit w) :
    ((F.polynomialOrbitCoordinates w g).coord : VectorPolynomial σ ℚ L) = g.log := rfl

@[simp] theorem polynomialOrbitCoordinates_symm_log (w : σ → ℕ)
    (g : (F.adaptedPolynomialFiltration w).Group) :
    (F.polynomialOrbitCoordinates w |>.symm g).log = g.coord.val := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def rankCoefficientOrbitHom (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.PolynomialOrbit w →* Multiplicative (F.HigherHorizontal (Finsupp.weight w α)) where
  toFun g := Multiplicative.ofAdd (F.higherHorizontalCoefficient w α
    (F.associatedDegree.polynomialOrbitCoordinates w g).coord)
  map_one' := by
    change Multiplicative.ofAdd (F.higherHorizontalCoefficient w α 0) = 1
    rw [map_zero]
    rfl
  map_mul' g h := by
    change Multiplicative.ofAdd (F.higherHorizontalCoefficient w α
      (F.associatedDegree.polynomialOrbitCoordinates w (g * h)).coord) =
      Multiplicative.ofAdd (F.higherHorizontalCoefficient w α
        (F.associatedDegree.polynomialOrbitCoordinates w g).coord +
        F.higherHorizontalCoefficient w α (F.associatedDegree.polynomialOrbitCoordinates w h).coord)
    rw [map_mul]
    exact congrArg Multiplicative.ofAdd (linearMap_lieBCH_eq_add
      (F.higherHorizontalCoefficient w α) (F.higherHorizontalCoefficient_lie w α) hs _ _)

theorem rankCoefficientOrbitHom_eq_iff (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ)
    (g h : F.associatedDegree.PolynomialOrbit w) :
    F.rankCoefficientOrbitHom hs w α g = F.rankCoefficientOrbitHom hs w α h ↔
      coefficients g.log α - coefficients h.log α ∈ F.layer (Finsupp.weight w α) 2 :=
  F.higherHorizontalMk_eq _ _ _

theorem rankCoefficientOrbitHom_eq_one_iff (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.PolynomialOrbit w) :
    F.rankCoefficientOrbitHom hs w α g = 1 ↔
      coefficients g.log α ∈ F.layer (Finsupp.weight w α) 2 := by
  have h := F.rankCoefficientOrbitHom_eq_iff hs w α g 1
  simpa only [map_one, show (1 : F.associatedDegree.PolynomialOrbit w).log = 0 from rfl,
    map_zero, Finsupp.zero_apply, sub_zero] using h

theorem polynomialOrbit_mul_coefficient_sub_mem_rank_two
    (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ)
    (g h : F.associatedDegree.PolynomialOrbit w) :
    coefficients (g * h).log α - (coefficients g.log α + coefficients h.log α) ∈
      F.layer (Finsupp.weight w α) 2 := by
  let q := F.associatedDegree.polynomialOrbitCoordinates w
  have hmap := congrArg Multiplicative.toAdd (map_mul (F.rankCoefficientOrbitHom hs w α) g h)
  change F.higherHorizontalMk (Finsupp.weight w α) (F.rankLayerCoefficient w α (q (g * h)).coord) =
    F.higherHorizontalMk (Finsupp.weight w α) (F.rankLayerCoefficient w α (q g).coord) +
      F.higherHorizontalMk (Finsupp.weight w α) (F.rankLayerCoefficient w α (q h).coord) at hmap
  rw [← map_add] at hmap
  exact (F.higherHorizontalMk_eq _ _ _).mp hmap

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

theorem exists_polynomialOrbit_factorization_rank_two
    {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
    (F : DegreeRankLieFiltration L s r) (hs : 1 ≤ s) (w : σ → ℕ)
    (α : ι → σ →₀ ℕ) (g E A U Q : F.associatedDegree.PolynomialOrbit w)
    (hg : F.associatedDegree.polynomialOrbitEval w 0 g = 1)
    (hE : F.associatedDegree.polynomialOrbitEval w 0 E = 1)
    (hA : F.associatedDegree.polynomialOrbitEval w 0 A = 1)
    (hU : F.associatedDegree.polynomialOrbitEval w 0 U = 1)
    (hQ : F.associatedDegree.polynomialOrbitEval w 0 Q = 1)
    (hcoeff : ∀ i, coefficients g.log (α i) -
      (coefficients E.log (α i) + coefficients A.log (α i) +
        coefficients U.log (α i) + coefficients Q.log (α i)) ∈
          F.layer (Finsupp.weight w (α i)) 2) :
    ∃ K : F.associatedDegree.PolynomialOrbit w,
      F.associatedDegree.polynomialOrbitEval w 0 K = 1 ∧ E * A * K * U * Q = g ∧
      ∀ i, coefficients K.log (α i) ∈ F.layer (Finsupp.weight w (α i)) 2 := by
  let K := A⁻¹ * E⁻¹ * g * Q⁻¹ * U⁻¹
  have hhom (i : ι) :
      F.rankCoefficientOrbitHom hs w (α i) g =
        F.rankCoefficientOrbitHom hs w (α i) E * F.rankCoefficientOrbitHom hs w (α i) A *
          F.rankCoefficientOrbitHom hs w (α i) U * F.rankCoefficientOrbitHom hs w (α i) Q := by
    let z (v : F.associatedDegree.PolynomialOrbit w) :=
      F.rankLayerCoefficient w (α i) (F.associatedDegree.polynomialOrbitCoordinates w v).coord
    change F.higherHorizontalMk _ (z g) =
      F.higherHorizontalMk _ (z E) + F.higherHorizontalMk _ (z A) +
        F.higherHorizontalMk _ (z U) + F.higherHorizontalMk _ (z Q)
    rw [← map_add, ← map_add, ← map_add]
    exact (F.higherHorizontalMk_eq _ _ _).mpr (hcoeff i)
  refine ⟨K, ?_, ?_, ?_⟩
  · simp only [K, map_mul, map_inv, hg, hE, hA, hU, hQ, inv_one, one_mul]
  · dsimp only [K]
    group
  · intro i
    apply (F.rankCoefficientOrbitHom_eq_one_iff hs w (α i) K).mp
    simp only [K, map_mul, map_inv]
    rw [hhom i]
    group

end Erdos3.DegreeRankLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PointwiseSymbolBudget
namespace OAI

section

namespace Erdos3

theorem shift_le_power_succ {p : ℝ} (hp : 0 ≤ p) (C : ℕ) :
    p + C ≤ (p + 2) ^ (C + 1) := by
  induction C with
  | zero => simp only [Nat.cast_zero, add_zero, zero_add, pow_one]; linarith
  | succ C ih =>
    have hpow : 1 ≤ (p + 2) ^ (C + 1) := one_le_pow₀ (by linarith)
    calc
      p + (C + 1 : ℕ) ≤ (p + 2) ^ (C + 1) + 1 := by push_cast; linarith
      _ ≤ (p + 2) ^ (C + 1) * (p + 2) := by nlinarith
      _ = (p + 2) ^ (C + 1 + 1) := (pow_succ _ _).symm

theorem shifted_self_power_le_base_power {p : ℝ} (hp : 0 ≤ p) (C : ℕ) :
    (p + C) ^ C ≤ (p + 2) ^ ((C + 1) * C) := by
  calc
    _ ≤ ((p + 2) ^ (C + 1)) ^ C := pow_le_pow_left₀ (by positivity) (shift_le_power_succ hp C) C
    _ = _ := (pow_mul _ _ _).symm

theorem exists_symbol_extension_budget (a c₀ c₁ c₂ c₃ c₄ : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q₁ := (p + c₀) ^ c₀ + (p + 2) ^ a + p + 2
      let q₂ := (q₁ + c₁) ^ c₁ + (q₁ + c₂) ^ c₂ + q₁ + 2
      let q₃ := (q₂ + c₃) ^ c₃ + q₂ + 2
      (p + c₀) ^ c₀ + (q₂ + c₃) ^ c₃ + (q₃ + c₄) ^ c₄ ≤ (p + 2) ^ C := by
  let Q₁ : Polynomial ℕ := (Polynomial.X + Polynomial.C c₀) ^ c₀ +
    (Polynomial.X + 2) ^ a + Polynomial.X + 2
  let Q₂ : Polynomial ℕ := (Q₁ + Polynomial.C c₁) ^ c₁ + (Q₁ + Polynomial.C c₂) ^ c₂ + Q₁ + 2
  let Q₃ : Polynomial ℕ := (Q₂ + Polynomial.C c₃) ^ c₃ + Q₂ + 2
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C c₀) ^ c₀ +
    (Q₂ + Polynomial.C c₃) ^ c₃ + (Q₃ + Polynomial.C c₄) ^ c₄
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨(C + 1) * C, by nlinarith, ?_⟩
  intro p hp
  apply le_trans _ (shifted_self_power_le_base_power hp C)
  simpa [B, Q₁, Q₂, Q₃, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

section

namespace Erdos3

theorem symbol_spanning_count_bound (s d m k : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hk : (k : ℝ) ≤ p) :
    ((d * (s + 1) * (m + 1) ^ s * k : ℕ) : ℝ) ≤ (p + (s + 3)) ^ (s + 3) := by
  have hdim := NilpotentLieFiltration.symbol_dimension_bound_le_power s d m hp hd hm
  have hbase : p + (s + 2 : ℝ) ≤ p + (s + 3 : ℝ) := by linarith
  have hdim' : ((d * (s + 1) * (m + 1) ^ s : ℕ) : ℝ) ≤
      (p + (s + 3)) ^ (s + 2) :=
    hdim.trans (pow_le_pow_left₀ (by positivity) hbase _)
  rw [Nat.cast_mul]
  calc
    _ ≤ (p + (s + 3)) ^ (s + 2) * (p + (s + 3)) :=
      mul_le_mul hdim' (hk.trans (le_add_of_nonneg_right (by positivity))) (by positivity) (by positivity)
    _ = (p + (s + 3)) ^ (s + 3) := (pow_succ (p + (s + 3)) (s + 2)).symm

theorem symbol_spanning_parameter_ge (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ (p + (s + 3)) ^ (s + 3) := by
  apply (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ s + 3)).trans
  simpa only [pow_one] using pow_le_pow_right₀
    (by have := Nat.cast_nonneg (α := ℝ) s; linarith : (1 : ℝ) ≤ p + (s + 3))
    (by omega : 1 ≤ s + 3)

theorem symbol_spanning_parameter_power_bound (s k : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ((p + (s + 3)) ^ (s + 3) + 2) ^ k ≤
      (p + 2) ^ (((s + 4) * (s + 3) + 2) * k) := by
  apply polynomial_budget_comp hp (by positivity) ((s + 4) * (s + 3)) k _ le_rfl
  simpa only [Nat.cast_add, Nat.cast_ofNat] using shifted_self_power_le_base_power hp (s + 3)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledProductReconstruction
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]
  [∀ a, LieAlgebra ℚ (M a)]
  {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realification_liePiEval_liePiMap (φ : ∀ a, L →ₗ⁅ℚ⁆ M a)
    (x : ℝ ⊗[ℚ] L) (a : α) :
    realificationLieHom (liePiEval a) (realificationLieHom (liePiMap φ) x) =
      realificationLieHom (φ a) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Fintype α] {κ : α → Type*}

theorem realification_pi_basis_repr (f : ∀ a, Basis (κ a) ℚ (M a))
    (x : ℝ ⊗[ℚ] (∀ a, M a)) (a : α) (i : κ a) :
    ((Pi.basis f).baseChange ℝ).repr x ⟨a, i⟩ =
      ((f a).baseChange ℝ).repr (realificationLieHom (liePiEval a) x) i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp only [realificationLieHom_tmul, Basis.baseChange_repr_tmul,
      Pi.basis_repr, liePiEval_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

theorem exists_controlled_rational_image_reconstruction (s : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ {ι κ L M : Type*} [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (hM : LieModule.lowerCentralSeries ℚ M M s = ⊥)
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Λ : Subgroup (NilpotentLieBCHGroup M s hM))
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (_hH : 1 ≤ H)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (_hΛin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates f Λ)
    (hΛout : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m)
    (_hcL : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (_hcM : ∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H)
    (_hφ : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (_hcover : Λ.map realificationHom ⊓ (realificationMap (hnil := hL) (hM := hM) φ).range ≤
      (Γ.map realificationHom).map (realificationMap (hnil := hL) (hM := hM) φ))
    (u : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL) ⧸
      Γ.map realificationHom) → ℂ)
    (_hker : ∀ k ∈ (realificationMap (hnil := hL) (hM := hM) φ).ker, ∀ x,
      u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x))
    (ℓ B : ℝ≥0)
    (_hu : letI := realificationQuotientMetricSpace e Γ l hl hΓ; LipschitzWith ℓ u)
    (_hub : ∀ x, ‖u x‖ ≤ B)
    (p : ℝ) (_hp : 0 ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p) (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hℓp : (ℓ : ℝ) ≤ Real.exp p) (_hBp : (B : ℝ) ≤ Real.exp p),
    letI := realificationQuotientMetricSpace f Λ m hm hΛout
    ∃ (v : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) s (realification_lowerCentralSeries_eq_bot hM) ⧸
      Λ.map realificationHom) → ℂ) (K : ℝ≥0),
      (K : ℝ) ≤ Real.exp ((p + N) ^ N) ∧ LipschitzWith K v ∧ (∀ y, ‖v y‖ ≤ 2 * B) ∧
      ∀ x, v (QuotientGroup.mk (realificationMap (hnil := hL) (hM := hM) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨C, _, hrep⟩ := exists_bounded_image_representatives s
  obtain ⟨D, _, hprod⟩ := exists_bch_triple_product_exp_bound s 1
  obtain ⟨F, _, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s 1
  obtain ⟨E, _, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s D
  obtain ⟨Z, _, hlog⟩ := exists_bchLogMetricConstant_exp_bound s
  obtain ⟨N, hN, hbudget⟩ := exists_generalReconstructionLogBudget_bound C D E F Z
  refine ⟨N, hN, ?_⟩
  intro ι κ L M _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL hM e f φ Γ Λ l m H hl hm hH
    hΓ hΛin hΛout hcL hcM hφ hcover u hker ℓ B hu hub p hp hι hκ hHp hmp hℓp hBp

  classical
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (e.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] M) := (f.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hL) (e.baseChange ℝ)
  let := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := realification_lowerCentralSeries_eq_bot hL) (e.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
  let Φ := realificationMap (hnil := hL) (hM := hM) φ
  let J := Φ.range
  obtain ⟨Q, hQ, hJ⟩ := exists_realified_image_defining_matrix (hL := hL) (hM := hM) e f φ hH hφ
  let HQ : ℝ≥0 := (2 * ((Fintype.card ι + 1) * (H * rationalKernelHeight (Fintype.card κ) H) ^ Fintype.card ι) : ℕ)
  have hQabs : ∀ i j, |(Q i j : ℝ)| ≤ HQ := by
    intro i j
    change |(Q i j : ℝ)| ≤ ((2 * ((Fintype.card ι + 1) *
      (H * rationalKernelHeight (Fintype.card κ) H) ^ Fintype.card ι) : ℕ) : ℝ)
    exact (hQ i j).abs_real_le
  let R := (((p + 2) ^ 4 + C) ^ C) + (p + 2) ^ 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let q := p + R + 1
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  let S := {g | g ∈ J ∧ ∀ i, |(f.baseChange ℝ).repr g.coord i| ≤ Real.exp R}
  have hrepS : ∀ y : CosetImage Φ (Λ.map realificationHom),
      ∃ x, projectToCosetImage Φ (Λ.map realificationHom) x = y ∧ Φ x ∈ S := by
    intro y
    obtain ⟨x, hx, hxb⟩ := hrep hL hM e f φ Λ m H p hm hΛin hcL hφ hp hι hκ hHp hmp y
    exact ⟨x, hx, ⟨⟨x, rfl⟩, hxb⟩⟩
  have hlarge {g} (hg : g ∈ S) : ∀ i, |(f.baseChange ℝ).repr g.coord i| ≤ Real.exp ((q + 2) ^ 1) := by
    intro i
    apply (hg.2 i).trans
    apply Real.exp_le_exp.mpr
    dsimp [q]
    simp only [pow_one]
    linarith
  let W : ℝ≥0 := ⟨Real.exp ((q + D) ^ D), Real.exp_nonneg _⟩
  have hW : 1 ≤ W := Real.one_le_exp (by positivity)
  have hprodS : ∀ x ∈ S, ∀ y ∈ S, ∀ i, |(f.baseChange ℝ).repr (y⁻¹ * x).coord i| ≤ W := by
    intro x hx y hy i
    have h := hprod (f.baseChange ℝ) (lieStructureConstants f) H q
      (realification_lowerCentralSeries_eq_bot hM) y⁻¹ x 1
      (fun i j k => (realLieBasis_structure f i j k).symm) hq (hκ.trans hpq)
      (hHp.trans (Real.exp_le_exp.mpr hpq)) hcM
      (fun j => by simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hlarge hy j)
      (hlarge hx) (fun j => by simp only [coord_one, map_zero, Finsupp.zero_apply, abs_zero]; positivity) i
    change |(f.baseChange ℝ).repr (y⁻¹ * x).coord i| ≤ Real.exp ((q + D) ^ D)
    simpa only [mul_one] using h
  obtain ⟨Kleft, _, hKleftBound, hKleft⟩ := hleft (f.baseChange ℝ) (lieStructureConstants f) H q
    (realification_lowerCentralSeries_eq_bot hM)
    (fun i j k => (realLieBasis_structure f i j k).symm) hq (hκ.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) hcM
  obtain ⟨ε, hε, hεinv, hgap⟩ := exists_uniform_lattice_image_gap (f.baseChange ℝ)
    (lieStructureConstants f) (fun i j k => (realLieBasis_structure f i j k).symm) hcM
    Q HQ W Kleft hW hQabs m hm J (Λ.map realificationHom) hJ
    (realification_subgroup_grid f Λ m hΛout) S (fun _ h => h.1) hprodS
    (fun y hy => hKleft y⁻¹ (fun j => by
      simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hlarge hy j))
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_image_section e f φ.toLinearMap hH hφ
  have hσB : ∀ i j, |(e.baseChange ℝ).repr (σ.baseChange ℝ ((f.baseChange ℝ) j)) i| ≤
      (rationalKernelHeight (Fintype.card κ) H : ℝ) := by
    intro i j
    rw [linearMap_baseChange_basis]
    exact (hσH i j).abs_real_le
  let T := bchLogMetricConstant s (Fintype.card κ) H 1
  let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ)
    (rationalKernelHeight (Fintype.card κ) H) * ((Fintype.card κ : ℝ≥0) + 1) * T
  have hlift := exists_local_metric_lifts_on_image
    (hnil := realification_lowerCentralSeries_eq_bot hL) (hM := realification_lowerCentralSeries_eq_bot hM)
    (e.baseChange ℝ) (f.baseChange ℝ) (realificationLieHom φ) (σ.baseChange ℝ)
    (linearMap_baseChange_image_section φ.toLinearMap σ hσ) (rationalKernelHeight (Fintype.card κ) H)
    hσB (lieStructureConstants f) (fun i j k => (realLieBasis_structure f i j k).symm) hcM
  let := realificationQuotientMetricSpace e Γ l hl hΓ
  have hpull : LipschitzWith ℓ (fun x => u (QuotientGroup.mk x)) := by
    simpa only [mul_one, Function.comp_def] using hu.comp
      (quotientMetricSpace_lipschitz_mk (e.baseChange ℝ) (Γ.map realificationHom)
        (realification_subgroup_closed_discrete e Γ l hl hΓ).1)
  obtain ⟨v, hv, hLip, hbound⟩ := exists_ambient_image_reconstruction Φ (Γ.map realificationHom)
    (Λ.map realificationHom) (realification_subgroup_closed_discrete f Λ m hm hΛout).1
    hcover (fun x => u (QuotientGroup.mk x)) hker
    (fun γ hγ x => congrArg u (QuotientGroup.eq.mpr (by
      simpa only [mul_inv_rev, inv_mul_cancel_left, inv_mul_cancel_right] using
        (Γ.map realificationHom).inv_mem hγ)))
    S ℓ K B T⁻¹ ε (inv_pos.mpr (bchLogMetricConstant_pos _ _ _ _)) hε hpull
    (fun x => hub _) hrepS hgap hlift
  let r := generalReconstructionLogBudget C D E F Z p
  obtain ⟨hr, hpr, h18, h48, h24, hZr, hEr, hFr⟩ :=
    generalReconstructionLogBudget_bounds C D E F Z hp
  have hexp : Real.exp p ≤ Real.exp r := Real.exp_le_exp.mpr hpr
  let Asec := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ)
    (rationalKernelHeight (Fintype.card κ) H)
  let Ndim : ℝ≥0 := (Fintype.card κ : ℝ≥0) + 1
  let Den : ℝ≥0 := (matrixDenominator Q * m : ℕ)
  let Row : ℝ≥0 := Ndim * (HQ + 1)
  let Box : ℝ≥0 := ⟨bchBoxCoordinateBound s (Fintype.card κ) H W,
    bchBoxCoordinateBound_nonneg _ _ _ W.coe_nonneg⟩
  have hAsec : (Asec : ℝ) ≤ Real.exp r :=
    (imageSection_bound_le_exp _ _ H hp hι hκ hHp).trans (Real.exp_le_exp.mpr h18)
  have hNdim : (Ndim : ℝ) ≤ Real.exp r := by
    apply le_trans _ hexp
    change (Fintype.card κ : ℝ) + 1 ≤ Real.exp p
    exact (by linarith : (Fintype.card κ : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
  have hT : (T : ℝ) ≤ Real.exp r :=
    (hlog _ H p hp hκ hHp).trans (Real.exp_le_exp.mpr hZr)
  have hDen : (Den : ℝ) ≤ Real.exp r :=
    (imageDefiningDenominator_le_exp Q (Fintype.card ι) H m hQ hp hι hκ hHp hmp).trans
      (Real.exp_le_exp.mpr h48)
  have hRow : (Row : ℝ) ≤ Real.exp r := by
    apply le_trans _ (Real.exp_le_exp.mpr h24)
    exact imageDefiningRow_bound_le_exp _ _ H hp hι hκ hHp
  have hBox : (Box : ℝ) ≤ Real.exp r := by
    have hpqd : p ≤ q + D := hpq.trans (le_add_of_nonneg_right (Nat.cast_nonneg D))
    have hwbound : (W : ℝ) ≤ Real.exp ((q + D + 2) ^ D) := by
      change Real.exp ((q + D) ^ D) ≤ _
      exact Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) D)
    have hh := (bchBoxCoordinateBound_le_bchBoxMetricConstant s (Fintype.card κ) H W).trans
      (hbox _ H W (q + D) (by positivity) (hκ.trans hpqd)
        (hHp.trans (Real.exp_le_exp.mpr hpqd)) hwbound)
    exact hh.trans (Real.exp_le_exp.mpr hEr)
  have hY : (Kleft : ℝ) ≤ Real.exp r := hKleftBound.trans (Real.exp_le_exp.mpr hFr)
  have hεformula : (ε : ℝ)⁻¹ = (T : ℝ) * Kleft + Den * Row * Box * T * Kleft + 1 := by
    rw [hεinv]
    change _ = (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * Kleft +
      ((matrixDenominator Q * m : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * ((HQ : ℝ) + 1)) *
        bchBoxCoordinateBound s (Fintype.card κ) H W *
        (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * Kleft + 1
    ring
  have htotal := generalReconstructionConstant_le_exp ℓ B Asec Ndim T Den Row Box Kleft ε r hr
    (hℓp.trans hexp) (hBp.trans hexp) hAsec hNdim hT hDen hRow hBox hY hεformula
  exact ⟨v, _, htotal.trans (Real.exp_le_exp.mpr (hbudget p hp)), hLip, hbound, hv⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedOrbitNormalization
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem eval_zero_eq_coefficient (p : VectorPolynomial σ R V) :
    eval (fun _ => 0) p = coefficients p 0 := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v => simp [MvPolynomial.aeval_zero', MvPolynomial.constantCoeff_eq]
  | add p q hp hq => simp [hp, hq]

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem horizontal_bch (a b : L) :
    lieQuotientMap (F.layerIdeal 2) (lieBCH s a b) =
      lieQuotientMap (F.layerIdeal 2) a + lieQuotientMap (F.layerIdeal 2) b := by
  rw [map_lieBCH]
  apply lieBCH_eq_add_of_lie_eq_zero
    (lie_quotient_lowerCentralSeries_eq_bot F.lowerCentralSeries_eq_bot (F.layerIdeal 2))
  rw [← LieHom.map_lie]
  apply (lieQuotientMap_eq_zero _ _).mpr
  exact F.lie_mem (show a ∈ F.layer 1 by rw [F.one_eq_top]; trivial)
    (show b ∈ F.layer 1 by rw [F.one_eq_top]; trivial)

def horizontalLog (g : F.Group) : L ⧸ F.layerIdeal 2 := lieQuotientMap (F.layerIdeal 2) g.coord

@[simp] theorem horizontalLog_mul (g h : F.Group) :
    F.horizontalLog (g * h) = F.horizontalLog g + F.horizontalLog h := F.horizontal_bch _ _

@[simp] theorem horizontalLog_inv (g : F.Group) : F.horizontalLog g⁻¹ = -F.horizontalLog g :=
  map_neg (lieQuotientMap (F.layerIdeal 2)) g.coord

theorem normalizedShift_horizontal_zero (h : σ → ℚ) (p : VectorPolynomial σ ℚ L)
    (ε γ : F.Group)
    (heq : (⟨eval h p⟩ : F.Group) * (⟨eval (fun _ => 0) p⟩ : F.Group)⁻¹ = ε * γ) :
    coefficients (normalizedShiftLog s h (-ε.coord) (-γ.coord) p - p) 0 ∈ F.layer 2 := by
  have hh := congrArg F.horizontalLog heq
  simp only [horizontalLog_mul, horizontalLog_inv] at hh
  rw [← sub_eq_add_neg] at hh
  change lieQuotientMap (F.layerIdeal 2) (eval h p) -
    lieQuotientMap (F.layerIdeal 2) (eval (fun _ => 0) p) =
    lieQuotientMap (F.layerIdeal 2) ε.coord + lieQuotientMap (F.layerIdeal 2) γ.coord at hh
  have hsolve := (sub_eq_iff_eq_add).mp hh
  apply (lieQuotientMap_eq_zero (F.layerIdeal 2) _).mp
  rw [← eval_zero_eq_coefficient]
  simp only [map_sub, eval_normalizedShiftLog, F.horizontal_bch, map_neg, zero_add]
  rw [hsolve]
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {τ L : Type*} [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

theorem dilationPair_coefficients_mem (r : ℚ) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L))
    (hq : ∀ a, coefficients q a ∈ F.dilationPairLayer r (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (a : τ →₀ ℕ) :
    coefficients q a ∈ F.dilationPairSubalgebra r := by
  by_cases ha : a = 0
  · rw [ha, hq0]
    exact (F.dilationPairSubalgebra r).zero_mem
  · have hpos : 0 < Finsupp.weight w a :=
      NilpotentLieFiltration.positive_weight_of_ne_zero w hw ha
    exact F.dilationPairLayer_antitone r (Nat.succ_le_of_lt hpos) (hq a)

noncomputable def restrictDilationPairPolynomial (r : ℚ) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L))
    (hq : ∀ a, coefficients q a ∈ F.dilationPairLayer r (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    VectorPolynomial τ ℚ (F.dilationPairSubalgebra r) :=
  restrictCoefficients (F.dilationPairSubalgebra r).toSubmodule q
    (F.dilationPair_coefficients_mem r w hw q hq hq0)

theorem restrictDilationPairPolynomial_eval (r : ℚ) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L))
    (hq : ∀ a, coefficients q a ∈ F.dilationPairLayer r (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (x : τ → ℚ) :
    (eval (V := F.dilationPairSubalgebra r) x
      (F.restrictDilationPairPolynomial r w hw q hq hq0) : L × L) = eval x q :=
  eval_restrictCoefficients (F.dilationPairSubalgebra r).toSubmodule q
    (F.dilationPair_coefficients_mem r w hw q hq hq0) x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def weightedGroupInclusion (c : σ → ℕ) :
    (F.weightedFiltration c).Group →* F.Group :=
  NilpotentLieBCHGroup.mapOfSteps (F.weightedSubalgebra c).incl

theorem weightedGroupInclusion_injective (c : σ → ℕ) :
    Function.Injective (F.weightedGroupInclusion c) :=
  NilpotentLieBCHGroup.mapOfSteps_injective _ (fun _ _ h => Subtype.ext h)

noncomputable def weightedNormalizationLog (p : VectorPolynomial τ ℚ L) (a b : F.Group) :
    VectorPolynomial τ ℚ L :=
  lieBCH s (lieBCH s (monomial 0 (-a.coord)) p) (monomial 0 (-b.coord))

theorem weightedNormalizationLog_adapted (c : σ → ℕ) (v : τ → ℕ)
    {p : VectorPolynomial τ ℚ L} (hp : F.WeightedAdapted c v p) (a b : F.Group) :
    F.WeightedAdapted c v (F.weightedNormalizationLog p a b) :=
  F.weightedAdapted_bch c v s
    (F.weightedAdapted_bch c v s (F.weightedAdapted_constant c v _) hp)
    (F.weightedAdapted_constant c v _)

theorem weightedNormalizationLog_eval (p : VectorPolynomial τ ℚ L) (a b : F.Group)
    (x : τ → ℚ) :
    eval x (F.weightedNormalizationLog p a b) =
      (a⁻¹ * (⟨eval x p⟩ : F.Group) * b⁻¹).coord := by
  simp only [weightedNormalizationLog, eval_lieBCH, eval_monomial,
    Finsupp.prod_zero_index, one_smul, NilpotentLieBCHGroup.coord_mul,
    NilpotentLieBCHGroup.coord_inv]

theorem weightedNormalizationLog_zero (p : VectorPolynomial τ ℚ L) (a b : F.Group)
    (hzero : (⟨eval (fun _ => 0) p⟩ : F.Group) = a * b) :
    coefficients (F.weightedNormalizationLog p a b) 0 = 0 := by
  rw [← eval_zero_eq_coefficient, F.weightedNormalizationLog_eval, hzero]
  simp

noncomputable def normalizedWeightedOrbit (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (a b : F.Group)
    (hzero : (⟨eval (fun _ => 0) p⟩ : F.Group) = a * b) :
    (F.weightedFiltration c).PolynomialOrbit v :=
  F.restrictWeightedOrbit c v hv (F.weightedNormalizationLog p a b)
    (F.weightedNormalizationLog_adapted c v hp a b) (F.weightedNormalizationLog_zero p a b hzero)

theorem normalizedWeightedOrbit_eval (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (a b : F.Group)
    (hzero : (⟨eval (fun _ => 0) p⟩ : F.Group) = a * b) (x : τ → ℤ) :
    F.weightedGroupInclusion c ((F.weightedFiltration c).polynomialOrbitEval v x
      (F.normalizedWeightedOrbit c v hv p hp a b hzero)) =
      a⁻¹ * (⟨eval (fun i => (x i : ℚ)) p⟩ : F.Group) * b⁻¹ := by
  apply NilpotentLieBCHGroup.ext
  change (((F.weightedFiltration c).polynomialOrbitEval v x
    (F.restrictWeightedOrbit c v hv _ _ _)).coord : L) = _
  rw [F.restrictWeightedOrbit_eval, F.weightedNormalizationLog_eval]

theorem normalizedWeightedOrbit_zero (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (a b : F.Group)
    (hzero : (⟨eval (fun _ => 0) p⟩ : F.Group) = a * b) :
    (F.weightedFiltration c).polynomialOrbitEval v 0
      (F.normalizedWeightedOrbit c v hv p hp a b hzero) = 1 := by
  apply F.weightedGroupInclusion_injective c
  rw [F.normalizedWeightedOrbit_eval, map_one]
  simp only [Pi.zero_apply, Int.cast_zero, hzero, inv_mul_cancel_left, mul_inv_cancel]

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AdditiveTriplePolynomialRestriction
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem additiveTriple_coefficients_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (a : τ →₀ ℕ) :
    coefficients q a ∈ F.additiveTripleSubalgebra i hi c hc := by
  by_cases ha : a = 0
  · rw [ha, hq0]
    exact (F.additiveTripleSubalgebra i hi c hc).zero_mem
  · have hpos : 0 < Finsupp.weight w a :=
      NilpotentLieFiltration.positive_weight_of_ne_zero w hw ha
    exact F.additiveTripleLayer_antitone i c (Nat.succ_le_of_lt hpos) (hq a)

noncomputable def restrictAdditiveTriplePolynomial (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    VectorPolynomial τ ℚ (F.additiveTripleSubalgebra i hi c hc) :=
  restrictCoefficients (F.additiveTripleSubalgebra i hi c hc).toSubmodule q
    (F.additiveTriple_coefficients_mem i hi c hc w hw q hq hq0)

theorem restrictAdditiveTriplePolynomial_adapted (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    (F.additiveTripleFiltration i hi c hc).Adapted w
      (F.restrictAdditiveTriplePolynomial i hi c hc w hw q hq hq0) := by
  apply ((F.additiveTripleFiltration i hi c hc).adapted_iff_coefficients w _).mpr
  intro a
  change (coefficients (F.restrictAdditiveTriplePolynomial i hi c hc w hw q hq hq0) a : L × L × L) ∈
    F.additiveTripleLayer i c (Finsupp.weight w a)
  rw [restrictAdditiveTriplePolynomial, coefficients_restrictCoefficients]
  exact hq a

theorem restrictAdditiveTriplePolynomial_eval (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (x : τ → ℚ) :
    (eval (V := F.additiveTripleSubalgebra i hi c hc) x
      (F.restrictAdditiveTriplePolynomial i hi c hc w hw q hq hq0) : L × L × L) = eval x q :=
  eval_restrictCoefficients (F.additiveTripleSubalgebra i hi c hc).toSubmodule q
    (F.additiveTriple_coefficients_mem i hi c hc w hw q hq hq0) x

noncomputable def restrictAdditiveTripleOrbit (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) : (F.additiveTripleFiltration i hi c hc).PolynomialOrbit w :=
  NilpotentLieFiltration.polynomialOrbitOfLog
    (F.restrictAdditiveTriplePolynomial i hi c hc w hw q hq hq0)
    (F.restrictAdditiveTriplePolynomial_adapted i hi c hc w hw q hq hq0)

theorem restrictAdditiveTripleOrbit_eval (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (x : τ → ℤ) :
    (((F.additiveTripleFiltration i hi c hc).polynomialOrbitEval w x
      (F.restrictAdditiveTripleOrbit i hi c hc w hw q hq hq0)).coord : L × L × L) =
      eval (fun j => (x j : ℚ)) q :=
  F.restrictAdditiveTriplePolynomial_eval i hi c hc w hw q hq hq0 _

theorem restrictAdditiveTripleOrbit_zero (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    (F.additiveTripleFiltration i hi c hc).polynomialOrbitEval w 0
      (F.restrictAdditiveTripleOrbit i hi c hc w hw q hq hq0) = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change (((F.additiveTripleFiltration i hi c hc).polynomialOrbitEval w 0
    (F.restrictAdditiveTripleOrbit i hi c hc w hw q hq hq0)).coord : L × L × L) = 0
  rw [F.restrictAdditiveTripleOrbit_eval]
  simpa only [Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using hq0

theorem exists_additiveTripleOrbit_of_coefficients (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    ∃ g : (F.additiveTripleFiltration i hi c hc).PolynomialOrbit w,
      (F.additiveTripleFiltration i hi c hc).polynomialOrbitEval w 0 g = 1 ∧
      ∀ x : τ → ℤ,
        (((F.additiveTripleFiltration i hi c hc).polynomialOrbitEval w x g).coord : L × L × L) =
          eval (fun j => (x j : ℚ)) q :=
  ⟨F.restrictAdditiveTripleOrbit i hi c hc w hw q hq hq0,
    F.restrictAdditiveTripleOrbit_zero i hi c hc w hw q hq hq0,
    F.restrictAdditiveTripleOrbit_eval i hi c hc w hw q hq hq0⟩

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MultiaffineTriplePolynomial
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

variable {σ V : Type*} [DecidableEq σ] [AddCommGroup V] [Module ℚ V]

noncomputable def splitTriple (i : σ) (u v : MvPolynomial (Option σ) ℚ)
    (p : VectorPolynomial σ ℚ V) : VectorPolynomial (Option σ) ℚ (V × V × V) :=
  pair (substitute (splitCoordinatePolynomial i (u + v)) p)
    (pair (substitute (splitCoordinatePolynomial i u) p)
      (substitute (splitCoordinatePolynomial i v) p))

theorem eval_splitTriple (i : σ) (u v : MvPolynomial (Option σ) ℚ)
    (p : VectorPolynomial σ ℚ V) (x : Option σ → ℚ) :
    eval x (splitTriple i u v p) =
      (eval (Function.update (fun j => x (some j)) i (MvPolynomial.aeval (R := ℚ) x (u + v))) p,
       eval (Function.update (fun j => x (some j)) i (MvPolynomial.aeval (R := ℚ) x u)) p,
       eval (Function.update (fun j => x (some j)) i (MvPolynomial.aeval (R := ℚ) x v)) p) := by
  simp only [splitTriple, eval_pair, eval_substitute, splitCoordinatePolynomial_eval]

theorem splitTriple_zero (i : σ) (u v : MvPolynomial (Option σ) ℚ)
    (p : VectorPolynomial σ ℚ V) (hp : coefficients p 0 = 0)
    (hu : MvPolynomial.aeval (R := ℚ) (fun _ : Option σ => (0 : ℚ)) u = 0)
    (hv : MvPolynomial.aeval (R := ℚ) (fun _ : Option σ => (0 : ℚ)) v = 0) :
    coefficients (splitTriple i u v p) 0 = 0 := by
  rw [← eval_zero_eq_coefficient, eval_splitTriple]
  simp only [map_add, hu, hv, add_zero, Function.update_eq_self, eval_zero_eq_coefficient, hp]
  rfl

end VectorPolynomial

namespace MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem splitTriple_neutral (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p)
    (a : Option σ →₀ ℕ) :
    tripleNeutral (coefficients (splitTriple i u v p) a) =
      coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p) a := by
  have h := congrArg (fun q => coefficients q a) (F.split_substitution_add i hi u v hp)
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply] at h
  simp only [splitTriple, coefficients_pair]
  change coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p) a +
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i v) p) a -
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i (u + v)) p) a = _
  rw [h]
  abel

theorem splitTriple_left (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p)
    (a : Option σ →₀ ℕ) :
    tripleLeft (coefficients (splitTriple i u v p) a) =
      coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p -
        VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p) a := by
  have h := congrArg (fun q => coefficients q a) (F.split_substitution_add i hi u v hp)
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply] at h
  simp only [splitTriple, coefficients_pair, map_sub, Finsupp.sub_apply]
  change coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i (u + v)) p) a -
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i v) p) a = _
  rw [h]
  abel

theorem splitTriple_right (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p)
    (a : Option σ →₀ ℕ) :
    tripleRight (coefficients (splitTriple i u v p) a) =
      coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i v) p -
        VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p) a := by
  have h := congrArg (fun q => coefficients q a) (F.split_substitution_add i hi u v hp)
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply] at h
  simp only [splitTriple, coefficients_pair, map_sub, Finsupp.sub_apply]
  change coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i (u + v)) p) a -
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p) a = _
  rw [h]
  abel

theorem splitTriple_coefficient_mem (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ)
    (hu : u ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    (hv : v ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) (a : Option σ →₀ ℕ) :
    coefficients (splitTriple i u v p) a ∈
      F.additiveTripleLayer i (omittedCoordinateWeight i) (Finsupp.weight (fun _ : Option σ => 1) a) := by
  rw [F.mem_additiveTripleLayer, F.splitTriple_neutral i hi u v hp,
    F.splitTriple_left i hi u v hp, F.splitTriple_right i hi u v hp]
  exact ⟨F.split_substitution_zero_weighted i hp a,
    F.split_substitution_sub_mem_active i u hu hp a,
    F.split_substitution_sub_mem_active i v hv hp a⟩

end MultidegreeLieFiltration

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PolarizedCoefficientPermutation
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def polynomialOrbitOfLog (p : VectorPolynomial σ ℚ L) (hp : F.Adapted p) : F.PolynomialOrbit :=
  ⟨⟨p⟩, hp⟩

@[simp] theorem polynomialOrbitOfLog_eval (p : VectorPolynomial σ ℚ L) (hp : F.Adapted p)
    (x : σ → ℤ) :
    (F.polynomialOrbitEval x (F.polynomialOrbitOfLog p hp)).coord = eval (fun i => (x i : ℚ)) p := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def constantMultidegreeOrbit (a : F.Group) : F.PolynomialOrbit :=
  ⟨⟨monomial 0 a.coord⟩, F.monomial_mem_adaptedSubmodule 0 (by
    change a.coord ∈ F.layer 0
    rw [F.zero_eq_top]
    trivial)⟩

theorem constantMultidegreeOrbit_eval (a : F.Group) (x : σ → ℤ) :
    F.polynomialOrbitEval x (F.constantMultidegreeOrbit a) = a := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => (x i : ℚ)) (monomial 0 a.coord) = a.coord
  rw [eval_monomial, Finsupp.prod_zero_index, one_smul]

noncomputable def normalizeMultidegreeOrbit (p : F.PolynomialOrbit) (a b : F.Group) :
    F.PolynomialOrbit := F.constantMultidegreeOrbit a⁻¹ * p * F.constantMultidegreeOrbit b⁻¹

theorem normalizeMultidegreeOrbit_eval (p : F.PolynomialOrbit) (a b : F.Group) (x : σ → ℤ) :
    F.polynomialOrbitEval x (F.normalizeMultidegreeOrbit p a b) =
      a⁻¹ * F.polynomialOrbitEval x p * b⁻¹ := by
  simp only [normalizeMultidegreeOrbit, map_mul, F.constantMultidegreeOrbit_eval]

theorem normalizeMultidegreeOrbit_zero (p : F.PolynomialOrbit) (a b : F.Group)
    (h : F.polynomialOrbitEval 0 p = a * b) :
    F.polynomialOrbitEval 0 (F.normalizeMultidegreeOrbit p a b) = 1 := by
  rw [F.normalizeMultidegreeOrbit_eval, h]
  simp

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem adapted_rationalDilation (r : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) : F.Adapted (weightedDilation (fun _ : σ => 1) r p) := by
  intro a
  rw [coefficients_weightedDilation]
  exact (F.layer _).smul_mem _ (hp a)

noncomputable def rationalDilationOrbit (r : ℚ) (p : F.PolynomialOrbit) : F.PolynomialOrbit :=
  F.polynomialOrbitOfLog (weightedDilation (fun _ : σ => 1) r (p.log F))
    (F.adapted_rationalDilation r _ (p.adapted F))

theorem rationalDilationOrbit_eval (r : ℚ) (p : F.PolynomialOrbit) (x : σ → ℤ) :
    (F.polynomialOrbitEval x (F.rationalDilationOrbit r p)).coord =
      eval (fun i => r * (x i : ℚ)) (p.log F) := by
  change eval (fun i => (x i : ℚ)) (weightedDilation (fun _ : σ => 1) r (p.log F)) = _
  rw [eval_weightedDilation]
  simp only [pow_one]

theorem rationalDilationOrbit_rescaled (r : ℚ) (q : ℤ) (hr : r * (q : ℚ) = 1)
    (p : F.PolynomialOrbit) (x : σ → ℤ) :
    F.polynomialOrbitEval (fun i => q * x i) (F.rationalDilationOrbit r p) =
      F.polynomialOrbitEval x p := by
  apply NilpotentLieBCHGroup.ext
  rw [F.rationalDilationOrbit_eval, F.polynomialOrbitEval_coord]
  simp only [Int.cast_mul, ← mul_assoc, hr, one_mul]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem strictUpperLayer_zero : F.strictUpperLayer 0 = ⊤ := by
  have h : F.ordinary.layer 1 ≤ (F.strictUpperLayer 0).toSubmodule := by
    rw [F.degree_eq]
    apply iSup_le
    intro a
    apply iSup_le
    intro ha
    have hlt : (0 : σ → ℕ) < a := by
      refine lt_iff_le_not_ge.mpr ⟨fun _ => Nat.zero_le _, ?_⟩
      intro hzero
      have heq : a = 0 := le_antisymm hzero (fun _ => Nat.zero_le _)
      simp only [heq, Pi.zero_apply, Finset.sum_const_zero] at ha
      omega
    intro x hx
    exact F.layer_le_strictUpperLayer hlt hx
  apply top_unique
  intro x _
  exact h (by simp only [F.ordinary.one_eq_top, Submodule.mem_top])

theorem dilationPairLayer_zero (q : ℚ) : F.dilationPairLayer q 0 = ⊤ := by
  apply top_unique
  intro x _
  rw [F.mem_dilationPairLayer]
  simp only [F.zero_eq_top, F.strictUpperLayer_zero, Submodule.mem_top, LieSubmodule.mem_top,
    true_and]

theorem dilationPair_degree_comap (q : ℚ) (n : ℕ) :
    (F.ordinary.dilationPairFiltration q).layer n =
      ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i),
        (F.dilationPairLayer q a).comap (F.ordinary.dilationPairSubalgebra q).incl.toLinearMap := by
  let K := F.ordinary.dilationPairSubalgebra q
  let ι := K.incl.toLinearMap
  by_cases hn : n = 0
  · subst n
    have hleft : (F.ordinary.dilationPairFiltration q).layer 0 = ⊤ := by
      apply top_unique
      rw [← (F.ordinary.dilationPairFiltration q).one_eq_top]
      exact (F.ordinary.dilationPairFiltration q).antitone (by decide : 0 ≤ 1)
    rw [hleft]
    symm
    apply top_unique
    apply le_iSup_of_le (0 : σ → ℕ)
    apply le_iSup_of_le (show 0 ≤ ∑ _ : σ, 0 from Nat.zero_le _)
    rw [F.dilationPairLayer_zero, Submodule.comap_top]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hr (a : σ → ℕ) (ha : n ≤ ∑ i, a i) :
        F.dilationPairLayer q a ≤ LinearMap.range ι := by
      intro x hx
      exact ⟨⟨x, F.dilationPairLayer_le_subalgebra q a (hn1.trans ha) hx⟩, rfl⟩
    change (F.ordinary.dilationPairLayer q n).comap ι = _
    rw [← F.dilationPairDegreeLayer_eq, dilationPairDegreeLayer]
    rw [submodule_comap_iSup_of_le_range ι Subtype.val_injective _
      (fun a => iSup_le (fun ha => hr a ha))]
    apply iSup_congr
    intro a
    exact submodule_comap_iSup_of_le_range ι Subtype.val_injective _ (hr a)

noncomputable def dilationPairMultidegree (q : ℚ) :
    MultidegreeLieFiltration σ (F.ordinary.dilationPairSubalgebra q) s bound where
  ordinary := F.ordinary.dilationPairFiltration q
  layer a := (F.dilationPairLayer q a).comap (F.ordinary.dilationPairSubalgebra q).incl.toLinearMap
  antitone := fun _ _ h _ hx => F.dilationPairLayer_antitone q h hx
  zero_eq_top := by rw [F.dilationPairLayer_zero, Submodule.comap_top]
  lie_mem := fun hx hy => F.dilationPairLayer_lie_mem q hx hy
  terminal a ha := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    change x.val = (0 : L × L)
    have h : x.val ∈ F.dilationPairLayer q a := hx
    simpa only [F.dilationPairLayer_terminal q a ha, Submodule.mem_bot] using h
  degree_eq := F.dilationPair_degree_comap q

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

namespace NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem dilationPair_top_group_relation (q : ℤ)
    (g : (F.dilationPairFiltration (q : ℚ)).Group)
    (hg : g ∈ (F.dilationPairFiltration (q : ℚ)).subgroup s) :
    (NilpotentLieBCHGroup.map (F.dilationPairFirst (q : ℚ)) g : F.Group) =
      (NilpotentLieBCHGroup.map (F.dilationPairSecond (q : ℚ)) g) ^ (q ^ s) := by
  apply NilpotentLieBCHGroup.ext
  rw [NilpotentLieBCHGroup.coord_zpow]
  change F.dilationPairFirst (q : ℚ) g.coord = (q ^ s) • F.dilationPairSecond (q : ℚ) g.coord
  rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow]
  exact F.dilationPairTop_relation (q : ℚ) hg

end NilpotentLieFiltration

namespace MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem dilationPair_top_group_relation (q : ℤ)
    (g : (F.dilationPairMultidegree (q : ℚ)).Group)
    (hg : g ∈ (F.dilationPairMultidegree (q : ℚ)).subgroup bound) :
    (NilpotentLieBCHGroup.map (F.ordinary.dilationPairFirst (q : ℚ)) g : F.Group) =
      (NilpotentLieBCHGroup.map (F.ordinary.dilationPairSecond (q : ℚ)) g) ^ (q ^ ∑ i, bound i) := by
  apply NilpotentLieBCHGroup.ext
  rw [NilpotentLieBCHGroup.coord_zpow]
  change g.coord.val.1 = (q ^ ∑ i, bound i) • g.coord.val.2
  rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow]
  exact F.dilationPairLayer_top_relation (q : ℚ) hg

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem exists_splitTriple_orbit (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ)
    (hu : u ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    (hv : v ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    (hu0 : MvPolynomial.aeval (R := ℚ) (fun _ : Option σ => (0 : ℚ)) u = 0)
    (hv0 : MvPolynomial.aeval (R := ℚ) (fun _ : Option σ => (0 : ℚ)) v = 0)
    (p : VectorPolynomial σ ℚ L) (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) :
    ∃ g : (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).PolynomialOrbit (fun _ : Option σ => 1),
      (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ 0 g = 1 ∧
      ∀ x : Option σ → ℤ,
        (((F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
          (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ x g).coord : L × L × L) =
          eval (fun j => (x j : ℚ)) (splitTriple i u v p) :=
  F.exists_additiveTripleOrbit_of_coefficients i hi (omittedCoordinateWeight i)
    (omittedCoordinateWeight_le_one i) (fun _ => 1) (fun _ => by decide) (splitTriple i u v p)
    (F.splitTriple_coefficient_mem i hi u v hu hv hp) (splitTriple_zero i u v p hp0 hu0 hv0)

theorem exists_coordinateAddition_orbit (i : σ) (hi : bound i ≤ 1)
    (p : F.PolynomialOrbit) (hp0 : F.polynomialOrbitEval 0 p = 1) :
    ∃ g : (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).PolynomialOrbit (fun _ : Option σ => 1),
      (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ 0 g = 1 ∧
      ∀ x : Option σ → ℤ,
        (((F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
          (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ x g).coord : L × L × L) =
          ((F.polynomialOrbitEval
              (Function.update (fun j => x (some j)) i (x (some i) + x none)) p).coord,
           (F.polynomialOrbitEval (fun j => x (some j)) p).coord,
           (F.polynomialOrbitEval (Function.update (fun j => x (some j)) i (x none)) p).coord) := by
  have hz : coefficients (p.log F) 0 = 0 := by
    have h := congrArg NilpotentLieBCHGroup.coord hp0
    simpa only [F.polynomialOrbitEval_coord, NilpotentLieBCHGroup.coord_one,
      Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using h
  have hX (j : Option σ) : (MvPolynomial.X j : MvPolynomial (Option σ) ℚ) ∈
      weightedSupportLE (fun _ : Option σ => 1) 1 := by
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : Option σ => 1) (Finsupp.single j 1) (1 : ℚ)
  obtain ⟨g, hg0, hg⟩ := F.exists_splitTriple_orbit i hi (MvPolynomial.X (some i)) (MvPolynomial.X none)
    (hX _) (hX _) (by simp) (by simp) (p.log F) (p.adapted F) hz
  refine ⟨g, hg0, fun x => ?_⟩
  have hcast (y : σ → ℤ) (n : ℤ) : (fun j => (Function.update y i n j : ℚ)) =
      Function.update (fun j => (y j : ℚ)) i (n : ℚ) := by
    funext j
    by_cases hj : j = i <;> simp [hj, Function.update_of_ne]
  simpa only [eval_splitTriple, F.polynomialOrbitEval_coord, map_add, MvPolynomial.aeval_X,
    Function.update_eq_self, hcast, Int.cast_add] using hg x

theorem exists_normalizedCoordinateAddition_orbit (i : σ) (hi : bound i ≤ 1)
    (p : F.PolynomialOrbit) (a b : F.Group) (hp0 : F.polynomialOrbitEval 0 p = a * b) :
    ∃ g : (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).PolynomialOrbit (fun _ : Option σ => 1),
      (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ 0 g = 1 ∧
      ∀ x : Option σ → ℤ,
        (((F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
          (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ x g).coord : L × L × L) =
          ((a⁻¹ * F.polynomialOrbitEval
              (Function.update (fun j => x (some j)) i (x (some i) + x none)) p * b⁻¹).coord,
           (a⁻¹ * F.polynomialOrbitEval (fun j => x (some j)) p * b⁻¹).coord,
           (a⁻¹ * F.polynomialOrbitEval (Function.update (fun j => x (some j)) i (x none)) p * b⁻¹).coord) := by
  obtain ⟨g, hg0, hg⟩ := F.exists_coordinateAddition_orbit i hi (F.normalizeMultidegreeOrbit p a b)
    (F.normalizeMultidegreeOrbit_zero p a b hp0)
  exact ⟨g, hg0, fun x => by simpa only [F.normalizeMultidegreeOrbit_eval] using hg x⟩

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def dilationPairLog (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) :
    VectorPolynomial σ ℚ (F.ordinary.dilationPairSubalgebra q) :=
  F.ordinary.restrictDilationPairPolynomial q (fun _ : σ => 1) (fun _ => by decide)
    (dilationPair (fun _ : σ => 1) q p)
    (F.ordinary.dilationPair_coefficients _ q (F.adapted_ordinary hp))
    (by simp only [coefficients_dilationPair, hp0, smul_zero]; rfl)

theorem dilationPairMultidegree_mem_layer (q : ℚ) (a : σ → ℕ)
    (x : F.ordinary.dilationPairSubalgebra q) :
    x ∈ (F.dilationPairMultidegree q).layer a ↔ x.val ∈ F.dilationPairLayer q a := Iff.rfl

theorem dilationPairLog_adapted (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) :
    (F.dilationPairMultidegree q).Adapted (F.dilationPairLog q p hp hp0) := by
  intro a
  rw [F.dilationPairMultidegree_mem_layer]
  rw [dilationPairLog, NilpotentLieFiltration.restrictDilationPairPolynomial,
    coefficients_restrictCoefficients, coefficients_dilationPair]
  have hw : Finsupp.weight (fun _ : σ => 1) a = ∑ i, a i := by
    simp only [Finsupp.weight_eq_sum, smul_eq_mul, mul_one]
  rw [hw]
  exact F.dilationPairLayer_diagonal q _ (hp a)

omit [DecidableEq σ] in
theorem dilationPairLog_eval (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) (x : σ → ℚ) :
    (eval (V := F.ordinary.dilationPairSubalgebra q) x (F.dilationPairLog q p hp hp0) : L × L) =
      (eval (fun i => q * x i) p, eval x p) := by
  rw [dilationPairLog, NilpotentLieFiltration.restrictDilationPairPolynomial_eval,
    eval_dilationPair]
  simp only [pow_one]

noncomputable def dilationPairPolynomialOrbit (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) :
    (F.dilationPairMultidegree q).PolynomialOrbit :=
  (F.dilationPairMultidegree q).polynomialOrbitOfLog
    (F.dilationPairLog q p hp hp0) (F.dilationPairLog_adapted q p hp hp0)

theorem dilationPairPolynomialOrbit_eval (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) (x : σ → ℤ) :
    (((F.dilationPairMultidegree q).polynomialOrbitEval x
      (F.dilationPairPolynomialOrbit q p hp hp0)).coord : L × L) =
      (eval (fun i => q * (x i : ℚ)) p, eval (fun i => (x i : ℚ)) p) :=
  F.dilationPairLog_eval q p hp hp0 _

theorem dilationPairPolynomialOrbit_zero (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) :
    (F.dilationPairMultidegree q).polynomialOrbitEval 0
      (F.dilationPairPolynomialOrbit q p hp hp0) = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change (((F.dilationPairMultidegree q).polynomialOrbitEval 0
    (F.dilationPairPolynomialOrbit q p hp hp0)).coord : L × L) = (0 : L × L)
  have h := F.dilationPairPolynomialOrbit_eval q p hp hp0 0
  simp only [Pi.zero_apply, Int.cast_zero, mul_zero, eval_zero_eq_coefficient, hp0] at h
  exact h

theorem exists_integer_dilationPair_orbit (q : ℤ) (p : F.PolynomialOrbit)
    (hp0 : F.polynomialOrbitEval 0 p = 1) :
    ∃ g : (F.dilationPairMultidegree (q : ℚ)).PolynomialOrbit,
      (F.dilationPairMultidegree (q : ℚ)).polynomialOrbitEval 0 g = 1 ∧
      ∀ x : σ → ℤ,
        (((F.dilationPairMultidegree (q : ℚ)).polynomialOrbitEval x g).coord : L × L) =
          ((F.polynomialOrbitEval (fun i => q * x i) p).coord, (F.polynomialOrbitEval x p).coord) := by
  have hz : coefficients (p.log F) 0 = 0 := by
    have h := congrArg NilpotentLieBCHGroup.coord hp0
    simpa only [F.polynomialOrbitEval_coord, NilpotentLieBCHGroup.coord_one,
      Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using h
  refine ⟨F.dilationPairPolynomialOrbit (q : ℚ) (p.log F) (p.adapted F) hz,
    F.dilationPairPolynomialOrbit_zero (q : ℚ) (p.log F) (p.adapted F) hz, fun x => ?_⟩
  simpa only [F.polynomialOrbitEval_coord, Int.cast_mul] using
    F.dilationPairPolynomialOrbit_eval (q : ℚ) (p.log F) (p.adapted F) hz x

theorem exists_normalized_dilationPair_orbit (q : ℤ) (p : F.PolynomialOrbit)
    (a b : F.Group) (hp0 : F.polynomialOrbitEval 0 p = a * b) :
    ∃ g : (F.dilationPairMultidegree (q : ℚ)).PolynomialOrbit,
      (F.dilationPairMultidegree (q : ℚ)).polynomialOrbitEval 0 g = 1 ∧
      ∀ x : σ → ℤ,
        (((F.dilationPairMultidegree (q : ℚ)).polynomialOrbitEval x g).coord : L × L) =
          ((a⁻¹ * F.polynomialOrbitEval (fun i => q * x i) p * b⁻¹).coord,
            (a⁻¹ * F.polynomialOrbitEval x p * b⁻¹).coord) := by
  obtain ⟨g, hg0, hg⟩ := F.exists_integer_dilationPair_orbit q (F.normalizeMultidegreeOrbit p a b)
    (F.normalizeMultidegreeOrbit_zero p a b hp0)
  exact ⟨g, hg0, fun x => by simpa only [F.normalizeMultidegreeOrbit_eval] using hg x⟩

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

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareGradedRelative
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

noncomputable def unitMonomial (n : ℕ) : Unit →₀ ℕ := Finsupp.single () n

@[simp] theorem weight_unitMonomial (n : ℕ) :
    Finsupp.weight (fun _ : Unit => 1) (unitMonomial n) = n := by
  simp [unitMonomial, Finsupp.weight_single]

@[simp] theorem unitMonomial_weight (α : Unit →₀ ℕ) :
    unitMonomial (Finsupp.weight (fun _ : Unit => 1) α) = α := by
  have h : α = Finsupp.single () (α ()) := by
    apply Finsupp.ext
    intro i
    cases i
    simp
  rw [h]
  simp [unitMonomial, Finsupp.weight_single]

theorem unitMonomial_injective : Function.Injective unitMonomial := by
  intro m n h
  have hh := congrArg (Finsupp.weight (fun _ : Unit => 1)) h
  simpa only [weight_unitMonomial] using hh

@[simp] theorem unitMonomial_add (m n : ℕ) :
    unitMonomial (m + n) = unitMonomial m + unitMonomial n :=
  Finsupp.single_add _ _ _

namespace NilpotentLieFiltration

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev AssociatedGraded (F : NilpotentLieFiltration L s) :=
  F.PolynomialSymbol (fun _ : Unit => 1)

noncomputable def associatedGradedIndexEquiv (ω : ι → ℕ) :
    SymbolBasisIndex (fun _ : Unit => 1) ω ≃ ι where
  toFun z := z.val.2
  invFun i := ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg unitMonomial z.property.symm).trans (unitMonomial_weight z.val.1)
    · rfl
  right_inv _ := rfl

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def associatedGradedBasis : Basis ι ℚ F.AssociatedGraded :=
  (F.polynomialSymbolBasis b ω hlayers (fun _ : Unit => 1)).reindex (associatedGradedIndexEquiv ω)

@[simp] theorem associatedGradedBasis_apply (i : ι) :
    F.associatedGradedBasis b ω hlayers i =
      F.polynomialSymbolBasis b ω hlayers (fun _ : Unit => 1)
        ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩ := by
  rw [associatedGradedBasis, Basis.reindex_apply]
  rfl

theorem associatedGradedBasis_repr (x : F.AssociatedGraded) (i : ι) :
    (F.associatedGradedBasis b ω hlayers).repr x i =
      (F.polynomialSymbolBasis b ω hlayers (fun _ : Unit => 1)).repr x
        ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩ := by
  rw [associatedGradedBasis, Basis.repr_reindex_apply]
  rfl

theorem associatedGradedBasis_bracket (i j k : ι) :
    (F.associatedGradedBasis b ω hlayers).repr
      ⁅F.associatedGradedBasis b ω hlayers i, F.associatedGradedBasis b ω hlayers j⁆ k =
      if ω i + ω j = ω k then b.repr ⁅b i, b j⁆ k else 0 := by
  classical
  rw [F.associatedGradedBasis_repr, F.associatedGradedBasis_apply,
    F.associatedGradedBasis_apply, F.polynomialSymbolBasis_bracket]
  simp only [← unitMonomial_add, unitMonomial_injective.eq_iff]

noncomputable def associatedGradedFiltration : NilpotentLieFiltration F.AssociatedGraded s :=
  F.polynomialSymbolFiltration (fun _ : Unit => 1)

theorem associatedGradedFiltration_layer (j : ℕ) :
    F.associatedGradedFiltration.layer j =
      Submodule.span ℚ (F.associatedGradedBasis b ω hlayers '' {i | j ≤ ω i}) := by
  rw [associatedGradedFiltration, F.polynomialSymbolFiltration_layer b ω hlayers]
  congr 1
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.val.2, hz, ?_⟩
    rw [F.associatedGradedBasis_apply]
    congr 1
    exact (associatedGradedIndexEquiv ω).left_inv z
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩, hi, ?_⟩
    exact (F.associatedGradedBasis_apply b ω hlayers i).symm

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def gradedMonomialLinear (j : ℕ) :
    F.layer j →ₗ[ℚ] F.adaptedLieSubalgebra (fun _ : Unit => 1) where
  toFun v := ⟨monomial (unitMonomial j) (v : L),
    F.monomial_mem_adaptedSubmodule (fun _ : Unit => 1) (unitMonomial j)
      (by simpa only [weight_unitMonomial] using v.property)⟩
  map_add' x y := by
    apply Subtype.ext
    exact TensorProduct.tmul_add _ _ _
  map_smul' a x := by
    apply Subtype.ext
    exact TensorProduct.tmul_smul a _ _

@[simp] theorem gradedMonomialLinear_coe (j : ℕ) (v : F.layer j) :
    (F.gradedMonomialLinear j v : VectorPolynomial Unit ℚ L) = monomial (unitMonomial j) (v : L) := rfl

noncomputable def associatedGradedPieceMap (j : ℕ) : F.layer j →ₗ[ℚ] F.AssociatedGraded :=
  (F.polynomialSymbolMap (fun _ : Unit => 1)).toLinearMap.comp (F.gradedMonomialLinear j)

@[simp] theorem associatedGradedPieceMap_apply (j : ℕ) (v : F.layer j) :
    F.associatedGradedPieceMap j v =
      F.polynomialSymbolMap (fun _ : Unit => 1) (F.gradedMonomialLinear j v) := rfl

theorem associatedGradedPieceMap_eq_zero_iff (j : ℕ) (v : F.layer j) :
    F.associatedGradedPieceMap j v = 0 ↔ (v : L) ∈ F.layer (j + 1) := by
  rw [F.associatedGradedPieceMap_apply, F.polynomialSymbolMap_eq_zero_iff]
  simp only [F.gradedMonomialLinear_coe, coefficients_monomial]
  constructor
  · intro h
    simpa only [Finsupp.single_eq_same, weight_unitMonomial] using h (unitMonomial j)
  · intro h α
    by_cases hα : unitMonomial j = α
    · subst α
      simpa only [Finsupp.single_eq_same, weight_unitMonomial] using h
    · rw [Finsupp.single_eq_of_ne (Ne.symm hα)]
      exact Submodule.zero_mem _

theorem associatedGradedPieceMap_lie (i j : ℕ) (u : F.layer i) (v : F.layer j) :
    ⁅F.associatedGradedPieceMap i u, F.associatedGradedPieceMap j v⁆ =
      F.associatedGradedPieceMap (i + j) ⟨⁅(u : L), (v : L)⁆, F.lie_mem u.property v.property⟩ := by
  simp only [F.associatedGradedPieceMap_apply]
  rw [← LieHom.map_lie]
  apply congrArg (F.polynomialSymbolMap (fun _ : Unit => 1))
  apply Subtype.ext
  change ⁅monomial (unitMonomial i) (u : L), monomial (unitMonomial j) (v : L)⁆ = _
  rw [lie_monomial, ← unitMonomial_add]
  rfl

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem associatedGradedPieceMap_coordinate (j : ℕ) (v : F.layer j) (i : ι) :
    (F.associatedGradedBasis b ω hlayers).repr (F.associatedGradedPieceMap j v) i =
      if j = ω i then b.repr (v : L) i else 0 := by
  classical
  rw [F.associatedGradedBasis_repr, F.associatedGradedPieceMap_apply,
    F.polynomialSymbolBasis_repr_map]
  simp only [F.gradedMonomialLinear_coe, coefficients_monomial]
  by_cases h : j = ω i
  · simp [h]
  · have h' : unitMonomial j ≠ unitMonomial (ω i) := fun he => h (unitMonomial_injective he)
    simp [h, h']

theorem associatedGradedPieceMap_basis (j : ℕ) (i : ι) (hi : j ≤ ω i) (he : j = ω i) :
    F.associatedGradedPieceMap j
      ⟨b i, by rw [hlayers]; exact Submodule.subset_span ⟨i, hi, rfl⟩⟩ =
        F.associatedGradedBasis b ω hlayers i := by
  classical
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext k
  rw [F.associatedGradedPieceMap_coordinate]
  simp only [Basis.repr_self, Finsupp.single_apply]
  by_cases h : i = k
  · subst k
    simp only [he, ite_true]
  · simp only [h, ite_false, ite_self]

theorem associatedGradedPieceMap_range (j : ℕ) :
    LinearMap.range (F.associatedGradedPieceMap j) =
      Submodule.span ℚ (F.associatedGradedBasis b ω hlayers '' {i | ω i = j}) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [basis_mem_span_image_iff]
    intro i hi
    rw [F.associatedGradedPieceMap_coordinate]
    exact if_neg (Ne.symm hi)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨⟨b i, ?_⟩, ?_⟩
    · rw [hlayers]
      exact Submodule.subset_span ⟨i, hi.symm.le, rfl⟩
    · exact F.associatedGradedPieceMap_basis b ω hlayers j i hi.symm.le hi.symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (U : LieSubalgebra ℚ F.AssociatedGraded)

noncomputable def gradedRefiltrationLayer (j : ℕ) : Submodule ℚ L :=
  (U.toSubmodule.comap (F.associatedGradedPieceMap j)).map (F.layer j).subtype

theorem mem_gradedRefiltrationLayer (j : ℕ) (v : L) :
    v ∈ F.gradedRefiltrationLayer U j ↔
      ∃ hv : v ∈ F.layer j, F.associatedGradedPieceMap j ⟨v, hv⟩ ∈ U := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hv, hU⟩
    exact ⟨⟨v, hv⟩, hU, rfl⟩

theorem mem_gradedRefiltrationLayer_iff (j : ℕ) (v : F.layer j) :
    (v : L) ∈ F.gradedRefiltrationLayer U j ↔ F.associatedGradedPieceMap j v ∈ U := by
  rw [F.mem_gradedRefiltrationLayer]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨v.property, h⟩⟩

theorem gradedRefiltrationLayer_le (j : ℕ) : F.gradedRefiltrationLayer U j ≤ F.layer j := by
  intro v hv
  exact ((F.mem_gradedRefiltrationLayer U j v).mp hv).choose

theorem layer_succ_le_gradedRefiltrationLayer (j : ℕ) :
    F.layer (j + 1) ≤ F.gradedRefiltrationLayer U j := by
  intro v hv
  rw [F.mem_gradedRefiltrationLayer]
  refine ⟨F.antitone (Nat.le_succ j) hv, ?_⟩
  rw [(F.associatedGradedPieceMap_eq_zero_iff j _).mpr hv]
  exact U.zero_mem

theorem gradedRefiltrationLayer_antitone : Antitone (F.gradedRefiltrationLayer U) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact (F.gradedRefiltrationLayer_le U j).trans
      ((F.antitone hlt).trans (F.layer_succ_le_gradedRefiltrationLayer U i))
  · exact le_rfl

theorem gradedRefiltrationLayer_lie_mem {i j : ℕ} {v z : L}
    (hv : v ∈ F.gradedRefiltrationLayer U i) (hz : z ∈ F.gradedRefiltrationLayer U j) :
    ⁅v, z⁆ ∈ F.gradedRefiltrationLayer U (i + j) := by
  obtain ⟨hv, hUv⟩ := (F.mem_gradedRefiltrationLayer U i v).mp hv
  obtain ⟨hz, hUz⟩ := (F.mem_gradedRefiltrationLayer U j z).mp hz
  rw [F.mem_gradedRefiltrationLayer]
  refine ⟨F.lie_mem hv hz, ?_⟩
  rw [← F.associatedGradedPieceMap_lie i j ⟨v, hv⟩ ⟨z, hz⟩]
  exact U.lie_mem hUv hUz

theorem gradedRefiltrationLayer_terminal : F.gradedRefiltrationLayer U (s + 1) = ⊥ :=
  bot_unique ((F.gradedRefiltrationLayer_le U (s + 1)).trans F.terminal.le)

noncomputable def gradedRefiltrationSubalgebra : LieSubalgebra ℚ L :=
  { F.gradedRefiltrationLayer U 1 with
    lie_mem' := fun hv hz => F.gradedRefiltrationLayer_antitone U (by decide : 1 ≤ 1 + 1)
      (F.gradedRefiltrationLayer_lie_mem U hv hz) }

noncomputable def gradedRefiltration :
    NilpotentLieFiltration (F.gradedRefiltrationSubalgebra U) s where
  layer j := (F.gradedRefiltrationLayer U j).comap (F.gradedRefiltrationSubalgebra U).incl.toLinearMap
  antitone := fun _ _ hij _ hv => F.gradedRefiltrationLayer_antitone U hij hv
  one_eq_top := by
    apply top_unique
    intro v _
    exact v.property
  lie_mem := fun hv hz => F.gradedRefiltrationLayer_lie_mem U hv hz
  terminal := by
    apply bot_unique
    intro v hv
    change v = 0
    apply Subtype.ext
    exact (Submodule.mem_bot ℚ).mp ((F.gradedRefiltrationLayer_terminal U) ▸ hv)

@[simp] theorem mem_gradedRefiltration_layer (j : ℕ) (v : F.gradedRefiltrationSubalgebra U) :
    v ∈ (F.gradedRefiltration U).layer j ↔ (v : L) ∈ F.gradedRefiltrationLayer U j := Iff.rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squareDiagonalLayer (j : ℕ) : F.layer j →ₗ[ℚ] F.squareFiltration.layer j where
  toFun x := ⟨⟨(x, x), (F.mem_squareLieSubalgebra _).mpr (by simp)⟩,
    x.property, x.property, by simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def squareRelativeLayer (j : ℕ) (hj : 1 ≤ j) :
    F.layer (j + 1) →ₗ[ℚ] F.squareFiltration.layer j where
  toFun x := ⟨⟨(x, 0), (F.mem_squareLieSubalgebra _).mpr (by
    simpa only [sub_zero] using F.antitone (Nat.add_le_add_right hj 1) x.property)⟩,
    F.antitone (Nat.le_succ j) x.property, (F.layer j).zero_mem, by
      change (x : L) - 0 ∈ F.layer (j + 1)
      simpa only [sub_zero] using x.property⟩
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; simp

noncomputable def squareGradedDiagonalPiece (j : ℕ) :
    F.layer j →ₗ[ℚ] F.squareFiltration.AssociatedGraded :=
  (F.squareFiltration.associatedGradedPieceMap j).comp (F.squareDiagonalLayer j)

noncomputable def squareGradedRelativePiece (j : ℕ) (hj : 1 ≤ j) :
    F.layer (j + 1) →ₗ[ℚ] F.squareFiltration.AssociatedGraded :=
  (F.squareFiltration.associatedGradedPieceMap j).comp (F.squareRelativeLayer j hj)

theorem squareGradedDiagonalPiece_eq_zero_iff (j : ℕ) (x : F.layer j) :
    F.squareGradedDiagonalPiece j x = 0 ↔ (x : L) ∈ F.layer (j + 1) := by
  change F.squareFiltration.associatedGradedPieceMap j (F.squareDiagonalLayer j x) = 0 ↔ _
  rw [F.squareFiltration.associatedGradedPieceMap_eq_zero_iff]
  change ((x : L) ∈ F.layer (j + 1) ∧ (x : L) ∈ F.layer (j + 1) ∧
    (x : L) - x ∈ F.layer (j + 1 + 1)) ↔ _
  simp only [sub_self, Submodule.zero_mem, and_true, and_self]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem squareGradedPiece_decomposition (j : ℕ) (hj : 1 ≤ j)
    (x : F.squareFiltration.layer j) :
    F.squareFiltration.associatedGradedPieceMap j x =
      F.squareGradedDiagonalPiece j ⟨x.val.val.2, x.property.2.1⟩ +
      F.squareGradedRelativePiece j hj ⟨x.val.val.1 - x.val.val.2, x.property.2.2⟩ := by
  change F.squareFiltration.associatedGradedPieceMap j x =
    F.squareFiltration.associatedGradedPieceMap j (F.squareDiagonalLayer j _) +
      F.squareFiltration.associatedGradedPieceMap j (F.squareRelativeLayer j hj _)
  rw [← map_add]
  apply congrArg (F.squareFiltration.associatedGradedPieceMap j)
  apply Subtype.ext
  apply Subtype.ext
  change x.val.val = (x.val.val.2, x.val.val.2) + (x.val.val.1 - x.val.val.2, 0)
  apply Prod.ext
  · change x.val.val.1 = x.val.val.2 + (x.val.val.1 - x.val.val.2)
    abel
  · exact (add_zero _).symm

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledIntegralCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (e : Basis (Fin d) ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def integralOrderedBasisProduct (B : ℕ) (z : Fin d → ℤ) :
    NilpotentLieBCHGroup L s hnil :=
  orderedBasisProduct e hnil (fun j => (B : ℚ) * (z j : ℚ))

namespace IsCentralLieBasis

variable {e} (he : IsCentralLieBasis e)
include he

end IsCentralLieBasis
end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (e : Basis (Fin d) ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def realIntegralOrderedBasisProduct (B : ℕ) (z : Fin d → ℤ) :
    NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil) :=
  realOrderedBasisProduct (e.baseChange ℝ) (realification_lowerCentralSeries_eq_bot hnil)
    (fun j => (B : ℝ) * (z j : ℝ))

namespace IsCentralLieBasis

variable {e} (he : IsCentralLieBasis e)
include he

end IsCentralLieBasis
end Erdos3

end

section

namespace Erdos3

open Module

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultidegreeCoordinateFreezing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

def retainedCoordinateWeight (S : Finset σ) (i : σ) : ℕ := if i ∈ S then 1 else 0

def freezeCoordinates (S : Finset σ) (b : σ → ℤ) (x : S → ℤ) (i : σ) : ℤ :=
  if h : i ∈ S then x ⟨i, h⟩ else b i

noncomputable def freezingPolynomial (S : Finset σ) (b : σ → ℤ) (i : σ) :
    MvPolynomial S ℚ :=
  if h : i ∈ S then MvPolynomial.X ⟨i, h⟩ else MvPolynomial.C (b i : ℚ)

theorem freezingPolynomial_support (S : Finset σ) (b : σ → ℤ) (i : σ) :
    freezingPolynomial S b i ∈ weightedSupportLE (fun _ : S => 1) (retainedCoordinateWeight S i) := by
  by_cases hi : i ∈ S
  · simp only [freezingPolynomial, retainedCoordinateWeight, dif_pos hi, if_pos hi]
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : S => 1) (Finsupp.single (⟨i, hi⟩ : S) 1) (1 : ℚ)
  · simp only [freezingPolynomial, retainedCoordinateWeight, dif_neg hi, if_neg hi]
    exact weightedSupportLE_C _ _ _

theorem freezingPolynomial_eval (S : Finset σ) (b : σ → ℤ) (x : S → ℤ) (i : σ) :
    MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (freezingPolynomial S b i) =
      (freezeCoordinates S b x i : ℚ) := by
  by_cases hi : i ∈ S <;> simp [freezingPolynomial, freezeCoordinates, hi]

theorem retainedCoordinate_degree [Fintype σ] (S : Finset σ) (bound : σ → ℕ) :
    multidegreeWeight (retainedCoordinateWeight S) bound = ∑ i ∈ S, bound i := by
  simp [multidegreeWeight, retainedCoordinateWeight]

namespace MultidegreeLieFiltration

open VectorPolynomial

variable {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem exists_normalized_frozen_orbit (S : Finset σ) (b : σ → ℤ)
    (p : F.PolynomialOrbit) (a γ : F.Group)
    (hzero : F.polynomialOrbitEval (freezeCoordinates S b 0) p = a * γ) :
    ∃ q : (F.weightedFiltration (retainedCoordinateWeight S)).PolynomialOrbit (fun _ : S => 1),
      (F.weightedFiltration (retainedCoordinateWeight S)).polynomialOrbitEval _ 0 q = 1 ∧
      ∀ x : S → ℤ, F.weightedGroupInclusion (retainedCoordinateWeight S)
        ((F.weightedFiltration (retainedCoordinateWeight S)).polynomialOrbitEval _ x q) =
          a⁻¹ * F.polynomialOrbitEval (freezeCoordinates S b x) p * γ⁻¹ := by
  let r := VectorPolynomial.substitute (freezingPolynomial S b) (p.log F)
  have hr : F.WeightedAdapted (retainedCoordinateWeight S) (fun _ : S => 1) r :=
    F.weightedAdapted_substitute _ _ _ (freezingPolynomial_support S b) (p.adapted F)
  have heval (x : S → ℤ) : (⟨eval (fun i => (x i : ℚ)) r⟩ : F.Group) =
      F.polynomialOrbitEval (freezeCoordinates S b x) p := by
    apply NilpotentLieBCHGroup.ext
    change eval (fun i => (x i : ℚ)) r = _
    simp only [r, eval_substitute, freezingPolynomial_eval, F.polynomialOrbitEval_coord]
  have hz : (⟨eval (fun _ => 0) r⟩ : F.Group) = a * γ := by
    simpa only [Pi.zero_apply, Int.cast_zero] using (heval 0).trans hzero
  refine ⟨F.normalizedWeightedOrbit _ _ (fun _ => by decide) r hr a γ hz,
    F.normalizedWeightedOrbit_zero _ _ (fun _ => by decide) r hr a γ hz, ?_⟩
  intro x
  rw [F.normalizedWeightedOrbit_eval, heval]

end MultidegreeLieFiltration

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TotalDegreeSplitDownsets
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem totalDegree_zero_layer : F.layer 0 = ⊤ := by
  apply top_unique
  rw [← F.one_eq_top]
  exact F.antitone (Nat.zero_le 1)

noncomputable def totalDegreeMultifiltration (σ : Type*) [Fintype σ] [Nonempty σ] :
    MultidegreeLieFiltration σ L s (fun _ => s) := by
  classical
  exact {
    ordinary := F
    layer := fun a => F.layer (∑ i, a i)
    antitone := fun _ _ h => F.antitone (Finset.sum_le_sum fun i _ => h i)
    zero_eq_top := by simpa only [Pi.zero_apply, Finset.sum_const_zero] using F.totalDegree_zero_layer
    lie_mem := by
      intro a b x y hx hy
      simpa only [Pi.add_apply, Finset.sum_add_distrib] using F.lie_mem hx hy
    terminal := by
      intro a ha
      change ¬∀ i, a i ≤ s at ha
      push Not at ha
      obtain ⟨i, hi⟩ := ha
      have hsum : a i ≤ ∑ j, a j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
      exact F.layer_eq_bot_above_step (hi.trans_le hsum)
    degree_eq := by
      intro n
      apply le_antisymm
      · let i : σ := Classical.choice (inferInstance : Nonempty σ)
        let a : σ → ℕ := Pi.single i n
        have hsum : ∑ j, a j = n := by simp [a]
        apply le_iSup_of_le a
        apply le_iSup_of_le (show n ≤ ∑ j, a j by omega)
        rw [hsum]
      · apply iSup_le
        intro a
        apply iSup_le
        intro ha
        exact F.antitone ha }

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {σ L : Type*} [Fintype σ] [Nonempty σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

theorem real_totalDegree_adapted (g : F.realification.PolynomialOrbit (fun _ : σ => 1)) :
    (F.totalDegreeMultifiltration σ).realification.Adapted g.log := by
  intro a
  change coefficients g.log a ∈ F.realification.layer (∑ i, a i)
  simpa only [Finsupp.weight_eq_sum, smul_eq_mul, mul_one] using
    (F.realification.adapted_iff_coefficients (fun _ : σ => 1) g.log).mp g.adapted a

noncomputable def realTotalDegreeOrbit (g : F.realification.PolynomialOrbit (fun _ : σ => 1)) :
    (F.totalDegreeMultifiltration σ).realification.PolynomialOrbit :=
  (F.totalDegreeMultifiltration σ).realification.polynomialOrbitOfLog g.log
    (F.real_totalDegree_adapted g)

set_option maxHeartbeats 1000000 in
theorem realTotalDegreeOrbit_eval (g : F.realification.PolynomialOrbit (fun _ : σ => 1))
    (x : σ → ℤ) :
    (F.totalDegreeMultifiltration σ).realification.polynomialOrbitEval x (F.realTotalDegreeOrbit g) =
      F.realification.polynomialOrbitEval (fun _ : σ => 1) x g := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped BigOperators

def totalDegreeSplitBound (s : ℕ) (b : Bool) : Fin 2 → ℕ :=
  ![if b then s else 0, if b then s - 1 else s]

def totalDegreeSplitDownset (s : ℕ) (b : Bool) : Set (Fin 2 →₀ ℕ) :=
  {a | ∀ i, a i ≤ totalDegreeSplitBound s b i}

theorem totalDegreeSplitBound_le (s : ℕ) (b : Bool) :
    totalDegreeSplitBound s b ≤ fun _ => s := by
  intro i
  fin_cases i <;> cases b <;> simp [totalDegreeSplitBound]

theorem totalDegreeSplitDownset_lower (s : ℕ) (b : Bool) :
    IsLowerSet (totalDegreeSplitDownset s b) :=
  fun _ _ hab hb i => (hab i).trans (hb i)

theorem mem_totalDegreeSplitDownset_false (s : ℕ) (a : Fin 2 →₀ ℕ) :
    a ∈ totalDegreeSplitDownset s false ↔ a 0 = 0 ∧ a 1 ≤ s := by
  simp [totalDegreeSplitDownset, totalDegreeSplitBound, Fin.forall_fin_two]

theorem mem_totalDegreeSplitDownset_true (s : ℕ) (a : Fin 2 →₀ ℕ) :
    a ∈ totalDegreeSplitDownset s true ↔ a 0 ≤ s ∧ a 1 ≤ s - 1 := by
  simp [totalDegreeSplitDownset, totalDegreeSplitBound, Fin.forall_fin_two]

theorem totalDegreeSplitDownset_covers (s : ℕ) (a : Fin 2 →₀ ℕ)
    (ha : (∑ i, a i) ≤ s) :
    a ∈ totalDegreeSplitDownset s false ∪ totalDegreeSplitDownset s true := by
  rw [Fin.sum_univ_two] at ha
  by_cases hzero : a 0 = 0
  · exact Or.inl ((mem_totalDegreeSplitDownset_false s a).mpr ⟨hzero, by omega⟩)
  · exact Or.inr ((mem_totalDegreeSplitDownset_true s a).mpr ⟨by omega, by omega⟩)

theorem totalDegreeSplitDownset_terminal {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (a : Fin 2 →₀ ℕ)
    (ha : a ∉ totalDegreeSplitDownset s false ∪ totalDegreeSplitDownset s true) :
    (F.totalDegreeMultifiltration (Fin 2)).layer (fun i => a i) = ⊥ := by
  apply F.layer_eq_bot_above_step
  exact Nat.lt_of_not_ge (fun h => ha (totalDegreeSplitDownset_covers s a h))

end Erdos3

end

end OAI

end


