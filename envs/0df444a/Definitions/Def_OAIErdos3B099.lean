-- Prove2me | Definitions.Def_OAIErdos3B099
-- name    : OAIErdos3B099
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T19:33:01.992338+00:00
-- url     : https://prove2.me/theorems/f106547d-dd2e-4fa3-9e1c-b384e4121a01
-- title:
--   OpenAI Erdős-3 split, definitions bundle 100 of 106
-- statement:
--   Definitions bundle 100 of 106 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B098`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 100 available.
--
--   Modules: `OAI.Erdos3.APFree.progressionPreimage`, `OAI.Erdos3.APFreeInterval.density`, `OAI.Erdos3.APFreeInterval.integerIndicator`, `OAI.Erdos3.APFreeInterval.integerIndicator_nat`, `OAI.Erdos3.APFreeInterval.noConfusion`, `OAI.Erdos3.APFreeInterval.parameter`, `OAI.Erdos3.APFreeInterval.reindex`, `OAI.Erdos3.DegreeRankLieFiltration.quotientLie`, `OAI.Erdos3.DegreeRankLieFiltration.quotientLie_mem`, `OAI.Erdos3.DegreeRankLieFiltration.quotientRank`, `OAI.Erdos3.FreeDegreeRankLieAlgebra`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.filtration`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.finite`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.hom_ext`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.instLieAlgebra`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.instLieRing`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.layerFamily`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.layerFamily_span`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.layerGenerators`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.layerGenerators_logHeight`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.layer_eq_span`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.lift`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.lift_basis_matrix_logHeight`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.lift_mem_layer`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.lift_of`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.lift_projection`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.mk`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.mk_surjective`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.of`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.of_mem_layer`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.projection`, `OAI.Erdos3.FreeDegreeRankLieAlgebra.projection_surjective`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.RankAlphabet`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.canonicalRankGenerators`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.canonicalRankGenerators_span`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.lift_mem_degreeRank`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.rankAlphabetVector`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.rankAlphabetVector_mem`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.rankAlphabetWeight`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.rankAlphabetWeight_pos`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.rankAlphabet_card_le`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.rankAlphabet_spans_layer`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.topRankGenerators`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.topRankGenerators_card_le`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.topRankGenerators_logHeight`, `OAI.Erdos3.FreeWeightedNilpotentLieAlgebra.topRankGenerators_span`, `OAI.Erdos3.IntegerVectorAPFree`, `OAI.Erdos3.IntegerVectorAPFree.affine_preimage`, `OAI.Erdos3.NilpotentLieBCHGroup.exists_controlled_fast_lift`, `OAI.Erdos3.NilpotentLieBCHGroup.realLinearCoordinateLift`, `OAI.Erdos3.NilpotentLieBCHGroup.realLinearCoordinateLift_coord`, `OAI.Erdos3.NilpotentLieFiltration.adaptedReducedRealSymbolHom`, `OAI.Erdos3.NilpotentLieFiltration.adaptedReducedRealSymbolHom_lift`, `OAI.Erdos3.NilpotentLieFiltration.adaptedReducedSymbolMap`, `OAI.Erdos3.NilpotentLieFiltration.adaptedReducedSymbolMap_native_basis`, `OAI.Erdos3.NilpotentLieFiltration.adaptedSquareBasis_bracket_repr_inl`, `OAI.Erdos3.NilpotentLieFiltration.adaptedSquareBasis_bracket_repr_inr`, `OAI.Erdos3.NilpotentLieFiltration.adaptedSquareBasis_structure_height`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_reduced_fast_lift`, `OAI.Erdos3.NilpotentLieFiltration.exists_lattice_ready_firstCoefficient_basis`, `OAI.Erdos3.NilpotentLieFiltration.exists_reduced_native_factorization`, `OAI.Erdos3.NilpotentLieFiltration.exists_square_rational_model`, `OAI.Erdos3.NilpotentLieFiltration.normalizedRelativeIdeal`, `OAI.Erdos3.NilpotentLieFiltration.normalizedRelativeSubmodule_lie_mem`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedDirectionalDerivative_single_bound`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientHorizontal`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientHorizontalSection`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientHorizontal_section`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientFastSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientFastSubmodule_le_horizontal_ker`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientOfPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientOfPolynomial_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientOfPolynomial_eq_of_firstJet`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientOfPolynomial_map`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientRelativeEquiv`, `OAI.Erdos3.NilpotentLieFiltration.realNormalizedFirstCoefficientMap_ker`, `OAI.Erdos3.NilpotentLieFiltration.realNormalizedFirstCoefficientMap_mem_fast_iff`, `OAI.Erdos3.NilpotentLieFiltration.realNormalizedFirstCoefficientMap_sub_mem_fast_iff`, `OAI.Erdos3.NilpotentLieFiltration.realNormalizedRelativeAdjoint`, `OAI.Erdos3.NilpotentLieFiltration.realNormalizedRelativeAdjoint_inclusion`, `OAI.Erdos3.NilpotentLieFiltration.realReducedNativeLift`, `OAI.Erdos3.NilpotentLieFiltration.realReducedNativeLift_constant`, `OAI.Erdos3.NilpotentLieFiltration.realReducedNativeLift_grid`, `OAI.Erdos3.NilpotentLieFiltration.realReducedNativeLift_slow`, `OAI.Erdos3.NilpotentLieFiltration.realReducedRelativeCoefficient`, `OAI.Erdos3.NilpotentLieFiltration.realReducedRelativeCoefficient_of_preimage`, `OAI.Erdos3.NilpotentLieFiltration.realReducedRelativeCoefficient_same_diagonal`, `OAI.Erdos3.NilpotentLieFiltration.realReducedRelativeSquareSymbolMap`, `OAI.Erdos3.NilpotentLieFiltration.realReducedRelativeSquareSymbolMap_adjoint`, `OAI.Erdos3.NilpotentLieFiltration.realReducedRelativeSquareSymbolMap_conjugation`, `OAI.Erdos3.NilpotentLieFiltration.realReducedRelativeSquareSymbolMap_conjugation_of_eq`, `OAI.Erdos3.NilpotentLieFiltration.realReducedRelativeSquareSymbolMap_projection`, `OAI.Erdos3.NilpotentLieFiltration.realReducedRelativeSquareSymbolMap_range`, `OAI.Erdos3.NilpotentLieFiltration.realShiftedCoefficient_mem_iff_tensor`, `OAI.Erdos3.NilpotentLieFiltration.reducedNativeIndex`, `OAI.Erdos3.NilpotentLieFiltration.reducedNativeIndex_injective`, `OAI.Erdos3.NilpotentLieFiltration.reducedNativeSection`, `OAI.Erdos3.NilpotentLieFiltration.reducedNativeSection_basis`, `OAI.Erdos3.NilpotentLieFiltration.reducedNativeSection_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.reducedNativeSection_coordinate_zero`, `OAI.Erdos3.NilpotentLieFiltration.reducedNativeSection_real_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.reducedNativeSection_real_coordinate_zero`, `OAI.Erdos3.NilpotentLieFiltration.reducedNativeSection_rightInverse`, `OAI.Erdos3.NilpotentLieFiltration.reducedRelativeSquareSymbolMap_lie`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareBasis_structure_height`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareFastDiagonalSubalgebra`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareFastRelativeSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareFastRelative_action_mem`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealDiagonalHom`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealFastRelative_action_mem`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealLinearLift`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealRelativePart`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealRelativePart_coord_kernel`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealRelativePart_exists_preimage`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealRelativePart_mul`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealRelativePart_mul_coord`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealRelativePart_of_factors`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealRelativePart_projection`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealRelativePart_triple_coord`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealRelative_conjugation`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealRelative_same_diagonal_mod_kernel`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealSymbolHom`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealSymbolHom_diagonal`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealSymbolKernel_bch`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealSymbolKernel_eq`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRealSymbolKernel_lie_eq_zero`, `OAI.Erdos3.NilpotentLieFiltration.relativeSquareLift_lie`, `OAI.Erdos3.NilpotentLieFiltration.squareFinBasis`, `OAI.Erdos3.NilpotentLieFiltration.squareFinBasis_layers`, `OAI.Erdos3.NilpotentLieFiltration.squareFinWeight`, `OAI.Erdos3.PatchKernel.integerLift`, `OAI.Erdos3.PolynomialPatch.castRank`, `OAI.Erdos3.PolynomialPatch.castRank_kernel_lip`, `OAI.Erdos3.PolynomialPatch.castRank_value`, `OAI.Erdos3.PolynomialPatch.formAtWeight`, `OAI.Erdos3.PolynomialPatch.formAtWeight_value`, `OAI.Erdos3.PolynomialPatch.padRank`, `OAI.Erdos3.PolynomialPatch.padRank_lip`, `OAI.Erdos3.PolynomialPatch.padRank_value`, `OAI.Erdos3.PolynomialPatch.rankWeightCode`, `OAI.Erdos3.PolynomialPatch.rankWeightCode_eq`, `OAI.Erdos3.PolynomialPatch.unitRank`, `OAI.Erdos3.PolynomialPatch.unitRank_lip`, `OAI.Erdos3.PolynomialPatch.unitRank_value`, `OAI.Erdos3.VectorPolynomial.directionalDerivative_single_coordinate`, `OAI.Erdos3.VectorPolynomial.directionalDerivative_single_scaled_bound`, `OAI.Erdos3.WeightedParameterPatch.castRank`, `OAI.Erdos3.WeightedParameterPatch.castRank_kernel_lip`, `OAI.Erdos3.WeightedParameterPatch.castRank_value`, `OAI.Erdos3.WeightedParameterPatch.padRank`, `OAI.Erdos3.WeightedParameterPatch.padRankFamily`, `OAI.Erdos3.WeightedParameterPatch.padRankFamily_value`, `OAI.Erdos3.WeightedParameterPatch.padRank_lip`, `OAI.Erdos3.WeightedParameterPatch.padRank_value`, `OAI.Erdos3.WeightedParameterPatch.product`, `OAI.Erdos3.WeightedParameterPatch.product_lip`, `OAI.Erdos3.WeightedParameterPatch.product_value`, `OAI.Erdos3.WeightedParameterPatch.unitRank`, `OAI.Erdos3.WeightedParameterPatch.unitRank_lip`, `OAI.Erdos3.WeightedParameterPatch.unitRank_value`, `OAI.Erdos3.WeightedParameterSlots.interleave`, `OAI.Erdos3.WeightedParameterSlots.interleave_center_left`, `OAI.Erdos3.WeightedParameterSlots.interleave_center_right`, `OAI.Erdos3.WeightedParameterSlots.interleave_slots`, `OAI.Erdos3.WeightedParameterSlots.placeCenter`, `OAI.Erdos3.WeightedParameterSlots.placeCenter_degree`, `OAI.Erdos3.WeightedParameterSlots.placeCenter_eval`, `OAI.Erdos3.WeightedParameterSlots.placementSubstitution_degree`, `OAI.Erdos3.ambientTorusTent`, `OAI.Erdos3.centeredTorusTent`, `OAI.Erdos3.crtProgressionWeight`, `OAI.Erdos3.cyclicIntervalSet`, `OAI.Erdos3.densityParameter`, `OAI.Erdos3.exists_adapted_free_degree_rank_model`, `OAI.Erdos3.exists_bounded_free_degree_rank_model`, `OAI.Erdos3.exists_common_rank_weight_patch_family`, `OAI.Erdos3.exists_fixed_weight_patch_function_budget`, `OAI.Erdos3.exists_patch_rank_weight_class`, `OAI.Erdos3.exists_unrestricted_fixed_weight_patch_function`, `OAI.Erdos3.exists_varying_rank_fixed_patch_function`, `OAI.Erdos3.fractionalPartBin_center_error`, `OAI.Erdos3.intervalDensity`, `OAI.Erdos3.intervalDensity_pos`, `OAI.Erdos3.intervalDensity_pos_iff`, `OAI.Erdos3.intervalIndicator`, `OAI.Erdos3.localTentKernel`, `OAI.Erdos3.localTentKernel_ge_half`, `OAI.Erdos3.localTent_translateSum_ge_half`, `OAI.Erdos3.polynomialTorusCell`, `OAI.Erdos3.progressionPreimage`, `OAI.Erdos3.progressionPreimage_subset`, `OAI.Erdos3.progressionTorusCenter`, `OAI.Erdos3.progressionTorusCutoff`, `OAI.Erdos3.residueBoxIntegerPoint`, `OAI.Erdos3.torusGridCenter`, `OAI.Erdos3.torusGridKernel`, `OAI.Erdos3.torusGrid_coordinate_cover`, `OAI.Erdos3.torusGrid_cover`, `_private.Estimates.NormalizedFixedPatchFunction.0.OAI.Erdos3.exp_neg_le_div`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B103

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FreeWeightedRankGenerators
namespace OAI

section

namespace Erdos3.FreeWeightedNilpotentLieAlgebra

open Module

variable (X : Type*) [Fintype X] (s : ℕ) (w : X → ℕ)

abbrev RankAlphabet := Σ i : Fin (s + 1), layerGenerators X s w (i.val + 1)

def rankAlphabetWeight (a : RankAlphabet X s w) : ℕ := a.1.val + 1

noncomputable def rankAlphabetVector (a : RankAlphabet X s w) : FreeWeightedNilpotentLieAlgebra X s w := a.2.val

theorem rankAlphabetWeight_pos (a : RankAlphabet X s w) : 0 < rankAlphabetWeight X s w a := Nat.succ_pos _

theorem rankAlphabetVector_mem (hw : ∀ x, 0 < w x) (a : RankAlphabet X s w) :
    rankAlphabetVector X s w a ∈ (filtration X s w hw).layer (rankAlphabetWeight X s w a) :=
  layerGenerators_mem X s w hw _ a.2.val a.2.property

theorem rankAlphabet_card_le : Fintype.card (RankAlphabet X s w) ≤
    (s + 1) * (Fintype.card X + 2) ^ (3 ^ s) := by
  classical
  simp only [RankAlphabet, Fintype.card_sigma, Fintype.card_coe]
  calc
    _ ≤ ∑ _i : Fin (s + 1), (Fintype.card X + 2) ^ (3 ^ s) :=
      Finset.sum_le_sum (fun i _ => layerGenerators_card_le X s w (i.val + 1))
    _ = _ := by simp

theorem rankAlphabet_spans_layer (hw : ∀ x, 0 < w x) (d : ℕ) (hd : 0 < d) :
    (filtration X s w hw).layer d ≤ Submodule.span ℚ
      (rankAlphabetVector X s w '' {a | rankAlphabetWeight X s w a = d}) := by
  by_cases hds : d ≤ s + 1
  · let j : Fin (s + 1) := ⟨d - 1, by omega⟩
    have hj : j.val + 1 = d := by dsimp only [j]; omega
    rw [layer_eq_span]
    apply Submodule.span_mono
    intro x hx
    have hx' : x ∈ layerGenerators X s w (j.val + 1) := by simpa only [hj, Finset.mem_coe] using hx
    exact ⟨⟨j, ⟨x, hx'⟩⟩, hj, rfl⟩
  · have hbot : (filtration X s w hw).layer d = ⊥ := by
      apply bot_unique
      exact ((filtration X s w hw).antitone (by omega : s + 1 ≤ d)).trans
        (filtration X s w hw).terminal.le
    rw [hbot]
    exact bot_le

noncomputable def topRankGenerators (k : ℕ) : Finset (FreeWeightedNilpotentLieAlgebra X s w) :=
  finiteWeightedLieValues (rankAlphabetVector X s w) (rankAlphabetWeight X s w) s k

theorem topRankGenerators_span (hw : ∀ x, 0 < w x) (k : ℕ) :
    Submodule.span ℚ (topRankGenerators X s w k : Set _) = (filtration X s w hw).rankLayer s k := by
  rw [(filtration X s w hw).rankLayer_eq_weighted_tree_span
    (rankAlphabetVector X s w) (rankAlphabetWeight X s w) (rankAlphabetWeight_pos X s w)
    (rankAlphabetVector_mem X s w hw) (rankAlphabet_spans_layer X s w hw)]
  rw [(filtration X s w hw).terminal, bot_sup_eq,
    weightedLieTreeSpan_eq_finite_span _ _ (rankAlphabetWeight_pos X s w)]
  rfl

theorem topRankGenerators_card_le (k : ℕ) :
    (topRankGenerators X s w k).card ≤
      ((s + 1) * (Fintype.card X + 2) ^ (3 ^ s) + 2) ^ (3 ^ s) :=
  (finiteWeightedLieValues_card_le (rankAlphabetVector X s w) (rankAlphabetWeight X s w) s k).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right (rankAlphabet_card_le X s w) 2) _)

theorem topRankGenerators_logHeight {ι : Type*} [Fintype ι]
    (e : Basis ι ℚ (FreeWeightedNilpotentLieAlgebra X s w)) {p : ℝ}
    (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ p)
    (hgen : ∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
      rationalLogHeight (e.repr (mk X s w x) i) ≤ p)
    (k : ℕ) (x : FreeWeightedNilpotentLieAlgebra X s w) (hx : x ∈ topRankGenerators X s w k) (i : ι) :
    rationalLogHeight (e.repr x i) ≤ (p + 3) ^ (6 * s + 2) := by
  classical
  have hv (a : RankAlphabet X s w) (j : ι) :
      rationalLogHeight (e.repr (rankAlphabetVector X s w a) j) ≤ p := by
    obtain ⟨y, hy, hya⟩ := Finset.mem_image.mp a.2.property
    change rationalLogHeight (e.repr a.2.val j) ≤ p
    rw [← hya]
    exact hgen y (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w _ hy) j
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have hraw := finiteLieTrees_coordinate_height e (rankAlphabetVector X s w)
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
    (fun a j => rationalHeightLE_ceil_exp (hv a j)) s a (Finset.mem_filter.mp ha).1 i
  apply rationalLogHeight_le_of_height hraw
  simpa only [show p + 1 + 2 = p + 3 by ring] using
    lieTreeHeight_le_exp (Fintype.card ι) ⌈Real.exp p⌉₊ s
      (hp.trans (le_add_of_nonneg_right zero_le_one))
      (hd.trans (le_add_of_nonneg_right zero_le_one)) (ceil_exp_le_exp_add_one hp)

end Erdos3.FreeWeightedNilpotentLieAlgebra

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FreeDegreeRankAdaptedBounds
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def quotientLie (I : LieIdeal ℚ L) {t : ℕ} (ht : t ≤ s)
    (hI : F.layer s (t + 1) ≤ I.toSubmodule) : DegreeRankLieFiltration (L ⧸ I) s t where
  rank_le_degree := ht
  layer d i := (F.layer d i).map (lieQuotientMap I).toLinearMap
  lex_antitone := fun h => Submodule.map_mono (F.lex_antitone h)
  one_eq_top := by
    rw [F.one_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (lieQuotientMap_surjective I)
  rank_zero_eq_one := fun d => congrArg (Submodule.map (lieQuotientMap I).toLinearMap)
    (F.rank_zero_eq_one d)
  overshoot := fun d i h => congrArg (Submodule.map (lieQuotientMap I).toLinearMap)
    (F.overshoot d i h)
  lie_mem := by
    rintro d e i j x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨⁅a, b⁆, F.lie_mem ha hb, (lieQuotientMap I).map_lie a b⟩
  terminal := by
    apply bot_unique
    rintro x ⟨a, ha, rfl⟩
    exact (lieQuotientMap_eq_zero I a).mpr (hI ha)

theorem quotientLie_mem (I : LieIdeal ℚ L) {t : ℕ} (ht : t ≤ s)
    (hI : F.layer s (t + 1) ≤ I.toSubmodule) {d i : ℕ} {x : L}
    (hx : x ∈ F.layer d i) :
    lieQuotientMap I x ∈ (F.quotientLie I ht hI).layer d i := ⟨x, hx, rfl⟩

def quotientRank (t : ℕ) (ht : t ≤ s) :
    DegreeRankLieFiltration (L ⧸ F.layerIdeal s (t + 1)) s t :=
  F.quotientLie (F.layerIdeal s (t + 1)) ht le_rfl

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

def FreeDegreeRankLieAlgebra (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x) :=
  FreeWeightedNilpotentLieAlgebra X s w ⧸
    (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1)

namespace FreeDegreeRankLieAlgebra

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)

noncomputable instance instLieRing : LieRing (FreeDegreeRankLieAlgebra X s r w hw) :=
  inferInstanceAs (LieRing (FreeWeightedNilpotentLieAlgebra X s w ⧸
    (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1)))

noncomputable instance instLieAlgebra : LieAlgebra ℚ (FreeDegreeRankLieAlgebra X s r w hw) :=
  inferInstanceAs (LieAlgebra ℚ (FreeWeightedNilpotentLieAlgebra X s w ⧸
    (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1)))

noncomputable def mk : FreeWeightedNilpotentLieAlgebra X s w →ₗ⁅ℚ⁆ FreeDegreeRankLieAlgebra X s r w hw :=
  lieQuotientMap ((FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1))

theorem mk_surjective : Function.Surjective (mk X s r w hw) := lieQuotientMap_surjective _

noncomputable def projection : FreeNilpotentLieAlgebra X s →ₗ⁅ℚ⁆ FreeDegreeRankLieAlgebra X s r w hw :=
  (mk X s r w hw).comp (FreeWeightedNilpotentLieAlgebra.mk X s w)

theorem projection_surjective : Function.Surjective (projection X s r w hw) :=
  (mk_surjective X s r w hw).comp (FreeWeightedNilpotentLieAlgebra.mk_surjective X s w)

noncomputable def of (x : X) : FreeDegreeRankLieAlgebra X s r w hw :=
  mk X s r w hw (FreeWeightedNilpotentLieAlgebra.of X s w x)

noncomputable def filtration (hr : r ≤ s) : DegreeRankLieFiltration (FreeDegreeRankLieAlgebra X s r w hw) s r :=
  (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.quotientRank r hr

theorem of_mem_layer (hr : r ≤ s) (x : X) :
    of X s r w hw x ∈ (filtration X s r w hw hr).layer (w x) 1 := by
  refine ⟨FreeWeightedNilpotentLieAlgebra.of X s w x, ?_, rfl⟩
  change FreeWeightedNilpotentLieAlgebra.of X s w x ∈
    (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).rankLayer (w x) 1
  rw [NilpotentLieFiltration.rankLayer_one]
  exact FreeWeightedNilpotentLieAlgebra.of_mem_layer X s w hw x

instance finite [Fintype X] : Module.Finite ℚ (FreeDegreeRankLieAlgebra X s r w hw) :=
  Module.Finite.of_surjective (mk X s r w hw).toLinearMap (mk_surjective X s r w hw)

end FreeDegreeRankLieAlgebra

end Erdos3

end

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (G : DegreeRankLieFiltration L s r) (w : X → ℕ) (hw : ∀ x, 0 < w x)
  (f : X → L) (hf : ∀ x, f x ∈ G.layer (w x) 0)

theorem FreeWeightedNilpotentLieAlgebra.lift_mem_degreeRank {d i : ℕ}
    {x : FreeWeightedNilpotentLieAlgebra X s w}
    (hx : x ∈ (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).rankLayer d i) :
    FreeWeightedNilpotentLieAlgebra.lift G.associatedDegree w f hf x ∈ G.layer d i := by
  apply NilpotentLieFiltration.map_rankLayer
    (FreeWeightedNilpotentLieAlgebra.filtration X s w hw) G
    (FreeWeightedNilpotentLieAlgebra.lift G.associatedDegree w f hf) ?_ hx
  intro d x hx
  exact FreeWeightedNilpotentLieAlgebra.lift_mem_layer G.associatedDegree w f hf hw hx

namespace FreeDegreeRankLieAlgebra

noncomputable def lift : FreeDegreeRankLieAlgebra X s r w hw →ₗ⁅ℚ⁆ L :=
  lieQuotientDescend
    ((FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1))
    (FreeWeightedNilpotentLieAlgebra.lift G.associatedDegree w f hf)
    (fun x hx => by
      have h := FreeWeightedNilpotentLieAlgebra.lift_mem_degreeRank G w hw f hf hx
      simpa only [G.terminal, Submodule.mem_bot] using h)

theorem lift_projection (x : FreeNilpotentLieAlgebra X s) :
    lift G w hw f hf (projection X s r w hw x) =
      FreeNilpotentLieAlgebra.lift f G.associatedDegree.lowerCentralSeries_eq_bot x := rfl

@[simp] theorem lift_of (x : X) : lift G w hw f hf (of X s r w hw x) = f x :=
  FreeWeightedNilpotentLieAlgebra.lift_of G.associatedDegree w f hf x

theorem lift_mem_layer (hr : r ≤ s) {d i : ℕ} {x : FreeDegreeRankLieAlgebra X s r w hw}
    (hx : x ∈ (filtration X s r w hw hr).layer d i) : lift G w hw f hf x ∈ G.layer d i := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact FreeWeightedNilpotentLieAlgebra.lift_mem_degreeRank G w hw f hf ha

theorem hom_ext {φ ψ : FreeDegreeRankLieAlgebra X s r w hw →ₗ⁅ℚ⁆ L}
    (h : ∀ x, φ (of X s r w hw x) = ψ (of X s r w hw x)) : φ = ψ := by
  have heq : φ.comp (mk X s r w hw) = ψ.comp (mk X s r w hw) :=
    FreeWeightedNilpotentLieAlgebra.hom_ext w h
  apply LieHom.ext
  intro x
  obtain ⟨a, rfl⟩ := mk_surjective X s r w hw x
  exact LieHom.congr_fun heq a

end FreeDegreeRankLieAlgebra

end Erdos3

end

section

namespace Erdos3

namespace FreeWeightedNilpotentLieAlgebra

variable (X : Type*) [Fintype X] (s : ℕ) (w : X → ℕ)

noncomputable def canonicalRankGenerators (d k : ℕ) : Finset (FreeWeightedNilpotentLieAlgebra X s w) := by
  classical
  exact layerGenerators X s w (d + 1) ∪
    finiteWeightedLieValues (rankAlphabetVector X s w) (rankAlphabetWeight X s w) d k

theorem canonicalRankGenerators_span (hw : ∀ x, 0 < w x) (d k : ℕ) :
    Submodule.span ℚ (canonicalRankGenerators X s w d k : Set _) =
      (filtration X s w hw).rankLayer d k := by
  classical
  rw [(filtration X s w hw).rankLayer_eq_weighted_tree_span
    (rankAlphabetVector X s w) (rankAlphabetWeight X s w) (rankAlphabetWeight_pos X s w)
    (rankAlphabetVector_mem X s w hw) (rankAlphabet_spans_layer X s w hw)]
  simp only [canonicalRankGenerators, Finset.coe_union, Submodule.span_union]
  rw [← layer_eq_span X s w hw (d + 1),
    weightedLieTreeSpan_eq_finite_span _ _ (rankAlphabetWeight_pos X s w)]

end FreeWeightedNilpotentLieAlgebra

namespace FreeDegreeRankLieAlgebra

open Module

variable (X : Type*) [Fintype X] (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)

noncomputable def layerGenerators (d k : ℕ) : Finset (FreeDegreeRankLieAlgebra X s r w hw) := by
  classical
  exact (FreeWeightedNilpotentLieAlgebra.canonicalRankGenerators X s w d k).image (mk X s r w hw)

theorem layer_eq_span (hr : r ≤ s) (d k : ℕ) :
    (filtration X s r w hw hr).layer d k = Submodule.span ℚ (layerGenerators X s r w hw d k : Set _) := by
  classical
  change ((FreeWeightedNilpotentLieAlgebra.filtration X s w hw).rankLayer d k).map
    (mk X s r w hw).toLinearMap = _
  rw [← FreeWeightedNilpotentLieAlgebra.canonicalRankGenerators_span X s w hw d k, Submodule.map_span]
  simp only [layerGenerators, Finset.coe_image]
  rfl

noncomputable def layerFamily (hr : r ≤ s) (d k : ℕ)
    (x : layerGenerators X s r w hw d k) : (filtration X s r w hw hr).layer d k :=
  ⟨x.val, by rw [layer_eq_span]; exact Submodule.subset_span x.property⟩

theorem layerFamily_span (hr : r ≤ s) (d k : ℕ) :
    Submodule.span ℚ (Set.range (layerFamily X s r w hw hr d k)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff _ _).mpr
  have hrange : Set.range (Subtype.val : layerGenerators X s r w hw d k →
      FreeDegreeRankLieAlgebra X s r w hw) = (layerGenerators X s r w hw d k : Set _) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [hrange]
  exact (layer_eq_span X s r w hw hr d k).symm

theorem layerGenerators_logHeight {ι : Type*} [Fintype ι]
    (b : Basis ι ℚ (FreeDegreeRankLieAlgebra X s r w hw)) {p : ℝ}
    (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p)
    (hgen : ∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
      rationalLogHeight (b.repr (projection X s r w hw x) i) ≤ p)
    (d k : ℕ) (hd : d ≤ s) (x : FreeDegreeRankLieAlgebra X s r w hw)
    (hx : x ∈ layerGenerators X s r w hw d k) (j : ι) :
    rationalLogHeight (b.repr x j) ≤ (p + 3) ^ (6 * s + 2) := by
  classical
  let H := ⌈Real.exp p⌉₊
  have hv (a : FreeWeightedNilpotentLieAlgebra.RankAlphabet X s w) (i : ι) :
      RationalHeightLE (b.repr (mk X s r w hw (FreeWeightedNilpotentLieAlgebra.rankAlphabetVector X s w a)) i) H := by
    obtain ⟨z, hz, hza⟩ := Finset.mem_image.mp a.2.property
    change RationalHeightLE (b.repr (mk X s r w hw a.2.val) i) H
    rw [← hza]
    exact rationalHeightLE_ceil_exp
      (hgen z (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w _ hz) i)
  have hraw : RationalHeightLE (b.repr x j) (lieTreeHeight (Fintype.card ι) H s) := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact (rationalHeightLE_ceil_exp
        (hgen z (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w _ hz) j)).mono
          (lieTreeHeight_ge_input _ _ _)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      rw [map_lieTreeEval]
      exact (finiteLieTrees_coordinate_height b
        (fun a => mk X s r w hw (FreeWeightedNilpotentLieAlgebra.rankAlphabetVector X s w a))
        (fun i j k => rationalHeightLE_ceil_exp (hc i j k)) hv d a (Finset.mem_filter.mp ha).1 j).mono
          (lieTreeHeight_mono _ _ hd)
  apply rationalLogHeight_le_of_height hraw
  simpa only [show p + 1 + 2 = p + 3 by ring] using
    lieTreeHeight_le_exp (Fintype.card ι) H s
      (hp.trans (le_add_of_nonneg_right zero_le_one))
      (hn.trans (le_add_of_nonneg_right zero_le_one)) (ceil_exp_le_exp_add_one hp)

end FreeDegreeRankLieAlgebra

end Erdos3

end

section

namespace Erdos3.FreeDegreeRankLieAlgebra

open Module
open scoped Matrix

variable {X ι κ L : Type*} [Fintype X] [Fintype ι] [Fintype κ] [DecidableEq κ]
  [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}

theorem lift_basis_matrix_logHeight
    (F : DegreeRankLieFiltration L s r) (w : X → ℕ) (hw : ∀ x, 0 < w x) (f : X → L)
    (hf : ∀ x, f x ∈ F.layer (w x) 0)
    (e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s))
    (he : ∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s)
    (b : Basis κ ℚ (FreeDegreeRankLieAlgebra X s r w hw)) (t : Basis ι ℚ L)
    (S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) κ ℚ)
    (hS : LinearMap.toMatrix e b (projection X s r w hw).toLinearMap * S = 1)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ p)
    (ht : (Fintype.card ι : ℝ) ≤ p)
    (hSH : ∀ i j, rationalLogHeight (S i j) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants t i j k) ≤ p)
    (hg : ∀ x i, rationalLogHeight (t.repr (f x) i) ≤ p) (i : ι) (j : κ) :
    rationalLogHeight (LinearMap.toMatrix b t (lift F w hw f hf).toLinearMap i j) ≤
      ((p + 3) ^ (6 * s + 2) + p + 2) ^ 4 := by
  classical
  let R := (p + 3) ^ (6 * s + 2) + p
  have hpR : p ≤ R := le_add_of_nonneg_left (by positivity)
  have hpowR : (p + 3) ^ (6 * s + 2) ≤ R := le_add_of_nonneg_right hp
  let σ := Matrix.toLin b e S
  have hσ : projection X s r w hw (σ (b j)) = b j := basisMatrix_section e b (projection X s r w hw).toLinearMap S hS (b j)
  have hcoord (k) : e.repr (σ (b j)) k = S k j := by
    simpa only [σ, LinearMap.toMatrix_toLin] using
      (LinearMap.toMatrix_apply b e (Matrix.toLin b e S) k j).symm
  rw [LinearMap.toMatrix_apply]
  have heval : lift F w hw f hf (b j) =
      FreeNilpotentLieAlgebra.lift f F.associatedDegree.lowerCentralSeries_eq_bot (σ (b j)) := by
    calc
      _ = lift F w hw f hf (projection X s r w hw (σ (b j))) := congrArg (lift F w hw f hf) hσ.symm
      _ = _ := lift_projection F w hw f hf (σ (b j))
  change rationalLogHeight (t.repr (lift F w hw f hf (b j)) i) ≤ (R + 2) ^ 4
  rw [heval]
  apply linearMap_coordinate_logHeight e t
    (FreeNilpotentLieAlgebra.lift f F.associatedDegree.lowerCentralSeries_eq_bot).toLinearMap (hp.trans hpR)
    (by simpa only [Fintype.card_fin] using hn.trans hpR) ?_ (σ (b j)) ?_ i
  · intro u v
    have h := FreeNilpotentLieAlgebra.lift_basis_matrix_logHeight t f
      F.associatedDegree.lowerCentralSeries_eq_bot e he hp ht hc hg v u
    apply le_trans _ hpowR
    simpa only [LinearMap.toMatrix_apply] using h
  · intro k
    rw [hcoord]
    exact (hSH k j).trans hpR

end Erdos3.FreeDegreeRankLieAlgebra

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_free_degree_rank_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (r : ℕ) (w : X → ℕ)
      (hw : ∀ x, 0 < w x) (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw) : ℝ) ≤ (p + C) ^ C ∧
      ∃ b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
          (FreeDegreeRankLieAlgebra X s r w hw),
        (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C) ∧
        (∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
          rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) i) ≤ (p + C) ^ C) ∧
        ∃ e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
          (∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
          (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
          ∃ S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
              (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ,
            LinearMap.toMatrix e b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap * S = 1 ∧
            ∀ i j, rationalLogHeight (S i j) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hmodel⟩ := exists_bounded_free_weighted_model s
  let B₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let V₀ : Polynomial ℕ := (Polynomial.C (s + 1) * (Polynomial.X + 2) ^ (3 ^ s) + 2) ^ (3 ^ s)
  let T₀ := B₀ + V₀ + (B₀ + 3) ^ (6 * s + 2) + 2
  let W₀ := T₀ + (T₀ + 3) ^ 51
  let R₀ := (W₀ + 2) ^ 4 + W₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R₀ + (R₀ + 3) ^ 5)
  refine ⟨C, hC, ?_⟩
  intro X _ r w hw p hp hX
  classical
  let B := (p + a) ^ a
  let V := (((s + 1 : ℕ) : ℝ) * (p + 2) ^ (3 ^ s) + 2) ^ (3 ^ s)
  let E := (B + 3) ^ (6 * s + 2)
  let T := B + V + E + 2
  let W := T + (T + 3) ^ 51
  let R := (W + 2) ^ 4 + W
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hBT : B ≤ T := (le_add_of_nonneg_right hV).trans
    ((le_add_of_nonneg_right hE).trans (le_add_of_nonneg_right (by norm_num)))
  have hVT : V ≤ T := (le_add_of_nonneg_left hB).trans
    ((le_add_of_nonneg_right hE).trans (le_add_of_nonneg_right (by norm_num)))
  have hET : E ≤ T := (le_add_of_nonneg_left (add_nonneg hB hV)).trans
    (le_add_of_nonneg_right (by norm_num))
  have hT : 0 ≤ T := hB.trans hBT
  have hTW : T ≤ W := le_add_of_nonneg_right (by positivity)
  have hW : 0 ≤ W := hT.trans hTW
  have hWR : W ≤ R := le_add_of_nonneg_left (by positivity)
  have hR : 0 ≤ R := hW.trans hWR
  have hprojR : (W + 2) ^ 4 ≤ R := le_add_of_nonneg_right hW
  have hsmall (k : ℕ) (hk : k ≤ 51) : (T + 1 + 2) ^ k ≤ W := by
    rw [show T + 1 + 2 = T + 3 from
      (add_assoc T 1 2).trans (congrArg (fun z : ℝ => T + z) (by norm_num))]
    exact (pow_le_pow_right₀ (by linarith only [hT]) hk).trans (le_add_of_nonneg_left hT)
  have hsum : R + (R + 3) ^ 5 ≤ (p + C) ^ C := by
    simpa [B₀, V₀, T₀, W₀, R₀, B, V, E, T, W, R, Polynomial.eval₂_pow] using hbudget p hp
  have hRC : R ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (R + 3) ^ 5)).trans hsum
  have hSC : (R + 3) ^ 5 ≤ (p + C) ^ C := (le_add_of_nonneg_left hR).trans hsum
  have hBC : B ≤ (p + C) ^ C := hBT.trans (hTW.trans (hWR.trans hRC))
  obtain ⟨hdim, e, _, _, _, _, _, hc, hgen, e₀, he₀, hdim₀, _⟩ := hmodel X w hw p hp hX
  let A := FreeWeightedNilpotentLieAlgebra.topRankGenerators X s w (r + 1)
  let I := (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1)
  let v : A → FreeWeightedNilpotentLieAlgebra X s w := Subtype.val
  have hrange : Set.range v = (A : Set (FreeWeightedNilpotentLieAlgebra X s w)) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule := by
    rw [hrange]
    exact FreeWeightedNilpotentLieAlgebra.topRankGenerators_span X s w hw (r + 1)
  have hcount : (Fintype.card A : ℝ) ≤ V := by
    have hcard := FreeWeightedNilpotentLieAlgebra.topRankGenerators_card_le X s w (r + 1)
    have hbase := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Fintype.card X + 2)
      (add_le_add hX (le_refl (2 : ℝ))) (3 ^ s)
    calc
      _ ≤ (((s + 1 : ℕ) : ℝ) * ((Fintype.card X : ℝ) + 2) ^ (3 ^ s) + 2) ^ (3 ^ s) := by
        simpa only [A, Fintype.card_coe, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          using (Nat.cast_le.mpr hcard : ((FreeWeightedNilpotentLieAlgebra.topRankGenerators X s w (r + 1)).card : ℝ) ≤ _)
      _ ≤ V := pow_le_pow_left₀ (by positivity)
        (add_le_add (mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg (s + 1))) (le_refl (2 : ℝ))) _
  have hv (i) (j : A) : rationalLogHeight (e.repr (v j) i) ≤ T :=
    (FreeWeightedNilpotentLieAlgebra.topRankGenerators_logHeight X s w e hB
      (by simpa only [Fintype.card_fin] using hdim) hc hgen (r + 1) j.val j.property i).trans hET
  obtain ⟨d, hd, b, D, _, hmatrix, _, hD, _, hbracket⟩ :=
    exists_lie_quotient_basis_exp_height e I v hspan (one_le_ceil_exp T)
      (fun i j => rationalHeightLE_ceil_exp (hv i j))
      (fun i j k => rationalHeightLE_ceil_exp ((hc i j k).trans hBT))
      (hT.trans (le_add_of_nonneg_right zero_le_one))
      (by simpa only [Fintype.card_fin] using hdim.trans (hBT.trans (le_add_of_nonneg_right zero_le_one)))
      (hcount.trans (hVT.trans (le_add_of_nonneg_right zero_le_one)))
      (ceil_exp_le_exp_add_one hT)
  change Basis (Fin d) ℚ (FreeDegreeRankLieAlgebra X s r w hw) at b
  change LinearMap.toMatrix e b (FreeDegreeRankLieAlgebra.mk X s r w hw).toLinearMap = D at hmatrix
  have hfin : finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw) = d := by
    simpa only [Fintype.card_fin] using finrank_eq_card_basis b
  subst d
  have hdimq : (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw) : ℝ) ≤ B :=
    (Nat.cast_le.mpr (by simpa only [Fintype.card_fin] using hd)).trans hdim
  have hD' (i j) : rationalLogHeight (D i j) ≤ W :=
    ((rationalLogHeight_le_iff _ _).mpr (hD i j)).trans (hsmall 7 (by omega))
  have htree (x : FreeNilpotentLieAlgebra X s)
      (hx : x ∈ FreeNilpotentLieAlgebra.treeGenerators X s) (j) :
      rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) j) ≤ R := by
    apply le_trans _ hprojR
    apply linearMap_coordinate_logHeight e b (FreeDegreeRankLieAlgebra.mk X s r w hw).toLinearMap hW
      (by simpa only [Fintype.card_fin] using hdim.trans (hBT.trans hTW)) ?_
      (FreeWeightedNilpotentLieAlgebra.mk X s w x) (fun i => (hgen x hx i).trans (hBT.trans hTW)) j
    intro i j
    have h := hD' j i
    rw [← hmatrix, LinearMap.toMatrix_apply] at h
    exact h
  let M := LinearMap.toMatrix e₀ b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap
  have hM (i j) : rationalLogHeight (M i j) ≤ R := by
    dsimp only [M]
    rw [LinearMap.toMatrix_apply]
    exact htree (e₀ j) (he₀ j) i
  obtain ⟨S, hMS, hS⟩ := exists_rational_section_exp_height M
    (basisMatrix_surjective e₀ b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap
      (FreeDegreeRankLieAlgebra.projection_surjective X s r w hw))
    (one_le_ceil_exp R) (fun i j => rationalHeightLE_ceil_exp (hM i j))
    (hR.trans (le_add_of_nonneg_right zero_le_one))
    (by simpa only [Fintype.card_fin] using (hdimq.trans
      (hBT.trans (hTW.trans (hWR.trans (le_add_of_nonneg_right zero_le_one))))))
    (ceil_exp_le_exp_add_one hR)
  refine ⟨hdimq.trans hBC, b, ?_, fun x hx i => (htree x hx i).trans hRC,
    e₀, he₀, hdim₀.trans hBC, S, hMS, ?_⟩
  · intro i j k
    exact ((rationalLogHeight_le_iff _ _).mpr (hbracket i j k)).trans
      ((hsmall 51 (by omega)).trans (hWR.trans hRC))
  · intro i j
    apply le_trans ((rationalLogHeight_le_iff _ _).mpr (hS i j))
    simpa only [show R + 1 + 2 = R + 3 from
      (add_assoc R 1 2).trans (congrArg (fun z : ℝ => R + z) (by norm_num))] using hSC

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_adapted_free_degree_rank_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (r : ℕ) (hr : r ≤ s)
      (w : X → ℕ) (hw : ∀ x, 0 < w x) (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw) : ℝ) ≤ (p + C) ^ C ∧
      ∃ b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
          (FreeDegreeRankLieAlgebra X s r w hw),
        IsCentralLieBasis b ∧
        (∀ i j, ∃ c ≤ finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw),
          (FreeDegreeRankLieAlgebra.filtration X s r w hw hr).layer i j = basisTail b c) ∧
        (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C) ∧
        (∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
          rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) i) ≤ (p + C) ^ C) ∧
        ∃ e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
          (∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
          (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
          ∃ S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
              (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ,
            LinearMap.toMatrix e b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap * S = 1 ∧
            ∀ i j, rationalLogHeight (S i j) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hmodel⟩ := exists_bounded_free_degree_rank_model s
  let B₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let P₀ := (B₀ + 3) ^ (6 * s + 2)
  let Q₀ := P₀ + (P₀ + 3) ^ 5
  let R₀ := (Q₀ + 2) ^ 4 + (P₀ + 3) ^ 11 + B₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R₀ + (R₀ + 3) ^ 5)
  refine ⟨C, hC, ?_⟩
  intro X _ r hr w hw p hp hX
  classical
  let B := (p + a) ^ a
  let P := (B + 3) ^ (6 * s + 2)
  let Q := P + (P + 3) ^ 5
  let R := (Q + 2) ^ 4 + (P + 3) ^ 11 + B
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hBP : B ≤ P :=
    (le_power_budget hB (by omega : 1 ≤ 6 * s + 2)).trans
      (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl B) (by norm_num : (2 : ℝ) ≤ 3)) _)
  have hPQ : P ≤ Q := le_add_of_nonneg_right (by positivity)
  have hIQ : (P + 3) ^ 5 ≤ Q := le_add_of_nonneg_left hP
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hBR : B ≤ R := le_add_of_nonneg_left (by positivity)
  have hR : 0 ≤ R := hB.trans hBR
  have hprojectionR : (Q + 2) ^ 4 ≤ R :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (P + 3) ^ 11)).trans (le_add_of_nonneg_right hB)
  have hstructureR : (P + 3) ^ 11 ≤ R :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (Q + 2) ^ 4)).trans (le_add_of_nonneg_right hB)
  have hsum : R + (R + 3) ^ 5 ≤ (p + C) ^ C := by
    simpa [B₀, P₀, Q₀, R₀, B, P, Q, R, Polynomial.eval₂_pow] using hbudget p hp
  have hRC : R ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (R + 3) ^ 5)).trans hsum
  have hSC : (R + 3) ^ 5 ≤ (p + C) ^ C := (le_add_of_nonneg_left hR).trans hsum
  obtain ⟨hdim, q, hc, hgen, e, he, hdim₀, _⟩ := hmodel X r w hw p hp hX
  let F := FreeDegreeRankLieAlgebra.filtration X s r w hw hr
  let v (i j : Fin (s + 1)) := FreeDegreeRankLieAlgebra.layerFamily X s r w hw hr i.val j.val
  have hv (i j : Fin (s + 1)) (x : FreeDegreeRankLieAlgebra.layerGenerators X s r w hw i.val j.val) (k) :
      rationalLogHeight (q.repr (v i j x : FreeDegreeRankLieAlgebra X s r w hw) k) ≤ P := by
    exact FreeDegreeRankLieAlgebra.layerGenerators_logHeight X s r w hw q hB
      (by simpa only [Fintype.card_fin] using hdim) hc hgen i.val j.val
      (Nat.le_of_lt_succ i.isLt) x.val x.property k
  obtain ⟨b, hcentral, hlayer, _, hinverse, hstructure⟩ := F.exists_rank_adapted_basis_logHeight q v
    (fun i j => FreeDegreeRankLieAlgebra.layerFamily_span X s r w hw hr i.val j.val) hP
    (by simpa only [Fintype.card_fin] using hdim.trans hBP) hv
    (fun i j k => (hc i j k).trans hBP)
  have htree (x : FreeNilpotentLieAlgebra X s)
      (hx : x ∈ FreeNilpotentLieAlgebra.treeGenerators X s) (j) :
      rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) j) ≤ R := by
    apply le_trans _ hprojectionR
    exact linearMap_coordinate_logHeight q b LinearMap.id hQ
      (by simpa only [Fintype.card_fin] using hdim.trans (hBP.trans hPQ))
      (fun i k => (hinverse i k).trans hIQ) (FreeDegreeRankLieAlgebra.projection X s r w hw x)
      (fun i => (hgen x hx i).trans (hBP.trans hPQ)) j
  let A := LinearMap.toMatrix e b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap
  have hA (i j) : rationalLogHeight (A i j) ≤ R := by
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact htree (e j) (he j) i
  obtain ⟨S, hAS, hS⟩ := exists_rational_section_exp_height A
    (basisMatrix_surjective e b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap
      (FreeDegreeRankLieAlgebra.projection_surjective X s r w hw))
    (one_le_ceil_exp R) (fun i j => rationalHeightLE_ceil_exp (hA i j))
    (hR.trans (le_add_of_nonneg_right zero_le_one))
    (by simpa only [Fintype.card_fin] using
      (hdim.trans (hBR.trans (le_add_of_nonneg_right zero_le_one))))
    (ceil_exp_le_exp_add_one hR)
  refine ⟨hdim.trans (hBR.trans hRC), b, hcentral, hlayer,
    fun i j k => (hstructure i j k).trans (hstructureR.trans hRC),
    fun x hx i => (htree x hx i).trans hRC, e, he, hdim₀.trans (hBR.trans hRC), S, hAS, ?_⟩
  intro i j
  apply le_trans ((rationalLogHeight_le_iff _ _).mpr (hS i j))
  simpa only [show R + 1 + 2 = R + 3 from
    (add_assoc R 1 2).trans (congrArg (fun z : ℝ => R + z) (by norm_num))] using hSC

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedParameterPatchRankPadding
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def localTentKernel (d q : ℕ) (hq : 8 ≤ q) : PatchKernel d where
  value x := max 0 (1 - (q : ℝ) / 2 * dist x 0)
  nonneg x := le_max_left _ _
  le_one x := max_le zero_le_one (by
    have h : 0 ≤ (q : ℝ) / 2 * dist x 0 := by positivity
    linarith)
  support x hx i := by
    have hqR : (8 : ℝ) ≤ q := by exact_mod_cast hq
    have hsmall : (q : ℝ) / 2 * dist x 0 < 1 := by
      by_contra h
      exact hx (max_eq_left (by linarith))
    have hcoord : |x i| ≤ dist x 0 := by
      simpa only [Real.dist_eq, Pi.zero_apply, sub_zero] using dist_le_pi_dist x 0 i
    have hdist : 0 ≤ dist x 0 := dist_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hqR hdist]
  lip := (q : ℝ≥0) / 2
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |max 0 (1 - (q : ℝ) / 2 * dist x 0) - max 0 (1 - (q : ℝ) / 2 * dist y 0)| ≤
      (q : ℝ) / 2 * dist x y
    calc
      _ ≤ |(1 - (q : ℝ) / 2 * dist x 0) - (1 - (q : ℝ) / 2 * dist y 0)| := by
        rw [max_comm 0 _, max_comm 0 _]
        exact abs_max_sub_max_le_abs _ _ _
      _ = (q : ℝ) / 2 * |dist x 0 - dist y 0| := by
        rw [show (1 - (q : ℝ) / 2 * dist x 0) - (1 - (q : ℝ) / 2 * dist y 0) =
          -((q : ℝ) / 2) * (dist x 0 - dist y 0) by ring,
          abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (q : ℝ) / 2)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (abs_dist_sub_le x y 0) (by positivity)

theorem localTentKernel_ge_half {d q : ℕ} (hq : 8 ≤ q) (x : Fin d → ℝ)
    (hx : dist x 0 ≤ 1 / (q : ℝ)) : 1 / 2 ≤ (localTentKernel d q hq).value x := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmul : (q : ℝ) * dist x 0 ≤ 1 := by
    simpa only [mul_comm] using (le_div_iff₀ hqR).mp hx
  exact (by linarith : (1 : ℝ) / 2 ≤ 1 - (q : ℝ) / 2 * dist x 0).trans (le_max_right _ _)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators NNReal

namespace WeightedParameterSlots

variable {σ : Type*} {p : σ → ℕ} {d n D E : ℕ}

theorem placementSubstitution_degree {w : Fin d → ℕ} {v : Fin n → ℕ}
    (f : Fin d → Fin n) (hweight : ∀ i, v (f i) = w i) (k : Fin n) (i : Fin d)
    (a : σ ⊕ Fin i.val) :
    PolynomialSlots.placementSubstitution f k i a ∈
      weightedSupportLE (weightedPatchVariableWeight p v k) (weightedPatchVariableWeight p w i a) := by
  cases a with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
    simp only [PolynomialSlots.placementSubstitution, Sum.elim_inr]
    split_ifs with h
    · have hX := weightedSupportLE_X (R := ℝ) (weightedPatchVariableWeight (σ := σ) p v k)
        (Sum.inr (⟨(f (earlierSlot i j)).val, h⟩ : Fin k.val))
      change _ ∈ weightedSupportLE _ (v (f (earlierSlot i j))) at hX
      rw [hweight] at hX
      exact hX
    · exact (weightedSupportLE _ _).zero_mem

noncomputable def placeCenter {w : Fin d → ℕ} (A : WeightedParameterSlots σ p d w)
    (f : Fin d → Fin n) (k : Fin n) (i : Fin d) :
    MvPolynomial (σ ⊕ Fin k.val) ℝ := aeval (PolynomialSlots.placementSubstitution f k i) (A.center i)

theorem placeCenter_degree {w : Fin d → ℕ} {v : Fin n → ℕ}
    (A : WeightedParameterSlots σ p d w) (f : Fin d → Fin n)
    (hweight : ∀ i, v (f i) = w i) (k : Fin n) (i : Fin d) :
    A.placeCenter f k i ∈ weightedSupportLE (weightedPatchVariableWeight p v k) (w i) :=
  weightedSupportLE_aeval _ _ _ (placementSubstitution_degree f hweight k i) (A.degree i)

theorem placeCenter_eval {w : Fin d → ℕ} (A : WeightedParameterSlots σ p d w)
    (f : Fin d → Fin n) (hf : StrictMono f) (i : Fin d) (t : σ → ℝ) (x : Fin n → ℝ) :
    aeval (Sum.elim t (fun j => x (earlierSlot (f i) j))) (A.placeCenter f (f i) i) =
      (A.slots t).center (fun j => x (f j)) i := by
  simp only [placeCenter, MvPolynomial.comp_aeval_apply, slots]
  apply congrArg (fun g : σ ⊕ Fin i.val → ℝ => aeval g (A.center i))
  funext a
  cases a with
  | inl a => simp [PolynomialSlots.placementSubstitution]
  | inr j =>
    have h : (f (earlierSlot i j)).val < (f i).val :=
      hf (show earlierSlot i j < i from j.isLt)
    simp only [PolynomialSlots.placementSubstitution, Sum.elim_inr, dif_pos h, aeval_X]
    rfl

noncomputable def interleave {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : WeightedParameterSlots σ p D w) (B : WeightedParameterSlots σ p E v) (I : SlotInterleaving D E) :
    WeightedParameterSlots σ p (D + E) (I.fill w v) where
  center k := Fin.addCases (A.placeCenter I.left k) (B.placeCenter I.right k) (I.perm k)
  degree k := by
    change Fin.addCases (A.placeCenter I.left k) (B.placeCenter I.right k) (I.perm k) ∈
      weightedSupportLE (weightedPatchVariableWeight p (I.fill w v) k) (Fin.append w v (I.perm k))
    generalize I.perm k = z
    refine Fin.addCases (fun i => ?_) (fun i => ?_) z
    · simpa only [Fin.addCases_left, Fin.append_left] using
        A.placeCenter_degree I.left (fun j => I.fill_left w v j) k i
    · simpa only [Fin.addCases_right, Fin.append_right] using
        B.placeCenter_degree I.right (fun j => I.fill_right w v j) k i

@[simp] theorem interleave_center_left {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : WeightedParameterSlots σ p D w) (B : WeightedParameterSlots σ p E v) (I : SlotInterleaving D E)
    (i : Fin D) : (A.interleave B I).center (I.left i) = A.placeCenter I.left (I.left i) i := by
  simp [interleave, SlotInterleaving.left]

@[simp] theorem interleave_center_right {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : WeightedParameterSlots σ p D w) (B : WeightedParameterSlots σ p E v) (I : SlotInterleaving D E)
    (i : Fin E) : (A.interleave B I).center (I.right i) = B.placeCenter I.right (I.right i) i := by
  simp [interleave, SlotInterleaving.right]

theorem interleave_slots {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : WeightedParameterSlots σ p D w) (B : WeightedParameterSlots σ p E v) (I : SlotInterleaving D E)
    (t : σ → ℝ) : (A.interleave B I).slots t = (A.slots t).interleave (B.slots t) I := by
  apply TriangularSlots.ext
  intro x k
  apply I.cases (p := fun k => ((A.interleave B I).slots t).center x k =
    ((A.slots t).interleave (B.slots t) I).center x k) _ _ k
  · intro i
    change aeval _ ((A.interleave B I).center (I.left i)) = _
    rw [interleave_center_left]
    simpa only [TriangularSlots.interleave, SlotInterleaving.fill_left] using
      A.placeCenter_eval I.left I.left_strictMono i t x
  · intro i
    change aeval _ ((A.interleave B I).center (I.right i)) = _
    rw [interleave_center_right]
    simpa only [TriangularSlots.interleave, SlotInterleaving.fill_right] using
      B.placeCenter_eval I.right I.right_strictMono i t x

end WeightedParameterSlots

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s D E : ℕ}

noncomputable def product (A : WeightedParameterPatch σ p s D) (B : WeightedParameterPatch σ p s E) :
    WeightedParameterPatch σ p s (D + E) :=
  let I := SlotInterleaving.sorted A.weight B.weight A.weight_mono B.weight_mono
  { weight := I.fill A.weight B.weight
    weight_pos := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_pos i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_pos i)
    weight_le := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_le i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_le i)
    weight_mono := SlotInterleaving.sorted_weight_mono _ _ _ _
    form := A.form.interleave B.form I
    kernel := A.kernel.product B.kernel I }

@[simp] theorem product_lip (A : WeightedParameterPatch σ p s D) (B : WeightedParameterPatch σ p s E) :
    (A.product B).kernel.lip = A.kernel.lip + B.kernel.lip := rfl

@[simp] theorem product_value (A : WeightedParameterPatch σ p s D) (B : WeightedParameterPatch σ p s E)
    (t : σ → ℝ) : (A.product B).value t = A.value t * B.value t := by
  let I := SlotInterleaving.sorted A.weight B.weight A.weight_mono B.weight_mono
  change ((A.form.interleave B.form I).slots t).patchValue (A.kernel.product B.kernel I) = _
  rw [WeightedParameterSlots.interleave_slots, TriangularSlots.interleave_patchValue]
  rfl

def castRank {d e : ℕ} (P : WeightedParameterPatch σ p s d) (h : d = e) :
    WeightedParameterPatch σ p s e := h ▸ P

@[simp] theorem castRank_value {d e : ℕ} (P : WeightedParameterPatch σ p s d)
    (h : d = e) (t : σ → ℝ) : (P.castRank h).value t = P.value t := by
  subst e
  rfl

@[simp] theorem castRank_kernel_lip {d e : ℕ} (P : WeightedParameterPatch σ p s d)
    (h : d = e) : (P.castRank h).kernel.lip = P.kernel.lip := by
  subst e
  rfl

noncomputable def unitRank (σ : Type*) (p : σ → ℕ) (s d : ℕ) (hs : 1 ≤ s) :
    WeightedParameterPatch σ p s d where
  weight := fun _ => 1
  weight_pos := fun _ => le_rfl
  weight_le := fun _ => hs
  weight_mono := fun _ _ _ => le_rfl
  form := { center := fun _ => 0, degree := fun _ => Submodule.zero_mem _ }
  kernel := localTentKernel d 8 le_rfl

@[simp] theorem unitRank_value {σ : Type*} {p : σ → ℕ} {s d : ℕ} (hs : 1 ≤ s) (t : σ → ℝ) :
    (unitRank σ p s d hs).value t = 1 := by
  change ((unitRank σ p s d hs).form.slots t).patchValue (localTentKernel d 8 le_rfl) = 1
  have hres : ((unitRank σ p s d hs).form.slots t).residual 0 = 0 := by
    ext i
    simp [unitRank, WeightedParameterSlots.slots, TriangularSlots.residual]
  rw [TriangularSlots.patchValue_eq_at_residual (b := 0)]
  · rw [hres]
    norm_num [localTentKernel]
  · intro i
    rw [hres]
    norm_num

@[simp] theorem unitRank_lip {σ : Type*} {p : σ → ℕ} {s d : ℕ} (hs : 1 ≤ s) :
    (unitRank σ p s d hs).kernel.lip = 4 := by
  norm_num [unitRank, localTentKernel]

noncomputable def padRank {σ : Type*} {p : σ → ℕ} {s d D : ℕ}
    (P : WeightedParameterPatch σ p s d) (hs : 1 ≤ s) (hd : d ≤ D) :
    WeightedParameterPatch σ p s D :=
  (P.product (unitRank σ p s (D-d) hs)).castRank (Nat.add_sub_of_le hd)

@[simp] theorem padRank_value {σ : Type*} {p : σ → ℕ} {s d D : ℕ}
    (P : WeightedParameterPatch σ p s d) (hs : 1 ≤ s) (hd : d ≤ D) (t : σ → ℝ) :
    (P.padRank hs hd).value t = P.value t := by
  simp only [padRank, castRank_value, product_value, unitRank_value, mul_one]

@[simp] theorem padRank_lip {σ : Type*} {p : σ → ℕ} {s d D : ℕ}
    (P : WeightedParameterPatch σ p s d) (hs : 1 ≤ s) (hd : d ≤ D) :
    (P.padRank hs hd).kernel.lip = P.kernel.lip + 4 := by
  simp only [padRank, castRank_kernel_lip, product_lip, unitRank_lip]

noncomputable def padRankFamily {σ H : Type*} {p : σ → ℕ} {s D : ℕ}
    (d : H → ℕ) (P : ∀ h, WeightedParameterPatch σ p s (d h))
    (hs : 1 ≤ s) (hd : ∀ h, d h ≤ D) : H → WeightedParameterPatch σ p s D :=
  fun h => (P h).padRank hs (hd h)

@[simp] theorem padRankFamily_value {σ H : Type*} {p : σ → ℕ} {s D : ℕ}
    (d : H → ℕ) (P : ∀ h, WeightedParameterPatch σ p s (d h))
    (hs : 1 ≤ s) (hd : ∀ h, d h ≤ D) (h : H) (t : σ → ℝ) :
    (padRankFamily d P hs hd h).value t = (P h).value t :=
  padRank_value _ _ _ _

end WeightedParameterPatch
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TorusCellBudget
namespace OAI

section

namespace Erdos3

noncomputable def torusGridCenter {d : ℕ} (q : ℕ) (a : Fin d → Fin q) : Fin d → ℝ :=
  fun i => (a i).val / (q : ℝ)

theorem fractionalPartBin_center_error {q : ℕ} (hq : 0 < q) (x : ℝ) :
    |((fractionalPartBin q hq x).val : ℝ) / q - Int.fract x| ≤ 1 / (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlo : ((fractionalPartBin q hq x).val : ℝ) ≤ (q : ℝ) * Int.fract x :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg q) (Int.fract_nonneg x))
  have hhi : (q : ℝ) * Int.fract x < ((fractionalPartBin q hq x).val : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hle : ((fractionalPartBin q hq x).val : ℝ) / q ≤ Int.fract x :=
    (div_le_iff₀ hqR).mpr (by simpa only [mul_comm] using hlo)
  rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
  apply (le_div_iff₀ hqR).mpr
  rw [sub_mul, div_mul_cancel₀ _ hqR.ne']
  nlinarith

theorem torusGrid_coordinate_cover {d q : ℕ} (hq : 0 < q) (x : Fin d → ℝ) :
    ∃ (a : Fin d → Fin q) (b : Fin d → ℤ),
      ∀ i, |(b i : ℝ) - (x - torusGridCenter q a) i| ≤ 1 / (q : ℝ) := by
  let a := fun i => fractionalPartBin q hq (x i)
  let b := fun i => Int.floor (x i)
  refine ⟨a, b, ?_⟩
  intro i
  have heq : (b i : ℝ) - (x - torusGridCenter q a) i =
      ((fractionalPartBin q hq (x i)).val : ℝ) / q - Int.fract (x i) := by
    simp only [b, a, Pi.sub_apply, torusGridCenter, Int.fract]
    ring
  rw [heq]
  exact fractionalPartBin_center_error hq (x i)

theorem torusGrid_cover {d q : ℕ} (hq : 0 < q) (x : Fin d → ℝ) :
    ∃ (a : Fin d → Fin q) (b : Fin d → ℤ),
      dist (fun i => (b i : ℝ) - (x - torusGridCenter q a) i) 0 ≤ 1 / (q : ℝ) := by
  obtain ⟨a, b, hab⟩ := torusGrid_coordinate_cover hq x
  refine ⟨a, b, (dist_pi_le_iff (by positivity)).mpr ?_⟩
  intro i
  simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using hab i

end Erdos3

end

section

namespace Erdos3

open CircleFourier

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped NNReal

noncomputable def ambientTorusTent {J : Type*} [Fintype J] (q : ℕ) (x : J → UnitAddCircle) : ℝ :=
  max 0 (1 - (q : ℝ) / 4 * ‖x‖)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def centeredTorusTent {J : Type*} [Fintype J] (q : ℕ)
    (c x : J → UnitAddCircle) : ℝ := ambientTorusTent q (x - c)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem localTent_translateSum_ge_half (d q : ℕ) (hq : 8 ≤ q) (x : Fin d → ℝ) :
    1 / 2 ≤ (localTentKernel d q hq).translateSum (torusGridCenter q) x := by
  obtain ⟨a, b, hab⟩ := torusGrid_cover (show 0 < q by omega) x
  exact (localTentKernel_ge_half hq _ hab).trans
    (((localTentKernel d q hq).kernel_le_periodicValue (x - torusGridCenter q a) b).trans
      ((localTentKernel d q hq).periodicValue_le_translateSum (torusGridCenter q) a x))

noncomputable def torusGridKernel (d q : ℕ) (hq : 8 ≤ q) (a : Fin d → Fin q) : PatchKernel d :=
  (localTentKernel d q hq).normalizedTranslate (torusGridCenter q) (1 / 2) (by norm_num)
    (fun x => by simpa using localTent_translateSum_ge_half d q hq x) a

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators NNReal

namespace PolynomialPatch

end PolynomialPatch

variable {σ : Type*} {s d : ℕ}

noncomputable def polynomialTorusCell (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hws : ∀ i, w i ≤ s) (hmono : Monotone w) (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i))
    (q : ℕ) (hq : 8 ≤ q) (a : Fin d → Fin q) : PolynomialPatch σ s d :=
  PolynomialPatch.ofCoordinates w hw hws hmono (fun i => P i - C (torusGridCenter q a i))
    (fun i => (weightedSupportLE _ _).sub_mem (hP i) (weightedSupportLE_C _ _ _))
    (torusGridKernel d q hq a)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

namespace PatchKernel

variable {d : ℕ}

noncomputable def integerLift (Φ : PatchKernel d) (x : Fin d → ℝ) : Fin d → ℤ := by
  classical
  exact if h : ∃ b : Fin d → ℤ, Φ.value (fun j => (b j : ℝ) - x j) ≠ 0 then h.choose else 0

end PatchKernel

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTProgressionVanishing
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def progressionTorusCenter {J : Type*} (k : ℕ) : J × Bool → UnitAddCircle :=
  fun t => if t.2 then ((1 / (4 * (k : ℝ)) : ℝ) : UnitAddCircle) else ((1 / 4 : ℝ) : UnitAddCircle)

noncomputable def progressionTorusCutoff {J : Type*} [Fintype J] (k : ℕ)
    (w : J × Bool → UnitAddCircle) : ℝ :=
  centeredTorusTent (64 * k) (progressionTorusCenter k) w

noncomputable def crtProgressionWeight {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) (k : ℕ)
    (z : ZMod (∏ j, N j) × ZMod (∏ j, N j)) : ℝ :=
  progressionTorusCutoff k (crtConfigurationTorus N hN z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def IntegerVectorAPFree {J : Type*} (A : Set (J → ℤ)) (k : ℕ) : Prop :=
  ∀ a d : J → ℤ, d ≠ 0 → ∃ i : Fin k, a + (i.val : ℤ) • d ∉ A

noncomputable def residueBoxIntegerPoint {J : Type*} (N : J → ℕ)
    (u : (j : J) → ZMod (N j)) : J → ℤ := fun j => (u j).val

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareRationalModel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def squareFinBasis (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i})) :
    Basis (Fin (Fintype.card (ι ⊕ {i // 2 ≤ w i}))) ℚ F.squareLieSubalgebra :=
  (F.adaptedSquareBasis b w h).reindex (Fintype.equivFin _)

noncomputable def squareFinWeight (w : ι → ℕ) :
    Fin (Fintype.card (ι ⊕ {i // 2 ≤ w i})) → ℕ :=
  fun i => squareBasisWeight w ((Fintype.equivFin _).symm i)

theorem squareFinBasis_layers (b : Basis ι ℚ L) (w : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) (j : ℕ) :
    F.squareFiltration.layer j = Submodule.span ℚ
      (F.squareFinBasis b w (hlayers 2) '' {i | j ≤ squareFinWeight w i}) := by
  rw [F.adaptedSquareBasis_layers b w hlayers j]
  exact (basis_reindex_span_weights _ _ _ _).symm

theorem exists_square_rational_model (b : Basis ι ℚ L) (w : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
    (Γ : Subgroup F.Group) {l H : ℕ} (hl : 0 < l) (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : 2 * (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (N : ℕ) (hN : 0 < N)
      (hinner : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (F.squareFinBasis b w (hlayers 2)) (F.squareLattice Γ))
      (houter : bchSubgroupCoordinates (F.squareFinBasis b w (hlayers 2))
        (F.squareLattice Γ) ⊆ denominatorGrid N),
      (F.squareFiltration.ofAdaptedBasis (F.squareFinBasis b w (hlayers 2))
        (squareFinWeight w) (F.squareFinBasis_layers b w hlayers)
        (F.squareLattice Γ) N hN hinner houter).GeometryComplexityLE ((p + 2) ^ 11) := by
  obtain ⟨N, hN, hNp, hinner, houter⟩ :=
    F.exists_adaptedSquareBasis_grid b w (hlayers 2) Γ hl hin hout hp hd hlp
  have hin' := bchSubgroup_inner_grid_reindex _ (Fintype.equivFin _) _ hinner
  have hout' := bchSubgroup_outer_grid_reindex _ (Fintype.equivFin _) _ houter
  refine ⟨N, hN, hin', hout', ?_⟩
  apply F.squareFiltration.ofAdaptedBasis_geometry _ _ _ _ _ _ hin' hout' (by positivity)
  · exact ((Nat.cast_le.mpr (card_squareBasis_index_le w)).trans (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd)).trans
        (le_power_budget hp (by decide : 1 ≤ 11))
  · exact hNp.trans (Real.exp_le_exp.mpr
      (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 9 ≤ 11)))
  · intro i j k
    change rationalLogHeight
      (lieStructureConstants (F.squareFinBasis b w (hlayers 2)) i j k) ≤ (p + 2) ^ 11
    rw [squareFinBasis, lieStructureConstants_reindex]
    exact F.adaptedSquareBasis_structure_bound b w (hlayers 2) hH hc hp hd hHp _ _ _

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateDerivativeBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]

theorem directionalDerivative_single_coordinate (f : L →ₗ[ℚ] ℝ)
    (p : VectorPolynomial σ ℚ L) (i : σ) (α : σ →₀ ℕ) :
    f (coefficients (directionalDerivative (Pi.single i 1) p) α) =
      (α i + 1 : ℝ) * f (coefficients p (α + Finsupp.single i 1)) := by
  rw [directionalDerivative_coordinate]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem directionalDerivative_single_scaled_bound
    (f : L →ₗ[ℚ] ℝ) (p : VectorPolynomial σ ℚ L)
    (d : ℕ) (hdegree : ∀ (β : σ →₀ ℕ) (i : σ), d < β i → f (coefficients p β) = 0)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ β, |f (coefficients p β)| ≤ M / monomialScale T β) (i : σ) (α : σ →₀ ℕ) :
    |f (coefficients (directionalDerivative (Pi.single i 1) p) α)| ≤
      ((d : ℝ) * M / T i) / monomialScale T α := by
  rw [directionalDerivative_single_coordinate]
  by_cases hd : d < α i + 1
  · rw [hdegree _ i (by simpa using hd), mul_zero, abs_zero]
    exact div_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hM) (hT i).le)
      (monomialScale_pos T hT α).le
  · have hdi : (α i + 1 : ℝ) ≤ d := by exact_mod_cast Nat.le_of_not_gt hd
    have hscale : monomialScale T (α + Finsupp.single i 1) = monomialScale T α * T i := by
      rw [monomialScale_add]
      simp [monomialScale]
    have hcoef := hp (α + Finsupp.single i 1)
    rw [hscale] at hcoef
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α i + 1)]
    calc
      _ ≤ (d : ℝ) * (M / (monomialScale T α * T i)) :=
        mul_le_mul hdi hcoef (abs_nonneg _) (Nat.cast_nonneg d)
      _ = _ := by ring

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem realAdaptedDirectionalDerivative_single_bound
    {σ ι L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T M x) (i : σ) :
    F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T ((s : ℝ) * M / T i)
      (F.realAdaptedDirectionalDerivative (Pi.single i 1) x) := by
  have hp := (F.realAdaptedCoefficientBound_polynomial_iff b ω hF (fun _ => 1) T hT hM
    (⟨x⟩ : F.RealAdaptedPolynomialGroup (fun _ => 1))).mp hx
  intro z
  rw [← F.realAdaptedPolynomialTensor_coordinates (fun _ => 1) b ω hF,
    F.realAdaptedDirectionalDerivative_polynomial]
  let f := ((b.baseChange ℝ).coord z.val.2).restrictScalars ℚ
  have hdegree : ∀ (β : σ →₀ ℕ) (j : σ), s < β j →
      f (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) β) = 0 := by
    intro β j hj
    have hβ := Finsupp.le_weight (fun _ : σ => 1) (s := j) (by decide) β
    have hi := F.adaptedBasis_weight_le_step b ω hF z.val.2
    have hni : ¬Finsupp.weight (fun _ : σ => 1) β ≤ ω z.val.2 := by omega
    exact (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp
      ((F.realification.adapted_iff_coefficients (fun _ => 1) _).mp
        (F.realAdaptedPolynomialMap_adapted (fun _ => 1) x) β) z.val.2 hni
  exact directionalDerivative_single_scaled_bound f
    (F.realAdaptedPolynomialMap (fun _ => 1) x) s hdegree T hT M hM
    (fun β => hp β z.val.2) i z.val.1

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealCoefficientPolynomialProjection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realFirstCoefficientOfPolynomial :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) →ₗ[ℚ] F.RealFirstCoefficientModule w :=
  ((F.realFirstCoefficientBasis b ω hF w).repr.symm.restrictScalars ℚ).toLinearMap.comp
    (supportedCoordinates (b.baseChange ℝ)
      {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 + 1 = ω z.2})

theorem realFirstCoefficientOfPolynomial_coordinate
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr
      (F.realFirstCoefficientOfPolynomial b ω hF w p) z =
      (b.baseChange ℝ).repr (coefficients p z.val.1) z.val.2 := by
  change ((F.realFirstCoefficientBasis b ω hF w).repr
    ((F.realFirstCoefficientBasis b ω hF w).repr.symm _)) z = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem realFirstCoefficientOfPolynomial_map (x : F.realShiftedCoefficientSubmodule w 1) :
    F.realFirstCoefficientOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w x.val) =
      F.realFirstCoefficientMap w x := by
  apply (F.realFirstCoefficientBasis b ω hF w).repr.injective
  ext z
  rw [F.realFirstCoefficientOfPolynomial_coordinate, F.realFirstCoefficientBasis_polynomial_coordinate]

theorem realFirstCoefficientOfPolynomial_eq_of_firstJet
    (p q : F.realification.adaptedLieSubalgebra w)
    (hpq : F.realification.filteredFirstJetMap w p = F.realification.filteredFirstJetMap w q) :
    F.realFirstCoefficientOfPolynomial b ω hF w p.val =
      F.realFirstCoefficientOfPolynomial b ω hF w q.val := by
  have hdiff := (F.realification.filteredFirstJetMap_eq_iff w p q).mp hpq
  apply (F.realFirstCoefficientBasis b ω hF w).repr.injective
  ext z
  rw [F.realFirstCoefficientOfPolynomial_coordinate, F.realFirstCoefficientOfPolynomial_coordinate]
  have hc := (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp (hdiff z.val.1)
    z.val.2 (by have hz := z.property; omega)
  rw [map_sub, Finsupp.sub_apply, map_sub, Finsupp.sub_apply] at hc
  exact sub_eq_zero.mp hc

include b ω hF in
theorem realShiftedCoefficient_mem_iff_tensor (k : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    x ∈ F.realShiftedCoefficientSubmodule w k ↔
      F.realAdaptedPolynomialTensor w x ∈ F.realification.shiftedPolynomialIdeal w k := by
  rw [F.realShiftedCoefficient_eq_span b ω hF, basis_mem_span_image_iff]
  constructor
  · intro hx α
    apply (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mpr
    intro i hi
    by_cases hai : Finsupp.weight w α ≤ ω i
    · change (b.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap w x) α) i = 0
      rw [F.realAdaptedPolynomialTensor_coordinates w b ω hF x ⟨(α, i), hai⟩]
      exact hx ⟨(α, i), hai⟩ hi
    · exact (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp
        ((F.realAdaptedPolynomialTensor w x).property α) i hai
  · intro hx z hz
    rw [← F.realAdaptedPolynomialTensor_coordinates w b ω hF x z]
    exact (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp (hx z.val.1) z.val.2 hz

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ReducedSquareFastKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

noncomputable def reducedSquareFastDiagonalSubalgebra : LieSubalgebra ℚ (F.quotientTop.PolynomialSymbol w) :=
  W.map (F.reducedSquareSndSymbolMap w)

noncomputable def reducedSquareFastRelativeSubmodule : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w) :=
  W.toSubmodule ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule

theorem reducedSquareFastRelative_action_mem (hw : ∀ i, 0 < w i)
    {u : F.quotientTop.PolynomialSymbol w} (hu : u ∈ F.reducedSquareFastDiagonalSubalgebra w W)
    {v : F.squareFiltration.quotientTop.PolynomialSymbol w} (hv : v ∈ F.reducedSquareFastRelativeSubmodule w W) :
    ⁅F.reducedSquareDiagonalSymbolMap w u, v⁆ ∈ F.reducedSquareFastRelativeSubmodule w W := by
  obtain ⟨x, hx, hxu⟩ := hu
  change F.reducedSquareSndSymbolMap w x = u at hxu
  have hk : F.reducedSquareSndSymbolMap w (x - F.reducedSquareDiagonalSymbolMap w u) = 0 := by
    rw [map_sub, F.reducedSquareSndSymbolMap_diagonal, hxu, sub_self]
  have hbracket := F.reducedSquareSndSymbolKernel_lie_eq_zero w hw hk hv.2
  rw [sub_lie] at hbracket
  have he := sub_eq_zero.mp hbracket
  constructor
  · rw [← he]
    exact W.lie_mem hx hv.1
  · change F.reducedSquareSndSymbolMap w ⁅F.reducedSquareDiagonalSymbolMap w u, v⁆ = 0
    rw [LieHom.map_lie, F.reducedSquareSndSymbolMap_diagonal, show F.reducedSquareSndSymbolMap w v = 0 from hv.2,
      lie_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem normalizedRelativeSubmodule_lie_mem (a p : F.adaptedLieSubalgebra w)
    (hp : p ∈ F.normalizedRelativeSubmodule w) :
    ⁅a, p⁆ ∈ F.normalizedRelativeSubmodule w := by
  refine ⟨(F.shiftedAdaptedIdeal w).lie_mem hp.1, ?_⟩
  change coefficients ⁅a.val, p.val⁆ 0 ∈ F.layer 2
  rw [← eval_zero_eq_coefficient]
  change evalLie (0 : σ → ℚ) ⁅a.val, p.val⁆ ∈ F.layer 2
  rw [LieHom.map_lie]
  apply (F.layerIdeal 2).lie_mem
  change eval (fun _ : σ => 0) p.val ∈ F.layer 2
  rw [eval_zero_eq_coefficient]
  exact hp.2

noncomputable def normalizedRelativeIdeal : LieIdeal ℚ (F.adaptedLieSubalgebra w) :=
  { F.normalizedRelativeSubmodule w with
    lie_mem := fun {a p} hp => F.normalizedRelativeSubmodule_lie_mem w a p hp }

theorem relativeSquareLift_lie (hw : ∀ i, 0 < w i)
    (a : F.adaptedLieSubalgebra w) (p : F.normalizedRelativeSubmodule w) :
    F.relativeSquareLift w hw ⟨⁅a, p.val⁆, F.normalizedRelativeSubmodule_lie_mem w a p.val p.property⟩ =
      ⁅F.squareDiagonalPolynomialMap w a, F.relativeSquareLift w hw p⁆ := by
  apply F.square_polynomial_ext w
  · rw [F.squareFstPolynomialMap_relative, LieHom.map_lie,
      F.squareFstPolynomialMap_diagonal, F.squareFstPolynomialMap_relative]
  · rw [F.squareSndPolynomialMap_relative, LieHom.map_lie,
      F.squareSndPolynomialMap_relative, lie_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

noncomputable def realLinearCoordinateLift (σ : M →ₗ[ℚ] L)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM)) :
    NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL) :=
  ⟨σ.baseChange ℝ g.coord⟩

@[simp] theorem realLinearCoordinateLift_coord (σ : M →ₗ[ℚ] L)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM)) :
    (realLinearCoordinateLift (hL := hL) (hM := hM) σ g).coord = σ.baseChange ℝ g.coord := rfl

theorem exists_controlled_fast_lift {ι κ μ δ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hM : LieModule.lowerCentralSeries ℚ M M t = ⊥)
    (e : Basis ι ℚ L) (f : Basis μ ℚ M) (c : ι → δ) (r : μ → δ)
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    (hU : BasisBlockInvariant e c U.toSubmodule)
    (φ : L →ₗ⁅ℚ⁆ M) (hblock : ∀ i j, r i ≠ c j → f.repr (φ (e j)) i = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ j i, RationalHeightLE (e.repr (v j) i) H)
    (hφ : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (ι ⊕ μ) : ℝ) ≤ p)
    (hcols : ((Fintype.card ι * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := (p + 2) ^ 10
    ∃ (σ : M →ₗ[ℚ] L) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((q + 2) ^ 36) ∧ l ∣ m ∧
      (∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM),
        g ∈ realificationSubgroup (hnil := hM) (U.map φ) →
          realLinearCoordinateLift (hL := hL) (hM := hM) σ g ∈ realificationSubgroup (hnil := hL) U ∧
          realificationMap (hnil := hL) (hM := hM) φ (realLinearCoordinateLift (hL := hL) (hM := hM) σ g) = g) ∧
      (∀ (W : δ → ℝ), (∀ d, 0 < W d) → ∀ (B : ℝ), 0 ≤ B →
        ∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM),
          (∀ i, |(f.baseChange ℝ).equivFun g.coord i| ≤ B / W (r i)) →
            ∀ i, |(e.baseChange ℝ).equivFun (realLinearCoordinateLift (hL := hL) (hM := hM) σ g).coord i| ≤
              Real.exp ((q + 2) ^ 18) * B / W (c i)) ∧
      (∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM),
        (f.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (realLinearCoordinateLift (hL := hL) (hM := hM) σ g).coord ∈
            realDenominatorGrid m) := by
  obtain ⟨σ, m, hm, hmp, hlm, _, hsolve, hslow, hgrid⟩ :=
    exists_controlled_linear_subspace_lift e f c r U.toSubmodule v hspan hU φ.toLinearMap hblock
      hH hl hv hφ hp hrows hcols hHp hlp
  refine ⟨σ, m, hm, hmp, hlm, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨hmem, hproj⟩ := hsolve g.coord hg
    exact ⟨hmem, NilpotentLieBCHGroup.ext hproj⟩
  · intro W hW B hB g hg
    exact hslow W hW B hB g.coord hg
  · intro g hg
    exact hgrid g.coord hg

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def reducedSquareRealSymbolHom :
    F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w →*
      F.quotientTop.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := F.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w) (F.reducedSquareSndSymbolMap w)

noncomputable def reducedSquareRealLinearLift
    (S : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
    (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w := ⟨S.baseChange ℝ g.coord⟩

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]

theorem exists_controlled_reduced_fast_lift {κ : Type*} [Fintype κ]
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1) U.toSubmodule)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ j i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hrows : (Fintype.card (ReducedSquareSymbolIndex s w ω ⊕ QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hcols : ((Fintype.card (ReducedSquareSymbolIndex s w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := (p + 2) ^ 10
    ∃ (S : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
      (m : ℕ), 0 < m ∧ (m : ℝ) ≤ Real.exp ((q + 2) ^ 36) ∧ l ∣ m ∧
      (∀ g : F.quotientTop.RealPolynomialSymbolGroup w,
        g.coord ∈ realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
          (F.reducedSquareRealLinearLift w S g).coord ∈ realificationLieSubalgebra U ∧
          F.reducedSquareRealSymbolHom w (F.reducedSquareRealLinearLift w S g) = g) ∧
      (∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ (B : ℝ), 0 ≤ B →
        ∀ g : F.quotientTop.RealPolynomialSymbolGroup w,
          F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
            (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T B g →
          F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
            (Real.exp ((q + 2) ^ 18) * B) (F.reducedSquareRealLinearLift w S g)) ∧
      (∀ g : F.quotientTop.RealPolynomialSymbolGroup w,
        F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l g →
        F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w m
          (F.reducedSquareRealLinearLift w S g)) := by
  obtain ⟨S, m, hm, hmp, hlm, hsolve, hslow, hgrid⟩ :=
    NilpotentLieBCHGroup.exists_controlled_fast_lift
      (F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (F.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (F.reducedSquareSymbolBasis e ω hF w) (F.quotientTopSymbolBasis e ω hF w)
      (fun z => z.val.1) (fun z => z.val.1) U v hspan hU (F.reducedSquareSndSymbolMap w)
      (fun i j hij => F.reducedSquareSndSymbolMap_monomial_blocks e ω hF w j i hij)
      hH hl hv (fun i j => (F.reducedSquareSndSymbolMap_basis_height e ω hF w j i).mono hH)
      hp hrows hcols hHp hlp
  refine ⟨S, m, hm, hmp, hlm, ?_, ?_, ?_⟩
  · intro g hg
    exact hsolve g hg
  · intro T hT B hB g hg
    exact hslow (monomialScale T) (monomialScale_pos T hT) B hB g hg
  · intro g hg
    exact hgrid g hg

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareRealSymbolKernel_eq :
    (F.reducedSquareSndSymbolMap w).ker.toSubmodule.baseChange ℝ =
      LinearMap.ker ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ) :=
  realification_ker (F.reducedSquareSndSymbolMap w).toLinearMap

theorem reducedSquareRealSymbolKernel_lie_eq_zero (hw : ∀ i, 0 < w i)
    {x y : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hx : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ x = 0)
    (hy : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ y = 0) :
    ⁅x, y⁆ = 0 := by
  have hx' : x ∈ (F.reducedSquareSndSymbolMap w).ker.toSubmodule.baseChange ℝ := by
    rw [F.reducedSquareRealSymbolKernel_eq]
    exact hx
  have hy' : y ∈ (F.reducedSquareSndSymbolMap w).ker.toSubmodule.baseChange ℝ := by
    rw [F.reducedSquareRealSymbolKernel_eq]
    exact hy
  have hh := lie_mem_real_baseChange (F.reducedSquareSndSymbolMap w).ker.toSubmodule
    (F.reducedSquareSndSymbolMap w).ker.toSubmodule ⊥
    (fun a ha b hb => (Submodule.mem_bot ℚ).mpr
      (F.reducedSquareSndSymbolKernel_lie_eq_zero w hw ha hb)) hx' hy'
  simpa only [Submodule.baseChange_bot, Submodule.mem_bot] using hh

theorem reducedSquareRealSymbolKernel_bch (hw : ∀ i, 0 < w i)
    {x y : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hx : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ x = 0)
    (hy : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ y = 0) :
    lieBCH s x y = x + y :=
  lieBCH_eq_add_of_lie_eq_zero
    (realification_lowerCentralSeries_eq_bot
      (F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w))
    (F.reducedSquareRealSymbolKernel_lie_eq_zero w hw hx hy)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def reducedSquareRealDiagonalHom :
    F.quotientTop.RealPolynomialSymbolGroup w →*
      F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w :=
  realificationMap
    (hnil := F.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (F.reducedSquareDiagonalSymbolMap w)

@[simp] theorem reducedSquareRealSymbolHom_diagonal (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    F.reducedSquareRealSymbolHom w (F.reducedSquareRealDiagonalHom w g) = g := by
  have h : (F.reducedSquareSndSymbolMap w).toLinearMap.comp
      (F.reducedSquareDiagonalSymbolMap w).toLinearMap = LinearMap.id := by
    ext x
    exact F.reducedSquareSndSymbolMap_diagonal w x
  have hr := congrArg (fun f : F.quotientTop.PolynomialSymbol w →ₗ[ℚ]
    F.quotientTop.PolynomialSymbol w => f.baseChange ℝ) h
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hr
  apply NilpotentLieBCHGroup.ext
  exact DFunLike.congr_fun hr g.coord

noncomputable def reducedSquareRealRelativePart
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w :=
  splitRelativePart (F.reducedSquareRealSymbolHom w) (F.reducedSquareRealDiagonalHom w) g

@[simp] theorem reducedSquareRealRelativePart_projection
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.reducedSquareRealSymbolHom w (F.reducedSquareRealRelativePart w g) = 1 :=
  splitRelativePart_projection _ _ (F.reducedSquareRealSymbolHom_diagonal w) g

theorem reducedSquareRealRelativePart_coord_kernel
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
      (F.reducedSquareRealRelativePart w g).coord = 0 :=
  congrArg NilpotentLieBCHGroup.coord (F.reducedSquareRealRelativePart_projection w g)

theorem reducedSquareRealRelativePart_mul
    (g h : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.reducedSquareRealRelativePart w (g * h) = F.reducedSquareRealRelativePart w g *
      (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g) *
        F.reducedSquareRealRelativePart w h *
        (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g))⁻¹) :=
  splitRelativePart_mul _ _ g h

theorem reducedSquareRealRelativePart_mul_coord (hw : ∀ i, 0 < w i)
    (g h : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    (F.reducedSquareRealRelativePart w (g * h)).coord =
      (F.reducedSquareRealRelativePart w g).coord +
      (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g) *
        F.reducedSquareRealRelativePart w h *
        (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g))⁻¹).coord := by
  have hk : F.reducedSquareRealSymbolHom w
      (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g) *
        F.reducedSquareRealRelativePart w h *
        (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w g))⁻¹) = 1 := by
    simp only [map_mul, map_inv, F.reducedSquareRealSymbolHom_diagonal,
      F.reducedSquareRealRelativePart_projection, mul_one, mul_inv_cancel]
  rw [F.reducedSquareRealRelativePart_mul, coord_mul]
  exact F.reducedSquareRealSymbolKernel_bch w hw
    (F.reducedSquareRealRelativePart_coord_kernel w g) (congrArg NilpotentLieBCHGroup.coord hk)

theorem reducedSquareRealRelative_same_diagonal_mod_kernel (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    {g h : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w}
    (hg : g.coord ∈ realificationLieSubalgebra U) (hh : h.coord ∈ realificationLieSubalgebra U)
    (hproj : F.reducedSquareRealSymbolHom w g = F.reducedSquareRealSymbolHom w h) :
    (F.reducedSquareRealRelativePart w g).coord - (F.reducedSquareRealRelativePart w h).coord ∈
      (F.reducedSquareFastRelativeSubmodule w U).baseChange ℝ := by
  have hpair := splitRelativePart_pair_mem (F.reducedSquareRealSymbolHom w)
    (F.reducedSquareRealDiagonalHom w) (F.reducedSquareRealSymbolHom_diagonal w)
    (realificationSubgroup
      (hnil := F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w) U)
    hg hh hproj
  have hneg : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
      (-(F.reducedSquareRealRelativePart w h).coord) = 0 := by
    rw [map_neg, F.reducedSquareRealRelativePart_coord_kernel, neg_zero]
  have he : (F.reducedSquareRealRelativePart w g * (F.reducedSquareRealRelativePart w h)⁻¹).coord =
      (F.reducedSquareRealRelativePart w g).coord - (F.reducedSquareRealRelativePart w h).coord := by
    rw [coord_mul, coord_inv, F.reducedSquareRealSymbolKernel_bch w hw
      (F.reducedSquareRealRelativePart_coord_kernel w g) hneg, sub_eq_add_neg]
  change _ ∈ (U.toSubmodule ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule).baseChange ℝ
  rw [realification_inf, F.reducedSquareRealSymbolKernel_eq]
  constructor
  · have hm : (F.reducedSquareRealRelativePart w g * (F.reducedSquareRealRelativePart w h)⁻¹).coord ∈
        realificationLieSubalgebra U := hpair.1
    rwa [he] at hm
  · change (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
      ((F.reducedSquareRealRelativePart w g).coord - (F.reducedSquareRealRelativePart w h).coord) = 0
    rw [map_sub, F.reducedSquareRealRelativePart_coord_kernel,
      F.reducedSquareRealRelativePart_coord_kernel, sub_self]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

noncomputable def realReducedRelativeSquareSymbolMap :
    (ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) →ₗ[ℝ]
      (ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w) :=
  (F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ

theorem realReducedRelativeSquareSymbolMap_range :
    LinearMap.range (F.realReducedRelativeSquareSymbolMap w hw) =
      LinearMap.ker ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ) := by
  have h := realification_map (⊤ : Submodule ℚ (F.normalizedRelativeSubmodule w))
    (F.reducedRelativeSquareSymbolMap w hw)
  simp only [Submodule.map_top, Submodule.baseChange_top] at h
  change LinearMap.range ((F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ) = _
  rw [← h, F.reducedRelativeSquareSymbolMap_range, F.reducedSquareRealSymbolKernel_eq]

@[simp] theorem realReducedRelativeSquareSymbolMap_projection
    (p : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
      (F.realReducedRelativeSquareSymbolMap w hw p) = 0 := by
  have h : F.realReducedRelativeSquareSymbolMap w hw p ∈
      LinearMap.range (F.realReducedRelativeSquareSymbolMap w hw) := ⟨p, rfl⟩
  rw [F.realReducedRelativeSquareSymbolMap_range] at h
  exact h

theorem reducedSquareRealRelativePart_exists_preimage
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    ∃ p : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w,
      F.realReducedRelativeSquareSymbolMap w hw p = (F.reducedSquareRealRelativePart w g).coord := by
  change (F.reducedSquareRealRelativePart w g).coord ∈
    LinearMap.range (F.realReducedRelativeSquareSymbolMap w hw)
  rw [F.realReducedRelativeSquareSymbolMap_range]
  exact F.reducedSquareRealRelativePart_coord_kernel w g

theorem reducedSquareRealRelativePart_of_factors
    (k : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (x : F.quotientTop.RealPolynomialSymbolGroup w)
    (hk : F.reducedSquareRealSymbolHom w k = 1) :
    F.reducedSquareRealRelativePart w (k * F.reducedSquareRealDiagonalHom w x) = k := by
  change (k * F.reducedSquareRealDiagonalHom w x) *
    (F.reducedSquareRealDiagonalHom w
      (F.reducedSquareRealSymbolHom w (k * F.reducedSquareRealDiagonalHom w x)))⁻¹ = k
  rw [map_mul, F.reducedSquareRealSymbolHom_diagonal, hk, one_mul]
  group

include hw in
theorem reducedSquareRealRelativePart_triple_coord
    (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    (F.reducedSquareRealRelativePart w (E * P * R)).coord =
      (F.reducedSquareRealRelativePart w E).coord +
        (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w E) *
          F.reducedSquareRealRelativePart w P *
            (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w E))⁻¹).coord +
        (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w (E * P)) *
          F.reducedSquareRealRelativePart w R *
            (F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w (E * P)))⁻¹).coord := by
  rw [F.reducedSquareRealRelativePart_mul_coord w hw (E * P) R,
    F.reducedSquareRealRelativePart_mul_coord w hw E P]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem realNormalizedFirstCoefficientMap_ker :
    LinearMap.ker (F.realNormalizedFirstCoefficientMap w) =
      LinearMap.ker (F.realReducedRelativeSquareSymbolMap w hw) := by
  have hk : LinearMap.ker ((F.normalizedFirstCoefficientMap w).baseChange ℝ) =
      LinearMap.ker ((F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ) := by
    rw [← realification_ker, ← realification_ker, F.normalizedFirstCoefficientMap_ker w hw]
  ext x
  change F.firstCoefficientRealEquiv w ((F.normalizedFirstCoefficientMap w).baseChange ℝ x) = 0 ↔
    (F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ x = 0
  rw [LinearEquiv.map_eq_zero_iff]
  exact SetLike.ext_iff.mp hk x

noncomputable def realFirstCoefficientRelativeEquiv :
    LinearMap.ker (F.realFirstCoefficientHorizontal w) ≃ₗ[ℝ]
      LinearMap.ker ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ) :=
  commonKernelSubmoduleEquiv (F.realNormalizedFirstCoefficientMap w)
    (F.realReducedRelativeSquareSymbolMap w hw)
    (LinearMap.ker (F.realFirstCoefficientHorizontal w))
    (LinearMap.ker ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ))
    (F.realNormalizedFirstCoefficientMap_ker w hw)
    (F.realNormalizedFirstCoefficientMap_range w)
    (F.realReducedRelativeSquareSymbolMap_range w hw)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def adaptedReducedSymbolMap :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.quotientTop.PolynomialSymbol w :=
  (F.quotientTopSymbolMap w).comp (F.polynomialSymbolMap w)

noncomputable def adaptedReducedRealSymbolHom :
    F.RealAdaptedPolynomialGroup w →* F.quotientTop.RealPolynomialSymbolGroup w :=
  realificationMap
    (hnil := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := F.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (F.adaptedReducedSymbolMap w)

noncomputable def realNormalizedRelativeAdjoint (g : F.RealAdaptedPolynomialGroup w) :
    (ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) ≃ₗ[ℝ]
      (ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :=
  realIdealAdjoint (F.normalizedRelativeIdeal w)
    (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot g

theorem realNormalizedRelativeAdjoint_inclusion (g : F.RealAdaptedPolynomialGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    (F.normalizedRelativeSubmodule w).subtype.baseChange ℝ (F.realNormalizedRelativeAdjoint w g x) =
      dualAdjoint g ((F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x) :=
  realIdealAdjoint_inclusion (F.normalizedRelativeIdeal w)
    (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot g x

theorem reducedRelativeSquareSymbolMap_lie (hw : ∀ i, 0 < w i)
    (a : F.adaptedLieSubalgebra w) (p : F.normalizedRelativeSubmodule w) :
    F.reducedRelativeSquareSymbolMap w hw
        ⟨⁅a, p.val⁆, F.normalizedRelativeSubmodule_lie_mem w a p.val p.property⟩ =
      ⁅F.reducedSquareDiagonalSymbolMap w (F.adaptedReducedSymbolMap w a),
        F.reducedRelativeSquareSymbolMap w hw p⁆ := by
  change F.reducedSquareSymbolMap w
      (F.squareFiltration.polynomialSymbolMap w
        (F.relativeSquareLift w hw ⟨⁅a, p.val⁆, _⟩)) = _
  rw [F.relativeSquareLift_lie, LieHom.map_lie, LieHom.map_lie,
    ← F.squareDiagonalSymbolMap_symbol, ← F.reducedSquareDiagonalSymbolMap_quotient]
  rfl

theorem realReducedRelativeSquareSymbolMap_adjoint (hw : ∀ i, 0 < w i)
    (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realReducedRelativeSquareSymbolMap w hw (F.realNormalizedRelativeAdjoint w g x) =
      dualAdjoint (F.reducedSquareRealDiagonalHom w (F.adaptedReducedRealSymbolHom w g))
        (F.realReducedRelativeSquareSymbolMap w hw x) := by
  let B := (F.reducedSquareDiagonalSymbolMap w).comp (F.adaptedReducedSymbolMap w)
  have hb : realificationMap
      (hnil := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
      (hM := F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w) B g =
      F.reducedSquareRealDiagonalHom w (F.adaptedReducedRealSymbolHom w g) := by
    apply NilpotentLieBCHGroup.ext
    change ((F.reducedSquareDiagonalSymbolMap w).toLinearMap.comp
      (F.adaptedReducedSymbolMap w).toLinearMap).baseChange ℝ g.coord =
      (F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ
        ((F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ g.coord)
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply]
  have he := realIdealMap_adjoint (F.normalizedRelativeIdeal w)
    (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot
    (F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
    B (F.reducedRelativeSquareSymbolMap w hw) (F.reducedRelativeSquareSymbolMap_lie w hw) g x
  rw [hb] at he
  exact he

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

noncomputable def realFirstCoefficientFastSubmodule : Submodule ℝ (F.RealFirstCoefficientModule w) :=
  ((F.firstCoefficientFastSubmodule w hw U).baseChange ℝ).map (F.firstCoefficientRealEquiv w).toLinearMap

theorem realFirstCoefficientFastSubmodule_le_horizontal_ker :
    F.realFirstCoefficientFastSubmodule w hw U ≤ LinearMap.ker (F.realFirstCoefficientHorizontal w) := by
  rintro x ⟨y, hy, rfl⟩
  change (F.firstCoefficientHorizontal w).baseChange ℝ
    ((F.firstCoefficientRealEquiv w).symm (F.firstCoefficientRealEquiv w y)) = 0
  rw [LinearEquiv.symm_apply_apply]
  have hm := Submodule.baseChange_mono ℝ (F.firstCoefficientFastSubmodule_le_horizontal_ker w hw U) hy
  rw [realification_ker] at hm
  exact hm

theorem realNormalizedFirstCoefficientMap_mem_fast_iff (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realNormalizedFirstCoefficientMap w x ∈ F.realFirstCoefficientFastSubmodule w hw U ↔
      F.realReducedRelativeSquareSymbolMap w hw x ∈ U.baseChange ℝ := by
  have hp : (F.firstCoefficientFastSubmodule w hw U).comap (F.normalizedFirstCoefficientMap w) =
      U.comap (F.reducedRelativeSquareSymbolMap w hw) := by
    ext p
    exact F.normalizedFirstCoefficientMap_mem_fast_iff w hw U p
  have hr := congrArg (fun P : Submodule ℚ (F.normalizedRelativeSubmodule w) => P.baseChange ℝ) hp
  rw [realification_comap, realification_comap] at hr
  have he : (F.normalizedFirstCoefficientMap w).baseChange ℝ x ∈
        (F.firstCoefficientFastSubmodule w hw U).baseChange ℝ ↔
      F.realReducedRelativeSquareSymbolMap w hw x ∈ U.baseChange ℝ := SetLike.ext_iff.mp hr x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = (F.normalizedFirstCoefficientMap w).baseChange ℝ x :=
      (F.firstCoefficientRealEquiv w).injective hxy
    rw [hyx] at hy
    exact he.mp hy
  · intro hx
    exact ⟨(F.normalizedFirstCoefficientMap w).baseChange ℝ x, he.mpr hx, rfl⟩

theorem realNormalizedFirstCoefficientMap_sub_mem_fast_iff
    (x y : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realNormalizedFirstCoefficientMap w x - F.realNormalizedFirstCoefficientMap w y ∈
        F.realFirstCoefficientFastSubmodule w hw U ↔
      F.realReducedRelativeSquareSymbolMap w hw x - F.realReducedRelativeSquareSymbolMap w hw y ∈
        U.baseChange ℝ := by
  rw [← map_sub, ← map_sub]
  exact F.realNormalizedFirstCoefficientMap_mem_fast_iff w hw U (x - y)

noncomputable def realFastCoefficientHorizontal :
    (F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) →ₗ[ℝ]
      (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :=
  (F.realFirstCoefficientFastSubmodule w hw U).liftQ (F.realFirstCoefficientHorizontal w)
    (F.realFirstCoefficientFastSubmodule_le_horizontal_ker w hw U)

noncomputable def realFastCoefficientHorizontalSection :
    (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) →ₗ[ℝ]
      (F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) :=
  (F.realFirstCoefficientFastSubmodule w hw U).mkQ.comp (F.realFirstCoefficientHorizontalSection w)

theorem realFastCoefficientHorizontal_section (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    F.realFastCoefficientHorizontal w hw U (F.realFastCoefficientHorizontalSection w hw U x) = x :=
  F.realFirstCoefficientHorizontal_section w x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include hw in
theorem reducedSquareRealRelative_conjugation
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (x : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hx : (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ x = 0) :
    dualAdjoint g x =
      (g * (⟨x⟩ : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) * g⁻¹).coord := by
  let I := (realLieHomToRat (realificationLieHom (F.reducedSquareSndSymbolMap w))).ker
  apply dualAdjoint_eq_conjugation_of_abelian_ideal I _ g x hx
  intro a ha b hb
  exact F.reducedSquareRealSymbolKernel_lie_eq_zero w hw ha hb

theorem realReducedRelativeSquareSymbolMap_conjugation
    (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realReducedRelativeSquareSymbolMap w hw (F.realNormalizedRelativeAdjoint w g x) =
      (F.reducedSquareRealDiagonalHom w (F.adaptedReducedRealSymbolHom w g) *
        (⟨F.realReducedRelativeSquareSymbolMap w hw x⟩ :
          F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) *
        (F.reducedSquareRealDiagonalHom w (F.adaptedReducedRealSymbolHom w g))⁻¹).coord := by
  rw [F.realReducedRelativeSquareSymbolMap_adjoint]
  exact F.reducedSquareRealRelative_conjugation w hw _ _
    (F.realReducedRelativeSquareSymbolMap_projection w hw x)

theorem realReducedRelativeSquareSymbolMap_conjugation_of_eq
    (g : F.RealAdaptedPolynomialGroup w) (h : F.quotientTop.RealPolynomialSymbolGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (r : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.adaptedReducedRealSymbolHom w g = h)
    (hx : F.realReducedRelativeSquareSymbolMap w hw x = r.coord) :
    F.realReducedRelativeSquareSymbolMap w hw (F.realNormalizedRelativeAdjoint w g x) =
      (F.reducedSquareRealDiagonalHom w h * r * (F.reducedSquareRealDiagonalHom w h)⁻¹).coord := by
  rw [F.realReducedRelativeSquareSymbolMap_conjugation, hg, hx]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

def reducedNativeIndex (s : ℕ) (w : σ → ℕ) (ω : ι → ℕ)
    (z : SymbolBasisIndex w (fun i : QuotientTopBasisIndex s ω => ω i.val)) :
    AdaptedBasisIndex w ω :=
  ⟨(z.val.1, z.val.2.val), z.property.le⟩

theorem reducedNativeIndex_injective (s : ℕ) (w : σ → ℕ) (ω : ι → ℕ) :
    Function.Injective (reducedNativeIndex s w ω) := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : AdaptedBasisIndex w ω => z.val.1) h
  · apply Subtype.ext
    exact congrArg (fun z : AdaptedBasisIndex w ω => z.val.2) h

variable (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

local notation "bq" => F.quotientTopBasis b ω hF
local notation "ωq" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "hq" => F.quotientTopBasis_layers b ω hF
local notation "Bq" => F.quotientTop.polynomialSymbolBasis bq ωq hq w
local notation "Ba" => F.adaptedMonomialBasis b ω hF w

noncomputable def reducedNativeSection : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.adaptedLieSubalgebra w :=
  (Bq).constr ℚ (fun z => Ba (reducedNativeIndex s w ω z))

@[simp] theorem reducedNativeSection_basis (z : SymbolBasisIndex w ωq) :
    F.reducedNativeSection b ω hF w (Bq z) = Ba (reducedNativeIndex s w ω z) :=
  Basis.constr_basis _ _ _ z

theorem adaptedReducedSymbolMap_native_basis (z : SymbolBasisIndex w ωq) :
    F.adaptedReducedSymbolMap w (Ba (reducedNativeIndex s w ω z)) = Bq z := by
  classical
  change F.quotientTop.polynomialSymbolMap w
    (F.quotientTopPolynomialMap w (Ba (reducedNativeIndex s w ω z))) = Bq z
  rw [F.quotientTop.polynomialSymbolBasis_apply]
  congr 1
  apply Subtype.ext
  apply coefficients.injective
  ext α
  change coefficients (VectorPolynomial.map (lieQuotientMap (F.layerIdeal (s + 1))).toLinearMap
    (Ba (reducedNativeIndex s w ω z)).val) α = _
  rw [coefficients_map, F.adaptedMonomialBasis_coe,
    F.quotientTop.adaptedMonomialBasis_coe, coefficients_monomial, coefficients_monomial]
  by_cases h : α = z.val.1
  · subst α
    simp only [reducedNativeIndex, Finsupp.single_eq_same, F.quotientTopBasis_apply]
    rfl
  · simp only [reducedNativeIndex, Finsupp.single_eq_of_ne h, map_zero]

theorem reducedNativeSection_rightInverse (x : F.quotientTop.PolynomialSymbol w) :
    F.adaptedReducedSymbolMap w (F.reducedNativeSection b ω hF w x) = x := by
  have he : (F.adaptedReducedSymbolMap w).toLinearMap.comp (F.reducedNativeSection b ω hF w) =
      LinearMap.id := by
    apply (Bq).ext
    intro z
    exact (congrArg (F.adaptedReducedSymbolMap w) (F.reducedNativeSection_basis b ω hF w z)).trans
      (F.adaptedReducedSymbolMap_native_basis b ω hF w z)
  exact DFunLike.congr_fun he x

theorem reducedNativeSection_coordinate (x : F.quotientTop.PolynomialSymbol w)
    (z : SymbolBasisIndex w ωq) :
    (Ba).repr (F.reducedNativeSection b ω hF w x) (reducedNativeIndex s w ω z) = (Bq).repr x z := by
  classical
  have he : ((Ba).coord (reducedNativeIndex s w ω z)).comp (F.reducedNativeSection b ω hF w) =
      (Bq).coord z := by
    apply (Bq).ext
    intro j
    change (Ba).repr (F.reducedNativeSection b ω hF w (Bq j)) (reducedNativeIndex s w ω z) =
      (Bq).repr (Bq j) z
    rw [F.reducedNativeSection_basis, Basis.repr_self, Basis.repr_self]
    simp only [Finsupp.single_apply, (reducedNativeIndex_injective s w ω).eq_iff]
  exact DFunLike.congr_fun he x

theorem reducedNativeSection_coordinate_zero (x : F.quotientTop.PolynomialSymbol w)
    (z : AdaptedBasisIndex w ω)
    (hz : ∀ j, reducedNativeIndex s w ω j ≠ z) :
    (Ba).repr (F.reducedNativeSection b ω hF w x) z = 0 := by
  classical
  have he : ((Ba).coord z).comp (F.reducedNativeSection b ω hF w) = 0 := by
    apply (Bq).ext
    intro j
    change (Ba).repr (F.reducedNativeSection b ω hF w (Bq j)) z = 0
    rw [F.reducedNativeSection_basis, Basis.repr_self]
    exact Finsupp.single_eq_of_ne (hz j).symm
  exact DFunLike.congr_fun he x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

noncomputable def realReducedRelativeCoefficient
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) :
    F.RealFirstCoefficientModule w :=
  ((F.realFirstCoefficientRelativeEquiv w hw).symm
    ⟨(F.reducedSquareRealRelativePart w g).coord, F.reducedSquareRealRelativePart_coord_kernel w g⟩).val

theorem realReducedRelativeCoefficient_of_preimage
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (hx : F.realReducedRelativeSquareSymbolMap w hw x = (F.reducedSquareRealRelativePart w g).coord) :
    F.realNormalizedFirstCoefficientMap w x = F.realReducedRelativeCoefficient w hw g :=
  commonKernelSubmoduleEquiv_symm_apply (F.realNormalizedFirstCoefficientMap w)
    (F.realReducedRelativeSquareSymbolMap w hw)
    (LinearMap.ker (F.realFirstCoefficientHorizontal w))
    (LinearMap.ker ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ))
    (F.realNormalizedFirstCoefficientMap_ker w hw)
    (F.realNormalizedFirstCoefficientMap_range w)
    (F.realReducedRelativeSquareSymbolMap_range w hw) x
    ⟨(F.reducedSquareRealRelativePart w g).coord, F.reducedSquareRealRelativePart_coord_kernel w g⟩ hx

theorem realReducedRelativeCoefficient_same_diagonal
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    {g h : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w}
    (hg : g.coord ∈ realificationLieSubalgebra U) (hh : h.coord ∈ realificationLieSubalgebra U)
    (hproj : F.reducedSquareRealSymbolHom w g = F.reducedSquareRealSymbolHom w h) :
    F.realReducedRelativeCoefficient w hw g - F.realReducedRelativeCoefficient w hw h ∈
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U) := by
  obtain ⟨x, hx⟩ := F.reducedSquareRealRelativePart_exists_preimage w hw g
  obtain ⟨y, hy⟩ := F.reducedSquareRealRelativePart_exists_preimage w hw h
  rw [← F.realReducedRelativeCoefficient_of_preimage w hw g x hx,
    ← F.realReducedRelativeCoefficient_of_preimage w hw h y hy,
    F.realNormalizedFirstCoefficientMap_sub_mem_fast_iff w hw]
  rw [hx, hy]
  exact F.reducedSquareRealRelative_same_diagonal_mod_kernel w hw U hg hh hproj

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

local notation "bq" => F.quotientTopBasis b ω hF
local notation "ωq" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "hq" => F.quotientTopBasis_layers b ω hF
local notation "Bq" => F.quotientTop.polynomialSymbolBasis bq ωq hq w
local notation "Ba" => F.adaptedMonomialBasis b ω hF w

theorem reducedNativeSection_real_coordinate (x : F.quotientTop.RealPolynomialSymbol w)
    (z : SymbolBasisIndex w ωq) :
    ((Ba).baseChange ℝ).repr ((F.reducedNativeSection b ω hF w).baseChange ℝ x)
      (reducedNativeIndex s w ω z) = ((Bq).baseChange ℝ).repr x z := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul,
      F.reducedNativeSection_coordinate]

theorem reducedNativeSection_real_coordinate_zero (x : F.quotientTop.RealPolynomialSymbol w)
    (z : AdaptedBasisIndex w ω) (hz : ∀ j, reducedNativeIndex s w ω j ≠ z) :
    ((Ba).baseChange ℝ).repr ((F.reducedNativeSection b ω hF w).baseChange ℝ x) z = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      F.reducedNativeSection_coordinate_zero b ω hF w x z hz]
    simp

noncomputable def realReducedNativeLift (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    F.RealAdaptedPolynomialGroup w :=
  ⟨(F.reducedNativeSection b ω hF w).baseChange ℝ g.coord⟩

@[simp] theorem adaptedReducedRealSymbolHom_lift (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    F.adaptedReducedRealSymbolHom w (F.realReducedNativeLift b ω hF w g) = g := by
  apply NilpotentLieBCHGroup.ext
  change (F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ
    ((F.reducedNativeSection b ω hF w).baseChange ℝ g.coord) = g.coord
  have he : ∀ x : F.quotientTop.RealPolynomialSymbol w,
      (F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ
        ((F.reducedNativeSection b ω hF w).baseChange ℝ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
      exact congrArg (fun y => a ⊗ₜ[ℚ] y) (F.reducedNativeSection_rightInverse b ω hF w x)
  exact he g.coord

theorem realReducedNativeLift_slow (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (g : F.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.quotientTop.SymbolSlowBound bq ωq hq w T M g) :
    F.RealAdaptedCoefficientBound b ω hF w T M (F.realReducedNativeLift b ω hF w g).coord := by
  intro z
  by_cases hz : ∃ j, reducedNativeIndex s w ω j = z
  · obtain ⟨j, rfl⟩ := hz
    change |((Ba).baseChange ℝ).repr ((F.reducedNativeSection b ω hF w).baseChange ℝ g.coord)
      (reducedNativeIndex s w ω j)| ≤ _
    rw [F.reducedNativeSection_real_coordinate]
    exact hg j
  · change |((Ba).baseChange ℝ).repr ((F.reducedNativeSection b ω hF w).baseChange ℝ g.coord) z| ≤ _
    rw [F.reducedNativeSection_real_coordinate_zero b ω hF w g.coord z (fun j hj => hz ⟨j, hj⟩), abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT z.val.1).le

theorem realReducedNativeLift_grid (l : ℕ) (g : F.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.quotientTop.SymbolRationalGrid bq ωq hq w l g) :
    F.RealAdaptedCoefficientGrid b ω hF w l (F.realReducedNativeLift b ω hF w g).coord := by
  classical
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => if hz : ∃ j, reducedNativeIndex s w ω j = z then a hz.choose else 0, ?_⟩
  funext z
  change ((if hz : ∃ j, reducedNativeIndex s w ω j = z then a hz.choose else 0 : ℤ) : ℝ) =
    (l : ℝ) * ((Ba).baseChange ℝ).repr ((F.reducedNativeSection b ω hF w).baseChange ℝ g.coord) z
  by_cases hz : ∃ j, reducedNativeIndex s w ω j = z
  · rw [dif_pos hz]
    have hc := F.reducedNativeSection_real_coordinate b ω hF w g.coord hz.choose
    have he := congrArg (fun t => ((Ba).baseChange ℝ).repr
      ((F.reducedNativeSection b ω hF w).baseChange ℝ g.coord) t) hz.choose_spec
    rw [he.symm.trans hc]
    exact congrFun ha hz.choose
  · rw [dif_neg hz, Int.cast_zero,
      F.reducedNativeSection_real_coordinate_zero b ω hF w g.coord z (fun j hj => hz ⟨j, hj⟩), mul_zero]

theorem realReducedNativeLift_constant (g : F.quotientTop.RealPolynomialSymbolGroup w) :
    coefficients (F.realAdaptedPolynomialMap w (F.realReducedNativeLift b ω hF w g).coord) 0 = 0 := by
  apply (b.baseChange ℝ).repr.injective
  ext i
  change (b.baseChange ℝ).repr
    (coefficients (F.realAdaptedPolynomialMap w (F.realReducedNativeLift b ω hF w g).coord) 0) i = 0
  let z : AdaptedBasisIndex w ω := ⟨(0, i), by simp⟩
  have hz : ∀ j, reducedNativeIndex s w ω j ≠ z := by
    intro j hj
    have hmono := congrArg (fun t : AdaptedBasisIndex w ω => Finsupp.weight w t.val.1) hj
    change Finsupp.weight w j.val.1 = Finsupp.weight w 0 at hmono
    rw [map_zero] at hmono
    exact (F.adaptedBasis_weight_pos b ω hF j.val.2.val).ne' (j.property.symm.trans hmono)
  exact (F.realAdaptedPolynomialTensor_coordinates w b ω hF _ z).trans
    (F.reducedNativeSection_real_coordinate_zero b ω hF w g.coord z hz)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

local notation "bq" => F.quotientTopBasis b ω hF
local notation "ωq" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "hq" => F.quotientTopBasis_layers b ω hF

theorem exists_reduced_native_factorization (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (l : ℕ) (g : F.RealAdaptedPolynomialGroup w)
    (A P R : F.quotientTop.RealPolynomialSymbolGroup w)
    (hprod : A * P * R = F.adaptedReducedRealSymbolHom w g)
    (hA : F.quotientTop.SymbolSlowBound bq ωq hq w T M A)
    (hR : F.quotientTop.SymbolRationalGrid bq ωq hq w l R) :
    ∃ a p r : F.RealAdaptedPolynomialGroup w,
      a * p * r = g ∧ F.adaptedReducedRealSymbolHom w a = A ∧
      F.adaptedReducedRealSymbolHom w p = P ∧ F.adaptedReducedRealSymbolHom w r = R ∧
      F.RealAdaptedCoefficientBound b ω hF w T M a.coord ∧
      F.RealAdaptedCoefficientGrid b ω hF w l r.coord ∧
      coefficients (F.realAdaptedPolynomialMap w a.coord) 0 = 0 ∧
      coefficients (F.realAdaptedPolynomialMap w r.coord) 0 = 0 ∧
      coefficients (F.realAdaptedPolynomialMap w p.coord) 0 =
        coefficients (F.realAdaptedPolynomialMap w g.coord) 0 := by
  let a := F.realReducedNativeLift b ω hF w A
  let r := F.realReducedNativeLift b ω hF w R
  let p := a⁻¹ * g * r⁻¹
  have hapr : a * p * r = g := by simp [p, mul_assoc]
  have ha : F.adaptedReducedRealSymbolHom w a = A := F.adaptedReducedRealSymbolHom_lift b ω hF w A
  have hr : F.adaptedReducedRealSymbolHom w r = R := F.adaptedReducedRealSymbolHom_lift b ω hF w R
  have hp : F.adaptedReducedRealSymbolHom w p = P := by
    change F.adaptedReducedRealSymbolHom w (a⁻¹ * g * r⁻¹) = P
    rw [map_mul, map_mul, map_inv, map_inv, ha, hr, ← hprod]
    simp [mul_assoc]
  have ha0 := F.realReducedNativeLift_constant b ω hF w A
  have hr0 := F.realReducedNativeLift_constant b ω hF w R
  refine ⟨a, p, r, hapr, ha, hp, hr, F.realReducedNativeLift_slow b ω hF w T hT hM A hA,
    F.realReducedNativeLift_grid b ω hF w l R hR, ha0, hr0, ?_⟩
  have hpoly : F.realAdaptedPolynomialGroupHom w a * F.realAdaptedPolynomialGroupHom w p *
      F.realAdaptedPolynomialGroupHom w r = F.realAdaptedPolynomialGroupHom w g := by
    rw [← map_mul, ← map_mul, hapr]
  exact F.realification.polynomial_factor_middle_constant w
    (F.realAdaptedPolynomialGroupHom w g) (F.realAdaptedPolynomialGroupHom w a)
    (F.realAdaptedPolynomialGroupHom w p) (F.realAdaptedPolynomialGroupHom w r) hpoly ha0 hr0

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareStructureHeight
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : F.layer 2 = Submodule.span ℚ (e '' {i | 2 ≤ ω i}))

theorem adaptedSquareBasis_bracket_repr_inl (x y : F.squareLieSubalgebra) (k : ι) :
    (F.adaptedSquareBasis e ω hF).repr ⁅x, y⁆ (Sum.inl k) = e.repr ⁅x.val.2, y.val.2⁆ k := by
  change (F.squareBasis e _).repr ⁅x, y⁆ (Sum.inl k) = _
  rw [F.squareBasis_repr_inl]
  rfl

theorem adaptedSquareBasis_bracket_repr_inr (x y : F.squareLieSubalgebra) (k : {i // 2 ≤ ω i}) :
    (F.adaptedSquareBasis e ω hF).repr ⁅x, y⁆ (Sum.inr k) =
      e.repr (⁅x.val.1, y.val.1⁆ - ⁅x.val.2, y.val.2⁆) k.val := by
  change (F.squareBasis e _).repr ⁅x, y⁆ (Sum.inr k) = _
  rw [F.squareBasis_repr_inr, supportedSubmoduleBasis_repr]
  rfl

theorem adaptedSquareBasis_structure_height {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (a b k : ι ⊕ {i // 2 ≤ ω i}) :
    RationalHeightLE ((F.adaptedSquareBasis e ω hF).repr
      ⁅F.adaptedSquareBasis e ω hF a, F.adaptedSquareBasis e ω hF b⁆ k) H := by
  rcases a with i | i <;> rcases b with j | j <;> rcases k with k | k
  · rw [F.adaptedSquareBasis_bracket_repr_inl, F.adaptedSquareBasis_inl, F.adaptedSquareBasis_inl]
    exact hc i j k
  · rw [F.adaptedSquareBasis_bracket_repr_inr, F.adaptedSquareBasis_inl, F.adaptedSquareBasis_inl]
    simpa only [sub_self, map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  · rw [F.adaptedSquareBasis_bracket_repr_inl, F.adaptedSquareBasis_inl, F.adaptedSquareBasis_inr]
    simpa only [lie_zero, map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  · rw [F.adaptedSquareBasis_bracket_repr_inr, F.adaptedSquareBasis_inl, F.adaptedSquareBasis_inr]
    simpa only [lie_zero, sub_zero] using hc i j.val k.val
  · rw [F.adaptedSquareBasis_bracket_repr_inl, F.adaptedSquareBasis_inr, F.adaptedSquareBasis_inl]
    simpa only [zero_lie, map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  · rw [F.adaptedSquareBasis_bracket_repr_inr, F.adaptedSquareBasis_inr, F.adaptedSquareBasis_inl]
    simpa only [zero_lie, sub_zero] using hc i.val j k.val
  · rw [F.adaptedSquareBasis_bracket_repr_inl, F.adaptedSquareBasis_inr, F.adaptedSquareBasis_inr]
    simpa only [lie_zero, map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  · rw [F.adaptedSquareBasis_bracket_repr_inr, F.adaptedSquareBasis_inr, F.adaptedSquareBasis_inr]
    simpa only [lie_zero, sub_zero] using hc i.val j.val k.val

variable (F : NilpotentLieFiltration L (s + 1))

theorem reducedSquareBasis_structure_height
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    {H : ℕ} (hH : 1 ≤ H) (hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (a b k : ReducedSquareBasisIndex s ω) :
    RationalHeightLE ((F.reducedSquareBasis e ω hF).repr
      ⁅F.reducedSquareBasis e ω hF a, F.reducedSquareBasis e ω hF b⁆ k) H := by
  change RationalHeightLE (lieStructureConstants (F.reducedSquareBasis e ω hF) a b k) H
  have hspan : (F.squareFiltration.layerIdeal (s + 1)).toSubmodule = Submodule.span ℚ
      (F.adaptedSquareBasis e ω (hF 2) '' {i | s + 1 ≤ squareBasisWeight ω i}) :=
    F.adaptedSquareBasis_layers e ω hF (s + 1)
  have he : lieStructureConstants (F.reducedSquareBasis e ω hF) a b k =
      lieStructureConstants (F.adaptedSquareBasis e ω (hF 2)) a.val b.val k.val :=
    supportedQuotientBasis_lieStructure (F.adaptedSquareBasis e ω (hF 2))
      (F.squareFiltration.layerIdeal (s + 1)) {i | s + 1 ≤ squareBasisWeight ω i} hspan a b k
  rw [he]
  exact F.adaptedSquareBasis_structure_height e ω (hF 2) hH hc a.val b.val k.val

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealReducedFastKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem reducedSquareRealFastRelative_action_mem (hw : ∀ i, 0 < w i)
    {u : ℝ ⊗[ℚ] F.quotientTop.PolynomialSymbol w}
    (hu : u ∈ realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w W))
    {v : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hv : v ∈ (F.reducedSquareFastRelativeSubmodule w W).baseChange ℝ) :
    ⁅(F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ u, v⁆ ∈
      (F.reducedSquareFastRelativeSubmodule w W).baseChange ℝ := by
  let P := (F.reducedSquareFastDiagonalSubalgebra w W).toSubmodule
  let K := F.reducedSquareFastRelativeSubmodule w W
  let d := (F.reducedSquareDiagonalSymbolMap w).toLinearMap
  have hu' : d.baseChange ℝ u ∈ (P.map d).baseChange ℝ := by
    rw [realification_map]
    exact ⟨u, hu, rfl⟩
  have hclosed : ∀ x ∈ P.map d, ∀ y ∈ K, ⁅x, y⁆ ∈ K := by
    rintro x ⟨y, hy, rfl⟩ z hz
    exact F.reducedSquareFastRelative_action_mem w W hw hy hz
  exact lie_mem_real_baseChange (P.map d) K K hclosed hu' hv

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FirstCoefficientLatticeCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_lattice_ready_firstCoefficient_basis
    {σ ι E : Type*} [AddCommGroup E] [Module ℝ E] {d : ℕ}
    (ω : ι → ℕ) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (b : Basis (Fin d) ℝ E) :
    ∃ (e : Equiv.Perm (Fin d)) (a : ℕ), a ≤ d ∧
      (∀ i, i.val < a ↔ (rows (e i)).val.1 = 0) ∧
      ∀ (f : E ≃ₗ[ℝ] E),
        (∀ i j, ω (rows i).val.2 ≤ ω (rows j).val.2 →
          LinearMap.toMatrix b b f.toLinearMap i j = (1 : Matrix (Fin d) (Fin d) ℝ) i j) →
        let b' := b.reindex e.symm
        let A := b'.equivFun.symm.trans (f.trans b'.equivFun)
        (∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0) ∧
        (∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1) ∧
        (∀ i j, i.val < a → j.val < a →
          (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin d) (Fin d) ℝ) i j) := by
  obtain ⟨e, a, ha, hm, hz⟩ := exists_sorted_firstCoefficient_rows ω rows
  refine ⟨e, a, ha, hz, ?_⟩
  intro f hf
  dsimp only
  simp only [basis_coordinate_linearEquiv_matrix]
  have hfirst (i) (hi : i.val < a) : ω (rows (e i)).val.2 = 1 :=
    (firstCoefficientIndex_zero_iff_grade_one ω (rows (e i))).mp ((hz i).mp hi)
  exact ⟨sorted_basis_upper_zero b (fun i => ω (rows i).val.2) f.toLinearMap hf e hm,
    sorted_basis_diagonal_one b (fun i => ω (rows i).val.2) f.toLinearMap hf e,
    sorted_basis_initial_identity b (fun i => ω (rows i).val.2) f.toLinearMap hf e hfirst⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedFixedPatchFunction
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exp_neg_le_div {P a b D : ℝ} (hD : 0 < D)
    (hDb : D ≤ Real.exp b) (hP : a + b ≤ P) :
    Real.exp (-P) ≤ Real.exp (-a) / D := by
  apply (le_div_iff₀ hD).mpr
  calc
    _ ≤ Real.exp (-P) * Real.exp b := mul_le_mul_of_nonneg_left hDb (Real.exp_nonneg _)
    _ = Real.exp (-P + b) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem exists_fixed_weight_patch_function_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X Ω T : Type*} [Fintype Ω] [Nonempty Ω] [Fintype T]
      {d : ℕ} {w : Fin d → ℕ},
      ∀ (A : Ω → PolynomialSlots X d w) (Φ : Ω → PatchKernel d)
        (hw : Monotone w) (_hpos : ∀ i, 1 ≤ w i) (_hs : ∀ i, w i ≤ s) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p →
      (∀ a i, realPolynomialMass ((A a).center i) ≤ p) →
      (∀ a, ((Φ a).lip : ℝ) ≤ Real.exp p) →
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → X → ℝ)
        (score : Ω → T → ℝ), (∀ a t, |score a t| ≤ 1) →
      (∀ a ∈ productive, Real.exp (-p) ≤
        (localLaw a).mean (fun t => score a t * ((A a).slots (point a t)).patchValue (Φ a))) →
      ∃ (Ψ : PatchKernel d) (B : PolynomialSlots X d w)
        (localForm : Ω → PolynomialSlots X d w) (retained : Finset Ω),
        (Ψ.lip : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ p + 1 / 4) ∧
        retained ⊆ productive ∧
        outer.mass productive * Real.exp (-((p + 2) ^ C)) ≤ outer.mass retained ∧
        ∀ a ∈ retained, Real.exp (-((p + 2) ^ C)) ≤ (localLaw a).mean (fun t => score a t *
          (B.shearTransformedSlots hw ((localForm a).loweringAt (point a t))).patchValue Ψ) := by
  obtain ⟨a, ha, htop⟩ := exists_patch_top_net_budget s
  let X : Polynomial ℕ := Polynomial.X
  let R : Polynomial ℕ := (X + 1) * (2 * X + 11)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (3 * R + (4 * R + 2) ^ a + X + 5)
  refine ⟨C, hC, ?_⟩
  intro X₀ Ω T _ _ _ d w A Φ hw hpos hs p hp hd hA hΦ outer productive localLaw point score hscore hpositive
  let r := (p + 1) * (2 * p + 11)
  let q := 4 * r
  have hr : 11 ≤ r := by dsimp only [r]; nlinarith
  have hpR : p + 1 ≤ r := by dsimp only [r]; nlinarith
  have hq : 0 ≤ q := by dsimp only [q]; linarith
  have hpq : p ≤ q := by dsimp only [q]; linarith
  have hbudget' : 3 * r + (q + 2) ^ a + p + 5 ≤ (p + 2) ^ C := by
    simpa [X, R, r, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (q + 2) ^ a := by positivity
  have hmassBudget : r + (q + 2) ^ a ≤ (p + 2) ^ C := by linarith
  have hscoreBudget : p + (r + 3) ≤ (p + 2) ^ C := by linarith
  have hLipBudget : 2 * r + 2 ≤ (p + 2) ^ C := by linarith
  obtain ⟨N, hN, _, hNerror, hNcount, hNlip⟩ :=
    exists_patch_kernel_mesh d hp (Real.exp_nonneg p) hd (le_refl (Real.exp p))
  let K : ℝ≥0 := (2 * ((N + 1) ^ d : ℕ) + 1) / patchKernelGridRadius N
  have hKq : (K : ℝ) ≤ Real.exp q := hNlip.trans (Real.exp_le_exp.mpr (by dsimp only [q]; linarith))
  have hMq : p + 1 / 4 ≤ Real.exp q := by
    have h := (Real.add_one_le_exp p).trans (Real.exp_le_exp.mpr hpq)
    linarith
  obtain ⟨J, hJ, _, hJcount, hJsmall, hJerror⟩ :=
    htop d (p + 1 / 4) K q hq (by linarith) K.coe_nonneg (hd.trans hpq) hMq hKq
  have htwocount : 2 * ((N + 1 : ℕ) : ℝ) ^ d ≤ Real.exp (r + 1) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp 1 * Real.exp r := mul_le_mul h2 (by exact_mod_cast hNcount) (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hlocalScore : Real.exp (-q) ≤ Real.exp (-p) / (2 * ((N + 1 : ℕ) : ℝ) ^ d) :=
    exp_neg_le_div (by positivity) htwocount (by dsimp only [q]; linarith)
  have hhomogeneous : (K : ℝ) * patchTopNetError d s J (p + 1 / 4) ≤
      Real.exp (-p) / (4 * ((N + 1 : ℕ) : ℝ) ^ d) := by
    apply hJerror.trans
    have h := div_le_div_of_nonneg_right hlocalScore (by norm_num : (0 : ℝ) ≤ 2)
    convert h using 1; ring
  obtain ⟨i, B, localForm, retained, hB, hretained, hmass, hlocal⟩ :=
    fixed_weight_patch_function A Φ hw hpos hs hp (Real.exp_nonneg p) (Real.exp_pos (-p)) hA hΦ
      hN hNerror hJ hJsmall hhomogeneous outer productive localLaw point score hscore hpositive
  refine ⟨gridPatchKernel d N hN i, B, localForm, retained,
    hNlip.trans (Real.exp_le_exp.mpr hLipBudget), hB, hretained, ?_, ?_⟩
  · let D : ℝ := ((N + 1 : ℕ) : ℝ) ^ d * ((J + 1 : ℕ) : ℝ) ^ (d * (d + 1) ^ s)
    have hD : 0 < D := by dsimp only [D]; positivity
    have hDupper : D ≤ Real.exp ((p + 2) ^ C) := by
      calc
        D ≤ Real.exp r * Real.exp ((q + 2) ^ a) := by
          exact mul_le_mul (by exact_mod_cast hNcount) (by exact_mod_cast hJcount)
            (by positivity) (Real.exp_nonneg _)
        _ = Real.exp (r + (q + 2) ^ a) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr hmassBudget
    have hi : Real.exp (-((p + 2) ^ C)) ≤ 1 / D := by
      simpa only [neg_zero, Real.exp_zero] using
        exp_neg_le_div (P := (p + 2) ^ C) (a := 0) hD hDupper (by linarith)
    exact (mul_le_mul_of_nonneg_left hi (outer.mass_nonneg productive)).trans
      (by simpa only [mul_one_div, D] using hmass)
  · intro x hx
    have hfourcount : 4 * ((N + 1 : ℕ) : ℝ) ^ d ≤ Real.exp (r + 3) := by
      have h4 : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
      calc
        _ ≤ Real.exp 3 * Real.exp r := mul_le_mul h4 (by exact_mod_cast hNcount) (by positivity) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    exact (exp_neg_le_div (by positivity) hfourcount hscoreBudget).trans (hlocal x hx)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_unrestricted_fixed_weight_patch_function (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {X Ω T : Type*} [Fintype X] [Fintype Ω] [Nonempty Ω] [Fintype T]
      {d : ℕ} {w : Fin d → ℕ},
      ∀ (A : Ω → PolynomialSlots X d w) (Φ : Ω → PatchKernel d)
        (hw : Monotone w) (_hpos : ∀ i, 1 ≤ w i) (_hs : ∀ i, w i ≤ s) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (∀ a, ((Φ a).lip : ℝ) ≤ Real.exp p) →
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → X → ℤ)
        (score : Ω → T → ℝ), (∀ a t, |score a t| ≤ 1) →
      (∀ a ∈ productive, Real.exp (-p) ≤ (localLaw a).mean (fun t =>
        score a t * ((A a).slots (fun i => (point a t i : ℝ))).patchValue (Φ a))) →
      ∃ (Ψ : PatchKernel d) (B : PolynomialSlots X d w)
        (localForm : Ω → PolynomialSlots X d w) (retained : Finset Ω),
        (Ψ.lip : ℝ) ≤ Real.exp ((p + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (p + 2) ^ E) ∧
        retained ⊆ productive ∧
        outer.mass productive * Real.exp (-((p + 2) ^ E)) ≤ outer.mass retained ∧
        ∀ a ∈ retained, Real.exp (-((p + 2) ^ E)) ≤ (localLaw a).mean (fun t => score a t *
          (B.shearTransformedSlots hw ((localForm a).loweringAt (fun i => (point a t i : ℝ)))).patchValue Ψ) := by
  obtain ⟨C, hC, hfixed⟩ := exists_fixed_weight_patch_function_budget s
  let Z : Polynomial ℕ := Polynomial.X
  let Q := Z + Polynomial.C (s + 1) * (2 * Z + 1) ^ s + 2
  obtain ⟨E, hE, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((Q + 2) ^ C + Q + 1)
  refine ⟨E, hE, ?_⟩
  intro X Ω T _ _ _ _ d w A Φ hw hpos hs p hp hd hX hΦ outer productive localLaw point score hscore hpositive
  let q : ℝ := p + ((s : ℝ) + 1) * (2 * p + 1) ^ s + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpq : p ≤ q := by
    have : 0 ≤ ((s : ℝ) + 1) * (2 * p + 1) ^ s := by positivity
    dsimp only [q]
    linarith
  have hbudget' : (q + 2) ^ C + q + 1 ≤ (p + 2) ^ E := by
    simpa [Z, Q, q, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_one] using hbudget p hp
  have hpower : (q + 2) ^ C ≤ (p + 2) ^ E := by linarith
  have hmassBudget : q + 1 / 4 ≤ (p + 2) ^ E := by
    have : 0 ≤ (q + 2) ^ C := by positivity
    linarith
  choose norm hnorm hperm using fun a => (A a).exists_coefficient_normalized
  have hnormMass (a) (i) : realPolynomialMass ((norm a).center i) ≤ q := by
    have h := (norm a).center_mass_le_of_normalized hpos s hs (hnorm a) i
    have hbound : (((s + 1) * (Fintype.card X + d + 1) ^ s : ℕ) : ℝ) ≤
        ((s : ℝ) + 1) * (2 * p + 1) ^ s := by
      push_cast
      gcongr
      linarith
    have ht := h.trans hbound
    dsimp only [q]
    linarith
  have hvalues (a : Ω) (t : X → ℤ) :
      ((norm a).slots (fun i => (t i : ℝ))).patchValue (Φ a) =
        ((A a).slots (fun i => (t i : ℝ))).patchValue (Φ a) := by
    obtain ⟨e, he⟩ := hperm a t
    unfold TriangularSlots.patchValue
    simp_rw [he]
    exact e.tsum_eq (fun b => (Φ a).value
      (((A a).slots (fun i => (t i : ℝ))).residual b))
  have hnormScore (a) (ha : a ∈ productive) : Real.exp (-q) ≤
      (localLaw a).mean (fun t => score a t *
        ((norm a).slots (fun i => (point a t i : ℝ))).patchValue (Φ a)) := by
    simp_rw [hvalues]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (hpositive a ha)
  obtain ⟨Ψ, B, localForm, retained, hLip, hMass, hretained, hprob, hlocal⟩ :=
    hfixed norm Φ hw hpos hs q hq (hd.trans hpq) hnormMass
      (fun a => (hΦ a).trans (Real.exp_le_exp.mpr hpq)) outer productive localLaw
      (fun a t i => (point a t i : ℝ)) score hscore hnormScore
  refine ⟨Ψ, B, localForm, retained, hLip.trans (Real.exp_le_exp.mpr hpower),
    fun i => (hMass i).trans hmassBudget, hretained, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hpower))
      (outer.mass_nonneg productive)).trans hprob
  · intro a ha
    exact (Real.exp_le_exp.mpr (neg_le_neg hpower)).trans (hlocal a ha)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.VaryingRankFixedPatchFunction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace PolynomialPatch

def castRank {X : Type*} {s d e : ℕ} (P : PolynomialPatch X s d) (h : d = e) :
    PolynomialPatch X s e := h ▸ P

theorem castRank_value {X : Type*} {s d e : ℕ} (P : PolynomialPatch X s d)
    (h : d = e) (t : X → ℝ) : (P.castRank h).value t = P.value t := by
  subst e
  rfl

theorem castRank_kernel_lip {X : Type*} {s d e : ℕ} (P : PolynomialPatch X s d)
    (h : d = e) : (P.castRank h).kernel.lip = P.kernel.lip := by
  subst e
  rfl

def formAtWeight {X : Type*} {s d : ℕ} (P : PolynomialPatch X s d)
    (w : Fin d → ℕ) (h : P.weight = w) : PolynomialSlots X d w := h ▸ P.form

theorem formAtWeight_value {X : Type*} {s d : ℕ} (P : PolynomialPatch X s d)
    (w : Fin d → ℕ) (h : P.weight = w) (t : X → ℝ) :
    ((P.formAtWeight w h).slots t).patchValue P.kernel = P.value t := by
  subst w
  rfl

def rankWeightCode {X : Type*} {s d : ℕ} (P : PolynomialPatch X s d)
    (D : ℕ) (hd : d ≤ D) : Fin (D + 1) × (Fin D → Fin (s + 1)) :=
  (⟨d, Nat.lt_succ_of_le hd⟩, fun i =>
    if hi : i.val < d then ⟨P.weight ⟨i.val, hi⟩, Nat.lt_succ_of_le (P.weight_le _)⟩ else 0)

theorem rankWeightCode_eq {X : Type*} {s d e D : ℕ}
    (P : PolynomialPatch X s d) (Q : PolynomialPatch X s e)
    (hd : d ≤ D) (he : e ≤ D)
    (hc : P.rankWeightCode D hd = Q.rankWeightCode D he) :
    ∃ h : d = e, (P.castRank h).weight = Q.weight := by
  have hde : d = e := congrArg (fun c => c.1.val) hc
  subst e
  refine ⟨rfl, ?_⟩
  funext i
  have h := congrArg (fun c => (c.2 ⟨i.val, i.isLt.trans_le hd⟩).val) hc
  simpa only [rankWeightCode, dif_pos i.isLt, castRank] using h

end PolynomialPatch

theorem exists_patch_rank_weight_class {X H : Type*} [Fintype H]
    (outer : FiniteProbabilityWeights H) (productive : Finset H)
    {s D : ℕ} (d : H → ℕ) (P : ∀ h, PolynomialPatch X s (d h))
    (hd : ∀ h, d h ≤ D) (hproductive : 0 < outer.mass productive) :
    ∃ (h₀ : H) (retained : Finset H), h₀ ∈ retained ∧ retained ⊆ productive ∧
      outer.mass productive / ((D + 1 : ℕ) * (s + 1) ^ D : ℕ) ≤ outer.mass retained ∧
      ∀ h ∈ retained, ∃ heq : d h = d h₀, ((P h).castRank heq).weight = (P h₀).weight := by
  let code := fun h => (P h).rankWeightCode D (hd h)
  obtain ⟨c, hc⟩ := outer.exists_code_fiber_mass productive code
  let retained := productive.filter (fun h => code h = c)
  have hmass : outer.mass productive / ((D + 1 : ℕ) * (s + 1) ^ D : ℕ) ≤
      outer.mass retained := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] at hc
    convert hc using 1
    congr 1
    ext h
    simp only [retained, Finset.mem_filter]
  have hretained : 0 < outer.mass retained :=
    (div_pos hproductive (by positivity)).trans_le hmass
  have hnonempty : retained.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    simp only [hempty, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hretained
  obtain ⟨h₀, hh₀⟩ := hnonempty
  refine ⟨h₀, retained, hh₀, Finset.filter_subset _ _, hmass, ?_⟩
  intro h hh
  apply PolynomialPatch.rankWeightCode_eq (P h) (P h₀) (hd h) (hd h₀)
  exact (Finset.mem_filter.mp hh).2.trans (Finset.mem_filter.mp hh₀).2.symm

theorem exists_common_rank_weight_patch_family {X H : Type*} [Fintype H]
    (outer : FiniteProbabilityWeights H) (productive : Finset H)
    {s D : ℕ} (d : H → ℕ) (P : ∀ h, PolynomialPatch X s (d h))
    (hd : ∀ h, d h ≤ D) (hproductive : 0 < outer.mass productive)
    (L : ℝ) (hL : ∀ h, ((P h).kernel.lip : ℝ) ≤ L) :
    ∃ (d₀ : ℕ) (w : Fin d₀ → ℕ) (A : H → PolynomialSlots X d₀ w)
      (Φ : H → PatchKernel d₀) (retained : Finset H),
      d₀ ≤ D ∧ Monotone w ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ s) ∧
      retained ⊆ productive ∧
      outer.mass productive / ((D + 1 : ℕ) * (s + 1) ^ D : ℕ) ≤ outer.mass retained ∧
      (∀ h, ((Φ h).lip : ℝ) ≤ L) ∧
      (∀ h ∈ retained, (Φ h).lip = (P h).kernel.lip) ∧
      ∀ h ∈ retained, ∀ t : X → ℝ, ((A h).slots t).patchValue (Φ h) = (P h).value t := by
  obtain ⟨h₀, retained, hh₀, hsub, hmass, hshape⟩ :=
    exists_patch_rank_weight_class outer productive d P hd hproductive
  let chooseIndex := fun h => if h ∈ retained then h else h₀
  have hmem (h) : chooseIndex h ∈ retained := by
    dsimp only [chooseIndex]
    split_ifs with hh
    · exact hh
    · exact hh₀
  choose rankEq weightEq using fun h => hshape (chooseIndex h) (hmem h)
  let patch := fun h => (P (chooseIndex h)).castRank (rankEq h)
  let A := fun h => (patch h).formAtWeight (P h₀).weight (weightEq h)
  let Φ := fun h => (patch h).kernel
  have hchoose (h) (hh : h ∈ retained) : chooseIndex h = h := by
    exact if_pos hh
  refine ⟨d h₀, (P h₀).weight, A, Φ, retained, hd h₀, (P h₀).weight_mono,
    (P h₀).weight_pos, (P h₀).weight_le, hsub, hmass, ?_, ?_, ?_⟩
  · intro h
    simpa only [Φ, patch, PolynomialPatch.castRank_kernel_lip] using hL (chooseIndex h)
  · intro h hh
    change ((P (chooseIndex h)).castRank (rankEq h)).kernel.lip = _
    rw [PolynomialPatch.castRank_kernel_lip]
    exact congrArg (fun a => (P a).kernel.lip) (hchoose h hh)
  · intro h hh t
    change (((patch h).formAtWeight _ (weightEq h)).slots t).patchValue (patch h).kernel = _
    rw [PolynomialPatch.formAtWeight_value]
    change ((P (chooseIndex h)).castRank (rankEq h)).value t = _
    rw [PolynomialPatch.castRank_value]
    exact congrArg (fun a => (P a).value t) (hchoose h hh)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

theorem exists_varying_rank_fixed_patch_function (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {X H T : Type*}
      [Fintype X] [Fintype H] [Nonempty H] [Fintype T]
      (outer : FiniteProbabilityWeights H) (productive : Finset H)
      (d : H → ℕ) (patch : ∀ h, PolynomialPatch X s (d h)) (D : ℕ) (p : ℝ),
      (∀ h, d h ≤ D) → 0 < outer.mass productive →
      0 ≤ p → (D : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (∀ h, ((patch h).kernel.lip : ℝ) ≤ Real.exp p) →
      ∀ (localLaw : H → FiniteProbabilityWeights T) (point : H → T → X → ℤ)
        (score : H → T → ℝ), (∀ h t, |score h t| ≤ 1) →
      (∀ h ∈ productive, Real.exp (-p) ≤ (localLaw h).mean
        (fun t => score h t * (patch h).value (fun i => (point h t i : ℝ)))) →
      ∃ (d₀ : ℕ) (w : Fin d₀ → ℕ) (hw : Monotone w) (Ψ : PatchKernel d₀)
        (B : PolynomialSlots X d₀ w) (localForm : H → PolynomialSlots X d₀ w)
        (retained : Finset H),
        d₀ ≤ D ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((p + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (p + 2) ^ E) ∧
        retained ⊆ productive ∧
        (outer.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((p + 2) ^ E)) ≤ outer.mass retained ∧
        ∀ h ∈ retained, Real.exp (-((p + 2) ^ E)) ≤ (localLaw h).mean
          (fun t => score h t *
            (B.shearTransformedSlots hw
              ((localForm h).loweringAt (fun i => (point h t i : ℝ)))).patchValue Ψ) := by
  obtain ⟨E, hE, hfixed⟩ := exists_unrestricted_fixed_weight_patch_function s
  refine ⟨E, hE, ?_⟩
  intro X H T _ _ _ _ outer productive d patch D p hd hproductive hp hD hX hLip
    localLaw point score hscore hpositive
  obtain ⟨d₀, w, A, Φ, middle, hd₀, hw, hpos, hws, hsub, hmass, hΦ, _, heval⟩ :=
    exists_common_rank_weight_patch_family outer productive d patch hd hproductive (Real.exp p) hLip
  have hmiddle (h) (hh : h ∈ middle) : Real.exp (-p) ≤ (localLaw h).mean (fun t =>
      score h t * ((A h).slots (fun i => (point h t i : ℝ))).patchValue (Φ h)) := by
    simp_rw [heval h hh]
    exact hpositive h (hsub hh)
  have hdreal : (d₀ : ℝ) ≤ p := (Nat.cast_le.mpr hd₀).trans hD
  obtain ⟨Ψ, B, localForm, retained, hΨ, hB, hretained, hmass', hlocal⟩ :=
    hfixed A Φ hw hpos hws p hp hdreal hX hΦ outer middle localLaw point score hscore hmiddle
  refine ⟨d₀, w, hw, Ψ, B, localForm, retained, hd₀, hpos, hws,
    hΨ, hB, hretained.trans hsub, ?_, hlocal⟩
  exact (mul_le_mul_of_nonneg_right hmass (Real.exp_nonneg _)).trans hmass'

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ProductiveAbsoluteCRTPatches
namespace OAI

section

namespace Erdos3

namespace IntegerVectorAPFree

variable {I J : Type*} {k : ℕ}

theorem affine_preimage {A : Set (J → ℤ)} (hA : IntegerVectorAPFree A k)
    (hk : 2 ≤ k) (L : (I → ℤ) →+ (J → ℤ)) (b : J → ℤ)
    (domain : Set (I → ℤ))
    (hinj : Set.InjOn (fun x => b + L x) domain) :
    IntegerVectorAPFree (domain ∩ (fun x => b + L x) ⁻¹' A) k := by
  intro a d hd
  by_contra! h
  have ha : a ∈ domain := by simpa using (h ⟨0, by omega⟩).1
  have had : a + d ∈ domain := by simpa using (h ⟨1, by omega⟩).1
  have hLd : L d ≠ 0 := by
    intro hzero
    have he : b + L (a + d) = b + L a := by simp [hzero]
    have he' : a + d = a := hinj had ha he
    apply hd
    exact add_left_cancel (show a + d = a + 0 by simpa using he')
  obtain ⟨i, hi⟩ := hA (b + L a) (L d) hLd
  apply hi
  have hp := (h i).2
  simpa only [Set.mem_preimage, map_add, map_zsmul, add_assoc] using hp

end IntegerVectorAPFree

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

namespace IntegerVectorAPFree

end IntegerVectorAPFree

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchRankPadding
namespace OAI

section

namespace Erdos3.PolynomialPatch

open scoped BigOperators NNReal

noncomputable def unitRank (σ : Type*) (s d : ℕ) (hs : 1 ≤ s) :
    PolynomialPatch σ s d where
  weight := fun _ => 1
  weight_pos := fun _ => le_rfl
  weight_le := fun _ => hs
  weight_mono := fun _ _ _ => le_rfl
  form := { center := fun _ => 0, degree := fun _ => Submodule.zero_mem _ }
  kernel := localTentKernel d 8 le_rfl

@[simp] theorem unitRank_value {σ : Type*} {s d : ℕ} (hs : 1 ≤ s) (t : σ → ℝ) :
    (unitRank σ s d hs).value t = 1 := by
  change ((unitRank σ s d hs).form.slots t).patchValue (localTentKernel d 8 le_rfl) = 1
  have hres : ((unitRank σ s d hs).form.slots t).residual 0 = 0 := by
    ext i
    simp [unitRank, PolynomialSlots.slots, TriangularSlots.residual]
  rw [TriangularSlots.patchValue_eq_at_residual (b := 0)]
  · rw [hres]
    norm_num [localTentKernel]
  · intro i
    rw [hres]
    norm_num

@[simp] theorem unitRank_lip {σ : Type*} {s d : ℕ} (hs : 1 ≤ s) :
    (unitRank σ s d hs).kernel.lip = 4 := by
  norm_num [unitRank, localTentKernel]

noncomputable def padRank {σ : Type*} {s d D : ℕ}
    (P : PolynomialPatch σ s d) (hs : 1 ≤ s) (hd : d ≤ D) :
    PolynomialPatch σ s D :=
  (P.product (unitRank σ s (D-d) hs)).castRank (Nat.add_sub_of_le hd)

@[simp] theorem padRank_value {σ : Type*} {s d D : ℕ}
    (P : PolynomialPatch σ s d) (hs : 1 ≤ s) (hd : d ≤ D) (t : σ → ℝ) :
    (P.padRank hs hd).value t = P.value t := by
  simp only [padRank, castRank_value, product_value, unitRank_value, mul_one]

@[simp] theorem padRank_lip {σ : Type*} {s d D : ℕ}
    (P : PolynomialPatch σ s d) (hs : 1 ≤ s) (hd : d ≤ D) :
    (P.padRank hs hd).kernel.lip = P.kernel.lip + 4 := by
  simp only [padRank, castRank_kernel_lip, product_lip, unitRank_lip]

end Erdos3.PolynomialPatch

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeSourceDensityParameter
namespace OAI

section

namespace Erdos3

noncomputable def densityParameter (α : ℝ) : ℝ := max 2 (Real.log (2 / α))

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def intervalIndicator (S : Finset ℕ) (n : ℕ) : ℝ := if n ∈ S then 1 else 0

noncomputable def intervalDensity (N : ℕ) (S : Finset ℕ) : ℝ := S.card / (N : ℝ)

theorem intervalDensity_pos {N : ℕ} {S : Finset ℕ} (hN : 0 < N) (hS : S.Nonempty) :
    0 < intervalDensity N S :=
  div_pos (by exact_mod_cast Finset.card_pos.mpr hS) (by exact_mod_cast hN)

def progressionPreimage (S : Finset ℕ) (a q M : ℕ) : Finset ℕ :=
  (Finset.range M).filter fun n => a + q * n ∈ S

theorem progressionPreimage_subset (S : Finset ℕ) (a q M : ℕ) :
    progressionPreimage S a q M ⊆ Finset.range M := Finset.filter_subset _ _

theorem APFree.progressionPreimage {S : Finset ℕ} {k : ℕ} (hS : APFree (S : Set ℕ) k)
    (a q M : ℕ) (hq : 0 < q) : APFree (progressionPreimage S a q M : Set ℕ) k := by
  apply (hS.affine_preimage a q hq).mono
  intro n hn
  exact (Finset.mem_filter.mp hn).2

theorem intervalDensity_pos_iff {N : ℕ} {S : Finset ℕ} (hN : 0 < N) :
    0 < intervalDensity N S ↔ S.Nonempty := by
  constructor
  · intro h
    by_contra hn
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he, intervalDensity] at h
  · exact intervalDensity_pos hN

end Erdos3

end

section

namespace Erdos3

open Filter

end Erdos3

end

section

namespace Erdos3.FixedDensity

end Erdos3.FixedDensity

namespace Erdos3

open FixedDensity

noncomputable def cyclicIntervalSet (S : Finset ℕ) (m : ℕ) [NeZero m] : Finset (ZMod m) := by
  classical
  exact Finset.univ.filter fun x => x.val ∈ S

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

structure APFreeInterval (k : ℕ) where
  length : ℕ
  length_gt_one : 1 < length
  points : Finset ℕ
  subset : points ⊆ Finset.range length
  nonempty : points.Nonempty
  free : APFree (points : Set ℕ) k

namespace APFreeInterval

variable {k : ℕ}

noncomputable def density (S : APFreeInterval k) : ℝ := intervalDensity S.length S.points

noncomputable def parameter (S : APFreeInterval k) : ℝ := densityParameter S.density

def reindex (S : APFreeInterval k) (a q len : ℕ) (hq : 0 < q) (hlen : 1 < len)
    (hpos : 0 < intervalDensity len (progressionPreimage S.points a q len)) : APFreeInterval k where
  length := len
  length_gt_one := hlen
  points := progressionPreimage S.points a q len
  subset := progressionPreimage_subset _ _ _ _
  nonempty := (intervalDensity_pos_iff (by omega)).mp hpos
  free := S.free.progressionPreimage a q len hq

end APFreeInterval

end Erdos3

end

section

namespace Erdos3

namespace APFreeInterval

end APFreeInterval
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntervalIntegerVectorAPFree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace APFreeInterval

noncomputable def integerIndicator {k : ℕ} (S : APFreeInterval k) (x : Unit → ℤ) : ℝ :=
  intervalIndicator S.points (x ()).toNat

@[simp] theorem integerIndicator_nat {k : ℕ} (S : APFreeInterval k) (n : ℕ) :
    S.integerIndicator (fun _ => (n : ℤ)) = intervalIndicator S.points n := by
  simp [integerIndicator]

end APFreeInterval

end Erdos3

end

end OAI

end


