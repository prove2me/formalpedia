-- Prove2me | Definitions.Def_OAIErdos3B027
-- name    : OAIErdos3B027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T18:39:16.157863+00:00
-- url     : https://prove2.me/theorems/2edead75-d96b-4deb-b538-1566a2ef67b4
-- title:
--   OpenAI Erdős-3 split, definitions bundle 28 of 106
-- statement:
--   Definitions bundle 28 of 106 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B026`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 28 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.FirstCoefficientIndex`, `OAI.Erdos3.NilpotentLieFiltration.FirstCoefficientModule`, `OAI.Erdos3.NilpotentLieFiltration.QuotientTopBasisIndex`, `OAI.Erdos3.NilpotentLieFiltration.QuotientTopSymbolIndex`, `OAI.Erdos3.NilpotentLieFiltration.RealFirstCoefficientModule`, `OAI.Erdos3.NilpotentLieFiltration.ReducedSquareBasisIndex`, `OAI.Erdos3.NilpotentLieFiltration.ReducedSquareSymbolIndex`, `OAI.Erdos3.NilpotentLieFiltration.adaptedAdjointConstant_sub_mem`, `OAI.Erdos3.NilpotentLieFiltration.adaptedLogDerivative_eq_formal`, `OAI.Erdos3.NilpotentLieFiltration.adaptedLogDerivative_sub_mem`, `OAI.Erdos3.NilpotentLieFiltration.adaptedSquareBasis`, `OAI.Erdos3.NilpotentLieFiltration.adaptedSquareBasis_inl`, `OAI.Erdos3.NilpotentLieFiltration.adaptedSquareBasis_inr`, `OAI.Erdos3.NilpotentLieFiltration.adaptedSquareBasis_layers`, `OAI.Erdos3.NilpotentLieFiltration.adaptedSquareBasis_pairMap_height`, `OAI.Erdos3.NilpotentLieFiltration.adaptedSquareBasis_structure_bound`, `OAI.Erdos3.NilpotentLieFiltration.card_squareBasis_index_le`, `OAI.Erdos3.NilpotentLieFiltration.exists_adaptedSquareBasis_grid`, `OAI.Erdos3.NilpotentLieFiltration.exists_real_adapted_log_derivative_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_sorted_firstCoefficient_rows`, `OAI.Erdos3.NilpotentLieFiltration.fastCoefficientMatrixParameter`, `OAI.Erdos3.NilpotentLieFiltration.fastCoefficientMatrixParameter_nonneg`, `OAI.Erdos3.NilpotentLieFiltration.fastCoefficient_matrix_dimensions`, `OAI.Erdos3.NilpotentLieFiltration.filteredFirstJet_logDerivative_eq`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientBasis`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientBasis_repr_map`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientConstant`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientFastSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientFastSubmodule_eq_image`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientFastSubmodule_le_horizontal_ker`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientHorizontal`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientHorizontalSection`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientHorizontalSection_mk`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientHorizontal_constant`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientHorizontal_map`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientHorizontal_section`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientIndexEmbedding`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientIndexFintype`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientIndex_card_le`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientIndex_grade_pos`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientIndex_zero_iff_grade_one`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientMap`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientMap_eq_zero_iff`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientMap_surjective`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientRealEquiv`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientRealEquiv_map`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientRelativeEquiv`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientRelativeEquiv_apply`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientRelativeMap`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientRelativeMap_coefficientMap`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientRelativeRangeEquiv`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientRelativeRangeEquiv_apply`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientSurvivorEquiv`, `OAI.Erdos3.NilpotentLieFiltration.le_fastCoefficientMatrixParameter`, `OAI.Erdos3.NilpotentLieFiltration.le_reducedMatrixParameter`, `OAI.Erdos3.NilpotentLieFiltration.mem_squareLayer_iff_second_and_difference`, `OAI.Erdos3.NilpotentLieFiltration.normalizedFirstCoefficientMap`, `OAI.Erdos3.NilpotentLieFiltration.normalizedFirstCoefficientMap_eq_zero_iff`, `OAI.Erdos3.NilpotentLieFiltration.normalizedFirstCoefficientMap_ker`, `OAI.Erdos3.NilpotentLieFiltration.normalizedFirstCoefficientMap_mem_fast_iff`, `OAI.Erdos3.NilpotentLieFiltration.normalizedFirstCoefficientMap_range`, `OAI.Erdos3.NilpotentLieFiltration.normalizedRelativeLog_horizontal`, `OAI.Erdos3.NilpotentLieFiltration.normalizedRelativeLog_mem`, `OAI.Erdos3.NilpotentLieFiltration.normalizedRelativeLog_shifted`, `OAI.Erdos3.NilpotentLieFiltration.quotientGradedMap`, `OAI.Erdos3.NilpotentLieFiltration.quotientGradedMap_piece`, `OAI.Erdos3.NilpotentLieFiltration.quotientGradedMap_piece_eq_zero_iff`, `OAI.Erdos3.NilpotentLieFiltration.quotientLie_mem_iff`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopBasis`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopBasis_apply`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopBasis_layers`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopBasis_repr_mk`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopGradedMap`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopGradedMap_piece_eq_zero_iff`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopSymbolBasis`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopSymbolIndex_card_le`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopSymbolIndex_finite`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedAdjoint_eq_formal`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedDirectionalDerivative`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedDirectionalDerivative_bound`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedDirectionalDerivative_mem_first`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedDirectionalDerivative_polynomial`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedDirectionalDerivative_tensor`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedDirectionalTangent`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedLogDerivative`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedLogDerivative_eq_formal`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedLogDerivative_mem_first`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedLogDerivative_tensor`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialJet`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialJet_base`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialJet_tangent`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientAdjoint`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientAdjoint_map`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientBasis`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientBasis_apply`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientBasis_polynomial_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientBasis_repr_map`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientDirectionMap`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientDirectionMap_rat`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientHorizontal`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientHorizontalSection`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientHorizontal_section`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientMap`, `OAI.Erdos3.NilpotentLieFiltration.realFullPolynomialHom`, `OAI.Erdos3.NilpotentLieFiltration.realFullPolynomialHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.realFullPolynomialLie`, `OAI.Erdos3.NilpotentLieFiltration.realFullPolynomialLie_apply`, `OAI.Erdos3.NilpotentLieFiltration.realLogDerivativeDirectionMap`, `OAI.Erdos3.NilpotentLieFiltration.realLogDerivativeDirectionMap_mem_first`, `OAI.Erdos3.NilpotentLieFiltration.realLogDerivativeDirectionMap_rat`, `OAI.Erdos3.NilpotentLieFiltration.realNormalizedFirstCoefficientMap`, `OAI.Erdos3.NilpotentLieFiltration.realNormalizedFirstCoefficientMap_range`, `OAI.Erdos3.NilpotentLieFiltration.realShiftedCoefficientSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.realShiftedCoefficient_eq_span`, `OAI.Erdos3.NilpotentLieFiltration.realShiftedCoefficient_lie_mem`, `OAI.Erdos3.NilpotentLieFiltration.realShiftedCoefficient_next_eq_span`, `OAI.Erdos3.NilpotentLieFiltration.realShiftedMonomialBasis`, `OAI.Erdos3.NilpotentLieFiltration.realShiftedMonomialBasis_coe`, `OAI.Erdos3.NilpotentLieFiltration.realShiftedMonomialBasis_repr`, `OAI.Erdos3.NilpotentLieFiltration.reducedMatrixParameter`, `OAI.Erdos3.NilpotentLieFiltration.reducedMatrixParameter_nonneg`, `OAI.Erdos3.NilpotentLieFiltration.reducedRelativeSquareSymbolMap`, `OAI.Erdos3.NilpotentLieFiltration.reducedRelativeSquareSymbolMap_apply`, `OAI.Erdos3.NilpotentLieFiltration.reducedRelativeSquareSymbolMap_eq_zero_iff`, `OAI.Erdos3.NilpotentLieFiltration.reducedRelativeSquareSymbolMap_projection`, `OAI.Erdos3.NilpotentLieFiltration.reducedRelativeSquareSymbolMap_range`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareBasis`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareBasis_layers`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareCoefficientMap`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareCoefficientMap_basis_height`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareCoefficientMap_basis_repr`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareCoefficientMap_horizontal`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareCoefficientMap_monomial_blocks`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareCoefficientMap_relative`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareCoefficientMap_relativeMap`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareCoefficientMap_repr_symbol`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareCoefficientMap_symbol`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonal`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonalPolynomialMap`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonalPolynomialMap_quotient`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonalSymbolHom`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonalSymbolMap`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonalSymbolMap_quotient`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonalSymbolMap_symbol`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonal_mem`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDiagonal_mk`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDifference`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDifferenceAdapted`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDifferenceRelative`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDifferenceRelative_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDifferenceRelative_relative`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDifference_basis_height`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDifference_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDifference_mem_two`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareDifference_mk`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedDiagonalPiece`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedDiagonalPiece_eq_zero_iff`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedRelativePiece`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquarePolynomialMap`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRelativeGroupPart`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareRelativeGroupPart_projection`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSnd`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndPolynomialMap`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndPolynomialMap_diagonal`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndPolynomialMap_quotient`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndSymbolHom`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndSymbolHom_diagonal`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndSymbolKernel_lie_eq_zero`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndSymbolKernel_lift`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndSymbolMap`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndSymbolMap_basis_height`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndSymbolMap_diagonal`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndSymbolMap_monomial_blocks`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndSymbolMap_quotient`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSndSymbolMap_symbol`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSnd_basis_height`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSnd_diagonal`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSnd_mem`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSnd_mk`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSymbolBasis`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSymbolIndex_card_le`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSymbolIndex_finite`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSymbolMap`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSymbolMap_surjective`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareSymbolMap_symbol`, `OAI.Erdos3.NilpotentLieFiltration.reduced_lift_matrix_dimensions`, `OAI.Erdos3.NilpotentLieFiltration.sorted_firstCoefficient_scale_bounds`, `OAI.Erdos3.NilpotentLieFiltration.squareBasis`, `OAI.Erdos3.NilpotentLieFiltration.squareBasisWeight`, `OAI.Erdos3.NilpotentLieFiltration.squareBasis_inl`, `OAI.Erdos3.NilpotentLieFiltration.squareBasis_inr`, `OAI.Erdos3.NilpotentLieFiltration.squareBasis_repr_inl`, `OAI.Erdos3.NilpotentLieFiltration.squareBasis_repr_inr`, `OAI.Erdos3.NilpotentLieFiltration.squareCoordinates`, `OAI.Erdos3.NilpotentLieFiltration.squareLattice_eq_pair_comap`, `OAI.Erdos3.NilpotentLieFiltration.squarePairMap`, `OAI.Erdos3.NilpotentLieFiltration.squarePairMap_false`, `OAI.Erdos3.NilpotentLieFiltration.squarePairMap_injective`, `OAI.Erdos3.NilpotentLieFiltration.squarePairMap_true`, `OAI.Erdos3.NilpotentLieFiltration.symbolAdjointConstant`, `OAI.Erdos3.NilpotentLieFiltration.symbolAdjointConstant_map`, `OAI.Erdos3.NilpotentLieFiltration.symbolLogDerivative`, `OAI.Erdos3.NilpotentLieFiltration.symbolLogDerivative_map`, `OAI.Erdos3.VectorPolynomial.directionalDerivative_single`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B097

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedSquareSymbol
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

theorem quotientLie_mem_iff (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
    (j : ℕ) (x : L) :
    lieQuotientMap I x ∈ (F.quotientLie I hI).layer j ↔ x ∈ F.layer j ⊔ I.toSubmodule := by
  change x ∈ ((F.layer j).map I.toSubmodule.mkQ).comap I.toSubmodule.mkQ ↔ _
  rw [Submodule.comap_map_mkQ, sup_comm]

noncomputable def quotientGradedMap (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule) :
    F.AssociatedGraded →ₗ⁅ℚ⁆ (F.quotientLie I hI).AssociatedGraded :=
  F.associatedGradedMap (F.quotientLie I hI) (lieQuotientMap I)
    (fun _ _ hx => F.quotientLie_mem I hI hx)

@[simp] theorem quotientGradedMap_piece (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
    (j : ℕ) (x : F.layer j) :
    F.quotientGradedMap I hI (F.associatedGradedPieceMap j x) =
      (F.quotientLie I hI).associatedGradedPieceMap j
        ⟨lieQuotientMap I x, F.quotientLie_mem I hI x.property⟩ :=
  F.associatedGradedMap_piece _ _ _ j x

theorem quotientGradedMap_piece_eq_zero_iff (I : LieIdeal ℚ L)
    (hI : F.layer (t + 1) ≤ I.toSubmodule) (j : ℕ) (x : F.layer j) :
    F.quotientGradedMap I hI (F.associatedGradedPieceMap j x) = 0 ↔
      (x : L) ∈ F.layer (j + 1) ⊔ I.toSubmodule := by
  rw [F.quotientGradedMap_piece, associatedGradedPieceMap_eq_zero_iff,
    F.quotientLie_mem_iff]

variable (F : NilpotentLieFiltration L (s + 1))

noncomputable def quotientTopGradedMap : F.AssociatedGraded →ₗ⁅ℚ⁆ F.quotientTop.AssociatedGraded :=
  F.quotientGradedMap (F.layerIdeal (s + 1)) le_rfl

theorem quotientTopGradedMap_piece_eq_zero_iff (j : ℕ) (hj : j ≤ s) (x : F.layer j) :
    F.quotientTopGradedMap (F.associatedGradedPieceMap j x) = 0 ↔ (x : L) ∈ F.layer (j + 1) := by
  have hle : (F.layerIdeal (s + 1)).toSubmodule ≤ F.layer (j + 1) :=
    F.antitone (Nat.add_le_add_right hj 1)
  have h := F.quotientGradedMap_piece_eq_zero_iff (F.layerIdeal (s + 1)) (t := s) le_rfl j x
  rw [sup_eq_left.mpr hle] at h
  convert h using 1
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

variable (h : σ → ℚ) (e m : L)
  (p : F.adaptedLieSubalgebra (fun _ : σ => 1))

theorem normalizedRelativeLog_shifted :
    F.normalizedRelativeLog h e m p ∈ F.shiftedAdaptedIdeal (fun _ : σ => 1) := by
  apply (F.polynomialSymbolMap_eq_zero_iff (fun _ => 1) _).mp
  change F.polynomialSymbolMap (fun _ => 1)
    (lieBCH s (F.normalizedShiftAdapted h (-e) (-m) p) (-p)) = 0
  rw [map_lieBCH, map_neg]
  have he : F.polynomialSymbolMap (fun _ => 1) (F.normalizedShiftAdapted h (-e) (-m) p) =
      F.polynomialSymbolMap (fun _ => 1) p := by
    apply (F.polynomialSymbolMap_eq_iff (fun _ => 1) _ _).mpr
    exact F.normalizedShiftLog_sub_coefficient_mem (fun _ => 1) (by simp) h (-e) (-m)
      ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property)
  rw [he]
  exact congrArg NilpotentLieBCHGroup.coord
    (mul_inv_cancel (⟨F.polynomialSymbolMap (fun _ => 1) p⟩ :
      F.PolynomialSymbolGroup (fun _ : σ => 1)))

theorem normalizedRelativeLog_horizontal
    (hzero : coefficients (normalizedShiftLog s h (-e) (-m) p.val - p.val) 0 ∈ F.layer 2) :
    coefficients (F.normalizedRelativeLog h e m p).val 0 ∈ F.layer 2 := by
  apply (lieQuotientMap_eq_zero (F.layerIdeal 2) _).mp
  rw [← eval_zero_eq_coefficient]
  change lieQuotientMap (F.layerIdeal 2)
    (eval (0 : σ → ℚ) ((F.adaptedLieSubalgebra (fun _ => 1)).incl
      (lieBCH s (F.normalizedShiftAdapted h (-e) (-m) p) (-p)))) = 0
  rw [map_lieBCH, eval_lieBCH, F.horizontal_bch, map_neg, map_neg, map_neg]
  have hz := (lieQuotientMap_eq_zero (F.layerIdeal 2) _).mpr hzero
  rw [← eval_zero_eq_coefficient, map_sub, map_sub] at hz
  rw [sub_eq_add_neg] at hz
  exact hz

theorem normalizedRelativeLog_mem
    (hzero : coefficients (normalizedShiftLog s h (-e) (-m) p.val - p.val) 0 ∈ F.layer 2) :
    F.normalizedRelativeLog h e m p ∈ F.normalizedRelativeSubmodule (fun _ : σ => 1) :=
  ⟨F.normalizedRelativeLog_shifted h e m p, F.normalizedRelativeLog_horizontal h e m p hzero⟩

variable [Fintype σ]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def reducedSquareGradedDiagonalPiece (j : ℕ) :
    F.layer j →ₗ[ℚ] F.squareFiltration.quotientTop.AssociatedGraded :=
  F.squareFiltration.quotientTopGradedMap.toLinearMap.comp (F.squareGradedDiagonalPiece j)

noncomputable def reducedSquareGradedRelativePiece (j : ℕ) (hj : 1 ≤ j) :
    F.layer (j + 1) →ₗ[ℚ] F.squareFiltration.quotientTop.AssociatedGraded :=
  F.squareFiltration.quotientTopGradedMap.toLinearMap.comp (F.squareGradedRelativePiece j hj)

theorem reducedSquareGradedDiagonalPiece_eq_zero_iff (j : ℕ) (hj : j ≤ s) (x : F.layer j) :
    F.reducedSquareGradedDiagonalPiece j x = 0 ↔ (x : L) ∈ F.layer (j + 1) := by
  change F.squareFiltration.quotientTopGradedMap
    (F.squareFiltration.associatedGradedPieceMap j (F.squareDiagonalLayer j x)) = 0 ↔ _
  rw [F.squareFiltration.quotientTopGradedMap_piece_eq_zero_iff j hj]
  exact (F.squareFiltration.associatedGradedPieceMap_eq_zero_iff j _).symm.trans
    (F.squareGradedDiagonalPiece_eq_zero_iff j x)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

variable [Fintype σ] (h : σ → ℚ) (e m : L)
  (p : F.adaptedLieSubalgebra (fun _ : σ => 1))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

theorem adaptedLogDerivative_sub_mem {p q : F.adaptedLieSubalgebra (fun _ : σ => 1)}
    (hpq : F.polynomialSymbolMap (fun _ => 1) p = F.polynomialSymbolMap (fun _ => 1) q) :
    F.adaptedLogDerivative h p - F.adaptedLogDerivative h q ∈
      F.shiftedPolynomialIdeal (fun _ : σ => 1) 2 := by
  have hd : p - q ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1 :=
    (F.polynomialSymbolMap_eq_iff (fun _ => 1) p q).mp hpq
  have hbracket : ∀ x ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1,
      ∀ y ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1,
        ⁅x, y⁆ ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 2 := by
    intro x hx y hy
    exact F.shiftedPolynomialIdeal_lie_mem (fun _ => 1) (i := 1) (j := 1) hx hy
  apply dualLogDerivative_sub_mem _ _ hbracket
    (F.adaptedPolynomialJet h p) (F.adaptedPolynomialJet h q)
  · rw [F.adaptedPolynomialJet_tangent]
    exact F.directionalDerivative_mem_next h p
  · rw [F.adaptedPolynomialJet_tangent]
    exact F.directionalDerivative_mem_next h q
  · constructor
    · simpa only [map_sub, F.adaptedPolynomialJet_base] using hd
    · have ht := F.adaptedDirectionalDerivative_mem_shifted h 1 hd
      rw [map_sub] at ht
      simpa only [map_sub, F.adaptedPolynomialJet_tangent] using ht

omit [Fintype σ] in
theorem adaptedAdjointConstant_sub_mem {p q : F.adaptedLieSubalgebra (fun _ : σ => 1)}
    (hpq : F.polynomialSymbolMap (fun _ => 1) p = F.polynomialSymbolMap (fun _ => 1) q)
    {m n : L} (hmn : m - n ∈ F.layer 2) :
    dualAdjoint (⟨p⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (F.adaptedConstant (fun _ => 1) m) -
      dualAdjoint (⟨q⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (F.adaptedConstant (fun _ => 1) n) ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 2 := by
  have hd : p - q ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1 :=
    (F.polynomialSymbolMap_eq_iff (fun _ => 1) p q).mp hpq
  have hbracket : ∀ x ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1,
      ∀ y ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1,
        ⁅x, y⁆ ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 2 := by
    intro x hx y hy
    exact F.shiftedPolynomialIdeal_lie_mem (fun _ => 1) (i := 1) (j := 1) hx hy
  apply dualAdjoint_sub_mem _ _ hbracket _ _ _ _
    (F.adaptedConstant_mem_shiftedIdeal (fun _ => 1) m)
    (F.adaptedConstant_mem_shiftedIdeal (fun _ => 1) n) hd
  change F.adaptedConstantLieHom (fun _ : σ => 1) m - F.adaptedConstantLieHom (fun _ => 1) n ∈ _
  rw [← map_sub]
  exact F.adaptedConstant_mem_shiftedPolynomialIdeal (fun _ => 1) 2 hmn

theorem filteredFirstJet_logDerivative_eq {p q : F.adaptedLieSubalgebra (fun _ : σ => 1)}
    (hpq : F.polynomialSymbolMap (fun _ => 1) p = F.polynomialSymbolMap (fun _ => 1) q) :
    F.filteredFirstJetMap (fun _ => 1) (F.adaptedLogDerivative h p) =
      F.filteredFirstJetMap (fun _ => 1) (F.adaptedLogDerivative h q) := by
  rw [← sub_eq_zero, ← map_sub]
  exact (F.filteredFirstJetMap_eq_zero_iff (fun _ => 1) _).mpr (F.adaptedLogDerivative_sub_mem h hpq)

noncomputable def symbolLogDerivative (x : F.PolynomialSymbol (fun _ : σ => 1)) :
    F.FilteredFirstJet (fun _ : σ => 1) :=
  F.filteredFirstJetMap (fun _ => 1)
    (F.adaptedLogDerivative h (Classical.choose (F.polynomialSymbolMap_surjective (fun _ => 1) x)))

@[simp] theorem symbolLogDerivative_map (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.symbolLogDerivative h (F.polynomialSymbolMap (fun _ => 1) p) =
      F.filteredFirstJetMap (fun _ => 1) (F.adaptedLogDerivative h p) :=
  F.filteredFirstJet_logDerivative_eq h (Classical.choose_spec
    (F.polynomialSymbolMap_surjective (fun _ => 1) (F.polynomialSymbolMap (fun _ => 1) p)))

noncomputable def symbolAdjointConstant (x : F.PolynomialSymbol (fun _ : σ => 1)) (m : L) :
    F.FilteredFirstJet (fun _ : σ => 1) :=
  F.filteredFirstJetMap (fun _ => 1)
    (dualAdjoint (⟨Classical.choose (F.polynomialSymbolMap_surjective (fun _ => 1) x)⟩ :
      (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) (F.adaptedConstant (fun _ => 1) m))

omit [Fintype σ] in
@[simp] theorem symbolAdjointConstant_map (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) (m : L) :
    F.symbolAdjointConstant (F.polynomialSymbolMap (fun _ => 1) p) m =
      F.filteredFirstJetMap (fun _ => 1)
        (dualAdjoint (⟨p⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
          (F.adaptedConstant (fun _ => 1) m)) := by
  change F.filteredFirstJetMap (fun _ => 1) _ = F.filteredFirstJetMap (fun _ => 1) _
  rw [← sub_eq_zero, ← map_sub]
  apply (F.filteredFirstJetMap_eq_zero_iff (fun _ => 1) _).mpr
  exact F.adaptedAdjointConstant_sub_mem (Classical.choose_spec
    (F.polynomialSymbolMap_surjective (fun _ => 1) (F.polynomialSymbolMap (fun _ => 1) p))) (by simp)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def reducedSquarePolynomialMap :
    F.squareFiltration.adaptedLieSubalgebra w →ₗ⁅ℚ⁆
      F.squareFiltration.quotientTop.adaptedLieSubalgebra w :=
  F.squareFiltration.filteredPolynomialMap F.squareFiltration.quotientTop
    (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)))
    (fun _ _ hx => F.squareFiltration.quotientLie_mem _ le_rfl hx) w

noncomputable def reducedSquareSymbolMap :
    F.squareFiltration.PolynomialSymbol w →ₗ⁅ℚ⁆ F.squareFiltration.quotientTop.PolynomialSymbol w :=
  F.squareFiltration.filteredPolynomialSymbolMap F.squareFiltration.quotientTop
    (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)))
    (fun _ _ hx => F.squareFiltration.quotientLie_mem _ le_rfl hx) w

@[simp] theorem reducedSquareSymbolMap_symbol (r : F.squareFiltration.adaptedLieSubalgebra w) :
    F.reducedSquareSymbolMap w (F.squareFiltration.polynomialSymbolMap w r) =
      F.squareFiltration.quotientTop.polynomialSymbolMap w (F.reducedSquarePolynomialMap w r) := rfl

variable [Fintype σ] (h : σ → ℚ) (e m : L)
  (p : F.adaptedLieSubalgebra (fun _ : σ => 1))

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareBasisGeometry
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squareCoordinates : F.squareLieSubalgebra ≃ₗ[ℚ] L × F.layer 2 where
  toFun x := (x.val.2, ⟨x.val.1 - x.val.2, (F.mem_squareLieSubalgebra x.val).mp x.property⟩)
  invFun x := ⟨(x.1 + x.2, x.1), (F.mem_squareLieSubalgebra _).mpr (by
    change x.1 + (x.2 : L) - x.1 ∈ F.layer 2
    rw [add_sub_cancel_left]
    exact x.2.property)⟩
  left_inv x := by apply Subtype.ext; apply Prod.ext <;> simp
  right_inv x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext; simp
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext; dsimp; abel
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext; exact (smul_sub r _ _).symm

noncomputable def squareBasis (b : Basis ι ℚ L) (c : Basis κ ℚ (F.layer 2)) :
    Basis (ι ⊕ κ) ℚ F.squareLieSubalgebra :=
  (b.prod c).map F.squareCoordinates.symm

@[simp] theorem squareBasis_inl (b : Basis ι ℚ L) (c : Basis κ ℚ (F.layer 2)) (i : ι) :
    (F.squareBasis b c (Sum.inl i)).val = (b i, b i) := by
  simp [squareBasis, Basis.map_apply, squareCoordinates]

@[simp] theorem squareBasis_inr (b : Basis ι ℚ L) (c : Basis κ ℚ (F.layer 2)) (i : κ) :
    (F.squareBasis b c (Sum.inr i)).val = ((c i : L), 0) := by
  simp [squareBasis, Basis.map_apply, squareCoordinates]

theorem squareBasis_repr_inl (b : Basis ι ℚ L) (c : Basis κ ℚ (F.layer 2))
    (x : F.squareLieSubalgebra) (i : ι) :
    (F.squareBasis b c).repr x (Sum.inl i) = b.repr x.val.2 i := by
  simp [squareBasis, Basis.map_repr, squareCoordinates]

theorem squareBasis_repr_inr (b : Basis ι ℚ L) (c : Basis κ ℚ (F.layer 2))
    (x : F.squareLieSubalgebra) (i : κ) :
    (F.squareBasis b c).repr x (Sum.inr i) =
      c.repr ⟨x.val.1 - x.val.2, (F.mem_squareLieSubalgebra x.val).mp x.property⟩ i := by
  simp [squareBasis, Basis.map_repr, squareCoordinates]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem mem_squareLayer_iff_second_and_difference (j : ℕ) (x : L × L) :
    x ∈ F.squareLayer j ↔ x.2 ∈ F.layer j ∧ x.1 - x.2 ∈ F.layer (j + 1) := by
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h.1, h.2⟩
    have hx := (F.layer j).add_mem (F.antitone (Nat.le_succ j) h.2) h.1
    simpa only [sub_add_cancel] using hx

noncomputable def adaptedSquareBasis (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i})) :
    Basis (ι ⊕ {i // 2 ≤ w i}) ℚ F.squareLieSubalgebra :=
  F.squareBasis b (supportedSubmoduleBasis b (F.layer 2) {i | 2 ≤ w i} h)

@[simp] theorem adaptedSquareBasis_inl (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i})) (i : ι) :
    (F.adaptedSquareBasis b w h (Sum.inl i)).val = (b i, b i) :=
  F.squareBasis_inl b _ i

@[simp] theorem adaptedSquareBasis_inr (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i})) (i : {i // 2 ≤ w i}) :
    (F.adaptedSquareBasis b w h (Sum.inr i)).val = (b i, 0) := by
  simp only [adaptedSquareBasis, F.squareBasis_inr]
  apply Prod.ext
  · exact supportedSubmoduleBasis_coe b (F.layer 2) {i | 2 ≤ w i} h i
  · rfl

def squareBasisWeight (w : ι → ℕ) : (ι ⊕ {i // 2 ≤ w i}) → ℕ :=
  Sum.elim w (fun i => w i - 1)

theorem adaptedSquareBasis_layers (b : Basis ι ℚ L) (w : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) (j : ℕ) :
    F.squareFiltration.layer j = Submodule.span ℚ
      (F.adaptedSquareBasis b w (hlayers 2) '' {i | j ≤ squareBasisWeight w i}) := by
  have hmem (k : ℕ) (x : L) : x ∈ F.layer k ↔ ∀ i, ¬ k ≤ w i → b.repr x i = 0 := by
    rw [hlayers k, basis_mem_span_image_iff]
    rfl
  ext x
  rw [F.mem_squareFiltration_layer, F.mem_squareLayer_iff_second_and_difference,
    basis_mem_span_image_iff, hmem, hmem]
  constructor
  · rintro ⟨hy, hz⟩ i hi
    cases i with
    | inl i =>
      change (F.squareBasis b _).repr x (Sum.inl i) = 0
      rw [F.squareBasis_repr_inl]
      exact hy i hi
    | inr i =>
      change (F.squareBasis b _).repr x (Sum.inr i) = 0
      rw [F.squareBasis_repr_inr, supportedSubmoduleBasis_repr]
      exact hz i (by change ¬ j ≤ w i - 1 at hi; have := i.property; omega)
  · intro hx
    constructor
    · intro i hi
      have hh := hx (Sum.inl i) hi
      change (F.squareBasis b _).repr x (Sum.inl i) = 0 at hh
      simpa only [F.squareBasis_repr_inl] using hh
    · intro i hi
      by_cases h2 : 2 ≤ w i
      · have hsmall : ¬ j ≤ squareBasisWeight w (Sum.inr (⟨i, h2⟩ : {i // 2 ≤ w i})) := by
          change ¬ j ≤ w i - 1
          omega
        have hh := hx (Sum.inr ⟨i, h2⟩) hsmall
        change (F.squareBasis b _).repr x
          (Sum.inr (⟨i, h2⟩ : {i // 2 ≤ w i})) = 0 at hh
        rw [F.squareBasis_repr_inr] at hh
        exact (supportedSubmoduleBasis_repr b (F.layer 2) {i | 2 ≤ w i}
          (hlayers 2) _ (⟨i, h2⟩ : {i // 2 ≤ w i})).symm.trans hh
      · exact (hmem 2 (x.val.1 - x.val.2)).mp
          ((F.mem_squareLieSubalgebra x.val).mp x.property) i h2

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev QuotientTopBasisIndex (s : ℕ) (ω : ι → ℕ) := {i : ι // ¬ s + 1 ≤ ω i}

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def quotientTopBasis :
    Basis (QuotientTopBasisIndex s ω) ℚ (L ⧸ F.layerIdeal (s + 1)) :=
  supportedQuotientBasis e (F.layerIdeal (s + 1)).toSubmodule {i | s + 1 ≤ ω i} (hF (s + 1))

@[simp] theorem quotientTopBasis_apply (i : QuotientTopBasisIndex s ω) :
    F.quotientTopBasis e ω hF i = lieQuotientMap (F.layerIdeal (s + 1)) (e i.val) :=
  supportedQuotientBasis_apply e _ _ _ i

theorem quotientTopBasis_repr_mk (x : L) (i : QuotientTopBasisIndex s ω) :
    (F.quotientTopBasis e ω hF).repr (lieQuotientMap (F.layerIdeal (s + 1)) x) i = e.repr x i.val :=
  supportedQuotientBasis_repr_mk e _ _ _ x i

theorem quotientTopBasis_layers (j : ℕ) :
    F.quotientTop.layer j = Submodule.span ℚ
      (F.quotientTopBasis e ω hF '' {i | j ≤ ω i.val}) :=
  F.supportedQuotientBasis_layers e ω hF (F.layerIdeal (s + 1)) le_rfl
    {i | s + 1 ≤ ω i} (hF (s + 1)) j

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def reducedSquareSnd :
    (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ⁅ℚ⁆
      (L ⧸ F.layerIdeal (s + 1)) :=
  lieQuotientDescend (F.squareFiltration.layerIdeal (s + 1))
    ((lieQuotientMap (F.layerIdeal (s + 1))).comp F.squareSnd) (by
      intro x hx
      exact (lieQuotientMap_eq_zero _ _).mpr hx.2.1)

noncomputable def reducedSquareDiagonal :
    (L ⧸ F.layerIdeal (s + 1)) →ₗ⁅ℚ⁆
      (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) :=
  lieQuotientDescend (F.layerIdeal (s + 1))
    ((lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).comp F.squareDiagonalLie) (by
      intro x hx
      apply (lieQuotientMap_eq_zero _ _).mpr
      exact ⟨hx, hx, by change x - x ∈ F.layer (s + 1 + 1); simp⟩)

@[simp] theorem reducedSquareSnd_mk (x : F.squareLieSubalgebra) :
    F.reducedSquareSnd (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) x) =
      lieQuotientMap (F.layerIdeal (s + 1)) (F.squareSnd x) := rfl

@[simp] theorem reducedSquareDiagonal_mk (x : L) :
    F.reducedSquareDiagonal (lieQuotientMap (F.layerIdeal (s + 1)) x) =
      lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) (F.squareDiagonalLie x) := rfl

@[simp] theorem reducedSquareSnd_diagonal (x : L ⧸ F.layerIdeal (s + 1)) :
    F.reducedSquareSnd (F.reducedSquareDiagonal x) = x := by
  obtain ⟨a, rfl⟩ := lieQuotientMap_surjective (F.layerIdeal (s + 1)) x
  rfl

theorem reducedSquareSnd_mem (j : ℕ)
    (x : F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1))
    (hx : x ∈ F.squareFiltration.quotientTop.layer j) :
    F.reducedSquareSnd x ∈ F.quotientTop.layer j := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact F.quotientLie_mem _ le_rfl ha.2.1

theorem reducedSquareDiagonal_mem (j : ℕ) (x : L ⧸ F.layerIdeal (s + 1))
    (hx : x ∈ F.quotientTop.layer j) :
    F.reducedSquareDiagonal x ∈ F.squareFiltration.quotientTop.layer j := by
  obtain ⟨a, ha, rfl⟩ := hx
  apply F.squareFiltration.quotientLie_mem _ le_rfl
  exact ⟨ha, ha, by change a - a ∈ F.layer (j + 1); simp⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squarePairMap : F.squareLieSubalgebra →ₗ⁅ℚ⁆ (Bool → L) :=
  liePiMap (fun i : Bool => cond i F.squareFst F.squareSnd)

@[simp] theorem squarePairMap_false (x : F.squareLieSubalgebra) : F.squarePairMap x false = x.val.2 := rfl
@[simp] theorem squarePairMap_true (x : F.squareLieSubalgebra) : F.squarePairMap x true = x.val.1 := rfl

theorem squarePairMap_injective : Function.Injective F.squarePairMap := by
  intro x y h
  apply Subtype.ext
  exact Prod.ext (congrFun h true) (congrFun h false)

theorem squareLattice_eq_pair_comap (Γ : Subgroup F.Group) :
    F.squareLattice Γ =
      (piBCHSubgroup (fun _ : Bool => F) (fun _ => Γ)).comap
        (map (hnil := F.squareFiltration.lowerCentralSeries_eq_bot)
          (hM := (pi (fun _ : Bool => F)).lowerCentralSeries_eq_bot) F.squarePairMap) := by
  ext g
  rw [F.mem_squareLattice, Subgroup.mem_comap, mem_piBCHSubgroup]
  constructor
  · intro h i
    cases i
    · exact h.2
    · exact h.1
  · intro h
    exact ⟨h true, h false⟩

variable [Fintype ι]

theorem card_squareBasis_index_le (w : ι → ℕ) :
    Fintype.card (ι ⊕ {i // 2 ≤ w i}) ≤ 2 * Fintype.card ι := by
  rw [Fintype.card_sum]
  have h := Fintype.card_subtype_le (fun i => 2 ≤ w i)
  omega

omit [Fintype ι] in

theorem adaptedSquareBasis_pairMap_height (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    (k : Σ _ : Bool, ι) (j : ι ⊕ {i // 2 ≤ w i}) :
    RationalHeightLE ((Pi.basis (fun _ : Bool => b)).repr
      (F.squarePairMap (F.adaptedSquareBasis b w h j)) k) 1 := by
  rcases k with ⟨flag, i⟩
  rw [Pi.basis_repr]
  cases j with
  | inl j =>
    cases flag <;>
      simpa only [squarePairMap_false, squarePairMap_true, adaptedSquareBasis_inl] using
        basis_repr_height_one b j i
  | inr j =>
    cases flag
    · simp only [squarePairMap_false, adaptedSquareBasis_inr, map_zero, Finsupp.zero_apply]
      exact rationalHeightLE_zero le_rfl
    · simpa only [squarePairMap_true, adaptedSquareBasis_inr] using basis_repr_height_one b j i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def reducedSquareSndPolynomialMap :
    F.squareFiltration.quotientTop.adaptedLieSubalgebra w →ₗ⁅ℚ⁆
      F.quotientTop.adaptedLieSubalgebra w :=
  F.squareFiltration.quotientTop.filteredPolynomialMap F.quotientTop
    F.reducedSquareSnd F.reducedSquareSnd_mem w

noncomputable def reducedSquareDiagonalPolynomialMap :
    F.quotientTop.adaptedLieSubalgebra w →ₗ⁅ℚ⁆
      F.squareFiltration.quotientTop.adaptedLieSubalgebra w :=
  F.quotientTop.filteredPolynomialMap F.squareFiltration.quotientTop
    F.reducedSquareDiagonal F.reducedSquareDiagonal_mem w

noncomputable def reducedSquareSndSymbolMap :
    F.squareFiltration.quotientTop.PolynomialSymbol w →ₗ⁅ℚ⁆ F.quotientTop.PolynomialSymbol w :=
  F.squareFiltration.quotientTop.filteredPolynomialSymbolMap F.quotientTop
    F.reducedSquareSnd F.reducedSquareSnd_mem w

noncomputable def reducedSquareDiagonalSymbolMap :
    F.quotientTop.PolynomialSymbol w →ₗ⁅ℚ⁆ F.squareFiltration.quotientTop.PolynomialSymbol w :=
  F.quotientTop.filteredPolynomialSymbolMap F.squareFiltration.quotientTop
    F.reducedSquareDiagonal F.reducedSquareDiagonal_mem w

@[simp] theorem reducedSquareSndSymbolMap_symbol
    (r : F.squareFiltration.quotientTop.adaptedLieSubalgebra w) :
    F.reducedSquareSndSymbolMap w (F.squareFiltration.quotientTop.polynomialSymbolMap w r) =
      F.quotientTop.polynomialSymbolMap w (F.reducedSquareSndPolynomialMap w r) := rfl

@[simp] theorem reducedSquareDiagonalSymbolMap_symbol (p : F.quotientTop.adaptedLieSubalgebra w) :
    F.reducedSquareDiagonalSymbolMap w (F.quotientTop.polynomialSymbolMap w p) =
      F.squareFiltration.quotientTop.polynomialSymbolMap w (F.reducedSquareDiagonalPolynomialMap w p) := rfl

@[simp] theorem reducedSquareSndPolynomialMap_diagonal (p : F.quotientTop.adaptedLieSubalgebra w) :
    F.reducedSquareSndPolynomialMap w (F.reducedSquareDiagonalPolynomialMap w p) = p := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  simp only [reducedSquareSndPolynomialMap, reducedSquareDiagonalPolynomialMap,
    filteredPolynomialMap_coefficient, F.reducedSquareSnd_diagonal]

@[simp] theorem reducedSquareSndSymbolMap_diagonal (x : F.quotientTop.PolynomialSymbol w) :
    F.reducedSquareSndSymbolMap w (F.reducedSquareDiagonalSymbolMap w x) = x := by
  obtain ⟨p, rfl⟩ := F.quotientTop.polynomialSymbolMap_surjective w x
  rw [F.reducedSquareDiagonalSymbolMap_symbol, F.reducedSquareSndSymbolMap_symbol,
    F.reducedSquareSndPolynomialMap_diagonal]

theorem reducedSquareSndPolynomialMap_quotient (p : F.squareFiltration.adaptedLieSubalgebra w) :
    F.reducedSquareSndPolynomialMap w (F.reducedSquarePolynomialMap w p) =
      F.quotientTopPolynomialMap w (F.squareSndPolynomialMap w p) := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  change coefficients (VectorPolynomial.map F.reducedSquareSnd.toLinearMap
      (VectorPolynomial.map (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).toLinearMap p.val)) α =
    coefficients (VectorPolynomial.map (lieQuotientMap (F.layerIdeal (s + 1))).toLinearMap
      (VectorPolynomial.map F.squareSnd.toLinearMap p.val)) α
  simp only [coefficients_map]
  rfl

theorem reducedSquareDiagonalPolynomialMap_quotient (p : F.adaptedLieSubalgebra w) :
    F.reducedSquareDiagonalPolynomialMap w (F.quotientTopPolynomialMap w p) =
      F.reducedSquarePolynomialMap w (F.squareDiagonalPolynomialMap w p) := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  change coefficients (VectorPolynomial.map F.reducedSquareDiagonal.toLinearMap
      (VectorPolynomial.map (lieQuotientMap (F.layerIdeal (s + 1))).toLinearMap p.val)) α =
    coefficients (VectorPolynomial.map (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).toLinearMap
      (VectorPolynomial.map F.squareDiagonalLie.toLinearMap p.val)) α
  simp only [coefficients_map]
  rfl

theorem reducedSquareSndSymbolMap_quotient (x : F.squareFiltration.PolynomialSymbol w) :
    F.reducedSquareSndSymbolMap w (F.reducedSquareSymbolMap w x) =
      F.quotientTopSymbolMap w (F.squareSndSymbolMap w x) := by
  obtain ⟨p, rfl⟩ := F.squareFiltration.polynomialSymbolMap_surjective w x
  rw [F.reducedSquareSymbolMap_symbol, F.reducedSquareSndSymbolMap_symbol,
    F.squareSndSymbolMap_symbol, F.quotientTopSymbolMap_symbol,
    F.reducedSquareSndPolynomialMap_quotient]

theorem reducedSquareDiagonalSymbolMap_quotient (x : F.PolynomialSymbol w) :
    F.reducedSquareDiagonalSymbolMap w (F.quotientTopSymbolMap w x) =
      F.reducedSquareSymbolMap w (F.squareDiagonalSymbolMap w x) := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.quotientTopSymbolMap_symbol, F.reducedSquareDiagonalSymbolMap_symbol,
    F.squareDiagonalSymbolMap_symbol, F.reducedSquareSymbolMap_symbol,
    F.reducedSquareDiagonalPolynomialMap_quotient]

theorem reducedSquareSymbolMap_surjective : Function.Surjective (F.reducedSquareSymbolMap w) :=
  F.squareFiltration.quotientTopSymbolMap_surjective w

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev ReducedSquareBasisIndex (s : ℕ) (ω : ι → ℕ) :=
  QuotientTopBasisIndex s (squareBasisWeight ω)

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def reducedSquareBasis :
    Basis (ReducedSquareBasisIndex s ω) ℚ
      (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) :=
  F.squareFiltration.quotientTopBasis (F.adaptedSquareBasis e ω (hF 2))
    (squareBasisWeight ω) (F.adaptedSquareBasis_layers e ω hF)

theorem reducedSquareBasis_layers (j : ℕ) :
    F.squareFiltration.quotientTop.layer j = Submodule.span ℚ
      (F.reducedSquareBasis e ω hF '' {i | j ≤ squareBasisWeight ω i.val}) :=
  F.squareFiltration.quotientTopBasis_layers (F.adaptedSquareBasis e ω (hF 2))
    (squareBasisWeight ω) (F.adaptedSquareBasis_layers e ω hF) j

theorem reducedSquareSnd_basis_height
    (a : ReducedSquareBasisIndex s ω) (b : QuotientTopBasisIndex s ω) :
    RationalHeightLE ((F.quotientTopBasis e ω hF).repr
      (F.reducedSquareSnd (F.reducedSquareBasis e ω hF a)) b) 1 := by
  dsimp only [reducedSquareBasis]
  rw [F.squareFiltration.quotientTopBasis_apply, F.reducedSquareSnd_mk, F.quotientTopBasis_repr_mk]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl i =>
    change RationalHeightLE (e.repr ((F.adaptedSquareBasis e ω (hF 2) (Sum.inl i)).val.2) b.val) 1
    rw [F.adaptedSquareBasis_inl]
    exact basis_repr_height_one e i b.val
  | inr i =>
    change RationalHeightLE (e.repr ((F.adaptedSquareBasis e ω (hF 2) (Sum.inr i)).val.2) b.val) 1
    rw [F.adaptedSquareBasis_inr, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev QuotientTopSymbolIndex (s : ℕ) (w : σ → ℕ) (ω : ι → ℕ) :=
  SymbolBasisIndex w (fun i : QuotientTopBasisIndex s ω => ω i.val)

abbrev ReducedSquareSymbolIndex (s : ℕ) (w : σ → ℕ) (ω : ι → ℕ) :=
  SymbolBasisIndex w (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω i.val)

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def quotientTopSymbolBasis :
    Basis (QuotientTopSymbolIndex s w ω) ℚ (F.quotientTop.PolynomialSymbol w) :=
  F.quotientTop.polynomialSymbolBasis (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w

noncomputable def reducedSquareSymbolBasis :
    Basis (ReducedSquareSymbolIndex s w ω) ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w) :=
  F.squareFiltration.quotientTop.polynomialSymbolBasis (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w

theorem reducedSquareSndSymbolMap_basis_height
    (a : ReducedSquareSymbolIndex s w ω) (b : QuotientTopSymbolIndex s w ω) :
    RationalHeightLE ((F.quotientTopSymbolBasis e ω hF w).repr
      (F.reducedSquareSndSymbolMap w (F.reducedSquareSymbolBasis e ω hF w a)) b) 1 :=
  filteredPolynomialSymbolMap_basis_height F.squareFiltration.quotientTop F.quotientTop
    (F.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
    (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem w le_rfl
    (fun i j => F.reducedSquareSnd_basis_height e ω hF j i) a b

theorem reducedSquareSndSymbolMap_monomial_blocks
    (a : ReducedSquareSymbolIndex s w ω) (b : QuotientTopSymbolIndex s w ω)
    (hab : b.val.1 ≠ a.val.1) :
    (F.quotientTopSymbolBasis e ω hF w).repr
      (F.reducedSquareSndSymbolMap w (F.reducedSquareSymbolBasis e ω hF w a)) b = 0 :=
  filteredPolynomialSymbolMap_monomial_blocks F.squareFiltration.quotientTop F.quotientTop
    (F.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
    (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem w a b hab

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adaptedSquareBasis_structure_bound (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hd : 2 * (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (i j k : ι ⊕ {i // 2 ≤ w i}) :
    rationalLogHeight (lieStructureConstants (F.adaptedSquareBasis b w h) i j k) ≤
      (p + 2) ^ 11 := by
  classical
  have hB (i j) : RationalHeightLE
      (LinearMap.toMatrix (F.adaptedSquareBasis b w h) (Pi.basis (fun _ : Bool => b))
        F.squarePairMap.toLinearMap i j) H := by
    rw [LinearMap.toMatrix_apply]
    exact (F.adaptedSquareBasis_pairMap_height b w h i j).mono hH
  obtain ⟨_, _, _, hbr⟩ := exists_bounded_lie_embedding_retraction
    (F.adaptedSquareBasis b w h) (Pi.basis (fun _ : Bool => b))
    F.squarePairMap F.squarePairMap_injective hH
    (lie_pi_structure_height (fun _ : Bool => b) hH (fun _ => hc))
    hB
  apply rationalLogHeight_le_of_height (hbr i j k)
  apply rationalLieStructureHeight_inverse_budget _ _ _ hp
  · simpa only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ,
      Fintype.card_bool, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using hd
  · exact (Nat.cast_le.mpr (card_squareBasis_index_le w)).trans (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd)
  · exact hHp

theorem exists_adaptedSquareBasis_grid (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    (Γ : Subgroup F.Group) {l : ℕ} (hl : 0 < l)
    (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : 2 * (Fintype.card ι : ℝ) ≤ p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (F.adaptedSquareBasis b w h) (F.squareLattice Γ) ∧
      bchSubgroupCoordinates (F.adaptedSquareBasis b w h) (F.squareLattice Γ) ⊆
        denominatorGrid N := by
  classical
  have hB (i j) : RationalHeightLE
      (LinearMap.toMatrix (F.adaptedSquareBasis b w h) (Pi.basis (fun _ : Bool => b))
        F.squarePairMap.toLinearMap i j) 1 := by
    rw [LinearMap.toMatrix_apply]
    exact F.adaptedSquareBasis_pairMap_height b w h i j
  rw [F.squareLattice_eq_pair_comap]
  apply exists_bchSubgroup_comap_grid_exp_bound
    (F.adaptedSquareBasis b w h) (Pi.basis (fun _ : Bool => b))
    F.squarePairMap F.squarePairMap_injective _ (H := 1) le_rfl hl
    hB
    (piBCHSubgroup_inner_grid (fun _ : Bool => F) (fun _ => b) (fun _ => Γ) l
      (fun _ => hin))
    (piBCHSubgroup_outer_grid (fun _ : Bool => F) (fun _ => b) (fun _ => Γ) l
      (fun _ => hout)) hp
  · simpa only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ,
      Fintype.card_bool, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using hd
  · exact (Nat.cast_le.mpr (card_squareBasis_index_le w)).trans (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd)
  · simpa only [Nat.cast_one] using Real.one_le_exp hp
  · exact hlp

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastCoefficientImage
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev FirstCoefficientModule (F : NilpotentLieFiltration L s) (w : σ → ℕ) :=
  (F.shiftedPolynomialIdeal w 1) ⧸
    (F.shiftedPolynomialIdeal w 2).toSubmodule.comap (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype

noncomputable def firstCoefficientMap (F : NilpotentLieFiltration L s) (w : σ → ℕ) :
    (F.shiftedPolynomialIdeal w 1) →ₗ[ℚ] F.FirstCoefficientModule w :=
  ((F.shiftedPolynomialIdeal w 2).toSubmodule.comap
    (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype).mkQ

theorem firstCoefficientMap_eq_zero_iff (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (p : F.shiftedPolynomialIdeal w 1) :
    F.firstCoefficientMap w p = 0 ↔
      ∀ α, coefficients (p.val : VectorPolynomial σ ℚ L) α ∈ F.layer (Finsupp.weight w α + 2) :=
  Submodule.Quotient.mk_eq_zero _

abbrev FirstCoefficientIndex (w : σ → ℕ) (ω : ι → ℕ) :=
  {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 + 1 = ω z.2}

def firstCoefficientSurvivorEquiv (w : σ → ℕ) (ω : ι → ℕ) :
    {z : ShiftedMonomialIndex w ω 1 //
      ¬ Finsupp.weight w z.val.val.1 + 2 ≤ ω z.val.val.2} ≃ FirstCoefficientIndex w ω where
  toFun z := ⟨z.val.val.val, by
    have h : Finsupp.weight w z.val.val.val.1 + 1 ≤ ω z.val.val.val.2 := z.val.property
    have hn : ¬ Finsupp.weight w z.val.val.val.1 + 2 ≤ ω z.val.val.val.2 := z.property
    omega⟩
  invFun z := ⟨⟨⟨z.val, by have h := z.property; omega⟩, z.property.le⟩, by
    change ¬ Finsupp.weight w z.val.1 + 2 ≤ ω z.val.2
    have h := z.property
    omega⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def firstCoefficientBasis (w : σ → ℕ) :
    Basis (FirstCoefficientIndex w ω) ℚ (F.FirstCoefficientModule w) :=
  (supportedQuotientBasis (F.shiftedMonomialBasis b ω hF w 1)
    ((F.shiftedPolynomialIdeal w 2).toSubmodule.comap
      (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype)
    {z | Finsupp.weight w z.val.val.1 + 2 ≤ ω z.val.val.2}
    (F.shiftedPolynomial_next_eq_span b ω hF w 1)).reindex (firstCoefficientSurvivorEquiv w ω)

theorem firstCoefficientBasis_repr_map (w : σ → ℕ) (p : F.shiftedPolynomialIdeal w 1)
    (z : FirstCoefficientIndex w ω) :
    (F.firstCoefficientBasis b ω hF w).repr (F.firstCoefficientMap w p) z =
      b.repr (coefficients (p.val : VectorPolynomial σ ℚ L) z.val.1) z.val.2 := by
  rw [firstCoefficientBasis, Basis.repr_reindex_apply]
  change (supportedQuotientBasis _ _ _ _).repr
    (((F.shiftedPolynomialIdeal w 2).toSubmodule.comap
      (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype).mkQ p) _ = _
  rw [supportedQuotientBasis_repr_mk, F.shiftedMonomialBasis_repr]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem firstCoefficientMap_surjective : Function.Surjective (F.firstCoefficientMap w) :=
  Submodule.mkQ_surjective _

noncomputable def firstCoefficientHorizontal : F.FirstCoefficientModule w →ₗ[ℚ] L ⧸ F.layer 2 :=
  ((F.shiftedPolynomialIdeal w 2).toSubmodule.comap
    (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype).liftQ
    (((F.layer 2).mkQ.comp (F.adaptedCoefficientMap w 0)).comp
      (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype) (by
        intro p hp
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        change coefficients p.val.val 0 ∈ F.layer 2
        have h := hp 0
        change coefficients p.val.val 0 ∈ F.layer (Finsupp.weight w 0 + 2) at h
        simpa only [map_zero, Nat.zero_add] using h)

@[simp] theorem firstCoefficientHorizontal_map (p : F.shiftedPolynomialIdeal w 1) :
    F.firstCoefficientHorizontal w (F.firstCoefficientMap w p) =
      (F.layer 2).mkQ (coefficients p.val.val 0) := rfl

noncomputable def firstCoefficientConstant : L →ₗ[ℚ] F.FirstCoefficientModule w :=
  (F.firstCoefficientMap w).comp
    ((F.adaptedConstantLieHom w).toLinearMap.codRestrict
      (F.shiftedPolynomialIdeal w 1).toSubmodule (F.adaptedConstant_mem_shiftedIdeal w))

@[simp] theorem firstCoefficientHorizontal_constant (x : L) :
    F.firstCoefficientHorizontal w (F.firstCoefficientConstant w x) = (F.layer 2).mkQ x := by
  change (F.layer 2).mkQ (coefficients (monomial 0 x) 0) = _
  simp only [coefficients_monomial, Finsupp.single_eq_same]

noncomputable def firstCoefficientHorizontalSection : (L ⧸ F.layer 2) →ₗ[ℚ] F.FirstCoefficientModule w :=
  (F.layer 2).liftQ (F.firstCoefficientConstant w) (by
    intro x hx
    change F.firstCoefficientMap w ⟨F.adaptedConstant w x, F.adaptedConstant_mem_shiftedIdeal w x⟩ = 0
    apply (F.firstCoefficientMap_eq_zero_iff w _).mpr
    exact F.adaptedConstant_mem_shiftedPolynomialIdeal w 2 hx)

@[simp] theorem firstCoefficientHorizontalSection_mk (x : L) :
    F.firstCoefficientHorizontalSection w ((F.layer 2).mkQ x) = F.firstCoefficientConstant w x := rfl

theorem firstCoefficientHorizontal_section (x : L ⧸ F.layer 2) :
    F.firstCoefficientHorizontal w (F.firstCoefficientHorizontalSection w x) = x := by
  obtain ⟨v, rfl⟩ := (F.layer 2).mkQ_surjective x
  rw [F.firstCoefficientHorizontalSection_mk, F.firstCoefficientHorizontal_constant]

noncomputable def normalizedFirstCoefficientMap :
    F.normalizedRelativeSubmodule w →ₗ[ℚ] F.FirstCoefficientModule w :=
  (F.firstCoefficientMap w).comp
    ((F.normalizedRelativeSubmodule w).subtype.codRestrict
      (F.shiftedPolynomialIdeal w 1).toSubmodule (fun p => p.property.1))

theorem normalizedFirstCoefficientMap_eq_zero_iff (p : F.normalizedRelativeSubmodule w) :
    F.normalizedFirstCoefficientMap w p = 0 ↔ p.val ∈ F.shiftedPolynomialIdeal w 2 :=
  F.firstCoefficientMap_eq_zero_iff w _

theorem normalizedFirstCoefficientMap_range :
    LinearMap.range (F.normalizedFirstCoefficientMap w) = LinearMap.ker (F.firstCoefficientHorizontal w) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr p.property.2
  · intro hx
    obtain ⟨p, rfl⟩ := F.firstCoefficientMap_surjective w x
    have hp : coefficients p.val.val 0 ∈ F.layer 2 := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact ⟨⟨p.val, p.property, hp⟩, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

theorem firstCoefficientIndex_grade_pos {σ ι : Type*} (ω : ι → ℕ)
    (z : FirstCoefficientIndex (fun _ : σ => 1) ω) : 1 ≤ ω z.val.2 := by
  have h := z.property
  omega

theorem firstCoefficientIndex_zero_iff_grade_one {σ ι : Type*} (ω : ι → ℕ)
    (z : FirstCoefficientIndex (fun _ : σ => 1) ω) :
    z.val.1 = 0 ↔ ω z.val.2 = 1 := by
  constructor
  · intro hz
    have h := z.property
    simpa only [hz, map_zero, zero_add] using h.symm
  · intro hz
    apply Finsupp.ext
    intro i
    change z.val.1 i = 0
    by_contra hi
    have hw := Finsupp.le_weight_of_ne_zero' (fun _ : σ => (1 : ℕ)) hi
    have h := z.property
    omega

theorem exists_sorted_firstCoefficient_rows {σ ι : Type*} {d : ℕ}
    (ω : ι → ℕ) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω) :
    ∃ (e : Equiv.Perm (Fin d)) (a : ℕ), a ≤ d ∧
      Monotone (fun i => ω (rows (e i)).val.2) ∧
      ∀ i, i.val < a ↔ (rows (e i)).val.1 = 0 := by
  obtain ⟨e, a, ha, hm, hi⟩ := exists_sorted_positive_weights
    (fun i => ω (rows i).val.2) (fun i => firstCoefficientIndex_grade_pos ω (rows i))
  refine ⟨e, a, ha, hm, ?_⟩
  intro i
  exact (hi i).trans (firstCoefficientIndex_zero_iff_grade_one ω (rows (e i))).symm

theorem sorted_firstCoefficient_scale_bounds {σ ι : Type*} {d a : ℕ}
    (ω : ι → ℕ) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (hzero : ∀ i, i.val < a ↔ (rows i).val.1 = 0)
    (T : σ → ℝ) (Tmin : ℝ) (hmin : 1 ≤ Tmin) (hT : ∀ i, Tmin ≤ T i) :
    (∀ i, i.val < a → monomialScale T (rows i).val.1 = 1) ∧
      (∀ i, a ≤ i.val → Tmin ≤ monomialScale T (rows i).val.1) := by
  constructor
  · intro i hi
    rw [(hzero i).mp hi, monomialScale_zero]
  · intro i hi
    apply le_monomialScale_of_ne_zero T hmin hT
    intro hz
    exact (not_lt_of_ge hi) ((hzero i).mpr hz)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareSndSymbolKernel_lift {x : F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hx : F.reducedSquareSndSymbolMap w x = 0) :
    ∃ y : F.squareFiltration.PolynomialSymbol w,
      F.squareSndSymbolMap w y = 0 ∧ F.reducedSquareSymbolMap w y = x := by
  obtain ⟨y, rfl⟩ := F.reducedSquareSymbolMap_surjective w x
  refine ⟨y - F.squareDiagonalSymbolMap w (F.squareSndSymbolMap w y), ?_, ?_⟩
  · rw [map_sub, F.squareSndSymbolMap_diagonal, sub_self]
  · rw [map_sub, ← F.reducedSquareDiagonalSymbolMap_quotient,
      ← F.reducedSquareSndSymbolMap_quotient, hx, map_zero, sub_zero]

theorem reducedSquareSndSymbolKernel_lie_eq_zero (hw : ∀ i, 0 < w i)
    {x y : F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hx : F.reducedSquareSndSymbolMap w x = 0) (hy : F.reducedSquareSndSymbolMap w y = 0) :
    ⁅x, y⁆ = 0 := by
  obtain ⟨a, ha, rfl⟩ := F.reducedSquareSndSymbolKernel_lift w hx
  obtain ⟨b, hb, rfl⟩ := F.reducedSquareSndSymbolKernel_lift w hy
  rw [← LieHom.map_lie, F.squareSndSymbolKernel_lie_eq_zero w hw ha hb, map_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def reducedSquareSndSymbolHom : F.squareFiltration.quotientTop.PolynomialSymbolGroup w →* F.quotientTop.PolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.reducedSquareSndSymbolMap w)

noncomputable def reducedSquareDiagonalSymbolHom : F.quotientTop.PolynomialSymbolGroup w →* F.squareFiltration.quotientTop.PolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.reducedSquareDiagonalSymbolMap w)

@[simp] theorem reducedSquareSndSymbolHom_diagonal (g : F.quotientTop.PolynomialSymbolGroup w) :
    F.reducedSquareSndSymbolHom w (F.reducedSquareDiagonalSymbolHom w g) = g := by
  apply NilpotentLieBCHGroup.ext
  exact F.reducedSquareSndSymbolMap_diagonal w g.coord

noncomputable def reducedSquareRelativeGroupPart (g : F.squareFiltration.quotientTop.PolynomialSymbolGroup w) :
    F.squareFiltration.quotientTop.PolynomialSymbolGroup w :=
  splitRelativePart (F.reducedSquareSndSymbolHom w) (F.reducedSquareDiagonalSymbolHom w) g

@[simp] theorem reducedSquareRelativeGroupPart_projection (g : F.squareFiltration.quotientTop.PolynomialSymbolGroup w) :
    F.reducedSquareSndSymbolHom w (F.reducedSquareRelativeGroupPart w g) = 1 :=
  splitRelativePart_projection _ _ (F.reducedSquareSndSymbolHom_diagonal w) g

variable (hw : ∀ i, 0 < w i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

noncomputable def reducedRelativeSquareSymbolMap :
    F.normalizedRelativeSubmodule w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w :=
  (F.reducedSquareSymbolMap w).toLinearMap.comp (F.relativeSquareSymbolMap w hw)

@[simp] theorem reducedRelativeSquareSymbolMap_apply (p : F.normalizedRelativeSubmodule w) :
    F.reducedRelativeSquareSymbolMap w hw p =
      F.reducedSquareSymbolMap w (F.relativeSquareSymbolMap w hw p) := rfl

@[simp] theorem reducedRelativeSquareSymbolMap_projection (p : F.normalizedRelativeSubmodule w) :
    F.reducedSquareSndSymbolMap w (F.reducedRelativeSquareSymbolMap w hw p) = 0 := by
  rw [F.reducedRelativeSquareSymbolMap_apply, F.reducedSquareSndSymbolMap_quotient,
    F.squareSndSymbolMap_relative, map_zero]

theorem reducedRelativeSquareSymbolMap_range :
    LinearMap.range (F.reducedRelativeSquareSymbolMap w hw) =
      (F.reducedSquareSndSymbolMap w).ker.toSubmodule := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    exact F.reducedRelativeSquareSymbolMap_projection w hw p
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := F.reducedSquareSndSymbolKernel_lift w hx
    have hr : y ∈ LinearMap.range (F.relativeSquareSymbolMap w hw) := by
      rw [F.relativeSquareSymbolMap_range w hw]
      exact hy
    obtain ⟨p, rfl⟩ := hr
    exact ⟨p, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def reducedSquareDifference :
    (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] L :=
  (F.squareFiltration.layerIdeal (s + 1)).toSubmodule.liftQ
    (F.squareFst.toLinearMap - F.squareSnd.toLinearMap) (by
      intro x hx
      change x.val.1 - x.val.2 = 0
      exact sub_eq_zero.mpr ((F.mem_squareFiltration_top x).mp hx).2)

@[simp] theorem reducedSquareDifference_mk (x : F.squareLieSubalgebra) :
    F.reducedSquareDifference (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) x) =
      x.val.1 - x.val.2 := rfl

theorem reducedSquareDifference_mem_layer (j : ℕ)
    (x : F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1))
    (hx : x ∈ F.squareFiltration.quotientTop.layer j) :
    F.reducedSquareDifference x ∈ F.layer (j + 1) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact hy.2.2

theorem reducedRelativeSquareSymbolMap_eq_zero_iff (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : F.normalizedRelativeSubmodule w) :
    F.reducedRelativeSquareSymbolMap w hw p = 0 ↔ p.val ∈ F.shiftedPolynomialIdeal w 2 := by
  constructor
  · intro hp α
    change coefficients p.val.val α ∈ F.layer (Finsupp.weight w α + 2)
    change F.squareFiltration.quotientTop.polynomialSymbolMap w
      (F.reducedSquarePolynomialMap w (F.relativeSquareLift w hw p)) = 0 at hp
    have hα := (F.squareFiltration.quotientTop.polynomialSymbolMap_eq_zero_iff w _).mp hp α
    have hd := F.reducedSquareDifference_mem_layer (Finsupp.weight w α + 1) _ hα
    change F.reducedSquareDifference
      (coefficients (map (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).toLinearMap
        (F.relativeSquarePolynomial w hw p)) α) ∈ _ at hd
    rw [coefficients_map] at hd
    change F.reducedSquareDifference
      (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
        (coefficients (F.relativeSquarePolynomial w hw p) α)) ∈ _ at hd
    rw [F.reducedSquareDifference_mk, F.relativeSquarePolynomial_coefficient] at hd
    simpa only [sub_zero, Nat.add_assoc] using hd
  · intro hp
    rw [F.reducedRelativeSquareSymbolMap_apply,
      (F.relativeSquareSymbolMap_eq_zero_iff w hw p).mpr hp, map_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (h : σ → ℚ) (e m : L)
  (p : F.adaptedLieSubalgebra (fun _ : σ => 1))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem normalizedFirstCoefficientMap_ker :
    LinearMap.ker (F.normalizedFirstCoefficientMap w) =
      LinearMap.ker (F.reducedRelativeSquareSymbolMap w hw) := by
  ext p
  change F.normalizedFirstCoefficientMap w p = 0 ↔ F.reducedRelativeSquareSymbolMap w hw p = 0
  rw [F.normalizedFirstCoefficientMap_eq_zero_iff, F.reducedRelativeSquareSymbolMap_eq_zero_iff]

noncomputable def firstCoefficientRelativeRangeEquiv :
    LinearMap.range (F.normalizedFirstCoefficientMap w) ≃ₗ[ℚ]
      LinearMap.range (F.reducedRelativeSquareSymbolMap w hw) :=
  commonKernelRangeEquiv (F.normalizedFirstCoefficientMap w) (F.reducedRelativeSquareSymbolMap w hw)
    (F.normalizedFirstCoefficientMap_ker w hw)

theorem firstCoefficientRelativeRangeEquiv_apply (p : F.normalizedRelativeSubmodule w) :
    (F.firstCoefficientRelativeRangeEquiv w hw ⟨F.normalizedFirstCoefficientMap w p, ⟨p, rfl⟩⟩ :
      F.squareFiltration.quotientTop.PolynomialSymbol w) = F.reducedRelativeSquareSymbolMap w hw p :=
  commonKernelRangeEquiv_apply _ _ _ p

noncomputable def firstCoefficientRelativeEquiv :
    LinearMap.ker (F.firstCoefficientHorizontal w) ≃ₗ[ℚ]
      (F.reducedSquareSndSymbolMap w).ker :=
  (LinearEquiv.ofEq _ _ (F.normalizedFirstCoefficientMap_range w).symm).trans
    ((F.firstCoefficientRelativeRangeEquiv w hw).trans
      (LinearEquiv.ofEq _ _ (F.reducedRelativeSquareSymbolMap_range w hw)))

theorem firstCoefficientRelativeEquiv_apply (p : F.normalizedRelativeSubmodule w)
    (hp : F.normalizedFirstCoefficientMap w p ∈ LinearMap.ker (F.firstCoefficientHorizontal w)) :
    (F.firstCoefficientRelativeEquiv w hw ⟨F.normalizedFirstCoefficientMap w p, hp⟩ :
      F.squareFiltration.quotientTop.PolynomialSymbol w) = F.reducedRelativeSquareSymbolMap w hw p :=
  F.firstCoefficientRelativeRangeEquiv_apply w hw p

noncomputable def firstCoefficientRelativeMap :
    LinearMap.ker (F.firstCoefficientHorizontal w) →ₗ[ℚ]
      F.squareFiltration.quotientTop.PolynomialSymbol w :=
  (F.reducedSquareSndSymbolMap w).ker.toSubmodule.subtype.comp
    (F.firstCoefficientRelativeEquiv w hw).toLinearMap

noncomputable def firstCoefficientFastSubmodule
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w)) :
    Submodule ℚ (F.FirstCoefficientModule w) :=
  (U.comap (F.firstCoefficientRelativeMap w hw)).map (LinearMap.ker (F.firstCoefficientHorizontal w)).subtype

theorem firstCoefficientFastSubmodule_le_horizontal_ker
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w)) :
    F.firstCoefficientFastSubmodule w hw U ≤ LinearMap.ker (F.firstCoefficientHorizontal w) := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem normalizedFirstCoefficientMap_mem_fast_iff
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (p : F.normalizedRelativeSubmodule w) :
    F.normalizedFirstCoefficientMap w p ∈ F.firstCoefficientFastSubmodule w hw U ↔
      F.reducedRelativeSquareSymbolMap w hw p ∈ U := by
  have hp : F.normalizedFirstCoefficientMap w p ∈ LinearMap.ker (F.firstCoefficientHorizontal w) := by
    rw [← F.normalizedFirstCoefficientMap_range w]
    exact ⟨p, rfl⟩
  constructor
  · rintro ⟨y, hy, he⟩
    have hy' : y = ⟨F.normalizedFirstCoefficientMap w p, hp⟩ := Subtype.ext he
    rw [hy'] at hy
    change (F.firstCoefficientRelativeEquiv w hw ⟨F.normalizedFirstCoefficientMap w p, hp⟩ :
      F.squareFiltration.quotientTop.PolynomialSymbol w) ∈ U at hy
    rwa [F.firstCoefficientRelativeEquiv_apply] at hy
  · intro h
    refine ⟨⟨F.normalizedFirstCoefficientMap w p, hp⟩, ?_, rfl⟩
    change (F.firstCoefficientRelativeEquiv w hw ⟨F.normalizedFirstCoefficientMap w p, hp⟩ :
      F.squareFiltration.quotientTop.PolynomialSymbol w) ∈ U
    rwa [F.firstCoefficientRelativeEquiv_apply]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

variable [Fintype σ]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareDifference_mem_two
    (x : F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) :
    F.reducedSquareDifference x ∈ F.layer 2 := by
  obtain ⟨y, rfl⟩ := lieQuotientMap_surjective (F.squareFiltration.layerIdeal (s + 1)) x
  rw [F.reducedSquareDifference_mk]
  exact (F.mem_squareLieSubalgebra y.val).mp y.property

noncomputable def reducedSquareDifferenceAdapted :
    F.squareFiltration.quotientTop.adaptedLieSubalgebra w →ₗ[ℚ] F.adaptedLieSubalgebra w :=
  ((VectorPolynomial.map F.reducedSquareDifference).comp
    (F.squareFiltration.quotientTop.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
      (F.adaptedLieSubalgebra w).toSubmodule (by
        intro p α
        change coefficients (VectorPolynomial.map F.reducedSquareDifference p.val) α ∈ _
        rw [coefficients_map]
        exact F.antitone (Nat.le_succ _) (F.reducedSquareDifference_mem_layer _ _ (p.property α)))

noncomputable def reducedSquareDifferenceRelative :
    F.squareFiltration.quotientTop.adaptedLieSubalgebra w →ₗ[ℚ] F.normalizedRelativeSubmodule w :=
  (F.reducedSquareDifferenceAdapted w).codRestrict (F.normalizedRelativeSubmodule w) (by
    intro p
    constructor
    · intro α
      change coefficients (VectorPolynomial.map F.reducedSquareDifference p.val) α ∈ _
      rw [coefficients_map]
      exact F.reducedSquareDifference_mem_layer _ _ (p.property α)
    · change coefficients (VectorPolynomial.map F.reducedSquareDifference p.val) 0 ∈ F.layer 2
      rw [coefficients_map]
      exact F.reducedSquareDifference_mem_two _)

theorem reducedSquareDifferenceRelative_coefficient
    (p : F.squareFiltration.quotientTop.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.reducedSquareDifferenceRelative w p).val.val α =
      F.reducedSquareDifference (coefficients p.val α) :=
  coefficients_map F.reducedSquareDifference p.val α

noncomputable def reducedSquareCoefficientMap :
    F.squareFiltration.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.FirstCoefficientModule w :=
  (F.squareFiltration.quotientTop.shiftedAdaptedIdeal w).toSubmodule.liftQ
    ((F.normalizedFirstCoefficientMap w).comp (F.reducedSquareDifferenceRelative w)) (by
      intro p hp
      apply (F.normalizedFirstCoefficientMap_eq_zero_iff w _).mpr
      intro α
      change coefficients (F.reducedSquareDifferenceRelative w p).val.val α ∈ _
      rw [F.reducedSquareDifferenceRelative_coefficient]
      exact F.reducedSquareDifference_mem_layer _ _ (hp α))

@[simp] theorem reducedSquareCoefficientMap_symbol
    (p : F.squareFiltration.quotientTop.adaptedLieSubalgebra w) :
    F.reducedSquareCoefficientMap w (F.squareFiltration.quotientTop.polynomialSymbolMap w p) =
      F.normalizedFirstCoefficientMap w (F.reducedSquareDifferenceRelative w p) := rfl

theorem reducedSquareDifferenceRelative_relative (hw : ∀ i, 0 < w i)
    (p : F.normalizedRelativeSubmodule w) :
    F.reducedSquareDifferenceRelative w
      (F.reducedSquarePolynomialMap w (F.relativeSquareLift w hw p)) = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.reducedSquareDifferenceRelative_coefficient]
  change F.reducedSquareDifference
    (coefficients (VectorPolynomial.map
      (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).toLinearMap
      (F.relativeSquarePolynomial w hw p)) α) = _
  rw [coefficients_map]
  change F.reducedSquareDifference
    (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
      (coefficients (F.relativeSquarePolynomial w hw p) α)) = _
  rw [F.reducedSquareDifference_mk, F.relativeSquarePolynomial_coefficient, sub_zero]

@[simp] theorem reducedSquareCoefficientMap_relative (hw : ∀ i, 0 < w i)
    (p : F.normalizedRelativeSubmodule w) :
    F.reducedSquareCoefficientMap w (F.reducedRelativeSquareSymbolMap w hw p) =
      F.normalizedFirstCoefficientMap w p := by
  change F.reducedSquareCoefficientMap w (F.squareFiltration.quotientTop.polynomialSymbolMap w
    (F.reducedSquarePolynomialMap w (F.relativeSquareLift w hw p))) = _
  rw [F.reducedSquareCoefficientMap_symbol, F.reducedSquareDifferenceRelative_relative]

theorem reducedSquareCoefficientMap_horizontal
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w) :
    F.firstCoefficientHorizontal w (F.reducedSquareCoefficientMap w x) = 0 := by
  obtain ⟨p, rfl⟩ := F.squareFiltration.quotientTop.polynomialSymbolMap_surjective w x
  rw [F.reducedSquareCoefficientMap_symbol]
  exact (F.normalizedFirstCoefficientMap_range w).le ⟨F.reducedSquareDifferenceRelative w p, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem reducedSquareCoefficientMap_relativeMap
    (x : LinearMap.ker (F.firstCoefficientHorizontal w)) :
    F.reducedSquareCoefficientMap w (F.firstCoefficientRelativeMap w hw x) = x.val := by
  have hx : x.val ∈ LinearMap.range (F.normalizedFirstCoefficientMap w) :=
    (F.normalizedFirstCoefficientMap_range w).ge x.property
  obtain ⟨p, hp⟩ := hx
  have hm : F.normalizedFirstCoefficientMap w p ∈ LinearMap.ker (F.firstCoefficientHorizontal w) :=
    (F.normalizedFirstCoefficientMap_range w).le ⟨p, rfl⟩
  have he : x = ⟨F.normalizedFirstCoefficientMap w p, hm⟩ := Subtype.ext hp.symm
  rw [he]
  change F.reducedSquareCoefficientMap w
    (F.firstCoefficientRelativeEquiv w hw ⟨F.normalizedFirstCoefficientMap w p, hm⟩).val = _
  rw [F.firstCoefficientRelativeEquiv_apply, F.reducedSquareCoefficientMap_relative]

theorem firstCoefficientRelativeMap_coefficientMap
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hx : x ∈ (F.reducedSquareSndSymbolMap w).ker) :
    F.firstCoefficientRelativeMap w hw
      ⟨F.reducedSquareCoefficientMap w x, F.reducedSquareCoefficientMap_horizontal w x⟩ = x := by
  have hx' : x ∈ LinearMap.range (F.reducedRelativeSquareSymbolMap w hw) :=
    (F.reducedRelativeSquareSymbolMap_range w hw).ge hx
  obtain ⟨p, rfl⟩ := hx'
  have hm : F.normalizedFirstCoefficientMap w p ∈ LinearMap.ker (F.firstCoefficientHorizontal w) :=
    (F.normalizedFirstCoefficientMap_range w).le ⟨p, rfl⟩
  have he : (⟨F.reducedSquareCoefficientMap w (F.reducedRelativeSquareSymbolMap w hw p),
      F.reducedSquareCoefficientMap_horizontal w _⟩ : LinearMap.ker (F.firstCoefficientHorizontal w)) =
      ⟨F.normalizedFirstCoefficientMap w p, hm⟩ :=
    Subtype.ext (F.reducedSquareCoefficientMap_relative w hw p)
  exact (congrArg (F.firstCoefficientRelativeMap w hw) he).trans
    (F.firstCoefficientRelativeEquiv_apply w hw p hm)

theorem firstCoefficientFastSubmodule_eq_image
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w)) :
    F.firstCoefficientFastSubmodule w hw U =
      (U ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule).map (F.reducedSquareCoefficientMap w) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨F.firstCoefficientRelativeMap w hw x, ⟨hx, ?_⟩,
      F.reducedSquareCoefficientMap_relativeMap w hw x⟩
    exact (F.firstCoefficientRelativeEquiv w hw x).property
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨⟨F.reducedSquareCoefficientMap w x, F.reducedSquareCoefficientMap_horizontal w x⟩, ?_, rfl⟩
    change F.firstCoefficientRelativeMap w hw
      ⟨F.reducedSquareCoefficientMap w x, F.reducedSquareCoefficientMap_horizontal w x⟩ ∈ U
    rw [F.firstCoefficientRelativeMap_coefficientMap w hw x hx.2]
    exact hx.1

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFirstCoefficientHorizontal
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

noncomputable def realAdaptedDirectionalDerivative :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) →ₗ[ℝ]
      (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :=
  (F.adaptedDirectionalDerivative h).baseChange ℝ

theorem realAdaptedDirectionalDerivative_polynomial
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedPolynomialMap (fun _ => 1) (F.realAdaptedDirectionalDerivative h x) =
      directionalDerivative h (F.realAdaptedPolynomialMap (fun _ => 1) x) := by
  apply coefficients.injective
  ext α
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r p =>
    change coefficients (F.realAdaptedPolynomialMap (fun _ => 1)
      ((F.adaptedDirectionalDerivative h).baseChange ℝ (r ⊗ₜ[ℚ] p))) α = _
    rw [LinearMap.baseChange_tmul, F.realAdaptedPolynomialMap_coefficient_tmul,
      F.adaptedDirectionalDerivative_coe, coefficients_directionalDerivative,
      coefficients_directionalDerivative]
    simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      F.realAdaptedPolynomialMap_coefficient_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem realAdaptedDirectionalDerivative_tensor
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedPolynomialTensor (fun _ => 1) (F.realAdaptedDirectionalDerivative h x) =
      F.realification.adaptedDirectionalDerivative h (F.realAdaptedPolynomialTensor (fun _ => 1) x) := by
  apply Subtype.ext
  exact F.realAdaptedDirectionalDerivative_polynomial h x

theorem realAdaptedDirectionalDerivative_bound (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T M x)
    (hh : ∀ i, |(h i : ℝ)| ≤ T i) :
    F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T ((Fintype.card σ : ℝ) * s * M)
      (F.realAdaptedDirectionalDerivative h x) := by
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
    have hni : ¬ Finsupp.weight (fun _ : σ => 1) β ≤ ω z.val.2 := by omega
    exact (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp
      ((F.realification.adapted_iff_coefficients (fun _ => 1) _).mp
        (F.realAdaptedPolynomialMap_adapted (fun _ => 1) x) β) z.val.2 hni
  exact directionalDerivative_scaled_coordinate_bound f
    (F.realAdaptedPolynomialMap (fun _ => 1) x) s hdegree T hT M hM
    (fun β => hp β z.val.2) h hh z.val.1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

noncomputable def realAdaptedPolynomialJet
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    DualGroup (F.adaptedPolynomialFiltration (fun _ : σ => 1)).realification.lowerCentralSeries_eq_bot :=
  ⟨dualConstantLie x + dualInfinitesimal (F.realAdaptedDirectionalDerivative h x)⟩

@[simp] theorem realAdaptedPolynomialJet_base
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualBaseLinear (F.realAdaptedPolynomialJet h x).coord = x := by
  change dualBaseLinear (dualConstantLie x + dualInfinitesimal _) = x
  simp only [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem realAdaptedPolynomialJet_tangent
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    dualTangentLinear (F.realAdaptedPolynomialJet h x).coord = F.realAdaptedDirectionalDerivative h x := by
  change dualTangentLinear (dualConstantLie x + dualInfinitesimal _) = _
  simp only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

noncomputable def realAdaptedLogDerivative
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  dualLogDerivative (F.realAdaptedPolynomialJet h x)

theorem realAdaptedLogDerivative_tensor
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedPolynomialTensor (fun _ => 1) (F.realAdaptedLogDerivative h x) =
      F.realification.adaptedLogDerivative h (F.realAdaptedPolynomialTensor (fun _ => 1) x) := by
  let φ := F.realAdaptedPolynomialTensor (fun _ : σ => 1)
  apply dualLinearLift_logDerivative_eq
    (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot
    (⊤ : LieIdeal ℚ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))) φ φ.toLinearMap
    (fun u v _ => φ.map_lie u v) (F.realAdaptedPolynomialJet h x) (by trivial)
    (F.realification.adaptedPolynomialJet h (φ x))
  rw [dualLinearLift_apply, F.realAdaptedPolynomialJet_base, F.realAdaptedPolynomialJet_tangent]
  change dualConstantLie (φ x) + dualInfinitesimal (φ (F.realAdaptedDirectionalDerivative h x)) =
    dualConstantLie (φ x) + dualInfinitesimal (F.realification.adaptedDirectionalDerivative h (φ x))
  rw [F.realAdaptedDirectionalDerivative_tensor]

theorem exists_real_adapted_log_derivative_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1),
      F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp ((p + 2) ^ a)) x →
      ∀ h : σ → ℚ, (∀ i, |(h i : ℝ)| ≤ T i) →
      F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C))
        (F.realAdaptedLogDerivative h x) := by
  have hoperationsExists := exists_scaled_polynomial_dual_bound s 1
  obtain ⟨c, _, hoperations⟩ := hoperationsExists
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ a +
    Polynomial.C (s + 1) * (Polynomial.X + 1) + Polynomial.X + 2
  let B : Polynomial ℕ := (Q + Polynomial.C c) ^ c
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc T hT x hx h hh
  let t := (s + 1 : ℝ) * (p + 1)
  let q := (p + 2) ^ a + t + p + 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ha : 0 ≤ (p + 2) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have haq : (p + 2) ^ a ≤ q + 2 := by dsimp [q]; linarith
  have hfinal : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [B, Q, q, t, Polynomial.eval₂_pow] using hbound p hp
  have hfactor : (Fintype.card σ : ℝ) * s ≤ Real.exp t := by
    have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
    have hmul := mul_le_mul_of_nonneg_right hσ hs
    have hsmall : (Fintype.card σ : ℝ) * s ≤ t := by dsimp [t]; nlinarith
    exact hsmall.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp t))
  have hgain : (Fintype.card σ : ℝ) * s * Real.exp ((p + 2) ^ a) ≤ Real.exp (q + 2) := by
    apply (mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [q]
    linarith
  have hvalue := F.realAdaptedCoefficientBound_mono b ω hF (fun _ => 1) T hT
    (Real.exp_le_exp.mpr haq) x hx
  have hderivative := F.realAdaptedCoefficientBound_mono b ω hF (fun _ => 1) T hT hgain
    (F.realAdaptedDirectionalDerivative h x)
    (F.realAdaptedDirectionalDerivative_bound h b ω hF T hT (Real.exp_nonneg _) x hx hh)
  have hdual := (hoperations F b ω hF (fun _ : σ => 1) (by simp) H q hH hq
    (hι.trans hpq) (hσ.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq)) hc T hT).1
    (F.realAdaptedPolynomialJet h x)
    (by simpa only [F.realAdaptedPolynomialJet_base, pow_one] using hvalue)
    (by simpa only [F.realAdaptedPolynomialJet_tangent, pow_one] using hderivative)
  exact F.realAdaptedCoefficientBound_mono b ω hF (fun _ => 1) T hT
    (Real.exp_le_exp.mpr hfinal) _ hdual

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

theorem directionalDerivative_single {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] (i : σ) (P : VectorPolynomial σ ℚ L) :
    directionalDerivative (Pi.single i 1) P = (MvPolynomial.pderiv i).toLinearMap.rTensor L P := by
  simp [directionalDerivative, Pi.single_apply]

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adaptedLogDerivative_eq_formal (i : σ)
    (P : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (F.adaptedLogDerivative (Pi.single i 1) P : VectorPolynomial σ ℚ L) =
      formalLogDerivative (hnil := F.lowerCentralSeries_eq_bot) i ⟨P.val⟩ := by
  let φ := (F.adaptedLieSubalgebra (fun _ : σ => 1)).incl
  apply dualLinearLift_logDerivative_eq
    (VectorPolynomial.lowerCentralSeries_eq_bot (σ := σ) F.lowerCentralSeries_eq_bot)
    ⊤ φ φ.toLinearMap (fun a b _ => φ.map_lie a b)
    (F.adaptedPolynomialJet (Pi.single i 1) P) (by trivial)
    (formalPolynomialJetHom i (⟨P.val⟩ : PolynomialGroup σ F.lowerCentralSeries_eq_bot))
  rw [dualLinearLift_apply, F.adaptedPolynomialJet_base, F.adaptedPolynomialJet_tangent]
  change dualConstantLie P.val + dualInfinitesimal (directionalDerivative (Pi.single i 1) P.val) =
    dualConstantLie P.val + dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.val)
  rw [directionalDerivative_single]

theorem realAdaptedLogDerivative_eq_formal (i : σ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedPolynomialMap (fun _ => 1) (F.realAdaptedLogDerivative (Pi.single i 1) x) =
      formalLogDerivative (hnil := F.realification.lowerCentralSeries_eq_bot) i
        ⟨F.realAdaptedPolynomialMap (fun _ => 1) x⟩ := by
  have h := congrArg
    (fun P : F.realification.adaptedLieSubalgebra (fun _ : σ => 1) => P.val)
    (F.realAdaptedLogDerivative_tensor (Pi.single i 1) x)
  exact h.trans (F.realification.adaptedLogDerivative_eq_formal i
    (F.realAdaptedPolynomialTensor (fun _ => 1) x))

omit [Fintype σ] [DecidableEq σ] in
noncomputable def realFullPolynomialLie (v : σ → ℕ) :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra v) →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  (F.realification.adaptedLieSubalgebra v).incl.comp (F.realAdaptedPolynomialTensor v)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem realFullPolynomialLie_apply (v : σ → ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra v) :
    F.realFullPolynomialLie v x = F.realAdaptedPolynomialMap v x := rfl

omit [Fintype σ] [DecidableEq σ] in
noncomputable def realFullPolynomialHom (v : σ → ℕ) :
    F.RealAdaptedPolynomialGroup v →* PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.realFullPolynomialLie v)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem realFullPolynomialHom_coord (v : σ → ℕ) (P : F.RealAdaptedPolynomialGroup v) :
    (F.realFullPolynomialHom v P).coord = F.realAdaptedPolynomialMap v P.coord := rfl

omit [Fintype σ] [DecidableEq σ] in
theorem realAdaptedAdjoint_eq_formal (v : σ → ℕ) (P : F.RealAdaptedPolynomialGroup v)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra v) :
    F.realAdaptedPolynomialMap v (dualAdjoint P x) =
      dualAdjoint (F.realFullPolynomialHom v P) (F.realAdaptedPolynomialMap v x) :=
  map_dualAdjoint (F.realFullPolynomialLie v) P x

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realAdaptedDirectionalTangent
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (σ → ℚ) →ₗ[ℚ] (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) where
  toFun h := F.realAdaptedDirectionalDerivative h x
  map_add' h k := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r p =>
      change r ⊗ₜ[ℚ] (F.adaptedDirectionalTangent p (h + k)) =
        r ⊗ₜ[ℚ] (F.adaptedDirectionalTangent p h) + r ⊗ₜ[ℚ] (F.adaptedDirectionalTangent p k)
      rw [map_add, TensorProduct.tmul_add]
    | add x y hx hy => simp only [map_add, hx, hy]; abel
  map_smul' q h := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r p =>
      change r ⊗ₜ[ℚ] (F.adaptedDirectionalTangent p (q • h)) =
        q • (r ⊗ₜ[ℚ] (F.adaptedDirectionalTangent p h))
      rw [map_smul, TensorProduct.tmul_smul]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]

noncomputable def realLogDerivativeDirectionMap
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (σ → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :=
  (dualRealLogarithmicDifferential
    (hnil := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).realification.lowerCentralSeries_eq_bot)
      x).comp (realDirectionExtension (F.realAdaptedDirectionalTangent x))

theorem realLogDerivativeDirectionMap_rat
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) (h : σ → ℚ) :
    F.realLogDerivativeDirectionMap x (fun i => (h i : ℝ)) = F.realAdaptedLogDerivative h x := by
  change dualRealLogarithmicDifferential x
    (realDirectionExtension (F.realAdaptedDirectionalTangent x) (fun i => (h i : ℝ))) = _
  rw [realDirectionExtension_rat]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realShiftedCoefficientSubmodule (w : σ → ℕ) (k : ℕ) :
    Submodule ℝ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :=
  (F.shiftedPolynomialIdeal w k).toSubmodule.baseChange ℝ

theorem realShiftedCoefficient_lie_mem (w : σ → ℕ) (k : ℕ)
    (x y : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (hy : y ∈ F.realShiftedCoefficientSubmodule w k) :
    ⁅x, y⁆ ∈ F.realShiftedCoefficientSubmodule w k :=
  ((F.shiftedPolynomialIdeal w k).baseChange ℝ).lie_mem hy

abbrev RealFirstCoefficientModule (w : σ → ℕ) :=
  (F.realShiftedCoefficientSubmodule w 1) ⧸
    (F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype

noncomputable def realFirstCoefficientMap (w : σ → ℕ) :
    (F.realShiftedCoefficientSubmodule w 1) →ₗ[ℝ] F.RealFirstCoefficientModule w :=
  ((F.realShiftedCoefficientSubmodule w 2).comap
    (F.realShiftedCoefficientSubmodule w 1).subtype).mkQ

noncomputable def realFirstCoefficientAdjoint (w : σ → ℕ) (g : F.RealAdaptedPolynomialGroup w) :
    F.RealFirstCoefficientModule w ≃ₗ[ℝ] F.RealFirstCoefficientModule w :=
  invariantRealAdjointQuotient ⊤ (F.realShiftedCoefficientSubmodule w 1)
    (F.realShiftedCoefficientSubmodule w 2)
    (fun x _ y hy => F.realShiftedCoefficient_lie_mem w 1 x y hy)
    (fun x _ y hy => F.realShiftedCoefficient_lie_mem w 2 x y hy) g (by trivial)

@[simp] theorem realFirstCoefficientAdjoint_map (w : σ → ℕ) (g : F.RealAdaptedPolynomialGroup w)
    (x : F.realShiftedCoefficientSubmodule w 1) :
    F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientMap w x) =
      F.realFirstCoefficientMap w
        ⟨dualAdjoint g x.val, dualAdjoint_real_mem_of_invariant ⊤ _
          (fun a _ b hb => F.realShiftedCoefficient_lie_mem w 1 a b hb) g (by trivial) x.val x.property⟩ :=
  rfl

theorem realAdaptedDirectionalDerivative_mem_first [Fintype σ] (h : σ → ℚ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedDirectionalDerivative h x ∈ F.realShiftedCoefficientSubmodule (fun _ => 1) 1 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r p =>
    change r ⊗ₜ[ℚ] (F.adaptedDirectionalDerivative h p) ∈
      (F.shiftedPolynomialIdeal (fun _ => 1) 1).toSubmodule.baseChange ℝ
    exact Submodule.tmul_mem_baseChange_of_mem r (F.directionalDerivative_mem_next h p)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem realAdaptedLogDerivative_mem_first [Fintype σ] (h : σ → ℚ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedLogDerivative h x ∈ F.realShiftedCoefficientSubmodule (fun _ => 1) 1 := by
  apply dualLogDerivative_mem_of_invariant ⊤
    ((F.realShiftedCoefficientSubmodule (fun _ => 1) 1).restrictScalars ℚ)
    (fun a _ b hb => F.realShiftedCoefficient_lie_mem (fun _ => 1) 1 a b hb)
    (F.realAdaptedPolynomialJet h x) (by trivial)
  rw [F.realAdaptedPolynomialJet_tangent]
  exact F.realAdaptedDirectionalDerivative_mem_first h x

theorem realLogDerivativeDirectionMap_mem_first [Fintype σ]
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) (h : σ → ℝ) :
    F.realLogDerivativeDirectionMap x h ∈ F.realShiftedCoefficientSubmodule (fun _ => 1) 1 := by
  classical
  have he : h = ∑ i, h i • Pi.single i (1 : ℝ) := by ext j; simp [Pi.single_apply]
  rw [he, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  have hunit : (Pi.single i (1 : ℝ)) = (fun j => (((Pi.single i (1 : ℚ) : σ → ℚ) j) : ℝ)) := by
    ext j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  rw [hunit, F.realLogDerivativeDirectionMap_rat]
  exact F.realAdaptedLogDerivative_mem_first _ x

noncomputable def realFirstCoefficientDirectionMap [Fintype σ]
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (σ → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule (fun _ : σ => 1) :=
  (F.realFirstCoefficientMap (fun _ => 1)).comp
    ((F.realLogDerivativeDirectionMap x).codRestrict
      (F.realShiftedCoefficientSubmodule (fun _ => 1) 1) (F.realLogDerivativeDirectionMap_mem_first x))

theorem realFirstCoefficientDirectionMap_rat [Fintype σ]
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) (h : σ → ℚ) :
    F.realFirstCoefficientDirectionMap x (fun i => (h i : ℝ)) =
      F.realFirstCoefficientMap (fun _ => 1)
        ⟨F.realAdaptedLogDerivative h x, F.realAdaptedLogDerivative_mem_first h x⟩ := by
  apply congrArg (F.realFirstCoefficientMap (fun _ => 1))
  apply Subtype.ext
  exact F.realLogDerivativeDirectionMap_rat x h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def firstCoefficientRealEquiv :
    (ℝ ⊗[ℚ] F.FirstCoefficientModule w) ≃ₗ[ℝ] F.RealFirstCoefficientModule w :=
  realSubquotientEquiv (F.shiftedPolynomialIdeal w 1).toSubmodule (F.shiftedPolynomialIdeal w 2).toSubmodule

theorem firstCoefficientRealEquiv_map (x : ℝ ⊗[ℚ] (F.shiftedPolynomialIdeal w 1)) :
    F.firstCoefficientRealEquiv w ((F.firstCoefficientMap w).baseChange ℝ x) =
      F.realFirstCoefficientMap w (realificationSubmoduleEquiv (F.shiftedPolynomialIdeal w 1).toSubmodule x) :=
  realSubquotientEquiv_project _ _ x

noncomputable def realFirstCoefficientHorizontal :
    F.RealFirstCoefficientModule w →ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :=
  ((F.firstCoefficientHorizontal w).baseChange ℝ).comp (F.firstCoefficientRealEquiv w).symm.toLinearMap

noncomputable def realFirstCoefficientHorizontalSection :
    (ℝ ⊗[ℚ] (L ⧸ F.layer 2)) →ₗ[ℝ] F.RealFirstCoefficientModule w :=
  (F.firstCoefficientRealEquiv w).toLinearMap.comp ((F.firstCoefficientHorizontalSection w).baseChange ℝ)

theorem realFirstCoefficientHorizontal_section (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    F.realFirstCoefficientHorizontal w (F.realFirstCoefficientHorizontalSection w x) = x := by
  change (F.firstCoefficientHorizontal w).baseChange ℝ
    ((F.firstCoefficientRealEquiv w).symm (F.firstCoefficientRealEquiv w
      ((F.firstCoefficientHorizontalSection w).baseChange ℝ x))) = x
  rw [LinearEquiv.symm_apply_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r v => rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, F.firstCoefficientHorizontal_section]
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def realNormalizedFirstCoefficientMap :
    (ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) →ₗ[ℝ] F.RealFirstCoefficientModule w :=
  (F.firstCoefficientRealEquiv w).toLinearMap.comp ((F.normalizedFirstCoefficientMap w).baseChange ℝ)

theorem realNormalizedFirstCoefficientMap_range :
    LinearMap.range (F.realNormalizedFirstCoefficientMap w) = LinearMap.ker (F.realFirstCoefficientHorizontal w) := by
  have hr : LinearMap.range ((F.normalizedFirstCoefficientMap w).baseChange ℝ) =
      LinearMap.ker ((F.firstCoefficientHorizontal w).baseChange ℝ) := by
    rw [← realification_ker, ← F.normalizedFirstCoefficientMap_range w]
    have he := realification_map (⊤ : Submodule ℚ (F.normalizedRelativeSubmodule w))
      (F.normalizedFirstCoefficientMap w)
    simpa only [Submodule.map_top, Submodule.baseChange_top] using he.symm
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    change (F.firstCoefficientHorizontal w).baseChange ℝ
      ((F.firstCoefficientRealEquiv w).symm (F.firstCoefficientRealEquiv w
        ((F.normalizedFirstCoefficientMap w).baseChange ℝ p))) = 0
    rw [LinearEquiv.symm_apply_apply]
    exact hr.le ⟨p, rfl⟩
  · intro hx
    have hy : (F.firstCoefficientRealEquiv w).symm x ∈
        LinearMap.range ((F.normalizedFirstCoefficientMap w).baseChange ℝ) := hr.ge hx
    obtain ⟨p, hp⟩ := hy
    refine ⟨p, ?_⟩
    change F.firstCoefficientRealEquiv w ((F.normalizedFirstCoefficientMap w).baseChange ℝ p) = x
    rw [hp, LinearEquiv.apply_symm_apply]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealFirstCoefficientBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realShiftedCoefficient_eq_span (w : σ → ℕ) (k : ℕ) :
    F.realShiftedCoefficientSubmodule w k = Submodule.span ℝ
      ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ ''
        {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}) := by
  change (F.shiftedPolynomialIdeal w k).toSubmodule.baseChange ℝ = _
  rw [F.shiftedPolynomialIdeal_eq_span_monomialBasis b ω hF,
    Submodule.baseChange_span, Set.image_image]
  congr 2
  funext z
  exact (Basis.baseChange_apply ℝ (F.adaptedMonomialBasis b ω hF w) z).symm

noncomputable def realShiftedMonomialBasis (w : σ → ℕ) (k : ℕ) :
    Basis (ShiftedMonomialIndex w ω k) ℝ (F.realShiftedCoefficientSubmodule w k) :=
  supportedSubmoduleBasis ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ)
    (F.realShiftedCoefficientSubmodule w k)
    {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}
    (F.realShiftedCoefficient_eq_span b ω hF w k)

@[simp] theorem realShiftedMonomialBasis_coe (w : σ → ℕ) (k : ℕ) (z : ShiftedMonomialIndex w ω k) :
    (F.realShiftedMonomialBasis b ω hF w k z : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) =
      (F.adaptedMonomialBasis b ω hF w).baseChange ℝ z.val :=
  supportedSubmoduleBasis_coe _ _ _ _ z

theorem realShiftedMonomialBasis_repr (w : σ → ℕ) (k : ℕ)
    (x : F.realShiftedCoefficientSubmodule w k) (z : ShiftedMonomialIndex w ω k) :
    (F.realShiftedMonomialBasis b ω hF w k).repr x z =
      ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr x.val z.val :=
  supportedSubmoduleBasis_repr _ _ _ _ x z

theorem realShiftedCoefficient_next_eq_span (w : σ → ℕ) (k : ℕ) :
    (F.realShiftedCoefficientSubmodule w (k + 1)).comap (F.realShiftedCoefficientSubmodule w k).subtype =
      Submodule.span ℝ (F.realShiftedMonomialBasis b ω hF w k ''
        {z | Finsupp.weight w z.val.val.1 + (k + 1) ≤ ω z.val.val.2}) := by
  have hP := F.realShiftedCoefficient_eq_span b ω hF w k
  have hQ := F.realShiftedCoefficient_eq_span b ω hF w (k + 1)
  have hdata := supportedSubmoduleBasis_comap_span
    ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ)
    (F.realShiftedCoefficientSubmodule w k) (F.realShiftedCoefficientSubmodule w (k + 1))
    {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}
    {z | Finsupp.weight w z.val.1 + (k + 1) ≤ ω z.val.2} hP hQ
  exact hdata

noncomputable def realFirstCoefficientBasis (w : σ → ℕ) :
    Basis (FirstCoefficientIndex w ω) ℝ (F.RealFirstCoefficientModule w) :=
  (supportedQuotientBasis (F.realShiftedMonomialBasis b ω hF w 1)
    ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype)
    {z | Finsupp.weight w z.val.val.1 + 2 ≤ ω z.val.val.2}
    (F.realShiftedCoefficient_next_eq_span b ω hF w 1)).reindex (firstCoefficientSurvivorEquiv w ω)

@[simp] theorem realFirstCoefficientBasis_apply (w : σ → ℕ) (z : FirstCoefficientIndex w ω) :
    F.realFirstCoefficientBasis b ω hF w z =
      F.realFirstCoefficientMap w
        (F.realShiftedMonomialBasis b ω hF w 1 ((firstCoefficientSurvivorEquiv w ω).symm z).val) := by
  rw [realFirstCoefficientBasis, Basis.reindex_apply, supportedQuotientBasis_apply]
  rfl

theorem realFirstCoefficientBasis_repr_map (w : σ → ℕ)
    (x : F.realShiftedCoefficientSubmodule w 1) (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientMap w x) z =
      ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr x.val
        ((firstCoefficientSurvivorEquiv w ω).symm z).val.val := by
  rw [realFirstCoefficientBasis, Basis.repr_reindex_apply]
  change (supportedQuotientBasis _ _ _ _).repr
    (((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype).mkQ x) _ = _
  rw [supportedQuotientBasis_repr_mk, F.realShiftedMonomialBasis_repr]

theorem realFirstCoefficientBasis_polynomial_coordinate (w : σ → ℕ)
    (x : F.realShiftedCoefficientSubmodule w 1) (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientMap w x) z =
      (b.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap w x.val) z.val.1) z.val.2 := by
  rw [F.realFirstCoefficientBasis_repr_map]
  exact (F.realAdaptedPolynomialTensor_coordinates w b ω hF x.val
    ((firstCoefficientSurvivorEquiv w ω).symm z).val.val).symm

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FirstCoefficientDimension
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ)

def firstCoefficientIndexEmbedding : FirstCoefficientIndex w ω ↪ AdaptedBasisIndex w ω where
  toFun z := ⟨z.val, (Nat.le_add_right _ 1).trans z.property.le⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : AdaptedBasisIndex w ω => z.val) h

variable [Fintype σ] [Fintype ι] (s : ℕ) (hw : ∀ i, 0 < w i) (hω : ∀ i, ω i ≤ s)

@[instance_reducible] noncomputable def firstCoefficientIndexFintype :
    Fintype (FirstCoefficientIndex w ω) := by
  letI := adaptedBasisIndexFintype w ω s hw hω
  exact Fintype.ofInjective (firstCoefficientIndexEmbedding w ω) (firstCoefficientIndexEmbedding w ω).injective

include hw hω in
theorem firstCoefficientIndex_card_le [Fintype (FirstCoefficientIndex w ω)] :
    Fintype.card (FirstCoefficientIndex w ω) ≤ Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s := by
  let := adaptedBasisIndexFintype w ω s hw hω
  exact (Fintype.card_le_of_injective _ (firstCoefficientIndexEmbedding w ω).injective).trans
    (adaptedBasisIndex_card_le w ω s hw hω)

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hw hF

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedSymbolDimensions
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include hF hw in
theorem quotientTopSymbolIndex_finite : Finite (QuotientTopSymbolIndex s w ω) :=
  symbolBasisIndex_finite w (fun i : QuotientTopBasisIndex s ω => ω i.val) s hw
    (F.quotientTop.adaptedBasis_weight_le_step (F.quotientTopBasis e ω hF)
      (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF))

include hF hw in
theorem reducedSquareSymbolIndex_finite : Finite (ReducedSquareSymbolIndex s w ω) :=
  symbolBasisIndex_finite w (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω i.val) s hw
    (F.squareFiltration.quotientTop.adaptedBasis_weight_le_step (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF))

include hF hw in
theorem quotientTopSymbolIndex_card_le [Fintype (QuotientTopSymbolIndex s w ω)] :
    Fintype.card (QuotientTopSymbolIndex s w ω) ≤
      Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s := by
  have h := symbolBasisIndex_card_le w (fun i : QuotientTopBasisIndex s ω => ω i.val) s hw
    (F.quotientTop.adaptedBasis_weight_le_step (F.quotientTopBasis e ω hF)
      (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF))
  exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Fintype.card_subtype_le _)))

include hF hw in
theorem reducedSquareSymbolIndex_card_le [Fintype (ReducedSquareSymbolIndex s w ω)] :
    Fintype.card (ReducedSquareSymbolIndex s w ω) ≤
      2 * (Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s) := by
  have h := symbolBasisIndex_card_le w
    (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω i.val) s hw
    (F.squareFiltration.quotientTop.adaptedBasis_weight_le_step (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF))
  have hc : Fintype.card (ReducedSquareBasisIndex s ω) ≤ 2 * Fintype.card ι :=
    (Fintype.card_subtype_le _).trans (card_squareBasis_index_le ω)
  exact h.trans (by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right ((Fintype.card σ + 1) ^ s)
      (Nat.mul_le_mul_right (s + 1) hc))

def reducedMatrixParameter (s : ℕ) (p : ℝ) : ℝ :=
  3 * (p + (s + 2)) ^ (s + 2) * (p + 1) + 2 * p + 2

theorem reducedMatrixParameter_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ reducedMatrixParameter s p := by
  unfold reducedMatrixParameter
  positivity

theorem le_reducedMatrixParameter (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ reducedMatrixParameter s p := by
  have h : 0 ≤ 3 * (p + (s + 2)) ^ (s + 2) * (p + 1) := by positivity
  unfold reducedMatrixParameter
  linarith

include hF hw in
theorem reduced_lift_matrix_dimensions {κ : Type*} [Fintype κ]
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p) :
    2 * (Fintype.card ι : ℝ) ≤ reducedMatrixParameter s p ∧
      (Fintype.card (ReducedSquareSymbolIndex s w ω ⊕ QuotientTopSymbolIndex s w ω) : ℝ) ≤
        reducedMatrixParameter s p ∧
      ((Fintype.card (ReducedSquareSymbolIndex s w ω) * Fintype.card κ : ℕ) : ℝ) ≤
        reducedMatrixParameter s p := by
  let d := (p + (s + 2)) ^ (s + 2)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hB : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ d :=
    (Nat.cast_le.mpr (F.quotientTopSymbolIndex_card_le e ω hF w hw)).trans
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hS : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ 2 * d := by
    have hh := Nat.cast_le (α := ℝ).mpr (F.reducedSquareSymbolIndex_card_le e ω hF w hw)
    rw [Nat.cast_mul, Nat.cast_ofNat] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ) (by norm_num))
  have hlarge : 3 * d * (p + 1) ≤ reducedMatrixParameter s p := by
    dsimp only [reducedMatrixParameter, d]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have hnonneg : 0 ≤ 3 * d * (p + 1) := by positivity
    dsimp only [reducedMatrixParameter]
    change 2 * (Fintype.card ι : ℝ) ≤ 3 * d * (p + 1) + 2 * p + 2
    linarith
  · rw [Fintype.card_sum, Nat.cast_add]
    calc
      _ ≤ 3 * d := by linarith
      _ ≤ 3 * d * (p + 1) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (show 1 ≤ p + 1 by linarith)
          (show 0 ≤ 3 * d by positivity)
      _ ≤ _ := hlarge
  · rw [Nat.cast_mul]
    calc
      _ ≤ (2 * d) * p := mul_le_mul hS hκ (Nat.cast_nonneg _) (by positivity)
      _ ≤ (3 * d) * (p + 1) :=
        mul_le_mul (by linarith) (by linarith) hp (by positivity)
      _ ≤ _ := hlarge

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FastCoefficientDimensionBudget
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

def fastCoefficientMatrixParameter (s : ℕ) (p : ℝ) : ℝ :=
  reducedMatrixParameter s p + (p + (s + 3)) ^ (s + 3) * (p + 1) + p + 2

theorem fastCoefficientMatrixParameter_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ fastCoefficientMatrixParameter s p := by
  have hr := reducedMatrixParameter_nonneg s hp
  unfold fastCoefficientMatrixParameter
  positivity

theorem le_fastCoefficientMatrixParameter (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ fastCoefficientMatrixParameter s p := by
  have hr := reducedMatrixParameter_nonneg s hp
  have hd : 0 ≤ (p + (s + 3)) ^ (s + 3) * (p + 1) := by positivity
  unfold fastCoefficientMatrixParameter
  linarith

theorem fastCoefficient_matrix_dimensions
    {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)]
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p) :
    (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ fastCoefficientMatrixParameter s p ∧
    (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ fastCoefficientMatrixParameter s p ∧
    (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ fastCoefficientMatrixParameter s p ∧
    ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤
      fastCoefficientMatrixParameter s p := by
  have hr := (F.reduced_lift_matrix_dimensions e ω hF w hw hp hι hσ hκ).2.1
  rw [Fintype.card_sum, Nat.cast_add] at hr
  have hr0 := reducedMatrixParameter_nonneg s hp
  have hd0 : 0 ≤ (p + (s + 3)) ^ (s + 3) := by positivity
  have hfac0 : 0 ≤ (p + (s + 3)) ^ (s + 3) * (p + 1) := by positivity
  have hrq : reducedMatrixParameter s p ≤ fastCoefficientMatrixParameter s p := by
    unfold fastCoefficientMatrixParameter
    linarith
  have hdf : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ (p + (s + 3)) ^ (s + 3) := by
    have h := (Nat.cast_le (α := ℝ).mpr
      (firstCoefficientIndex_card_le w ω (s + 1) hw (F.adaptedBasis_weight_le_step e ω hF))).trans
      (symbol_dimension_bound_le_power (s + 1) (Fintype.card ι) (Fintype.card σ) hp hι hσ)
    simpa [Nat.cast_add, Nat.add_assoc, add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] using h
  have hdq : (p + (s + 3)) ^ (s + 3) * (p + 1) ≤ fastCoefficientMatrixParameter s p := by
    unfold fastCoefficientMatrixParameter
    linarith
  refine ⟨((le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hr).trans hrq,
    ((le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hr).trans hrq, ?_, ?_⟩
  · exact hdf.trans ((by nlinarith : (p + (s + 3)) ^ (s + 3) ≤
      (p + (s + 3)) ^ (s + 3) * (p + 1)).trans hdq)
  · rw [Nat.cast_mul]
    exact (mul_le_mul hdf (hκ.trans (by linarith)) (Nat.cast_nonneg _) hd0).trans hdq

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ReducedSquareCoefficientCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem reducedSquareDifference_basis_height (a : ReducedSquareBasisIndex s ω) (i : ι) :
    RationalHeightLE (e.repr (F.reducedSquareDifference (F.reducedSquareBasis e ω hF a)) i) 1 := by
  dsimp only [reducedSquareBasis]
  rw [F.squareFiltration.quotientTopBasis_apply, F.reducedSquareDifference_mk]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl j =>
    rw [F.adaptedSquareBasis_inl, sub_self, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl
  | inr j =>
    rw [F.adaptedSquareBasis_inr, sub_zero]
    exact basis_repr_height_one e j.val i

theorem reducedSquareCoefficientMap_repr_symbol
    (p : F.squareFiltration.quotientTop.adaptedLieSubalgebra w) (i : FirstCoefficientIndex w ω) :
    (F.firstCoefficientBasis e ω hF w).repr
      (F.reducedSquareCoefficientMap w (F.squareFiltration.quotientTop.polynomialSymbolMap w p)) i =
      e.repr (F.reducedSquareDifference (coefficients p.val i.val.1)) i.val.2 := by
  rw [F.reducedSquareCoefficientMap_symbol]
  change (F.firstCoefficientBasis e ω hF w).repr
    (F.firstCoefficientMap w ⟨(F.reducedSquareDifferenceRelative w p).val, _⟩) i = _
  rw [F.firstCoefficientBasis_repr_map, F.reducedSquareDifferenceRelative_coefficient]

theorem reducedSquareCoefficientMap_basis_repr [DecidableEq σ]
    (a : ReducedSquareSymbolIndex s w ω) (i : FirstCoefficientIndex w ω) :
    (F.firstCoefficientBasis e ω hF w).repr
      (F.reducedSquareCoefficientMap w (F.reducedSquareSymbolBasis e ω hF w a)) i =
      if a.val.1 = i.val.1 then
        e.repr (F.reducedSquareDifference (F.reducedSquareBasis e ω hF a.val.2)) i.val.2 else 0 := by
  change (F.firstCoefficientBasis e ω hF w).repr
    (F.reducedSquareCoefficientMap w
      (F.squareFiltration.quotientTop.polynomialSymbolBasis (F.reducedSquareBasis e ω hF)
        (fun j => squareBasisWeight ω j.val) (F.reducedSquareBasis_layers e ω hF) w a)) i = _
  rw [F.squareFiltration.quotientTop.polynomialSymbolBasis_apply,
    F.reducedSquareCoefficientMap_repr_symbol, F.squareFiltration.quotientTop.adaptedMonomialBasis_coe,
    coefficients_monomial]
  by_cases hai : a.val.1 = i.val.1
  · simp only [hai, Finsupp.single_eq_same, ite_true]
  · rw [Finsupp.single_eq_of_ne (Ne.symm hai), map_zero, map_zero,
      Finsupp.zero_apply, if_neg hai]

theorem reducedSquareCoefficientMap_basis_height
    (a : ReducedSquareSymbolIndex s w ω) (i : FirstCoefficientIndex w ω) :
    RationalHeightLE ((F.firstCoefficientBasis e ω hF w).repr
      (F.reducedSquareCoefficientMap w (F.reducedSquareSymbolBasis e ω hF w a)) i) 1 := by
  classical
  rw [F.reducedSquareCoefficientMap_basis_repr]
  split_ifs
  · exact F.reducedSquareDifference_basis_height e ω hF a.val.2 i.val.2
  · exact rationalHeightLE_zero le_rfl

theorem reducedSquareCoefficientMap_monomial_blocks
    (a : ReducedSquareSymbolIndex s w ω) (i : FirstCoefficientIndex w ω) (hai : i.val.1 ≠ a.val.1) :
    (F.firstCoefficientBasis e ω hF w).repr
      (F.reducedSquareCoefficientMap w (F.reducedSquareSymbolBasis e ω hF w a)) i = 0 := by
  classical
  rw [F.reducedSquareCoefficientMap_basis_repr, if_neg (Ne.symm hai)]

end Erdos3.NilpotentLieFiltration

end

end OAI

end


