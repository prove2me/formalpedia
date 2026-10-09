-- Prove2me | Definitions.Def_OAIErdos3B023
-- name    : OAIErdos3B023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T16:20:24.948156+00:00
-- url     : https://prove2.me/theorems/4a443998-2367-43c9-9454-e72d8d1bf4da
-- title:
--   OpenAI Erdős-3 split, definitions bundle 24 of 103
-- statement:
--   Definitions bundle 24 of 103 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B022`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 24 available.
--
--   Modules: `OAI.Erdos3.MultidegreeLieFiltration.exists_real_normalized_frozen_orbit`, `OAI.Erdos3.MultidegreeLieFiltration.realWeightedGroupInclusion`, `OAI.Erdos3.MultidegreeLieFiltration.realWeightedGroupInclusion_injective`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedWeightedOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedWeightedOrbit_eval`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjointRealLinearEquiv`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjointRealLinearEquiv_apply`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_real_mem_of_invariant`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_smul_real`, `OAI.Erdos3.NilpotentLieBCHGroup.invariantRealAdjoint`, `OAI.Erdos3.NilpotentLieBCHGroup.invariantRealAdjointQuotient`, `OAI.Erdos3.NilpotentLieBCHGroup.invariantRealAdjointQuotient_mk`, `OAI.Erdos3.NilpotentLieBCHGroup.invariantRealAdjoint_coe`, `OAI.Erdos3.NilpotentLieBCHGroup.invariantRealAdjoint_map_submodule`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationMap_incl_injective`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationMap_incl_mem`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationMap_incl_range`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationSubgroup`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationSubgroupHom`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationSubgroupHom_surjective`, `OAI.Erdos3.NilpotentLieBCHGroup.realification_grid_inv`, `OAI.Erdos3.NilpotentLieBCHGroup.realification_grid_mul`, `OAI.Erdos3.NilpotentLieBCHGroup.realification_subgroup_comap_incl`, `OAI.Erdos3.NilpotentLieFiltration.RealPolynomialSymbol`, `OAI.Erdos3.NilpotentLieFiltration.RealPolynomialSymbolGroup`, `OAI.Erdos3.NilpotentLieFiltration.SymbolRationalGrid`, `OAI.Erdos3.NilpotentLieFiltration.SymbolSlowBound`, `OAI.Erdos3.NilpotentLieFiltration.dualAdjoint_realBasis_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.exists_symbol_rational_inv_mul_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_symbol_rational_product_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_symbol_slow_mul_inv_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_symbol_slow_product_bound`, `OAI.Erdos3.NilpotentLieFiltration.gradedBasisSplitting`, `OAI.Erdos3.NilpotentLieFiltration.gradedBasisSplitting_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.gradedBasisSplitting_real_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.gradedSymbolPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.gradedSymbolPolynomialLie`, `OAI.Erdos3.NilpotentLieFiltration.gradedSymbolPolynomial_basis`, `OAI.Erdos3.NilpotentLieFiltration.gradedSymbolPolynomial_block_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.gradedSymbolPolynomial_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.gradedSymbolPolynomial_coefficient_of_ne`, `OAI.Erdos3.NilpotentLieFiltration.gradedSymbolPolynomial_injective`, `OAI.Erdos3.NilpotentLieFiltration.gradedSymbolPolynomial_lie_basis`, `OAI.Erdos3.NilpotentLieFiltration.mem_real_symbolPointwiseSubalgebra_iff_coefficients`, `OAI.Erdos3.NilpotentLieFiltration.mem_real_symbolPointwiseSubalgebra_iff_values`, `OAI.Erdos3.NilpotentLieFiltration.mem_symbolPointwiseSubalgebra_iff`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolBasis_repr_reindex`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedSymbolRepresentative`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedSymbolRepresentative_coe`, `OAI.Erdos3.NilpotentLieFiltration.realBasis_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.realGradeTruncation_eq_iff`, `OAI.Erdos3.NilpotentLieFiltration.realGradeTruncation_quotient`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_coefficient_tmul`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_coordinate_of_ne`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_injective`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_map_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolBasis_bracket_support`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolBasis_repr_reindex`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfPolynomial_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfPolynomial_eq_iff_symbolMap_eq`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfPolynomial_eq_zero_iff`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfPolynomial_representative`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_adapted`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_coefficient_of_ne`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_coefficient_splitting`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_constant`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_eq_map`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_eval₂`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_rational_coefficients`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolRepresentative_slow_coefficients`, `OAI.Erdos3.NilpotentLieFiltration.real_mem_layer_iff_basis_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.reindexSymbolBasisIndex`, `OAI.Erdos3.NilpotentLieFiltration.scaledRealPolynomialSymbolBasis`, `OAI.Erdos3.NilpotentLieFiltration.scaledRealPolynomialSymbolBasis_bound_iff`, `OAI.Erdos3.NilpotentLieFiltration.scaledRealPolynomialSymbolBasis_repr`, `OAI.Erdos3.NilpotentLieFiltration.scaledRealPolynomialSymbolBasis_structure`, `OAI.Erdos3.NilpotentLieFiltration.sub_realGradeTruncation_mem`, `OAI.Erdos3.NilpotentLieFiltration.symbolBasisIndex_monomial_ne_zero`, `OAI.Erdos3.NilpotentLieFiltration.symbolPointwiseSubalgebra`, `OAI.Erdos3.NilpotentLieFiltration.symbolPointwiseSubalgebra_blockInvariant`, `OAI.Erdos3.NilpotentLieFiltration.symbolPointwiseSubalgebra_eq_ker`, `OAI.Erdos3.NilpotentLieFiltration.symbolPointwiseSubalgebra_iInf`, `OAI.Erdos3.NilpotentLieFiltration.symbolRationalGrid_inv`, `OAI.Erdos3.NilpotentLieFiltration.symbolRationalGrid_mono`, `OAI.Erdos3.NilpotentLieFiltration.symbolRationalGrid_reindex_iff`, `OAI.Erdos3.NilpotentLieFiltration.symbolSlowBound_inv_iff`, `OAI.Erdos3.NilpotentLieFiltration.symbolSlowBound_log_norm`, `OAI.Erdos3.NilpotentLieFiltration.symbolSlowBound_mono`, `OAI.Erdos3.NilpotentLieFiltration.symbolSlowBound_reindex_iff`, `OAI.Erdos3.NilpotentLieFiltration.symbolSubalgebraQuotientMap`, `OAI.Erdos3.NilpotentLieFiltration.symbolSubalgebraQuotientMap_real_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.truncateRealGrades`, `OAI.Erdos3.NilpotentLieFiltration.truncateRealGrades_coord`, `OAI.Erdos3.NilpotentLieFiltration.truncateRealGrades_mem_of_quotient_mem`, `OAI.Erdos3.NilpotentLieFiltration.truncateRealGrades_quotient`, `OAI.Erdos3.NilpotentLieFiltration.truncateRealSymbol`, `OAI.Erdos3.NilpotentLieFiltration.truncateRealSymbol_coord`, `OAI.Erdos3.NilpotentLieFiltration.truncateRealSymbol_quotient`, `OAI.Erdos3.NilpotentLieFiltration.truncateRealSymbol_rational`, `OAI.Erdos3.NilpotentLieFiltration.truncateRealSymbol_slow`, `OAI.Erdos3.VectorPolynomial.coefficients_realificationLieEquiv_tmul`, `OAI.Erdos3.VectorPolynomial.coefficients_realificationLinearEquiv_tmul`, `OAI.Erdos3.VectorPolynomial.coefficients_realification_smul`, `OAI.Erdos3.VectorPolynomial.coefficients_smul_real`, `OAI.Erdos3.VectorPolynomial.eval_realificationLieEquiv_tmul`, `OAI.Erdos3.VectorPolynomial.lieTensorLeftComm`, `OAI.Erdos3.VectorPolynomial.mixedCoordinates`, `OAI.Erdos3.VectorPolynomial.mixedCoordinates_apply`, `OAI.Erdos3.VectorPolynomial.mixedCoordinates_symm_apply`, `OAI.Erdos3.VectorPolynomial.ofSupportedCoordinates`, `OAI.Erdos3.VectorPolynomial.ofSupportedCoordinates_apply`, `OAI.Erdos3.VectorPolynomial.ofSupportedCoordinates_apply_of_not_mem`, `OAI.Erdos3.VectorPolynomial.ofSupportedCoordinates_single`, `OAI.Erdos3.VectorPolynomial.realCoefficient`, `OAI.Erdos3.VectorPolynomial.realCoefficient_apply`, `OAI.Erdos3.VectorPolynomial.realLieAlgebra`, `OAI.Erdos3.VectorPolynomial.realModule`, `OAI.Erdos3.VectorPolynomial.realMonomial`, `OAI.Erdos3.VectorPolynomial.realMonomial_apply`, `OAI.Erdos3.VectorPolynomial.realScalarTower`, `OAI.Erdos3.VectorPolynomial.realificationLieEquiv`, `OAI.Erdos3.VectorPolynomial.realificationLieEquiv_smul`, `OAI.Erdos3.VectorPolynomial.realificationLieEquiv_tmul_tmul`, `OAI.Erdos3.VectorPolynomial.realificationLinearEquiv`, `OAI.Erdos3.VectorPolynomial.realificationLinearEquiv_eq_zero_iff`, `OAI.Erdos3.VectorPolynomial.realificationRealLinearEquiv`, `OAI.Erdos3.VectorPolynomial.realificationRealLinearEquiv_apply`, `OAI.Erdos3.VectorPolynomial.supportedCoordinates`, `OAI.Erdos3.VectorPolynomial.supportedCoordinates_apply`, `OAI.Erdos3.VectorPolynomial.supportedCoordinates_ofSupportedCoordinates`, `OAI.Erdos3.exists_bch_rational_product_bound`, `OAI.Erdos3.exists_real_bch_rational_closure`, `OAI.Erdos3.exists_real_bch_rational_product_bound`, `OAI.Erdos3.lieSubalgebra_mem_iInf`, `OAI.Erdos3.linear_map_lie_of_basis`, `OAI.Erdos3.mem_petalComparisonSpace`, `OAI.Erdos3.mem_realified_four_product_iff`, `OAI.Erdos3.pairDifferenceFunctional`, `OAI.Erdos3.pairDifferenceFunctional_apply`, `OAI.Erdos3.petalComparisonSpace`, `OAI.Erdos3.petalComparisonSpace_decompose`, `OAI.Erdos3.petalComparisonSpace_le_pi`, `OAI.Erdos3.petalComparisonSpace_top_tree`, `OAI.Erdos3.rational_inclusion_mem_realificationLieSubalgebra_iff`, `OAI.Erdos3.realDenominatorGrid_neg`, `OAI.Erdos3.realDenominatorGrid_subset_of_dvd`, `OAI.Erdos3.realDenominatorGrid_zero`, `OAI.Erdos3.realIdealAdjoint`, `OAI.Erdos3.realIdealAdjoint_inclusion`, `OAI.Erdos3.realIdealMap_adjoint`, `OAI.Erdos3.real_baseChange_iInf`, `OAI.Erdos3.real_baseChange_ker`, `OAI.Erdos3.real_baseChange_pi`, `OAI.Erdos3.real_four_alternating`, `OAI.Erdos3.real_four_projection`, `OAI.Erdos3.real_four_single`, `OAI.Erdos3.real_pair_projection`, `OAI.Erdos3.realificationLieHom_incl_injective`, `OAI.Erdos3.realificationLieSubalgebra`, `OAI.Erdos3.realificationLieSubalgebra_iInf`, `OAI.Erdos3.realificationLieSubalgebra_map`, `OAI.Erdos3.realificationLieSubalgebra_toSubmodule`, `OAI.Erdos3.realification_fourBalancedDependent`, `OAI.Erdos3.realification_fourCommonModulo`, `OAI.Erdos3.realification_ideal_intertwining`, `OAI.Erdos3.realification_map`, `OAI.Erdos3.realification_petalComparisonSpace`, `OAI.Erdos3.realification_sup`, `OAI.Erdos3.toLin_baseChange_coordinates`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B091
import Definitions.Def_OAIErdos3B092

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RationalBCHProducts
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realification_grid_mul (e : Basis ι ℚ L) (l m : ℕ) (hl : 0 < l)
    (hmul : ∀ a b : NilpotentLieBCHGroup L s hnil,
      e.equivFun a.coord ∈ denominatorGrid l → e.equivFun b.coord ∈ denominatorGrid l →
      e.equivFun (a * b).coord ∈ denominatorGrid m)
    (a b : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (ha : (e.baseChange ℝ).equivFun a.coord ∈ realDenominatorGrid l)
    (hb : (e.baseChange ℝ).equivFun b.coord ∈ realDenominatorGrid l) :
    (e.baseChange ℝ).equivFun (a * b).coord ∈ realDenominatorGrid m := by
  obtain ⟨aq, haq, heqa⟩ := (realification_grid_iff (hnil := hnil) e l hl a).mp ha
  obtain ⟨bq, hbq, heqb⟩ := (realification_grid_iff (hnil := hnil) e l hl b).mp hb
  rw [← heqa, ← heqb, ← map_mul, realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
  exact hmul aq bq haq hbq

theorem realification_grid_inv (e : Basis ι ℚ L) (l m : ℕ) (hl : 0 < l)
    (hinv : ∀ a : NilpotentLieBCHGroup L s hnil,
      e.equivFun a.coord ∈ denominatorGrid l → e.equivFun (a⁻¹).coord ∈ denominatorGrid m)
    (a : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (ha : (e.baseChange ℝ).equivFun a.coord ∈ realDenominatorGrid l) :
    (e.baseChange ℝ).equivFun (a⁻¹).coord ∈ realDenominatorGrid m := by
  obtain ⟨aq, haq, heqa⟩ := (realification_grid_iff (hnil := hnil) e l hl a).mp ha
  rw [← heqa, ← map_inv, realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
  exact hinv aq haq

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_real_bch_rational_closure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ a b : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil),
          (e.baseChange ℝ).equivFun a.coord ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun b.coord ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (a * b).coord ∈ realDenominatorGrid m) ∧
        (∀ a : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil),
          (e.baseChange ℝ).equivFun a.coord ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (a⁻¹).coord ∈ realDenominatorGrid m) := by
  obtain ⟨C, hC, hbound⟩ := exists_bch_rational_closure s
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hnil hp hd hH hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hmul⟩ := hbound e H p hp hd hH hc l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_, ?_⟩
  · exact NilpotentLieBCHGroup.realification_grid_mul (hnil := hnil) e l m hl
      (fun a b ha hb => hmul a.coord b.coord ha hb)
  · apply NilpotentLieBCHGroup.realification_grid_inv (hnil := hnil) e l m hl
    intro a ha
    change e.equivFun (-a.coord) ∈ denominatorGrid m
    rw [map_neg]
    exact denominatorGrid_subset_of_dvd hlm (denominatorGrid_neg l ha)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realDenominatorGrid_zero {ι : Type*} (l : ℕ) :
    (0 : ι → ℝ) ∈ realDenominatorGrid l := by
  exact ⟨0, by ext i; simp⟩

theorem realDenominatorGrid_subset_of_dvd {ι : Type*} {l m : ℕ} (hl : 0 < l) (hlm : l ∣ m) :
    (realDenominatorGrid l : Set (ι → ℝ)) ⊆ realDenominatorGrid m := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := realDenominatorGrid_exists_rational l hl x hx
  exact (real_cast_mem_denominatorGrid_iff m y).mpr (denominatorGrid_subset_of_dvd hlm hy)

theorem exists_real_bch_rational_product_bound (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (lieStructureConstants e i j z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)),
          rs.length ≤ k →
          (∀ r ∈ rs, (e.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid l) →
          (e.baseChange ℝ).equivFun rs.prod.coord ∈ realDenominatorGrid m := by
  induction k with
  | zero =>
    refine ⟨2, by omega, ?_⟩
    intro ι L _ _ _ e H p hnil hp hd hH hc l hl hlp
    refine ⟨l, hl, hlp.trans (Real.exp_le_exp.mpr (le_power_budget hp (by omega))), dvd_refl l, ?_⟩
    intro rs hlen hrs
    have hrs0 : rs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst rs
    simpa only [List.prod_nil, NilpotentLieBCHGroup.coord_one, map_zero] using
      (realDenominatorGrid_zero (ι := ι) l)
  | succ k ih =>
    obtain ⟨K, hK, hprod⟩ := ih
    obtain ⟨J, _, hmul⟩ := exists_real_bch_rational_closure s
    let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C K) ^ K + Polynomial.C J) ^ J
    obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
    refine ⟨C, hC, ?_⟩
    intro ι L _ _ _ e H p hnil hp hd hH hc l hl hlp
    obtain ⟨m₁, hm₁, hm₁p, hlm₁, hprod₁⟩ := hprod e H p hnil hp hd hH hc l hl hlp
    let q : ℝ := (p + K) ^ K
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hpq : p ≤ q := by
      apply (show p ≤ p + K from le_add_of_nonneg_right (Nat.cast_nonneg K)).trans
      have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
      simpa only [pow_one] using pow_le_pow_right₀
        (show (1 : ℝ) ≤ p + K by linarith) (show 1 ≤ K by omega)
    obtain ⟨m₂, hm₂, hm₂p, hm₁m₂, hmul₂, _⟩ := hmul e H q hnil hq (hd.trans hpq)
      (hH.trans (Real.exp_le_exp.mpr hpq)) hc m₁ hm₁ hm₁p
    have hpoly : (q + J) ^ J ≤ (p + C) ^ C := by
      simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
    refine ⟨m₂, hm₂, hm₂p.trans (Real.exp_le_exp.mpr hpoly), hlm₁.trans hm₁m₂, ?_⟩
    intro rs hlen hrs
    cases rs with
    | nil =>
      simpa only [List.prod_nil, NilpotentLieBCHGroup.coord_one, map_zero] using
        (realDenominatorGrid_zero (ι := ι) m₂)
    | cons r rs =>
      rw [List.prod_cons]
      apply hmul₂
      · exact realDenominatorGrid_subset_of_dvd hl hlm₁ (hrs r (List.mem_cons_self))
      · apply hprod₁ rs (Nat.le_of_succ_le_succ hlen)
        exact fun x hx => hrs x (List.mem_cons_of_mem r hx)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem exists_bch_rational_product_bound (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (lieStructureConstants e i j z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List (NilpotentLieBCHGroup L s hnil), rs.length ≤ k →
          (∀ r ∈ rs, e.equivFun r.coord ∈ denominatorGrid l) →
          e.equivFun rs.prod.coord ∈ denominatorGrid m := by
  have hrealExists := exists_real_bch_rational_product_bound s k
  obtain ⟨C, hC, hreal⟩ := hrealExists
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hnil hp hd hH hc l hl hlp
  have hproductsExists := hreal e H p hnil hp hd hH hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hproducts⟩ := hproductsExists
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro rs hlen hrs
  have hinputs : ∀ r ∈ rs.map (realificationHom (hnil := hnil)),
      (e.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid l := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    rw [realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
    exact hrs q hq
  have hout := hproducts (rs.map (realificationHom (hnil := hnil)))
    (by simpa only [List.length_map] using hlen) hinputs
  rw [← map_list_prod, realificationHom_coordinates, real_cast_mem_denominatorGrid_iff] at hout
  exact hout

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolAbsorptionBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

abbrev RealPolynomialSymbol {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ) :=
  ℝ ⊗[ℚ] F.PolynomialSymbol w

abbrev RealPolynomialSymbolGroup {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ) :=
  NilpotentLieBCHGroup (F.RealPolynomialSymbol w) s
    (realification_lowerCentralSeries_eq_bot (F.polynomialSymbol_lowerCentralSeries_eq_bot w))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realPolynomialSymbolBasis_bracket_support (u v z : SymbolBasisIndex w ω)
    (h : ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
      ⁅(F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ u,
        (F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ v⁆ z ≠ 0) :
    u.val.1 + v.val.1 = z.val.1 := by
  classical
  by_contra hn
  apply h
  rw [realLieBasis_structure]
  change (((F.polynomialSymbolBasis b ω hlayers w).repr
    ⁅F.polynomialSymbolBasis b ω hlayers w u,
      F.polynomialSymbolBasis b ω hlayers w v⁆ z : ℚ) : ℝ) = 0
  simp only [F.polynomialSymbolBasis_bracket, hn, ↓reduceIte, Rat.cast_zero]

noncomputable def scaledRealPolynomialSymbolBasis (T : σ → ℝ) (hT : ∀ i, 0 < T i) :
    Basis (SymbolBasisIndex w ω) ℝ (F.RealPolynomialSymbol w) :=
  inverseScaledBasis ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
    (fun z => monomialScale T z.val.1) (fun z => monomialScale_pos T hT z.val.1)

theorem scaledRealPolynomialSymbolBasis_repr (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x : F.RealPolynomialSymbol w) (z : SymbolBasisIndex w ω) :
    (F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT).repr x z =
      monomialScale T z.val.1 *
        ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x z :=
  inverseScaledBasis_repr _ _ _ _ _

theorem scaledRealPolynomialSymbolBasis_structure (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (u v z : SymbolBasisIndex w ω) :
    (F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT).repr
      ⁅F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT u,
        F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT v⁆ z =
      (lieStructureConstants (F.polynomialSymbolBasis b ω hlayers w) u v z : ℝ) := by
  apply Eq.trans (inverseScaledBasis_bracket _ _ _ ?_ u v z)
  · exact realLieBasis_structure _ u v z
  · intro i j k h
    have hijk := F.realPolynomialSymbolBasis_bracket_support b ω hlayers w i j k h
    rw [← hijk, monomialScale_add]

theorem scaledRealPolynomialSymbolBasis_bound_iff (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x : F.RealPolynomialSymbol w) (z : SymbolBasisIndex w ω) (M : ℝ) :
    |(F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT).repr x z| ≤ M ↔
      |((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x z| ≤
        M / monomialScale T z.val.1 := by
  rw [F.scaledRealPolynomialSymbolBasis_repr, abs_mul,
    abs_of_pos (monomialScale_pos T hT z.val.1), le_div_iff₀ (monomialScale_pos T hT z.val.1)]
  rw [mul_comm]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

theorem realDenominatorGrid_neg {ι : Type*} (l : ℕ) {x : ι → ℝ}
    (hx : x ∈ realDenominatorGrid l) : -x ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨-z, ?_⟩
  funext i
  have hi := congrFun hz i
  change (z i : ℝ) = (l : ℝ) * x i at hi
  change ((-z i : ℤ) : ℝ) = (l : ℝ) * (-x i)
  rw [Int.cast_neg, hi, mul_neg]

namespace NilpotentLieFiltration

open Module

def SymbolRationalGrid {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (l : ℕ) (g : F.RealPolynomialSymbolGroup w) : Prop :=
  (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr g.coord z)
    ∈ realDenominatorGrid l

theorem symbolRationalGrid_inv {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (l : ℕ) {g : F.RealPolynomialSymbolGroup w}
    (hg : F.SymbolRationalGrid b ω hlayers w l g) :
    F.SymbolRationalGrid b ω hlayers w l g⁻¹ := by
  change (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr (-g.coord) z)
    ∈ realDenominatorGrid l
  have heq : (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr (-g.coord) z) =
      -(fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr g.coord z) := by
    funext z
    simp only [map_neg, Finsupp.neg_apply, Pi.neg_apply]
  rw [heq]
  exact realDenominatorGrid_neg l hg

theorem exists_symbol_rational_product_bound (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List (F.RealPolynomialSymbolGroup w), rs.length ≤ k →
          (∀ r ∈ rs, F.SymbolRationalGrid b ω hlayers w l r) →
          F.SymbolRationalGrid b ω hlayers w m rs.prod := by
  obtain ⟨K, _, hK⟩ := exists_real_bch_rational_product_bound s k
  let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let B := F.polynomialSymbolBasis b ω hlayers w
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℝ) from le_add_of_nonneg_right (by positivity)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hstruct : ∀ i j z, RationalHeightLE (lieStructureConstants B i j z) H :=
    F.polynomialSymbolBasis_bracket_height b ω hlayers w hH hb
  obtain ⟨m, hm, hmp, hlm, hprod⟩ := hK B H q
    (F.polynomialSymbol_lowerCentralSeries_eq_bot w) hq hdim
    (hHp.trans (Real.exp_le_exp.mpr hpq)) hstruct l hl (hlp.trans (Real.exp_le_exp.mpr hpq))
  have hpoly : (q + K) ^ K ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  exact ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hpoly), hlm, hprod⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def SymbolSlowBound {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (T : σ → ℝ) (M : ℝ) (g : F.RealPolynomialSymbolGroup w) : Prop :=
  ∀ z : SymbolBasisIndex w ω,
    |((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr g.coord z| ≤
      M / monomialScale T z.val.1

@[simp] theorem symbolSlowBound_inv_iff {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (T : σ → ℝ) (M : ℝ) (g : F.RealPolynomialSymbolGroup w) :
    F.SymbolSlowBound b ω hlayers w T M g⁻¹ ↔ F.SymbolSlowBound b ω hlayers w T M g := by
  simp only [SymbolSlowBound, NilpotentLieBCHGroup.coord_inv, map_neg, Finsupp.neg_apply, abs_neg]

theorem exists_symbol_slow_product_bound (s a k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ rs : List (F.RealPolynomialSymbolGroup w), rs.length ≤ k →
      (∀ r ∈ rs, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) r) →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) rs.prod := by
  obtain ⟨K, _, hK⟩ := exists_bch_fixed_product_exp_bound s a k
  let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H p hH hp hι hσ hHp hb T hT rs hlen hrs
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let B := F.polynomialSymbolBasis b ω hlayers w
  let E := F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℝ) from le_add_of_nonneg_right (by positivity)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hstruct : ∀ i j z, algebraMap ℚ ℝ (lieStructureConstants B i j z) = E.repr ⁅E i, E j⁆ z :=
    fun i j z => (F.scaledRealPolynomialSymbolBasis_structure b ω hlayers w T hT i j z).symm
  have hheight : ∀ i j z, RationalHeightLE (lieStructureConstants B i j z) H :=
    F.polynomialSymbolBasis_bracket_height b ω hlayers w hH hb
  have hinput : ∀ r ∈ rs, ∀ z, |E.repr r.coord z| ≤ Real.exp ((q + 2) ^ a) := by
    intro r hr z
    have hscaled := (F.scaledRealPolynomialSymbolBasis_bound_iff b ω hlayers w T hT
      r.coord z (Real.exp ((p + 2) ^ a))).mpr (hrs r hr z)
    exact hscaled.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a))
  have hpoly : (q + K) ^ K ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  intro z
  apply (F.scaledRealPolynomialSymbolBasis_bound_iff b ω hlayers w T hT
    rs.prod.coord z (Real.exp ((p + C) ^ C))).mp
  exact (hK E (lieStructureConstants B) H q
    (realification_lowerCentralSeries_eq_bot (F.polynomialSymbol_lowerCentralSeries_eq_bot w))
    rs hstruct hq hdim hlen (hHp.trans (Real.exp_le_exp.mpr hpq)) hheight hinput z).trans
      (Real.exp_le_exp.mpr hpoly)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

include hlayers

theorem symbolBasisIndex_monomial_ne_zero (z : SymbolBasisIndex w ω) : z.val.1 ≠ 0 := by
  intro hz
  have hd := z.property
  rw [hz, map_zero] at hd
  have hp := F.adaptedBasis_weight_pos b ω hlayers z.val.2
  omega

theorem symbolSlowBound_log_norm [Fintype (SymbolBasisIndex w ω)]
    (T : σ → ℝ) {R M : ℝ} (hR : 1 ≤ R) (hT : ∀ i, R ≤ T i) (hM : 0 ≤ M)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hlayers w T M g) :
    ‖((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).equivFun g.coord‖ ≤ M / R := by
  apply (pi_norm_le_iff_of_nonneg (div_nonneg hM (zero_le_one.trans hR))).mpr
  intro z
  change |((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr g.coord z| ≤ M / R
  have hscale := le_monomialScale_of_ne_zero T hR hT
    (F.symbolBasisIndex_monomial_ne_zero b ω hlayers w z)
  exact (hg z).trans (div_le_div_of_nonneg_left hM (zero_lt_one.trans_le hR) hscale)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem sub_realGradeTruncation_mem (j : ℕ) (x : ℝ ⊗[ℚ] L) :
    x - basisBelowProjection (b.baseChange ℝ) w j x ∈ F.realification.layer j := by
  change x - basisBelowProjection (b.baseChange ℝ) w j x ∈ (F.realLayer j).toSubmodule
  rw [F.realLayer_eq_span_basis b j {i | j ≤ w i} (hlayers j)]
  exact sub_basisBelowProjection_mem (b.baseChange ℝ) w j x

include hlayers in
theorem realGradeTruncation_eq_iff (j : ℕ) (x y : ℝ ⊗[ℚ] L) :
    basisBelowProjection (b.baseChange ℝ) w j x = basisBelowProjection (b.baseChange ℝ) w j y ↔
      x - y ∈ F.realification.layer j := by
  change _ ↔ x - y ∈ (F.realLayer j).toSubmodule
  rw [F.realLayer_eq_span_basis b j {i | j ≤ w i} (hlayers j)]
  exact basisBelowProjection_eq_iff (b.baseChange ℝ) w j x y

include hlayers in
theorem realGradeTruncation_quotient (j : ℕ) (x : ℝ ⊗[ℚ] L) :
    lieQuotientMap (F.realification.layerIdeal j) (basisBelowProjection (b.baseChange ℝ) w j x) =
      lieQuotientMap (F.realification.layerIdeal j) x := by
  have h := (lieQuotientMap_eq_zero (F.realification.layerIdeal j) _).mpr
    (F.sub_realGradeTruncation_mem b w hlayers j x)
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

noncomputable def truncateRealGrades (j : ℕ) (g : F.realification.Group) : F.realification.Group :=
  ⟨basisBelowProjection (b.baseChange ℝ) w j g.coord⟩

@[simp] theorem truncateRealGrades_coord (j : ℕ) (g : F.realification.Group) :
    (F.truncateRealGrades b w j g).coord = basisBelowProjection (b.baseChange ℝ) w j g.coord := rfl

include hlayers in
theorem truncateRealGrades_quotient (j : ℕ) (g : F.realification.Group) :
    NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) (F.truncateRealGrades b w j g) =
      NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) g := by
  apply NilpotentLieBCHGroup.ext
  exact F.realGradeTruncation_quotient b w hlayers j g.coord

include hlayers in

theorem truncateRealGrades_mem_of_quotient_mem (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule)
    (j : ℕ) (g : F.realification.Group)
    (hg : NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) g ∈
      (NilpotentLieBCHGroup.realLieSubgroup (hnil := F.realification.lowerCentralSeries_eq_bot) U).map
        (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j))) :
    (F.truncateRealGrades b w j g).coord ∈ U := by
  obtain ⟨u, hu, heq⟩ := Subgroup.mem_map.mp hg
  have hdiff : g.coord - u.coord ∈ F.realification.layer j := by
    apply (lieQuotientMap_eq_zero (F.realification.layerIdeal j) _).mp
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg NilpotentLieBCHGroup.coord heq).symm
  have ht := (F.realGradeTruncation_eq_iff b w hlayers j g.coord u.coord).mpr hdiff
  change basisBelowProjection (b.baseChange ℝ) w j g.coord ∈ U
  rw [ht]
  exact hU.below_mem (b.baseChange ℝ) w U.toSubmodule j u.coord hu

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) (v : σ → ℕ)

theorem symbolSlowBound_mono (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M N : ℝ} (hMN : M ≤ N)
    (g : F.RealPolynomialSymbolGroup v) (hg : F.SymbolSlowBound b w hlayers v T M g) :
    F.SymbolSlowBound b w hlayers v T N g := by
  intro z
  exact (hg z).trans (div_le_div_of_nonneg_right hMN (le_of_lt (monomialScale_pos T hT z.val.1)))

theorem symbolRationalGrid_mono {l m : ℕ} (hl : 0 < l) (hlm : l ∣ m)
    (g : F.RealPolynomialSymbolGroup v) (hg : F.SymbolRationalGrid b w hlayers v l g) :
    F.SymbolRationalGrid b w hlayers v m g :=
  realDenominatorGrid_subset_of_dvd hl hlm hg

noncomputable def truncateRealSymbol (j : ℕ) (g : F.RealPolynomialSymbolGroup v) :
    F.RealPolynomialSymbolGroup v :=
  (F.polynomialSymbolFiltration v).truncateRealGrades
    (F.polynomialSymbolBasis b w hlayers v) (fun z => w z.val.2) j g

@[simp] theorem truncateRealSymbol_coord (j : ℕ) (g : F.RealPolynomialSymbolGroup v) :
    (F.truncateRealSymbol b w hlayers v j g).coord =
      basisBelowProjection ((F.polynomialSymbolBasis b w hlayers v).baseChange ℝ)
        (fun z => w z.val.2) j g.coord := rfl

theorem truncateRealSymbol_slow (j : ℕ) (g : F.RealPolynomialSymbolGroup v)
    (T : σ → ℝ) (M : ℝ) (hg : F.SymbolSlowBound b w hlayers v T M g) :
    F.SymbolSlowBound b w hlayers v T M (F.truncateRealSymbol b w hlayers v j g) := by
  intro z
  exact (basisCoordinateProjection_abs_repr_le
    ((F.polynomialSymbolBasis b w hlayers v).baseChange ℝ) {z | w z.val.2 < j} g.coord z).trans (hg z)

theorem truncateRealSymbol_rational (j : ℕ) (g : F.RealPolynomialSymbolGroup v)
    (l : ℕ) (hg : F.SymbolRationalGrid b w hlayers v l g) :
    F.SymbolRationalGrid b w hlayers v l (F.truncateRealSymbol b w hlayers v j g) :=
  basisCoordinateProjection_real_grid ((F.polynomialSymbolBasis b w hlayers v).baseChange ℝ)
    {z | w z.val.2 < j} l g.coord hg

theorem truncateRealSymbol_quotient (j : ℕ) (g : F.RealPolynomialSymbolGroup v) :
    NilpotentLieBCHGroup.quotientHom
        ((F.polynomialSymbolFiltration v).realification.layerIdeal j)
        (F.truncateRealSymbol b w hlayers v j g) =
      NilpotentLieBCHGroup.quotientHom ((F.polynomialSymbolFiltration v).realification.layerIdeal j) g :=
  (F.polynomialSymbolFiltration v).truncateRealGrades_quotient
    (F.polynomialSymbolBasis b w hlayers v) (fun z => w z.val.2)
    (F.polynomialSymbolFiltration_layer b w hlayers v) j g

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ : Type*}

def reindexSymbolBasisIndex (w : σ → ℕ) (ω : ι → ℕ) (e : ι ≃ κ) :
    SymbolBasisIndex w ω ≃ SymbolBasisIndex w (fun k => ω (e.symm k)) where
  toFun z := ⟨(z.val.1, e z.val.2), by simpa only [Equiv.symm_apply_apply] using z.property⟩
  invFun z := ⟨(z.val.1, e.symm z.val.2), z.property⟩
  left_inv z := by apply Subtype.ext; simp only [Equiv.symm_apply_apply]
  right_inv z := by apply Subtype.ext; simp only [Equiv.apply_symm_apply]

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (e : ι ≃ κ)
  (hF' : ∀ j, F.layer j = Submodule.span ℚ ((b.reindex e) '' {k | j ≤ ω (e.symm k)}))
  (w : σ → ℕ)

theorem polynomialSymbolBasis_repr_reindex (x : F.PolynomialSymbol w)
    (z : SymbolBasisIndex w (fun k => ω (e.symm k))) :
    (F.polynomialSymbolBasis (b.reindex e) (fun k => ω (e.symm k)) hF' w).repr x z =
      (F.polynomialSymbolBasis b ω hF w).repr x ((reindexSymbolBasisIndex w ω e).symm z) := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.polynomialSymbolBasis_repr_map, F.polynomialSymbolBasis_repr_map,
    Basis.repr_reindex_apply]
  rfl

theorem realPolynomialSymbolBasis_repr_reindex (x : F.RealPolynomialSymbol w)
    (z : SymbolBasisIndex w (fun k => ω (e.symm k))) :
    ((F.polynomialSymbolBasis (b.reindex e) (fun k => ω (e.symm k)) hF' w).baseChange ℝ).repr x z =
      ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr x
        ((reindexSymbolBasisIndex w ω e).symm z) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul,
      F.polynomialSymbolBasis_repr_reindex b ω hF e hF' w]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem symbolSlowBound_reindex_iff (T : σ → ℝ) (M : ℝ) (g : F.RealPolynomialSymbolGroup w) :
    F.SymbolSlowBound (b.reindex e) (fun k => ω (e.symm k)) hF' w T M g ↔
      F.SymbolSlowBound b ω hF w T M g := by
  constructor
  · intro hg z
    have hz := hg (reindexSymbolBasisIndex w ω e z)
    rw [F.realPolynomialSymbolBasis_repr_reindex b ω hF e hF' w,
      Equiv.symm_apply_apply] at hz
    exact hz
  · intro hg z
    rw [F.realPolynomialSymbolBasis_repr_reindex b ω hF e hF' w]
    exact hg ((reindexSymbolBasisIndex w ω e).symm z)

theorem symbolRationalGrid_reindex_iff (l : ℕ) (g : F.RealPolynomialSymbolGroup w) :
    F.SymbolRationalGrid (b.reindex e) (fun k => ω (e.symm k)) hF' w l g ↔
      F.SymbolRationalGrid b ω hF w l g := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun z => a (reindexSymbolBasisIndex w ω e z), ?_⟩
    funext z
    have hz := congrFun ha (reindexSymbolBasisIndex w ω e z)
    change (a (reindexSymbolBasisIndex w ω e z) : ℝ) = (l : ℝ) *
      ((F.polynomialSymbolBasis (b.reindex e) (fun k => ω (e.symm k)) hF' w).baseChange ℝ).repr
        g.coord (reindexSymbolBasisIndex w ω e z) at hz
    rw [F.realPolynomialSymbolBasis_repr_reindex b ω hF e hF' w,
      Equiv.symm_apply_apply] at hz
    exact hz
  · rintro ⟨a, ha⟩
    refine ⟨fun z => a ((reindexSymbolBasisIndex w ω e).symm z), ?_⟩
    funext z
    change (a ((reindexSymbolBasisIndex w ω e).symm z) : ℝ) = (l : ℝ) *
      ((F.polynomialSymbolBasis (b.reindex e) (fun k => ω (e.symm k)) hF' w).baseChange ℝ).repr
        g.coord z
    rw [F.realPolynomialSymbolBasis_repr_reindex b ω hF e hF' w]
    exact congrFun ha ((reindexSymbolBasisIndex w ω e).symm z)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_symbol_slow_mul_inv_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ E A : F.RealPolynomialSymbolGroup w,
      F.SymbolSlowBound b ω hF w T (Real.exp (p + 2)) E →
      F.SymbolSlowBound b ω hF w T (Real.exp (p + 2)) A →
      F.SymbolSlowBound b ω hF w T (Real.exp ((p + C) ^ C)) (E * A⁻¹) := by
  obtain ⟨C, hC, hprod⟩ := exists_symbol_slow_product_bound s 1 2
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hc T hT E A hE hA
  have hinputs : ∀ x ∈ [E, A⁻¹], F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ 1)) x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simpa only [pow_one] using hE
    · simpa only [pow_one] using (F.symbolSlowBound_inv_iff b ω hF w T _ A).mpr hA
  simpa only [List.prod_cons, List.prod_nil, mul_one] using
    hprod F b ω hF w hw H p hH hp hι hσ hHp hc T hT [E, A⁻¹] (by simp) hinputs

theorem exists_symbol_rational_inv_mul_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ D R : F.RealPolynomialSymbolGroup w,
          F.SymbolRationalGrid b ω hF w l D → F.SymbolRationalGrid b ω hF w l R →
          F.SymbolRationalGrid b ω hF w m (D⁻¹ * R) := by
  obtain ⟨C, hC, hprod⟩ := exists_symbol_rational_product_bound s 2
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hproducts⟩ := hprod F b ω hF w hw H p hH hp hι hσ hHp hc l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro D R hD hR
  have hinputs : ∀ x ∈ [D⁻¹, R], F.SymbolRationalGrid b ω hF w l x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact F.symbolRationalGrid_inv b ω hF w l hD
    · exact hR
  simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts [D⁻¹, R] (by simp) hinputs

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealGradedSymbolPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

variable {σ ι R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

noncomputable def mixedCoordinates (b : Basis ι S V) :
    VectorPolynomial σ R V ≃ₗ[R] ((σ →₀ ℕ) × ι) →₀ S :=
  coefficients.trans ((Finsupp.mapRange.linearEquiv (b.repr.restrictScalars R)).trans
    (Finsupp.curryLinearEquiv R).symm)

@[simp] theorem mixedCoordinates_apply (b : Basis ι S V)
    (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) (i : ι) :
    mixedCoordinates b p (α, i) = b.repr (coefficients p α) i := rfl

@[simp] theorem mixedCoordinates_symm_apply (b : Basis ι S V)
    (c : ((σ →₀ ℕ) × ι) →₀ S) (α : σ →₀ ℕ) (i : ι) :
    b.repr (coefficients ((mixedCoordinates b).symm c : VectorPolynomial σ R V) α) i =
      c (α, i) := by
  rw [← mixedCoordinates_apply, LinearEquiv.apply_symm_apply]

noncomputable def ofSupportedCoordinates (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) : (A →₀ S) →ₗ[R] VectorPolynomial σ R V :=
  (mixedCoordinates b).symm.toLinearMap.comp (Finsupp.lmapDomain S R Subtype.val)

@[simp] theorem ofSupportedCoordinates_apply (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) (c : A →₀ S) (z : A) :
    b.repr (coefficients (ofSupportedCoordinates (R := R) b A c) z.val.1) z.val.2 = c z := by
  change mixedCoordinates b ((mixedCoordinates b).symm _) z.val = _
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.mapDomain_apply Subtype.val_injective c z

theorem ofSupportedCoordinates_apply_of_not_mem (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) (c : A →₀ S) (α : σ →₀ ℕ) (i : ι)
    (h : (α, i) ∉ A) :
    b.repr (coefficients (ofSupportedCoordinates (R := R) b A c) α) i = 0 := by
  change mixedCoordinates b ((mixedCoordinates b).symm _) (α, i) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨z, hz⟩
  exact h (hz ▸ z.property)

noncomputable def supportedCoordinates (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) : VectorPolynomial σ R V →ₗ[R] A →₀ S :=
  (Finsupp.lsubtypeDomain A).comp (mixedCoordinates b).toLinearMap

@[simp] theorem supportedCoordinates_apply (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) (p : VectorPolynomial σ R V) (z : A) :
    supportedCoordinates b A p z = b.repr (coefficients p z.val.1) z.val.2 := rfl

@[simp] theorem supportedCoordinates_ofSupportedCoordinates (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) (c : A →₀ S) :
    supportedCoordinates b A (ofSupportedCoordinates (R := R) b A c) = c := by
  ext z
  exact ofSupportedCoordinates_apply b A c z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

section Linear

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def realificationLinearEquiv :
    (ℝ ⊗[ℚ] VectorPolynomial σ ℚ V) ≃ₗ[ℚ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V) :=
  TensorProduct.leftComm ℚ ℝ (MvPolynomial σ ℚ) V

@[simp] theorem coefficients_realificationLinearEquiv_tmul
    (a : ℝ) (p : VectorPolynomial σ ℚ V) (α : σ →₀ ℕ) :
    coefficients (realificationLinearEquiv (a ⊗ₜ[ℚ] p)) α = a ⊗ₜ[ℚ] coefficients p α := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul f v =>
    change coefficients (f ⊗ₜ[ℚ] (a ⊗ₜ[ℚ] v)) α = _
    rw [coefficients_tmul, coefficients_tmul, TensorProduct.tmul_smul]
  | add p q hp hq =>
    simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hp, hq]

theorem realificationLinearEquiv_eq_zero_iff
    (x : ℝ ⊗[ℚ] VectorPolynomial σ ℚ V) :
    x = 0 ↔ ∀ α, coefficients (realificationLinearEquiv x) α = 0 := by
  constructor
  · rintro rfl α
    simp only [map_zero, Finsupp.zero_apply]
  · intro hx
    apply realificationLinearEquiv.injective
    apply coefficients.injective
    ext α
    simpa only [map_zero, Finsupp.zero_apply] using hx α

end Linear

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

section General

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] {N : Type*} [LieRing N] [LieAlgebra R N]

noncomputable def lieTensorLeftComm :
    (A ⊗[R] (B ⊗[R] N)) ≃ₗ⁅R⁆ (B ⊗[R] (A ⊗[R] N)) :=
  { TensorProduct.leftComm R A B N with
  map_lie' {x y} := by
    change TensorProduct.leftComm R A B N ⁅x, y⁆ =
      ⁅TensorProduct.leftComm R A B N x, TensorProduct.leftComm R A B N y⁆
    induction x using TensorProduct.induction_on with
    | zero =>
      refine (congrArg _ (zero_lie (L := (A ⊗[R] (B ⊗[R] N))) (M := (A ⊗[R] (B ⊗[R] N))) _)).trans ?_
      first | (simp; done) | (rw [map_zero]; exact (zero_lie (L := (B ⊗[R] (A ⊗[R] N))) (M := (B ⊗[R] (A ⊗[R] N))) _).symm)
    | tmul a p =>
      induction y using TensorProduct.induction_on with
      | zero =>
        refine (congrArg _ (lie_zero (L := (A ⊗[R] (B ⊗[R] N))) (M := (A ⊗[R] (B ⊗[R] N))) _)).trans ?_
        first | (simp; done) | (rw [map_zero]; exact (lie_zero (L := (B ⊗[R] (A ⊗[R] N))) (M := (B ⊗[R] (A ⊗[R] N))) _).symm)
      | tmul b q =>
        induction p using TensorProduct.induction_on with
        | zero =>
          rw [TensorProduct.tmul_zero]
          refine (congrArg _ (zero_lie (L := (A ⊗[R] (B ⊗[R] N))) (M := (A ⊗[R] (B ⊗[R] N))) _)).trans ?_
          first | (simp; done) | (rw [map_zero]; exact (zero_lie (L := (B ⊗[R] (A ⊗[R] N))) (M := (B ⊗[R] (A ⊗[R] N))) _).symm)
        | tmul f u =>
          induction q using TensorProduct.induction_on with
          | zero =>
            rw [TensorProduct.tmul_zero]
            refine (congrArg _ (lie_zero (L := (A ⊗[R] (B ⊗[R] N))) (M := (A ⊗[R] (B ⊗[R] N))) _)).trans ?_
            first | (simp; done) | (rw [map_zero]; exact (lie_zero (L := (B ⊗[R] (A ⊗[R] N))) (M := (B ⊗[R] (A ⊗[R] N))) _).symm)
          | tmul g v =>
            simp only [LieAlgebra.ExtendScalars.bracket_tmul, TensorProduct.leftComm_tmul]
          | add q r hq hr =>
            rw [TensorProduct.tmul_add, LieRing.lie_add, map_add, hq, hr, map_add, LieRing.lie_add]
        | add p q hp hq =>
          rw [TensorProduct.tmul_add, LieRing.add_lie, map_add, hp, hq, map_add, LieRing.add_lie]
      | add y z hy hz => rw [LieRing.lie_add, map_add, hy, hz, map_add, LieRing.lie_add]
    | add x z hx hz => rw [LieRing.add_lie, map_add, hx, hz, map_add, LieRing.add_lie] }

end General

noncomputable def realificationLieEquiv :
    (ℝ ⊗[ℚ] VectorPolynomial σ ℚ L) ≃ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  lieTensorLeftComm

@[simp] theorem realificationLieEquiv_tmul_tmul (a : ℝ) (p : MvPolynomial σ ℚ) (v : L) :
    realificationLieEquiv (a ⊗ₜ[ℚ] (p ⊗ₜ[ℚ] v)) = p ⊗ₜ[ℚ] (a ⊗ₜ[ℚ] v) :=
  TensorProduct.leftComm_tmul ℚ _ _ _

@[simp] theorem coefficients_realificationLieEquiv_tmul
    (a : ℝ) (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    coefficients (realificationLieEquiv (a ⊗ₜ[ℚ] p)) α = a ⊗ₜ[ℚ] coefficients p α := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul f v =>
    rw [realificationLieEquiv_tmul_tmul, coefficients_tmul, coefficients_tmul,
      TensorProduct.tmul_smul]
  | add p q hp hq =>
    simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hp, hq]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

theorem eval_realificationLieEquiv_tmul {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (r : ℝ) (p : VectorPolynomial σ ℚ L) (x : σ → ℚ) :
    eval x (realificationLieEquiv (r ⊗ₜ[ℚ] p)) = r ⊗ₜ[ℚ] eval x p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v =>
    rw [realificationLieEquiv_tmul_tmul, eval_tmul, eval_tmul, TensorProduct.tmul_smul]
  | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

section Linear

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable instance realModule : Module ℝ (VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V)) :=
  (realificationLinearEquiv (σ := σ) (V := V)).symm.toAddEquiv.module ℝ

noncomputable def realificationRealLinearEquiv :
    (ℝ ⊗[ℚ] VectorPolynomial σ ℚ V) ≃ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V) :=
  ((realificationLinearEquiv (σ := σ) (V := V)).symm.toAddEquiv.linearEquiv ℝ).symm

@[simp] theorem realificationRealLinearEquiv_apply
    (x : ℝ ⊗[ℚ] VectorPolynomial σ ℚ V) :
    realificationRealLinearEquiv x = realificationLinearEquiv x := rfl

instance realScalarTower : IsScalarTower ℚ ℝ (VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V)) :=
  LinearEquiv.isScalarTower ℝ (realificationLinearEquiv (σ := σ) (V := V)).symm

theorem coefficients_realification_smul (a : ℝ)
    (x : ℝ ⊗[ℚ] VectorPolynomial σ ℚ V) (α : σ →₀ ℕ) :
    coefficients (realificationLinearEquiv (a • x)) α =
      a • coefficients (realificationLinearEquiv x) α := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r p =>
    rw [TensorProduct.smul_tmul', coefficients_realificationLinearEquiv_tmul,
      coefficients_realificationLinearEquiv_tmul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    simp only [smul_add, map_add, Finsupp.add_apply, hx, hy]

@[simp] theorem coefficients_smul_real (a : ℝ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V)) (α : σ →₀ ℕ) :
    coefficients (a • P) α = a • coefficients P α := by
  obtain ⟨x, rfl⟩ := realificationRealLinearEquiv.surjective P
  rw [← map_smul, realificationRealLinearEquiv_apply, realificationRealLinearEquiv_apply]
  exact coefficients_realification_smul a x α

noncomputable def realCoefficient (α : σ →₀ ℕ) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V) →ₗ[ℝ] ℝ ⊗[ℚ] V where
  toFun P := coefficients P α
  map_add' P Q := by simp only [map_add, Finsupp.add_apply]
  map_smul' a P := coefficients_smul_real a P α

@[simp] theorem realCoefficient_apply (α : σ →₀ ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V)) : realCoefficient α P = coefficients P α := rfl

noncomputable def realMonomial (α : σ →₀ ℕ) :
    (ℝ ⊗[ℚ] V) →ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V) where
  toFun := monomial α
  map_add' x y := by
    apply coefficients.injective
    simp only [coefficients_monomial, map_add, Finsupp.single_add]
  map_smul' a x := by
    apply coefficients.injective
    ext β
    simp only [coefficients_smul_real, coefficients_monomial]
    exact DFunLike.congr_fun (Finsupp.smul_single a α x).symm β

@[simp] theorem realMonomial_apply (α : σ →₀ ℕ) (x : ℝ ⊗[ℚ] V) :
    realMonomial α x = monomial (R := ℚ) α x := rfl

end Linear

section Lie

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realificationLieEquiv_smul (a : ℝ)
    (x : ℝ ⊗[ℚ] VectorPolynomial σ ℚ L) :
    realificationLieEquiv (a • x) = a • realificationLieEquiv x :=
  (realificationRealLinearEquiv (σ := σ) (V := L)).map_smul a x

noncomputable instance realLieAlgebra : LieAlgebra ℝ (VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) where
  lie_smul a P Q := by
    obtain ⟨p, rfl⟩ := realificationLieEquiv.surjective P
    obtain ⟨q, rfl⟩ := realificationLieEquiv.surjective Q
    change ⁅realificationLieEquiv p, a • realificationLieEquiv q⁆ =
      a • ⁅realificationLieEquiv p, realificationLieEquiv q⁆
    rw [← realificationLieEquiv_smul, ← LieEquiv.map_lie, lie_smul,
      realificationLieEquiv_smul, LieEquiv.map_lie]

end Lie

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module VectorPolynomial

section BasisCriterion

attribute [local instance 100] LieRing.ofAssociativeRing

theorem linear_map_lie_of_basis {R V W ι : Type*} [CommRing R]
    [LieRing V] [LieAlgebra R V] [LieRing W] [LieAlgebra R W]
    (b : Basis ι R V) (f : V →ₗ[R] W)
    (h : ∀ i j, f ⁅b i, b j⁆ = ⁅f (b i), f (b j)⁆) (x y : V) :
    f ⁅x, y⁆ = ⁅f x, f y⁆ := by
  have he : (LieModule.toEnd R V V).toLinearMap.compr₂ f =
      (LieModule.toEnd R W W).toLinearMap.compl₁₂ f f :=
    LinearMap.ext_basis b b h
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

end BasisCriterion

namespace VectorPolynomial

theorem ofSupportedCoordinates_single {σ ι R S V : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]
    (b : Basis ι S V) (A : Set ((σ →₀ ℕ) × ι)) (z : A) (c : S) :
    ofSupportedCoordinates (R := R) b A (Finsupp.single z c) =
      monomial z.val.1 (c • b z.val.2) := by
  classical
  apply (mixedCoordinates b).injective
  change mixedCoordinates b ((mixedCoordinates b).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  change Finsupp.mapDomain Subtype.val (Finsupp.single z c) = _
  rw [Finsupp.mapDomain_single]
  apply Finsupp.ext
  rintro ⟨α, i⟩
  rw [mixedCoordinates_apply, coefficients_monomial]
  by_cases hα : z.val.1 = α <;> by_cases hi : z.val.2 = i <;>
    simp [Finsupp.single_apply, Prod.ext_iff, hα, hi]

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def gradedSymbolPolynomial :
    F.PolynomialSymbol w →ₗ[ℚ] VectorPolynomial σ ℚ F.AssociatedGraded :=
  (ofSupportedCoordinates (F.associatedGradedBasis b ω hlayers)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}).comp
      (F.polynomialSymbolBasis b ω hlayers w).repr.toLinearMap

@[simp] theorem gradedSymbolPolynomial_coefficient (x : F.PolynomialSymbol w)
    (z : SymbolBasisIndex w ω) :
    (F.associatedGradedBasis b ω hlayers).repr
      (coefficients (F.gradedSymbolPolynomial b ω hlayers w x) z.val.1) z.val.2 =
      (F.polynomialSymbolBasis b ω hlayers w).repr x z := by
  dsimp only [gradedSymbolPolynomial, LinearMap.comp_apply, LinearEquiv.coe_coe]
  generalize (F.polynomialSymbolBasis b ω hlayers w).repr x = c
  have h := ofSupportedCoordinates_apply (R := ℚ) (F.associatedGradedBasis b ω hlayers)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}
    c z
  convert h using 2

theorem gradedSymbolPolynomial_coefficient_of_ne (x : F.PolynomialSymbol w)
    (α : σ →₀ ℕ) (i : ι) (h : Finsupp.weight w α ≠ ω i) :
    (F.associatedGradedBasis b ω hlayers).repr
      (coefficients (F.gradedSymbolPolynomial b ω hlayers w x) α) i = 0 := by
  dsimp only [gradedSymbolPolynomial, LinearMap.comp_apply, LinearEquiv.coe_coe]
  generalize (F.polynomialSymbolBasis b ω hlayers w).repr x = c
  have hh := ofSupportedCoordinates_apply_of_not_mem (R := ℚ) (F.associatedGradedBasis b ω hlayers)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}
    c α i h
  convert hh using 2

@[simp] theorem gradedSymbolPolynomial_basis (z : SymbolBasisIndex w ω) :
    F.gradedSymbolPolynomial b ω hlayers w (F.polynomialSymbolBasis b ω hlayers w z) =
      monomial z.val.1 (F.associatedGradedBasis b ω hlayers z.val.2) := by
  simp only [gradedSymbolPolynomial, LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.repr_self]
  have h := ofSupportedCoordinates_single (R := ℚ) (F.associatedGradedBasis b ω hlayers)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2} z (1 : ℚ)
  simpa only [one_smul] using h

theorem gradedSymbolPolynomial_injective :
    Function.Injective (F.gradedSymbolPolynomial b ω hlayers w) := by
  intro x y hxy
  apply (F.polynomialSymbolBasis b ω hlayers w).repr.injective
  ext z
  rw [← F.gradedSymbolPolynomial_coefficient, ← F.gradedSymbolPolynomial_coefficient, hxy]

theorem gradedSymbolPolynomial_lie_basis (u v : SymbolBasisIndex w ω) :
    F.gradedSymbolPolynomial b ω hlayers w
      ⁅F.polynomialSymbolBasis b ω hlayers w u, F.polynomialSymbolBasis b ω hlayers w v⁆ =
      ⁅F.gradedSymbolPolynomial b ω hlayers w (F.polynomialSymbolBasis b ω hlayers w u),
        F.gradedSymbolPolynomial b ω hlayers w (F.polynomialSymbolBasis b ω hlayers w v)⁆ := by
  classical
  rw [F.gradedSymbolPolynomial_basis, F.gradedSymbolPolynomial_basis, lie_monomial]
  apply coefficients.injective
  ext α
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  rw [coefficients_monomial]
  by_cases hα : u.val.1 + v.val.1 = α
  · subst α
    rw [Finsupp.single_eq_same]
    rw [F.associatedGradedBasis_bracket]
    by_cases hd : Finsupp.weight w (u.val.1 + v.val.1) = ω i
    · have hgrade : ω u.val.2 + ω v.val.2 = ω i := by
        simpa only [map_add, u.property, v.property] using hd
      rw [if_pos hgrade]
      have hc := F.gradedSymbolPolynomial_coefficient b ω hlayers w
        ⁅F.polynomialSymbolBasis b ω hlayers w u, F.polynomialSymbolBasis b ω hlayers w v⁆
        ⟨(u.val.1 + v.val.1, i), hd⟩
      exact hc.trans (by rw [F.polynomialSymbolBasis_bracket, if_pos rfl])
    · have hgrade : ω u.val.2 + ω v.val.2 ≠ ω i := by
        simpa only [map_add, u.property, v.property] using hd
      rw [if_neg hgrade]
      exact F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ _ _ hd
  · rw [Finsupp.single_eq_of_ne (Ne.symm hα), map_zero, Finsupp.zero_apply]
    by_cases hd : Finsupp.weight w α = ω i
    · have hc := F.gradedSymbolPolynomial_coefficient b ω hlayers w
        ⁅F.polynomialSymbolBasis b ω hlayers w u, F.polynomialSymbolBasis b ω hlayers w v⁆
        ⟨(α, i), hd⟩
      exact hc.trans (by rw [F.polynomialSymbolBasis_bracket, if_neg hα])
    · exact F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ _ _ hd

noncomputable def gradedSymbolPolynomialLie :
    F.PolynomialSymbol w →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ F.AssociatedGraded where
  toLinearMap := F.gradedSymbolPolynomial b ω hlayers w
  map_lie' {x y} := by
    change F.gradedSymbolPolynomial b ω hlayers w ⁅x, y⁆ =
      ⁅F.gradedSymbolPolynomial b ω hlayers w x, F.gradedSymbolPolynomial b ω hlayers w y⁆
    apply linear_map_lie_of_basis (F.polynomialSymbolBasis b ω hlayers w)
      (F.gradedSymbolPolynomial b ω hlayers w) ?_ x y
    intro u v
    have h := F.gradedSymbolPolynomial_lie_basis b ω hlayers w u v
    convert h using 2

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realGradedSymbolPolynomial :
    F.RealPolynomialSymbol w →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  VectorPolynomial.realificationLieEquiv.toLieHom.comp
    (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) (F.gradedSymbolPolynomialLie b ω hlayers w))

@[simp] theorem realGradedSymbolPolynomial_coefficient_tmul
    (a : ℝ) (x : F.PolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (F.realGradedSymbolPolynomial b ω hlayers w (a ⊗ₜ[ℚ] x)) α =
      a ⊗ₜ[ℚ] coefficients (F.gradedSymbolPolynomial b ω hlayers w x) α := by
  simp only [realGradedSymbolPolynomial, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    LieAlgebra.ExtendScalars.map_apply_tmul, AlgHom.id_apply]
  have he : F.gradedSymbolPolynomialLie b ω hlayers w x = F.gradedSymbolPolynomial b ω hlayers w x := rfl
  rw [he]
  exact coefficients_realificationLieEquiv_tmul a (F.gradedSymbolPolynomial b ω hlayers w x) α

theorem realGradedSymbolPolynomial_coordinate (x : F.RealPolynomialSymbol w)
    (z : SymbolBasisIndex w ω) :
    ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) z.val.1) z.val.2 =
      ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x z := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [F.realGradedSymbolPolynomial_coefficient_tmul, Basis.baseChange_repr_tmul,
      F.gradedSymbolPolynomial_coefficient, Basis.baseChange_repr_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem realGradedSymbolPolynomial_coordinate_of_ne (x : F.RealPolynomialSymbol w)
    (α : σ →₀ ℕ) (i : ι) (h : Finsupp.weight w α ≠ ω i) :
    ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) i = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [F.realGradedSymbolPolynomial_coefficient_tmul, Basis.baseChange_repr_tmul,
      F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w x α i h, zero_smul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]

theorem realGradedSymbolPolynomial_injective :
    Function.Injective (F.realGradedSymbolPolynomial b ω hlayers w) := by
  intro x y h
  apply ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.injective
  ext z
  rw [← F.realGradedSymbolPolynomial_coordinate, ← F.realGradedSymbolPolynomial_coordinate, h]

theorem realGradedSymbolPolynomial_map_coefficient {W : Type*} [AddCommGroup W] [Module ℚ W]
    (f : F.AssociatedGraded →ₗ[ℚ] W) (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (VectorPolynomial.realificationLinearEquiv
      (((VectorPolynomial.map f).comp (F.gradedSymbolPolynomial b ω hlayers w)).baseChange ℝ x)) α =
      f.baseChange ℝ (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, coefficients_realificationLinearEquiv_tmul,
      LinearMap.comp_apply, coefficients_map, F.realGradedSymbolPolynomial_coefficient_tmul,
      LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def realificationLieSubalgebra (K : LieSubalgebra ℚ L) :
    LieSubalgebra ℝ (ℝ ⊗[ℚ] L) := (realificationLieHom K.incl).range

theorem realificationLieSubalgebra_toSubmodule (K : LieSubalgebra ℚ L) :
    (realificationLieSubalgebra K).toSubmodule = K.toSubmodule.baseChange ℝ := rfl

theorem realificationLieHom_incl_injective (K : LieSubalgebra ℚ L) :
    Function.Injective (realificationLieHom K.incl) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) K.incl.toLinearMap
    (fun _ _ h => Subtype.ext h)

theorem rational_inclusion_mem_realificationLieSubalgebra_iff (K : LieSubalgebra ℚ L) (a : L) :
    rationalLieInclusion a ∈ realificationLieSubalgebra K ↔ a ∈ K :=
  one_tmul_mem_real_baseChange_iff K.toSubmodule a

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realificationSubgroup (K : LieSubalgebra ℚ L) :
    Subgroup (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :=
  realLieSubgroup (realificationLieSubalgebra K)

theorem realificationMap_incl_injective (K : LieSubalgebra ℚ L) :
    Function.Injective (realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
      (hM := hnil) K.incl) := by
  intro x y hxy
  apply ext
  apply realificationLieHom_incl_injective K
  exact congrArg coord hxy

theorem realificationMap_incl_mem (K : LieSubalgebra ℚ L)
    (x : NilpotentLieBCHGroup (ℝ ⊗[ℚ] K) s
      (realification_lowerCentralSeries_eq_bot (lie_subalgebra_lowerCentralSeries_eq_bot hnil K))) :
    realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) (hM := hnil) K.incl x ∈
      realificationSubgroup (hnil := hnil) K :=
  ⟨x.coord, rfl⟩

theorem realificationMap_incl_range (K : LieSubalgebra ℚ L) :
    (realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) (hM := hnil) K.incl).range =
      realificationSubgroup (hnil := hnil) K := by
  ext g
  change (∃ x, realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
    (hM := hnil) K.incl x = g) ↔ ∃ y, realificationLieHom K.incl y = g.coord
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.coord, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨⟨y⟩, ext hy⟩

theorem realification_subgroup_comap_incl (K : LieSubalgebra ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) :
    (Γ.map realificationHom).comap
      (realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) (hM := hnil) K.incl) =
      (Γ.comap (map (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)).map
        (realificationHom (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg, heq⟩ := Subgroup.mem_map.mp hx
    have hgK : g.coord ∈ K := by
      apply (rational_inclusion_mem_realificationLieSubalgebra_iff K g.coord).mp
      have hm := realificationMap_incl_mem (hnil := hnil) K x
      rw [← heq] at hm
      exact hm
    let a : NilpotentLieBCHGroup K s (lie_subalgebra_lowerCentralSeries_eq_bot hnil K) :=
      ⟨⟨g.coord, hgK⟩⟩
    have hag : map K.incl a = g := ext rfl
    refine Subgroup.mem_map.mpr ⟨a, ?_, ?_⟩
    · change map K.incl a ∈ Γ
      rwa [hag]
    · apply realificationMap_incl_injective (hnil := hnil) K
      rw [realificationMap_realificationHom, hag]
      exact heq
  · rintro ⟨a, ha, rfl⟩
    change realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
      (hM := hnil) K.incl (realificationHom a) ∈ Γ.map realificationHom
    rw [realificationMap_realificationHom]
    exact Subgroup.mem_map.mpr ⟨map K.incl a, ha, rfl⟩

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem lieSubalgebra_mem_iInf {η R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (U : η → LieSubalgebra R L) (x : L) : x ∈ (⨅ j, U j) ↔ ∀ j, x ∈ U j := by
  change x ∈ ((sInf (Set.range U) : LieSubalgebra R L) : Set L) ↔ _
  rw [LieSubalgebra.coe_sInf]
  simp

theorem real_baseChange_ker {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℚ V] [Module ℚ W] (f : V →ₗ[ℚ] W) :
    (LinearMap.ker f).baseChange ℝ = LinearMap.ker (f.baseChange ℝ) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact (Module.Flat.ker_lTensor_eq ℝ ℝ f).symm

theorem real_baseChange_pi {η V : Type*} {W : η → Type*}
    [AddCommGroup V] [Module ℚ V] [∀ j, AddCommGroup (W j)] [∀ j, Module ℚ (W j)]
    (f : ∀ j, V →ₗ[ℚ] W j) :
    (TensorProduct.piRightHom ℚ ℝ ℝ W).comp ((LinearMap.pi f).baseChange ℝ) =
      LinearMap.pi (fun j => (f j).baseChange ℝ) := by
  ext a v
  rfl

theorem real_baseChange_iInf {η V : Type*} [Fintype η] [AddCommGroup V] [Module ℚ V]
    (U : η → Submodule ℚ V) :
    (⨅ j, U j).baseChange ℝ = ⨅ j, (U j).baseChange ℝ := by
  classical
  let f := LinearMap.pi (fun j => (U j).mkQ)
  let e := TensorProduct.piRight ℚ ℝ ℝ (fun j => V ⧸ U j)
  have hker : LinearMap.ker f = ⨅ j, U j := by
    simp only [f, LinearMap.ker_pi, Submodule.ker_mkQ]
  have hsingle (j : η) : (U j).baseChange ℝ = LinearMap.ker ((U j).mkQ.baseChange ℝ) := by
    simpa only [Submodule.ker_mkQ] using real_baseChange_ker (U j).mkQ
  rw [← hker, real_baseChange_ker]
  simp_rw [hsingle]
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_iInf]
  have heq : e (f.baseChange ℝ x) = fun j => (U j).mkQ.baseChange ℝ x :=
    congrArg (fun g => g x) (real_baseChange_pi (fun j => (U j).mkQ))
  constructor
  · intro hx
    have hz : e (f.baseChange ℝ x) = 0 := by rw [hx, map_zero]
    rw [heq] at hz
    exact fun j => congrFun hz j
  · intro hx
    apply e.injective
    rw [map_zero, heq]
    funext j
    exact hx j

theorem realificationLieSubalgebra_iInf {η L : Type*} [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] (U : η → LieSubalgebra ℚ L) :
    realificationLieSubalgebra (⨅ j, U j) = ⨅ j, realificationLieSubalgebra (U j) := by
  have hsub : (⨅ j, U j).toSubmodule = ⨅ j, (U j).toSubmodule := by
    ext x
    change x ∈ (⨅ j, U j) ↔ x ∈ (⨅ j, (U j).toSubmodule)
    rw [Submodule.mem_iInf]
    exact lieSubalgebra_mem_iInf U x
  ext x
  change x ∈ (⨅ j, U j).toSubmodule.baseChange ℝ ↔ _
  rw [hsub, real_baseChange_iInf]
  simp only [Submodule.mem_iInf, lieSubalgebra_mem_iInf]
  rfl

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realWeightedGroupInclusion (c : σ → ℕ) :
    (F.weightedFiltration c).realification.Group →* F.realification.Group :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (F.weightedFiltration c).lowerCentralSeries_eq_bot)
    (hM := F.ordinary.lowerCentralSeries_eq_bot) (F.weightedSubalgebra c).incl

theorem realWeightedGroupInclusion_injective (c : σ → ℕ) :
    Function.Injective (F.realWeightedGroupInclusion c) := by
  intro x y hxy
  apply NilpotentLieBCHGroup.ext
  exact realificationLieHom_incl_injective (F.weightedSubalgebra c)
    (congrArg NilpotentLieBCHGroup.coord hxy)

noncomputable def realifiedWeightedOrbit {τ : Type*} (c : σ → ℕ) {v : τ → ℕ}
    (q : (F.realification.weightedFiltration c).PolynomialOrbit v) :
    (F.weightedFiltration c).realification.PolynomialOrbit v :=
  NilpotentLieFiltration.polynomialOrbitOfLog
    (VectorPolynomial.map (F.realifiedWeightedEquiv c).symm.toLinearMap q.log)
    ((F.realification.weightedFiltration c).adapted_map (F.weightedFiltration c).realification
      (F.realifiedWeightedEquiv c).symm.toLinearMap
      (fun n x hx => (F.realifiedWeightedEquiv_symm_mem_layer c n x).mpr hx) v q.adapted)

theorem realifiedWeightedOrbit_eval {τ : Type*} (c : σ → ℕ) {v : τ → ℕ}
    (q : (F.realification.weightedFiltration c).PolynomialOrbit v) (x : τ → ℤ) :
    F.realWeightedGroupInclusion c
      ((F.weightedFiltration c).realification.polynomialOrbitEval v x (F.realifiedWeightedOrbit c q)) =
        F.realification.weightedGroupInclusion c
          ((F.realification.weightedFiltration c).polynomialOrbitEval v x q) := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (F.weightedSubalgebra c).incl
    (eval (fun i => (x i : ℚ))
      (VectorPolynomial.map (F.realifiedWeightedEquiv c).symm.toLinearMap q.log)) = _
  rw [eval_map, ← F.realifiedWeightedEquiv_coe]
  exact congrArg (fun z : F.realification.weightedSubalgebra c => (z : ℝ ⊗[ℚ] L))
    ((F.realifiedWeightedEquiv c).apply_symm_apply _)

theorem exists_real_normalized_frozen_orbit [DecidableEq σ] (S : Finset σ) (b : σ → ℤ)
    (p : F.realification.PolynomialOrbit) (a γ : F.realification.Group)
    (hzero : F.realification.polynomialOrbitEval (freezeCoordinates S b 0) p = a * γ) :
    ∃ q : (F.weightedFiltration (retainedCoordinateWeight S)).realification.PolynomialOrbit
        (fun _ : S => 1),
      (F.weightedFiltration (retainedCoordinateWeight S)).realification.polynomialOrbitEval _ 0 q = 1 ∧
      ∀ x : S → ℤ, F.realWeightedGroupInclusion (retainedCoordinateWeight S)
        ((F.weightedFiltration (retainedCoordinateWeight S)).realification.polynomialOrbitEval _ x q) =
          a⁻¹ * F.realification.polynomialOrbitEval (freezeCoordinates S b x) p * γ⁻¹ := by
  obtain ⟨q, hq, hval⟩ := F.realification.exists_normalized_frozen_orbit S b p a γ hzero
  refine ⟨F.realifiedWeightedOrbit _ q, ?_, ?_⟩
  · apply F.realWeightedGroupInclusion_injective (retainedCoordinateWeight S)
    rw [F.realifiedWeightedOrbit_eval, hq, map_one, map_one]
  · intro x
    rw [F.realifiedWeightedOrbit_eval, hval]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem realification_sup (P Q : Submodule ℚ V) :
    (P ⊔ Q).baseChange ℝ = P.baseChange ℝ ⊔ Q.baseChange ℝ := by
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    change (1 : ℝ) ⊗ₜ[ℚ] (a + b) ∈ _
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem_sup (Submodule.tmul_mem_baseChange_of_mem _ ha)
      (Submodule.tmul_mem_baseChange_of_mem _ hb)
  · exact sup_le (Submodule.baseChange_mono ℝ le_sup_left)
      (Submodule.baseChange_mono ℝ le_sup_right)

theorem real_four_projection (x : ℝ ⊗[ℚ] (Fin 4 → V)) (k : Fin 4) :
    (LinearMap.proj k).baseChange ℝ x =
      (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)) x k := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem real_four_single (k : Fin 4) (x : ℝ ⊗[ℚ] V) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V))
        ((LinearMap.single ℚ (fun _ : Fin 4 => V) k).baseChange ℝ x) =
      LinearMap.single ℝ (fun _ : Fin 4 => ℝ ⊗[ℚ] V) k x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    ext j
    change a ⊗ₜ[ℚ] ((Pi.single k x : Fin 4 → V) j) =
      (Pi.single k (a ⊗ₜ[ℚ] x) : Fin 4 → ℝ ⊗[ℚ] V) j
    rw [TensorProduct.tmul_single]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem real_four_alternating (x : ℝ ⊗[ℚ] (Fin 4 → V)) :
    (fourAlternatingMap (R := ℚ)).baseChange ℝ x =
      fourAlternatingMap (R := ℝ) ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)) x) := by
  simp only [fourAlternatingMap, LinearMap.baseChange_sub, LinearMap.baseChange_add,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.proj_apply, real_four_projection]

theorem mem_realified_four_product_iff (D : Submodule ℚ V)
    (x : ℝ ⊗[ℚ] (Fin 4 → V)) :
    x ∈ (Submodule.pi Set.univ (fun _ : Fin 4 => D)).baseChange ℝ ↔
      ∀ k, (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)) x k ∈ D.baseChange ℝ := by
  have heq : Submodule.pi Set.univ (fun _ : Fin 4 => D) =
      ⨅ k : Fin 4, D.comap (LinearMap.proj k) := by
    ext v
    simp [Submodule.mem_pi]
  rw [heq, real_baseChange_iInf]
  simp only [Submodule.mem_iInf, realification_comap, Submodule.mem_comap, real_four_projection]

theorem realification_fourCommonModulo (C D : Submodule ℚ V) :
    ((fourCommonModulo C D).baseChange ℝ).map
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).toLinearMap =
      fourCommonModulo (C.baseChange ℝ) (D.baseChange ℝ) := by
  let e := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)
  have hmem (x : ℝ ⊗[ℚ] (Fin 4 → V)) :
      x ∈ (fourCommonModulo C D).baseChange ℝ ↔
        e x ∈ fourCommonModulo (C.baseChange ℝ) (D.baseChange ℝ) := by
    rw [fourCommonModulo, realification_inf, Submodule.mem_inf,
      mem_realified_four_product_iff, real_baseChange_iInf, mem_fourCommonModulo]
    simp only [e, Submodule.mem_iInf, realification_comap, Submodule.mem_comap,
      LinearMap.baseChange_sub, LinearMap.sub_apply, real_four_projection]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mp hx
  · intro hv
    refine ⟨e.symm v, (hmem _).mpr ?_, e.apply_symm_apply v⟩
    simpa only [e.apply_symm_apply] using hv

theorem realification_fourBalancedDependent (D : Submodule ℚ V) :
    ((fourBalancedDependent D).baseChange ℝ).map
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).toLinearMap =
      fourBalancedDependent (D.baseChange ℝ) := by
  let e := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)
  have hmem (x : ℝ ⊗[ℚ] (Fin 4 → V)) :
      x ∈ (fourBalancedDependent D).baseChange ℝ ↔
        e x ∈ fourBalancedDependent (D.baseChange ℝ) := by
    rw [fourBalancedDependent, realification_inf, realification_ker, Submodule.mem_inf,
      mem_realified_four_product_iff, LinearMap.mem_ker, real_four_alternating,
      mem_fourBalancedDependent, fourAlternatingMap_apply]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mp hx
  · intro hv
    refine ⟨e.symm v, (hmem _).mpr ?_, e.apply_symm_apply v⟩
    simpa only [e.apply_symm_apply] using hv

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def symbolPointwiseSubalgebra (U : LieSubalgebra ℚ F.AssociatedGraded) :
    LieSubalgebra ℚ (F.PolynomialSymbol w) :=
  (coefficientLieSubalgebra U).comap (F.gradedSymbolPolynomialLie b ω hlayers w)

theorem mem_symbolPointwiseSubalgebra_iff (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.PolynomialSymbol w) :
    x ∈ F.symbolPointwiseSubalgebra b ω hlayers w U ↔
      ∀ α, coefficients (F.gradedSymbolPolynomial b ω hlayers w x) α ∈ U := Iff.rfl

theorem gradedSymbolPolynomial_block_coefficient [DecidableEq σ]
    (α β : σ →₀ ℕ) (x : F.PolynomialSymbol w) :
    coefficients (F.gradedSymbolPolynomial b ω hlayers w
      (basisCoordinateProjection (F.polynomialSymbolBasis b ω hlayers w)
        {z | z.val.1 = α} x)) β =
      if β = α then coefficients (F.gradedSymbolPolynomial b ω hlayers w x) β else 0 := by
  classical
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  by_cases hβ : β = α
  · rw [if_pos hβ]
    by_cases hd : Finsupp.weight w β = ω i
    · rw [F.gradedSymbolPolynomial_coefficient b ω hlayers w _ ⟨(β, i), hd⟩,
        F.gradedSymbolPolynomial_coefficient b ω hlayers w x ⟨(β, i), hd⟩,
        basisCoordinateProjection_repr]
      exact if_pos hβ
    · rw [F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ β i hd,
        F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w x β i hd]
  · rw [if_neg hβ, map_zero, Finsupp.zero_apply]
    by_cases hd : Finsupp.weight w β = ω i
    · rw [F.gradedSymbolPolynomial_coefficient b ω hlayers w _ ⟨(β, i), hd⟩,
        basisCoordinateProjection_repr]
      exact if_neg hβ
    · exact F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ β i hd

theorem symbolPointwiseSubalgebra_blockInvariant (U : LieSubalgebra ℚ F.AssociatedGraded) :
    BasisBlockInvariant (F.polynomialSymbolBasis b ω hlayers w) (fun z => z.val.1)
      (F.symbolPointwiseSubalgebra b ω hlayers w U).toSubmodule := by
  classical
  intro α x hx
  apply (F.mem_symbolPointwiseSubalgebra_iff b ω hlayers w U _).mpr
  intro β
  rw [F.gradedSymbolPolynomial_block_coefficient]
  split_ifs
  · exact (F.mem_symbolPointwiseSubalgebra_iff b ω hlayers w U x).mp hx β
  · exact U.zero_mem

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

section Algebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def petalComparisonSpace (C P K : Submodule R V) : Submodule R (Fin 2 → V) :=
  (C ⊔ K).comap (LinearMap.proj (1 : Fin 2) : (Fin 2 → V) →ₗ[R] V) ⊓
    (P ⊔ K).comap ((LinearMap.proj (0 : Fin 2) : (Fin 2 → V) →ₗ[R] V) -
      (LinearMap.proj (1 : Fin 2) : (Fin 2 → V) →ₗ[R] V))

theorem mem_petalComparisonSpace (C P K : Submodule R V) (x : Fin 2 → V) :
    x ∈ petalComparisonSpace C P K ↔ x 1 ∈ C ⊔ K ∧ x 0 - x 1 ∈ P ⊔ K := Iff.rfl

theorem petalComparisonSpace_decompose (C P K : Submodule R V) (x : Fin 2 → V)
    (hx : x ∈ petalComparisonSpace C P K) :
    ∃ c ∈ C, ∃ p ∈ P, ∃ k₀ ∈ K, ∃ k₁ ∈ K,
      x 0 = c + p + k₀ ∧ x 1 = c + k₁ := by
  obtain ⟨c, hc, k₁, hk₁, h₁⟩ := Submodule.mem_sup.mp hx.1
  obtain ⟨p, hp, k₀, hk₀, h₀⟩ := Submodule.mem_sup.mp hx.2
  change c + k₁ = x 1 at h₁
  change p + k₀ = x 0 - x 1 at h₀
  refine ⟨c, hc, p, hp, k₁ + k₀, K.add_mem hk₁ hk₀, k₁, hk₁, ?_, h₁.symm⟩
  calc
    x 0 = (x 0 - x 1) + x 1 := (sub_add_cancel _ _).symm
    _ = (p + k₀) + (c + k₁) := by rw [← h₀, ← h₁]
    _ = c + p + (k₁ + k₀) := by abel

theorem petalComparisonSpace_le_pi (C P K U : Submodule R V)
    (hC : C ≤ U) (hP : P ≤ U) (hK : K ≤ U) :
    petalComparisonSpace C P K ≤ Submodule.pi Set.univ (fun _ : Fin 2 => U) := by
  intro x hx
  obtain ⟨c, hc, p, hp, k₀, hk₀, k₁, hk₁, h₀, h₁⟩ := petalComparisonSpace_decompose C P K x hx
  apply Submodule.mem_pi.mpr
  intro i _
  fin_cases i
  · change x 0 ∈ U
    rw [h₀]
    exact U.add_mem (U.add_mem (hC hc) (hP hp)) (hK hk₀)
  · change x 1 ∈ U
    rw [h₁]
    exact U.add_mem (hC hc) (hK hk₁)

end Algebra

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem real_pair_projection (x : ℝ ⊗[ℚ] (Fin 2 → V)) (k : Fin 2) :
    (LinearMap.proj k).baseChange ℝ x =
      (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => V)) x k := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem realification_petalComparisonSpace (C P K : Submodule ℚ V) :
    ((petalComparisonSpace C P K).baseChange ℝ).map
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => V)).toLinearMap =
      petalComparisonSpace (C.baseChange ℝ) (P.baseChange ℝ) (K.baseChange ℝ) := by
  let e := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => V)
  have hmem (x : ℝ ⊗[ℚ] (Fin 2 → V)) :
      x ∈ (petalComparisonSpace C P K).baseChange ℝ ↔
        e x ∈ petalComparisonSpace (C.baseChange ℝ) (P.baseChange ℝ) (K.baseChange ℝ) := by
    simp only [petalComparisonSpace, realification_inf, realification_comap, realification_sup,
      Submodule.mem_inf, Submodule.mem_comap, LinearMap.baseChange_sub, LinearMap.sub_apply,
      LinearMap.proj_apply, real_pair_projection, e]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mp hx
  · intro hv
    refine ⟨e.symm v, (hmem _).mpr ?_, e.apply_symm_apply v⟩
    simpa only [e.apply_symm_apply] using hv

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem realification_map {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (U : Submodule ℚ V) (f : V →ₗ[ℚ] W) :
    (U.map f).baseChange ℝ = (U.baseChange ℝ).map (f.baseChange ℝ) := by
  rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span, Submodule.map_span]
  apply congrArg (Submodule.span ℝ)
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(1 : ℝ) ⊗ₜ[ℚ] x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩

theorem realificationLieSubalgebra_map {L M : Type*}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (U : LieSubalgebra ℚ L) (f : L →ₗ⁅ℚ⁆ M) :
    realificationLieSubalgebra (U.map f) =
      (realificationLieSubalgebra U).map (realificationLieHom f) := by
  apply LieSubalgebra.toSubmodule_injective
  exact realification_map U.toSubmodule f.toLinearMap

theorem toLin_baseChange_coordinates {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (T : Matrix ι κ ℚ) (y : ℝ ⊗[ℚ] M) :
    (e.baseChange ℝ).equivFun ((Matrix.toLin f e T).baseChange ℝ y) =
      (fun i j => (T i j : ℝ)) *ᵥ (f.baseChange ℝ).equivFun y := by
  classical
  simpa only [LinearMap.toMatrix_toLin] using
    (baseChange_matrix_apply f e (Matrix.toLin f e T) y).symm

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def symbolSubalgebraQuotientMap (U : LieSubalgebra ℚ F.AssociatedGraded) :
    F.PolynomialSymbol w →ₗ[ℚ] VectorPolynomial σ ℚ (F.AssociatedGraded ⧸ U.toSubmodule) :=
  (VectorPolynomial.map U.toSubmodule.mkQ).comp (F.gradedSymbolPolynomial b ω hlayers w)

theorem symbolPointwiseSubalgebra_eq_ker (U : LieSubalgebra ℚ F.AssociatedGraded) :
    (F.symbolPointwiseSubalgebra b ω hlayers w U).toSubmodule =
      LinearMap.ker (F.symbolSubalgebraQuotientMap b ω hlayers w U) := by
  ext x
  change x ∈ F.symbolPointwiseSubalgebra b ω hlayers w U ↔
    F.symbolSubalgebraQuotientMap b ω hlayers w U x = 0
  rw [F.mem_symbolPointwiseSubalgebra_iff]
  constructor
  · intro hx
    apply coefficients.injective
    ext α
    change coefficients (VectorPolynomial.map U.toSubmodule.mkQ
      (F.gradedSymbolPolynomial b ω hlayers w x)) α = _
    rw [coefficients_map, map_zero, Finsupp.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero U.toSubmodule).mpr (hx α)
  · intro hx α
    have hc := congrArg (fun p => coefficients p α) hx
    change coefficients (VectorPolynomial.map U.toSubmodule.mkQ
      (F.gradedSymbolPolynomial b ω hlayers w x)) α = _ at hc
    rw [coefficients_map, map_zero, Finsupp.zero_apply] at hc
    exact (Submodule.Quotient.mk_eq_zero U.toSubmodule).mp hc

theorem symbolSubalgebraQuotientMap_real_coefficient
    (U : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (VectorPolynomial.realificationLinearEquiv
      ((F.symbolSubalgebraQuotientMap b ω hlayers w U).baseChange ℝ x)) α =
      U.toSubmodule.mkQ.baseChange ℝ
        (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) := by
  unfold symbolSubalgebraQuotientMap
  exact F.realGradedSymbolPolynomial_map_coefficient b ω hlayers w U.toSubmodule.mkQ x α

theorem mem_real_symbolPointwiseSubalgebra_iff_coefficients
    (U : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w) :
    x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hlayers w U) ↔
      ∀ α, coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α ∈
        realificationLieSubalgebra U := by
  change x ∈ (F.symbolPointwiseSubalgebra b ω hlayers w U).toSubmodule.baseChange ℝ ↔ _
  rw [F.symbolPointwiseSubalgebra_eq_ker, real_baseChange_ker]
  change (F.symbolSubalgebraQuotientMap b ω hlayers w U).baseChange ℝ x = 0 ↔ _
  rw [VectorPolynomial.realificationLinearEquiv_eq_zero_iff]
  have hker : U.toSubmodule.baseChange ℝ = LinearMap.ker (U.toSubmodule.mkQ.baseChange ℝ) := by
    simpa only [Submodule.ker_mkQ] using real_baseChange_ker U.toSubmodule.mkQ
  constructor
  · intro hx α
    change coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α ∈ U.toSubmodule.baseChange ℝ
    rw [hker]
    change U.toSubmodule.mkQ.baseChange ℝ
      (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) = 0
    exact (F.symbolSubalgebraQuotientMap_real_coefficient b ω hlayers w U x α).symm.trans (hx α)
  · intro hx α
    have h := hx α
    change coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α ∈ U.toSubmodule.baseChange ℝ at h
    rw [hker] at h
    exact (F.symbolSubalgebraQuotientMap_real_coefficient b ω hlayers w U x α).trans h

theorem mem_real_symbolPointwiseSubalgebra_iff_values
    (U : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w) :
    x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hlayers w U) ↔
      ∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x) ∈
        realificationLieSubalgebra U := by
  rw [F.mem_real_symbolPointwiseSubalgebra_iff_coefficients]
  exact (eval₂_mem_iff_coefficients (realificationLieSubalgebra U).toSubmodule _).symm

theorem symbolPointwiseSubalgebra_iInf {η : Type*} (U : η → LieSubalgebra ℚ F.AssociatedGraded) :
    F.symbolPointwiseSubalgebra b ω hlayers w (⨅ j, U j) =
      ⨅ j, F.symbolPointwiseSubalgebra b ω hlayers w (U j) := by
  ext x
  rw [lieSubalgebra_mem_iInf, F.mem_symbolPointwiseSubalgebra_iff]
  simp only [F.mem_symbolPointwiseSubalgebra_iff, lieSubalgebra_mem_iInf]
  exact forall_comm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

section Functional

variable {R L M : Type*} [CommRing R] [AddCommGroup L] [Module R L]
  [AddCommGroup M] [Module R M]

def pairDifferenceFunctional (η : L →ₗ[R] M) : (Fin 2 → L) →ₗ[R] M :=
  η.comp (LinearMap.proj (0 : Fin 2)) - η.comp (LinearMap.proj (1 : Fin 2))

theorem pairDifferenceFunctional_apply (η : L →ₗ[R] M) (z : Fin 2 → L) :
    pairDifferenceFunctional η z = η (z 0) - η (z 1) := rfl

end Functional

theorem petalComparisonSpace_top_tree
    {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup M] [Module ℚ M]
    {s r : ℕ} (F : DegreeRankLieFiltration L s r) (d : I → ℕ)
    (C P : I → Submodule ℚ L) (hC : ∀ i, C i ≤ F.layer (d i) 1)
    (hP : ∀ i, P i ≤ F.layer (d i) 1)
    (η : L →ₗ[ℚ] M) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hinvariant : ∀ c p : I → L, (∀ i, c i ∈ C i) → (∀ i, p i ∈ P i) →
      η (lieTreeEval (c + p) a) = η (lieTreeEval c a))
    (z : I → Fin 2 → L)
    (hz : ∀ i, z i ∈ petalComparisonSpace (C i) (P i) (F.layer (d i) 2)) :
    pairDifferenceFunctional η (lieTreeEval z a) = 0 := by
  classical
  choose c hc p hp k₀ hk₀ k₁ hk₁ h₀ h₁ using
    (fun i => petalComparisonSpace_decompose (C i) (P i) (F.layer (d i) 2) (z i) (hz i))
  have hle (i : I) : F.layer (d i) 2 ≤ F.layer (d i) 1 :=
    F.lex_antitone (Or.inr ⟨rfl, by omega⟩)
  have hz₀ (i : I) : z i 0 ∈ F.layer (d i) 1 := by
    rw [h₀]
    exact (F.layer (d i) 1).add_mem ((F.layer (d i) 1).add_mem (hC i (hc i)) (hP i (hp i)))
      (hle i (hk₀ i))
  have hz₁ (i : I) : z i 1 ∈ F.layer (d i) 1 := by
    rw [h₁]
    exact (F.layer (d i) 1).add_mem (hC i (hc i)) (hle i (hk₁ i))
  have hdiff₀ (i : I) : z i 0 - (c i + p i) ∈ F.layer (d i) 2 := by
    rw [h₀]
    simpa only [add_sub_cancel_left] using hk₀ i
  have hdiff₁ (i : I) : z i 1 - c i ∈ F.layer (d i) 2 := by
    rw [h₁]
    simpa only [add_sub_cancel_left] using hk₁ i
  have heq₀ := F.top_lieTreeEval_congr (fun i => z i 0) (c + p) d hz₀
    (fun i => (F.layer (d i) 1).add_mem (hC i (hc i)) (hP i (hp i))) hdiff₀ a hd hr
  have heq₁ := F.top_lieTreeEval_congr (fun i => z i 1) c d hz₁
    (fun i => hC i (hc i)) hdiff₁ a hd hr
  change η ((liePiEval (0 : Fin 2)) (lieTreeEval z a)) -
    η ((liePiEval (1 : Fin 2)) (lieTreeEval z a)) = 0
  rw [map_lieTreeEval, map_lieTreeEval]
  change η (lieTreeEval (fun i => z i 0) a) - η (lieTreeEval (fun i => z i 1) a) = 0
  rw [heq₀, heq₁, hinvariant c p hc hp, sub_self]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolRepresentativeSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_smul_real (g : NilpotentLieBCHGroup L s hnil) (r : ℝ) (x : L) :
    dualAdjoint g (r • x) = r • dualAdjoint g x := by
  let T : L →ₗ[ℚ] L := r • LinearMap.id
  have hT : ∀ a b : L, b ∈ (⊤ : LieIdeal ℚ L) →
      T ⁅a, b⁆ = ⁅(LieHom.id : L →ₗ⁅ℚ⁆ L) a, T b⁆ := by
    intro a b _
    change r • ⁅a, b⁆ = ⁅a, r • b⁆
    exact (lie_smul r a b).symm
  exact (dualLinearLift_adjoint_eq hnil ⊤ LieHom.id T hT g x
    (by trivial) g (r • x) rfl rfl).symm

noncomputable def dualAdjointRealLinearEquiv (g : NilpotentLieBCHGroup L s hnil) :
    L ≃ₗ[ℝ] L :=
  { dualAdjointAddEquiv g with map_smul' := dualAdjoint_smul_real g }

@[simp] theorem dualAdjointRealLinearEquiv_apply
    (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjointRealLinearEquiv g x = dualAdjoint g x := rfl

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_real_mem_of_invariant (U : LieSubalgebra ℚ L) (V : Submodule ℝ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (x : L) (hx : x ∈ V) :
    dualAdjoint g x ∈ V :=
  dualAdjoint_mem_of_invariant U (V.restrictScalars ℚ) hUV g hg x hx

noncomputable def invariantRealAdjoint (U : LieSubalgebra ℚ L) (W : Submodule ℝ L)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ W)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) : W ≃ₗ[ℝ] W where
  toFun x := ⟨dualAdjoint g x.val, dualAdjoint_real_mem_of_invariant U W hUW g hg x.val x.property⟩
  invFun x := ⟨dualAdjoint g⁻¹ x.val,
    dualAdjoint_real_mem_of_invariant U W hUW g⁻¹ (U.neg_mem hg) x.val x.property⟩
  left_inv x := Subtype.ext (dualAdjoint_inv_cancel g x.val)
  right_inv x := Subtype.ext (dualAdjoint_cancel_inv g x.val)
  map_add' x y := Subtype.ext (dualAdjoint_add g x.val y.val)
  map_smul' r x := Subtype.ext (dualAdjoint_smul_real g r x.val)

@[simp] theorem invariantRealAdjoint_coe (U : LieSubalgebra ℚ L) (W : Submodule ℝ L)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ W)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (x : W) :
    (invariantRealAdjoint U W hUW g hg x : L) = dualAdjoint g x.val := rfl

theorem invariantRealAdjoint_map_submodule (U : LieSubalgebra ℚ L) (W V : Submodule ℝ L)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ W)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) :
    (V.comap W.subtype).map (invariantRealAdjoint U W hUW g hg).toLinearMap = V.comap W.subtype := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact dualAdjoint_real_mem_of_invariant U V hUV g hg x.val hx
  · intro y hy
    refine ⟨(invariantRealAdjoint U W hUW g hg).symm y, ?_, ?_⟩
    · exact dualAdjoint_real_mem_of_invariant U V hUV g⁻¹ (U.neg_mem hg) y.val hy
    · exact (invariantRealAdjoint U W hUW g hg).apply_symm_apply y

noncomputable def invariantRealAdjointQuotient (U : LieSubalgebra ℚ L) (W V : Submodule ℝ L)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ W)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) :
    (W ⧸ V.comap W.subtype) ≃ₗ[ℝ] (W ⧸ V.comap W.subtype) :=
  Submodule.Quotient.equiv _ _ (invariantRealAdjoint U W hUW g hg)
    (invariantRealAdjoint_map_submodule U W V hUW hUV g hg)

@[simp] theorem invariantRealAdjointQuotient_mk (U : LieSubalgebra ℚ L) (W V : Submodule ℝ L)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ W)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (x : W) :
    invariantRealAdjointQuotient U W V hUW hUV g hg ((V.comap W.subtype).mkQ x) =
      (V.comap W.subtype).mkQ (invariantRealAdjoint U W hUW g hg x) := rfl

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped TensorProduct
open NilpotentLieBCHGroup

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  (I : LieIdeal ℚ L)

theorem realification_ideal_intertwining (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M)
    (hT : ∀ a b, b ∈ I → T ⁅a, b⁆ = ⁅B a, T b⁆)
    (x y : ℝ ⊗[ℚ] L) (hy : y ∈ I.toSubmodule.baseChange ℝ) :
    T.baseChange ℝ ⁅x, y⁆ = ⁅realificationLieHom B x, T.baseChange ℝ y⁆ := by
  obtain ⟨v, rfl⟩ := hy
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul q b =>
      change (r * q) ⊗ₜ[ℚ] T ⁅a, b.val⁆ = (r * q) ⊗ₜ[ℚ] ⁅B a, T b.val⁆
      rw [hT a b.val b.property]
    | add v z hv hz => simp only [map_add, lie_add, hv, hz]
  | add x z hx hz => simp only [map_add, add_lie, hx, hz]

variable {s t : ℕ} (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (hM : LieModule.lowerCentralSeries ℚ M M t = ⊥)

noncomputable def realIdealAdjoint
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL)) :
    (ℝ ⊗[ℚ] I.toSubmodule) ≃ₗ[ℝ] (ℝ ⊗[ℚ] I.toSubmodule) :=
  (realificationSubmoduleEquiv I.toSubmodule).trans
    ((invariantRealAdjoint ⊤ (I.toSubmodule.baseChange ℝ)
      (fun _ _ _ hy => (I.baseChange ℝ).lie_mem hy) g (by trivial)).trans
        (realificationSubmoduleEquiv I.toSubmodule).symm)

theorem realIdealAdjoint_inclusion
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL))
    (x : ℝ ⊗[ℚ] I.toSubmodule) :
    I.toSubmodule.subtype.baseChange ℝ (realIdealAdjoint I hL g x) =
      dualAdjoint g (I.toSubmodule.subtype.baseChange ℝ x) := by
  change (realificationSubmoduleEquiv I.toSubmodule
    ((realificationSubmoduleEquiv I.toSubmodule).symm
      ((invariantRealAdjoint ⊤ (I.toSubmodule.baseChange ℝ)
        (fun _ _ _ hy => (I.baseChange ℝ).lie_mem hy) g (by trivial))
          (realificationSubmoduleEquiv I.toSubmodule x))) : ℝ ⊗[ℚ] L) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem realIdealMap_adjoint (B : L →ₗ⁅ℚ⁆ M) (f : I.toSubmodule →ₗ[ℚ] M)
    (hf : ∀ a (p : I.toSubmodule),
      f ⟨⁅a, p.val⁆, I.lie_mem p.property⟩ = ⁅B a, f p⁆)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL))
    (x : ℝ ⊗[ℚ] I.toSubmodule) :
    f.baseChange ℝ (realIdealAdjoint I hL g x) =
      dualAdjoint (realificationMap (hnil := hL) (hM := hM) B g) (f.baseChange ℝ x) := by
  obtain ⟨T, hTf⟩ := f.exists_extend
  have he (p : I.toSubmodule) : T p.val = f p := DFunLike.congr_fun hTf p
  have hT (a b : L) (hb : b ∈ I) : T ⁅a, b⁆ = ⁅B a, T b⁆ := by
    rw [he ⟨⁅a, b⁆, I.lie_mem hb⟩, he ⟨b, hb⟩]
    exact hf a ⟨b, hb⟩
  have hr (y : ℝ ⊗[ℚ] I.toSubmodule) :
      T.baseChange ℝ (I.toSubmodule.subtype.baseChange ℝ y) = f.baseChange ℝ y := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hTf]
  have hx : I.toSubmodule.subtype.baseChange ℝ x ∈ I.toSubmodule.baseChange ℝ := ⟨x, rfl⟩
  let J : LieIdeal ℚ (ℝ ⊗[ℚ] L) :=
    { (I.toSubmodule.baseChange ℝ).restrictScalars ℚ with
      lie_mem := fun {a b} hb => (I.baseChange ℝ).lie_mem hb }
  calc
    _ = T.baseChange ℝ (I.toSubmodule.subtype.baseChange ℝ (realIdealAdjoint I hL g x)) := (hr _).symm
    _ = T.baseChange ℝ (dualAdjoint g (I.toSubmodule.subtype.baseChange ℝ x)) := by
      rw [realIdealAdjoint_inclusion]
    _ = dualAdjoint (realificationMap (hnil := hL) (hM := hM) B g)
        (T.baseChange ℝ (I.toSubmodule.subtype.baseChange ℝ x)) := by
      exact dualLinearLift_adjoint_of_steps (realification_lowerCentralSeries_eq_bot hL)
        (realification_lowerCentralSeries_eq_bot hM) J
        (realLieHomToRat (realificationLieHom B)) ((T.baseChange ℝ).restrictScalars ℚ)
        (realification_ideal_intertwining I B T hT) g _ hx
    _ = _ := by rw [hr]

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realSymbolRepresentative :
    F.RealPolynomialSymbol w →ₗ[ℚ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) where
  toFun x := ofSupportedCoordinates (b.baseChange ℝ)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}
      (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x)
  map_add' x y := by simp only [map_add]
  map_smul' a x := by
    have h := (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.restrictScalars ℚ).map_smul a x
    change ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr (a • x) =
      a • ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x at h
    rw [h, map_smul]
    rfl

noncomputable def realSymbolOfPolynomial :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) →ₗ[ℚ] F.RealPolynomialSymbol w :=
  (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.symm.restrictScalars ℚ).toLinearMap.comp
    (supportedCoordinates (b.baseChange ℝ)
      {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2})

@[simp] theorem realSymbolRepresentative_coefficient
    (x : F.RealPolynomialSymbol w) (z : SymbolBasisIndex w ω) :
    (b.baseChange ℝ).repr
      (coefficients (F.realSymbolRepresentative b ω hlayers w x) z.val.1) z.val.2 =
      ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x z := by
  dsimp only [realSymbolRepresentative, LinearMap.coe_mk, AddHom.coe_mk]
  generalize ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x = c
  have hc := ofSupportedCoordinates_apply (σ := σ) (ι := ι) (R := ℚ) (S := ℝ) (V := ℝ ⊗[ℚ] L) (b.baseChange ℝ)
        {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}
        c z
  convert hc using 2

theorem realSymbolRepresentative_coefficient_of_ne
    (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) (i : ι)
    (h : Finsupp.weight w α ≠ ω i) :
    (b.baseChange ℝ).repr (coefficients (F.realSymbolRepresentative b ω hlayers w x) α) i = 0 := by
  dsimp only [realSymbolRepresentative, LinearMap.coe_mk, AddHom.coe_mk]
  generalize ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x = c
  have hc := ofSupportedCoordinates_apply_of_not_mem (σ := σ) (ι := ι) (R := ℚ) (S := ℝ) (V := ℝ ⊗[ℚ] L) (b.baseChange ℝ)
        {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}
        c α i h
  convert hc using 2

@[simp] theorem realSymbolOfPolynomial_coordinate
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (z : SymbolBasisIndex w ω) :
    ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
      (F.realSymbolOfPolynomial b ω hlayers w p) z =
      (b.baseChange ℝ).repr (coefficients p z.val.1) z.val.2 := by
  change (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
    (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.symm _)) z = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem realSymbolOfPolynomial_representative (x : F.RealPolynomialSymbol w) :
    F.realSymbolOfPolynomial b ω hlayers w (F.realSymbolRepresentative b ω hlayers w x) = x := by
  apply ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.injective
  ext z
  rw [F.realSymbolOfPolynomial_coordinate, F.realSymbolRepresentative_coefficient]

include hlayers

theorem real_mem_layer_iff_basis_coordinates (j : ℕ) (v : ℝ ⊗[ℚ] L) :
    v ∈ F.realification.layer j ↔ ∀ i, ¬ j ≤ ω i → (b.baseChange ℝ).repr v i = 0 := by
  change v ∈ (F.realLayer j).toSubmodule ↔ _
  rw [F.realLayer_eq_span_basis b j {i | j ≤ ω i} (hlayers j), basis_mem_span_image_iff]
  rfl

theorem realSymbolRepresentative_adapted (x : F.RealPolynomialSymbol w) :
    F.realification.Adapted w (F.realSymbolRepresentative b ω hlayers w x) := by
  rw [F.realification.adapted_iff_coefficients]
  intro α
  apply (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mpr
  intro i hi
  exact F.realSymbolRepresentative_coefficient_of_ne b ω hlayers w x α i
    (fun h => hi h.le)

theorem realSymbolRepresentative_constant (x : F.RealPolynomialSymbol w) :
    coefficients (F.realSymbolRepresentative b ω hlayers w x) 0 = 0 := by
  apply (b.baseChange ℝ).repr.injective
  ext i
  change (b.baseChange ℝ).repr (coefficients (F.realSymbolRepresentative b ω hlayers w x) 0) i = 0
  apply F.realSymbolRepresentative_coefficient_of_ne
  rw [map_zero]
  exact (F.adaptedBasis_weight_pos b ω hlayers i).ne

noncomputable def realAdaptedSymbolRepresentative (x : F.RealPolynomialSymbol w) :
    F.realification.adaptedLieSubalgebra w :=
  ⟨F.realSymbolRepresentative b ω hlayers w x,
    (F.realification.mem_adaptedSubmodule w _).mpr
      (F.realSymbolRepresentative_adapted b ω hlayers w x)⟩

@[simp] theorem realAdaptedSymbolRepresentative_coe (x : F.RealPolynomialSymbol w) :
    (F.realAdaptedSymbolRepresentative b ω hlayers w x : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) =
      F.realSymbolRepresentative b ω hlayers w x := rfl

theorem realSymbolOfPolynomial_eq_zero_iff
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realSymbolOfPolynomial b ω hlayers w p = 0 ↔
      ∀ α, coefficients (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
        F.realification.layer (Finsupp.weight w α + 1) := by
  constructor
  · intro hp α
    apply (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mpr
    intro i hi
    by_cases he : Finsupp.weight w α = ω i
    · have hc := F.realSymbolOfPolynomial_coordinate b ω hlayers w p ⟨(α, i), he⟩
      rw [hp, map_zero, Finsupp.zero_apply] at hc
      exact hc.symm
    · exact (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp
        (p.property α) i (by omega)
  · intro hp
    apply ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.injective
    ext z
    rw [map_zero, Finsupp.zero_apply, F.realSymbolOfPolynomial_coordinate]
    exact (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp
      (hp z.val.1) z.val.2 (by have hz := z.property; omega)

theorem realSymbolOfPolynomial_eq_iff_symbolMap_eq
    (p q : F.realification.adaptedLieSubalgebra w) :
    F.realSymbolOfPolynomial b ω hlayers w p = F.realSymbolOfPolynomial b ω hlayers w q ↔
      F.realification.polynomialSymbolMap w p = F.realification.polynomialSymbolMap w q := by
  rw [← sub_eq_zero, ← map_sub]
  change F.realSymbolOfPolynomial b ω hlayers w
    ((p - q : F.realification.adaptedLieSubalgebra w) : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) = 0 ↔ _
  rw [F.realSymbolOfPolynomial_eq_zero_iff b ω hlayers w (p - q),
    F.realification.polynomialSymbolMap_eq_iff]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hF

theorem realBasis_mem_layer (i : ι) : (b.baseChange ℝ) i ∈ F.realification.layer (ω i) := by
  apply (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mpr
  intro k hk
  have hki : k ≠ i := by rintro rfl; exact hk le_rfl
  rw [Basis.repr_self]
  exact Finsupp.single_eq_of_ne hki

theorem dualAdjoint_realBasis_coordinate (g : F.realification.Group) (i k : ι)
    (hki : ω k ≤ ω i) :
    (b.baseChange ℝ).repr (dualAdjoint g ((b.baseChange ℝ) i)) k =
      (b.baseChange ℝ).repr ((b.baseChange ℝ) i) k := by
  have hd := F.realification.dualAdjoint_sub_mem_next_layer (ω i) g ((b.baseChange ℝ) i)
    (F.realBasis_mem_layer b ω hF i)
  have hz := (F.real_mem_layer_iff_basis_coordinates b ω hF (ω i + 1) _).mp hd k
    (by omega)
  simpa only [map_sub, Finsupp.sub_apply, sub_eq_zero] using hz

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realSymbolRepresentative_slow_coefficients (T : σ → ℝ)
    (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hlayers w T M g)
    (α : σ →₀ ℕ) (i : ι) :
    |(b.baseChange ℝ).repr (coefficients (F.realSymbolRepresentative b ω hlayers w g.coord) α) i| ≤
      M / monomialScale T α := by
  by_cases h : Finsupp.weight w α = ω i
  · have hc := F.realSymbolRepresentative_coefficient b ω hlayers w g.coord ⟨(α, i), h⟩
    exact (congrArg abs hc).le.trans (hg ⟨(α, i), h⟩)
  · rw [F.realSymbolRepresentative_coefficient_of_ne b ω hlayers w g.coord α i h, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem realSymbolRepresentative_rational_coefficients (l : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hlayers w l g) :
    (fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
      (coefficients (F.realSymbolRepresentative b ω hlayers w g.coord) z.1) z.2)
        ∈ realDenominatorGrid l := by
  classical
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => if h : Finsupp.weight w z.1 = ω z.2 then a ⟨z, h⟩ else 0, ?_⟩
  funext z
  change ((if h : Finsupp.weight w z.1 = ω z.2 then a ⟨z, h⟩ else 0 : ℤ) : ℝ) =
    (l : ℝ) * (b.baseChange ℝ).repr
      (coefficients (F.realSymbolRepresentative b ω hlayers w g.coord) z.1) z.2
  by_cases h : Finsupp.weight w z.1 = ω z.2
  · rw [dif_pos h]
    have hc := F.realSymbolRepresentative_coefficient b ω hlayers w g.coord ⟨z, h⟩
    change (b.baseChange ℝ).repr
      (coefficients (F.realSymbolRepresentative b ω hlayers w g.coord) z.1) z.2 = _ at hc
    rw [hc]
    exact congrFun ha ⟨z, h⟩
  · rw [dif_neg h, Int.cast_zero,
      F.realSymbolRepresentative_coefficient_of_ne b ω hlayers w g.coord z.1 z.2 h, mul_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def gradedBasisSplitting : F.AssociatedGraded ≃ₗ[ℚ] L :=
  (F.associatedGradedBasis b ω hlayers).repr.trans b.repr.symm

@[simp] theorem gradedBasisSplitting_coordinate (x : F.AssociatedGraded) (i : ι) :
    b.repr (F.gradedBasisSplitting b ω hlayers x) i =
      (F.associatedGradedBasis b ω hlayers).repr x i := by
  simp [gradedBasisSplitting]

theorem gradedBasisSplitting_real_coordinate (x : ℝ ⊗[ℚ] F.AssociatedGraded) (i : ι) :
    (b.baseChange ℝ).repr
      ((F.gradedBasisSplitting b ω hlayers).toLinearMap.baseChange ℝ x) i =
      ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul]
    exact congrArg (fun q : ℚ => q • a) (F.gradedBasisSplitting_coordinate b ω hlayers x i)
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

variable (w : σ → ℕ)

theorem realSymbolRepresentative_coefficient_splitting (x : F.RealPolynomialSymbol w)
    (α : σ →₀ ℕ) :
    coefficients (F.realSymbolRepresentative b ω hlayers w x) α =
      (F.gradedBasisSplitting b ω hlayers).toLinearMap.baseChange ℝ
        (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) := by
  apply (b.baseChange ℝ).repr.injective
  ext i
  rw [F.gradedBasisSplitting_real_coordinate]
  by_cases h : Finsupp.weight w α = ω i
  · exact (F.realSymbolRepresentative_coefficient b ω hlayers w x ⟨(α, i), h⟩).trans
      (F.realGradedSymbolPolynomial_coordinate b ω hlayers w x ⟨(α, i), h⟩).symm
  · rw [F.realSymbolRepresentative_coefficient_of_ne b ω hlayers w x α i h,
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w x α i h]

theorem realSymbolRepresentative_eq_map (x : F.RealPolynomialSymbol w) :
    F.realSymbolRepresentative b ω hlayers w x =
      VectorPolynomial.map
        (((F.gradedBasisSplitting b ω hlayers).toLinearMap.baseChange ℝ).restrictScalars ℚ)
        (F.realGradedSymbolPolynomial b ω hlayers w x) := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  exact F.realSymbolRepresentative_coefficient_splitting b ω hlayers w x α

theorem realSymbolRepresentative_eval₂ (x : F.RealPolynomialSymbol w) (t : σ → ℝ) :
    eval₂ t (F.realSymbolRepresentative b ω hlayers w x) =
      (F.gradedBasisSplitting b ω hlayers).toLinearMap.baseChange ℝ
        (eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x)) := by
  rw [F.realSymbolRepresentative_eq_map, VectorPolynomial.eval₂_map]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RealifiedSubgroupLattice
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realificationSubgroupHom (K : LieSubalgebra ℚ L) :
    NilpotentLieBCHGroup (ℝ ⊗[ℚ] K) s
      (realification_lowerCentralSeries_eq_bot (lie_subalgebra_lowerCentralSeries_eq_bot hnil K)) →*
      realificationSubgroup (hnil := hnil) K :=
  (realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
    (hM := hnil) K.incl).codRestrict _ (realificationMap_incl_mem (hnil := hnil) K)

theorem realificationSubgroupHom_surjective (K : LieSubalgebra ℚ L) :
    Function.Surjective (realificationSubgroupHom (hnil := hnil) K) := by
  intro g
  have hg : g.1 ∈ (realificationMap
      (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) (hM := hnil) K.incl).range := by
    rw [realificationMap_incl_range]
    exact g.2
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, Subtype.ext hx⟩

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end


