-- Prove2me | Definitions.Def_OAIErdos3B095
-- name    : OAIErdos3B095
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T17:17:10.539978+00:00
-- url     : https://prove2.me/theorems/32166784-cfdf-43be-8e41-d4ef9007ddee
-- title:
--   OpenAI Erdős-3 split, definitions bundle 96 of 106
-- statement:
--   Definitions bundle 96 of 106 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B094`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 96 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.PolynomialRationalGrid`, `OAI.Erdos3.NilpotentLieFiltration.PolynomialSlowBound`, `OAI.Erdos3.NilpotentLieFiltration.RealAdaptedCoefficientBound`, `OAI.Erdos3.NilpotentLieFiltration.RealAdaptedPolynomialGroup`, `OAI.Erdos3.NilpotentLieFiltration.adaptedConstantGroupHom`, `OAI.Erdos3.NilpotentLieFiltration.adaptedConstantGroupHom_log`, `OAI.Erdos3.NilpotentLieFiltration.adaptedConstantLieHom`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialConstantHom`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialConstantHom_constant`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialConstantHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.affinePolynomialOrbit`, `OAI.Erdos3.NilpotentLieFiltration.affinePolynomialOrbit_integer_coord`, `OAI.Erdos3.NilpotentLieFiltration.affinePolynomialOrbit_log`, `OAI.Erdos3.NilpotentLieFiltration.affinePolynomialOrbit_real_coord`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedMap`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedMap_piece`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedPieceMap_repr_symm`, `OAI.Erdos3.NilpotentLieFiltration.exists_constant_normalized_polynomial`, `OAI.Erdos3.NilpotentLieFiltration.exists_polynomial_rational_product_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_polynomial_slow_product_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_scaled_polynomial_dual_bound`, `OAI.Erdos3.NilpotentLieFiltration.filteredPolynomialMap`, `OAI.Erdos3.NilpotentLieFiltration.filteredPolynomialMap_coe`, `OAI.Erdos3.NilpotentLieFiltration.filteredPolynomialMap_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.filteredPolynomialMap_mem_shiftedIdeal`, `OAI.Erdos3.NilpotentLieFiltration.filteredPolynomialMap_surjective`, `OAI.Erdos3.NilpotentLieFiltration.filteredPolynomialSymbolMap`, `OAI.Erdos3.NilpotentLieFiltration.filteredPolynomialSymbolMap_surjective`, `OAI.Erdos3.NilpotentLieFiltration.filteredPolynomialSymbolMap_symbol`, `OAI.Erdos3.NilpotentLieFiltration.gradedPieceProjection`, `OAI.Erdos3.NilpotentLieFiltration.gradedPieceProjection_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.gradedPieceProjection_eq_pieceMap`, `OAI.Erdos3.NilpotentLieFiltration.gradedRefiltrationLayer_eq_inf_comap`, `OAI.Erdos3.NilpotentLieFiltration.linearPolynomialGroup`, `OAI.Erdos3.NilpotentLieFiltration.linearPolynomialGroup_log`, `OAI.Erdos3.NilpotentLieFiltration.linearPolynomial_adapted`, `OAI.Erdos3.NilpotentLieFiltration.polynomialRationalGrid_constant`, `OAI.Erdos3.NilpotentLieFiltration.polynomialRationalGrid_groupHom_iff`, `OAI.Erdos3.NilpotentLieFiltration.polynomialRationalGrid_linear`, `OAI.Erdos3.NilpotentLieFiltration.polynomialRationalGrid_of_dvd`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_constant`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_groupHom_iff`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_inv_iff`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_linear`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_mono`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolHom_constant`, `OAI.Erdos3.NilpotentLieFiltration.polynomial_factor_middle_constant`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedCoefficientBound_mono`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedCoefficientBound_polynomial_iff`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedCoefficientBound_scaled_iff`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedMonomialBasis_bracket_support`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialGroupHom`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialGroupHom_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialGroupHom_lift`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialGroupHom_log`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialGroupHom_surjective`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialGroupLift`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialMap`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialMap_adapted`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialMap_coefficient_tmul`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialTensor`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialTensor_coe`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialTensor_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedPolynomialTensor_surjective`, `OAI.Erdos3.NilpotentLieFiltration.realAdapted_factor_middle_constant`, `OAI.Erdos3.NilpotentLieFiltration.realFilteredPolynomialMap_polynomial`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_coefficient_of_polynomial`, `OAI.Erdos3.NilpotentLieFiltration.realQuotientPolynomialOrbit_realEval`, `OAI.Erdos3.NilpotentLieFiltration.realQuotientPolynomialOrbit_surjective`, `OAI.Erdos3.NilpotentLieFiltration.real_gradedPieceProjection_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.scaledRealAdaptedMonomialBasis`, `OAI.Erdos3.NilpotentLieFiltration.scaledRealAdaptedMonomialBasis_bound_iff`, `OAI.Erdos3.NilpotentLieFiltration.scaledRealAdaptedMonomialBasis_repr`, `OAI.Erdos3.NilpotentLieFiltration.scaledRealAdaptedMonomialBasis_structure`, `OAI.Erdos3.NilpotentLieFiltration.shiftedGradedPolynomial`, `OAI.Erdos3.NilpotentLieFiltration.shiftedGradedPolynomial_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.shiftedGradedPolynomial_coefficient_of_mem`, `OAI.Erdos3.NilpotentLieFiltration.shiftedGradedPolynomial_eq_zero_iff`, `OAI.Erdos3.NilpotentLieFiltration.shiftedGradedPolynomial_monomial`, `OAI.Erdos3.NilpotentLieFiltration.shiftedGradedPolynomial_zero`, `OAI.Erdos3.NilpotentLieFiltration.stepOne_coord_mul`, `OAI.Erdos3.NilpotentLieFiltration.stepOne_lie_eq_zero`, `OAI.Erdos3.VectorPolynomial.mapLie`, `OAI.Erdos3.dualStructureConstants`, `OAI.Erdos3.dualStructureConstants_height`, `OAI.Erdos3.exists_dual_coordinate_operation_bound`, `OAI.Erdos3.exists_rational_dual_operation_grid`, `OAI.Erdos3.exists_real_dual_operation_grid`, `OAI.Erdos3.polynomialShearOrbitParameterCoordinates`, `OAI.Erdos3.polynomialShearOrbitParameterCoordinates_degree`, `OAI.Erdos3.polynomialShearReal_adapted_iff_coordinate_support`, `OAI.Erdos3.rationalDualBasis`, `OAI.Erdos3.rationalDualBasis_grid_iff`, `OAI.Erdos3.rationalDualBasis_inl`, `OAI.Erdos3.rationalDualBasis_inr`, `OAI.Erdos3.rationalDualBasis_repr_inl`, `OAI.Erdos3.rationalDualBasis_repr_inr`, `OAI.Erdos3.rationalDualBasis_structure`, `OAI.Erdos3.rationalDualBasis_structure_height`, `OAI.Erdos3.realDualBasis`, `OAI.Erdos3.realDualBasis_inl`, `OAI.Erdos3.realDualBasis_inr`, `OAI.Erdos3.realDualBasis_repr_inl`, `OAI.Erdos3.realDualBasis_repr_inr`, `OAI.Erdos3.realDualBasis_structure`, `OAI.Erdos3.real_dual_adjoint_grid_of_rational`, `OAI.Erdos3.real_dual_log_grid_of_rational`, `OAI.Erdos3.weightedPolynomialShearOrbitParameterCoordinates`, `OAI.Erdos3.weightedPolynomialShearOrbitParameterCoordinates_degree`, `OAI.Erdos3.weightedPolynomialShearReal_adapted_iff_coordinate_support`, `_private.Linear.RealDualRationalBounds.0.OAI.Erdos3.dual_basis_bound`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B023

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealDualRationalBounds
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

noncomputable def realDualBasis (b : Basis ι ℝ L) : Basis (ι ⊕ ι) ℝ (DualLieAlgebra L) :=
  (b.prod b).map dualRealCoordinates.symm

@[simp] theorem realDualBasis_inl (b : Basis ι ℝ L) (i : ι) :
    realDualBasis b (Sum.inl i) = dualConstantLie (b i) := by
  simp [realDualBasis, Basis.map_apply]

@[simp] theorem realDualBasis_inr (b : Basis ι ℝ L) (i : ι) :
    realDualBasis b (Sum.inr i) = dualInfinitesimal (b i) := by
  simp [realDualBasis, Basis.map_apply]

@[simp] theorem realDualBasis_repr_inl (b : Basis ι ℝ L) (x : DualLieAlgebra L) (i : ι) :
    (realDualBasis b).repr x (Sum.inl i) = b.repr (dualBaseLinear x) i := by
  simp [realDualBasis, Basis.map_repr]

@[simp] theorem realDualBasis_repr_inr (b : Basis ι ℝ L) (x : DualLieAlgebra L) (i : ι) :
    (realDualBasis b).repr x (Sum.inr i) = b.repr (dualTangentLinear x) i := by
  simp [realDualBasis, Basis.map_repr]

def dualStructureConstants (c : ι → ι → ι → ℚ) : (ι ⊕ ι) → (ι ⊕ ι) → (ι ⊕ ι) → ℚ
  | Sum.inl i, Sum.inl j, Sum.inl k => c i j k
  | Sum.inl i, Sum.inr j, Sum.inr k => c i j k
  | Sum.inr i, Sum.inl j, Sum.inr k => c i j k
  | _, _, _ => 0

theorem realDualBasis_structure (b : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ ℝ (c i j k) = b.repr ⁅b i, b j⁆ k)
    (i j k : ι ⊕ ι) :
    algebraMap ℚ ℝ (dualStructureConstants c i j k) =
      (realDualBasis b).repr ⁅realDualBasis b i, realDualBasis b j⁆ k := by
  cases i <;> cases j <;> cases k <;>
    simp [dualStructureConstants, dualBaseLinear_lie, dualTangentLinear_lie, ← hc]

theorem dualStructureConstants_height (c : ι → ι → ι → ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (i j k : ι ⊕ ι) :
    RationalHeightLE (dualStructureConstants c i j k) H := by
  cases i <;> cases j <;> cases k <;>
    first | exact hc _ _ _ | exact rationalHeightLE_zero hH

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem dual_basis_bound {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L] (e : Basis ι ℝ L)
    (z : DualLieAlgebra L) (M : ℝ)
    (hb : ∀ i, |e.repr (dualBaseLinear z) i| ≤ M)
    (ht : ∀ i, |e.repr (dualTangentLinear z) i| ≤ M) :
    ∀ i, |(realDualBasis e).repr z i| ≤ M := by
  intro i
  cases i with
  | inl i => simpa only [realDualBasis_repr_inl] using hb i
  | inr i => simpa only [realDualBasis_repr_inr] using ht i

theorem exists_dual_coordinate_operation_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L]
      [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      1 ≤ H → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      (∀ z : DualGroup hnil,
        (∀ i, |e.repr (dualBaseLinear z.coord) i| ≤ Real.exp ((p + 2) ^ a)) →
        (∀ i, |e.repr (dualTangentLinear z.coord) i| ≤ Real.exp ((p + 2) ^ a)) →
        ∀ i, |e.repr (dualLogDerivative z) i| ≤ Real.exp ((p + C) ^ C)) ∧
      (∀ (g : NilpotentLieBCHGroup L s hnil) (x : L),
        (∀ i, |e.repr g.coord i| ≤ Real.exp ((p + 2) ^ a)) →
        (∀ i, |e.repr x i| ≤ Real.exp ((p + 2) ^ a)) →
        ∀ i, |e.repr (dualAdjoint g x) i| ≤ Real.exp ((p + C) ^ C)) := by
  have hproductExists := exists_bch_fixed_product_exp_bound s a 3
  obtain ⟨K, _, hproduct⟩ := hproductExists
  let B : Polynomial ℕ := (2 * Polynomial.X + Polynomial.C K) ^ K
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ _ _ e c H p hnil hstructure hH hp hd hHp hc
  have hfinal : (2 * p + K) ^ K ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbound p hp
  have hinput : Real.exp ((p + 2) ^ a) ≤ Real.exp ((2 * p + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a)
  have hdim : (Fintype.card (ι ⊕ ι) : ℝ) ≤ 2 * p := by
    rw [Fintype.card_sum, Nat.cast_add]
    linarith
  have hproducts (rs : List (DualGroup hnil)) (hlen : rs.length ≤ 3)
      (hrs : ∀ r ∈ rs, ∀ i,
        |(realDualBasis e).repr r.coord i| ≤ Real.exp ((p + 2) ^ a)) :
      ∀ i, |(realDualBasis e).repr rs.prod.coord i| ≤ Real.exp ((p + C) ^ C) := by
    have hb := hproduct (realDualBasis e) (dualStructureConstants c) H (2 * p)
      (dualLie_lowerCentralSeries_eq_bot hnil) rs (realDualBasis_structure e c hstructure)
      (by positivity) hdim hlen (hHp.trans (Real.exp_le_exp.mpr (by linarith)))
      (dualStructureConstants_height c hH hc) (fun r hr i => (hrs r hr i).trans hinput)
    exact fun i => (hb i).trans (Real.exp_le_exp.mpr hfinal)
  constructor
  · intro z hbase htangent i
    have hconst : ∀ j, |(realDualBasis e).repr
        ((dualConstantHom (dualBaseHom z))⁻¹).coord j| ≤ Real.exp ((p + 2) ^ a) := by
      apply dual_basis_bound
      · intro j
        change |e.repr (dualBaseLinear (-dualConstantLie (dualBaseLinear z.coord))) j| ≤ _
        simpa only [map_neg, dualBaseLinear_constant, Finsupp.neg_apply, abs_neg] using hbase j
      · intro j
        change |e.repr (dualTangentLinear (-dualConstantLie (dualBaseLinear z.coord))) j| ≤ _
        simp only [map_neg, dualTangentLinear_constant, neg_zero, map_zero, Finsupp.zero_apply, abs_zero]
        exact Real.exp_nonneg _
    have hinputs : ∀ r ∈ [z, (dualConstantHom (dualBaseHom z))⁻¹],
        ∀ j, |(realDualBasis e).repr r.coord j| ≤ Real.exp ((p + 2) ^ a) := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dual_basis_bound e _ _ hbase htangent
      · exact hconst
    have hh := hproducts [z, (dualConstantHom (dualBaseHom z))⁻¹] (by simp) hinputs (Sum.inr i)
    simpa only [List.prod_cons, List.prod_nil, mul_one, realDualBasis_repr_inr, dualLogDerivative] using hh
  · intro g x hg hx i
    have hleft : ∀ j, |(realDualBasis e).repr (dualConstantHom g).coord j| ≤
        Real.exp ((p + 2) ^ a) := by
      apply dual_basis_bound
      · intro j
        change |e.repr (dualBaseLinear (dualConstantLie g.coord)) j| ≤ _
        simpa only [dualBaseLinear_constant] using hg j
      · intro j
        change |e.repr (dualTangentLinear (dualConstantLie g.coord)) j| ≤ _
        simp only [dualTangentLinear_constant, map_zero, Finsupp.zero_apply, abs_zero]
        exact Real.exp_nonneg _
    have hmiddle : ∀ j, |(realDualBasis e).repr (dualTangentElement (hnil := hnil) x).coord j| ≤
        Real.exp ((p + 2) ^ a) := by
      apply dual_basis_bound
      · intro j
        change |e.repr (dualBaseLinear (dualInfinitesimal x)) j| ≤ _
        simp only [dualBaseLinear_infinitesimal, map_zero, Finsupp.zero_apply, abs_zero]
        exact Real.exp_nonneg _
      · intro j
        change |e.repr (dualTangentLinear (dualInfinitesimal x)) j| ≤ _
        simpa only [dualTangentLinear_infinitesimal] using hx j
    have hright : ∀ j, |(realDualBasis e).repr ((dualConstantHom g)⁻¹).coord j| ≤
        Real.exp ((p + 2) ^ a) := by
      intro j
      simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hleft j
    have hinputs : ∀ r ∈ [dualConstantHom g, dualTangentElement x, (dualConstantHom g)⁻¹],
        ∀ j, |(realDualBasis e).repr r.coord j| ≤ Real.exp ((p + 2) ^ a) := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hleft
      · exact hmiddle
      · exact hright
    have hh := hproducts [dualConstantHom g, dualTangentElement x, (dualConstantHom g)⁻¹]
      (by simp) hinputs (Sum.inr i)
    simpa only [List.prod_cons, List.prod_nil, mul_one, ← mul_assoc, realDualBasis_repr_inr, dualAdjoint] using hh

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def rationalDualBasis (b : Basis ι ℚ L) : Basis (ι ⊕ ι) ℚ (DualLieAlgebra L) :=
  (b.prod b).map dualCoordinates.symm

@[simp] theorem rationalDualBasis_inl (b : Basis ι ℚ L) (i : ι) :
    rationalDualBasis b (Sum.inl i) = dualConstantLie (b i) := by
  simp [rationalDualBasis, Basis.map_apply]

@[simp] theorem rationalDualBasis_inr (b : Basis ι ℚ L) (i : ι) :
    rationalDualBasis b (Sum.inr i) = dualInfinitesimal (b i) := by
  simp [rationalDualBasis, Basis.map_apply]

@[simp] theorem rationalDualBasis_repr_inl (b : Basis ι ℚ L) (x : DualLieAlgebra L) (i : ι) :
    (rationalDualBasis b).repr x (Sum.inl i) = b.repr (dualBaseLinear x) i := by
  simp [rationalDualBasis, Basis.map_repr]

@[simp] theorem rationalDualBasis_repr_inr (b : Basis ι ℚ L) (x : DualLieAlgebra L) (i : ι) :
    (rationalDualBasis b).repr x (Sum.inr i) = b.repr (dualTangentLinear x) i := by
  simp [rationalDualBasis, Basis.map_repr]

theorem rationalDualBasis_structure (b : Basis ι ℚ L) (i j k : ι ⊕ ι) :
    lieStructureConstants (L := DualLieAlgebra L) (rationalDualBasis b) i j k =
      dualStructureConstants (lieStructureConstants b) i j k := by
  cases i <;> cases j <;> cases k <;>
    simp [lieStructureConstants, dualStructureConstants, dualBaseLinear_lie, dualTangentLinear_lie]

theorem rationalDualBasis_structure_height (b : Basis ι ℚ L) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) (i j k : ι ⊕ ι) :
    RationalHeightLE (lieStructureConstants (L := DualLieAlgebra L) (rationalDualBasis b) i j k) H := by
  rw [rationalDualBasis_structure]
  exact dualStructureConstants_height _ hH hc i j k

theorem rationalDualBasis_grid_iff [Fintype ι] (b : Basis ι ℚ L) (l : ℕ) (x : DualLieAlgebra L) :
    (rationalDualBasis b).equivFun x ∈ denominatorGrid l ↔
      b.equivFun (dualBaseLinear x) ∈ denominatorGrid l ∧
      b.equivFun (dualTangentLinear x) ∈ denominatorGrid l := by
  constructor
  · rintro ⟨a, ha⟩
    constructor
    · exact ⟨fun i => a (Sum.inl i), fun i => by
        simpa only [Basis.equivFun_apply, Pi.smul_apply, rationalDualBasis_repr_inl] using ha (Sum.inl i)⟩
    · exact ⟨fun i => a (Sum.inr i), fun i => by
        simpa only [Basis.equivFun_apply, Pi.smul_apply, rationalDualBasis_repr_inr] using ha (Sum.inr i)⟩
  · rintro ⟨⟨a, ha⟩, ⟨b', hb'⟩⟩
    refine ⟨Sum.elim a b', ?_⟩
    intro i
    cases i with
    | inl i => simpa only [Sum.elim_inl, Basis.equivFun_apply, Pi.smul_apply, rationalDualBasis_repr_inl] using ha i
    | inr i => simpa only [Sum.elim_inr, Basis.equivFun_apply, Pi.smul_apply, rationalDualBasis_repr_inr] using hb' i

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem exists_rational_dual_operation_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      1 ≤ H → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ z : DualGroup hnil,
          e.equivFun (dualBaseLinear z.coord) ∈ denominatorGrid l →
          e.equivFun (dualTangentLinear z.coord) ∈ denominatorGrid l →
          e.equivFun (dualLogDerivative z) ∈ denominatorGrid m) ∧
        (∀ (g : NilpotentLieBCHGroup L s hnil) (x : L),
          e.equivFun g.coord ∈ denominatorGrid l → e.equivFun x ∈ denominatorGrid l →
          e.equivFun (dualAdjoint g x) ∈ denominatorGrid m) := by
  have hproductsExists := exists_bch_rational_product_bound s 3
  obtain ⟨D, _, hproducts⟩ := hproductsExists
  let B : Polynomial ℕ := (2 * Polynomial.X + Polynomial.C D) ^ D
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hnil hH hp hd hHp hc l hl hlp
  have hp2 : p ≤ 2 * p := by linarith
  have hdim : (Fintype.card (ι ⊕ ι) : ℝ) ≤ 2 * p := by
    rw [Fintype.card_sum, Nat.cast_add]
    linarith
  have hdata := hproducts (rationalDualBasis e) H (2 * p) (dualLie_lowerCentralSeries_eq_bot hnil)
    (by positivity) hdim (hHp.trans (Real.exp_le_exp.mpr hp2))
    (rationalDualBasis_structure_height e hH hc) l hl (hlp.trans (Real.exp_le_exp.mpr hp2))
  obtain ⟨m, hm, hmp, hlm, hprod⟩ := hdata
  have hfinal : (2 * p + D) ^ D ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbound p hp
  have hzero : (0 : ι → ℚ) ∈ denominatorGrid l := ⟨0, by intro i; simp⟩
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hfinal), hlm, ?_, ?_⟩
  · intro z hb ht
    have hz := (rationalDualBasis_grid_iff e l z.coord).mpr ⟨hb, ht⟩
    have hconst : (rationalDualBasis e).equivFun (dualConstantHom (dualBaseHom z)).coord ∈
        denominatorGrid l := by
      apply (rationalDualBasis_grid_iff e l _).mpr
      change e.equivFun (dualBaseLinear (dualConstantLie (dualBaseLinear z.coord))) ∈ _ ∧
        e.equivFun (dualTangentLinear (dualConstantLie (dualBaseLinear z.coord))) ∈ _
      simpa only [dualBaseLinear_constant, dualTangentLinear_constant, map_zero] using And.intro hb hzero
    have hinv : (rationalDualBasis e).equivFun ((dualConstantHom (dualBaseHom z))⁻¹).coord ∈
        denominatorGrid l := by
      simpa only [coord_inv, map_neg] using denominatorGrid_neg l hconst
    have hinputs : ∀ r ∈ [z, (dualConstantHom (dualBaseHom z))⁻¹],
        (rationalDualBasis e).equivFun r.coord ∈ denominatorGrid l := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hz
      · exact hinv
    have hout := (rationalDualBasis_grid_iff e m _).mp
      (hprod [z, (dualConstantHom (dualBaseHom z))⁻¹] (by simp) hinputs)
    simpa only [List.prod_cons, List.prod_nil, mul_one, dualLogDerivative] using hout.2
  · intro g x hg hx
    have hleft : (rationalDualBasis e).equivFun (dualConstantHom g).coord ∈ denominatorGrid l := by
      apply (rationalDualBasis_grid_iff e l _).mpr
      change e.equivFun (dualBaseLinear (dualConstantLie g.coord)) ∈ _ ∧
        e.equivFun (dualTangentLinear (dualConstantLie g.coord)) ∈ _
      simpa only [dualBaseLinear_constant, dualTangentLinear_constant, map_zero] using And.intro hg hzero
    have hmiddle : (rationalDualBasis e).equivFun (dualTangentElement (hnil := hnil) x).coord ∈
        denominatorGrid l := by
      apply (rationalDualBasis_grid_iff e l _).mpr
      change e.equivFun (dualBaseLinear (dualInfinitesimal x)) ∈ _ ∧
        e.equivFun (dualTangentLinear (dualInfinitesimal x)) ∈ _
      simpa only [dualBaseLinear_infinitesimal, dualTangentLinear_infinitesimal, map_zero] using And.intro hzero hx
    have hright : (rationalDualBasis e).equivFun ((dualConstantHom g)⁻¹).coord ∈ denominatorGrid l := by
      simpa only [coord_inv, map_neg] using denominatorGrid_neg l hleft
    have hinputs : ∀ r ∈ [dualConstantHom g, dualTangentElement x, (dualConstantHom g)⁻¹],
        (rationalDualBasis e).equivFun r.coord ∈ denominatorGrid l := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hleft
      · exact hmiddle
      · exact hright
    have hout := (rationalDualBasis_grid_iff e m _).mp
      (hprod [dualConstantHom g, dualTangentElement x, (dualConstantHom g)⁻¹] (by simp) hinputs)
    simpa only [List.prod_cons, List.prod_nil, mul_one, ← mul_assoc, dualAdjoint] using hout.2

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem real_dual_log_grid_of_rational (e : Basis ι ℚ L) (l m : ℕ) (hl : 0 < l)
    (hlog : ∀ z : DualGroup hnil,
      e.equivFun (dualBaseLinear z.coord) ∈ denominatorGrid l →
      e.equivFun (dualTangentLinear z.coord) ∈ denominatorGrid l →
      e.equivFun (dualLogDerivative z) ∈ denominatorGrid m)
    (z : DualGroup (realification_lowerCentralSeries_eq_bot hnil))
    (hb : (e.baseChange ℝ).equivFun (dualBaseLinear z.coord) ∈ realDenominatorGrid l)
    (ht : (e.baseChange ℝ).equivFun (dualTangentLinear z.coord) ∈ realDenominatorGrid l) :
    (e.baseChange ℝ).equivFun (dualLogDerivative z) ∈ realDenominatorGrid m := by
  obtain ⟨a, ha, hea⟩ := real_grid_exists_rationalLieInclusion e l hl _ hb
  obtain ⟨b, hb, heb⟩ := real_grid_exists_rationalLieInclusion e l hl _ ht
  let q : DualGroup hnil := ⟨dualConstantLie a + dualInfinitesimal b⟩
  have hqa : dualBaseLinear q.coord = a := by
    change dualBaseLinear (dualConstantLie a + dualInfinitesimal b) = a
    simp only [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]
  have hqb : dualTangentLinear q.coord = b := by
    change dualTangentLinear (dualConstantLie a + dualInfinitesimal b) = b
    simp only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]
  have hq := hlog q (by rwa [hqa]) (by rwa [hqb])
  have he : rationalLieInclusion (dualLogDerivative q) = dualLogDerivative z := by
    apply dualLinearLift_logDerivative_eq (realification_lowerCentralSeries_eq_bot hnil)
      (⊤ : LieIdeal ℚ L) rationalLieInclusion rationalLieInclusion.toLinearMap
      (fun x y _ => rationalLieInclusion.map_lie x y) q (by trivial) z
    apply dual_ext
    · rw [dualLinearLift_base, hqa]
      exact hea
    · rw [dualLinearLift_tangent, hqb]
      exact heb
  change (fun i => (e.baseChange ℝ).repr (dualLogDerivative z) i) ∈ realDenominatorGrid m
  rw [← he]
  simp_rw [rationalLieInclusion_coordinates]
  exact (real_cast_mem_denominatorGrid_iff m _).mpr hq

theorem real_dual_adjoint_grid_of_rational (e : Basis ι ℚ L) (l m : ℕ) (hl : 0 < l)
    (had : ∀ (g : NilpotentLieBCHGroup L s hnil) (x : L),
      e.equivFun g.coord ∈ denominatorGrid l → e.equivFun x ∈ denominatorGrid l →
      e.equivFun (dualAdjoint g x) ∈ denominatorGrid m)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (x : ℝ ⊗[ℚ] L)
    (hg : (e.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l)
    (hx : (e.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    (e.baseChange ℝ).equivFun (dualAdjoint g x) ∈ realDenominatorGrid m := by
  obtain ⟨a, ha, hea⟩ := real_grid_exists_rationalLieInclusion e l hl _ hg
  obtain ⟨b, hb, heb⟩ := real_grid_exists_rationalLieInclusion e l hl _ hx
  let q : NilpotentLieBCHGroup L s hnil := ⟨a⟩
  have hq := had q b ha hb
  have he : rationalLieInclusion (dualAdjoint q b) = dualAdjoint g x :=
    dualLinearLift_adjoint_eq (realification_lowerCentralSeries_eq_bot hnil)
      (⊤ : LieIdeal ℚ L) rationalLieInclusion rationalLieInclusion.toLinearMap
      (fun u v _ => rationalLieInclusion.map_lie u v) q b (by trivial) g x hea heb
  change (fun i => (e.baseChange ℝ).repr (dualAdjoint g x) i) ∈ realDenominatorGrid m
  rw [← he]
  simp_rw [rationalLieInclusion_coordinates]
  exact (real_cast_mem_denominatorGrid_iff m _).mpr hq

theorem exists_real_dual_operation_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      1 ≤ H → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ z : DualGroup (realification_lowerCentralSeries_eq_bot hnil),
          (e.baseChange ℝ).equivFun (dualBaseLinear z.coord) ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (dualTangentLinear z.coord) ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (dualLogDerivative z) ∈ realDenominatorGrid m) ∧
        (∀ (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
          (x : ℝ ⊗[ℚ] L),
          (e.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun x ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (dualAdjoint g x) ∈ realDenominatorGrid m) := by
  have hratExists := exists_rational_dual_operation_grid s
  obtain ⟨C, hC, hrat⟩ := hratExists
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hnil hH hp hd hHp hc l hl hlp
  have hdata := hrat e H p hnil hH hp hd hHp hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hlog, had⟩ := hdata
  exact ⟨m, hm, hmp, hlm, real_dual_log_grid_of_rational e l m hl hlog,
    real_dual_adjoint_grid_of_rational e l m hl had⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealAdaptedPolynomialGroup
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

variable {σ R L M : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

noncomputable def mapLie (f : L →ₗ⁅R⁆ M) :
    VectorPolynomial σ R L →ₗ⁅R⁆ VectorPolynomial σ R M where
  toLinearMap := map f.toLinearMap
  map_lie' {p q} :=
    (LieAlgebra.ExtendScalars.map (AlgHom.id R (MvPolynomial σ R)) f).map_lie p q

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (f : L →ₗ⁅ℚ⁆ M) (hf : ∀ j, ∀ x ∈ F.layer j, f x ∈ G.layer j)
  (w : σ → ℕ)

noncomputable def filteredPolynomialMap :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ G.adaptedLieSubalgebra w :=
  { ((VectorPolynomial.map f.toLinearMap).comp (F.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
      (G.adaptedLieSubalgebra w).toSubmodule (by
        intro p α
        change coefficients (VectorPolynomial.map f.toLinearMap p.val) α ∈ _
        rw [coefficients_map]
        exact hf _ _ (p.property α)) with
    map_lie' {p q} := by
      apply Subtype.ext
      exact (VectorPolynomial.mapLie f).map_lie p.val q.val }

@[simp] theorem filteredPolynomialMap_coe (p : F.adaptedLieSubalgebra w) :
    (F.filteredPolynomialMap G f hf w p : VectorPolynomial σ ℚ M) =
      VectorPolynomial.map f.toLinearMap p.val := rfl

theorem filteredPolynomialMap_mem_shiftedIdeal {p : F.adaptedLieSubalgebra w}
    (hp : p ∈ F.shiftedAdaptedIdeal w) :
    F.filteredPolynomialMap G f hf w p ∈ G.shiftedAdaptedIdeal w := by
  intro α
  change coefficients (VectorPolynomial.map f.toLinearMap p.val) α ∈ _
  rw [coefficients_map]
  exact hf _ _ (hp α)

noncomputable def filteredPolynomialSymbolMap : F.PolynomialSymbol w →ₗ⁅ℚ⁆ G.PolynomialSymbol w :=
  { toLinearMap := (F.shiftedAdaptedIdeal w).toSubmodule.liftQ
      ((G.polynomialSymbolMap w).toLinearMap.comp (F.filteredPolynomialMap G f hf w).toLinearMap) (by
        intro p hp
        exact (lieQuotientMap_eq_zero (G.shiftedAdaptedIdeal w) _).mpr
          (F.filteredPolynomialMap_mem_shiftedIdeal G f hf w hp))
    map_lie' {x y} := by
      obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
      obtain ⟨q, rfl⟩ := F.polynomialSymbolMap_surjective w y
      change G.polynomialSymbolMap w (F.filteredPolynomialMap G f hf w ⁅p, q⁆) =
        ⁅G.polynomialSymbolMap w (F.filteredPolynomialMap G f hf w p),
          G.polynomialSymbolMap w (F.filteredPolynomialMap G f hf w q)⁆
      rw [LieHom.map_lie, LieHom.map_lie] }

@[simp] theorem filteredPolynomialSymbolMap_symbol (p : F.adaptedLieSubalgebra w) :
    F.filteredPolynomialSymbolMap G f hf w (F.polynomialSymbolMap w p) =
      G.polynomialSymbolMap w (F.filteredPolynomialMap G f hf w p) := rfl

noncomputable def associatedGradedMap : F.AssociatedGraded →ₗ⁅ℚ⁆ G.AssociatedGraded :=
  F.filteredPolynomialSymbolMap G f hf (fun _ : Unit => 1)

@[simp] theorem associatedGradedMap_piece (j : ℕ) (x : F.layer j) :
    F.associatedGradedMap G f hf (F.associatedGradedPieceMap j x) =
      G.associatedGradedPieceMap j ⟨f x, hf j x x.property⟩ := by
  change G.polynomialSymbolMap (fun _ : Unit => 1)
    (F.filteredPolynomialMap G f hf (fun _ : Unit => 1) (F.gradedMonomialLinear j x)) = _
  apply congrArg (G.polynomialSymbolMap (fun _ : Unit => 1))
  apply Subtype.ext
  exact VectorPolynomial.map_monomial f.toLinearMap (unitMonomial j) x

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (f : L →ₗ⁅ℚ⁆ M) (hf : ∀ j, ∀ x ∈ F.layer j, f x ∈ G.layer j)
  (w : σ → ℕ)

@[simp] theorem filteredPolynomialMap_coefficient (p : F.adaptedLieSubalgebra w)
    (α : σ →₀ ℕ) :
    coefficients (F.filteredPolynomialMap G f hf w p).val α = f (coefficients p.val α) :=
  coefficients_map f.toLinearMap p.val α

theorem filteredPolynomialMap_surjective
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, f x = y) :
    Function.Surjective (F.filteredPolynomialMap G f hf w) := by
  classical
  intro q
  let v (α : σ →₀ ℕ) : L := if coefficients q.val α = 0 then 0 else
    Classical.choose (hsurj (Finsupp.weight w α) (coefficients q.val α) (q.property α))
  have hv (α : σ →₀ ℕ) : f (v α) = coefficients q.val α := by
    dsimp only [v]
    split_ifs with hz
    · rw [map_zero, hz]
    · exact (Classical.choose_spec (hsurj _ _ (q.property α))).2
  have hmem (α : σ →₀ ℕ) : v α ∈ F.layer (Finsupp.weight w α) := by
    dsimp only [v]
    split_ifs
    · exact Submodule.zero_mem _
    · exact (Classical.choose_spec (hsurj _ _ (q.property α))).1
  let c : (σ →₀ ℕ) →₀ L := Finsupp.onFinset (coefficients q.val).support v (by
    intro α hα
    apply Finsupp.mem_support_iff.mpr
    intro hz
    exact hα (by simp only [v, hz, ite_true]))
  let p : F.adaptedLieSubalgebra w := ⟨coefficients.symm c, by
    intro α
    simpa only [LinearEquiv.apply_symm_apply, c, Finsupp.onFinset_apply] using hmem α⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.filteredPolynomialMap_coefficient G f hf w]
  simpa only [p, LinearEquiv.apply_symm_apply, c, Finsupp.onFinset_apply] using hv α

theorem filteredPolynomialSymbolMap_surjective
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, f x = y) :
    Function.Surjective (F.filteredPolynomialSymbolMap G f hf w) := by
  intro y
  obtain ⟨q, rfl⟩ := G.polynomialSymbolMap_surjective w y
  obtain ⟨p, rfl⟩ := F.filteredPolynomialMap_surjective G f hf w hsurj q
  exact ⟨F.polynomialSymbolMap w p, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (w : σ → ℕ)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (I : LieIdeal ℚ L)
    (hI : F.layer (t + 1) ≤ I.toSubmodule) {w : σ → ℕ}

theorem realQuotientPolynomialOrbit_surjective :
    Function.Surjective (F.realQuotientPolynomialOrbit I hI (w := w)) := by
  intro q
  let φ := realLieHomToRat (realificationLieHom (lieQuotientMap I))
  have hf : ∀ j, ∀ x ∈ F.realification.layer j,
      φ x ∈ (F.quotientLie I hI).realification.layer j := by
    intro j x hx
    exact F.realQuotientStep_mem_layer I hI hx
  have hsurj : ∀ j, ∀ y ∈ (F.quotientLie I hI).realification.layer j,
      ∃ x ∈ F.realification.layer j, φ x = y := by
    intro j y hy
    change y ∈ ((F.layer j).map (lieQuotientMap I).toLinearMap).baseChange ℝ at hy
    rw [realification_map] at hy
    exact hy
  obtain ⟨p, hp⟩ := F.realification.filteredPolynomialMap_surjective
    (F.quotientLie I hI).realification φ hf w hsurj
    ⟨q.log, ((F.quotientLie I hI).realification.mem_adaptedSubmodule w q.log).mpr q.adapted⟩
  let g : F.realification.PolynomialOrbit w :=
    polynomialOrbitOfLog p.val ((F.realification.mem_adaptedSubmodule w p.val).mp p.property)
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.map φ.toLinearMap p.val = q.log
  exact congrArg Subtype.val hp

theorem realQuotientPolynomialOrbit_realEval
    (g : F.realification.PolynomialOrbit w) (z : σ → ℝ) :
    (F.quotientLie I hI).realification.polynomialOrbitRealEval w z
      (F.realQuotientPolynomialOrbit I hI g) =
      F.realQuotientStepHom I hI (F.realification.polynomialOrbitRealEval w z g) := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_map (realificationLieHom (lieQuotientMap I)).toLinearMap z g.log

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def realAdaptedPolynomialMap :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  VectorPolynomial.realificationLieEquiv.toLieHom.comp
    (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) (F.adaptedLieSubalgebra w).incl)

@[simp] theorem realAdaptedPolynomialMap_coefficient_tmul
    (a : ℝ) (p : F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.realAdaptedPolynomialMap w (a ⊗ₜ[ℚ] p)) α =
      a ⊗ₜ[ℚ] coefficients (p : VectorPolynomial σ ℚ L) α := by
  change coefficients (VectorPolynomial.realificationLieEquiv
    (a ⊗ₜ[ℚ] (p : VectorPolynomial σ ℚ L))) α = _
  have hc := coefficients_realificationLieEquiv_tmul a (p : VectorPolynomial σ ℚ L) α
  convert hc using 2

theorem realAdaptedPolynomialMap_adapted (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realification.Adapted w (F.realAdaptedPolynomialMap w x) := by
  rw [F.realification.adapted_iff_coefficients]
  intro α
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    rw [F.realAdaptedPolynomialMap_coefficient_tmul]
    exact LieSubmodule.tmul_mem_baseChange_of_mem a (p.property α)
  | add x y hx hy =>
    rw [map_add, map_add, Finsupp.add_apply]
    exact Submodule.add_mem _ hx hy

noncomputable def realAdaptedPolynomialTensor :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ⁅ℚ⁆ F.realification.adaptedLieSubalgebra w where
  toLinearMap := (F.realAdaptedPolynomialMap w).toLinearMap.codRestrict
    (F.realification.adaptedSubmodule w) (fun x =>
      (F.realification.mem_adaptedSubmodule w _).mpr (F.realAdaptedPolynomialMap_adapted w x))
  map_lie' {x y} := by
    apply Subtype.ext
    exact (F.realAdaptedPolynomialMap w).map_lie x y

@[simp] theorem realAdaptedPolynomialTensor_coe (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    (F.realAdaptedPolynomialTensor w x : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) =
      F.realAdaptedPolynomialMap w x := rfl

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realAdaptedPolynomialTensor_coordinates
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}) :
    (b.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap w x) z.val.1) z.val.2 =
      ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr x z := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    rw [F.realAdaptedPolynomialMap_coefficient_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, F.adaptedMonomialBasis_repr]
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply, hx, hy]

include b ω hlayers in
theorem realAdaptedPolynomialTensor_surjective :
    Function.Surjective (F.realAdaptedPolynomialTensor w) := by
  intro p
  let c := supportedCoordinates (b.baseChange ℝ)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 ≤ ω z.2}
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  let x := ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr.symm c
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply coefficients.injective
  ext α
  apply (b.baseChange ℝ).repr.injective
  ext i
  by_cases h : Finsupp.weight w α ≤ ω i
  · have hc := F.realAdaptedPolynomialTensor_coordinates w b ω hlayers x ⟨(α, i), h⟩
    change (b.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap w x) α) i = _
    rw [hc]
    change (((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr
      (((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr.symm c)) ⟨(α, i), h⟩ = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · have hleft := (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp
      ((F.realification.adapted_iff_coefficients w _).mp
        (F.realAdaptedPolynomialMap_adapted w x) α) i h
    have hright := (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp (p.property α) i h
    exact hleft.trans hright.symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedMonomialBasis_bracket_support (u v z : AdaptedBasisIndex w ω)
    (h : ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr
      ⁅(F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ u,
        (F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ v⁆ z ≠ 0) :
    u.val.1 + v.val.1 = z.val.1 := by
  classical
  by_contra hn
  apply h
  rw [realLieBasis_structure]
  change (((F.adaptedMonomialBasis b ω hlayers w).repr
    ⁅F.adaptedMonomialBasis b ω hlayers w u,
      F.adaptedMonomialBasis b ω hlayers w v⁆ z : ℚ) : ℝ) = 0
  simp only [F.adaptedMonomialBasis_bracket, hn, ite_false, Rat.cast_zero]

noncomputable def scaledRealAdaptedMonomialBasis (T : σ → ℝ) (hT : ∀ i, 0 < T i) :
    Basis (AdaptedBasisIndex w ω) ℝ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :=
  inverseScaledBasis ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ)
    (fun z => monomialScale T z.val.1) (fun z => monomialScale_pos T hT z.val.1)

theorem scaledRealAdaptedMonomialBasis_repr (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (z : AdaptedBasisIndex w ω) :
    (F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT).repr x z =
      monomialScale T z.val.1 *
        ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr x z :=
  inverseScaledBasis_repr _ _ _ _ _

theorem scaledRealAdaptedMonomialBasis_structure (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (u v z : AdaptedBasisIndex w ω) :
    (F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT).repr
      ⁅F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT u,
        F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT v⁆ z =
      (lieStructureConstants (F.adaptedMonomialBasis b ω hlayers w) u v z : ℝ) := by
  apply Eq.trans (inverseScaledBasis_bracket _ _ _ ?_ u v z)
  · exact realLieBasis_structure _ u v z
  · intro i j k h
    have he := F.realAdaptedMonomialBasis_bracket_support b ω hlayers w i j k h
    rw [← he, monomialScale_add]

theorem scaledRealAdaptedMonomialBasis_bound_iff (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (z : AdaptedBasisIndex w ω) (M : ℝ) :
    |(F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT).repr x z| ≤ M ↔
      |((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr x z| ≤
        M / monomialScale T z.val.1 := by
  rw [F.scaledRealAdaptedMonomialBasis_repr, abs_mul,
    abs_of_pos (monomialScale_pos T hT z.val.1), le_div_iff₀ (monomialScale_pos T hT z.val.1)]
  rw [mul_comm]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

theorem realFilteredPolynomialMap_polynomial
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    G.realAdaptedPolynomialMap w ((F.filteredPolynomialMap G φ hφ w).toLinearMap.baseChange ℝ x) =
      VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
        (F.realAdaptedPolynomialMap w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r p =>
    apply coefficients.injective
    ext α
    rw [LinearMap.baseChange_tmul, G.realAdaptedPolynomialMap_coefficient_tmul,
      coefficients_map, F.realAdaptedPolynomialMap_coefficient_tmul]
    change r ⊗ₜ[ℚ] coefficients (F.filteredPolynomialMap G φ hφ w p).val α =
      r ⊗ₜ[ℚ] φ (coefficients p.val α)
    rw [F.filteredPolynomialMap_coefficient]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

abbrev RealAdaptedPolynomialGroup := (F.adaptedPolynomialFiltration w).realification.Group

noncomputable def realAdaptedPolynomialGroupHom :
    F.RealAdaptedPolynomialGroup w →* (F.realification.adaptedPolynomialFiltration w).Group :=
  NilpotentLieBCHGroup.map (F.realAdaptedPolynomialTensor w)

@[simp] theorem realAdaptedPolynomialGroupHom_log (g : F.RealAdaptedPolynomialGroup w) :
    ((F.realAdaptedPolynomialGroupHom w g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) =
      F.realAdaptedPolynomialMap w g.coord := rfl

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hlayers in
theorem realAdaptedPolynomialGroupHom_surjective : Function.Surjective (F.realAdaptedPolynomialGroupHom w) := by
  intro g
  obtain ⟨x, hx⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hlayers g.coord
  exact ⟨⟨x⟩, NilpotentLieBCHGroup.ext hx⟩

noncomputable def realAdaptedPolynomialGroupLift (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.RealAdaptedPolynomialGroup w :=
  (F.realAdaptedPolynomialGroupHom_surjective w b ω hlayers g).choose

@[simp] theorem realAdaptedPolynomialGroupHom_lift
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realAdaptedPolynomialGroupHom w (F.realAdaptedPolynomialGroupLift w b ω hlayers g) = g :=
  (F.realAdaptedPolynomialGroupHom_surjective w b ω hlayers g).choose_spec

theorem realAdaptedPolynomialGroupHom_coordinate (g : F.RealAdaptedPolynomialGroup w)
    (z : AdaptedBasisIndex w ω) :
    (b.baseChange ℝ).repr (coefficients
      ((F.realAdaptedPolynomialGroupHom w g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.val.1) z.val.2 =
      ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr g.coord z :=
  F.realAdaptedPolynomialTensor_coordinates w b ω hlayers g.coord z

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScaledPolynomialDualBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def adaptedPolynomialConstantHom :
    (F.adaptedPolynomialFiltration w).Group →* F.Group :=
  NilpotentLieBCHGroup.map ((evalLie (0 : σ → ℚ)).comp (F.adaptedLieSubalgebra w).incl)

@[simp] theorem adaptedPolynomialConstantHom_coord
    (g : (F.adaptedPolynomialFiltration w).Group) :
    (F.adaptedPolynomialConstantHom w g).coord =
      coefficients (g.coord : VectorPolynomial σ ℚ L) 0 :=
  eval_zero_eq_coefficient _

theorem polynomial_factor_middle_constant
    (g e p r : (F.adaptedPolynomialFiltration w).Group) (h : e * p * r = g)
    (he : coefficients (e.coord : VectorPolynomial σ ℚ L) 0 = 0)
    (hr : coefficients (r.coord : VectorPolynomial σ ℚ L) 0 = 0) :
    coefficients (p.coord : VectorPolynomial σ ℚ L) 0 =
      coefficients (g.coord : VectorPolynomial σ ℚ L) 0 := by
  have he' : F.adaptedPolynomialConstantHom w e = 1 := by
    apply NilpotentLieBCHGroup.ext
    rw [F.adaptedPolynomialConstantHom_coord, NilpotentLieBCHGroup.coord_one, he]
  have hr' : F.adaptedPolynomialConstantHom w r = 1 := by
    apply NilpotentLieBCHGroup.ext
    rw [F.adaptedPolynomialConstantHom_coord, NilpotentLieBCHGroup.coord_one, hr]
  have h' := congrArg (F.adaptedPolynomialConstantHom w) h
  rw [map_mul, map_mul, he', hr', one_mul, mul_one] at h'
  have hc := congrArg NilpotentLieBCHGroup.coord h'
  simpa only [F.adaptedPolynomialConstantHom_coord] using hc

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def adaptedConstantLieHom : L →ₗ⁅ℚ⁆ F.adaptedLieSubalgebra w where
  toFun := F.adaptedConstant w
  map_add' a b := by
    apply Subtype.ext
    exact TensorProduct.tmul_add _ _ _
  map_smul' a b := by
    apply Subtype.ext
    exact TensorProduct.tmul_smul a _ _
  map_lie' {a b} := by
    apply Subtype.ext
    change monomial 0 ⁅a, b⁆ = ⁅monomial 0 a, monomial 0 b⁆
    rw [lie_monomial, zero_add]

noncomputable def adaptedConstantGroupHom : F.Group →* (F.adaptedPolynomialFiltration w).Group :=
  NilpotentLieBCHGroup.map (F.adaptedConstantLieHom w)

@[simp] theorem adaptedConstantGroupHom_log (g : F.Group) :
    ((F.adaptedConstantGroupHom w g).coord : VectorPolynomial σ ℚ L) = monomial 0 g.coord := rfl

@[simp] theorem adaptedPolynomialConstantHom_constant (g : F.Group) :
    F.adaptedPolynomialConstantHom w (F.adaptedConstantGroupHom w g) = g := by
  apply NilpotentLieBCHGroup.ext
  rw [F.adaptedPolynomialConstantHom_coord, F.adaptedConstantGroupHom_log,
    coefficients_monomial, Finsupp.single_eq_same]

@[simp] theorem polynomialSymbolHom_constant (g : F.Group) :
    F.polynomialSymbolHom w (F.adaptedConstantGroupHom w g) = 1 := by
  apply NilpotentLieBCHGroup.ext
  exact F.polynomialSymbolMap_constant w g.coord

theorem exists_constant_normalized_polynomial
    (g : (F.adaptedPolynomialFiltration w).Group) (r γ : F.Group)
    (hg : F.adaptedPolynomialConstantHom w g = r * γ) :
    ∃ q : (F.adaptedPolynomialFiltration w).Group,
      F.adaptedConstantGroupHom w r * q * F.adaptedConstantGroupHom w γ = g ∧
      coefficients (q.coord : VectorPolynomial σ ℚ L) 0 = 0 ∧
      F.polynomialSymbolHom w q = F.polynomialSymbolHom w g := by
  let c := F.adaptedConstantGroupHom w
  let q := c r⁻¹ * g * c γ⁻¹
  have hq : F.adaptedPolynomialConstantHom w q = 1 := by
    simp only [q, c, map_mul, F.adaptedPolynomialConstantHom_constant, hg]
    simp
  refine ⟨q, ?_, ?_, ?_⟩
  · simp [q, c, mul_assoc]
  · have hc := congrArg NilpotentLieBCHGroup.coord hq
    simpa only [F.adaptedPolynomialConstantHom_coord, NilpotentLieBCHGroup.coord_one] using hc
  · simp only [q, c, map_mul, F.polynomialSymbolHom_constant, one_mul, mul_one]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

def PolynomialRationalGrid (l : ℕ) (g : (F.realification.adaptedPolynomialFiltration w).Group) : Prop :=
  (fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid l

theorem polynomialRationalGrid_of_dvd {l m : ℕ} (hl : 0 < l) (hlm : l ∣ m)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w l g) : F.PolynomialRationalGrid b w m g :=
  realDenominatorGrid_subset_of_dvd hl hlm hg

theorem polynomialRationalGrid_constant (l : ℕ) (c : F.realification.Group)
    (hc : (fun i => (b.baseChange ℝ).repr c.coord i) ∈ realDenominatorGrid l) :
    F.PolynomialRationalGrid b w l (F.realification.adaptedConstantGroupHom w c) := by
  classical
  obtain ⟨a, ha⟩ := hc
  refine ⟨fun z => if z.1 = 0 then a z.2 else 0, ?_⟩
  funext z
  change ((if z.1 = 0 then a z.2 else 0 : ℤ) : ℝ) =
    (l : ℝ) * (b.baseChange ℝ).repr
      (coefficients ((F.realification.adaptedConstantGroupHom w c).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
  rw [F.realification.adaptedConstantGroupHom_log, coefficients_monomial]
  by_cases h : z.1 = 0
  · simpa only [h, ite_true, Finsupp.single_eq_same, Pi.smul_apply, smul_eq_mul] using congrFun ha z.2
  · simp only [h, ite_false, Int.cast_zero, Finsupp.single_eq_of_ne h, map_zero,
      Finsupp.zero_apply, mul_zero]

theorem polynomialRationalGrid_groupHom_iff (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (l : ℕ) (g : F.RealAdaptedPolynomialGroup w) :
    F.PolynomialRationalGrid b w l (F.realAdaptedPolynomialGroupHom w g) ↔
      (fun z : AdaptedBasisIndex w ω =>
        ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr g.coord z) ∈ realDenominatorGrid l := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun z => a z.val, ?_⟩
    funext z
    have hz := congrFun ha z.val
    change (a z.val : ℝ) = (l : ℝ) * (b.baseChange ℝ).repr
      (coefficients ((F.realAdaptedPolynomialGroupHom w g).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.val.1) z.val.2 at hz
    rw [F.realAdaptedPolynomialGroupHom_coordinate w b ω hlayers g z] at hz
    exact hz
  · rintro ⟨a, ha⟩
    refine ⟨fun z => if h : Finsupp.weight w z.1 ≤ ω z.2 then a ⟨z, h⟩ else 0, ?_⟩
    funext z
    change ((if h : Finsupp.weight w z.1 ≤ ω z.2 then a ⟨z, h⟩ else 0 : ℤ) : ℝ) =
      (l : ℝ) * (b.baseChange ℝ).repr (coefficients
        ((F.realAdaptedPolynomialGroupHom w g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
    by_cases h : Finsupp.weight w z.1 ≤ ω z.2
    · rw [dif_pos h, F.realAdaptedPolynomialGroupHom_coordinate w b ω hlayers g ⟨z, h⟩]
      exact congrFun ha ⟨z, h⟩
    · have hz := (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp
        ((F.realAdaptedPolynomialGroupHom w g).coord.property z.1) z.2 h
      rw [dif_neg h, Int.cast_zero, hz, mul_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

def PolynomialSlowBound (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) : Prop :=
  ∀ α i, |(b.baseChange ℝ).repr
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤ M / monomialScale T α

theorem polynomialSlowBound_inv_iff (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.PolynomialSlowBound b w T M g⁻¹ ↔ F.PolynomialSlowBound b w T M g := by
  change (∀ α i, |(b.baseChange ℝ).repr
    (coefficients (-(g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) α) i| ≤ M / monomialScale T α) ↔ _
  simp only [map_neg, Finsupp.neg_apply, abs_neg, PolynomialSlowBound]

theorem polynomialSlowBound_mono (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M N : ℝ} (hMN : M ≤ N) (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) : F.PolynomialSlowBound b w T N g := by
  intro α i
  exact (hg α i).trans (div_le_div_of_nonneg_right hMN (monomialScale_pos T hT α).le)

theorem polynomialSlowBound_constant (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (c : F.realification.Group)
    (hc : ∀ i, |(b.baseChange ℝ).repr c.coord i| ≤ M) :
    F.PolynomialSlowBound b w T M (F.realification.adaptedConstantGroupHom w c) := by
  classical
  intro α i
  rw [F.realification.adaptedConstantGroupHom_log, coefficients_monomial]
  by_cases hα : α = 0
  · subst α
    simpa only [Finsupp.single_eq_same, monomialScale_zero, div_one] using hc i
  · rw [Finsupp.single_eq_of_ne hα, map_zero, Finsupp.zero_apply, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem polynomialSlowBound_groupHom_iff (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealAdaptedPolynomialGroup w) :
    F.PolynomialSlowBound b w T M (F.realAdaptedPolynomialGroupHom w g) ↔
      ∀ z : AdaptedBasisIndex w ω,
        |((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr g.coord z| ≤
          M / monomialScale T z.val.1 := by
  constructor
  · intro hg z
    rw [← F.realAdaptedPolynomialGroupHom_coordinate w b ω hlayers g z]
    exact hg z.val.1 z.val.2
  · intro hg α i
    by_cases h : Finsupp.weight w α ≤ ω i
    · rw [F.realAdaptedPolynomialGroupHom_coordinate w b ω hlayers g ⟨(α, i), h⟩]
      exact hg ⟨(α, i), h⟩
    · have hz := (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp
        ((F.realAdaptedPolynomialGroupHom w g).coord.property α) i h
      rw [hz, abs_zero]
      exact div_nonneg hM (monomialScale_pos T hT α).le

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem realAdapted_factor_middle_constant
    (g a b c : F.RealAdaptedPolynomialGroup w) (h : a * b * c = g)
    (ha : coefficients (F.realAdaptedPolynomialMap w a.coord) 0 = 0)
    (hc : coefficients (F.realAdaptedPolynomialMap w c.coord) 0 = 0) :
    coefficients (F.realAdaptedPolynomialMap w b.coord) 0 =
      coefficients (F.realAdaptedPolynomialMap w g.coord) 0 := by
  have hp : F.realAdaptedPolynomialGroupHom w a * F.realAdaptedPolynomialGroupHom w b *
      F.realAdaptedPolynomialGroupHom w c = F.realAdaptedPolynomialGroupHom w g := by
    rw [← map_mul, ← map_mul, h]
  exact F.realification.polynomial_factor_middle_constant w
    (F.realAdaptedPolynomialGroupHom w g) (F.realAdaptedPolynomialGroupHom w a)
    (F.realAdaptedPolynomialGroupHom w b) (F.realAdaptedPolynomialGroupHom w c) hp ha hc

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

theorem exists_polynomial_rational_product_bound (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List ((F.realification.adaptedPolynomialFiltration w).Group), rs.length ≤ k →
        (∀ r ∈ rs, F.PolynomialRationalGrid b w l r) → F.PolynomialRationalGrid b w m rs.prod := by
  obtain ⟨K, _, hK⟩ := exists_real_bch_rational_product_bound s k
  let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  let : Fintype (AdaptedBasisIndex w ω) :=
    adaptedBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let B := F.adaptedMonomialBasis b ω hlayers w
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℝ) from le_add_of_nonneg_right (by positivity)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (AdaptedBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (adaptedBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  obtain ⟨m, hm, hmp, hlm, hprod⟩ := hK B H q (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot
    hq hdim (hHp.trans (Real.exp_le_exp.mpr hpq))
    (F.adaptedMonomialBasis_bracket_height b ω hlayers w hH hb) l hl (hlp.trans (Real.exp_le_exp.mpr hpq))
  have hpoly : (q + K) ^ K ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hpoly), hlm, ?_⟩
  intro rs hlen hrs
  let ys := rs.map (F.realAdaptedPolynomialGroupLift w b ω hlayers)
  have hys : ys.map (F.realAdaptedPolynomialGroupHom w) = rs := by
    simp only [ys, List.map_map, Function.comp_def, F.realAdaptedPolynomialGroupHom_lift]
    simp
  have hinput : ∀ r ∈ ys, (B.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid l := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
    apply (F.polynomialRationalGrid_groupHom_iff b w ω hlayers l _).mp
    rw [F.realAdaptedPolynomialGroupHom_lift]
    exact hrs u hu
  have hout := (F.polynomialRationalGrid_groupHom_iff b w ω hlayers m ys.prod).mpr
    (hprod ys (by simpa only [ys, List.length_map] using hlen) hinput)
  rwa [map_list_prod, hys] at hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem linearPolynomial_adapted (a : σ → L) :
    linearPolynomial (R := ℚ) a ∈ F.adaptedLieSubalgebra (fun _ => 1) := by
  intro α
  by_cases h : ∃ i, Finsupp.single i 1 = α
  · obtain ⟨i, rfl⟩ := h
    rw [coefficients_linearPolynomial_single]
    simp only [Finsupp.weight_single, one_smul, F.one_eq_top, Submodule.mem_top]
  · rw [coefficients_linearPolynomial_of_ne a α (by simpa only [not_exists] using h)]
    exact Submodule.zero_mem _

noncomputable def linearPolynomialGroup (a : σ → L) :
    (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
  ⟨⟨linearPolynomial a, F.linearPolynomial_adapted a⟩⟩

@[simp] theorem linearPolynomialGroup_log (a : σ → L) :
    ((F.linearPolynomialGroup a).coord : VectorPolynomial σ ℚ L) = linearPolynomial a := rfl

theorem stepOne_lie_eq_zero (F : NilpotentLieFiltration L 1) (a b : L) : ⁅a, b⁆ = 0 := by
  have ha : a ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hb : b ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have h := F.lie_mem ha hb
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem stepOne_coord_mul (F : NilpotentLieFiltration L 1) (a b : F.Group) :
    (a * b).coord = a.coord + b.coord :=
  lieBCH_eq_add_of_lie_eq_zero F.lowerCentralSeries_eq_bot (F.stepOne_lie_eq_zero a.coord b.coord)

theorem polynomialSlowBound_linear (b : Basis ι ℚ L)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (a : σ → ℝ ⊗[ℚ] L) (ha : ∀ i j, |(b.baseChange ℝ).repr (a i) j| ≤ M / T i) :
    F.PolynomialSlowBound b (fun _ => 1) T M (F.realification.linearPolynomialGroup a) := by
  classical
  intro α j
  rw [F.realification.linearPolynomialGroup_log]
  by_cases h : ∃ i, Finsupp.single i 1 = α
  · obtain ⟨i, rfl⟩ := h
    rw [coefficients_linearPolynomial_single]
    simpa [monomialScale] using ha i j
  · rw [coefficients_linearPolynomial_of_ne a α (by simpa only [not_exists] using h),
      map_zero, Finsupp.zero_apply, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem polynomialRationalGrid_linear (b : Basis ι ℚ L) (m : ℕ) (a : σ → ℝ ⊗[ℚ] L)
    (ha : (fun z : σ × ι => (b.baseChange ℝ).repr (a z.1) z.2) ∈ realDenominatorGrid m) :
    F.PolynomialRationalGrid b (fun _ => 1) m (F.realification.linearPolynomialGroup a) := by
  classical
  obtain ⟨n, hn⟩ := ha
  refine ⟨fun z => if h : ∃ i, Finsupp.single i 1 = z.1 then n (h.choose, z.2) else 0, ?_⟩
  funext z
  change ((if h : ∃ i, Finsupp.single i 1 = z.1 then n (h.choose, z.2) else 0 : ℤ) : ℝ) =
    (m : ℝ) * (b.baseChange ℝ).repr
      (coefficients ((F.realification.linearPolynomialGroup a).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
  rw [F.realification.linearPolynomialGroup_log]
  by_cases h : ∃ i, Finsupp.single i 1 = z.1
  · rw [dif_pos h]
    have hc := coefficients_linearPolynomial_single (R := ℚ) a h.choose
    rw [h.choose_spec] at hc
    rw [hc]
    exact congrFun hn (h.choose, z.2)
  · rw [dif_neg h, Int.cast_zero,
      coefficients_linearPolynomial_of_ne a z.1 (by simpa only [not_exists] using h),
      map_zero, Finsupp.zero_apply, mul_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_polynomial_slow_product_bound (s a k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∀ rs : List ((F.realification.adaptedPolynomialFiltration w).Group), rs.length ≤ k →
      (∀ r ∈ rs, F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a)) r) →
      F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C)) rs.prod := by
  obtain ⟨K, _, hK⟩ := exists_bch_fixed_product_exp_bound s a k
  let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H p hH hp hι hσ hHp hb T hT rs hlen hrs
  let : Fintype (AdaptedBasisIndex w ω) :=
    adaptedBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let B := F.adaptedMonomialBasis b ω hlayers w
  let E := F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℝ) from le_add_of_nonneg_right (by positivity)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (AdaptedBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (adaptedBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hstruct : ∀ i j z, algebraMap ℚ ℝ (lieStructureConstants B i j z) = E.repr ⁅E i, E j⁆ z :=
    fun i j z => (F.scaledRealAdaptedMonomialBasis_structure b ω hlayers w T hT i j z).symm
  have hheight : ∀ i j z, RationalHeightLE (lieStructureConstants B i j z) H :=
    F.adaptedMonomialBasis_bracket_height b ω hlayers w hH hb
  let ys := rs.map (F.realAdaptedPolynomialGroupLift w b ω hlayers)
  have hys : ys.map (F.realAdaptedPolynomialGroupHom w) = rs := by
    simp only [ys, List.map_map, Function.comp_def, F.realAdaptedPolynomialGroupHom_lift]
    simp
  have hinput : ∀ r ∈ ys, ∀ z, |E.repr r.coord z| ≤ Real.exp ((q + 2) ^ a) := by
    intro r hr z
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
    have hslow : F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a))
        (F.realAdaptedPolynomialGroupHom w (F.realAdaptedPolynomialGroupLift w b ω hlayers u)) := by
      rw [F.realAdaptedPolynomialGroupHom_lift]
      exact hrs u hu
    have hz := (F.polynomialSlowBound_groupHom_iff b w ω hlayers T hT (Real.exp_nonneg _) _).mp hslow z
    have hscaled := (F.scaledRealAdaptedMonomialBasis_bound_iff b ω hlayers w T hT _ z _).mpr hz
    exact hscaled.trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by positivity) (add_le_add hpq (le_refl 2)) a))
  have hpoly : (q + K) ^ K ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  have hout : F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C))
      (F.realAdaptedPolynomialGroupHom w ys.prod) := by
    apply (F.polynomialSlowBound_groupHom_iff b w ω hlayers T hT (Real.exp_nonneg _) _).mpr
    intro z
    apply (F.scaledRealAdaptedMonomialBasis_bound_iff b ω hlayers w T hT _ z _).mp
    exact (hK E (lieStructureConstants B) H q
      (F.adaptedPolynomialFiltration w).realification.lowerCentralSeries_eq_bot ys hstruct hq hdim
      (by simpa only [ys, List.length_map] using hlen) (hHp.trans (Real.exp_le_exp.mpr hpq))
      hheight hinput z).trans (Real.exp_le_exp.mpr hpoly)
  rwa [map_list_prod, hys] at hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

noncomputable def affinePolynomialOrbit (b : L) (a : σ → L) :
    F.PolynomialOrbit (fun _ : σ => 1) :=
  polynomialOrbitOfLog (monomial 0 b + linearPolynomial a) (by
    apply (F.mem_adaptedSubmodule _ _).mp
    exact (F.adaptedSubmodule _).add_mem
      ((F.mem_adaptedSubmodule _ _).mpr (F.adapted_constant _ b))
      (F.linearPolynomial_adapted a))

@[simp] theorem affinePolynomialOrbit_log (b : L) (a : σ → L) :
    (F.affinePolynomialOrbit b a).log = monomial 0 b + linearPolynomial a := rfl

variable [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

theorem affinePolynomialOrbit_real_coord (b : L) (a : σ → L) (x : σ → ℝ) :
    (F.polynomialOrbitRealEval (fun _ => 1) x (F.affinePolynomialOrbit b a)).coord =
      b + ∑ j, x j • a j := by
  rw [polynomialOrbitRealEval_coord, affinePolynomialOrbit_log, map_add,
    eval₂_monomial, Finsupp.prod_zero_index, one_smul, eval₂_linearPolynomial]

theorem affinePolynomialOrbit_integer_coord (b : L) (a : σ → L) (x : σ → ℤ) :
    (F.polynomialOrbitEval (fun _ => 1) x (F.affinePolynomialOrbit b a)).coord =
      b + ∑ j, (x j : ℝ) • a j := by
  rw [← F.polynomialOrbitRealEval_integer]
  exact F.affinePolynomialOrbit_real_coord b a _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

def RealAdaptedCoefficientBound (T : σ → ℝ) (M : ℝ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) : Prop :=
  ∀ z : AdaptedBasisIndex w ω,
    |((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr x z| ≤ M / monomialScale T z.val.1

theorem realAdaptedCoefficientBound_mono (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M N : ℝ} (hMN : M ≤ N) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (hx : F.RealAdaptedCoefficientBound b ω hF w T M x) :
    F.RealAdaptedCoefficientBound b ω hF w T N x := by
  intro z
  exact (hx z).trans (div_le_div_of_nonneg_right hMN (monomialScale_pos T hT z.val.1).le)

theorem realAdaptedCoefficientBound_scaled_iff (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.RealAdaptedCoefficientBound b ω hF w T M x ↔
      ∀ z, |(F.scaledRealAdaptedMonomialBasis b ω hF w T hT).repr x z| ≤ M := by
  simp only [RealAdaptedCoefficientBound, F.scaledRealAdaptedMonomialBasis_bound_iff]

theorem realAdaptedCoefficientBound_polynomial_iff (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (g : F.RealAdaptedPolynomialGroup w) :
    F.RealAdaptedCoefficientBound b ω hF w T M g.coord ↔
      F.PolynomialSlowBound b w T M (F.realAdaptedPolynomialGroupHom w g) :=
  (F.polynomialSlowBound_groupHom_iff b w ω hF T hT hM g).symm

theorem exists_scaled_polynomial_dual_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      (∀ z : DualGroup (F.adaptedPolynomialFiltration w).realification.lowerCentralSeries_eq_bot,
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) (dualBaseLinear z.coord) →
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) (dualTangentLinear z.coord) →
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + C) ^ C)) (dualLogDerivative z)) ∧
      (∀ (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w),
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) g.coord →
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) x →
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + C) ^ C)) (dualAdjoint g x)) := by
  have hdualExists := exists_dual_coordinate_operation_bound s a
  obtain ⟨D, _, hdual⟩ := hdualExists
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2)
  let B : Polynomial ℕ := (Q + Polynomial.C D) ^ D
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hc T hT
  let : Fintype (AdaptedBasisIndex w ω) :=
    adaptedBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hF)
  let q := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ (s + 2))).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (AdaptedBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (adaptedBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hF))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hfinal : (q + D) ^ D ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hbound p hp
  have hinput : Real.exp ((p + 2) ^ a) ≤ Real.exp ((q + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (add_le_add hpq (le_refl (2 : ℝ))) a)
  let E := F.scaledRealAdaptedMonomialBasis b ω hF w T hT
  have hoperations := hdual E (lieStructureConstants (F.adaptedMonomialBasis b ω hF w)) H q
    (F.adaptedPolynomialFiltration w).realification.lowerCentralSeries_eq_bot
    (fun i j k => (F.scaledRealAdaptedMonomialBasis_structure b ω hF w T hT i j k).symm)
    hH hq hdim (hHp.trans (Real.exp_le_exp.mpr hpq))
    (F.adaptedMonomialBasis_bracket_height b ω hF w hH hc)
  have hin (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
      (hx : F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) x) :
      ∀ z, |E.repr x z| ≤ Real.exp ((q + 2) ^ a) :=
    fun z => ((F.realAdaptedCoefficientBound_scaled_iff b ω hF w T hT _ x).mp hx z).trans hinput
  have hout (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
      (hx : ∀ z, |E.repr x z| ≤ Real.exp ((q + D) ^ D)) :
      F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + C) ^ C)) x := by
    apply (F.realAdaptedCoefficientBound_scaled_iff b ω hF w T hT _ x).mpr
    exact fun z => (hx z).trans (Real.exp_le_exp.mpr hfinal)
  constructor
  · intro z hb ht
    exact hout _ (hoperations.1 z (hin _ hb) (hin _ ht))
  · intro g x hg hx
    exact hout _ (hoperations.2 g x (hin _ hg) (hin _ hx))

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearWeightedOrbitCoordinates
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module VectorPolynomial
open scoped TensorProduct

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}
variable (s : ℕ) (hw : ∀ i, w i ≤ s)

theorem polynomialShearReal_adapted_iff_coordinate_support
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)) :
    (polynomialShearFiltration w s hw).realification.Adapted (fun _ : σ => 1) p ↔
      ∀ a : PolynomialShearIndex w,
        VectorPolynomial.coordinate
          (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p ∈
          weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a) := by
  rw [NilpotentLieFiltration.adapted_iff_coefficients]
  constructor
  · intro hp a α hα
    change α ∈ (VectorPolynomial.coordinate
      (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p).support at hα
    by_contra hdeg
    have hc := ((polynomialShearFiltration w s hw).real_mem_layer_iff_basis_coordinates
      (polynomialShearBasis (R := ℚ) w) (polynomialShearDeficit w)
      (fun j => polynomialShearLayer_span w j) _ _).mp (hp α) a hdeg
    apply (MvPolynomial.mem_support_iff.mp hα)
    rw [VectorPolynomial.coeff_coordinate]
    exact hc
  · intro hp α
    apply ((polynomialShearFiltration w s hw).real_mem_layer_iff_basis_coordinates
      (polynomialShearBasis (R := ℚ) w) (polynomialShearDeficit w)
      (fun j => polynomialShearLayer_span w j) _ _).mpr
    intro a ha
    change (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a)
      (VectorPolynomial.coefficients p α) = 0
    have hc : (VectorPolynomial.coordinate
        (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p).coeff α = 0 := by
      by_contra hne
      exact ha (hp a (MvPolynomial.mem_support_iff.mpr hne))
    exact (VectorPolynomial.coeff_coordinate _ p α).symm.trans hc

noncomputable def polynomialShearOrbitParameterCoordinates
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : σ => 1))
    (a : PolynomialShearIndex w) : MvPolynomial σ ℝ :=
  VectorPolynomial.coordinate
    (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom g.log

theorem polynomialShearOrbitParameterCoordinates_degree
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : σ => 1))
    (a : PolynomialShearIndex w) :
    polynomialShearOrbitParameterCoordinates s hw g a ∈
      weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a) :=
  (polynomialShearReal_adapted_iff_coordinate_support s hw g.log).mp g.adapted a

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module
open scoped BigOperators TensorProduct

variable {σ : Type*} {d : ℕ}

variable (w : Fin d → ℕ) [Fintype (PolynomialShearIndex w)]

variable (s : ℕ) (hw : ∀ i, w i ≤ s)
variable (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : σ => 1))
variable (t : σ → ℝ)

local notation "orbitD" => polynomialShearRealificationEquiv w
  (NilpotentLieBCHGroup.coord
    (NilpotentLieFiltration.polynomialOrbitRealEval
      (NilpotentLieFiltration.realification (polynomialShearFiltration w s hw))
      (fun _ : σ => 1) t g))
local notation "symbolicD" => polynomialSymbolicShearDerivation w
  (polynomialShearOrbitParameterCoordinates s hw g)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module VectorPolynomial
open scoped TensorProduct

section Coordinates

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}
variable (s : ℕ) (hw : ∀ i, w i ≤ s) (weight : σ → ℕ)

theorem weightedPolynomialShearReal_adapted_iff_coordinate_support
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)) :
    (polynomialShearFiltration w s hw).realification.Adapted weight p ↔
      ∀ a : PolynomialShearIndex w,
        VectorPolynomial.coordinate
          (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p ∈
          weightedSupportLE weight (polynomialShearDeficit w a) := by
  rw [NilpotentLieFiltration.adapted_iff_coefficients]
  constructor
  · intro hp a α hα
    change α ∈ (VectorPolynomial.coordinate
      (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p).support at hα
    by_contra hdeg
    have hc := ((polynomialShearFiltration w s hw).real_mem_layer_iff_basis_coordinates
      (polynomialShearBasis (R := ℚ) w) (polynomialShearDeficit w)
      (fun j => polynomialShearLayer_span w j) _ _).mp (hp α) a hdeg
    apply (MvPolynomial.mem_support_iff.mp hα)
    rw [VectorPolynomial.coeff_coordinate]
    exact hc
  · intro hp α
    apply ((polynomialShearFiltration w s hw).real_mem_layer_iff_basis_coordinates
      (polynomialShearBasis (R := ℚ) w) (polynomialShearDeficit w)
      (fun j => polynomialShearLayer_span w j) _ _).mpr
    intro a ha
    change (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a)
      (VectorPolynomial.coefficients p α) = 0
    have hc : (VectorPolynomial.coordinate
        (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p).coeff α = 0 := by
      by_contra hne
      exact ha (hp a (MvPolynomial.mem_support_iff.mpr hne))
    exact (VectorPolynomial.coeff_coordinate _ p α).symm.trans hc

noncomputable def weightedPolynomialShearOrbitParameterCoordinates
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit weight)
    (a : PolynomialShearIndex w) : MvPolynomial σ ℝ :=
  VectorPolynomial.coordinate
    (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom g.log

theorem weightedPolynomialShearOrbitParameterCoordinates_degree
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit weight)
    (a : PolynomialShearIndex w) :
    weightedPolynomialShearOrbitParameterCoordinates s hw weight g a ∈
      weightedSupportLE weight (polynomialShearDeficit w a) :=
  (weightedPolynomialShearReal_adapted_iff_coordinate_support s hw weight g.log).mp g.adapted a

end Coordinates

variable {σ : Type*} {d : ℕ}

variable (w : Fin d → ℕ) [Fintype (PolynomialShearIndex w)]
variable (s : ℕ) (hw : ∀ i, w i ≤ s) (weight : σ → ℕ)
variable (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit weight)
variable (t : σ → ℝ)

local notation "orbitD" => polynomialShearRealificationEquiv w
  (NilpotentLieBCHGroup.coord
    (NilpotentLieFiltration.polynomialOrbitRealEval
      (NilpotentLieFiltration.realification (polynomialShearFiltration w s hw))
      weight t g))
local notation "symbolicD" => polynomialSymbolicShearDerivation w
  (weightedPolynomialShearOrbitParameterCoordinates s hw weight g)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AssociatedGradedBasisIndependence
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def gradedPieceProjection (j : ℕ) : L →ₗ[ℚ] F.AssociatedGraded :=
  (F.associatedGradedBasis b ω hlayers).repr.symm.toLinearMap.comp
    (b.repr.toLinearMap.comp (basisGradeProjection b ω j))

theorem gradedPieceProjection_coordinate (j : ℕ) (v : L) (i : ι) :
    (F.associatedGradedBasis b ω hlayers).repr (F.gradedPieceProjection b ω hlayers j v) i =
      if ω i = j then b.repr v i else 0 := by
  simp only [gradedPieceProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, basisGradeProjection_repr]

theorem gradedPieceProjection_eq_pieceMap (j : ℕ) (v : F.layer j) :
    F.gradedPieceProjection b ω hlayers j v = F.associatedGradedPieceMap j v := by
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  rw [F.gradedPieceProjection_coordinate, F.associatedGradedPieceMap_coordinate]
  simp only [eq_comm]

theorem gradedRefiltrationLayer_eq_inf_comap (U : LieSubalgebra ℚ F.AssociatedGraded) (j : ℕ) :
    F.gradedRefiltrationLayer U j =
      F.layer j ⊓ U.toSubmodule.comap (F.gradedPieceProjection b ω hlayers j) := by
  ext v
  rw [F.mem_gradedRefiltrationLayer, Submodule.mem_inf, Submodule.mem_comap]
  constructor
  · rintro ⟨hv, hU⟩
    exact ⟨hv, (F.gradedPieceProjection_eq_pieceMap b ω hlayers j ⟨v, hv⟩).symm ▸ hU⟩
  · rintro ⟨hv, hU⟩
    exact ⟨hv, F.gradedPieceProjection_eq_pieceMap b ω hlayers j ⟨v, hv⟩ ▸ hU⟩

theorem real_gradedPieceProjection_coordinate (j : ℕ) (v : ℝ ⊗[ℚ] L) (i : ι) :
    ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr
      ((F.gradedPieceProjection b ω hlayers j).baseChange ℝ v) i =
      if ω i = j then (b.baseChange ℝ).repr v i else 0 := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      F.gradedPieceProjection_coordinate, Basis.baseChange_repr_tmul]
    split_ifs <;> simp only [zero_smul]
  | add v z hv hz =>
    simp only [map_add, Finsupp.add_apply, hv, hz]
    split_ifs <;> simp only [add_zero]

theorem realGradedSymbolPolynomial_coefficient_of_polynomial
    (w : σ → ℕ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ) :
    coefficients (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realSymbolOfPolynomial b ω hlayers w p)) α =
        (F.gradedPieceProjection b ω hlayers (Finsupp.weight w α)).baseChange ℝ (coefficients p α) := by
  apply ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr.injective
  ext i
  rw [F.real_gradedPieceProjection_coordinate]
  by_cases h : Finsupp.weight w α = ω i
  · rw [if_pos h.symm]
    exact (F.realGradedSymbolPolynomial_coordinate b ω hlayers w _ ⟨(α, i), h⟩).trans
      (F.realSymbolOfPolynomial_coordinate b ω hlayers w p ⟨(α, i), h⟩)
  · rw [if_neg (Ne.symm h)]
    exact F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w _ α i h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hb : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem associatedGradedPieceMap_repr_symm (j : ℕ) (x : F.layer j) :
    b.repr.symm ((F.associatedGradedBasis b ω hb).repr (F.associatedGradedPieceMap j x)) =
      basisGradeProjection b ω j x.val := by
  apply b.repr.injective
  ext i
  rw [b.repr.apply_symm_apply, F.associatedGradedPieceMap_coordinate,
    basisGradeProjection_repr]
  simp only [eq_comm]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hb : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedGradedPolynomial
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def shiftedGradedPolynomial (k : ℕ) :
    VectorPolynomial σ ℚ L →ₗ[ℚ] VectorPolynomial σ ℚ F.AssociatedGraded where
  toFun p := coefficients.symm (Finsupp.onFinset (coefficients p).support
    (fun α => F.gradedPieceProjection b ω hlayers (Finsupp.weight w α + k) (coefficients p α)) (by
      intro α hα
      apply Finsupp.mem_support_iff.mpr
      intro hc
      apply hα
      rw [hc, map_zero]))
  map_add' p q := by
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    simp only [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply, map_add, Finsupp.add_apply]
  map_smul' c p := by
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    simp only [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply, map_smul, Finsupp.smul_apply,
      RingHom.id_apply]

@[simp] theorem shiftedGradedPolynomial_coefficient (k : ℕ) (p : VectorPolynomial σ ℚ L)
    (α : σ →₀ ℕ) :
    coefficients (F.shiftedGradedPolynomial b ω hlayers w k p) α =
      F.gradedPieceProjection b ω hlayers (Finsupp.weight w α + k) (coefficients p α) := by
  simp only [shiftedGradedPolynomial, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply]

theorem shiftedGradedPolynomial_monomial (k : ℕ) (α : σ →₀ ℕ) (v : L) :
    F.shiftedGradedPolynomial b ω hlayers w k (monomial α v) =
      monomial α (F.gradedPieceProjection b ω hlayers (Finsupp.weight w α + k) v) := by
  classical
  apply coefficients.injective
  apply Finsupp.ext
  intro β
  rw [F.shiftedGradedPolynomial_coefficient, coefficients_monomial, coefficients_monomial]
  by_cases h : α = β
  · subst β
    rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), Finsupp.single_eq_of_ne (Ne.symm h), map_zero]

theorem shiftedGradedPolynomial_coefficient_of_mem (k : ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule w k) (α : σ →₀ ℕ) :
    coefficients (F.shiftedGradedPolynomial b ω hlayers w k p) α =
      F.associatedGradedPieceMap (Finsupp.weight w α + k) ⟨coefficients p α, hp α⟩ := by
  rw [F.shiftedGradedPolynomial_coefficient]
  exact F.gradedPieceProjection_eq_pieceMap b ω hlayers (Finsupp.weight w α + k)
    ⟨coefficients p α, hp α⟩

theorem shiftedGradedPolynomial_eq_zero_iff (k : ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule w k) :
    F.shiftedGradedPolynomial b ω hlayers w k p = 0 ↔
      p ∈ F.shiftedAdaptedSubmodule w (k + 1) := by
  constructor
  · intro hz α
    have hc := congrArg (fun q : VectorPolynomial σ ℚ F.AssociatedGraded => coefficients q α) hz
    rw [F.shiftedGradedPolynomial_coefficient_of_mem b ω hlayers w k hp,
      map_zero, Finsupp.zero_apply] at hc
    have hh := (F.associatedGradedPieceMap_eq_zero_iff _ _).mp hc
    simpa only [Nat.add_assoc] using hh
  · intro hp'
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [F.shiftedGradedPolynomial_coefficient_of_mem b ω hlayers w k hp, map_zero, Finsupp.zero_apply]
    apply (F.associatedGradedPieceMap_eq_zero_iff _ _).mpr
    simpa only [Nat.add_assoc] using hp' α

theorem shiftedGradedPolynomial_zero (p : F.adaptedLieSubalgebra w) :
    F.shiftedGradedPolynomial b ω hlayers w 0 p.val =
      F.gradedSymbolPolynomial b ω hlayers w (F.polynomialSymbolMap w p) := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  apply Finsupp.ext
  intro i
  rw [F.shiftedGradedPolynomial_coefficient, Nat.add_zero, F.gradedPieceProjection_coordinate]
  by_cases hd : Finsupp.weight w α = ω i
  · rw [if_pos hd.symm]
    exact ((F.gradedSymbolPolynomial_coefficient b ω hlayers w (F.polynomialSymbolMap w p)
      ⟨(α, i), hd⟩).trans (F.polynomialSymbolBasis_repr_map b ω hlayers w p ⟨(α, i), hd⟩)).symm
  · rw [if_neg (Ne.symm hd)]
    exact (F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ α i hd).symm

end Erdos3.NilpotentLieFiltration

end

end OAI

end


