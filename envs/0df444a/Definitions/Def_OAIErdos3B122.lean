-- Prove2me | Definitions.Def_OAIErdos3B122
-- name    : OAIErdos3B122
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T05:59:38.129525+00:00
-- url     : https://prove2.me/theorems/895e2a08-8f01-4d92-8ee7-9309602a5aed
-- title:
--   OpenAI Erdős-3 split, definitions bundle 123 of 132
-- statement:
--   Definitions bundle 123 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B121`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 123 available.
--
--   Modules: `OAI.Erdos3.MultidegreeLieFiltration.exists_real_normalized_addition_orbit`, `OAI.Erdos3.MultidegreeLieFiltration.realAdditiveTriple_frequency_phase`, `OAI.Erdos3.MultidegreeLieFiltration.realAdditiveTriple_omitted_frequency_phase`, `OAI.Erdos3.MultidegreeLieFiltration.realDilationPair_frequency_phase`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedAdditiveTripleOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedAdditiveTripleOrbit_eval`, `OAI.Erdos3.MultidegreeLieFiltration.realifiedAdditiveTripleOrbit_zero`, `OAI.Erdos3.NativeDegreeRankFamily.quadruple_common_anchor`, `OAI.Erdos3.NativeDegreeRankFamily.shiftPair`, `OAI.Erdos3.NativeDegreeRankFamily.shiftPair_mul_star`, `OAI.Erdos3.NativeDegreeRankFamily.shiftPair_norm`, `OAI.Erdos3.NativeSampleModelFamily.ofModels`, `OAI.Erdos3.NativeSampleModelFamily.recOn`, `OAI.Erdos3.NilpotentLieFiltration.exists_common_refiltered_marked_symbol_factors`, `OAI.Erdos3.NilpotentLieFiltration.exists_common_refiltered_terminal_discrepancies`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_prescribed_fast_symbol_factorization`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_prescribed_marked_native_factorizations`, `OAI.Erdos3.NilpotentLieFiltration.exists_realFilteredSymbolGroupMap_grid`, `OAI.Erdos3.NilpotentLieFiltration.filteredSymbolMapDenominator`, `OAI.Erdos3.NilpotentLieFiltration.filteredSymbolMapDenominator_le`, `OAI.Erdos3.NilpotentLieFiltration.filteredSymbolMapDenominator_le_exp`, `OAI.Erdos3.NilpotentLieFiltration.filteredSymbolMapDenominator_pos`, `OAI.Erdos3.NilpotentLieFiltration.fullMarkedNativeInput`, `OAI.Erdos3.NilpotentLieFiltration.realDilationPair_frequency_phase`, `OAI.Erdos3.NilpotentLieFiltration.realFilteredSymbolGroupMap_grid`, `OAI.Erdos3.NilpotentLieFiltration.realFilteredSymbolGroupMap_slow`, `OAI.Erdos3.NilpotentLieFiltration.realFilteredSymbolGroupMap_slow_exp`, `OAI.Erdos3.NilpotentLieFiltration.realFilteredSymbolGroupMap_symbol`, `OAI.Erdos3.PolynomialTranslationLie.exists_translation_major_twisted_vertical_selection`, `OAI.Erdos3.RankPreparationFamily.PreparedHeights`, `OAI.Erdos3.RankPreparationFamily.PreparedHeights.coefficientTorus_compact`, `OAI.Erdos3.RankPreparationFamily.PreparedHeights.exists_uniform_charts`, `OAI.Erdos3.RankPreparationFamily.PreparedHeights.lattice_full`, `OAI.Erdos3.RankPreparationFamily.PreparedHeights.pad`, `OAI.Erdos3.RankPreparationFamily.Sized.pad`, `OAI.Erdos3.RankPreparationFamily.initial`, `OAI.Erdos3.RankPreparationFamily.pad`, `OAI.Erdos3.RankPreparationFamily.pad_apply_castLE`, `OAI.Erdos3.RankPreparationFamily.pad_apply_ge`, `OAI.Erdos3.RankPreparationFamily.pad_apply_lt`, `OAI.Erdos3.RankPreparationFamily.pad_coefficients_mem`, `OAI.Erdos3.RankPreparationFamily.pad_sum`, `OAI.Erdos3.RankPreparationFamily.pad_value`, `OAI.Erdos3.RankPreparationLayer.basisAxisScale_le_exp`, `OAI.Erdos3.RankPreparationLayer.euclideanEquiv`, `OAI.Erdos3.RankPreparationLayer.euclidean_finrank`, `OAI.Erdos3.RankPreparationLayer.exists_short_integral_basis`, `OAI.Erdos3.RankPreparationLayer.integralCoordinateBasis`, `OAI.Erdos3.RankPreparationLayer.integralCoordinateBasis_card`, `OAI.Erdos3.RankPreparationLayer.integralCoordinateBasis_integer`, `OAI.Erdos3.RankPreparationLayer.integralCoordinateMatrix`, `OAI.Erdos3.RankPreparationLayer.lattice_full`, `OAI.Erdos3.RankPreparationLayer.rank_add_orthogonal_finrank`, `OAI.Erdos3.RankPreparationLayer.shortIntegralBasisNormBound`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.dilationObservable_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_dilation_niltest_of_data`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_lipschitz_unitVertical_triple_descent`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_native_addition_orbit`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_unitVertical_dilation_quotient_niltest`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_unitVertical_triple_quotient_niltest`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.tripleObservable`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.tripleObservable_component_top`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.tripleObservable_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.tripleObservable_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.tripleObservable_norm_le`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.tripleObservable_of_addition_values`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.tripleObservable_top_invariant`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.tripleSpaceProjection_top_smul`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.unitVertical_dilation_top_invariant`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.unitVertical_top_action`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.unitVertical_triple_top_invariant`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.combinationNiltest`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.combinationNiltest_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.coordinateCombination`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.coordinateCombination_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.coordinateCombination_norm`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.coordinateCombination_vertical`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.differenceObservable`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.differenceObservable_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.differenceObservable_norm`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.differenceObservable_rank_invariant`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.differenceObservable_unit`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.rankDifference`, `OAI.Erdos3.RationalFilteredNilmanifold.selectedOrbitFactors`, `OAI.Erdos3.RationalFilteredNilmanifold.selectedOrbitFactors_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.selectedOrbitFactors_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.selectedOrbitFactors_normBound`, `OAI.Erdos3.RationalFilteredNilmanifold.selectedOrbitFrequencies`, `OAI.Erdos3.VectorPolynomial.allocatedMaskedTiltedConstant`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientSample_floor_coefficient_remainder`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientSample_floor_polynomial_remainder`, `OAI.Erdos3.VectorPolynomial.coefficientIntegerFloorPolynomial`, `OAI.Erdos3.VectorPolynomial.coefficientIntegerFloorPolynomial_degree`, `OAI.Erdos3.VectorPolynomial.exists_allocated_uniform_charts`, `OAI.Erdos3.allocatedUniformChartLog`, `OAI.Erdos3.basisAxisScale_jointRationalSpace_le_exp`, `OAI.Erdos3.dominatedDensityRatio`, `OAI.Erdos3.exists_localPivot_weighted_native_vertical_partners`, `OAI.Erdos3.exists_uniform_projected_chart`, `OAI.Erdos3.exists_weighted_native_vertical_partners`, `OAI.Erdos3.exp_scaled_norm_le_one`, `OAI.Erdos3.finite_double_normalization`, `OAI.Erdos3.finite_remove_normalization`, `OAI.Erdos3.latticeGaussianMean`, `OAI.Erdos3.layerIntegerRestriction`, `OAI.Erdos3.lipschitz_signed_tensor_cross_product`, `OAI.Erdos3.lipschitz_three_conjugates_of_bounds`, `OAI.Erdos3.preparationExponent_mono`, `OAI.Erdos3.preparationExponent_pos`, `OAI.Erdos3.preparationHeight`, `OAI.Erdos3.preparationHeight_le_exp`, `OAI.Erdos3.preparationHeight_mono`, `OAI.Erdos3.preparationHeight_pos`, `OAI.Erdos3.real_top_frequency_mul`, `OAI.Erdos3.recoveredIntegerDeck`, `OAI.Erdos3.recoveredIntegerTransverse`, `OAI.Erdos3.recoveredLayeredIntegerLift`, `OAI.Erdos3.recoveredMixedCoordinates`, `_private.Estimates.NativeLocalPivotVerticalPartners.0.OAI.Erdos3.norm_expect_scaled_product`, `_private.Estimates.NativeLocalPivotVerticalPartners.0.OAI.Erdos3.weighted_fixed_choices`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B115

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSampleModelFamily
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  {D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)} {w : σ → ℕ}

noncomputable def selectedOrbitFactors (base T : ∀ i, (D i).Niltest w)
    (active : Finset ι) (i : ι) : (D i).Niltest w := by
  classical
  exact if i ∈ active then T i else (base i).oneOnOrbit

noncomputable def selectedOrbitFrequencies (eta : ∀ i, L i →ₗ[ℚ] ℚ)
    (active : Finset ι) (i : ι) : L i →ₗ[ℚ] ℚ := by
  classical
  exact if i ∈ active then eta i else 0

theorem selectedOrbitFactors_eval [Fintype ι] (base T : ∀ i, (D i).Niltest w)
    (active : Finset ι) (x : σ → ℤ) :
    (∏ i, (selectedOrbitFactors base T active i).eval x) = ∏ i ∈ active, (T i).eval x := by
  classical
  have heval (i : ι) : (selectedOrbitFactors base T active i).eval x =
      if i ∈ active then (T i).eval x else 1 := by
    by_cases hi : i ∈ active <;>
      simp only [selectedOrbitFactors, hi, ite_true, ite_false, Niltest.oneOnOrbit_eval]
  simp only [heval, Finset.prod_ite_mem_eq]

theorem selectedOrbitFactors_normBound (base T : ∀ i, (D i).Niltest w) (active : Finset ι)
    (hcap : ∀ i ∈ active, (T i).normBound ≤ 1) (i : ι) :
    (selectedOrbitFactors base T active i).normBound ≤ 1 := by
  classical
  by_cases hi : i ∈ active
  · simpa only [selectedOrbitFactors, hi, ite_true] using hcap i hi
  · simp only [selectedOrbitFactors, hi, ite_false, Niltest.oneOnOrbit, le_refl]

theorem selectedOrbitFactors_complexity (base T : ∀ i, (D i).Niltest w)
    (active : Finset ι) {p : ℝ} (hp : 2 ≤ p) (hD : ∀ i, (D i).GeometryComplexityLE p)
    (hT : ∀ i ∈ active, (T i).ComplexityLE p) (i : ι) :
    (selectedOrbitFactors base T active i).ComplexityLE p := by
  classical
  by_cases hi : i ∈ active
  · simpa only [selectedOrbitFactors, hi, ite_true] using hT i hi
  · simpa only [selectedOrbitFactors, hi, ite_false] using
      (base i).oneOnOrbit_complexity hp (hD i)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeSampleModelFamily {ι σ X : Type*} (w : σ → ℕ) (degree : ℕ) (p : ℝ)
    (sample : X → σ → ℤ) (g : ι → X → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : ι → model.Niltest w
  norm : ∀ i, (test i).normBound ≤ 1
  complexity : ∀ i, (test i).ComplexityLE p
  eval : ∀ i x, g i x = (test i).eval (sample x)

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra NativeSampleModel.topology NativeSampleModel.topologicalAdd NativeSampleModel.continuousSMul NativeSampleModel.hausdorff NativeSampleModelFamily.lie NativeSampleModelFamily.algebra NativeSampleModelFamily.topology NativeSampleModelFamily.topologicalAdd NativeSampleModelFamily.continuousSMul NativeSampleModelFamily.hausdorff

namespace NativeSampleModelFamily

variable {ι σ X : Type*} {w : σ → ℕ} {degree : ℕ} {p : ℝ}
  {sample : X → σ → ℤ} {g : ι → X → ℂ}

noncomputable def ofModels {ι : Type} [Fintype ι] {g : ι → X → ℂ}
    (V : ∀ i, NativeSampleModel w degree p sample (g i))
    (hp : 2 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) :
    NativeSampleModelFamily w degree (productNiltestBudget p) sample g := by
  classical
  let D := fun i => (V i).model
  let base := fun i => (V i).test
  let : FiniteDimensional ℚ (∀ i, (V i).L) :=
    (RationalFilteredNilmanifold.productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, (V i).L))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, (V i).L)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, (V i).L)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis D)
  let factors := fun j => RationalFilteredNilmanifold.selectedOrbitFactors base base {j}
  have hD : ∀ i, (D i).GeometryComplexityLE p := fun i => (V i).complexity.1
  have hcomp : ∀ j i, (factors j i).ComplexityLE p := fun j =>
    RationalFilteredNilmanifold.selectedOrbitFactors_complexity base base {j} hp hD
      (fun i _ => (V i).complexity)
  have hcap : ∀ j i, (factors j i).normBound ≤ 1 := fun j =>
    RationalFilteredNilmanifold.selectedOrbitFactors_normBound base base {j}
      (fun i _ => (V i).norm)
  have hp0 : 0 ≤ p := by linarith
  let tests := fun j => RationalFilteredNilmanifold.unitBoundedPiNiltest
    D (factors j) hp0 hι (hcomp j) (hcap j)
  refine {
    L := ∀ i, (V i).L
    dim := Fintype.card (Σ i, Fin (V i).dim)
    model := RationalFilteredNilmanifold.pi D
    test := tests
    norm := fun _ => le_rfl
    complexity := fun j => RationalFilteredNilmanifold.unitBoundedPiNiltest_complexity
      D (factors j) hp0 hι (hcomp j) (hcap j)
    eval := ?_ }
  intro j x
  change g j x = (RationalFilteredNilmanifold.unitBoundedPiNiltest
    D (factors j) hp0 hι (hcomp j) (hcap j)).eval (sample x)
  rw [RationalFilteredNilmanifold.unitBoundedPiNiltest_eval]
  change g j x = ∏ i, (RationalFilteredNilmanifold.selectedOrbitFactors base base {j} i).eval
    (sample x)
  rw [RationalFilteredNilmanifold.selectedOrbitFactors_eval]
  simpa only [Finset.prod_singleton] using (V j).eval x

end NativeSampleModelFamily

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledPrescribedMarkedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped Matrix TensorProduct NNReal

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (w : σ → ℕ)
  [Fintype (SymbolBasisIndex w ω)] [Fintype (SymbolBasisIndex w ν)]

noncomputable def filteredSymbolMapDenominator : ℕ :=
  matrixDenominator (fun i j => (G.polynomialSymbolBasis c ν hG w).repr
    (F.filteredPolynomialSymbolMap G φ hφ w (F.polynomialSymbolBasis b ω hF w j)) i)

theorem realFilteredSymbolGroupMap_slow
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A : ℝ} (hA : 0 ≤ A)
    (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolSlowBound b ω hF w T A g) :
    G.SymbolSlowBound c ν hG w T
      (((Fintype.card (SymbolBasisIndex w ω) : ℝ) + 1) * (H + 1) * A)
      (F.realFilteredSymbolGroupMap G φ hφ w g) := by
  classical
  let B := F.polynomialSymbolBasis b ω hF w
  let C := G.polynomialSymbolBasis c ν hG w
  let ψ := (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap
  let D := LinearMap.toMatrix B C ψ
  have hblock : ∀ i j, i.val.1 ≠ j.val.1 → D i j = 0 := by
    intro i j hij
    simpa only [D, B, C, ψ, LinearMap.toMatrix_apply, LieHom.coe_toLinearMap] using
      F.filteredPolynomialSymbolMap_monomial_blocks G b ω hF c ν hG φ hφ w j i hij
  have hheight : ∀ i j, RationalHeightLE (D i j) H := by
    intro i j
    simpa only [D, B, C, ψ, LinearMap.toMatrix_apply, LieHom.coe_toLinearMap] using
      F.filteredPolynomialSymbolMap_basis_height G b ω hF c ν hG φ hφ w hH hentries j i
  intro i
  have h := rational_coordinate_map_weighted (B.baseChange ℝ) (C.baseChange ℝ)
    (ψ.baseChange ℝ) D (realified_linear_coordinate_matrix B C ψ)
    (fun j => j.val.1) (fun j => j.val.1) hblock (H : ℝ≥0)
    (fun i j => by exact_mod_cast (hheight i j).1)
    (monomialScale T) (monomialScale_pos T hT) hA g.coord hg i
  exact h

theorem realFilteredSymbolGroupMap_slow_exp
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A : ℝ} (hA : 0 ≤ A)
    (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolSlowBound b ω hF w T A g) :
    G.SymbolSlowBound c ν hG w T (Real.exp ((p + 2) ^ 3) * A)
      (F.realFilteredSymbolGroupMap G φ hφ w g) := by
  have hbound := F.realFilteredSymbolGroupMap_slow G b ω hF c ν hG φ hφ w
    hH hentries T hT hA g hg
  have hfac : ((Fintype.card (SymbolBasisIndex w ω) : ℝ) + 1) * (H + 1) ≤
      Real.exp ((p + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power _ hp hdim 1 (by omega))
    gcongr
    exact hHp.trans (Real.exp_le_exp.mpr (by simp))
  intro i
  exact (hbound i).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfac hA) (monomialScale_pos T hT _).le)

theorem realFilteredSymbolGroupMap_grid (l : ℕ) (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolRationalGrid b ω hF w l g) :
    G.SymbolRationalGrid c ν hG w
      (F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w * l)
      (F.realFilteredSymbolGroupMap G φ hφ w g) := by
  classical
  have h := realified_linear_coordinate_grid
    (F.polynomialSymbolBasis b ω hF w) (G.polynomialSymbolBasis c ν hG w)
    (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap l g.coord hg
  have hm : LinearMap.toMatrix (F.polynomialSymbolBasis b ω hF w)
      (G.polynomialSymbolBasis c ν hG w)
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap =
      fun i j => (G.polynomialSymbolBasis c ν hG w).repr
        (F.filteredPolynomialSymbolMap G φ hφ w (F.polynomialSymbolBasis b ω hF w j)) i := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    rfl
  rw [hm] at h
  exact h

theorem filteredSymbolMapDenominator_pos :
    0 < F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w :=
  matrixDenominator_pos _

theorem filteredSymbolMapDenominator_le {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H) :
    F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w ≤
      H ^ (Fintype.card (SymbolBasisIndex w ν) * Fintype.card (SymbolBasisIndex w ω)) := by
  apply matrixDenominator_le
  intro i j
  exact F.filteredPolynomialSymbolMap_basis_height G b ω hF c ν hG φ hφ w hH hentries j i

theorem filteredSymbolMapDenominator_le_exp {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hsource : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ p)
    (htarget : (Fintype.card (SymbolBasisIndex w ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    (F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w : ℝ) ≤
      Real.exp ((p + 2) ^ 3) := by
  apply matrixDenominator_le_exp_power _ hp 1 htarget hsource
  intro i j
  have h := (F.filteredPolynomialSymbolMap_basis_height G b ω hF c ν hG φ hφ w
    hH hentries j i).2
  exact (Nat.cast_le.mpr h).trans (hHp.trans (Real.exp_le_exp.mpr (by simp)))

theorem exists_realFilteredSymbolGroupMap_grid
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hsource : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ p)
    (htarget : (Fintype.card (SymbolBasisIndex w ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ g : F.RealPolynomialSymbolGroup w,
        F.SymbolRationalGrid b ω hF w l g →
        G.SymbolRationalGrid c ν hG w m (F.realFilteredSymbolGroupMap G φ hφ w g) := by
  let d := F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w
  have hd := F.filteredSymbolMapDenominator_le_exp G b ω hF c ν hG φ hφ w
    hH hentries hp hsource htarget hHp
  refine ⟨d * l, Nat.mul_pos
    (F.filteredSymbolMapDenominator_pos G b ω hF c ν hG φ hφ w) hl, ?_,
    dvd_mul_left _ _, ?_⟩
  · rw [Nat.cast_mul]
    calc
      (d : ℝ) * l ≤ Real.exp ((p + 2) ^ 3) * Real.exp p :=
        mul_le_mul hd hlp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((p + 2) ^ 3 + p) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((p + 2) ^ 4) := by
        apply Real.exp_le_exp.mpr
        have hp3 : p ≤ (p + 2) ^ 3 := le_power_budget hp (by omega)
        calc
          (p + 2) ^ 3 + p ≤ 2 * (p + 2) ^ 3 := by linarith
          _ ≤ (p + 2) * (p + 2) ^ 3 := by gcongr; linarith
          _ = (p + 2) ^ 4 := by ring
  · exact F.realFilteredSymbolGroupMap_grid G b ω hF c ν hG φ hφ w l

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

theorem exists_controlled_prescribed_fast_symbol_factorization (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ ξ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype ξ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ [Fintype (SymbolBasisIndex w ω)] [Fintype (SymbolBasisIndex w ν)]
        (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : ξ → F.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      BasisBlockInvariant (F.polynomialSymbolBasis b ω hF w) (fun z => z.val.1) U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card (SymbolBasisIndex w ω ⊕ SymbolBasisIndex w ν) : ℝ) ≤ p →
      ((Fintype.card (SymbolBasisIndex w ω) * Fintype.card ξ : ℕ) : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H) →
      (∀ j i, RationalHeightLE ((F.polynomialSymbolBasis b ω hF w).repr (v j) i) H) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
        ∀ (E P R : F.RealPolynomialSymbolGroup w) (EF RF : G.RealPolynomialSymbolGroup w),
        P.coord ∈ realificationLieSubalgebra U →
        F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
        G.SymbolSlowBound c ν hG w T (Real.exp ((p + 2) ^ a)) EF →
        F.SymbolRationalGrid b ω hF w l R → G.SymbolRationalGrid c ν hG w l RF →
        ((F.realFilteredSymbolGroupMap G φ hφ w E)⁻¹ * EF).coord ∈
          realificationLieSubalgebra (U.map (F.filteredPolynomialSymbolMap G φ hφ w)) →
        (RF * (F.realFilteredSymbolGroupMap G φ hφ w R)⁻¹).coord ∈
          realificationLieSubalgebra (U.map (F.filteredPolynomialSymbolMap G φ hφ w)) →
        ∃ E' P' R' : F.RealPolynomialSymbolGroup w,
          E' * P' * R' = E * P * R ∧
          P'.coord ∈ realificationLieSubalgebra U ∧
          F.realFilteredSymbolGroupMap G φ hφ w E' = EF ∧
          F.realFilteredSymbolGroupMap G φ hφ w R' = RF ∧
          F.SymbolSlowBound b ω hF w T (Real.exp ((p + C) ^ C)) E' ∧
          F.SymbolRationalGrid b ω hF w m R' := by
  obtain ⟨ceF, hceF, hslowF⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨ceG, hceG, hslowG⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨crF, hcrF, hrationalF⟩ := exists_symbol_rational_product_bound s 2
  obtain ⟨crG, hcrG, hrationalG⟩ := exists_symbol_rational_product_bound s 2
  let ce := max ceF ceG
  let cr := max crF crG
  obtain ⟨C, hC, hbudget⟩ := exists_fastSymbolCorrectionBudget a ce cr
  refine ⟨C, hC, ?_⟩
  intro σ ι κ ξ L M _ _ _ _ _ _ _ _ F G b ω hF c ν hG φ hφ w hw _ _
    U v hspan hU H l p hH hl hp hι hκ hσ hrows hcols hHp hlp hb hc hentries hv
  classical
  let p₀ : ℝ := p + (p + 2) ^ a + (p + 2) ^ 4 + 2
  let p₁ : ℝ := p₀ + (p₀ + ce) ^ ce + (p₀ + cr) ^ cr
  let p₂ : ℝ := p₁ + ((p₁ + 2) ^ 10 + 2) ^ 36 + ((p₁ + 2) ^ 10 + 2) ^ 18 + 2
  have hbase : 0 ≤ p + 2 := add_nonneg hp (by norm_num)
  have ha0 : 0 ≤ (p + 2) ^ a := pow_nonneg hbase _
  have h40 : 0 ≤ (p + 2) ^ 4 := pow_nonneg hbase _
  have hp₀ : 0 ≤ p₀ := add_nonneg (add_nonneg (add_nonneg hp ha0) h40) (by norm_num)
  have hce0 : 0 ≤ (p₀ + ce) ^ ce := pow_nonneg (add_nonneg hp₀ (Nat.cast_nonneg _)) _
  have hcr0 : 0 ≤ (p₀ + cr) ^ cr := pow_nonneg (add_nonneg hp₀ (Nat.cast_nonneg _)) _
  have hp₁ : 0 ≤ p₁ := add_nonneg (add_nonneg hp₀ hce0) hcr0
  have hsection : 0 ≤ (p₁ + 2) ^ 10 + 2 :=
    add_nonneg (pow_nonneg (add_nonneg hp₁ (by norm_num)) _) (by norm_num)
  have h36 : 0 ≤ ((p₁ + 2) ^ 10 + 2) ^ 36 := pow_nonneg hsection _
  have h18 : 0 ≤ ((p₁ + 2) ^ 10 + 2) ^ 18 := pow_nonneg hsection _
  have hp₂ : 0 ≤ p₂ := add_nonneg (add_nonneg (add_nonneg hp₁ h36) h18) (by norm_num)
  have hpp₀ : p ≤ p₀ :=
    ((le_add_of_nonneg_right ha0).trans (le_add_of_nonneg_right h40)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  have h₀₁ : p₀ ≤ p₁ := (le_add_of_nonneg_right hce0).trans (le_add_of_nonneg_right hcr0)
  have h₁₂ : p₁ ≤ p₂ :=
    ((le_add_of_nonneg_right h36).trans (le_add_of_nonneg_right h18)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  have hpp₁ := hpp₀.trans h₀₁
  have hpp₂ := hpp₁.trans h₁₂
  have hdimF : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ p := by
    simp only [Fintype.card_sum, Nat.cast_add] at hrows
    linarith only [hrows, Nat.cast_nonneg (α := ℝ) (Fintype.card (SymbolBasisIndex w ν))]
  have hdimG : (Fintype.card (SymbolBasisIndex w ν) : ℝ) ≤ p := by
    simp only [Fintype.card_sum, Nat.cast_add] at hrows
    linarith only [hrows, Nat.cast_nonneg (α := ℝ) (Fintype.card (SymbolBasisIndex w ω))]
  let d := F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w
  have hd : 0 < d := F.filteredSymbolMapDenominator_pos G b ω hF c ν hG φ hφ w
  have hdle := F.filteredSymbolMapDenominator_le G b ω hF c ν hG φ hφ w hH hentries
  have hdl : ((d * l : ℕ) : ℝ) ≤ Real.exp p₀ := by
    apply (kernel_inclusion_denominator_mul_le_exp _ _ H d l hp hdimG hdimF hHp hdle hlp).trans
    apply Real.exp_le_exp.mpr
    exact (le_add_of_nonneg_left (add_nonneg hp ha0)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  obtain ⟨l₁, hl₁, hl₁p, hdl₁, hprodG⟩ := hrationalG G c ν hG w hw H p₀ hH hp₀
    (hκ.trans hpp₀) (hσ.trans hpp₀) (hHp.trans (Real.exp_le_exp.mpr hpp₀)) hc
    (d * l) (Nat.mul_pos hd hl) hdl
  have hll₁ : l ∣ l₁ := (dvd_mul_left l d).trans hdl₁
  have hl₁p₁ : (l₁ : ℝ) ≤ Real.exp p₁ := by
    apply (hl₁p.trans (Real.exp_le_exp.mpr
      (shifted_power_self_mono hp₀ (by omega : 1 ≤ crG) (le_max_right crF crG)))).trans
      (Real.exp_le_exp.mpr ?_)
    exact le_add_of_nonneg_left (add_nonneg hp₀ hce0)
  obtain ⟨S, l₂, hl₂, hl₂p, hl₁₂, hsolve, hslowLift, hgridLift⟩ :=
    NilpotentLieBCHGroup.exists_controlled_fast_lift
      (F.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (G.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (F.polynomialSymbolBasis b ω hF w) (G.polynomialSymbolBasis c ν hG w)
      (fun z => z.val.1) (fun z => z.val.1) U v hspan hU
      (F.filteredPolynomialSymbolMap G φ hφ w)
      (fun i j hij => F.filteredPolynomialSymbolMap_monomial_blocks G b ω hF c ν hG φ hφ w j i hij)
      hH hl₁ hv
      (fun i j => F.filteredPolynomialSymbolMap_basis_height G b ω hF c ν hG φ hφ w hH hentries j i)
      hp₁ (hrows.trans hpp₁) (hcols.trans hpp₁) (hHp.trans (Real.exp_le_exp.mpr hpp₁)) hl₁p₁
  simp only [Basis.equivFun_apply] at hslowLift hgridLift
  have hl₂p₂ : (l₂ : ℝ) ≤ Real.exp p₂ := by
    apply hl₂p.trans (Real.exp_le_exp.mpr ?_)
    exact ((le_add_of_nonneg_left hp₁).trans (le_add_of_nonneg_right h18)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  obtain ⟨m, hm, hmp, hl₂m, hprodF⟩ := hrationalF F b ω hF w hw H p₂ hH hp₂
    (hι.trans hpp₂) (hσ.trans hpp₂) (hHp.trans (Real.exp_le_exp.mpr hpp₂)) hb l₂ hl₂ hl₂p₂
  have hbound : (p₂ + ce) ^ ce + (p₂ + cr) ^ cr ≤ (p + C) ^ C := hbudget p hp
  have hfinalE : (p₂ + ce) ^ ce ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hp₂ (Nat.cast_nonneg cr)) cr)).trans hbound
  have hfinalR : (p₂ + cr) ^ cr ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (add_nonneg hp₂ (Nat.cast_nonneg ce)) ce)).trans hbound
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr
    ((shifted_power_self_mono hp₂ (by omega : 1 ≤ crF) (le_max_left crF crG)).trans hfinalR)), (hll₁.trans hl₁₂).trans hl₂m, ?_⟩
  intro T hT E P R EF RF hP hE hEF hR hRF hleft hright
  let π := F.realFilteredSymbolGroupMap G φ hφ w
  let lift := NilpotentLieBCHGroup.realLinearCoordinateLift
    (hL := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := G.polynomialSymbol_lowerCentralSeries_eq_bot w) S
  let A := lift ((π E)⁻¹ * EF)
  let D := lift (RF * (π R)⁻¹)
  obtain ⟨hA, hAimage⟩ := hsolve ((π E)⁻¹ * EF) hleft
  obtain ⟨hD, hDimage⟩ := hsolve (RF * (π R)⁻¹) hright
  have himageA : π A = (π E)⁻¹ * EF := hAimage
  have himageD : π D = RF * (π R)⁻¹ := hDimage
  have hAfast : A.coord ∈ realificationLieSubalgebra U := hA
  have hDfast : D.coord ∈ realificationLieSubalgebra U := hD
  have hslowπ := F.realFilteredSymbolGroupMap_slow_exp G b ω hF c ν hG φ hφ w
    hH hentries hp hdimF hHp T hT (Real.exp_nonneg _) E hE
  have h34 : (p + 2) ^ 3 ≤ (p + 2) ^ 4 := pow_le_pow_right₀ (by linarith only [hp]) (by omega)
  have hslowπ' : G.SymbolSlowBound c ν hG w T (Real.exp ((p₀ + 2) ^ (1 : ℕ))) (π E) := by
    apply G.symbolSlowBound_mono c ν hG w T hT _ _ hslowπ
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    calc
      _ ≤ (p + 2) ^ 4 + (p + 2) ^ a := add_le_add h34 le_rfl
      _ = (p + 2) ^ a + (p + 2) ^ 4 := add_comm _ _
      _ ≤ p + (p + 2) ^ a + (p + 2) ^ 4 :=
        add_le_add (le_add_of_nonneg_left hp) le_rfl
      _ ≤ p₀ := le_add_of_nonneg_right (by norm_num)
      _ ≤ p₀ + 2 := le_add_of_nonneg_right (by norm_num)
  have hslowEF : G.SymbolSlowBound c ν hG w T (Real.exp ((p₀ + 2) ^ (1 : ℕ))) EF := by
    apply G.symbolSlowBound_mono c ν hG w T hT _ _ hEF
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    exact (((le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right h40)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  have hslowDis : G.SymbolSlowBound c ν hG w T (Real.exp ((p₀ + ce) ^ ce)) ((π E)⁻¹ * EF) := by
    have hh := hslowG G c ν hG w hw H p₀ hH hp₀ (hκ.trans hpp₀) (hσ.trans hpp₀)
      (hHp.trans (Real.exp_le_exp.mpr hpp₀)) hc T hT [(π E)⁻¹, EF] (by simp) (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact (G.symbolSlowBound_inv_iff c ν hG w T _ _).mpr hslowπ'
        · exact hslowEF)
    have hh' : G.SymbolSlowBound c ν hG w T (Real.exp ((p₀ + ceG) ^ ceG)) ((π E)⁻¹ * EF) := by
      simpa only [List.prod_cons, List.prod_nil, mul_one] using hh
    exact G.symbolSlowBound_mono c ν hG w T hT (Real.exp_le_exp.mpr
      (shifted_power_self_mono hp₀ (by omega : 1 ≤ ceG) (le_max_right ceF ceG))) _ hh'
  have hslowDis₁ : G.SymbolSlowBound c ν hG w T (Real.exp p₁) ((π E)⁻¹ * EF) := by
    apply G.symbolSlowBound_mono c ν hG w T hT _ _ hslowDis
    apply Real.exp_le_exp.mpr
    exact (le_add_of_nonneg_left hp₀).trans (le_add_of_nonneg_right hcr0)
  have hslowA : F.SymbolSlowBound b ω hF w T
      (Real.exp (((p₁ + 2) ^ 10 + 2) ^ 18) * Real.exp p₁) A := by
    exact hslowLift (monomialScale T) (monomialScale_pos T hT)
      (Real.exp p₁) (Real.exp_nonneg _) ((π E)⁻¹ * EF) hslowDis₁
  have hslowA₂ : F.SymbolSlowBound b ω hF w T (Real.exp ((p₂ + 2) ^ (1 : ℕ))) A := by
    apply F.symbolSlowBound_mono b ω hF w T hT _ _ hslowA
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    calc
      _ = p₁ + ((p₁ + 2) ^ 10 + 2) ^ 18 := add_comm _ _
      _ ≤ p₁ + ((p₁ + 2) ^ 10 + 2) ^ 36 + ((p₁ + 2) ^ 10 + 2) ^ 18 :=
        add_le_add (le_add_of_nonneg_right h36) le_rfl
      _ ≤ p₂ := le_add_of_nonneg_right (by norm_num)
      _ ≤ p₂ + 2 := le_add_of_nonneg_right (by norm_num)
  have hslowE₂ : F.SymbolSlowBound b ω hF w T (Real.exp ((p₂ + 2) ^ (1 : ℕ))) E := by
    apply F.symbolSlowBound_mono b ω hF w T hT _ _ hE
    apply Real.exp_le_exp.mpr
    have hh : (p + 2) ^ a ≤ p₀ :=
      ((le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right h40)).trans
        (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
    simp only [pow_one]
    exact (hh.trans (h₀₁.trans h₁₂)).trans (le_add_of_nonneg_right (by norm_num))
  have hgridπ : G.SymbolRationalGrid c ν hG w (d * l) (π R) :=
    F.realFilteredSymbolGroupMap_grid G b ω hF c ν hG φ hφ w l R hR
  have hgridRF : G.SymbolRationalGrid c ν hG w (d * l) RF :=
    realDenominatorGrid_subset_of_dvd hl (dvd_mul_left l d) hRF
  have hgridDis : G.SymbolRationalGrid c ν hG w l₁ (RF * (π R)⁻¹) := by
    have hh := hprodG [RF, (π R)⁻¹] (by simp) (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hgridRF
      · exact G.symbolRationalGrid_inv c ν hG w (d * l) hgridπ)
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hh
  have hgridD : F.SymbolRationalGrid b ω hF w l₂ D := hgridLift _ hgridDis
  have hgridR₂ : F.SymbolRationalGrid b ω hF w l₂ R :=
    realDenominatorGrid_subset_of_dvd hl (hll₁.trans hl₁₂) hR
  refine ⟨E * A, A⁻¹ * P * D⁻¹, D * R, by
    simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left], ?_, ?_, ?_, ?_, ?_⟩
  · exact (NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).mul_mem
      ((NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).mul_mem
        ((NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).inv_mem hAfast) hP)
      ((NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).inv_mem hDfast)
  · change π (E * A) = EF
    rw [map_mul, himageA, mul_inv_cancel_left]
  · change π (D * R) = RF
    rw [map_mul, himageD, inv_mul_cancel_right]
  · have hh := hslowF F b ω hF w hw H p₂ hH hp₂ (hι.trans hpp₂) (hσ.trans hpp₂)
      (hHp.trans (Real.exp_le_exp.mpr hpp₂)) hb T hT [E, A] (by simp) (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact hslowE₂
        · exact hslowA₂)
    have hh' : F.SymbolSlowBound b ω hF w T (Real.exp ((p₂ + ceF) ^ ceF)) (E * A) := by
      simpa only [List.prod_cons, List.prod_nil, mul_one] using hh
    exact F.symbolSlowBound_mono b ω hF w T hT (Real.exp_le_exp.mpr
      ((shifted_power_self_mono hp₂ (by omega : 1 ≤ ceF) (le_max_left ceF ceG)).trans hfinalE)) _ hh'
  · have hh := hprodF [D, R] (by simp) (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hgridD
      · exact hgridR₂)
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hh

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem realFilteredSymbolGroupMap_symbol [Fintype σ] [Fintype ι] [Fintype κ] (w : σ → ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realFilteredSymbolGroupMap G φ hφ w (F.realPolynomialSymbolHom b ω hF w g) =
      G.realPolynomialSymbolHom c ν hG w (F.realPolynomialGroupMap G φ hφ w g) := by
  apply NilpotentLieBCHGroup.ext
  exact F.realFilteredPolynomialSymbolMap_polynomial G φ hφ b ω hF c ν hG w g.coord

variable [Fintype σ] [Fintype ι] [Fintype κ]

theorem exists_common_refiltered_marked_symbol_factors
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ p)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ (side : σ → ℝ), (∀ i, 0 < side i) →
      ∀ (q : ℝ) (W : LieSubalgebra ℚ F.AssociatedGraded)
        (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
      F.HasCommonRefilteredOrbitFactors b ω hF side q l W g →
      ∃ El Pl Rl : G.RealPolynomialSymbolGroup (fun _ : σ => 1),
        El * Pl * Rl = G.realPolynomialSymbolHom c ν hG (fun _ => 1)
          (F.realPolynomialGroupMap G φ hφ (fun _ => 1) g) ∧
        Pl.coord ∈ realificationLieSubalgebra
          (G.symbolPointwiseSubalgebra c ν hG (fun _ => 1)
            (W.map (F.associatedGradedMap G φ hφ))) ∧
        G.SymbolSlowBound c ν hG (fun _ => 1) side
          (Real.exp ((p + 2) ^ 3 + q)) El ∧
        G.SymbolRationalGrid c ν hG (fun _ => 1) m Rl := by
  obtain ⟨m, hm, hmp, hlm, hgrid⟩ :=
    F.exists_realFilteredSymbolGroupMap_grid G b ω hF c ν hG φ hφ (fun _ : σ => 1)
      hH hentries hp hsource htarget hHp l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro side hside q W g hfactor
  obtain ⟨E, P, R, hprod, hP, hE, hR⟩ :=
    hfactor.symbolFactors F b ω hF side q l W g
  let π := F.realFilteredSymbolGroupMap G φ hφ (fun _ : σ => 1)
  refine ⟨π E, π P, π R, ?_, ?_, ?_, hgrid R hR⟩
  · rw [← map_mul, ← map_mul, hprod]
    exact F.realFilteredSymbolGroupMap_symbol G b ω hF c ν hG φ hφ (fun _ => 1) g
  · exact F.real_symbolPointwiseSubalgebra_map_mem G b ω hF c ν hG φ hφ
      (fun _ => 1) W P.coord hP
  · have hslow := F.realFilteredSymbolGroupMap_slow_exp G b ω hF c ν hG φ hφ
      (fun _ : σ => 1) hH hentries hp hsource hHp side hside (Real.exp_nonneg q) E hE
    simpa only [Real.exp_add] using hslow

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

def fullMarkedNativeInput (s a C : ℕ) (p : ℝ) : ℝ :=
  (pointwiseFastSectionInput s p + C) ^ C + (p + 2) ^ a + pointwiseFastSectionInput s p

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_common_refiltered_terminal_discrepancies (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ χ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype χ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
      [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
      (HMap l : ℕ) (pMap : ℝ), 1 ≤ HMap → 0 < l → 0 ≤ pMap →
      (∀ i j, RationalHeightLE (c.repr (φ (b j)) i) HMap) →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ pMap →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ pMap →
      (HMap : ℝ) ≤ Real.exp pMap → (l : ℝ) ≤ Real.exp pMap →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((pMap + 2) ^ 4) ∧ l ∣ m ∧
        ∀ (HCompare : ℕ) (pCompare : ℝ), 1 ≤ HCompare → 0 ≤ pCompare →
        (Fintype.card κ : ℝ) ≤ pCompare → (Fintype.card σ : ℝ) ≤ pCompare →
        (Fintype.card χ : ℝ) ≤ pCompare → (HCompare : ℝ) ≤ Real.exp pCompare →
        Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pCompare →
        (∀ i j z, RationalHeightLE (c.repr ⁅c i, c j⁆ z) HCompare) →
        ∀ side : σ → ℝ, (∀ i, Real.exp ((pCompare + C) ^ C) ≤ side i) →
        ∀ q : ℝ, Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pCompare + 2) ^ a) →
        ∀ (W : LieSubalgebra ℚ F.AssociatedGraded)
          (vg : χ → G.PolynomialSymbol (fun _ : σ => 1)),
        Submodule.span ℚ (Set.range vg) =
          (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
            (W.map (F.associatedGradedMap G φ hφ))).toSubmodule →
        (∀ i z, RationalHeightLE
          ((G.polynomialSymbolBasis c ν hG (fun _ : σ => 1)).repr (vg i) z) HCompare) →
        ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
        F.HasCommonRefilteredOrbitFactors b ω hF side q l W g →
        ∃ E P R : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
          E * P * R = F.realPolynomialSymbolHom b ω hF (fun _ => 1) g ∧
          P.coord ∈ realificationLieSubalgebra
            (F.symbolPointwiseSubalgebra b ω hF (fun _ : σ => 1) W) ∧
          F.SymbolSlowBound b ω hF (fun _ : σ => 1) side (Real.exp q) E ∧
          F.SymbolRationalGrid b ω hF (fun _ : σ => 1) l R ∧
          ∀ E₀ R₀ : G.RealPolynomialSymbolGroup (fun _ : σ => 1),
            (E₀⁻¹ * G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1)
              (F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g) * R₀⁻¹).coord ∈
                realificationLieSubalgebra
                  (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
                    (W.map (F.associatedGradedMap G φ hφ))) →
            G.SymbolSlowBound c ν hG (fun _ : σ => 1) side
              (Real.exp ((pCompare + 2) ^ a)) E₀ →
            G.SymbolRationalGrid c ν hG (fun _ : σ => 1) m R₀ →
            ((F.realFilteredSymbolGroupMap G φ hφ (fun _ : σ => 1) E)⁻¹ * E₀).coord ∈
              realificationLieSubalgebra
                (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
                  (W.map (F.associatedGradedMap G φ hφ))) ∧
            (R₀ * (F.realFilteredSymbolGroupMap G φ hφ (fun _ : σ => 1) R)⁻¹).coord ∈
              realificationLieSubalgebra
                (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
                  (W.map (F.associatedGradedMap G φ hφ))) := by
  obtain ⟨C, hC, hcompare⟩ := exists_controlled_terminal_symbol_comparison s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ χ L M _ _ _ _ _ _ _ _ F G b ω hF c ν hG φ hφ _ _
    HMap l pMap hHMap hl hpMap hentries hsource htarget hHMapExp hlExp
  obtain ⟨m, hm, hmExp, hlm, hmapGrid⟩ :=
    F.exists_realFilteredSymbolGroupMap_grid G b ω hF c ν hG φ hφ (fun _ : σ => 1)
      hHMap hentries hpMap hsource htarget hHMapExp l hl hlExp
  refine ⟨m, hm, hmExp, hlm, ?_⟩
  intro HCompare pCompare hHCompare hpCompare hκ hσ hχ hHCompareExp hgridAbsorb
    hbracket side hside q hslowAbsorb W vg hspan hvg g hnative
  have hsidePos : ∀ i, 0 < side i := fun i => (Real.exp_pos _).trans_le (hside i)
  obtain ⟨E, P, R, hprod, hP, hE, hR⟩ :=
    hnative.symbolFactors F b ω hF side q l W g
  refine ⟨E, P, R, hprod, hP, hE, hR, ?_⟩
  intro E₀ R₀ hterminal hE₀ hR₀
  let π := F.realFilteredSymbolGroupMap G φ hφ (fun _ : σ => 1)
  let U := G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
    (W.map (F.associatedGradedMap G φ hφ))
  let P₀ := E₀⁻¹ * G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1)
    (F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g) * R₀⁻¹
  have hmapP : (π P).coord ∈ realificationLieSubalgebra U :=
    F.real_symbolPointwiseSubalgebra_map_mem G b ω hF c ν hG φ hφ
      (fun _ : σ => 1) W P.coord hP
  have hmapSlow : G.SymbolSlowBound c ν hG (fun _ : σ => 1) side
      (Real.exp ((pCompare + 2) ^ a)) (π E) := by
    have hslow := F.realFilteredSymbolGroupMap_slow_exp G b ω hF c ν hG φ hφ
      (fun _ : σ => 1) hHMap hentries hpMap hsource hHMapExp side hsidePos
      (Real.exp_nonneg q) E hE
    have hslow' : G.SymbolSlowBound c ν hG (fun _ : σ => 1) side
        (Real.exp ((pMap + 2) ^ 3 + q)) (π E) := by
      simpa only [Real.exp_add] using hslow
    exact G.symbolSlowBound_mono c ν hG (fun _ : σ => 1) side hsidePos hslowAbsorb _ hslow'
  have hmapGridR : G.SymbolRationalGrid c ν hG (fun _ : σ => 1) m (π R) :=
    hmapGrid R hR
  have hcompareProd : π E * π P * π R = E₀ * P₀ * R₀ := by
    calc
      π E * π P * π R = π (F.realPolynomialSymbolHom b ω hF (fun _ : σ => 1) g) := by
        rw [← map_mul, ← map_mul, hprod]
      _ = G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1)
          (F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g) :=
        F.realFilteredSymbolGroupMap_symbol G b ω hF c ν hG φ hφ (fun _ : σ => 1) g
      _ = E₀ * P₀ * R₀ := by
        dsimp only [P₀]
        group
  exact hcompare G c ν hG (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    U vg hspan HCompare m pCompare hHCompare hm hpCompare hκ hσ hχ hHCompareExp
    (hmExp.trans hgridAbsorb) hbracket hvg side hside
    (π E) (π P) (π R) E₀ P₀ R₀ hmapP hterminal hcompareProd hmapSlow hE₀ hmapGridR hR₀

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_controlled_prescribed_marked_native_factorizations (s a : ℕ) :
    ∃ Cf Cnative : ℕ, 2 ≤ Cf ∧ 2 ≤ Cnative ∧
    ∀ {σ ι κ ξ μ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [Fintype ξ] [Fintype μ] [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (τ : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (U : LieSubalgebra ℚ F.AssociatedGraded) (v : μ → F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U.toSubmodule →
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
    ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card ξ : ℝ) ≤ p → (Fintype.card μ : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
      (∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H) →
    ∃ m : ℕ, 0 < m ∧
      (m : ℝ) ≤ Real.exp ((markedNativeLiftInput (fullMarkedNativeInput s a Cf p) + Cnative) ^ Cnative) ∧
      l ∣ m ∧
    ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
    ∀ X EF RF : (G.realification.adaptedPolynomialFiltration w).Group,
      G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ a)) EF →
      G.PolynomialRationalGrid c w l RF →
      coefficients ((EF⁻¹ * X * RF⁻¹).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
        G.realGradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1 →
    ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group),
      F.realPolynomialGroupMap G φ hφ w g = X →
    ∀ E P R : F.RealPolynomialSymbolGroup w,
      E * P * R = F.realPolynomialSymbolHom b ω hF w g →
      P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) →
      F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
      F.SymbolRationalGrid b ω hF w l R →
      ((F.realFilteredSymbolGroupMap G φ hφ w E)⁻¹ *
        G.realPolynomialSymbolHom c τ hG w EF).coord ∈ realificationLieSubalgebra
          (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ))) →
      (G.realPolynomialSymbolHom c τ hG w RF *
        (F.realFilteredSymbolGroupMap G φ hφ w R)⁻¹).coord ∈ realificationLieSubalgebra
          (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ))) →
    ∃ (e middle r : (F.realification.adaptedPolynomialFiltration w).Group)
      (q : (F.gradedRefiltration U).realification.PolynomialOrbit w),
      e * middle * r = g ∧
      F.realPolynomialGroupMap G φ hφ w e = EF ∧
      F.realPolynomialGroupMap G φ hφ w r = RF ∧
      F.realPolynomialGroupMap G φ hφ w middle = EF⁻¹ * X * RF⁻¹ ∧
      F.PolynomialSlowBound b w T (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput s a Cf p) + Cnative) ^ Cnative)) e ∧
      F.PolynomialRationalGrid b w m r ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra U).incl)).toLinearMap
        q.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration U).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra U).incl
        ((F.gradedRefiltration U).realification.polynomialOrbitRealEval w t q) =
          F.adaptedPolynomialRealValueHom w t middle := by
  obtain ⟨Cf, hCf, hfast⟩ := exists_controlled_prescribed_fast_symbol_factorization s a
  obtain ⟨Cnative, hCnative, hnative⟩ := exists_controlled_marked_native_factorization s 1
  refine ⟨Cf, Cnative, hCf, hCnative, ?_⟩
  intro σ ι κ ξ μ L M _ _ _ _ _ _ _ _ _ F G φ hφ b ω hF c τ hG w hw hsurj
    bk U v hU hvspan H l p hH hl hp hι hκ hξ hμ hσ hHp hlp hb hc hkernel hentries hv
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hF)
  let : Fintype (SymbolBasisIndex w τ) :=
    symbolBasisIndexFintype w τ s hw (G.adaptedBasis_weight_le_step c τ hG)
  let Q := pointwiseFastSectionInput s p
  have hpQ : p ≤ Q := pointwiseFastSectionInput_ge s hp
  have hQ : 0 ≤ Q := hp.trans hpQ
  have hcounts := F.pointwiseSymbolSpanning_section_counts (ξ := μ) G b ω hF c τ hG w hw
    hp hι hκ hμ hσ
  obtain ⟨n, hn, hnp, hln, hcorrect⟩ := hfast F G b ω hF c τ hG φ hφ w hw
    (F.symbolPointwiseSubalgebra b ω hF w U) (F.pointwiseSymbolSpanningFamily b ω hF w v)
    (F.pointwiseSymbolSpanningFamily_span b ω hF w U hU v hvspan)
    (F.symbolPointwiseSubalgebra_blockInvariant b ω hF w U)
    H l Q hH hl hQ (hι.trans hpQ) (hκ.trans hpQ) (hσ.trans hpQ)
    hcounts.2.1 hcounts.2.2 (hHp.trans (Real.exp_le_exp.mpr hpQ))
    (hlp.trans (Real.exp_le_exp.mpr hpQ)) hb hc hentries
    (F.pointwiseSymbolSpanningFamily_height b ω hF w v hH hv)
  let B := fullMarkedNativeInput s a Cf p
  have hslow0 : 0 ≤ (p + 2) ^ a := by positivity
  have hfast0 : 0 ≤ (Q + Cf) ^ Cf := by positivity
  have hQB : Q ≤ B := by
    change Q ≤ (Q + Cf) ^ Cf + (p + 2) ^ a + Q
    linarith only [hfast0, hslow0]
  have hpB : p ≤ B := hpQ.trans hQB
  have hB : 0 ≤ B := hp.trans hpB
  have hfastB : (Q + Cf) ^ Cf ≤ B := by
    change _ ≤ (Q + Cf) ^ Cf + (p + 2) ^ a + Q
    linarith only [hslow0, hQ]
  have hslowB : (p + 2) ^ a ≤ B := by
    change _ ≤ (Q + Cf) ^ Cf + (p + 2) ^ a + Q
    linarith only [hfast0, hQ]
  obtain ⟨m, hm, hmp, hnm, hfactor⟩ := hnative F G φ hφ b ω hF c τ hG w hw hsurj
    bk H n B hH hn hB (hι.trans hpB) (hκ.trans hpB) (hξ.trans hpB) (hσ.trans hpB)
    (hHp.trans (Real.exp_le_exp.mpr hpB)) (hnp.trans (Real.exp_le_exp.mpr hfastB))
    hb hkernel hentries
  refine ⟨m, hm, hmp, hln.trans hnm, ?_⟩
  intro T hT X EF RF hEF hRF hconstant
  have hEFbound : CoefficientBound (c.baseChange ℝ) T
      (Real.exp ((B + 2) ^ 1)) EF.coord.val :=
    G.polynomialSlowBound_mono c w T hT
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using hslowB.trans (by linarith only))) EF hEF
  have hRFgrid : CoefficientGrid (c.baseChange ℝ) n RF.coord.val := by
    obtain ⟨z, hz⟩ := G.polynomialRationalGrid_of_dvd c w hl hln RF hRF
    intro α
    exact ⟨fun i => z (α, i), funext (fun i => congrFun hz (α, i))⟩
  intro g hg E P R hprod hP hEslow hRgrid hleft hright
  have hscale : Real.exp ((p + 2) ^ a) ≤ Real.exp ((Q + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith only [hp]) (by linarith only [hpQ]) a)
  have himage := F.symbolPointwiseSubalgebra_map G b ω hF c τ hG φ hφ w U hU
  rw [← himage] at hleft hright
  obtain ⟨E', P', R', hprod', hP', hEmark, hRmark, hEbound, hRden⟩ :=
    hcorrect T hT E P R (G.realPolynomialSymbolHom c τ hG w EF)
      (G.realPolynomialSymbolHom c τ hG w RF) hP
      (F.symbolSlowBound_mono b ω hF w T hT hscale E hEslow)
      (G.symbolSlowBound_mono c τ hG w T hT hscale _
        (G.polynomialSlowBound_symbol c τ hG w T _ EF hEF))
      hRgrid (G.polynomialRationalGrid_symbol c τ hG w l RF hRF) hleft hright
  have hEbound' : F.SymbolSlowBound b ω hF w T (Real.exp ((B + 2) ^ 1)) E' :=
    F.symbolSlowBound_mono b ω hF w T hT
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using hfastB.trans (by linarith only))) E' hEbound
  have hfirst : coefficients ((EF⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF⁻¹).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
      G.realGradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1 := by
    rw [hg]
    exact hconstant
  obtain ⟨e, middle, r, q, hprod'', _, _, _, heF, hrF, hpF, heslow, hrden, hq, hvalues⟩ :=
    hfactor U hU T hT g E' P' R' (hprod'.trans hprod) hP' EF RF
      (congrArg NilpotentLieBCHGroup.coord hEmark)
      (congrArg NilpotentLieBCHGroup.coord hRmark) hEbound' hEFbound hRden hRFgrid hfirst
  exact ⟨e, middle, r, q, hprod'', heF, hrF, hpF.trans (by rw [hg]), heslow, hrden, hq, hvalues⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.DilationFrequencyPhase
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem NilpotentLieFiltration.realDilationPair_frequency_phase
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (q : ℤ) (η : L →ₗ[ℚ] ℚ)
    (g : (F.dilationPairFiltration (q : ℚ)).realification.Group)
    (hg : g ∈ (F.dilationPairFiltration (q : ℚ)).realification.subgroup s) :
    (realifyFunctional η (F.realDilationPairProjection (q : ℚ) 0 g).coord : CircleFourier.Circle) =
      (q ^ s) • (realifyFunctional η
        (F.realDilationPairProjection (q : ℚ) 1 g).coord : CircleFourier.Circle) := by
  rw [F.realDilationPair_top_group_relation q g hg, NilpotentLieBCHGroup.coord_zpow,
    map_zsmul, AddCircle.coe_zsmul]

theorem MultidegreeLieFiltration.realDilationPair_frequency_phase
    {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
    (q : ℤ) (η : L →ₗ[ℚ] ℚ)
    (g : (F.dilationPairMultidegree (q : ℚ)).realification.Group)
    (hg : g ∈ (F.dilationPairMultidegree (q : ℚ)).realification.subgroup bound) :
    (realifyFunctional η (F.ordinary.realDilationPairProjection (q : ℚ) 0 g).coord : CircleFourier.Circle) =
      (q ^ ∑ i, bound i) • (realifyFunctional η
        (F.ordinary.realDilationPairProjection (q : ℚ) 1 g).coord : CircleFourier.Circle) := by
  rw [F.realDilationPair_top_group_relation q g hg, NilpotentLieBCHGroup.coord_zpow,
    map_zsmul, AddCircle.coe_zsmul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationDescent
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realifiedAdditiveTripleOrbit {τ : Type*} (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {v : τ → ℕ}
    (q : (F.realification.additiveTripleFiltration i hi c hc).PolynomialOrbit v) :
    (F.additiveTripleFiltration i hi c hc).realification.PolynomialOrbit v :=
  NilpotentLieFiltration.polynomialOrbitOfLog
    (VectorPolynomial.map (F.realifiedAdditiveTripleEquiv i hi c hc).symm.toLinearMap q.log)
    ((F.realification.additiveTripleFiltration i hi c hc).adapted_map
      (F.additiveTripleFiltration i hi c hc).realification
      (F.realifiedAdditiveTripleEquiv i hi c hc).symm.toLinearMap
      (fun n x hx => (F.realifiedAdditiveTripleEquiv_symm_mem_layer i hi c hc n x).mpr hx) v q.adapted)

theorem realifiedAdditiveTripleOrbit_eval {τ : Type*} (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {v : τ → ℕ}
    (q : (F.realification.additiveTripleFiltration i hi c hc).PolynomialOrbit v) (x : τ → ℤ) :
    F.realifiedAdditiveTripleEquiv i hi c hc
      (((F.additiveTripleFiltration i hi c hc).realification.polynomialOrbitEval v x
        (F.realifiedAdditiveTripleOrbit i hi c hc q)).coord) =
      ((F.realification.additiveTripleFiltration i hi c hc).polynomialOrbitEval v x q).coord := by
  change F.realifiedAdditiveTripleEquiv i hi c hc
    (eval (fun j => (x j : ℚ)) (VectorPolynomial.map
      (F.realifiedAdditiveTripleEquiv i hi c hc).symm.toLinearMap q.log)) = _
  rw [eval_map]
  exact (F.realifiedAdditiveTripleEquiv i hi c hc).apply_symm_apply _

theorem realifiedAdditiveTripleOrbit_zero {τ : Type*} (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {v : τ → ℕ}
    (q : (F.realification.additiveTripleFiltration i hi c hc).PolynomialOrbit v)
    (hq : (F.realification.additiveTripleFiltration i hi c hc).polynomialOrbitEval v 0 q = 1) :
    (F.additiveTripleFiltration i hi c hc).realification.polynomialOrbitEval v 0
      (F.realifiedAdditiveTripleOrbit i hi c hc q) = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply (F.realifiedAdditiveTripleEquiv i hi c hc).injective
  rw [F.realifiedAdditiveTripleOrbit_eval, hq]
  exact (map_zero _).symm

theorem exists_real_normalized_addition_orbit (i : σ) (hi : bound i ≤ 1)
    (p : F.realification.PolynomialOrbit) (a b : F.realification.Group)
    (hp0 : F.realification.polynomialOrbitEval 0 p = a * b) :
    ∃ g : (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).realification.PolynomialOrbit (fun _ : Option σ => 1),
      (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).realification.polynomialOrbitEval _ 0 g = 1 ∧
      ∀ x : Option σ → ℤ,
        let h := (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
          (omittedCoordinateWeight_le_one i)).realification.polynomialOrbitEval _ x g
        F.realAdditiveTripleProjection i hi _ (omittedCoordinateWeight_le_one i) 0 h =
          a⁻¹ * F.realification.polynomialOrbitEval
            (Function.update (fun j => x (some j)) i (x (some i) + x none)) p * b⁻¹ ∧
        F.realAdditiveTripleProjection i hi _ (omittedCoordinateWeight_le_one i) 1 h =
          a⁻¹ * F.realification.polynomialOrbitEval (fun j => x (some j)) p * b⁻¹ ∧
        F.realAdditiveTripleProjection i hi _ (omittedCoordinateWeight_le_one i) 2 h =
          a⁻¹ * F.realification.polynomialOrbitEval
            (Function.update (fun j => x (some j)) i (x none)) p * b⁻¹ := by
  obtain ⟨q, hq0, hq⟩ := F.realification.exists_normalizedCoordinateAddition_orbit i hi p a b hp0
  refine ⟨F.realifiedAdditiveTripleOrbit i hi _ (omittedCoordinateWeight_le_one i) q,
    F.realifiedAdditiveTripleOrbit_zero i hi _ (omittedCoordinateWeight_le_one i) q hq0, ?_⟩
  intro x
  dsimp only
  have he (j : Fin 3) := F.realAdditiveTripleProjection_coord i hi _
    (omittedCoordinateWeight_le_one i) j
    ((F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
      (omittedCoordinateWeight_le_one i)).realification.polynomialOrbitEval _ x
      (F.realifiedAdditiveTripleOrbit i hi _ (omittedCoordinateWeight_le_one i) q))
  simp only [F.realifiedAdditiveTripleOrbit_eval, hq x] at he
  exact ⟨NilpotentLieBCHGroup.ext (he 0), NilpotentLieBCHGroup.ext (he 1),
    NilpotentLieBCHGroup.ext (he 2)⟩

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

namespace RationalFilteredNilmanifold.MultidegreeStructure

open CircleFourier
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)
  (i : σ) (hi : bound i ≤ 1) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
  (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
  (hEL : E.lattice = M.additiveTripleLattice i hi c hc)

noncomputable def tripleObservable (ε : D.RealGroup) (u : Fin 3 → D.Space → ℂ) (x : E.Space) : ℂ :=
  u 0 (ε • M.tripleSpaceProjection i hi c hc E hEL 0 x) *
    star (u 1 (ε • M.tripleSpaceProjection i hi c hc E hEL 1 x)) *
    star (u 2 (ε • M.tripleSpaceProjection i hi c hc E hEL 2 x))

theorem tripleObservable_mk (ε : D.RealGroup) (u : Fin 3 → D.Space → ℂ) (g : E.RealGroup) :
    M.tripleObservable i hi c hc E hEL ε u (QuotientGroup.mk g) =
      u 0 (QuotientGroup.mk (ε * M.filtration.realAdditiveTripleProjection i hi c hc 0 g)) *
        star (u 1 (QuotientGroup.mk (ε * M.filtration.realAdditiveTripleProjection i hi c hc 1 g))) *
        star (u 2 (QuotientGroup.mk (ε * M.filtration.realAdditiveTripleProjection i hi c hc 2 g))) := rfl

theorem tripleObservable_norm_le (ε : D.RealGroup) (u : Fin 3 → D.Space → ℂ)
    (hu : ∀ j x, ‖u j x‖ ≤ 1) (x : E.Space) :
    ‖M.tripleObservable i hi c hc E hEL ε u x‖ ≤ 1 := by
  simp only [tripleObservable, norm_mul, norm_star]
  have h01 : ‖u 0 (ε • M.tripleSpaceProjection i hi c hc E hEL 0 x)‖ *
      ‖u 1 (ε • M.tripleSpaceProjection i hi c hc E hEL 1 x)‖ ≤ 1 := by
    simpa only [mul_one] using mul_le_mul (hu 0 _) (hu 1 _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [mul_one] using mul_le_mul h01 (hu 2 _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem tripleSpaceProjection_top_smul (ε : D.RealGroup) (j : Fin 3) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.additiveTripleFiltration i hi c hc).realification.subgroup s)
    (x : E.Space) :
    ε • M.tripleSpaceProjection i hi c hc E hEL j (k • x) =
      M.filtration.realAdditiveTripleProjection i hi c hc j k •
        (ε • M.tripleSpaceProjection i hi c hc E hEL j x) := by
  have hz := M.filtration.realAdditiveTripleProjection_mem i hi c hc j hk
  rw [M.tripleSpaceProjection_smul, ← mul_smul, ← mul_smul,
    (M.filtration.realification.ordinary.top_commutes _ hz ε).eq]

theorem tripleObservable_component_top (ε : D.RealGroup) (u : D.Space → ℂ)
    (χ : D.RealGroup → CircleFourier.Circle)
    (hu : ∀ z, z ∈ M.filtration.realification.ordinary.subgroup s →
      ∀ x, u (z • x) = character (χ z) * u x)
    (j : Fin 3) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.additiveTripleFiltration i hi c hc).realification.subgroup s)
    (x : E.Space) :
    u (ε • M.tripleSpaceProjection i hi c hc E hEL j (k • x)) =
      character (χ (M.filtration.realAdditiveTripleProjection i hi c hc j k)) *
        u (ε • M.tripleSpaceProjection i hi c hc E hEL j x) := by
  rw [M.tripleSpaceProjection_top_smul i hi c hc E hEL ε j k hk x]
  exact hu _ (M.filtration.realAdditiveTripleProjection_mem i hi c hc j hk) _

theorem tripleObservable_top_invariant
    (ε : D.RealGroup) (u : Fin 3 → D.Space → ℂ) (χ : D.RealGroup → CircleFourier.Circle)
    (hu : ∀ j z, z ∈ M.filtration.realification.ordinary.subgroup s →
      ∀ x, u j (z • x) = character (χ z) * u j x)
    (k : E.RealGroup)
    (hk : k ∈ (M.filtration.additiveTripleFiltration i hi c hc).realification.subgroup s)
    (hphase : χ (M.filtration.realAdditiveTripleProjection i hi c hc 0 k) =
      χ (M.filtration.realAdditiveTripleProjection i hi c hc 1 k) +
        χ (M.filtration.realAdditiveTripleProjection i hi c hc 2 k))
    (x : E.Space) :
    M.tripleObservable i hi c hc E hEL ε u (k • x) =
      M.tripleObservable i hi c hc E hEL ε u x := by
  have hvalue (j : Fin 3) := M.tripleObservable_component_top i hi c hc E hEL ε (u j) χ (hu j) j k hk x
  have hprod := congrArg₂ (fun a b : ℂ => a * b)
    (congrArg₂ (fun a b : ℂ => a * star b) (hvalue 0) (hvalue 1))
    (congrArg star (hvalue 2))
  exact hprod.trans (triple_phase_cancellation
    (fun j => u j (ε • M.tripleSpaceProjection i hi c hc E hEL j x))
    (fun j => χ (M.filtration.realAdditiveTripleProjection i hi c hc j k)) hphase)

end RationalFilteredNilmanifold.MultidegreeStructure
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_native_addition_orbit (i : σ) (hi : bound i ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) s r)
    (hEF : E.filtration = M.filtration.additiveTripleFiltration i hi
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ) :
    ∃ q : E.filtration.realification.PolynomialOrbit (fun _ : Option σ => 1),
      E.filtration.realification.polynomialOrbitEval _ 0 q = 1 ∧
      ∀ (x : Option σ → ℤ) (j : Fin 3),
        (QuotientGroup.mk (ε * M.filtration.realAdditiveTripleProjection i hi
          (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i) j
          (E.filtration.realification.polynomialOrbitEval _ x q)) : D.Space) =
          QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x j) g) := by
  let F := M.filtration.additiveTripleFiltration i hi
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)
  obtain ⟨q, hq0, hq⟩ := M.filtration.exists_real_normalized_addition_orbit i hi g ε γ hfactor
  have hF : F.realification = E.filtration.realification := by rw [hEF]
  let qE := F.realification.orbitEquivOfEq hF (fun _ : Option σ => 1) q
  have hqE (x : Option σ → ℤ) : E.filtration.realification.polynomialOrbitEval _ x qE =
      F.realification.polynomialOrbitEval _ x q := F.realification.orbitEquivOfEq_eval hF _ q x
  have hvalues (x : Option σ → ℤ) (j : Fin 3) :
      M.filtration.realAdditiveTripleProjection i hi _ (omittedCoordinateWeight_le_one i) j
        (F.realification.polynomialOrbitEval _ x q) =
          ε⁻¹ * M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x j) g * γ⁻¹ := by
    fin_cases j
    · exact (hq x).1
    · exact (hq x).2.1
    · exact (hq x).2.2
  refine ⟨qE, (hqE 0).trans hq0, ?_⟩
  intro x j
  rw [hqE, hvalues]
  simp only [← mul_assoc, mul_inv_cancel, one_mul]
  exact QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ)

theorem tripleObservable_of_addition_values (i : σ) (hi : bound i ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) s r)
    (hEL : E.lattice = M.additiveTripleLattice i hi
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
    (g : M.filtration.realification.PolynomialOrbit) (ε : D.RealGroup)
    (q : E.filtration.realification.PolynomialOrbit (fun _ : Option σ => 1))
    (hvalues : ∀ (x : Option σ → ℤ) (j : Fin 3),
      (QuotientGroup.mk (ε * M.filtration.realAdditiveTripleProjection i hi
        (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i) j
        (E.filtration.realification.polynomialOrbitEval _ x q)) : D.Space) =
        QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x j) g))
    (u : Fin 3 → D.Space → ℂ) (x : Option σ → ℤ) :
    M.tripleObservable i hi _ (omittedCoordinateWeight_le_one i) E hEL ε u
      (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval _ x q)) =
        u 0 (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x 0) g)) *
        star (u 1 (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x 1) g))) *
        star (u 2 (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x 2) g))) := by
  rw [M.tripleObservable_mk, hvalues x 0, hvalues x 1, hvalues x 2]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem real_top_frequency_mul {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (η : L →ₗ[ℚ] ℚ)
    (z w : F.realification.Group) (hz : z ∈ F.realification.subgroup s) :
    ((realifyFunctional η (z * w).coord : ℝ) : CircleFourier.Circle) =
      (realifyFunctional η z.coord : CircleFourier.Circle) +
        (realifyFunctional η w.coord : CircleFourier.Circle) := by
  change ((realifyFunctional η (lieBCH s z.coord w.coord) : ℝ) : CircleFourier.Circle) = _
  rw [lieBCH_eq_add_of_lie_eq_zero F.realification.lowerCentralSeries_eq_bot
    (F.realification.top_layer_central hz w.coord), map_add, AddCircle.coe_add]

theorem MultidegreeLieFiltration.realAdditiveTriple_frequency_phase
    {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
    (i : σ) (hi : bound i ≤ 1) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (htop : F.realification.weightedLayer c s = ⊥) (η : L →ₗ[ℚ] ℚ)
    (g : (F.additiveTripleFiltration i hi c hc).realification.Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi c hc).realification.subgroup s) :
    (realifyFunctional η (F.realAdditiveTripleProjection i hi c hc 0 g).coord : CircleFourier.Circle) =
      (realifyFunctional η (F.realAdditiveTripleProjection i hi c hc 1 g).coord : CircleFourier.Circle) +
        (realifyFunctional η (F.realAdditiveTripleProjection i hi c hc 2 g).coord : CircleFourier.Circle) := by
  apply F.realAdditiveTriple_top_phase i hi c hc htop
    (fun z => (realifyFunctional η z.coord : CircleFourier.Circle)) ?_ g hg
  intro z w hz _
  exact real_top_frequency_mul F.ordinary η z w hz

theorem MultidegreeLieFiltration.realAdditiveTriple_omitted_frequency_phase
    {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
    (i : σ) (hi : bound i = 1) (hs : ∑ j, bound j = s) (η : L →ₗ[ℚ] ℚ)
    (g : (F.additiveTripleFiltration i hi.le (omittedCoordinateWeight i)
      (omittedCoordinateWeight_le_one i)).realification.Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi.le (omittedCoordinateWeight i)
      (omittedCoordinateWeight_le_one i)).realification.subgroup s) :
    (realifyFunctional η (F.realAdditiveTripleProjection i hi.le _
      (omittedCoordinateWeight_le_one i) 0 g).coord : CircleFourier.Circle) =
      (realifyFunctional η (F.realAdditiveTripleProjection i hi.le _
        (omittedCoordinateWeight_le_one i) 1 g).coord : CircleFourier.Circle) +
      (realifyFunctional η (F.realAdditiveTripleProjection i hi.le _
        (omittedCoordinateWeight_le_one i) 2 g).coord : CircleFourier.Circle) :=
  F.realAdditiveTriple_frequency_phase i hi.le _ (omittedCoordinateWeight_le_one i)
    (F.realification.omitted_weighted_top i hi hs) η g hg

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound)

omit [DecidableEq σ] in
theorem unitVertical_top_action (hs : ∑ j, bound j = s)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (a : I) (z : D.RealGroup) (hz : z ∈ M.filtration.realification.ordinary.subgroup s)
    (x : D.Space) : V.observable a (z • x) =
      character (realifyFunctional V.frequency z.coord : CircleFourier.Circle) * V.observable a x := by
  have htop : M.realSubgroup bound = M.filtration.realification.ordinary.subgroup s := by
    rw [M.realSubgroup_top, hs]
    change D.filtration.realification.subgroup s = M.filtration.ordinary.realification.subgroup s
    rw [M.ordinary]
  exact V.vertical a z (htop.symm ▸ hz) x

theorem unitVertical_triple_top_invariant (i : σ) (hi : bound i = 1)
    (hs : ∑ j, bound j = s)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) s r)
    (hEL : E.lattice = M.additiveTripleLattice i hi.le
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (ε : D.RealGroup) (a : Fin 3 → I) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.additiveTripleFiltration i hi.le
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)).realification.subgroup s)
    (x : E.Space) :
    M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i) E hEL ε
        (fun j => V.observable (a j)) (k • x) =
      M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i) E hEL ε
        (fun j => V.observable (a j)) x := by
  apply M.tripleObservable_top_invariant i hi.le _ (omittedCoordinateWeight_le_one i) E hEL
    ε (fun j => V.observable (a j))
    (fun z => (realifyFunctional V.frequency z.coord : CircleFourier.Circle)) ?_ k hk ?_ x
  · intro j z hz y
    exact M.unitVertical_top_action hs V (a j) z hz y
  · exact M.filtration.realAdditiveTriple_omitted_frequency_phase i hi hs V.frequency ⟨k.coord⟩ hk

end RationalFilteredNilmanifold.MultidegreeStructure
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r n : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) (i : σ) (hi : bound i = 1)
  (hs : ∑ j, bound j = s + 1)

variable (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) (s + 1) r)
  (hEF : E.filtration = M.filtration.additiveTripleFiltration i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  (hEL : E.lattice = M.additiveTripleLattice i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  [TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))] [T2Space (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))]

variable (Q : RationalFilteredNilmanifold ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))) s n)
  (hQL : Q.lattice = E.lattice.map (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl))
  [TopologicalSpace (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))] [T2Space (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))]

include hs hEF hQL

theorem exists_lipschitz_unitVertical_triple_descent
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j k, RationalHeightLE (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) H)
    (hstructure : ∀ a b c, RationalHeightLE (lieStructureConstants Q.basis a b c) H)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (ε : D.RealGroup) (a : Fin 3 → I) (A : ℝ≥0)
    (hLip : letI := E.metricSpace
      LipschitzWith A (M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
        E hEL ε (fun j => V.observable (a j)))) :
    letI := Q.metricSpace
    ∃ v : Q.Space → ℂ,
      (∀ g : E.RealGroup, v (QuotientGroup.mk (realificationMap
        (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap (E.filtration.layerIdeal (s + 1))) g)) =
          M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
            E hEL ε (fun j => V.observable (a j)) (QuotientGroup.mk g)) ∧
      LipschitzWith (rationalReconstructionLipschitzBound s r n H A 1) v ∧
      ∀ x, ‖v x‖ ≤ 1 := by
  let : MetricSpace (Q.RealGroup ⧸ Q.lattice.map realificationHom) :=
    realificationQuotientMetricSpace Q.basis Q.lattice Q.grid Q.grid_pos Q.outer_grid
  have hcover : Q.lattice ≤ E.lattice.map (mapOfSteps
      (hL := E.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap (E.filtration.layerIdeal (s + 1)))) := by
    rw [hQL]
    exact le_rfl
  have hker : ∀ k ∈ (realificationMap
      (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap (E.filtration.layerIdeal (s + 1)))).ker,
      ∀ x : E.RealGroup,
        M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
          E hEL ε (fun j => V.observable (a j)) (QuotientGroup.mk (k * x)) =
        M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
          E hEL ε (fun j => V.observable (a j)) (QuotientGroup.mk x) := by
    intro k hk x
    have hkE : k ∈ E.filtration.realification.subgroup (s + 1) :=
      (E.filtration.mem_realQuotientStepHom_ker (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl k).mp hk
    have hkF : k ∈ (M.filtration.additiveTripleFiltration i hi.le
        (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)).realification.subgroup (s + 1) := by
      rw [← hEF]
      exact hkE
    exact M.unitVertical_triple_top_invariant i hi hs E hEL V ε a k hkF (QuotientGroup.mk x)
  obtain ⟨v, hv, hvlip, hvnorm⟩ := exists_lipschitz_realification_reconstruction
    (hL := E.filtration.lowerCentralSeries_eq_bot) (hM := Q.filtration.lowerCentralSeries_eq_bot)
    E.basis Q.basis (lieQuotientMap (E.filtration.layerIdeal (s + 1))) (lieQuotientMap_surjective (E.filtration.layerIdeal (s + 1))) E.lattice Q.lattice hcover
    E.grid Q.grid H E.grid_pos Q.grid_pos hH E.outer_grid Q.outer_grid hentries hstructure
    (M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
      E hEL ε (fun j => V.observable (a j))) hker A 1 hLip
    (M.tripleObservable_norm_le i hi.le _ (omittedCoordinateWeight_le_one i)
      E hEL ε (fun j => V.observable (a j)) (fun j x => V.norm (a j) x))
  let vQ : Q.Space → ℂ := v
  refine ⟨vQ, hv, ?_, ?_⟩
  · exact hvlip.weaken (by simp only [Fintype.card_fin, le_refl])
  · intro x
    exact hvnorm x

theorem exists_unitVertical_triple_quotient_niltest {τ : Type*} {w : τ → ℕ}
    (hQF : Q.filtration = E.filtration.quotientTop)
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j k, RationalHeightLE (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) H)
    (hstructure : ∀ a b c, RationalHeightLE (lieStructureConstants Q.basis a b c) H)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (ε : D.RealGroup) (a : Fin 3 → I) (A : ℝ≥0)
    (hLip : letI := E.metricSpace
      LipschitzWith A (M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
        E hEL ε (fun j => V.observable (a j))))
    (g : E.filtration.realification.PolynomialOrbit w) :
    ∃ T : Q.Niltest w, T.normBound = 1 ∧
      T.lipBound = rationalReconstructionLipschitzBound s r n H A 1 ∧
      T.orbit = E.topQuotientOrbit Q hQF g ∧
      ∀ x : τ → ℤ, T.eval x =
        M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
          E hEL ε (fun j => V.observable (a j))
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval w x g)) := by
  obtain ⟨v, hv, hvlip, hvnorm⟩ := M.exists_lipschitz_unitVertical_triple_descent
    i hi hs E hEF hEL Q hQL hH hentries hstructure V ε a A hLip
  let T : Q.Niltest w :=
    { orbit := E.topQuotientOrbit Q hQF g
      observable := v
      normBound := 1
      lipBound := rationalReconstructionLipschitzBound s r n H A 1
      norm_le := hvnorm
      lipschitz := hvlip }
  refine ⟨T, rfl, rfl, rfl, fun x => ?_⟩
  change v (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitEval w x
    (E.topQuotientOrbit Q hQF g))) = _
  rw [E.topQuotientOrbit_eval Q hQF]
  exact hv _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound)

theorem unitVertical_dilation_top_invariant (q : ℤ) (hs : ∑ j, bound j = s)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) s r)
    (hEL : E.lattice = M.dilationPairLattice (q : ℚ))
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (ε : D.RealGroup) (a₀ : I) (a : Fin (q ^ s).natAbs → I) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.ordinary.dilationPairFiltration (q : ℚ)).realification.subgroup s)
    (x : E.Space) :
    M.dilationObservable (q : ℚ) E hEL (q ^ s) ε (V.observable a₀)
        (fun j => V.observable (a j)) (k • x) =
      M.dilationObservable (q : ℚ) E hEL (q ^ s) ε (V.observable a₀)
        (fun j => V.observable (a j)) x := by
  apply M.dilationObservable_top_invariant (q : ℚ) E hEL (q ^ s) ε
    (V.observable a₀) (fun j => V.observable (a j))
    (fun z => (realifyFunctional V.frequency z.coord : CircleFourier.Circle)) ?_ ?_ k hk ?_ x
  · exact fun z hz y => M.unitVertical_top_action hs V a₀ z hz y
  · exact fun j z hz y => M.unitVertical_top_action hs V (a j) z hz y
  · exact M.filtration.ordinary.realDilationPair_frequency_phase q V.frequency ⟨k.coord⟩ hk

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r n : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) (q : ℤ) (hs : ∑ j, bound j = s + 1)
  (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) (s + 1) r)
  (hEF : E.filtration = M.filtration.ordinary.dilationPairFiltration (q : ℚ))
  (hEL : E.lattice = M.dilationPairLattice (q : ℚ))
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra (q : ℚ))]
  (Q : RationalFilteredNilmanifold
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  (hQF : Q.filtration = E.filtration.quotientTop)
  (hQL : Q.lattice = E.lattice.map
    (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl))
  [TopologicalSpace (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ]
    ((M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) ⧸ E.filtration.layerIdeal (s + 1)))]

include hs hEF hQF hQL

omit [DecidableEq σ] in
theorem exists_unitVertical_dilation_quotient_niltest {τ : Type*} {w : τ → ℕ}
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j k, RationalHeightLE
      (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) H)
    (hstructure : ∀ a b c, RationalHeightLE (lieStructureConstants Q.basis a b c) H)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (ε : D.RealGroup) (a₀ : I) (a : Fin (q ^ (s + 1)).natAbs → I) (A : ℝ≥0)
    (hLip : letI := E.metricSpace
      LipschitzWith A (M.dilationObservable (q : ℚ) E hEL (q ^ (s + 1)) ε
        (V.observable a₀) (fun j => V.observable (a j))))
    (g : E.filtration.realification.PolynomialOrbit w) :
    ∃ T : Q.Niltest w, T.normBound = 1 ∧
      T.lipBound = rationalReconstructionLipschitzBound s r n H A 1 ∧
      T.orbit = E.topQuotientOrbit Q hQF g ∧
      ∀ x : τ → ℤ, T.eval x =
        M.dilationObservable (q : ℚ) E hEL (q ^ (s + 1)) ε
          (V.observable a₀) (fun j => V.observable (a j))
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval w x g)) := by
  let U : E.Niltest w :=
    { orbit := g
      observable := M.dilationObservable (q : ℚ) E hEL (q ^ (s + 1)) ε
        (V.observable a₀) (fun j => V.observable (a j))
      normBound := 1
      lipBound := A
      norm_le := M.dilationObservable_norm_le (q : ℚ) E hEL (q ^ (s + 1)) ε
        (V.observable a₀) (fun j => V.observable (a j)) (V.norm a₀) (fun j => V.norm (a j))
      lipschitz := hLip }
  have hinv : ∀ k ∈ E.filtration.realification.subgroup (s + 1), ∀ x,
      U.observable (k • x) = U.observable x := by
    intro k hk x
    have hk' : k ∈ (M.filtration.ordinary.dilationPairFiltration (q : ℚ)).realification.subgroup
        (s + 1) := by rw [← hEF]; exact hk
    exact M.unitVertical_dilation_top_invariant q hs E hEL V ε a₀ a k hk' x
  obtain ⟨T, hTo, hTn, hTl, hTe⟩ := E.exists_topInvariant_niltest Q hQF hQL U hinv H hH hentries hstructure
  exact ⟨T, hTn, hTl, hTo, hTe⟩

theorem exists_dilation_niltest_of_data {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j k, RationalHeightLE
      (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) H)
    (hstructure : ∀ a b c, RationalHeightLE (lieStructureConstants Q.basis a b c) H)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (a₀ : I) (a : Fin (q ^ (s + 1)).natAbs → I) (A : ℝ≥0)
    (hLip : letI := E.metricSpace
      LipschitzWith A (M.dilationObservable (q : ℚ) E hEL (q ^ (s + 1)) ε
        (V.observable a₀) (fun j => V.observable (a j)))) :
    ∃ T : Q.Niltest (fun _ : σ => 1), T.normBound = 1 ∧
      T.lipBound = rationalReconstructionLipschitzBound s r n H A 1 ∧
      Q.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
      ∀ x, T.eval x =
        V.observable a₀ (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval
          (fun i => q * x i) g)) *
        star (signedTensorProduct (q ^ (s + 1)) (fun j => V.observable (a j)
          (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)))) := by
  obtain ⟨h, hh0, hh⟩ := M.exists_native_dilation_orbit q E hEF g ε γ hγ hfactor
  obtain ⟨T, hTn, hTl, hTo, hTe⟩ := M.exists_unitVertical_dilation_quotient_niltest
    q hs E hEF hEL Q hQF hQL hH hentries hstructure V ε a₀ a A hLip h
  refine ⟨T, hTn, hTl, ?_, ?_⟩
  · rw [hTo, E.topQuotientOrbit_eval Q hQF, hh0, map_one]
  · intro x
    rw [hTe, M.dilationObservable_mk, (hh x).1, (hh x).2]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeLocalPivotVerticalPartners
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exp_scaled_norm_le_one {b : ℝ} {z : ℂ} (hz : ‖z‖ ≤ Real.exp b) :
    ‖(Real.exp (-b) : ℂ) * z‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-b) * Real.exp b := mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

theorem finite_double_normalization {X : Type*} (S : Finset X) (f g : X → ℂ) (b : ℝ)
    (hcorr : Real.exp (-b) ≤ ‖𝔼 x ∈ S, f x * g x‖) :
    Real.exp (-(3 * b)) ≤ ‖𝔼 x ∈ S,
      ((Real.exp (-b) : ℂ) * f x) * ((Real.exp (-b) : ℂ) * g x)‖ := by
  have hmean : (𝔼 x ∈ S, ((Real.exp (-b) : ℂ) * f x) * ((Real.exp (-b) : ℂ) * g x)) =
      ((Real.exp (-b) : ℂ) * (Real.exp (-b) : ℂ)) * (𝔼 x ∈ S, f x * g x) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [hmean, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(3 * b)) = (Real.exp (-b) * Real.exp (-b)) * Real.exp (-b) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcorr (by positivity)

theorem finite_remove_normalization {X : Type*} (S : Finset X) (f g : X → ℂ)
    {b rho : ℝ} (hb : 0 ≤ b)
    (hcorr : rho ≤ ‖𝔼 x ∈ S, ((Real.exp (-b) : ℂ) * f x) * g x‖) :
    rho ≤ ‖𝔼 x ∈ S, f x * g x‖ := by
  have hmean : (𝔼 x ∈ S, ((Real.exp (-b) : ℂ) * f x) * g x) =
      (Real.exp (-b) : ℂ) * (𝔼 x ∈ S, f x * g x) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [hmean, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at hcorr
  exact hcorr.trans (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hb)))

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem weighted_fixed_choices {Ω K : Type*} {I : K → Type*}
    [Fintype Ω] [Fintype K] [∀ k, Fintype (I k)]
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (rel : ∀ (_ : Ω) (k : K), I k → Prop)
    (hex : ∀ a ∈ H, ∀ k, ∃ i, rel a k i) {b : ℝ}
    (hcard : ∀ k, (Fintype.card (I k) : ℝ) ≤ Real.exp b) :
    ∃ (choice : ∀ k, I k) (S : Finset Ω), S ⊆ H ∧ 0 < outer.mass S ∧
      Real.exp (-b * Fintype.card K) * outer.mass H ≤ outer.mass S ∧
      ∀ a ∈ S, ∀ k, rel a k (choice k) := by
  classical
  have hHne : H.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he] at hH
    simp only [FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hH
  obtain ⟨a0, ha0⟩ := hHne
  let : ∀ k, Nonempty (I k) := fun k => ⟨(hex a0 ha0 k).choose⟩
  let code : Ω → ∀ k, I k := fun a k =>
    if ha : a ∈ H then (hex a ha k).choose else (hex a0 ha0 k).choose
  have hcode (a : Ω) (ha : a ∈ H) (k : K) : rel a k (code a k) := by
    simpa only [code, dif_pos ha] using (hex a ha k).choose_spec
  have hc : (Fintype.card (∀ k, I k) : ℝ) ≤ Real.exp (b * Fintype.card K) := by
    rw [Fintype.card_pi, Nat.cast_prod]
    calc
      _ ≤ ∏ _k : K, Real.exp b :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun k _ => hcard k)
      _ = (Real.exp b) ^ Fintype.card K := by simp
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨choice, hchoice⟩ := outer.exists_code_fiber_mass H code
  let S := H.filter (fun a => code a = choice)
  have hmass : Real.exp (-b * Fintype.card K) * outer.mass H ≤ outer.mass S := by
    calc
      _ = outer.mass H / Real.exp (b * Fintype.card K) := by
        rw [show -b * (Fintype.card K : ℝ) = -(b * Fintype.card K) by ring,
          Real.exp_neg, div_eq_mul_inv, mul_comm]
      _ ≤ outer.mass H / Fintype.card (∀ k, I k) :=
        div_le_div_of_nonneg_left hH.le (by positivity) hc
      _ ≤ _ := hchoice
      _ = outer.mass S := by
        congr 1
        ext a
        simp only [S, Finset.mem_filter]
  refine ⟨choice, S, Finset.filter_subset _ _, (mul_pos (Real.exp_pos _) hH).trans_le hmass,
    hmass, ?_⟩
  intro a ha k
  obtain ⟨haH, he⟩ := Finset.mem_filter.mp ha
  rw [← he]
  exact hcode a haH k

theorem exists_weighted_native_vertical_partners
    {Ω K T σ : Type*} [Fintype Ω] [Fintype K] {L : K → Type*}
    [∀ k, LieRing (L k)] [∀ k, LieAlgebra ℚ (L k)] {s : ℕ} {d : K → ℕ}
    [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L k)] [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L k)]
    [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L k)] [∀ k, T2Space (ℝ ⊗[ℚ] L k)]
    (D : ∀ k, RationalFilteredNilmanifold (L k) s (d k)) {w : σ → ℕ}
    (Q : ∀ k, (D k).Niltest w)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (S : Ω → K → Finset T) (point : Ω → T → σ → ℤ)
    (weight : Ω → K → T → ℂ) {p q delta : ℝ}
    (hq : 0 ≤ q) (hpq : p ≤ q) (hdelta : 0 < delta)
    (hprecision : (delta / 2)⁻¹ ≤ Real.exp q)
    (hQ : ∀ k, (Q k).ComplexityLE p) (hcap : ∀ k, ((Q k).normBound : ℝ) ≤ 1)
    (hS : ∀ a ∈ H, ∀ k, (S a k).Nonempty)
    (hweight : ∀ a ∈ H, ∀ k t, t ∈ S a k → ‖weight a k t‖ ≤ 1)
    (hcorr : ∀ a ∈ H, ∀ k, delta ≤
      ‖𝔼 t ∈ S a k, weight a k t * (Q k).eval (point a t)‖) :
    ∃ (freq : ∀ k, L k →ₗ[ℚ] ℚ) (V : ∀ k, (D k).Niltest w) (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      Real.exp (-verticalDecompositionBudget q * Fintype.card K) * outer.mass H ≤
        outer.mass retained ∧
      (∀ k, (V k).ComplexityLE p ∧ (V k).orbit = (Q k).orbit ∧
        (V k).normBound = (Q k).normBound ∧ (V k).lipBound = (Q k).lipBound ∧
        ((V k).normBound : ℝ) ≤ 1) ∧
      (∀ k i, rationalLogHeight (freq k ((D k).basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s → ∀ x,
        (V k).observable (z • x) =
          character ((realifyFunctional (freq k) z.coord : ℝ) : CircleFourier.Circle) *
            (V k).observable x) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s →
        z ∈ (D k).realLattice → ∃ n : ℤ, realifyFunctional (freq k) z.coord = n) ∧
      (∀ k (z : (D k).RealGroup) (c : ℂ),
        (∀ x, (Q k).observable (z • x) = c * (Q k).observable x) →
        ∀ x, (V k).observable (z • x) = c * (V k).observable x) ∧
      ∀ a ∈ retained, ∀ k, delta / (2 * Real.exp (verticalDecompositionBudget q)) ≤
        ‖𝔼 t ∈ S a k, weight a k t * (V k).eval (point a t)‖ := by
  classical
  choose I instI freq V hcard hheight hcert hvert hint hpres hobs happrox using
    fun k => (Q k).exists_vertical_decomposition_preserving_bounds_and_characters
      hq ((hQ k).mono hpq) (by positivity : 0 < delta / 2) hprecision
  let : ∀ k, Fintype (I k) := instI
  let rel : ∀ (_ : Ω) (k : K), I k → Prop := fun a k i =>
    delta / (2 * Real.exp (verticalDecompositionBudget q)) ≤
      ‖𝔼 t ∈ S a k, weight a k t * (V k i).eval (point a t)‖
  have hex (a : Ω) (ha : a ∈ H) (k : K) : ∃ i, rel a k i := by
    have hh := exists_correlating_summand (hS a ha k) (weight a k)
      (fun t => star ((Q k).eval (point a t)))
      (fun i t => star ((V k i).eval (point a t))) hdelta (Real.exp_pos _)
      (hcard k) (hweight a ha k)
    apply (by simpa only [finiteCorrelation, star_star, rel] using hh)
    · intro t _
      simpa only [← star_sum, ← star_sub, norm_star] using happrox k (point a t)
    · simpa only [finiteCorrelation, star_star] using hcorr a ha k
  obtain ⟨choice, retained, hsub, hpos, hmass, hselected⟩ :=
    weighted_fixed_choices outer H hH rel hex hcard
  have hnonzero (k : K) : ∃ x, (V k (choice k)).observable x ≠ 0 := by
    by_contra! hz
    have hne : retained.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he] at hpos
      simp only [FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hpos
    obtain ⟨a, ha⟩ := hne
    have he := hselected a ha k
    have heval (t : T) : (V k (choice k)).eval (point a t) = 0 := hz _
    change delta / (2 * Real.exp (verticalDecompositionBudget q)) ≤ _ at he
    simp only [heval, mul_zero, Finset.expect_const_zero, norm_zero] at he
    exact (not_le_of_gt (by positivity : 0 < delta / (2 * Real.exp
      (verticalDecompositionBudget q)))) he
  refine ⟨fun k => freq k (choice k), fun k => V k (choice k), retained,
    hsub, hpos, hmass, ?_, fun k => hheight k (choice k), fun k => hvert k (choice k),
    fun k => hint k (choice k) (hnonzero k), fun k z c hc x => hpres k z c hc (choice k) x,
    hselected⟩
  intro k
  obtain ⟨_, ho, hn, hl⟩ := hcert k (choice k)
  have hcOriginal : (V k (choice k)).ComplexityLE p := by
    refine ⟨(hQ k).1, ?_⟩
    rw [hn, hl]
    exact (hQ k).2
  exact ⟨hcOriginal, ho, hn, hl, hn ▸ hcap k⟩

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem norm_expect_scaled_product {T : Type*} (S : Finset T)
    (c : ℝ) (hc : 0 ≤ c) (f g : T → ℂ) :
    ‖𝔼 t ∈ S, ((c : ℂ) * f t) * g t‖ = c * ‖𝔼 t ∈ S, f t * g t‖ := by
  have he : (𝔼 t ∈ S, ((c : ℂ) * f t) * g t) =
      (c : ℂ) * (𝔼 t ∈ S, f t * g t) := by
    simp only [mul_assoc, Finset.mul_expect]
  rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]

theorem exists_localPivot_weighted_native_vertical_partners
    {Ω K T σ τ : Type*} [Fintype Ω] [Fintype K]
    {L : K → Type*} {Llocal : Ω → K → Type*}
    [∀ k, LieRing (L k)] [∀ k, LieAlgebra ℚ (L k)]
    [∀ a k, LieRing (Llocal a k)] [∀ a k, LieAlgebra ℚ (Llocal a k)]
    {s : ℕ} {d : K → ℕ} {sLocal dLocal : Ω → K → ℕ}
    [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L k)]
    [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L k)]
    [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L k)] [∀ k, T2Space (ℝ ⊗[ℚ] L k)]
    [∀ a k, TopologicalSpace (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, IsTopologicalAddGroup (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, ContinuousSMul ℝ (ℝ ⊗[ℚ] Llocal a k)]
    [∀ a k, T2Space (ℝ ⊗[ℚ] Llocal a k)]
    (D : ∀ k, RationalFilteredNilmanifold (L k) s (d k))
    (Dlocal : ∀ a k, RationalFilteredNilmanifold (Llocal a k) (sLocal a k) (dLocal a k))
    {w : σ → ℕ} {wLocal : τ → ℕ}
    (Q : ∀ k, (D k).Niltest w) (P : ∀ a k, (Dlocal a k).Niltest wLocal)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (S : Ω → K → Finset T)
    (pointAmbient : Ω → T → σ → ℤ) (pointLocal : Ω → K → T → τ → ℤ)
    (twist : Ω → K → T → ℂ) {pNative pLocal r q : ℝ}
    (hpLocal : 0 ≤ pLocal) (hr : 0 ≤ r) (hpq : pNative ≤ q)
    (hprecision : pLocal + r + 1 ≤ q)
    (hQ : ∀ k, (Q k).ComplexityLE pNative)
    (hcap : ∀ k, ((Q k).normBound : ℝ) ≤ 1)
    (hP : ∀ a ∈ H, ∀ k, (P a k).ComplexityLE pLocal)
    (htwist : ∀ a ∈ H, ∀ k t, t ∈ S a k → ‖twist a k t‖ ≤ 1)
    (hcorr : ∀ a ∈ H, ∀ k, Real.exp (-r) ≤
      ‖𝔼 t ∈ S a k,
        ((P a k).eval (pointLocal a k t) * twist a k t) * (Q k).eval (pointAmbient a t)‖) :
    ∃ (freq : ∀ k, L k →ₗ[ℚ] ℚ) (V : ∀ k, (D k).Niltest w) (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      Real.exp (-verticalDecompositionBudget q * Fintype.card K) * outer.mass H ≤
        outer.mass retained ∧
      (∀ k, (V k).ComplexityLE pNative ∧ (V k).orbit = (Q k).orbit ∧
        (V k).normBound = (Q k).normBound ∧ (V k).lipBound = (Q k).lipBound ∧
        ((V k).normBound : ℝ) ≤ 1) ∧
      (∀ k i, rationalLogHeight (freq k ((D k).basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s → ∀ x,
        (V k).observable (z • x) =
          character ((realifyFunctional (freq k) z.coord : ℝ) : CircleFourier.Circle) *
            (V k).observable x) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s →
        z ∈ (D k).realLattice → ∃ n : ℤ, realifyFunctional (freq k) z.coord = n) ∧
      (∀ k (z : (D k).RealGroup) (c : ℂ),
        (∀ x, (Q k).observable (z • x) = c * (Q k).observable x) →
        ∀ x, (V k).observable (z • x) = c * (V k).observable x) ∧
      ∀ a ∈ retained, ∀ k, Real.exp (-r) / (2 * Real.exp (verticalDecompositionBudget q)) ≤
        ‖𝔼 t ∈ S a k,
          ((P a k).eval (pointLocal a k t) * twist a k t) * (V k).eval (pointAmbient a t)‖ := by
  classical
  let weight : Ω → K → T → ℂ := fun a k t =>
    (Real.exp (-pLocal) : ℂ) * ((P a k).eval (pointLocal a k t) * twist a k t)
  have hweight (a : Ω) (ha : a ∈ H) (k : K) (t : T) (ht : t ∈ S a k) :
      ‖weight a k t‖ ≤ 1 := by
    change ‖((Real.exp (-pLocal) : ℂ) *
      ((P a k).eval (pointLocal a k t) * twist a k t))‖ ≤ 1
    rw [← mul_assoc, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (exp_scaled_norm_le_one ((P a k).eval_budget (hP a ha k) _))).trans
      (htwist a ha k t ht)
  have hS (a : Ω) (ha : a ∈ H) (k : K) : (S a k).Nonempty := by
    by_contra hn
    have hh := hcorr a ha k
    rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hh
    simp only [Finset.expect_empty, norm_zero] at hh
    exact (not_le_of_gt (Real.exp_pos _)) hh
  have hnormalized (a : Ω) (ha : a ∈ H) (k : K) :
      Real.exp (-pLocal) * Real.exp (-r) ≤
        ‖𝔼 t ∈ S a k, weight a k t * (Q k).eval (pointAmbient a t)‖ := by
    change _ ≤ ‖𝔼 t ∈ S a k,
      ((Real.exp (-pLocal) : ℂ) * ((P a k).eval (pointLocal a k t) * twist a k t)) *
        (Q k).eval (pointAmbient a t)‖
    rw [norm_expect_scaled_product _ _ (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hcorr a ha k) (Real.exp_nonneg _)
  obtain ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, hint,
      hpres, hselected⟩ := exists_weighted_native_vertical_partners D Q outer H hH S
    pointAmbient weight (by linarith : 0 ≤ q) hpq (by positivity)
    (nativeLocalPivotVertical_inverse_precision_le_exp hprecision) hQ hcap hS hweight hnormalized
  refine ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, hint, hpres, ?_⟩
  intro a ha k
  have hs := hselected a ha k
  change (Real.exp (-pLocal) * Real.exp (-r)) /
      (2 * Real.exp (verticalDecompositionBudget q)) ≤
    ‖𝔼 t ∈ S a k,
      ((Real.exp (-pLocal) : ℂ) * ((P a k).eval (pointLocal a k t) * twist a k t)) *
        (V k).eval (pointAmbient a t)‖ at hs
  rw [norm_expect_scaled_product _ _ (Real.exp_nonneg _), mul_div_assoc] at hs
  exact (mul_le_mul_iff_right₀ (Real.exp_pos (-pLocal))).mp
    (by simpa only [mul_comm] using hs)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedTranslationMajorTwistedVerticalSelection
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial CircleFourier
open scoped TensorProduct BigOperators NNReal

theorem exists_translation_major_twisted_vertical_selection :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X U L : Type*} [LieRing L] [LieAlgebra ℚ L]
      {m d t e : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
      (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M) (D : RationalFilteredNilmanifold L t e) (htd : t < d) (ω : U → ℕ)
      (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (mass K : ℝ≥0)
      (_hdegree : D₀.totalDegree ≤ d) (_hD : realPolynomialMass D₀ ≤ mass)
      (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit ω)
      (R : D.Niltest ω) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ mass K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (B : Finset X), B.Nonempty → ∀ (sample : X → U → ℤ) (multiplier : X → ℂ),
      (∀ x ∈ B, ‖multiplier x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ B, multiplier x *
        twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval ω (sample x) orbit)) *
        R.eval (sample x)‖ →
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (V : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Niltest ω)
        (W : (D.raiseStep htd.le).Niltest ω),
        V.ComplexityLE ((raisedNiltestBudget p + C) ^ C) ∧
        V.orbit = orbit ∧ V.normBound = 1 ∧
        W.ComplexityLE ((raisedNiltestBudget p + C) ^ C) ∧
        W.orbit = D.raiseStepRealOrbit htd.le R.orbit ∧ W.normBound = R.normBound ∧
        (∀ i, rationalLogHeight (η ((weightedTranslationResidueNilmanifold w d hw hwd M hM).basis i)) ≤
          (raisedNiltestBudget p + C) ^ C) ∧
        η (centralRationalElement w d hd 1) = 1 ∧
        (∀ z, z ∈ (weightedFiltration w d hwd).realification.subgroup d → ∀ x,
          V.observable (z • x) =
            character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x) ∧
        (∀ z, z ∈ (D.raiseStep htd.le).filtration.realification.subgroup d → ∀ x,
          W.observable (z • x) =
            character ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
              W.observable x) ∧
        (∃ x, V.observable x ≠ 0) ∧ (∃ x, W.observable x ≠ 0) ∧
        Real.exp (-((raisedNiltestBudget p + C) ^ C)) ≤
          ‖𝔼 x ∈ B, multiplier x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨C, hC, hselect⟩ := exists_native_vertical_pair_preserving_characters_power
  refine ⟨C, hC, ?_⟩
  intro X U L _ _ m d t e w hw hd hwd _ _ _ _ _ _ _ _ _ M hM D htd ω Ψ D₀ mass K hdegree hD T hT hLip
    orbit R p hp hgeometry hbound hR hRcap B hB sample multiplier hmultiplier hcorr
  let Q := weightedTranslationTwistedNiltest w d hw hwd M hM ω hd Ψ D₀ mass K hdegree hD T hT hLip orbit
  have hQ : Q.ComplexityLE p :=
    weightedTranslationTwistedNiltest_complexity w d hw hwd M hM ω hd Ψ D₀ mass K hdegree hD T hT hLip orbit
      hgeometry hbound
  have hraise := le_raisedNiltestBudget p
  have hraisedcorr : Real.exp (-(raisedNiltestBudget p)) ≤
      ‖𝔼 x ∈ B, multiplier x * Q.eval (sample x) * (R.raiseStep htd.le).eval (sample x)‖ := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hraise)).trans
    simpa only [Q, weightedTranslationTwistedNiltest_eval,
      RationalFilteredNilmanifold.Niltest.raiseStep_eval] using hcorr
  obtain ⟨η, η', V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, _, hvertV, _,
      hpresV, _, hVne, hWne, hbias⟩ :=
    hselect (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le)
      Q (R.raiseStep htd.le) (raisedNiltestBudget p) (hp.trans hraise)
      (hQ.mono hraise) (R.raiseStep_complexity htd.le hp hR)
      (by change (1 : ℝ) ≤ 1; exact le_rfl) hRcap
      B hB sample multiplier hmultiplier hraisedcorr
  have hη : η (centralRationalElement w d hd 1) = 1 :=
    weightedTranslation_twisted_selected_frequency_one w d hw hd hwd M hM Ψ D₀ T η V.observable
      hvertV hVne hpresV
  exact ⟨η, V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, hη, hvertV,
    D.raiseStep_observable_top_vertical htd W.observable, hVne, hWne, hbias⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial CircleFourier
open scoped TensorProduct BigOperators NNReal

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeTripleObservableMetric
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitz_three_conjugates_of_bounds {X : Type*} [PseudoMetricSpace X]
    (f : Fin 3 → X → ℂ) {K : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j))
    (hbound : ∀ j x, ‖f j x‖ ≤ 1) :
    LipschitzWith (3 * K) (fun x => f 0 x * star (f 1 x) * star (f 2 x)) := by
  have h01 := lipschitz_mul_star_of_bounds (f 0) (f 1)
    (Bf := 1) (Bg := 1) (hf 0) (hf 1) (hbound 0) (hbound 1)
  have hb01 (x : X) : ‖f 0 x * star (f 1 x)‖ ≤ 1 := by
    simpa only [norm_mul, norm_star, mul_one] using
      mul_le_mul (hbound 0 x) (hbound 1 x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h := lipschitz_mul_star_of_bounds (fun x => f 0 x * star (f 1 x)) (f 2)
    (Bf := 1) (Bg := 1) h01 (hf 2) hb01 (hbound 2)
  convert h using 1
  ring

namespace RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound)

theorem tripleObservable_lipschitz (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
    (hEL : E.lattice = M.additiveTripleLattice i hi c hc)
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [T2Space (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hheight : ∀ j a k, rationalLogHeight
      (D.basis.repr (M.filtration.additiveTripleProjection i hi c hc j (E.basis a)) k) ≤ p)
    (ε : D.RealGroup) (u : Fin 3 → D.Space → ℂ) (K A : ℝ≥0)
    (hu : ∀ j x, ‖u j x‖ ≤ 1)
    (hLip : letI := D.metricSpace; ∀ j, LipschitzWith K (u j))
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) :
    letI := E.metricSpace
    LipschitzWith (3 * (K * (A * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩)))
      (M.tripleObservable i hi c hc E hEL ε u) := by
  let := E.metricSpace
  let := D.metricSpace
  apply lipschitz_three_conjugates_of_bounds
    (fun j x => u j (ε • M.tripleSpaceProjection i hi c hc E hEL j x))
  · intro j
    exact (hLip j).comp (hε.comp
      (M.tripleSpaceProjection_lipschitz i hi c hc E hEL j hp hD hE (hheight j)))
  · exact fun j x => hu j _

end RationalFilteredNilmanifold.MultidegreeStructure
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeDilationObservableMetric
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitz_signed_tensor_cross_product {X : Type*} [PseudoMetricSpace X]
    (m : ℤ) (f₀ : X → ℂ) (f : Fin m.natAbs → X → ℂ) {K : ℝ≥0}
    (hf₀ : LipschitzWith K f₀) (hf : ∀ j, LipschitzWith K (f j))
    (h₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hbound : ∀ j x, ‖f j x‖ ≤ 1) :
    LipschitzWith ((m.natAbs + 1 : ℝ≥0) * K)
      (fun x => f₀ x * star (signedTensorProduct m (fun j => f j x))) := by
  have h := lipschitz_mul_star_of_bounds f₀ (fun x => signedTensorProduct m (fun j => f j x))
    (Bf := 1) (Bg := 1) hf₀ (signedTensorProduct_lipschitz m f hf hbound)
    h₀ (fun x => signedTensorProduct_norm_le m _ (fun j => hbound j x))
  convert h using 1
  ring

namespace RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound)

theorem dilationObservable_lipschitz (q : ℚ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
    (hEL : E.lattice = M.dilationPairLattice q)
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    [T2Space (ℝ ⊗[ℚ] M.filtration.ordinary.dilationPairSubalgebra q)]
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hheight : ∀ j a k, rationalLogHeight
      (D.basis.repr (M.filtration.ordinary.dilationPairProjection q j (E.basis a)) k) ≤ p)
    (m : ℤ) (ε : D.RealGroup) (u₀ : D.Space → ℂ) (u : Fin m.natAbs → D.Space → ℂ)
    (K A : ℝ≥0) (h₀ : ∀ x, ‖u₀ x‖ ≤ 1) (hu : ∀ j x, ‖u j x‖ ≤ 1)
    (hLip₀ : letI := D.metricSpace; LipschitzWith K u₀)
    (hLip : letI := D.metricSpace; ∀ j, LipschitzWith K (u j))
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) :
    letI := E.metricSpace
    LipschitzWith ((m.natAbs + 1 : ℝ≥0) *
      (K * (A * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩)))
      (M.dilationObservable q E hEL m ε u₀ u) := by
  let := E.metricSpace
  let := D.metricSpace
  apply lipschitz_signed_tensor_cross_product m
    (fun x => u₀ (ε • M.dilationSpaceProjection q E hEL 0 x))
    (fun j x => u j (ε • M.dilationSpaceProjection q E hEL 1 x))
  · exact hLip₀.comp (hε.comp (M.dilationSpaceProjection_lipschitz q E hEL 0 hp hD hE (hheight 0)))
  · exact fun j => (hLip j).comp
      (hε.comp (M.dilationSpaceProjection_lipschitz q E hEL 1 hp hD hE (hheight 1)))
  · exact fun x => h₀ _
  · exact fun j x => hu j _

end RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolarizedVerticalNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct NNReal

variable {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p)

noncomputable def coordinateCombination (i j : I) (c : ℂ) (x : D.Space) : ℂ :=
  V.observable i x + c * V.observable j x

theorem coordinateCombination_norm (i j : I) (c : ℂ) (hc : ‖c‖ ≤ 1) (x : D.Space) :
    ‖V.coordinateCombination i j c x‖ ≤ 2 := by
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  have hmul := mul_le_mul hc (V.norm j x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  linarith [V.norm i x]

theorem coordinateCombination_lipschitz (i j : I) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    letI := D.metricSpace
    LipschitzWith (2 * V.lipBound) (V.coordinateCombination i j c) := by
  let := D.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hi := (V.lipschitz i).dist_le_mul x y
  have hj := (V.lipschitz j).dist_le_mul x y
  rw [dist_eq_norm] at hi hj ⊢
  have he : V.coordinateCombination i j c x - V.coordinateCombination i j c y =
      (V.observable i x - V.observable i y) + c * (V.observable j x - V.observable j y) := by
    unfold coordinateCombination
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  have hm := mul_le_mul_of_nonneg_right hc (norm_nonneg (V.observable j x - V.observable j y))
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  nlinarith

theorem coordinateCombination_vertical (i j : I) (c : ℂ) (z : D.RealGroup) (hz : z ∈ T)
    (x : D.Space) : V.coordinateCombination i j c (z • x) =
      CircleFourier.character ((realifyFunctional V.frequency z.coord : ℝ) : CircleFourier.Circle) *
        V.coordinateCombination i j c x := by
  unfold coordinateCombination
  rw [V.vertical i z hz, V.vertical j z hz]
  ring

noncomputable def combinationNiltest {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (i j : I) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    D.Niltest w where
  orbit := g
  observable := V.coordinateCombination i j c
  normBound := 2
  lipBound := 2 * V.lipBound
  norm_le := V.coordinateCombination_norm i j c hc
  lipschitz := V.coordinateCombination_lipschitz i j c hc

theorem combinationNiltest_complexity {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (i j : I) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    (V.combinationNiltest g i j c hc).ComplexityLE (p + 5) := by
  refine ⟨hD.mono D (by linarith), ?_⟩
  change Real.log (2 + (2 : ℝ) + ((2 * V.lipBound : ℝ≥0) : ℝ)) ≤ p + 5
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  calc
    _ ≤ 6 * Real.exp p := by nlinarith [V.lip_bound, Real.one_le_exp hp]
    _ ≤ Real.exp 5 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (5 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankPairs
namespace OAI

section

namespace Erdos3

namespace NativeDegreeRankFamily

variable {s r : ℕ} {G : Type*} [AddGroup G] {p : ℝ} (W : NativeDegreeRankFamily s r G p)

noncomputable def shiftPair (i : Fin W.outputDim) (a h : G) (δ n : ℤ) : ℂ :=
  star (W.eval i h n) * W.eval i (h - a) (n + δ)

theorem shiftPair_norm (i : Fin W.outputDim) (a h : G) (δ n : ℤ) :
    ‖W.shiftPair i a h δ n‖ ≤ 1 := by
  rw [shiftPair, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval i h n)).trans
    (W.norm_eval i (h - a) (n + δ))

theorem shiftPair_mul_star (i : Fin W.outputDim) (a h k : G) (δ n : ℤ) :
    W.shiftPair i a h δ n * star (W.shiftPair i a k δ n) =
      fourPointProduct (W.eval i h) (W.eval i (h - a))
        (W.eval i k) (W.eval i (k - a)) δ n := by
  simp only [shiftPair, fourPointProduct, star_mul, star_star]
  ring

theorem quadruple_common_anchor (i : Fin W.outputDim) (a h k : G) (δ n : ℤ) (w v : ℂ) :
    fourPointProduct (W.eval i h) (W.eval i (h - a))
        (W.eval i k) (W.eval i (k - a)) δ n * w * v =
      (w * star (W.shiftPair i a k δ n)) * (W.shiftPair i a h δ n * v) := by
  rw [← W.shiftPair_mul_star]
  ring

end NativeDegreeRankFamily

namespace NativeMultilinearIntervalFamily

end NativeMultilinearIntervalFamily

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalDifference
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators NNReal

variable {L I J : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] [Fintype J]
  {s d : ℕ} [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p) (U : D.UnitVerticalObservable T J p)

noncomputable def differenceObservable (a : I × J) (x : D.Space) : ℂ :=
  V.observable a.1 x * star (U.observable a.2 x)

theorem differenceObservable_unit (x : D.Space) :
    ∑ a, ‖V.differenceObservable U a x‖ ^ 2 = 1 := by
  simp only [differenceObservable, norm_mul, norm_star, mul_pow, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, U.unit, mul_one, V.unit]

theorem differenceObservable_norm (a : I × J) (x : D.Space) :
    ‖V.differenceObservable U a x‖ ≤ 1 := by
  simpa only [differenceObservable, norm_mul, norm_star, mul_one] using
    mul_le_mul (V.norm a.1 x) (U.norm a.2 x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem differenceObservable_lipschitz (a : I × J) :
    letI := D.metricSpace
    LipschitzWith (V.lipBound + U.lipBound) (V.differenceObservable U a) := by
  let := D.metricSpace
  exact (lipschitz_mul_star_of_bounds (V.observable a.1) (U.observable a.2)
    (Bf := 1) (Bg := 1) (V.lipschitz a.1) (U.lipschitz a.2)
    (V.norm a.1) (U.norm a.2)).weaken (by simp only [one_mul]; exact le_of_eq (add_comm _ _))

variable {r : ℕ} (R : D.DegreeRankStructure r)
  (V : D.UnitVerticalObservable (R.realSubgroup s r) I p)
  (U : D.UnitVerticalObservable (R.realSubgroup s r) J p)
  (hfreq : ∀ x ∈ R.filtration.layer s r, V.frequency x = U.frequency x)

include hfreq in
theorem differenceObservable_rank_invariant (a : I × J) (z : D.RealGroup)
    (hz : z ∈ R.realSubgroup s r) (x : D.Space) :
    V.differenceObservable U a (z • x) = V.differenceObservable U a x := by
  have heq := realifyFunctional_eq_on_submodule (R.filtration.layer s r)
    V.frequency U.frequency hfreq z.coord hz
  let c := CircleFourier.character
    ((realifyFunctional U.frequency z.coord : ℝ) : CircleFourier.Circle)
  have hc : c * star c = 1 := by
    dsimp only [c]
    rw [← CircleFourier.character_neg, ← CircleFourier.character_add,
      add_neg_cancel, CircleFourier.character_zero]
  unfold differenceObservable
  rw [V.vertical a.1 z hz, U.vertical a.2 z hz, heq, star_mul]
  change (c * V.observable a.1 x) * (star (U.observable a.2 x) * star c) = _
  calc
    _ = (c * star c) * (V.observable a.1 x * star (U.observable a.2 x)) := by ring
    _ = _ := by rw [hc, one_mul]

noncomputable def rankDifference :
    D.UnitVerticalObservable (R.realSubgroup s r) (I × J) (p + 2) where
  observable := V.differenceObservable U
  unit := V.differenceObservable_unit U
  norm := V.differenceObservable_norm U
  lipBound := V.lipBound + U.lipBound
  lip_bound := by
    change (V.lipBound : ℝ) + U.lipBound ≤ Real.exp (p + 2)
    calc
      _ ≤ 2 * Real.exp p := by linarith [V.lip_bound, U.lip_bound]
      _ ≤ Real.exp 2 * Real.exp p := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  lipschitz := V.differenceObservable_lipschitz U
  frequency := 0
  height i := by
    have hp := (rationalLogHeight_nonneg (V.frequency (D.basis i))).trans (V.height i)
    simpa [rationalLogHeight] using (show (0 : ℝ) ≤ p + 2 by linarith)
  vertical a z hz x := by
    simpa only [realifyFunctional_zero, AddCircle.coe_zero,
      CircleFourier.character_zero, one_mul] using
      differenceObservable_rank_invariant R V U hfreq a z hz x
  integral _ _ _ := ⟨0, by simp only [realifyFunctional_zero, Int.cast_zero]⟩

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedGeometricInputBudget
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory

def allocatedUniformChartLog {A : Type*} [Semiring A] (p : A) : A := 20 * (p + 1) ^ 3

theorem exists_uniform_projected_chart {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)]
    {p : ℝ} (hdim : (Fintype.card J : ℝ) ≤ p) :
    ∃ b : Basis (Fin (finrank ℝ Wᗮ)) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∀ z, ‖normalizedOrthogonalChart W b z‖ ≤ Real.exp (allocatedUniformChartLog p) * ‖z‖) ∧
      (∀ z, ‖(normalizedOrthogonalChart W b).symm z‖ ≤ Real.exp (allocatedUniformChartLog p) * ‖z‖) ∧
      0 ≤ mixedDensityCovolumeRatio W b ∧
      mixedDensityCovolumeRatio W b ≤ Real.exp (allocatedUniformChartLog p) := by
  have hn : finrank ℝ Wᗮ ≤ Fintype.card J := by
    simpa only [finrank_euclideanSpace] using Wᗮ.finrank_le
  have hnp : (finrank ℝ Wᗮ : ℝ) ≤ p := (Nat.cast_le.mpr hn).trans hdim
  have hlog : 20 * ((finrank ℝ Wᗮ : ℝ) + 1) ^ 3 ≤ allocatedUniformChartLog p := by
    unfold allocatedUniformChartLog
    gcongr
  have he := Real.exp_le_exp.mpr hlog
  obtain ⟨b, hb, _, hf, hi, _, hv⟩ := exists_quantitative_projected_chart W
  exact ⟨b, hb, fun z => (hf z).trans (mul_le_mul_of_nonneg_right he (norm_nonneg z)),
    fun z => (hi z).trans (mul_le_mul_of_nonneg_right he (norm_nonneg z)),
    (mixedDensityCovolumeRatio_pos W b).le, hv.trans he⟩

namespace VectorPolynomial

theorem exists_allocated_uniform_charts {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {p : ℝ} (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p) :
    ∃ b : ∀ j, Basis (Fin (finrank ℝ (euclideanSubspace (U j))ᗮ)) ℝ (euclideanSubspace (U j))ᗮ,
      (∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))) ∧
      (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤
        Real.exp (allocatedUniformChartLog p) * ‖z‖) ∧
      (∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog p) * ‖z‖) ∧
      (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp (allocatedUniformChartLog p)) := by
  choose b hb hf hi hv0 hv using (fun j => exists_uniform_projected_chart (euclideanSubspace (U j)) (hJ j))
  exact ⟨b, hb, hf, hi, fun j => ⟨hv0 j, hv j⟩⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {p c e E : ℝ}
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (M₀ : ℕ)
local notation "period" => kernelPeriodCandidate (m + 1)
local notation "L" => scalarSourceTransitionBound


local notation "chartCap" => (NNReal.mk (Real.exp c) (Real.exp_nonneg c))
local notation "geometryQ" => Real.toNNReal (8 * (allocatedComparisonDimension m p + 1))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {p c e E : ℝ}
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (M₀ : ℕ)
local notation "period" => kernelPeriodCandidate (m + 1)
local notation "L" => scalarSourceTransitionBound


local notation "chartCap" => (NNReal.mk (Real.exp c) (Real.exp_nonneg c))
local notation "geometryQ" => Real.toNNReal (8 * (allocatedComparisonDimension m p + 1))

variable {K : ℕ}





end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoefficientIntegerFloorRemainder
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def coefficientIntegerFloorPolynomial
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (j : Fin m) (i : J j) : MvPolynomial K ℤ :=
  integerMonomialArrayPolynomial Subtype.val
    (fun d : BoundedCoefficientExponent K (j.val + 1) =>
      ⌊(c ⟨j, d⟩).val i - mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) (a j) d i⌋)

theorem coefficientIntegerFloorPolynomial_degree
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (j : Fin m) (i : J j) :
    (coefficientIntegerFloorPolynomial U b o a c j i).totalDegree ≤ j.val + 1 :=
  integerMonomialArrayPolynomial_degree Subtype.val _ (fun d => d.property)

theorem canonicalCoefficientSample_floor_coefficient_remainder
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o a = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) (i : J j) :
    (c ⟨j, d⟩).val i - mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) (a j) d i =
      (⌊(c ⟨j, d⟩).val i - mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) (a j) d i⌋ : ℤ) := by
  obtain ⟨z, hz⟩ := canonicalCoefficientSample_integer_remainder U b hb o a c hc j d i
  rw [mixedLiftCoefficient_eq, hz, Int.floor_intCast]

theorem canonicalCoefficientSample_floor_polynomial_remainder
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o a = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (i : J j) :
    coefficientRowPolynomial U c j i =
      mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (a j) i +
        MvPolynomial.map (Int.castRingHom ℝ) (coefficientIntegerFloorPolynomial U b o a c j i) ∧
      (coefficientIntegerFloorPolynomial U b o a c j i).totalDegree ≤ j.val + 1 := by
  refine ⟨?_, coefficientIntegerFloorPolynomial_degree U b o a c j i⟩
  rw [coefficientIntegerFloorPolynomial, integerMonomialArrayPolynomial_map]
  change (∑ d : BoundedCoefficientExponent K (j.val + 1), MvPolynomial.monomial d.val ((c ⟨j,d⟩).val i)) = _
  unfold mixedLiftPolynomial monomialArrayPolynomial
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [← map_add]
  apply congrArg (MvPolynomial.monomial d.val)
  have hd := canonicalCoefficientSample_floor_coefficient_remainder U b hb o a c hc j d i
  linarith

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RecoveredLatticeMatrixInvariance
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I E : Type*} [Fintype D] [Fintype I] [Fintype E] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis E ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

noncomputable def recoveredIntegerTransverse : (D → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun β i := standardLatticeCoordinates W bW b hb β (Sum.inl i)
  map_add' β γ := by ext i; simp only [map_add, Pi.add_apply]
  map_smul' q β := by ext i; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

noncomputable def recoveredIntegerDeck : (D → ℤ) →ₗ[ℤ] (E → ℤ) where
  toFun β i := standardLatticeCoordinates W bW b hb β (Sum.inr i)
  map_add' β γ := by ext i; simp only [map_add, Pi.add_apply]
  map_smul' q β := by ext i; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

variable (o : OrthonormalBasis I ℝ W)

noncomputable def recoveredMixedCoordinates (y : EuclideanSpace ℝ D) (β : D → ℤ) :
    (I → ℝ) × (Fin n → ℤ) :=
  ((mixedRealCoordinates W b o y).1, recoveredIntegerTransverse W bW b hb β)

end Erdos3

end

section

namespace Erdos3

open Module Submodule

variable {m d a : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

def layerIntegerRestriction (e : Fin d ≃ Sigma J) (j : Fin m) :
    (Fin d → ℤ) →ₗ[ℤ] (J j → ℤ) where
  toFun β i := β (e.symm ⟨j, i⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def recoveredLayeredIntegerLift (e : Fin d ≃ Sigma J)
    (M : Fin d → Fin a → ℤ) (β : Sigma J → ℤ) (k : Fin a → ℤ) : Sigma J → ℤ :=
  fun i => recoveredIntegerLift M (fun i => β (e i)) k (e.symm i)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationProjectedAxisBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial

noncomputable def preparationHeight (p : ℝ) (depth : ℕ) : ℕ :=
  ⌊Real.exp ((p + 2) ^ budgetDepthExponent 38 depth)⌋₊

theorem preparationExponent_pos (depth : ℕ) : 1 ≤ budgetDepthExponent 38 depth := by
  induction depth with
  | zero => rfl
  | succ d ih => simp only [budgetDepthExponent]; omega

theorem preparationExponent_mono : Monotone (budgetDepthExponent 38) := by
  apply monotone_nat_of_le_succ
  intro d
  simp only [budgetDepthExponent]
  omega

theorem preparationHeight_pos {p : ℝ} (hp : 0 ≤ p) (depth : ℕ) :
    1 ≤ preparationHeight p depth := by
  apply Nat.le_floor
  norm_cast
  exact Real.one_le_exp (by positivity)

theorem preparationHeight_le_exp (p : ℝ) (depth : ℕ) :
    (preparationHeight p depth : ℝ) ≤ Real.exp ((p + 2) ^ budgetDepthExponent 38 depth) :=
  Nat.floor_le (Real.exp_nonneg _)

theorem preparationHeight_mono {p : ℝ} (hp : 0 ≤ p) : Monotone (preparationHeight p) := by
  intro d e hde
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  exact pow_le_pow_right₀ (by linarith) (preparationExponent_mono hde)

namespace RankPreparationFamily

def PreparedHeights {I J : Type} {s : ℕ} (L : RankPreparationFamily I J s) (p : ℝ) (R : ℕ) : Prop :=
  ∀ i, (L i).Valid (i.val + 1) (preparationHeight p (s - 1 - i.val)) R

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

variable {I J : Type} [Fintype J] [DecidableEq J] {j : ℕ}

noncomputable def initial (p : VectorPolynomial I ℝ (J → ℝ)) : RankPreparationFamily I J (j + 1) :=
  fun i => if i = Fin.last j then RankPreparationLayer.initial p else RankPreparationLayer.empty

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3

open scoped BigOperators
open VectorPolynomial

namespace RankPreparationLayer

end RankPreparationLayer

namespace RankPreparationFamily

variable {I J : Type} {m q : ℕ}

noncomputable def pad (L : RankPreparationFamily I J m) (q : ℕ) :
    RankPreparationFamily I J q := fun j =>
  if hj : j.val < m then L ⟨j.val, hj⟩ else RankPreparationLayer.empty

@[simp] theorem pad_apply_lt (L : RankPreparationFamily I J m) (j : Fin q)
    (hj : j.val < m) : L.pad q j = L ⟨j.val, hj⟩ := by
  simp only [pad, dif_pos hj]

@[simp] theorem pad_apply_ge (L : RankPreparationFamily I J m) (j : Fin q)
    (hj : m ≤ j.val) : L.pad q j = RankPreparationLayer.empty := by
  simp only [pad, dif_neg (by omega : ¬j.val < m)]

@[simp] theorem pad_apply_castLE (L : RankPreparationFamily I J m) (hmq : m ≤ q)
    (j : Fin m) : L.pad q (j.castLE hmq) = L j := by
  simp only [pad, Fin.val_castLE, dif_pos j.isLt]

theorem PreparedHeights.pad {L : RankPreparationFamily I J m} {p : ℝ} {R : ℕ}
    (hL : L.PreparedHeights p R) (hmq : m ≤ q) (hp : 0 ≤ p) :
    (L.pad q).PreparedHeights p R := by
  intro j
  by_cases hj : j.val < m
  · rw [pad_apply_lt L j hj]
    exact (hL ⟨j.val, hj⟩).mono_height
      (preparationHeight_mono hp (by change m - 1 - j.val ≤ q - 1 - j.val; omega))
  · rw [pad_apply_ge L j (by omega)]
    exact RankPreparationLayer.empty_valid _ _ _

theorem pad_coefficients_mem (L : RankPreparationFamily I J m)
    (hL : ∀ j α, coefficients (L j).poly α ∈ (L j).space) :
    ∀ j α, coefficients (L.pad q j).poly α ∈ (L.pad q j).space := by
  intro j
  by_cases hj : j.val < m
  · rw [pad_apply_lt L j hj]
    exact hL ⟨j.val, hj⟩
  · rw [pad_apply_ge L j (by omega)]
    exact (RankPreparationLayer.empty_valid 0 0 0).2.1

theorem Sized.pad {L : RankPreparationFamily I J m} {D t : ℕ}
    (hL : L.Sized D t) (hmq : m ≤ q) : (L.pad q).Sized D t := by
  intro j
  by_cases hj : j.val < m
  · rw [pad_apply_lt L j hj]
    obtain ⟨hc, hb, hr⟩ := hL ⟨j.val, hj⟩
    exact ⟨hc.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_right (by omega)
      (by change m - 1 - j.val ≤ q - 1 - j.val; omega))), hb, hr⟩
  · rw [pad_apply_ge L j (by omega)]
    change Fintype.card PEmpty ≤ _ ∧ Fintype.card PEmpty ≤ _ ∧ Fintype.card PEmpty ≤ _
    simp

theorem pad_sum {V : Type*} [AddCommMonoid V]
    (L : RankPreparationFamily I J m) (hmq : m ≤ q)
    (f : RankPreparationLayer I J → V) (hf : f RankPreparationLayer.empty = 0) :
    (∑ j, f (L.pad q j)) = ∑ j, f (L j) := by
  symm
  apply Fintype.sum_of_injective (Fin.castLE hmq)
    (fun i j hij => Fin.ext (congrArg (fun k : Fin q => k.val) hij))
  · intro j hj
    have hge : m ≤ j.val := by
      by_contra hnot
      have hlt : j.val < m := by omega
      exact hj ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩
    rw [pad_apply_ge L j hge, hf]
  · intro j
    rw [pad_apply_castLE]

@[simp] theorem pad_value [DecidableEq J] (L : RankPreparationFamily I J m)
    (hmq : m ≤ q) (x : I → ℝ) : (L.pad q).value x = L.value x :=
  pad_sum L hmq (fun layer => layer.value x) (RankPreparationLayer.empty_value x)

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3

open Module Submodule VectorPolynomial
open scoped BigOperators

namespace RankPreparationLayer

variable {I J : Type} (L : RankPreparationLayer I J)

noncomputable def euclideanEquiv : euclideanSubspace L.space ≃ₗ[ℝ] L.space :=
  (euclideanSubspaceArrayEquiv L.space).toLinearEquiv.trans
    (LinearEquiv.piUnique ℝ (fun _ : Unit => L.space))

theorem euclidean_finrank : finrank ℝ (euclideanSubspace L.space) = L.rank :=
  L.euclideanEquiv.finrank_eq

theorem rank_add_orthogonal_finrank :
    L.rank + finrank ℝ (euclideanSubspace L.space)ᗮ = Fintype.card L.Coord := by
  rw [← L.euclidean_finrank, Submodule.finrank_add_finrank_orthogonal, finrank_euclideanSpace]

theorem lattice_full {d H R : ℕ} (hL : L.Valid d H R) (hH : 1 ≤ H) (hR : 1 ≤ R) :
    IsZLattice ℝ (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space)) :=
  jointRationalSpaceLattice_full L.basis L.rows hH hR hL.2.2.1 hL.2.2.2

end RankPreparationLayer

namespace RankPreparationFamily

variable {I J : Type} {s : ℕ} (L : RankPreparationFamily I J s)

theorem PreparedHeights.lattice_full {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (i : Fin s) :
    IsZLattice ℝ (latticeSection (standardEuclideanLattice (L i).Coord)
      (euclideanSubspace (L i).space)) :=
  (L i).lattice_full (hL i) (preparationHeight_pos hp _) hR

theorem PreparedHeights.coefficientTorus_compact {K : Type*} [Fintype K]
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R) (hp : 0 ≤ p) (hR : 1 ≤ R) :
    CompactSpace (CoefficientTorus (K := K) (fun i => (L i).space)) := by
  let := fun i => hL.lattice_full L hp hR i
  exact coefficientTorus_compact_of_lattice (fun i => (L i).space)

theorem PreparedHeights.exists_uniform_charts {p c : ℝ} {R : ℕ}
    (hL : L.PreparedHeights p R) (hp : 0 ≤ p) (hR : 1 ≤ R)
    (hC : ∀ i, (Fintype.card (L i).Coord : ℝ) ≤ c) :
    ∃ b : ∀ i, Basis (Fin (finrank ℝ (euclideanSubspace (L i).space)ᗮ)) ℝ
        (euclideanSubspace (L i).space)ᗮ,
      (∀ i, span ℤ (Set.range (b i)) = projectedIntegerLattice (euclideanSubspace (L i).space)) ∧
      (∀ i z, ‖normalizedOrthogonalChart (euclideanSubspace (L i).space) (b i) z‖ ≤
        Real.exp (allocatedUniformChartLog c) * ‖z‖) ∧
      (∀ i z, ‖(normalizedOrthogonalChart (euclideanSubspace (L i).space) (b i)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog c) * ‖z‖) ∧
      (∀ i, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L i).space) (b i) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (L i).space) (b i) ≤
          Real.exp (allocatedUniformChartLog c)) := by
  let := fun i => hL.lattice_full L hp hR i
  exact exists_allocated_uniform_charts (fun i => (L i).space) hC

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationLayer

open Module Submodule

variable {X J E : Type} [Fintype E] (L : RankPreparationLayer X J)
variable [IsZLattice ℝ
  (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))]

noncomputable def integralCoordinateBasis
    (bW : Basis E ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))) :
    Basis E ℝ L.space :=
  (bW.ofZLatticeBasis ℝ _).map L.euclideanEquiv

theorem integralCoordinateBasis_card
    (bW : Basis E ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))) :
    Fintype.card E = L.rank :=
  (Module.finrank_eq_card_basis (L.integralCoordinateBasis bW)).symm

omit [Fintype E] in
theorem integralCoordinateBasis_integer
    (bW : Basis E ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space)))
    (i : L.Coord) (e : E) :
    ∃ z : ℤ, (L.integralCoordinateBasis bW e).val i = (z : ℝ) := by
  have h := (mem_standardEuclideanLattice L.Coord (bW e).val.val).mp (bW e).property i
  obtain ⟨z, hz⟩ := h
  refine ⟨z, ?_⟩
  change ((bW.ofZLatticeBasis ℝ _) e).val i = (z : ℝ)
  rw [Basis.ofZLatticeBasis_apply]
  exact hz.symm

noncomputable def integralCoordinateMatrix
    (bW : Basis E ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))) :
    L.Coord → E → ℤ :=
  fun i e => Classical.choose (L.integralCoordinateBasis_integer bW i e)

end Erdos3.RankPreparationLayer

end

section

namespace Erdos3.RankPreparationLayer

open Module Submodule VectorPolynomial BohrLattice.MinkowskiSecondBox

variable {X J : Type} (L : RankPreparationLayer X J)

noncomputable def shortIntegralBasisNormBound (H R : ℕ) : ℝ :=
  (L.rank : ℝ) * L.rank.factorial * minkowskiSecondConstant L.rank *
    ((Fintype.card L.Coord : ℝ) *
      (jointSpaceGeneratorHeight (Fintype.card L.Coord) (Fintype.card L.Column)
        (Fintype.card L.Row) H R : ℝ) ^ (Fintype.card L.Coord * Fintype.card L.Coord))

theorem exists_short_integral_basis {d H R : ℕ}
    (hL : L.Valid d H R) (hH : 1 ≤ H) (hR : 1 ≤ R) :
    ∃ bW : Basis (Fin L.rank) ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space)),
      ∀ a, ‖(bW a).val‖ ≤ L.shortIntegralBasisNormBound H R := by
  let := L.lattice_full hL hH hR
  obtain ⟨P, hP, hspace⟩ := exists_jointRationalSpace_generators
    L.basis L.rows hH hR hL.2.2.1 hL.2.2.2
  obtain ⟨v, hvspan, hvmem, hvnorm⟩ :=
    exists_bounded_integral_span_of_rational_range P L.space hspace hP
  let o : OrthonormalBasis (Fin L.rank) ℝ (euclideanSubspace L.space) :=
    (stdOrthonormalBasis ℝ (euclideanSubspace L.space)).reindex
      (finCongr L.euclidean_finrank)
  obtain ⟨b, hbspan, _hbprod, hbnorm⟩ := exists_short_euclidean_lattice_basis
    (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))
    o v hvspan hvmem hvnorm
  refine ⟨integerBasisOfReal _ b hbspan, ?_⟩
  intro a
  rw [integerBasisOfReal_apply]
  exact hbnorm a

end Erdos3.RankPreparationLayer

end

section

namespace Erdos3

open Module Submodule

theorem basisAxisScale_jointRationalSpace_le_exp
    {J C V K : Type*} [Fintype J] [Fintype C] [Fintype V]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) {H R : ℕ}
    (hH : 1 ≤ H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    (hA : ∀ v j, RationalHeightLE (A v j) R)
    (b : Basis K ℝ (euclideanSubspace (VectorPolynomial.jointRationalSpace B A))ᗮ)
    (hb : span ℤ (Set.range b) =
      projectedIntegerLattice (euclideanSubspace (VectorPolynomial.jointRationalSpace B A)))
    {p : ℝ} (hp : 0 ≤ p)
    (hJ : (Fintype.card J : ℝ) ≤ p) (hC : (Fintype.card C : ℝ) ≤ p)
    (hV : (Fintype.card V : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hRp : (R : ℝ) ≤ Real.exp p)
    (i : K) :
    (basisAxisScale b i : ℝ) ≤ Real.exp ((p+2)^28) := by
  obtain ⟨Q, hQ, hQker⟩ :=
    VectorPolynomial.exists_jointRationalSpace_defining_matrix B A hH hB hA
  have hscale := basisAxisScale_le_of_rational_kernel Q _ hQker hQ b hb i
  have hrow : (Fintype.card (J ⊕ V) : ℝ) ≤ 2*p := by
    rw [Fintype.card_sum, Nat.cast_add]
    linarith only [hJ, hV]
  have hcol : (Fintype.card J : ℝ) ≤ 2*p := by linarith only [hJ, hp]
  have hheight :
      ((max (imageDefiningHeight (Fintype.card C) (Fintype.card J) H) R : ℕ) : ℝ) ≤
        Real.exp ((2*p+2)^10) := by
    apply (jointSpaceDefiningHeight_le_exp _ _ H R hp hJ hC hHp hRp).trans
    apply Real.exp_le_exp.mpr
    exact pow_le_pow_left₀ (show 0 ≤ p+2 by positivity) (show p+2 ≤ 2*p+2 by linarith only [hp]) 10
  have hceil := rationalKernelSeparationConstant_ceil_le_exp_power Q
    (show 0 ≤ 2*p by positivity) 10 (by decide) hrow hcol hheight hQ
  have hpower : (2*p+2)^14 ≤ (p+2)^28 := by
    calc
      _ ≤ ((p+2)^2)^14 := pow_le_pow_left₀ (show 0 ≤ 2*p+2 by positivity)
        (show 2*p+2 ≤ (p+2)^2 by nlinarith only [hp, sq_nonneg p]) 14
      _ = _ := by rw [← pow_mul]
  calc
    _ ≤ (⌈rationalKernelAxisBound Q
        (max (imageDefiningHeight (Fintype.card C) (Fintype.card J) H) R)⌉₊ : ℝ) :=
      Nat.cast_le.mpr hscale
    _ ≤ Real.exp ((2*p+2)^14) := hceil
    _ ≤ _ := Real.exp_le_exp.mpr hpower

namespace RankPreparationLayer

theorem basisAxisScale_le_exp {X J : Type} (L : RankPreparationLayer X J)
    {degree H R : ℕ} (hL : L.Valid degree H R) (hH : 1 ≤ H)
    {K : Type*} (b : Basis K ℝ (euclideanSubspace L.space)ᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice (euclideanSubspace L.space))
    {p : ℝ} (hp : 0 ≤ p)
    (hCoord : (Fintype.card L.Coord : ℝ) ≤ p)
    (hColumn : (Fintype.card L.Column : ℝ) ≤ p)
    (hRow : (Fintype.card L.Row : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hRp : (R : ℝ) ≤ Real.exp p)
    (i : K) :
    (basisAxisScale b i : ℝ) ≤ Real.exp ((p+2)^28) :=
  basisAxisScale_jointRationalSpace_le_exp L.basis L.rows hH hL.2.2.1 hL.2.2.2
    b hb hp hCoord hColumn hRow hHp hRp i

end RankPreparationLayer

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtGaussianMean
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def latticeGaussianMean (Λ : Submodule ℤ E) (t : ℝ) (k : ℕ) (α : E) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), normalizedLatticeGaussian Λ t ((n : ℝ) ^ k • α)) /
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedJointMaskedDensityComparison
namespace OAI

section

namespace Erdos3
open MeasureTheory

noncomputable def dominatedDensityRatio {X : Type*} (D A : X → ℝ) (x : X) : ℂ :=
  (A x / D x : ℝ)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

noncomputable def allocatedMaskedTiltedConstant (m : ℕ) : ℕ :=
  Classical.choose (exists_affine_coefficient_cover_tilted_family_comparison.{0, 0, 0, 0} m)

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

end Erdos3.VectorPolynomial

end

end OAI

end


