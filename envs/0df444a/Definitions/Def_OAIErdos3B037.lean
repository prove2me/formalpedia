-- Prove2me | Definitions.Def_OAIErdos3B037
-- name    : OAIErdos3B037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T01:21:23.466689+00:00
-- url     : https://prove2.me/theorems/94798ca5-e1ef-4881-b716-295d851d3728
-- title:
--   OpenAI Erdős-3 split, definitions bundle 38 of 132
-- statement:
--   Definitions bundle 38 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B036`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 38 available.
--
--   Modules: `OAI.Erdos3.MultidegreeLieFiltration.exists_realPositivePolynomial_component`, `OAI.Erdos3.MultidegreeLieFiltration.exists_realPositivePolynomial_orbit`, `OAI.Erdos3.MultidegreeLieFiltration.exists_realPositivePolynomial_preimage_layer`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDownsetOrbit`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialDownsetOrbit_eval`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialMonomial`, `OAI.Erdos3.MultidegreeLieFiltration.positivePolynomialMonomial_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialEquiv`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialEquiv_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialMap_monomial`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialMonomial_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialOrbitTransport`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialOrbitTransport_eval`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialOrbitTransport_zero`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialTensor_mem_layer`, `OAI.Erdos3.MultidegreeLieFiltration.realPositivePolynomialTensor_surjective`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.PositivePolynomialBasisIndex`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.PositivePolynomialDownsetIndex`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.PositivePolynomialGridStable`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_canonical_positivePolynomial_splitting`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_controlled_positivePolynomial_model`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_positivePolynomial_factor_approximation`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_positivePolynomial_model_uniform`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_positivePolynomial_observable_pullback`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_positivePolynomial_product_reconstruction`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_positivePolynomial_source_reconstruction`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_positivePolynomial_stable_grid`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_positivePolynomial_vector_factor_approximation`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_uniform_positivePolynomial_splitting`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positiveCoefficientBasis_card_le`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialBasis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialBasisIndex_card_le`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialBasis_evaluation_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialBasis_structure_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialDownsetBasis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialDownsetBasis_structure`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialDownsetFinBasis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialDownsetFinBasis_degree_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialDownsetFinBasis_multidegree_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialDownsetIndex_card_le`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialDownsetLattice`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialDownsetLattice_coordinates`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialDownsetModel`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialDownsetModelMultidegree`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialDownsetModel_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialDownset_projection_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialEvaluationCosetMap`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialEvaluationCosetMap_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialEvaluationCosetMap_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialEvaluationDenominator`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialEvaluationDenominator_le_exp`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialEvaluationDenominator_pos`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialEvaluation_metric_bound`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialFactorNiltest`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialFactorNiltest_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialFactorNiltest_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialFactorNiltest_unit_interval`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialFinBasis`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialFinBasis_degree_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialFinBasis_evaluation_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialFinBasis_multidegree_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialFinBasis_structure_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialLattice`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialLattice_coordinates`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialLattice_maps`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialModel`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialModelMultidegree`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialModel_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialProductProjection_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialProductProjection_orbit`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialQuotientProductModel`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialQuotientProductModel_geometry`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialQuotientProductModel_lattice_cover`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialQuotientProductModel_map_height`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomialQuotientProductModel_map_injective`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.positivePolynomial_vector_error_of_lift`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.onNativeCover`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.onNativeCover_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.onNativeCover_evalCyclic`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.onNativeCover_lipBound`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.onNativeCover_log`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.onNativeCover_normBound`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.onSublattice`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.onSublattice_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.onSublattice_unit_interval`, `OAI.Erdos3.RationalFilteredNilmanifold.splitCoverProjection`, `OAI.Erdos3.RationalFilteredNilmanifold.splitCoverProjection_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.splitCoverProjection_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.splitCoverProjection_pullback`, `OAI.Erdos3.RationalFilteredNilmanifold.sublatticeProjection`, `OAI.Erdos3.RationalFilteredNilmanifold.sublatticeProjection_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.sublatticeProjection_mk`, `OAI.Erdos3.RationalFilteredNilmanifold.sublattice_pullback_lipschitz`, `OAI.Erdos3.exists_common_height_bounded_subspace_family`, `OAI.Erdos3.exists_formal_geometry_uniform_budget`, `OAI.Erdos3.exists_positivePolynomialModel_budget`, `OAI.Erdos3.formalBracketMatrixHeight_le_exp`, `OAI.Erdos3.formalCurrentMatrixHeight_le_exp`, `OAI.Erdos3.formalGeometryHeight_ge_input`, `OAI.Erdos3.formalGeometryHeight_le_exp`, `OAI.Erdos3.gaussian_translate_bound`, `OAI.Erdos3.heightBoundedLieSubalgebras_ncard_exp_bound`, `OAI.Erdos3.heightBoundedSubspaces_ncard_exp_bound`, `OAI.Erdos3.hyperplaneRetraction`, `OAI.Erdos3.hyperplaneRetraction_coe`, `OAI.Erdos3.hyperplaneRetraction_mem`, `OAI.Erdos3.hyperplaneRetraction_on_kernel`, `OAI.Erdos3.integralLatticeCoordinate`, `OAI.Erdos3.integralLatticeCoordinate_cast`, `OAI.Erdos3.integralLatticeValue`, `OAI.Erdos3.integralLatticeValue_cast`, `OAI.Erdos3.latticeGaussianMass`, `OAI.Erdos3.latticeGaussianMass_add_lattice`, `OAI.Erdos3.latticeHyperplane`, `OAI.Erdos3.latticeHyperplaneBasis`, `OAI.Erdos3.latticeHyperplaneBasis_inl`, `OAI.Erdos3.latticeHyperplaneBasis_inr`, `OAI.Erdos3.latticeHyperplaneInclusion`, `OAI.Erdos3.latticeHyperplaneRetraction`, `OAI.Erdos3.latticeHyperplaneRetraction_coe`, `OAI.Erdos3.latticeHyperplaneSplit`, `OAI.Erdos3.latticeHyperplaneSplit_symm_coe`, `OAI.Erdos3.latticeHyperplane_discrete`, `OAI.Erdos3.mem_latticeHyperplane`, `OAI.Erdos3.positivePolynomialDenominatorBudget`, `OAI.Erdos3.positivePolynomialDenominatorBudget_le_model`, `OAI.Erdos3.positivePolynomialInputBudget`, `OAI.Erdos3.positivePolynomialInputBudget_le_denominator`, `OAI.Erdos3.positivePolynomialInputBudget_nonneg`, `OAI.Erdos3.positivePolynomialModelBudget`, `OAI.Erdos3.rationalConstraint_base_count_le_exp`, `OAI.Erdos3.rationalConstraint_list_count_le_exp`, `OAI.Erdos3.rationalConstraint_list_count_le_exp_of_le`, `OAI.Erdos3.rational_height_count_exp_bound`, `OAI.Erdos3.rational_height_count_le_cube`, `OAI.Erdos3.rational_log_height_count_exp_bound`, `OAI.Erdos3.squarefreeInputBudget_le_positive`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B107

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FormalGeometryBudget
namespace OAI

section

namespace Erdos3

theorem formalGeometryHeight_ge_input (n r H : ℕ) : H ≤ formalGeometryHeight n r H :=
  (Nat.le_max_left H _).trans (Nat.le_max_left _ _)

theorem formalBracketMatrixHeight_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (formalBracketMatrixHeight n H : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  have hh : (H : ℝ) * H * H ≤ Real.exp (3 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp p :=
        mul_le_mul (mul_le_mul hH hH (Nat.cast_nonneg _) (Real.exp_nonneg _)) hH
          (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hpow := pow_le_pow_left₀
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg H)) (Nat.cast_nonneg H)) hh (n ^ 2)
  rw [← Real.exp_nat_mul] at hpow
  have hinner : (((n ^ 2 + 1) * (H * H * H) ^ (n ^ 2)) * H : ℕ) ≤
      Real.exp ((n : ℝ) ^ 2 + n ^ 2 * (3 * p) + p) := by
    push_cast
    rw [Real.exp_add, Real.exp_add]
    apply mul_le_mul _ hH (Nat.cast_nonneg H) (by positivity)
    exact mul_le_mul (Real.add_one_le_exp ((n : ℝ) ^ 2))
      (by simpa only [Nat.cast_pow] using hpow) (by positivity) (Real.exp_nonneg _)
  have hout := pow_le_pow_left₀
    (Nat.cast_nonneg (((n ^ 2 + 1) * (H * H * H) ^ (n ^ 2)) * H)) hinner n
  rw [← Real.exp_nat_mul] at hout
  have htotal : (formalBracketMatrixHeight n H : ℝ) ≤
      Real.exp ((n : ℝ) + n * (n ^ 2 + n ^ 2 * (3 * p) + p)) := by
    unfold formalBracketMatrixHeight
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Real.exp_add]
    exact mul_le_mul (Real.add_one_le_exp n) hout (by positivity) (Real.exp_nonneg _)
  apply htotal.trans (Real.exp_le_exp.mpr ?_)
  calc
    (n : ℝ) + n * (n ^ 2 + n ^ 2 * (3 * p) + p) ≤
        p + p * (p ^ 2 + p ^ 2 * (3 * p) + p) := by gcongr
    _ ≤ (p + 2) ^ 5 := by
      have h : 0 ≤ p ^ 5 + 7 * p ^ 4 + 39 * p ^ 3 + 79 * p ^ 2 + 79 * p + 32 := by positivity
      nlinarith

theorem formalCurrentMatrixHeight_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (formalCurrentMatrixHeight n H : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  have hh : (H : ℝ) * H ≤ Real.exp (2 * p) := by
    rw [show 2 * p = p + p by ring, Real.exp_add]
    exact mul_le_mul hH hH (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg H)) hh n
  rw [← Real.exp_nat_mul] at hpow
  have htotal : (formalCurrentMatrixHeight n H : ℝ) ≤ Real.exp ((n : ℝ) + n * (2 * p)) := by
    unfold formalCurrentMatrixHeight
    push_cast
    rw [Real.exp_add]
    exact mul_le_mul (Real.add_one_le_exp n) hpow (by positivity) (Real.exp_nonneg _)
  apply htotal.trans (Real.exp_le_exp.mpr ?_)
  have hnp : (n : ℝ) * (2 * p) ≤ p * (2 * p) := mul_le_mul_of_nonneg_right hn (by positivity)
  have h : 0 ≤ p ^ 3 + 4 * p ^ 2 + 11 * p + 8 := by positivity
  nlinarith

theorem formalGeometryHeight_le_exp (n r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (formalGeometryHeight n r H : ℝ) ≤ Real.exp ((((p + 2) ^ 9) + 2) ^ 5) := by
  let q := (p + 2) ^ 9
  let M := max H (homogeneousIntersectionBasisHeight n r H)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by decide : 1 ≤ 9)
  have hMq : (M : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_max]
    exact max_le (hH.trans (Real.exp_le_exp.mpr hpq)) (stepDrop_basis_height_budget n r H hp hn hr hH)
  have hq5 : q ≤ (q + 2) ^ 5 := le_power_budget hq (by decide : 1 ≤ 5)
  have h35 : (q + 2) ^ 3 ≤ (q + 2) ^ 5 :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ q + 2) (by decide : 3 ≤ 5)
  change ((max M (max (formalCurrentMatrixHeight n M) (formalBracketMatrixHeight n M)) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_max M (max (formalCurrentMatrixHeight n M) (formalBracketMatrixHeight n M)),
    Nat.cast_max (formalCurrentMatrixHeight n M) (formalBracketMatrixHeight n M)]
  exact max_le (hMq.trans (Real.exp_le_exp.mpr hq5))
    (max_le ((formalCurrentMatrixHeight_le_exp n M hq (hn.trans hpq) hMq).trans
      (Real.exp_le_exp.mpr h35)) (formalBracketMatrixHeight_le_exp n M hq (hn.trans hpq) hMq))

theorem exists_formal_geometry_uniform_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n r H : ℕ) (p : ℝ), 0 ≤ p →
      (n : ℝ) ≤ p → (r : ℝ) ≤ 5 * p → (H : ℝ) ≤ Real.exp p →
      (formalGeometryHeight n r H : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget
    (((((Polynomial.X + 2) ^ 3 + 2) ^ 9) + 2) ^ 5)
  refine ⟨C, hC, fun n r H p hp hn hr hH => ?_⟩
  let t := (p + 2) ^ 3
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_power_budget hp (by decide : 1 ≤ 3)
  have hrt : (r : ℝ) ≤ t := by
    have h : 0 ≤ p ^ 3 + 6 * p ^ 2 + 7 * p + 8 := by positivity
    dsimp [t]
    nlinarith
  have hcap : ((t + 2) ^ 9 + 2) ^ 5 ≤ (p + C) ^ C := by
    simpa [t, Polynomial.eval₂_pow] using hbound p hp
  exact (formalGeometryHeight_le_exp n r H ht (hn.trans hpt) hrt
    (hH.trans (Real.exp_le_exp.mpr hpt))).trans (Real.exp_le_exp.mpr hcap)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RationalConstraintCountBudget
namespace OAI

section

namespace Erdos3

open Module

theorem rational_height_count_le_cube (H : ℕ) : (2 * H + 1) * (H + 1) ≤ (H + 1) ^ 3 := by
  have h : 2 * H + 1 ≤ (H + 1) ^ 2 := by nlinarith
  calc
    _ ≤ (H + 1) ^ 2 * (H + 1) := Nat.mul_le_mul_right _ h
    _ = _ := by ring

theorem rational_height_count_exp_bound (H N : ℕ) {A : ℝ}
    (hA : 0 ≤ A) (hH : (H : ℝ) ≤ Real.exp A) :
    ((((2 * H + 1) * (H + 1)) ^ N : ℕ) : ℝ) ≤ Real.exp (3 * N * (A + 1)) := by
  have h1 : 1 ≤ Real.exp A := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hA
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hH1 : (H : ℝ) + 1 ≤ Real.exp (A + 1) := by
    calc
      _ ≤ Real.exp A + Real.exp A := add_le_add hH h1
      _ = 2 * Real.exp A := by ring
      _ ≤ Real.exp 1 * Real.exp A := mul_le_mul_of_nonneg_right htwo (Real.exp_pos A).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hcount : (((2 * H + 1) * (H + 1) : ℕ) : ℝ) ≤ Real.exp (3 * (A + 1)) := by
    calc
      _ ≤ ((H + 1 : ℕ) : ℝ) ^ 3 := by exact_mod_cast rational_height_count_le_cube H
      _ ≤ Real.exp (A + 1) ^ 3 := by
        apply pow_le_pow_left₀ (by positivity)
        simpa only [Nat.cast_add, Nat.cast_one] using hH1
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  rw [Nat.cast_pow]
  calc
    _ ≤ Real.exp (3 * (A + 1)) ^ N := pow_le_pow_left₀ (by positivity) hcount N
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem rational_log_height_count_exp_bound (N : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ((((2 * ⌈Real.exp A⌉₊ + 1) * (⌈Real.exp A⌉₊ + 1)) ^ N : ℕ) : ℝ) ≤
      Real.exp (3 * N * (A + 2)) := by
  have he := rational_height_count_exp_bound ⌈Real.exp A⌉₊ N
    (A := A + 1) (by linarith) (ceil_exp_le_exp_add_one hA)
  convert he using 1
  congr 1
  ring

theorem heightBoundedLieSubalgebras_ncard_exp_bound
    {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (m : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ((heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊).ncard : ℝ) ≤
      Real.exp (3 * (m : ℝ) * Fintype.card ι * (A + 2)) := by
  have hc := (finite_card_heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊).2
  have he := rational_log_height_count_exp_bound (m * Fintype.card ι) hA
  have hr := (Nat.cast_le.mpr hc).trans he
  simpa only [Nat.cast_mul, mul_assoc] using hr

end Erdos3

end

section

namespace Erdos3

theorem rationalConstraint_base_count_le_exp (m n d : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) :
    ((m * (n + 1) * (((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (n * d)) : ℕ) : ℝ) ≤
      Real.exp (2 * p + 3 * p ^ 2 * (p + 2)) := by
  have hpower := rational_log_height_count_exp_bound (n * d) hp
  have hnd : (n : ℝ) * d ≤ p ^ 2 := by
    simpa only [pow_two] using mul_le_mul hn hd (Nat.cast_nonneg d) hp
  have hpower' :
      (((((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (n * d)) : ℕ) : ℝ) ≤
        Real.exp (3 * p ^ 2 * (p + 2)) := by
    apply hpower.trans (Real.exp_le_exp.mpr _)
    rw [Nat.cast_mul]
    nlinarith [mul_le_mul_of_nonneg_right hnd (show 0 ≤ 3 * (p + 2) by positivity)]
  have hmexp : (m : ℝ) ≤ Real.exp p := hm.trans (by linarith [Real.add_one_le_exp p])
  have hnexp : ((n + 1 : ℕ) : ℝ) ≤ Real.exp p := by
    rw [Nat.cast_add, Nat.cast_one]
    exact (add_le_add hn (le_refl 1)).trans (Real.add_one_le_exp p)
  calc
    _ ≤ Real.exp p * Real.exp p * Real.exp (3 * p ^ 2 * (p + 2)) := by
      rw [Nat.cast_mul, Nat.cast_mul]
      exact mul_le_mul (mul_le_mul hmexp hnexp (by positivity) (Real.exp_nonneg _))
        hpower' (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem rationalConstraint_list_count_le_exp (m n d N : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hn : (n : ℝ) ≤ p)
    (hd : (d : ℝ) ≤ p) (hN : (N : ℝ) ≤ p) :
    (((m * (n + 1) * (((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (n * d)) + 1) ^
      (N + 1) : ℕ) : ℝ) ≤ Real.exp ((p + 8) ^ 8) := by
  let M := m * (n + 1) * (((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (n * d))
  let F := 2 * p + 3 * p ^ 2 * (p + 2)
  have hM : (M : ℝ) ≤ Real.exp F := rationalConstraint_base_count_le_exp m n d hp hm hn hd
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have h1 : 1 ≤ Real.exp F := Real.one_le_exp hF
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hM1 : ((M + 1 : ℕ) : ℝ) ≤ Real.exp (F + 1) := by
    calc
      _ ≤ 2 * Real.exp F := by push_cast; linarith
      _ ≤ Real.exp 1 * Real.exp F := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hpoly : F + 1 ≤ (p + 8) ^ 4 := by
    dsimp only [F]
    nlinarith [pow_nonneg hp 3, pow_nonneg hp 4]
  have hN1 : ((N + 1 : ℕ) : ℝ) ≤ p + 8 := by push_cast; linarith
  have ht : 1 ≤ p + 8 := by linarith
  change (((M + 1) ^ (N + 1) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (F + 1)) ^ (N + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM1 _
    _ = Real.exp (((N + 1 : ℕ) : ℝ) * (F + 1)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((p + 8) ^ 5) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ (p + 8) * (p + 8) ^ 4 := mul_le_mul hN1 hpoly (by positivity) (by positivity)
        _ = _ := by ring
    _ ≤ _ := Real.exp_le_exp.mpr (pow_le_pow_right₀ ht (by norm_num))

theorem rationalConstraint_list_count_le_exp_of_le (M m n d N : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hn : (n : ℝ) ≤ p)
    (hd : (d : ℝ) ≤ p) (hN : (N : ℝ) ≤ p)
    (hM : M ≤ m * (n + 1) *
      (((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (n * d))) :
    (((M + 1) ^ (N + 1) : ℕ) : ℝ) ≤ Real.exp ((p + 8) ^ 8) := by
  apply le_trans _ (rationalConstraint_list_count_le_exp m n d N hp hm hn hd hN)
  exact_mod_cast Nat.pow_le_pow_left (Nat.add_le_add_right hM 1) (N + 1)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonSubspaceFamily
namespace OAI

section

namespace Erdos3

open Module

theorem heightBoundedSubspaces_ncard_exp_bound
    {ι L : Type*} [Fintype ι] [AddCommGroup L] [Module ℚ L]
    (e : Basis ι ℚ L) (m : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ((heightBoundedSubspaces e m ⌈Real.exp A⌉₊).ncard : ℝ) ≤
      Real.exp (3 * (m : ℝ) * Fintype.card ι * (A + 2)) := by
  have hc := (finite_card_heightBoundedSubspaces e m ⌈Real.exp A⌉₊).2
  have he := rational_log_height_count_exp_bound (m * Fintype.card ι) hA
  have hr := (Nat.cast_le.mpr hc).trans he
  simpa only [Nat.cast_mul, mul_assoc] using hr

theorem exists_common_height_bounded_subspace_family
    {α ι κ L : Type*} [Fintype ι] [Fintype κ] [AddCommGroup L] [Module ℚ L]
    (e : Basis ι ℚ L) (S : Finset α) (hS : S.Nonempty)
    (K : α → κ → Submodule ℚ L) (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hK : ∀ a ∈ S, ∀ k, K a k ∈ heightBoundedSubspaces e m ⌈Real.exp A⌉₊) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      Real.exp (-(3 * (m : ℝ) * Fintype.card ι * (A + 2)) * Fintype.card κ) * S.card ≤
        (T.card : ℝ) := by
  classical
  let C := heightBoundedSubspaces e m ⌈Real.exp A⌉₊
  let : Fintype C := (finite_card_heightBoundedSubspaces e m ⌈Real.exp A⌉₊).1.fintype
  have hcard : Fintype.card C = C.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hcount : (Fintype.card C : ℝ) ≤ Real.exp (3 * (m : ℝ) * Fintype.card ι * (A + 2)) := by
    rw [hcard]
    exact heightBoundedSubspaces_ncard_exp_bound e m hA
  obtain ⟨labels, T, hsub, hnonempty, hsize, hconst⟩ := exists_large_fixed_choices S hS
    (fun a k (u : C) => K a k = u.val)
    (fun a ha k => ⟨⟨K a k, hK a ha k⟩, rfl⟩) hcount
  obtain ⟨a₀, ha₀⟩ := hnonempty
  refine ⟨a₀, hsub ha₀, T, hsub, ha₀, ?_, hsize⟩
  intro a ha
  funext k
  exact (hconst a ha k).trans (hconst a₀ ha₀ k).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeHyperplaneBasis
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def latticeHyperplane (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ) : Submodule ℤ f.ker :=
  ZLattice.comap ℝ Λ f.ker.subtype

@[simp]
theorem mem_latticeHyperplane (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ) (x : f.ker) :
    x ∈ latticeHyperplane Λ f ↔ (x : E) ∈ Λ := Iff.rfl

noncomputable def hyperplaneRetraction (f : E →ₗ[ℝ] ℝ) (w : E) (hw : f w = 1) :
    E →ₗ[ℝ] f.ker where
  toFun x := ⟨x - f x • w, by simp only [LinearMap.mem_ker, map_sub, map_smul, hw, smul_eq_mul, mul_one, sub_self]⟩
  map_add' x y := by
    apply Subtype.ext
    change (x + y) - f (x + y) • w = (x - f x • w) + (y - f y • w)
    rw [map_add, add_smul]
    abel
  map_smul' a x := by
    apply Subtype.ext
    change a • x - f (a • x) • w = a • (x - f x • w)
    rw [map_smul, smul_eq_mul, smul_sub, smul_smul]

@[simp]
theorem hyperplaneRetraction_coe (f : E →ₗ[ℝ] ℝ) (w : E) (hw : f w = 1) (x : E) :
    (hyperplaneRetraction f w hw x : E) = x - f x • w := rfl

@[simp]
theorem hyperplaneRetraction_on_kernel (f : E →ₗ[ℝ] ℝ) (w : E) (hw : f w = 1) (x : f.ker) :
    hyperplaneRetraction f w hw (x : E) = x := by
  apply Subtype.ext
  simp only [hyperplaneRetraction_coe, LinearMap.mem_ker.mp x.property, zero_smul, sub_zero]

theorem hyperplaneRetraction_mem (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) (x : E) (hx : x ∈ Λ) :
    hyperplaneRetraction f w hw x ∈ latticeHyperplane Λ f := by
  change x - f x • w ∈ Λ
  obtain ⟨n, hn⟩ := hint x hx
  rw [hn]
  simpa only [Int.cast_smul_eq_zsmul] using Λ.sub_mem hx (Λ.smul_mem n hwΛ)

instance latticeHyperplane_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (f : E →ₗ[ℝ] ℝ) : DiscreteTopology (latticeHyperplane Λ f) :=
  ZLattice.comap_discreteTopology ℝ Λ (by fun_prop) Subtype.val_injective

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def integralLatticeValue (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) (x : Λ) : ℤ :=
  (hint x x.property).choose

theorem integralLatticeValue_cast (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) (x : Λ) :
    (integralLatticeValue Λ f hint x : ℝ) = f (x : E) :=
  (hint x x.property).choose_spec.symm

noncomputable def integralLatticeCoordinate (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) : Λ →ₗ[ℤ] ℤ where
  toFun := integralLatticeValue Λ f hint
  map_add' x y := by
    apply Int.cast_injective (α := ℝ)
    simp only [Int.cast_add, integralLatticeValue_cast, Submodule.coe_add, map_add]
  map_smul' a x := by
    apply Int.cast_injective (α := ℝ)
    simp only [integralLatticeValue_cast, Submodule.coe_smul, map_zsmul, RingHom.id_apply,
      smul_eq_mul, Int.cast_mul, zsmul_eq_mul]

theorem integralLatticeCoordinate_cast (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) (x : Λ) :
    (integralLatticeCoordinate Λ f hint x : ℝ) = f (x : E) :=
  integralLatticeValue_cast Λ f hint x

end Erdos3

end

section

namespace Erdos3

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def latticeGaussianMass (Λ : Submodule ℤ E) (t : ℝ) (x : E) : ℝ :=
  ∑' m : Λ, Real.exp (-Real.pi * t * ‖x - (m : E)‖ ^ 2)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeGaussianMass_add_lattice (Λ : Submodule ℤ E) (t : ℝ) (x : E) (v : Λ) :
    latticeGaussianMass Λ t (x + (v : E)) = latticeGaussianMass Λ t x := by
  have h := (Equiv.addRight v).tsum_eq (fun m : Λ => Real.exp (-Real.pi * t * ‖x + (v : E) - (m : E)‖ ^ 2))
  simpa only [latticeGaussianMass, Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub] using h.symm

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def latticeHyperplaneRetraction (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) : Λ →ₗ[ℤ] latticeHyperplane Λ f where
  toFun x := ⟨hyperplaneRetraction f w hw x, hyperplaneRetraction_mem Λ f hint w hwΛ hw x x.property⟩
  map_add' x y := by
    apply Subtype.ext
    change hyperplaneRetraction f w hw ((x : E) + y) = _
    exact map_add (hyperplaneRetraction f w hw) (x : E) (y : E)
  map_smul' n x := by
    apply Subtype.ext
    change hyperplaneRetraction f w hw (n • (x : E)) = n • hyperplaneRetraction f w hw x
    exact map_zsmul (hyperplaneRetraction f w hw) n (x : E)

@[simp]
theorem latticeHyperplaneRetraction_coe (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) (x : Λ) :
    (((latticeHyperplaneRetraction Λ f hint w hwΛ hw x : latticeHyperplane Λ f) : f.ker) : E) =
      (x : E) - f (x : E) • w := rfl

noncomputable def latticeHyperplaneSplit (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) :
    Λ ≃ₗ[ℤ] (latticeHyperplane Λ f × ℤ) :=
  { (latticeHyperplaneRetraction Λ f hint w hwΛ hw).prod (integralLatticeCoordinate Λ f hint) with
    invFun y := ⟨((y.1 : f.ker) : E) + y.2 • w,
      Λ.add_mem ((mem_latticeHyperplane Λ f (y.1 : f.ker)).mp y.1.property) (Λ.smul_mem y.2 hwΛ)⟩
    left_inv x := by
      apply Subtype.ext
      change (x : E) - f (x : E) • w + integralLatticeCoordinate Λ f hint x • w = (x : E)
      rw [← Int.cast_smul_eq_zsmul ℝ, integralLatticeCoordinate_cast]
      exact sub_add_cancel _ _
    right_inv y := by
      apply Prod.ext
      · apply Subtype.ext
        apply Subtype.ext
        change ((y.1 : f.ker) : E) + y.2 • w -
          f (((y.1 : f.ker) : E) + y.2 • w) • w = ((y.1 : f.ker) : E)
        have hy : f ((y.1 : f.ker) : E) = 0 := (y.1 : f.ker).property
        rw [map_add, map_zsmul, hy, hw, zero_add, zsmul_eq_mul, mul_one,
          Int.cast_smul_eq_zsmul]
        exact add_sub_cancel_right _ _
      · apply Int.cast_injective (α := ℝ)
        change (integralLatticeCoordinate Λ f hint _ : ℝ) = (y.2 : ℝ)
        rw [integralLatticeCoordinate_cast]
        change f (((y.1 : f.ker) : E) + y.2 • w) = (y.2 : ℝ)
        have hy : f ((y.1 : f.ker) : E) = 0 := (y.1 : f.ker).property
        simp only [map_add, map_zsmul, hy, hw, zero_add, zsmul_eq_mul, mul_one] }

theorem latticeHyperplaneSplit_symm_coe (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) (y : latticeHyperplane Λ f × ℤ) :
    ((latticeHyperplaneSplit Λ f hint w hwΛ hw).symm y : E) =
      ((y.1 : f.ker) : E) + y.2 • w := rfl

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem gaussian_translate_bound (t R : ℝ) (ht : 0 ≤ t) (hR : 0 ≤ R)
    (x m : E) (hx : ‖x‖ ≤ R) :
    Real.exp (-Real.pi * t * ‖x - m‖ ^ 2) ≤
      Real.exp (Real.pi * t * R ^ 2) * Real.exp (-Real.pi * (t / 2) * ‖m‖ ^ 2) := by
  have htriangle : ‖m‖ ≤ ‖x - m‖ + ‖x‖ := by
    calc
      ‖m‖ = ‖(m - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖m - x‖ + ‖x‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  have hsquare : ‖m‖ ^ 2 ≤ 2 * ‖x - m‖ ^ 2 + 2 * R ^ 2 := by
    have hx0 := norm_nonneg x
    have hm0 := norm_nonneg m
    have hxm0 := norm_nonneg (x - m)
    nlinarith [sq_nonneg (‖x - m‖ - ‖x‖)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le ht)
    (sub_nonneg.mpr hsquare)]

variable [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def latticeHyperplaneBasis (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1)
    (b : Module.Basis ι ℤ (latticeHyperplane Λ f)) : Module.Basis (ι ⊕ Unit) ℤ Λ :=
  (b.prod (Module.Basis.singleton Unit ℤ)).map
    (latticeHyperplaneSplit Λ f hint w hwΛ hw).symm

@[simp]
theorem latticeHyperplaneBasis_inl (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1)
    (b : Module.Basis ι ℤ (latticeHyperplane Λ f)) (i : ι) :
    (latticeHyperplaneBasis Λ f hint w hwΛ hw b (Sum.inl i) : E) = (b i : f.ker) := by
  simp [latticeHyperplaneBasis, latticeHyperplaneSplit_symm_coe]

@[simp]
theorem latticeHyperplaneBasis_inr (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1)
    (b : Module.Basis ι ℤ (latticeHyperplane Λ f)) (j : Unit) :
    (latticeHyperplaneBasis Λ f hint w hwΛ hw b (Sum.inr j) : E) = w := by
  simp [latticeHyperplaneBasis, latticeHyperplaneSplit_symm_coe]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeGaussianHyperplane
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def latticeHyperplaneInclusion (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ) :
    latticeHyperplane Λ f →ₗ[ℤ] Λ where
  toFun x := ⟨((x : f.ker) : E), (mem_latticeHyperplane Λ f (x : f.ker)).mp x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SplitCoverProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D E : RationalFilteredNilmanifold L s d)

noncomputable def sublatticeProjection (h : E.lattice ≤ D.lattice) : E.Space → D.Space :=
  cosetMap E.realLattice D.realLattice (MonoidHom.id _) (Subgroup.map_mono h)

@[simp] theorem sublatticeProjection_mk (h : E.lattice ≤ D.lattice) (x : E.RealGroup) :
    sublatticeProjection D E h (QuotientGroup.mk x) = QuotientGroup.mk x := rfl

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem sublatticeProjection_lipschitz (h : E.lattice ≤ D.lattice) (hb : E.basis = D.basis) :
    letI := E.metricSpace
    letI := D.metricSpace
    LipschitzWith 1 (sublatticeProjection D E h) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hLip : LipschitzWith 1 (MonoidHom.id D.RealGroup) := LipschitzWith.id
  have hc := lipschitz_cosetMap E.realLattice D.realLattice E.realLattice_closed_discrete.1
    D.realLattice_closed_discrete.1 (MonoidHom.id _) (Subgroup.map_mono h) hLip
  change @LipschitzWith E.Space D.Space
    (quotientMetricSpace (E.basis.baseChange ℝ) E.realLattice
      E.realLattice_closed_discrete.1).toEMetricSpace.toPseudoEMetricSpace
    (quotientMetricSpace (D.basis.baseChange ℝ) D.realLattice
      D.realLattice_closed_discrete.1).toEMetricSpace.toPseudoEMetricSpace
    1 (sublatticeProjection D E h)
  rw [hb]
  exact hc

theorem sublattice_pullback_lipschitz (h : E.lattice ≤ D.lattice) (hb : E.basis = D.basis)
    (u : D.Space → ℂ) {K : ℝ≥0} (hu : letI := D.metricSpace; LipschitzWith K u) :
    letI := E.metricSpace
    LipschitzWith K (u ∘ sublatticeProjection D E h) := by
  let := E.metricSpace
  let := D.metricSpace
  simpa only [mul_one] using hu.comp (sublatticeProjection_lipschitz D E h hb)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : Option ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (V : RationalFilteredNilmanifold (∀ i, L i) s (Fintype.card (Σ i, Fin (d i))))
  (hsub : (pi D).lattice ≤ V.lattice)

noncomputable def splitCoverProjection :
    (D none).Space × (pi (fun i => D (some i))).Space → V.Space :=
  sublatticeProjection V (pi D) hsub ∘ (optionProductSpaceEquiv D).symm

theorem splitCoverProjection_mk (x : (pi D).RealGroup) :
    splitCoverProjection D V hsub (optionProductSpaceEquiv D (QuotientGroup.mk x)) =
      QuotientGroup.mk x := by
  simp only [splitCoverProjection, Function.comp_apply, Equiv.symm_apply_apply,
    sublatticeProjection_mk]

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [T2Space (ℝ ⊗[ℚ] (∀ i, L (some i)))]

theorem splitCoverProjection_lipschitz (hb : (pi D).basis = V.basis) :
    letI := (D none).metricSpace
    letI := (pi (fun i => D (some i))).metricSpace
    letI := V.metricSpace
    LipschitzWith ((1 + productMetricBound (fun i => d (some i))) * productMetricBound d)
      (splitCoverProjection D V hsub) := by
  let := (D none).metricSpace
  let := (pi (fun i => D (some i))).metricSpace
  let := (pi D).metricSpace
  let := V.metricSpace
  simpa only [one_mul, splitCoverProjection] using
    (sublatticeProjection_lipschitz V (pi D) hsub hb).comp (optionProductSpaceEquiv_symm_lipschitz D)

theorem splitCoverProjection_pullback (hb : (pi D).basis = V.basis)
    (u : V.Space → ℂ) {K : ℝ≥0} (hu : letI := V.metricSpace; LipschitzWith K u)
    (hpositive : ∀ x, (u x).im = 0 ∧ 0 ≤ (u x).re ∧ (u x).re ≤ 1) :
    letI := (D none).metricSpace
    letI := (pi (fun i => D (some i))).metricSpace
    let v := u ∘ splitCoverProjection D V hsub
    LipschitzWith (K * ((1 + productMetricBound (fun i => d (some i))) * productMetricBound d)) v ∧
      (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
      ∀ x : (pi D).RealGroup, v (optionProductSpaceEquiv D (QuotientGroup.mk x)) =
        u (QuotientGroup.mk x) := by
  let := (D none).metricSpace
  let := (pi (fun i => D (some i))).metricSpace
  let := V.metricSpace
  exact ⟨hu.comp (splitCoverProjection_lipschitz D V hsub hb),
    fun x => hpositive _, fun x => congrArg u (splitCoverProjection_mk D V hsub x)⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeCoverNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T : D.Niltest w) (Λ : Subgroup D.filtration.Group) (m : ℕ) (hm : 0 < m)
  (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid m) (hΛ : Λ ≤ D.lattice)

noncomputable def onSublattice : (D.withLattice Λ m hm hin hout).Niltest w where
  orbit := T.orbit
  observable := T.observable ∘ sublatticeProjection D (D.withLattice Λ m hm hin hout) hΛ
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le _ := T.norm_le _
  lipschitz := sublattice_pullback_lipschitz D (D.withLattice Λ m hm hin hout) hΛ rfl
    T.observable T.lipschitz

theorem onSublattice_complexity {p : ℝ} (hT : T.ComplexityLE p)
    (hD : (D.withLattice Λ m hm hin hout).GeometryComplexityLE p) :
    (T.onSublattice Λ m hm hin hout hΛ).ComplexityLE p := ⟨hD, hT.2⟩

theorem onSublattice_unit_interval (hT : T.UnitIntervalValued) :
    (T.onSublattice Λ m hm hin hout hΛ).UnitIntervalValued := fun _ => hT _

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieFiltration
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
    (T : D.Niltest w) (E : RationalFilteredNilmanifold L s d)
    (hfil : E.filtration = D.filtration) (hb : E.basis = D.basis)
    (hΛ : E.lattice ≤ D.lattice)

noncomputable def onNativeCover : E.Niltest w where
  orbit := polynomialOrbitOfLog T.orbit.log (by rw [hfil]; exact T.orbit.adapted)
  observable := T.observable ∘ sublatticeProjection D E hΛ
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le _ := T.norm_le _
  lipschitz := sublattice_pullback_lipschitz D E hΛ hb T.observable T.lipschitz

@[simp] theorem onNativeCover_log :
    (T.onNativeCover E hfil hb hΛ).orbit.log = T.orbit.log := rfl

@[simp] theorem onNativeCover_normBound :
    (T.onNativeCover E hfil hb hΛ).normBound = T.normBound := rfl

@[simp] theorem onNativeCover_lipBound :
    (T.onNativeCover E hfil hb hΛ).lipBound = T.lipBound := rfl

@[simp] theorem onNativeCover_eval (x : σ → ℤ) :
    (T.onNativeCover E hfil hb hΛ).eval x = T.eval x := rfl

@[simp] theorem onNativeCover_evalCyclic (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (T.onNativeCover E hfil hb hΛ).evalCyclic N x = T.evalCyclic N x := rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPositivePolynomialDownsets
namespace OAI

section

namespace Erdos3

noncomputable def positivePolynomialInputBudget (t : ℕ) (p : ℝ) : ℝ :=
  p + 1 + squarefreeInputBudget t p

noncomputable def positivePolynomialDenominatorBudget (t : ℕ) (p : ℝ) : ℝ :=
  positivePolynomialInputBudget t p + (positivePolynomialInputBudget t p + 2) ^ 4

noncomputable def positivePolynomialModelBudget (t : ℕ) (p : ℝ) : ℝ :=
  positivePolynomialDenominatorBudget t p +
    (positivePolynomialDenominatorBudget t p + (bchIntegralDenominatorBound t + 5 : ℕ)) ^
      (bchIntegralDenominatorBound t + 5)

theorem positivePolynomialInputBudget_nonneg (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ positivePolynomialInputBudget t p :=
  add_nonneg (by linarith) (squarefreeInputBudget_nonneg t hp)

theorem squarefreeInputBudget_le_positive (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    squarefreeInputBudget t p ≤ positivePolynomialInputBudget t p :=
  le_add_of_nonneg_left (by linarith)

theorem positivePolynomialInputBudget_le_denominator (t : ℕ) (p : ℝ) :
    positivePolynomialInputBudget t p ≤ positivePolynomialDenominatorBudget t p :=
  le_add_of_nonneg_right (by positivity)

theorem positivePolynomialDenominatorBudget_le_model (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    positivePolynomialDenominatorBudget t p ≤ positivePolynomialModelBudget t p := by
  have h := (positivePolynomialInputBudget_nonneg t hp).trans
    (positivePolynomialInputBudget_le_denominator t p)
  exact le_add_of_nonneg_right (pow_nonneg (add_nonneg h (Nat.cast_nonneg _)) _)

theorem exists_positivePolynomialModel_budget (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      positivePolynomialModelBudget t p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := Polynomial.X + 1 +
    (Polynomial.C (2 ^ t) * Polynomial.X + (Polynomial.X + 3) ^ 8)
  let R : Polynomial ℕ := Q + (Q + 2) ^ 4
  let K := bchIntegralDenominatorBound t + 5
  obtain ⟨C, hC, h⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa only [positivePolynomialModelBudget, positivePolynomialDenominatorBudget,
    positivePolynomialInputBudget, squarefreeInputBudget, R, Q, K,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one,
    Polynomial.eval₂_ofNat, map_pow, map_ofNat, Nat.coe_castRingHom] using h p hp

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

abbrev PositivePolynomialBasisIndex := Σ a : BoxedDegreeIndex bound,
  Fin (finrank ℚ (M.filtration.positiveCoefficientLayer a))

noncomputable def positivePolynomialBasis (p : ℝ) :
    Basis M.PositivePolynomialBasisIndex ℚ M.filtration.positivePolynomialAlgebra :=
  M.filtration.positivePolynomialBasis (M.positiveCoefficientBasis p)

theorem positivePolynomialBasisIndex_card_le (p : ℝ) :
    Fintype.card M.PositivePolynomialBasisIndex ≤ 2 ^ (∑ i, bound i) * d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  rw [← finrank_eq_card_basis (M.positivePolynomialBasis p)]
  simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
    M.filtration.positivePolynomial_finrank_le_total

omit [DecidableEq σ] in
theorem positiveCoefficientBasis_card_le (a : BoxedDegreeIndex bound) :
    finrank ℚ (M.filtration.positiveCoefficientLayer a) ≤ d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
    (M.filtration.positiveCoefficientLayer a).finrank_le

omit [DecidableEq σ] in
theorem positivePolynomialBasis_structure_height {p : ℝ} (hM : M.ComplexityLE p)
    (i j k : M.PositivePolynomialBasisIndex) :
    RationalHeightLE (lieStructureConstants (M.positivePolynomialBasis p) i j k)
      (squarefreeStructureHeight d ⌈Real.exp p⌉₊) := by
  have h := M.filtration.positivePolynomialBasis_structure_height
    (M.positiveCoefficientBasis p) D.basis (one_le_ceil_exp p)
    (M.positiveCoefficientBasis_height hM)
    (fun i j k => rationalHeightLE_ceil_exp (hM.1.2.2.1 i j k))
    (fun a => by simpa only [Fintype.card_fin] using M.positiveCoefficientBasis_card_le a) i j k
  simpa only [positivePolynomialBasis, Fintype.card_fin] using h

omit [DecidableEq σ] in
theorem positivePolynomialBasis_evaluation_height {p : ℝ} (hM : M.ComplexityLE p)
    (i : M.PositivePolynomialBasisIndex) (k : Fin d) :
    RationalHeightLE (D.basis.repr
      (M.filtration.positivePolynomialEvaluation (M.positivePolynomialBasis p i)) k) ⌈Real.exp p⌉₊ := by
  change RationalHeightLE (D.basis.repr
    (M.filtration.positivePolynomialEvaluation
      (M.filtration.positivePolynomialBasis (M.positiveCoefficientBasis p) i)) k) _
  rw [M.filtration.positivePolynomialBasis_evaluation]
  exact M.positiveCoefficientBasis_height hM i.1 i.2 k

noncomputable def positivePolynomialFinBasis (p : ℝ) :
    Basis (Fin (Fintype.card M.PositivePolynomialBasisIndex)) ℚ M.filtration.positivePolynomialAlgebra :=
  (M.positivePolynomialBasis p).reindex (Fintype.equivFin M.PositivePolynomialBasisIndex)

theorem positivePolynomialFinBasis_structure_height {p : ℝ} (hM : M.ComplexityLE p) (i j k) :
    RationalHeightLE (lieStructureConstants (M.positivePolynomialFinBasis p) i j k)
      (squarefreeStructureHeight d ⌈Real.exp p⌉₊) := by
  rw [positivePolynomialFinBasis, lieStructureConstants_reindex]
  exact M.positivePolynomialBasis_structure_height hM _ _ _

theorem positivePolynomialFinBasis_evaluation_height {p : ℝ} (hM : M.ComplexityLE p) (i k) :
    RationalHeightLE (D.basis.repr
      (M.filtration.positivePolynomialEvaluation (M.positivePolynomialFinBasis p i)) k) ⌈Real.exp p⌉₊ := by
  rw [positivePolynomialFinBasis, Basis.reindex_apply]
  exact M.positivePolynomialBasis_evaluation_height hM _ _

theorem positivePolynomialFinBasis_multidegree_height (p : ℝ) (a : σ → ℕ) (j k) :
    RationalHeightLE ((M.positivePolynomialFinBasis p).repr
      (M.filtration.positivePolynomialMultidegreeBasis (M.positiveCoefficientBasis p) a j).val k) 1 := by
  rw [positivePolynomialFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.positivePolynomialMultidegreeBasis_height (M.positiveCoefficientBasis p) a j _

theorem positivePolynomialFinBasis_degree_height (p : ℝ) (n : ℕ) (j k) :
    RationalHeightLE ((M.positivePolynomialFinBasis p).repr
      (M.filtration.positivePolynomialDegreeBasis (M.positiveCoefficientBasis p) n j).val k) 1 := by
  rw [positivePolynomialFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.positivePolynomialDegreeBasis_height (M.positiveCoefficientBasis p) n j _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)

abbrev PositivePolynomialDownsetIndex :=
  {j : M.PositivePolynomialBasisIndex // j ∉ {k | boxedDegreeMonomial k.1 ∉ J}}

noncomputable def positivePolynomialDownsetBasis (p : ℝ) :
    Basis (M.PositivePolynomialDownsetIndex J) ℚ
      (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ) :=
  M.filtration.positivePolynomialDownsetBasis (M.positiveCoefficientBasis p) J hJ

noncomputable def positivePolynomialDownsetFinBasis (p : ℝ) :
    Basis (Fin (Fintype.card (M.PositivePolynomialDownsetIndex J))) ℚ
      (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ) :=
  (M.positivePolynomialDownsetBasis J hJ p).reindex (Fintype.equivFin _)

theorem positivePolynomialDownsetIndex_card_le :
    Fintype.card (M.PositivePolynomialDownsetIndex J) ≤
      Fintype.card M.PositivePolynomialBasisIndex := Fintype.card_subtype_le _

omit [DecidableEq σ] [DecidablePred (· ∈ J)] in
theorem positivePolynomialDownsetBasis_structure (p : ℝ) (i j k) :
    lieStructureConstants (M.positivePolynomialDownsetBasis J hJ p) i j k =
      lieStructureConstants (M.positivePolynomialBasis p) i.val j.val k.val := by
  exact supportedQuotientBasis_lieStructure _ _ _
    (M.filtration.positivePolynomialDownsetIdeal_eq_span (M.positiveCoefficientBasis p) J hJ) i j k

theorem positivePolynomialDownsetFinBasis_multidegree_height (p : ℝ) (a : σ → ℕ) (j k) :
    RationalHeightLE ((M.positivePolynomialDownsetFinBasis J hJ p).repr
      (M.filtration.positivePolynomialDownsetMultidegreeBasis (M.positiveCoefficientBasis p) J hJ a j).val k) 1 := by
  rw [positivePolynomialDownsetFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.positivePolynomialDownsetMultidegreeBasis_height
    (M.positiveCoefficientBasis p) J hJ a j _

theorem positivePolynomialDownsetFinBasis_degree_height (p : ℝ) (n : ℕ) (j k) :
    RationalHeightLE ((M.positivePolynomialDownsetFinBasis J hJ p).repr
      (M.filtration.positivePolynomialDownsetDegreeBasis (M.positiveCoefficientBasis p) J hJ n j).val k) 1 := by
  rw [positivePolynomialDownsetFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.positivePolynomialDownsetDegreeBasis_height
    (M.positiveCoefficientBasis p) J hJ n j _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

def PositivePolynomialGridStable (p : ℝ) (B : ℕ) : Prop :=
  ∀ x ∈ coordinateGridModule (M.positivePolynomialBasis p) B,
    ∀ y ∈ coordinateGridModule (M.positivePolynomialBasis p) B,
      lieBCH (∑ i, bound i) x y ∈ coordinateGridModule (M.positivePolynomialBasis p) B

noncomputable def positivePolynomialLattice (p : ℝ) (B : ℕ)
    (hstable : M.PositivePolynomialGridStable p B) :
    Subgroup M.filtration.positivePolynomialMultidegree.ordinary.Group :=
  coordinateGridBCHSubgroup (M.positivePolynomialBasis p) B
    M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot hstable

theorem positivePolynomialLattice_coordinates (p : ℝ) (B : ℕ)
    (hstable : M.PositivePolynomialGridStable p B) :
    bchSubgroupCoordinates (M.positivePolynomialBasis p) (M.positivePolynomialLattice p B hstable) =
      scaledIntegerGrid B := coordinateGridBCHSubgroup_coordinates _ _ _ hstable

noncomputable def positivePolynomialEvaluationDenominator (p : ℝ) : ℕ :=
  D.grid * matrixDenominator (LinearMap.toMatrix (M.positivePolynomialBasis p) D.basis
    M.filtration.positivePolynomialEvaluation.toLinearMap)

theorem positivePolynomialEvaluationDenominator_pos (p : ℝ) :
    0 < M.positivePolynomialEvaluationDenominator p :=
  Nat.mul_pos D.grid_pos (matrixDenominator_pos _)

theorem positivePolynomialLattice_maps (p : ℝ) (B : ℕ)
    (hstable : M.PositivePolynomialGridStable p B)
    (hdiv : M.positivePolynomialEvaluationDenominator p ∣ B) :
    M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) := by
  classical
  intro g hg
  apply (bchSubgroupCoordinates_repr (M.positivePolynomialBasis p)
    (D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation)) g).mp
  rw [bchSubgroupCoordinates_comap_of_steps (M.positivePolynomialBasis p) D.basis]
  apply D.inner_grid
  apply matrix_mulVec_fine_grid
  apply scaledIntegerGrid_subset_of_dvd hdiv
  rw [← M.positivePolynomialLattice_coordinates p B hstable]
  exact (bchSubgroupCoordinates_repr (M.positivePolynomialBasis p)
    (M.positivePolynomialLattice p B hstable) g).mpr hg

theorem exists_positivePolynomial_stable_grid {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ B : ℕ, 0 < B ∧ M.positivePolynomialEvaluationDenominator p ∣ B ∧
      B ≤ bchIntegralDenominatorBound (∑ i, bound i) *
        squarefreeStructureHeight d ⌈Real.exp p⌉₊ ^ (Fintype.card M.PositivePolynomialBasisIndex ^ 3) *
        M.positivePolynomialEvaluationDenominator p ∧ M.PositivePolynomialGridStable p B :=
  exists_bch_stable_integral_grid (M.positivePolynomialBasis p)
    M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot
    (M.positivePolynomialEvaluationDenominator p) (M.positivePolynomialEvaluationDenominator_pos p)
    (M.positivePolynomialBasis_structure_height hM)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def positivePolynomialModel (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) :
    RationalFilteredNilmanifold M.filtration.positivePolynomialAlgebra
      (∑ i, bound i) (Fintype.card M.PositivePolynomialBasisIndex) where
  filtration := M.filtration.positivePolynomialMultidegree.ordinary
  basis := M.positivePolynomialFinBasis p
  layerBasis i := M.filtration.positivePolynomialDegreeBasis (M.positiveCoefficientBasis p) (i.val + 1)
  lattice := M.positivePolynomialLattice p B hstable
  grid := B
  grid_pos := hB
  inner_grid := by
    apply bchSubgroup_inner_grid_reindex
    rw [M.positivePolynomialLattice_coordinates]
  outer_grid := by
    apply bchSubgroup_outer_grid_reindex
    rw [M.positivePolynomialLattice_coordinates]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid B B hx

noncomputable def positivePolynomialModelMultidegree (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) :
    (M.positivePolynomialModel p B hB hstable).MultidegreeStructure bound where
  filtration := M.filtration.positivePolynomialMultidegree
  ordinary := rfl
  basis a := M.filtration.positivePolynomialMultidegreeBasis (M.positiveCoefficientBasis p)
    (fun i => (a i).val)

theorem positivePolynomialModel_complexity {p q : ℝ} (hM : M.ComplexityLE p)
    (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B)
    (hq : 0 ≤ q) (hd : (Fintype.card M.PositivePolynomialBasisIndex : ℝ) ≤ q)
    (hBq : (B : ℝ) ≤ Real.exp q)
    (hHq : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp q) :
    (M.positivePolynomialModelMultidegree p B hB hstable).ComplexityLE q := by
  have hone : ((1 : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_one]
    exact Real.one_le_exp hq
  refine ⟨⟨hd, hBq, ?_, ?_⟩, ?_⟩
  · intro i j k
    exact rationalLogHeight_le_of_height (M.positivePolynomialFinBasis_structure_height hM i j k) hHq
  · intro i j k
    exact rationalLogHeight_le_of_height (M.positivePolynomialFinBasis_degree_height p (i.val + 1) j k) hone
  · intro a j k
    exact rationalLogHeight_le_of_height
      (M.positivePolynomialFinBasis_multidegree_height p (fun i => (a i).val) j k) hone

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped BigOperators
open NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem positivePolynomialEvaluationDenominator_le_exp {p : ℝ} (hM : M.ComplexityLE p) :
    (M.positivePolynomialEvaluationDenominator p : ℝ) ≤
      Real.exp (positivePolynomialDenominatorBudget (∑ i, bound i) p) := by
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let t := ∑ i, bound i
  have hSQ := squarefreeInputBudget_le_positive t hp
  have hpQ : p ≤ positivePolynomialInputBudget t p :=
    (le_squarefreeInputBudget t hp).trans hSQ
  have hp1Q : p + 1 ≤ positivePolynomialInputBudget t p :=
    le_add_of_nonneg_right (squarefreeInputBudget_nonneg t hp)
  have hQ := positivePolynomialInputBudget_nonneg t hp
  have hNQ : (Fintype.card M.PositivePolynomialBasisIndex : ℝ) ≤
      positivePolynomialInputBudget t p := by
    apply le_trans _ hSQ
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast M.positivePolynomialBasisIndex_card_le p
      _ ≤ (2 : ℝ) ^ t * p := mul_le_mul_of_nonneg_left hM.1.1 (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have hA : ∀ i j, RationalHeightLE
      (LinearMap.toMatrix (M.positivePolynomialBasis p) D.basis
        M.filtration.positivePolynomialEvaluation.toLinearMap i j) ⌈Real.exp p⌉₊ := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    exact M.positivePolynomialBasis_evaluation_height hM j i
  have hden := matrixDenominator_allowance_le_exp _ D.grid ⌈Real.exp p⌉₊ hA hQ
    (by simpa only [Fintype.card_fin] using hM.1.1.trans hpQ) hNQ
    ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1Q))
    (hM.1.2.1.trans (Real.exp_le_exp.mpr hpQ))
  exact hden.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hQ))

theorem exists_controlled_positivePolynomial_model {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
      (M.positivePolynomialModelMultidegree p B hB hstable).ComplexityLE
        (positivePolynomialModelBudget (∑ i, bound i) p) ∧
      M.positivePolynomialLattice p B hstable ≤
        D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let t := ∑ i, bound i
  have hSR := (squarefreeInputBudget_le_positive t hp).trans
    (positivePolynomialInputBudget_le_denominator t p)
  have hR := (positivePolynomialInputBudget_nonneg t hp).trans
    (positivePolynomialInputBudget_le_denominator t p)
  have hRT := positivePolynomialDenominatorBudget_le_model t hp
  have hNR : (Fintype.card M.PositivePolynomialBasisIndex : ℝ) ≤
      positivePolynomialDenominatorBudget t p := by
    apply le_trans _ hSR
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast M.positivePolynomialBasisIndex_card_le p
      _ ≤ (2 : ℝ) ^ t * p := mul_le_mul_of_nonneg_left hM.1.1 (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have hHR : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp (positivePolynomialDenominatorBudget t p) :=
    (squarefreeStructureHeight_ceil_exp d hp hM.1.1).trans
      (Real.exp_le_exp.mpr ((le_add_of_nonneg_left (mul_nonneg (by positivity) hp)).trans hSR))
  obtain ⟨B, hB, hdiv, hraw, hstable⟩ := M.exists_positivePolynomial_stable_grid hM
  refine ⟨B, hB, hstable, ?_, M.positivePolynomialLattice_maps p B hstable hdiv⟩
  apply M.positivePolynomialModel_complexity hM B hB hstable (hR.trans hRT) (hNR.trans hRT)
  · apply (Nat.cast_le.mpr hraw).trans
    exact (integral_grid_allowance_le_exp (bchIntegralDenominatorBound t)
      (Fintype.card M.PositivePolynomialBasisIndex) _ _ hR hNR hHR
      (M.positivePolynomialEvaluationDenominator_le_exp hM)).trans
        (Real.exp_le_exp.mpr (le_add_of_nonneg_left hR))
  · exact hHR.trans (Real.exp_le_exp.mpr hRT)

theorem exists_positivePolynomial_model_uniform (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
      {bound : σ → ℕ} (M : D.MultidegreeStructure bound) {p : ℝ},
      (∑ i, bound i) = t → M.ComplexityLE p →
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
        (M.positivePolynomialModelMultidegree p B hB hstable).ComplexityLE ((p + C) ^ C) ∧
        M.positivePolynomialLattice p B hstable ≤
          D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) := by
  obtain ⟨C, hC, hbudget⟩ := exists_positivePolynomialModel_budget t
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ s d D bound M p ht hM
  obtain ⟨B, hB, hstable, hmodel, hmap⟩ := M.exists_controlled_positivePolynomial_model hM
  refine ⟨B, hB, hstable, hmodel.mono _ ?_, hmap⟩
  rw [ht]
  exact hbudget p ((Nat.cast_nonneg d).trans hM.1.1)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)

noncomputable def positivePolynomialDownsetLattice (p : ℝ) (B : ℕ)
    (hstable : M.PositivePolynomialGridStable p B) :
    Subgroup (M.filtration.positivePolynomialDownsetQuotient J hJ).ordinary.Group :=
  (M.positivePolynomialLattice p B hstable).map
    (M.filtration.positivePolynomialMultidegree.ordinary.quotientStepHom
      (restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ)
      (by rw [M.filtration.positivePolynomialMultidegree.ordinary.terminal]; exact bot_le))

theorem positivePolynomialDownsetLattice_coordinates (p : ℝ) (B : ℕ)
    (hstable : M.PositivePolynomialGridStable p B) :
    bchSubgroupCoordinates (M.positivePolynomialDownsetBasis J hJ p)
      (M.positivePolynomialDownsetLattice J hJ p B hstable) = scaledIntegerGrid B := by
  exact M.filtration.positivePolynomialMultidegree.ordinary.quotientStep_exact_grid_supported
    (M.positivePolynomialBasis p)
    (restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ) _
    {j | boxedDegreeMonomial j.1 ∉ J}
    (M.filtration.positivePolynomialDownsetIdeal_eq_span (M.positiveCoefficientBasis p) J hJ)
    (M.positivePolynomialLattice p B hstable) B (M.positivePolynomialLattice_coordinates p B hstable)

noncomputable def positivePolynomialDownsetModel (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) :
    RationalFilteredNilmanifold
      (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ)
      (∑ i, bound i) (Fintype.card (M.PositivePolynomialDownsetIndex J)) where
  filtration := (M.filtration.positivePolynomialDownsetQuotient J hJ).ordinary
  basis := M.positivePolynomialDownsetFinBasis J hJ p
  layerBasis i := M.filtration.positivePolynomialDownsetDegreeBasis
    (M.positiveCoefficientBasis p) J hJ (i.val + 1)
  lattice := M.positivePolynomialDownsetLattice J hJ p B hstable
  grid := B
  grid_pos := hB
  inner_grid := by
    apply bchSubgroup_inner_grid_reindex
    rw [M.positivePolynomialDownsetLattice_coordinates]
  outer_grid := by
    apply bchSubgroup_outer_grid_reindex
    rw [M.positivePolynomialDownsetLattice_coordinates]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid B B hx

noncomputable def positivePolynomialDownsetModelMultidegree (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) :
    (M.positivePolynomialDownsetModel J hJ p B hB hstable).MultidegreeStructure bound where
  filtration := M.filtration.positivePolynomialDownsetQuotient J hJ
  ordinary := rfl
  basis a := M.filtration.positivePolynomialDownsetMultidegreeBasis
    (M.positiveCoefficientBasis p) J hJ (fun i => (a i).val)

theorem positivePolynomialDownsetModel_complexity (p q : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (hE : (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q) :
    (M.positivePolynomialDownsetModelMultidegree J hJ p B hB hstable).ComplexityLE q := by
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hE.1
  have hone : ((1 : ℕ) : ℝ) ≤ Real.exp q := by simpa only [Nat.cast_one] using Real.one_le_exp hq
  have hc (i j k : M.PositivePolynomialBasisIndex) :
      rationalLogHeight (lieStructureConstants (M.positivePolynomialBasis p) i j k) ≤ q := by
    have h := hE.2.2.1 ((Fintype.equivFin _) i) ((Fintype.equivFin _) j) ((Fintype.equivFin _) k)
    simpa only [positivePolynomialModel, positivePolynomialFinBasis, lieStructureConstants_reindex,
      Equiv.symm_apply_apply] using h
  refine ⟨⟨(Nat.cast_le.mpr (M.positivePolynomialDownsetIndex_card_le J)).trans hE.1,
    hE.2.1, ?_, ?_⟩, ?_⟩
  · intro i j k
    change rationalLogHeight (lieStructureConstants (M.positivePolynomialDownsetFinBasis J hJ p) i j k) ≤ q
    rw [positivePolynomialDownsetFinBasis, lieStructureConstants_reindex,
      M.positivePolynomialDownsetBasis_structure]
    exact hc _ _ _
  · intro i j k
    exact rationalLogHeight_le_of_height
      (M.positivePolynomialDownsetFinBasis_degree_height J hJ p (i.val + 1) j k) hone
  · intro a j k
    exact rationalLogHeight_le_of_height
      (M.positivePolynomialDownsetFinBasis_multidegree_height J hJ p (fun i => (a i).val) j k) hone

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem positivePolynomialEvaluation_metric_bound {p q : ℝ} (hM : M.ComplexityLE p)
    (hpq : p ≤ q) (hdim : (Fintype.card M.PositivePolynomialBasisIndex : ℝ) ≤ q) :
    (coordinateLipschitzBound d (Fintype.card M.PositivePolynomialBasisIndex) ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp ((q + 3) ^ 2) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hq : 0 ≤ q := hp.trans hpq
  have hH : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (q + 1) :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr (by linarith))
  have h := coordinateLipschitzBound_le_exp d (Fintype.card M.PositivePolynomialBasisIndex)
    ⌈Real.exp p⌉₊ (p := q + 1) (by linarith) (by linarith [hM.1.1]) (by linarith) hH
  have heq : q + 1 + 2 = q + 3 := by ring
  simpa only [heq] using h

noncomputable def positivePolynomialEvaluationCosetMap (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (hmap : M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation)) :
    (M.positivePolynomialModel p B hB hstable).Space → D.Space :=
  cosetMap _ _
    (realificationMap (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation)
    (realificationMap_subgroup M.filtration.positivePolynomialEvaluation _ _ hmap)

theorem positivePolynomialEvaluationCosetMap_mk (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (hmap : M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation)) (g) :
    M.positivePolynomialEvaluationCosetMap p B hB hstable hmap (QuotientGroup.mk g) =
      QuotientGroup.mk (realificationMap
        (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation g) := rfl

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
  [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]

theorem positivePolynomialEvaluationCosetMap_lipschitz {p : ℝ} (hM : M.ComplexityLE p)
    (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B)
    (hmap : M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation)) :
    letI := (M.positivePolynomialModel p B hB hstable).metricSpace
    letI := D.metricSpace
    LipschitzWith (coordinateLipschitzBound d (Fintype.card M.PositivePolynomialBasisIndex) ⌈Real.exp p⌉₊)
      (M.positivePolynomialEvaluationCosetMap p B hB hstable hmap) := by
  let := (M.positivePolynomialModel p B hB hstable).metricSpace
  let := D.metricSpace
  have h := lipschitz_realificationMap_quotient
    (M.positivePolynomialModel p B hB hstable).basis D.basis
    M.filtration.positivePolynomialEvaluation
    (M.positivePolynomialLattice p B hstable) D.lattice hmap B D.grid hB D.grid_pos
    (M.positivePolynomialModel p B hB hstable).outer_grid D.outer_grid ⌈Real.exp p⌉₊
    (fun k i => M.positivePolynomialFinBasis_evaluation_height hM i k)
  simp only [Fintype.card_fin] at h
  convert h using 1
  rfl

theorem exists_positivePolynomial_observable_pullback {p q : ℝ} (hM : M.ComplexityLE p)
    (hpq : p ≤ q) (hdim : (Fintype.card M.PositivePolynomialBasisIndex : ℝ) ≤ q)
    (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B)
    (hmap : M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation))
    (u : D.Space → ℂ) (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp q)
    (hu : letI := D.metricSpace; LipschitzWith ℓ u) :
    ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp (q + (q + 3) ^ 2) ∧
      (letI := (M.positivePolynomialModel p B hB hstable).metricSpace
       LipschitzWith K (u ∘ M.positivePolynomialEvaluationCosetMap p B hB hstable hmap)) := by
  let := D.metricSpace
  let := (M.positivePolynomialModel p B hB hstable).metricSpace
  let C := coordinateLipschitzBound d (Fintype.card M.PositivePolynomialBasisIndex) ⌈Real.exp p⌉₊
  refine ⟨ℓ * C, ?_, hu.comp (M.positivePolynomialEvaluationCosetMap_lipschitz hM B hB hstable hmap)⟩
  calc
    (ℓ * C : ℝ≥0) ≤ Real.exp q * Real.exp ((q + 3) ^ 2) :=
      mul_le_mul hℓ (M.positivePolynomialEvaluation_metric_bound hM hpq hdim)
        C.coe_nonneg (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped BigOperators

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PositivePolynomialVectorOrbit
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialMonomial (a : σ →₀ ℕ) (ha : a ≠ 0) :
    F.layer (fun i => a i) →ₗ[ℚ] F.positivePolynomialAlgebra where
  toFun x := ⟨monomial a x.val, F.monomial_mem_adaptedSubmodule a x.property, by
    classical
    simp [ha]⟩
  map_add' x y := by
    apply Subtype.ext
    change monomial a (x.val + y.val) = monomial a x.val + monomial a y.val
    simp [monomial, TensorProduct.tmul_add]
  map_smul' c x := by
    apply Subtype.ext
    change monomial a (c • x.val) = c • monomial a x.val
    simp [monomial]

theorem positivePolynomialMonomial_mem_layer (a : σ →₀ ℕ) (ha : a ≠ 0)
    (x : F.layer (fun i => a i)) :
    F.positivePolynomialMonomial a ha x ∈ F.positivePolynomialMultidegreeLayer (fun i => a i) := by
  change monomial a x.val ∈ coefficientSupport {b : σ →₀ ℕ | (fun i => a i) ≤ fun i => b i}
  apply monomial_mem_coefficientSupport
  exact fun i => le_rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realPositivePolynomialMap_monomial (a : σ →₀ ℕ) (ha : a ≠ 0)
    (x : ℝ ⊗[ℚ] F.layer (fun i => a i)) :
    F.realPositivePolynomialMap ((F.positivePolynomialMonomial a ha).baseChange ℝ x) =
      monomial a ((F.layer (fun i => a i)).subtype.baseChange ℝ x) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => first | (simp; done) | (simp [monomial]; done) | exact (map_zero _).symm
  | tmul r y =>
    apply coefficients.injective
    ext b
    rw [LinearMap.baseChange_tmul, F.realPositivePolynomialMap_coefficient_tmul]
    change r ⊗ₜ[ℚ] coefficients (monomial a y.val) b =
      coefficients (monomial a (r ⊗ₜ[ℚ] y.val)) b
    by_cases hab : a = b
    · subst b
      simp
    · simp [hab]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    simp [monomial, TensorProduct.tmul_add]

theorem realPositivePolynomialMonomial_mem_layer (a : σ →₀ ℕ) (ha : a ≠ 0)
    (x : ℝ ⊗[ℚ] F.layer (fun i => a i)) :
    (F.positivePolynomialMonomial a ha).baseChange ℝ x ∈
      (F.positivePolynomialMultidegreeLayer (fun i => a i)).baseChange ℝ := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    rw [LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem r (F.positivePolynomialMonomial_mem_layer a ha y)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem exists_realPositivePolynomial_component
    (p : F.realification.positivePolynomialAlgebra) (a : σ →₀ ℕ) :
    ∃ x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra,
      F.realPositivePolynomialTensor x = F.realification.positivePolynomialComponent a p ∧
      x ∈ (F.positivePolynomialMultidegreeLayer (fun i => a i)).baseChange ℝ := by
  classical
  by_cases ha : a = 0
  · subst a
    refine ⟨0, ?_, Submodule.zero_mem _⟩
    rw [map_zero]
    exact ((F.realification.positivePolynomialComponent_eq_zero 0 p).mpr p.property.2).symm
  · let Q := F.layer (fun i => a i)
    let c : Q.baseChange ℝ := ⟨coefficients p.val a, p.property.1 a⟩
    let y : ℝ ⊗[ℚ] Q := (realificationSubmoduleEquiv Q).symm c
    have hy : Q.subtype.baseChange ℝ y = c.val :=
      congrArg Subtype.val ((realificationSubmoduleEquiv Q).apply_symm_apply c)
    refine ⟨(F.positivePolynomialMonomial a ha).baseChange ℝ y, ?_,
      F.realPositivePolynomialMonomial_mem_layer a ha y⟩
    apply Subtype.ext
    change F.realPositivePolynomialMap ((F.positivePolynomialMonomial a ha).baseChange ℝ y) =
      monomial a (coefficients p.val a)
    rw [F.realPositivePolynomialMap_monomial, hy]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realPositivePolynomialTensor_mem_layer (a : σ → ℕ)
    {x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra}
    (hx : x ∈ (F.positivePolynomialMultidegreeLayer a).baseChange ℝ) :
    F.realPositivePolynomialTensor x ∈ F.realification.positivePolynomialMultidegreeLayer a := by
  let U := F.positivePolynomialMultidegreeLayer a
  have hbase (z : ℝ ⊗[ℚ] U) :
      F.realPositivePolynomialTensor (U.subtype.baseChange ℝ z) ∈
        F.realification.positivePolynomialMultidegreeLayer a := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r p =>
      intro b hb
      change coefficients (F.realPositivePolynomialMap
        (U.subtype.baseChange ℝ (r ⊗ₜ[ℚ] p))) b = 0
      rw [LinearMap.baseChange_tmul, F.realPositivePolynomialMap_coefficient_tmul]
      have hz : coefficients p.val.val b = 0 := p.property b hb
      change r ⊗ₜ[ℚ] coefficients p.val.val b = 0
      rw [hz, TensorProduct.tmul_zero]
    | add z w hz hw =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hz hw
  let z := (realificationSubmoduleEquiv U).symm ⟨x, hx⟩
  have hz : U.subtype.baseChange ℝ z = x :=
    congrArg Subtype.val ((realificationSubmoduleEquiv U).apply_symm_apply ⟨x, hx⟩)
  exact hz ▸ hbase z

theorem exists_realPositivePolynomial_preimage_layer (a : σ → ℕ)
    (p : F.realification.positivePolynomialAlgebra)
    (hp : p ∈ F.realification.positivePolynomialMultidegreeLayer a) :
    ∃ x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra,
      x ∈ (F.positivePolynomialMultidegreeLayer a).baseChange ℝ ∧
      F.realPositivePolynomialTensor x = p := by
  classical
  choose y hy hylayer using F.exists_realPositivePolynomial_component p
  refine ⟨∑ b ∈ (coefficients p.val).support, y b, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro b hb
    have hab : a ≤ fun i => b i := by
      by_contra h
      have hz : coefficients p.val b = 0 := hp b h
      exact (Finsupp.mem_support_iff.mp hb) hz
    exact Submodule.baseChange_mono ℝ (F.positivePolynomialMultidegreeLayer_antitone hab) (hylayer b)
  · rw [map_sum]
    simp_rw [hy]
    exact F.realification.sum_positivePolynomialComponent p

theorem realPositivePolynomialTensor_surjective : Function.Surjective F.realPositivePolynomialTensor := by
  intro p
  obtain ⟨x, _, hx⟩ := F.exists_realPositivePolynomial_preimage_layer 0 p (by
    rw [F.realification.positivePolynomialMultidegreeLayer_zero]
    trivial)
  exact ⟨x, hx⟩

noncomputable def realPositivePolynomialEquiv :
    (ℝ ⊗[ℚ] F.positivePolynomialAlgebra) ≃ₗ⁅ℚ⁆ F.realification.positivePolynomialAlgebra :=
  LieEquiv.ofBijective F.realPositivePolynomialTensor
    ⟨F.realPositivePolynomialTensor_injective, F.realPositivePolynomialTensor_surjective⟩

theorem realPositivePolynomialEquiv_mem_layer (a : σ → ℕ)
    (x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra) :
    F.realPositivePolynomialEquiv x ∈ F.realification.positivePolynomialMultidegreeLayer a ↔
      x ∈ (F.positivePolynomialMultidegreeLayer a).baseChange ℝ := by
  constructor
  · intro hx
    obtain ⟨y, hy, heq⟩ := F.exists_realPositivePolynomial_preimage_layer a _ hx
    have hxy : y = x := F.realPositivePolynomialTensor_injective heq
    exact hxy ▸ hy
  · exact F.realPositivePolynomialTensor_mem_layer a

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realPositivePolynomialOrbitTransport
    (g : F.realification.positivePolynomialMultidegree.PolynomialOrbit) :
    F.positivePolynomialMultidegree.realification.PolynomialOrbit :=
  F.positivePolynomialMultidegree.realification.polynomialOrbitOfLog
    (VectorPolynomial.map F.realPositivePolynomialEquiv.symm.toLinearMap
      (PolynomialOrbit.log F.realification.positivePolynomialMultidegree g)) (by
        intro a
        rw [coefficients_map]
        change F.realPositivePolynomialEquiv.symm _ ∈
          (F.positivePolynomialMultidegreeLayer (fun i => a i)).baseChange ℝ
        apply (F.realPositivePolynomialEquiv_mem_layer (fun i => a i) _).mp
        rw [F.realPositivePolynomialEquiv.apply_symm_apply]
        exact PolynomialOrbit.adapted F.realification.positivePolynomialMultidegree g a)

theorem realPositivePolynomialOrbitTransport_eval
    (g : F.realification.positivePolynomialMultidegree.PolynomialOrbit) (x : σ → ℤ) :
    NilpotentLieBCHGroup.mapOfSteps F.realPositivePolynomialEquiv.toLieHom
        (F.positivePolynomialMultidegree.realification.polynomialOrbitEval x
          (F.realPositivePolynomialOrbitTransport g)) =
      F.realification.positivePolynomialMultidegree.polynomialOrbitEval x g := by
  apply NilpotentLieBCHGroup.ext
  change F.realPositivePolynomialEquiv
      (eval (fun i => (x i : ℚ)) (VectorPolynomial.map F.realPositivePolynomialEquiv.symm.toLinearMap
        (PolynomialOrbit.log F.realification.positivePolynomialMultidegree g))) = _
  rw [eval_map]
  exact F.realPositivePolynomialEquiv.apply_symm_apply _

theorem realPositivePolynomialOrbitTransport_zero
    (g : F.realification.positivePolynomialMultidegree.PolynomialOrbit)
    (hg : F.realification.positivePolynomialMultidegree.polynomialOrbitEval 0 g = 1) :
    F.positivePolynomialMultidegree.realification.polynomialOrbitEval 0
      (F.realPositivePolynomialOrbitTransport g) = 1 := by
  apply NilpotentLieBCHGroup.mapOfSteps_injective F.realPositivePolynomialEquiv.toLieHom
    F.realPositivePolynomialEquiv.injective
  rw [map_one, F.realPositivePolynomialOrbitTransport_eval, hg]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem exists_realPositivePolynomial_orbit (g : F.realification.PolynomialOrbit)
    (hg : F.realification.polynomialOrbitEval 0 g = 1) :
    ∃ h : F.positivePolynomialMultidegree.realification.PolynomialOrbit,
      F.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
      ∀ x, NilpotentLieBCHGroup.realificationMap
          (hnil := F.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
          (hM := F.ordinary.lowerCentralSeries_eq_bot) F.positivePolynomialEvaluation
          (F.positivePolynomialMultidegree.realification.polynomialOrbitEval x h) =
        F.realification.polynomialOrbitEval x g := by
  obtain ⟨q, hqzero, hq⟩ := F.realification.exists_positivePolynomial_orbit g hg
  refine ⟨F.realPositivePolynomialOrbitTransport q,
    F.realPositivePolynomialOrbitTransport_zero q hqzero, ?_⟩
  intro x
  apply NilpotentLieBCHGroup.ext
  have htransport := congrArg NilpotentLieBCHGroup.coord
    (F.realPositivePolynomialOrbitTransport_eval q x)
  have hprojection := congrArg NilpotentLieBCHGroup.coord (hq x)
  calc
    _ = F.realification.positivePolynomialEvaluation (F.realPositivePolynomialEquiv
        (F.positivePolynomialMultidegree.realification.polynomialOrbitEval x
          (F.realPositivePolynomialOrbitTransport q)).coord) :=
      (F.realPositivePolynomialEvaluation_commute _).symm
    _ = F.realification.positivePolynomialEvaluation
        (F.realification.positivePolynomialMultidegree.polynomialOrbitEval x q).coord :=
      congrArg F.realification.positivePolynomialEvaluation htransport
    _ = _ := hprojection

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)

theorem positivePolynomialDownset_projection_height (p : ℝ) (i j) :
    RationalHeightLE ((M.positivePolynomialDownsetFinBasis J hJ p).repr
      (lieQuotientMap (restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ)
        (M.positivePolynomialFinBasis p j)) i) 1 := by
  rw [positivePolynomialDownsetFinBasis, Basis.repr_reindex_apply,
    positivePolynomialFinBasis, Basis.reindex_apply]
  change RationalHeightLE ((M.filtration.positivePolynomialDownsetBasis
    (M.positiveCoefficientBasis p) J hJ).repr
      (lieQuotientMap _ (M.filtration.positivePolynomialBasis (M.positiveCoefficientBasis p) _)) _) 1
  rw [M.filtration.positivePolynomialDownsetBasis_repr]
  exact basis_repr_height_one _ _ _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial NilpotentLieBCHGroup

variable {α σ L : Type*} [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
  {bound : σ → ℕ} (M : D.MultidegreeStructure bound)
  (J : α → Set (σ →₀ ℕ)) [∀ a, DecidablePred (· ∈ J a)] (hJ : ∀ a, IsLowerSet (J a))

noncomputable def positivePolynomialQuotientProductModel (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) :=
  RationalFilteredNilmanifold.pi (fun a => M.positivePolynomialDownsetModel (J a) (hJ a) p B hB hstable)

omit [DecidableEq α] in
theorem positivePolynomialQuotientProductModel_geometry (p q : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (hα : (Fintype.card α : ℝ) ≤ q)
    (hE : (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q) :
    (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).GeometryComplexityLE ((q + 2) ^ 2) :=
  pi_geometry _ ((Nat.cast_nonneg _).trans hE.1) hα
    (fun a => (M.positivePolynomialDownsetModel_complexity (J a) (hJ a) p q B hB hstable hE).1)

omit [DecidableEq α] in
theorem positivePolynomialQuotientProductModel_map_height (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) (i j) :
    RationalHeightLE ((M.positivePolynomialQuotientProductModel J hJ p B hB hstable).basis.repr
      (M.filtration.positivePolynomialQuotientProductMap J hJ (M.positivePolynomialFinBasis p j)) i) 1 := by
  change RationalHeightLE ((pi (fun a => M.positivePolynomialDownsetModel (J a) (hJ a) p B hB hstable)).basis.repr _ i) 1
  rw [productFinBasis_repr]
  exact M.positivePolynomialDownset_projection_height _ _ p _ j

theorem positivePolynomialQuotientProductModel_lattice_cover (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → M.filtration.layer (fun i => c i) = ⊥) :
    (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).realLattice ⊓
      (M.filtration.positivePolynomialQuotientProductRealMap J hJ).range ≤
        (M.positivePolynomialModel p B hB hstable).realLattice.map
          (M.filtration.positivePolynomialQuotientProductRealMap J hJ) := by
  exact M.filtration.positivePolynomialQuotientProduct_lattice_cover J hJ
    (M.positiveCoefficientBasis p) hcover (M.positivePolynomialLattice p B hstable) B
    (M.positivePolynomialLattice_coordinates p B hstable)

omit [DecidableEq σ] [∀ a, DecidablePred (· ∈ J a)] in
theorem positivePolynomialQuotientProductModel_map_injective (p : ℝ)
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → M.filtration.layer (fun i => c i) = ⊥) :
    Function.Injective (M.filtration.positivePolynomialQuotientProductRealMap J hJ) :=
  M.filtration.positivePolynomialQuotientProductRealMap_injective J hJ (M.positiveCoefficientBasis p) hcover

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J)

noncomputable def positivePolynomialDownsetOrbit
    (g : F.positivePolynomialMultidegree.realification.PolynomialOrbit) :
    (F.positivePolynomialDownsetQuotient J hJ).realification.PolynomialOrbit :=
  F.positivePolynomialMultidegree.realQuotientMultidegreeOrbit
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ) g

theorem positivePolynomialDownsetOrbit_eval
    (g : F.positivePolynomialMultidegree.realification.PolynomialOrbit) (x : σ → ℤ) :
    (F.positivePolynomialDownsetQuotient J hJ).realification.polynomialOrbitEval x
      (F.positivePolynomialDownsetOrbit J hJ g) =
        F.positivePolynomialMultidegree.realQuotientMultidegreeMap
          (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ)
          (F.positivePolynomialMultidegree.realification.polynomialOrbitEval x g) :=
  F.positivePolynomialMultidegree.realQuotientMultidegreeOrbit_eval _ g x

end Erdos3.MultidegreeLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open VectorPolynomial

variable {α σ L : Type*} [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
  {bound : σ → ℕ} (M : D.MultidegreeStructure bound)
  (J : α → Set (σ →₀ ℕ)) [∀ a, DecidablePred (· ∈ J a)] (hJ : ∀ a, IsLowerSet (J a))

theorem positivePolynomialProductProjection_mk (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (g : M.filtration.positivePolynomialMultidegree.realification.Group) (a : α) :
    productProjection (fun a => M.positivePolynomialDownsetModel (J a) (hJ a) p B hB hstable) a
      (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ g)) =
        QuotientGroup.mk (M.filtration.positivePolynomialMultidegree.realQuotientMultidegreeMap
          (restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)) g) := by
  change QuotientGroup.mk (realBCHPiEquiv
    (fun a => (M.filtration.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary)
      (M.filtration.positivePolynomialQuotientProductRealMap J hJ g) a) = _
  rw [M.filtration.positivePolynomialQuotientProductRealMap_component]
  rfl

theorem positivePolynomialProductProjection_orbit (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (g : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit)
    (x : σ → ℤ) (a : α) :
    productProjection (fun a => M.positivePolynomialDownsetModel (J a) (hJ a) p B hB hstable) a
      (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ
        (M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval x g))) =
      QuotientGroup.mk ((M.filtration.positivePolynomialDownsetQuotient (J a) (hJ a)).realification.polynomialOrbitEval x
        (M.filtration.positivePolynomialDownsetOrbit (J a) (hJ a) g)) := by
  rw [M.positivePolynomialProductProjection_mk,
    M.filtration.positivePolynomialDownsetOrbit_eval]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_positivePolynomial_product_reconstruction (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α σ L : Type*} [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ a, DecidablePred (· ∈ J a)] (hJ : ∀ a, IsLowerSet (J a))
      [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [T2Space (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      (p q : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
      (∑ i, bound i) = t → (Fintype.card α : ℝ) ≤ q →
      (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q →
      (∀ c, c ≠ 0 → (∀ a, c ∉ J a) → M.filtration.layer (fun i => c i) = ⊥) →
      ∀ (u : (M.positivePolynomialModel p B hB hstable).Space → ℂ) (ℓ : ℝ≥0),
        (ℓ : ℝ) ≤ Real.exp q →
        (letI := (M.positivePolynomialModel p B hB hstable).metricSpace; LipschitzWith ℓ u) →
        (∀ x, ‖u x‖ ≤ 1) →
        ∃ (v : (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).Space → ℂ) (K : ℝ≥0),
          (K : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
          (letI := (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).metricSpace;
            LipschitzWith K v) ∧ (∀ y, ‖v y‖ ≤ 2) ∧
          ∀ x, v (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ x)) =
            u (QuotientGroup.mk x) := by
  obtain ⟨a, _, hrec⟩ := exists_native_complex_reconstruction t
  let P : Polynomial ℕ := (Polynomial.X + (Polynomial.X + 2) ^ 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro α σ L _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _ _ _ _ _ p q B hB hstable ht hα hX hcover u ℓ hℓ hu hub
  subst t
  let X := M.positivePolynomialModel p B hB hstable
  let Y := M.positivePolynomialQuotientProductModel J hJ p B hB hstable
  let r := q + (q + 2) ^ 2
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hX.1
  have hqr : q ≤ r := le_add_of_nonneg_right (sq_nonneg _)
  have hrr : (q + 2) ^ 2 ≤ r := le_add_of_nonneg_left hq
  have hr : 0 ≤ r := hq.trans hqr
  have hY := M.positivePolynomialQuotientProductModel_geometry J hJ p q B hB hstable hα hX
  have hmap : ∀ i j, rationalLogHeight
      (Y.basis.repr (M.filtration.positivePolynomialQuotientProductMap J hJ (X.basis j)) i) ≤ r := by
    intro i j
    exact rationalLogHeight_le_of_height
      (M.positivePolynomialQuotientProductModel_map_height J hJ p B hB hstable i j)
      (by simpa only [Nat.cast_one] using Real.one_le_exp hr)
  have hker : ∀ k ∈ (M.filtration.positivePolynomialQuotientProductRealMap J hJ).ker, ∀ x,
      u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x) := by
    intro k hk x
    have hk1 : k = 1 := M.positivePolynomialQuotientProductModel_map_injective J hJ p hcover
      ((MonoidHom.mem_ker.mp hk).trans (map_one _).symm)
    rw [hk1, one_mul]
  obtain ⟨v, K, hK, hv, hb, heval⟩ := hrec X Y
    (M.filtration.positivePolynomialQuotientProductMap J hJ) hr
    (hX.mono X hqr) (hY.mono Y hrr) hmap
    (M.positivePolynomialQuotientProductModel_lattice_cover J hJ p B hB hstable hcover)
    u ℓ (hℓ.trans (Real.exp_le_exp.mpr hqr)) hu hub hker
  have hcost : (r + a) ^ a ≤ (q + C) ^ C := by
    simpa [P, r, Polynomial.eval₂_pow] using hbudget q hq
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv, hb, heval⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped BigOperators

variable {α σ L : Type*} [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
  {bound : σ → ℕ} (M : D.MultidegreeStructure bound)
  (J : α → Set (σ →₀ ℕ)) [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped BigOperators

variable {I α σ L : Type*} [Fintype I] [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
  {bound : σ → ℕ} (M : D.MultidegreeStructure bound)
  (J : α → Set (σ →₀ ℕ)) [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))

theorem positivePolynomial_vector_error_of_lift (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (g : M.filtration.realification.PolynomialOrbit)
    (h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit)
    (hproj : ∀ x, realificationMap
      (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation
      (M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval x h) =
        M.filtration.realification.polynomialOrbitEval x g)
    (n : α → ℕ)
    (ψ : ∀ i, Fin (n i) → (M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable).Space → ℝ)
    (c : (∀ i, Fin (n i)) → EuclideanSpace ℂ I) (u : I → D.Space → ℂ) (epsilon : ℝ)
    (happrox : ∀ y, ‖(WithLp.toLp 2 (fun k => u k (QuotientGroup.mk (realificationMap
        (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation y))) : EuclideanSpace ℂ I) -
      ∑ j, (∏ i, (ψ i (j i) (productProjection
        (fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable) i
        (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ y))) : ℂ)) • c j‖ ≤ epsilon) :
    ∀ x, ‖(WithLp.toLp 2 (fun k => u k (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g))) : EuclideanSpace ℂ I) -
      ∑ j, (∏ i, (ψ i (j i) (QuotientGroup.mk
        ((M.filtration.positivePolynomialDownsetQuotient (J i) (hJ i)).realification.polynomialOrbitEval x
          (M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h))) : ℂ)) • c j‖ ≤ epsilon := by
  intro x
  have hx := happrox (M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval x h)
  rw [hproj x] at hx
  simpa only [M.positivePolynomialProductProjection_orbit] using hx

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PositivePolynomialFactorNiltests
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct NNReal

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)
  [TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
    VectorPolynomial.restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
    VectorPolynomial.restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
    VectorPolynomial.restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ))]
  [T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
    VectorPolynomial.restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ))]
  (p : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B)
  (g : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit)
  (ψ : (M.positivePolynomialDownsetModel J hJ p B hB hstable).Space → ℝ)
  (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (K : ℝ≥0)
  (hLip : letI := (M.positivePolynomialDownsetModel J hJ p B hB hstable).metricSpace;
    LipschitzWith K ψ)

noncomputable def positivePolynomialFactorNiltest :
    (M.positivePolynomialDownsetModel J hJ p B hB hstable).Niltest (fun _ : σ => 1) :=
  (M.positivePolynomialDownsetModel J hJ p B hB hstable).sectionNiltest
    ((M.positivePolynomialDownsetModelMultidegree J hJ p B hB hstable).orbitToOrdinary
      (M.filtration.positivePolynomialDownsetOrbit J hJ g))
    (fun z (_ : Unit) => ψ z) (fun z _ => hψ z) K (fun _ => hLip) (some ())

theorem positivePolynomialFactorNiltest_unit_interval :
    (M.positivePolynomialFactorNiltest J hJ p B hB hstable g ψ hψ K hLip).UnitIntervalValued :=
  (M.positivePolynomialDownsetModel J hJ p B hB hstable).sectionNiltest_unit_interval _ _ _ _ _ _

theorem positivePolynomialFactorNiltest_eval (x : σ → ℤ) :
    (M.positivePolynomialFactorNiltest J hJ p B hB hstable g ψ hψ K hLip).eval x =
      (ψ (QuotientGroup.mk ((M.filtration.positivePolynomialDownsetQuotient J hJ).realification.polynomialOrbitEval x
        (M.filtration.positivePolynomialDownsetOrbit J hJ g))) : ℂ) := by
  exact congrArg (fun z : (M.positivePolynomialDownsetModel J hJ p B hB hstable).RealGroup =>
    (ψ (QuotientGroup.mk z) : ℂ))
    ((M.positivePolynomialDownsetModelMultidegree J hJ p B hB hstable).orbitToOrdinary_eval
      (M.filtration.positivePolynomialDownsetOrbit J hJ g) x)

theorem positivePolynomialFactorNiltest_complexity {q : ℝ}
    (hE : (M.positivePolynomialDownsetModel J hJ p B hB hstable).GeometryComplexityLE q)
    (hK : (K : ℝ) ≤ Real.exp q) :
    (M.positivePolynomialFactorNiltest J hJ p B hB hstable g ψ hψ K hLip).ComplexityLE (q + 2) := by
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hE.1
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog : Real.log (3 + (K : ℝ)) ≤ q + 2 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    rw [Real.exp_add]
    nlinarith [Real.one_le_exp hq,
      mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg q)]
  exact (M.positivePolynomialDownsetModel J hJ p B hB hstable).sectionNiltest_complexityLE
    _ _ _ _ _ _ (hE.mono _ (by linarith)) hlog

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CanonicalPositivePolynomialSplitting
namespace OAI

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_positivePolynomial_source_reconstruction (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α σ L : Type*} [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ a, DecidablePred (· ∈ J a)] (hJ : ∀ a, IsLowerSet (J a))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [T2Space (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      (p q : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
      (∑ i, bound i) = t → M.ComplexityLE p → p ≤ q → (Fintype.card α : ℝ) ≤ q →
      (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q →
      M.positivePolynomialLattice p B hstable ≤
        D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) →
      (∀ c, c ≠ 0 → (∀ a, c ∉ J a) → M.filtration.layer (fun i => c i) = ⊥) →
      ∀ (u : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp q →
        (letI := D.metricSpace; LipschitzWith ℓ u) → (∀ x, ‖u x‖ ≤ 1) →
        ∃ (v : (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).Space → ℂ) (K : ℝ≥0),
          (K : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
          (letI := (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).metricSpace;
            LipschitzWith K v) ∧ (∀ y, ‖v y‖ ≤ 2) ∧
          ∀ x, v (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ x)) =
            u (QuotientGroup.mk (realificationMap
              (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
              (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation x)) := by
  obtain ⟨a, _, hrec⟩ := exists_positivePolynomial_product_reconstruction t
  let P : Polynomial ℕ := (Polynomial.X + (Polynomial.X + 3) ^ 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro α σ L _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _ _ _ _ _ _ _ _ _ p q B hB hstable
    ht hM hpq hα hX hmap hcover u ℓ hℓ hu hub
  let r := q + (q + 3) ^ 2
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hX.1
  have hqr : q ≤ r := le_add_of_nonneg_right (sq_nonneg _)
  let u₀ := u ∘ M.positivePolynomialEvaluationCosetMap p B hB hstable hmap
  obtain ⟨K₀, hK₀, hu₀⟩ := M.exists_positivePolynomial_observable_pullback hM hpq hX.1
    B hB hstable hmap u ℓ hℓ hu
  have hub₀ : ∀ x, ‖u₀ x‖ ≤ 1 := fun x => hub _
  obtain ⟨v, K, hK, hv, hb, heval⟩ := hrec M J hJ p r B hB hstable ht (hα.trans hqr)
    (hX.mono _ hqr) hcover u₀ K₀ hK₀ hu₀ hub₀
  have hcost : (r + a) ^ a ≤ (q + C) ^ C := by
    simpa [P, r, Polynomial.eval₂_pow] using hbudget q hq
  refine ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv, hb, ?_⟩
  intro x
  simpa only [u₀, Function.comp_apply, M.positivePolynomialEvaluationCosetMap_mk] using heval x

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_positivePolynomial_factor_approximation (t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α σ L : Type*} [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [T2Space (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      (p q : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
      (∑ i, bound i) = t → M.ComplexityLE p → p ≤ q → (Fintype.card α : ℝ) ≤ q →
      (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q →
      M.positivePolynomialLattice p B hstable ≤ D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) →
      (∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥) →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((q + 2) ^ a) →
      let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable
      letI : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((q + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((q + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (E i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧ (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ (u : D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp q →
              (letI := D.metricSpace; LipschitzWith ell u) → (∀ x, ‖u x‖ ≤ 1) →
              ∃ c : (∀ i, Fin (n i)) → ℂ, (∀ j, ‖c j‖ ≤ 2) ∧
                ∀ x, ‖u (QuotientGroup.mk (realificationMap
                    (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
                    (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation x)) -
                  ∑ j, (∏ i, (ψ i (j i) (productProjection E i
                    (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ x))) : ℂ)) * c j‖ ≤ epsilon := by
  obtain ⟨b, _, hrec⟩ := exists_positivePolynomial_source_reconstruction t
  obtain ⟨c, _, happ⟩ := exists_controlled_native_product_approximation t a b
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C b + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro α σ L _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    p q B hB hstable ht hM hpq hα hX hmap hcover epsilon hepsilon hscale
  subst t
  let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  let := (pi E).metricSpace
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hX.1
  let R := q + b
  have hqR : q ≤ R := le_add_of_nonneg_right (Nat.cast_nonneg b)
  have hR : 0 ≤ R := hq.trans hqR
  have hscaleR : 1 / epsilon ≤ Real.exp ((R + 2) ^ a) :=
    hscale.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) a))
  obtain ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, happrox⟩ := happ E hR (hα.trans hqR)
    (fun i => ((M.positivePolynomialDownsetModel_complexity (J i) (hJ i) p q B hB hstable hX).1).mono (E i) hqR)
    hepsilon hscaleR
  have hcost : (R + c) ^ c ≤ (q + C) ^ C := by
    simpa [P, R, Polynomial.eval₂_pow] using hbudget q hq
  have hexp := Real.exp_le_exp.mpr hcost
  refine ⟨n, hn, fun i => (hnb i).trans hexp, hcount.trans hexp,
    K, fun i => (hKb i).trans hexp, ψ, hunit, hsum, hLip, ?_⟩
  intro u ell hell hu hub
  obtain ⟨v, Kv, hKv, hv, hvb, heval⟩ := hrec M J hJ p q B hB hstable rfl hM hpq hα hX hmap hcover u ell hell hu hub
  have hKvR : (Kv : ℝ) ≤ Real.exp ((R + 2) ^ b) :=
    hKv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hR (by linarith) b))
  obtain ⟨coeff, hcoeff, herr⟩ := happrox v Kv hKvR hv hvb
  refine ⟨coeff, hcoeff, fun x => ?_⟩
  have h := herr (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ x))
  convert h using 1
  congr 2
  exact (heval x).symm

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_positivePolynomial_vector_factor_approximation (t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I α σ L : Type*} [Fintype I] [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [T2Space (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      (p q : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
      (∑ i, bound i) = t → M.ComplexityLE p → p ≤ q → (Fintype.card α : ℝ) ≤ q →
      (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q →
      M.positivePolynomialLattice p B hstable ≤ D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) →
      (∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥) →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((q + 2) ^ a) →
      (Fintype.card I : ℝ) ≤ Real.exp q →
      let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable
      letI : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((q + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((q + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (E i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧ (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ (u : I → D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp q →
              (letI := D.metricSpace; ∀ k, LipschitzWith ell (u k)) →
              (∀ k x, ‖u k x‖ ≤ 1) →
              ∃ c : (∀ i, Fin (n i)) → EuclideanSpace ℂ I,
                (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ Real.exp (q + 2)) ∧
                ∀ x, ‖(WithLp.toLp 2 (fun k => u k (QuotientGroup.mk (realificationMap
                    (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
                    (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation x))) : EuclideanSpace ℂ I) -
                  ∑ j, (∏ i, (ψ i (j i) (productProjection E i
                    (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ x))) : ℂ)) • c j‖ ≤ epsilon := by
  obtain ⟨C, hC, happ⟩ := exists_positivePolynomial_factor_approximation t (a + 1)
  refine ⟨C, hC, ?_⟩
  intro I α σ L _ _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    p q B hB hstable ht hM hpq hα hX hmap hcover epsilon hepsilon hscale hI
  classical
  let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hX.1
  obtain ⟨hprecision, hprecision_scale⟩ := vector_approximation_precision a hq hI hepsilon hscale
  obtain ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, happrox⟩ :=
    happ M J hJ p q B hB hstable ht hM hpq hα hX hmap hcover
      (epsilon / (Fintype.card I + 1 : ℝ)) hprecision hprecision_scale
  refine ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, ?_⟩
  intro u ell hell hu hub
  choose coeff hcoeff herr using (fun k => happrox (u k) ell hell (hu k) (hub k))
  let c (j : ∀ i, Fin (n i)) : EuclideanSpace ℂ I := WithLp.toLp 2 (fun k => coeff k j)
  have hc : ∀ j k, ‖c j k‖ ≤ 2 := fun j k => hcoeff k j
  refine ⟨c, hc, fun j => euclidean_coefficient_norm_le_exp hq hI (c j) (hc j), ?_⟩
  intro x
  apply euclidean_error_le_of_coordinate_errors _ hepsilon.le
  intro k
  simpa only [PiLp.sub_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, c, WithLp.ofLp_toLp] using herr k x

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_uniform_positivePolynomial_splitting (t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I α σ L : Type*} [Fintype I] [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      [T2Space (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))]
      (p : ℝ), (∑ i, bound i) = t → M.ComplexityLE p →
      (Fintype.card α : ℝ) ≤ p + 2 →
      (∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥) →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      M.filtration.realification.polynomialOrbitEval 0 g = 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      (Fintype.card I : ℝ) ≤ Real.exp p →
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
        (∀ i, (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) p B hB hstable).ComplexityLE ((p + C) ^ C)) ∧
        ∃ h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit,
          M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
          ∃ n : α → ℕ, (∀ i, 0 < n i) ∧
            (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
            (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            ∃ T : ∀ i, Fin (n i) → (M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable).Niltest (fun _ : σ => 1),
              (∀ i j, (T i j).normBound = 1) ∧ (∀ i j, (T i j).UnitIntervalValued) ∧
              (∀ i j, (T i j).ComplexityLE ((p + C) ^ C)) ∧
              (∀ i j, (T i j).orbit =
                (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) p B hB hstable).orbitToOrdinary
                  (M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h)) ∧
              ∀ (u : I → D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
                (letI := D.metricSpace; ∀ k, LipschitzWith ell (u k)) →
                (∀ k x, ‖u k x‖ ≤ 1) →
                ∃ c : (∀ i, Fin (n i)) → EuclideanSpace ℂ I,
                  (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ Real.exp ((p + C) ^ C)) ∧
                  ∀ x, ‖(WithLp.toLp 2 (fun k => u k
                      (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g))) : EuclideanSpace ℂ I) -
                    ∑ j, (∏ i, (T i (j i)).eval x) • c j‖ ≤ epsilon := by
  let hmodels_exists := exists_positivePolynomial_model_uniform t
  let b := hmodels_exists.choose
  have hmodels := hmodels_exists.choose_spec
  let happ_exists := exists_positivePolynomial_vector_factor_approximation t a
  let c := happ_exists.choose
  have happ := happ_exists.choose_spec
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b + 2
  let P : Polynomial ℕ := Q + (Q + Polynomial.C c) ^ c + 2
  let hbudget_exists := exists_natPolynomial_eval_budget P
  let C := hbudget_exists.choose
  have hC : 2 ≤ C := hbudget_exists.choose_spec.1
  have hbudget : ∀ p : ℝ, 0 ≤ p →
      P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C := hbudget_exists.choose_spec.2
  refine ⟨C, hC, ?_⟩
  intro I α σ L _ _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    p ht hM hα hcover g hg epsilon hepsilon hscale hI
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let q := p + (p + b) ^ b + 2
  have hmodel_nonneg : 0 ≤ (p + b) ^ b := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith only [hmodel_nonneg]
  have hq : 0 ≤ q := hp.trans hpq
  have hαq : (Fintype.card α : ℝ) ≤ q := by dsimp [q]; linarith only [hα, hmodel_nonneg]
  have hcost : q + (q + c) ^ c + 2 ≤ (p + C) ^ C := by
    simpa [P, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (q + c) ^ c := by positivity
  have hpower_cost : (q + c) ^ c ≤ (p + C) ^ C := by linarith only [hcost, hq]
  have hq_cost : q + 2 ≤ (p + C) ^ C := by linarith only [hcost, hpow]
  let model := hmodels.2 M ht hM
  let B := model.choose
  let hB : 0 < B := model.choose_spec.choose
  let hstable : M.PositivePolynomialGridStable p B := model.choose_spec.choose_spec.choose
  have hmodel := model.choose_spec.choose_spec.choose_spec.1
  have hmap : M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) :=
    model.choose_spec.choose_spec.choose_spec.2
  have hX : (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q :=
    (hmodel.mono _ (by dsimp [q]; linarith only [hp])).1
  let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  have hE (i) := M.positivePolynomialDownsetModel_complexity (J i) (hJ i) p q B hB hstable hX
  let lift := M.filtration.exists_realPositivePolynomial_orbit g hg
  let h := lift.choose
  have hh := lift.choose_spec.1
  have hproj := lift.choose_spec.2
  have hscaleq : 1 / epsilon ≤ Real.exp ((q + 2) ^ a) :=
    hscale.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith only [hp]) (by linarith only [hpq]) a))
  have hIq : (Fintype.card I : ℝ) ≤ Real.exp q := hI.trans (Real.exp_le_exp.mpr hpq)
  let approximation :=
    happ.2 M J hJ p q B hB hstable ht hM hpq hαq hX hmap hcover epsilon hepsilon hscaleq hIq
  let n := approximation.choose
  have hn := approximation.choose_spec.1
  have hnb := approximation.choose_spec.2.1
  have hcount := approximation.choose_spec.2.2.1
  let constants := approximation.choose_spec.2.2.2
  let K := constants.choose
  have hKb := constants.choose_spec.1
  let factors := constants.choose_spec.2
  let ψ := factors.choose
  have hunit := factors.choose_spec.1
  have hsum := factors.choose_spec.2.1
  have hLip := factors.choose_spec.2.2.1
  have happrox := factors.choose_spec.2.2.2
  let T (i) (j : Fin (n i)) :=
    M.positivePolynomialFactorNiltest (J i) (hJ i) p B hB hstable h (ψ i j) (hunit i j) (K i) (hLip i j)
  have hT (i) (j : Fin (n i)) : (T i j).ComplexityLE ((p + C) ^ C) := by
    have hgeometry := (hE i).1.mono (E i) (le_add_of_nonneg_right hpow)
    have hK : (K i : ℝ) ≤ Real.exp (q + (q + c) ^ c) :=
      (hKb i).trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hq))
    exact (M.positivePolynomialFactorNiltest_complexity (J i) (hJ i) p B hB hstable h
      (ψ i j) (hunit i j) (K i) (hLip i j) hgeometry hK).mono hcost
  refine ⟨B, hB, hstable, fun i => (hE i).mono _ (by linarith only [hq_cost]), h, hh, n, hn,
    fun i => (hnb i).trans (Real.exp_le_exp.mpr hpower_cost),
    hcount.trans (Real.exp_le_exp.mpr hpower_cost), T, fun _ _ => rfl,
    fun i j => M.positivePolynomialFactorNiltest_unit_interval (J i) (hJ i) p B hB hstable h
      (ψ i j) (hunit i j) (K i) (hLip i j), hT, fun _ _ => rfl, ?_⟩
  intro u ell hell hu hub
  let coefficients := happrox u ell (hell.trans (Real.exp_le_exp.mpr hpq)) hu hub
  let coeff := coefficients.choose
  have hcoeff := coefficients.choose_spec.1
  have hcoeffnorm := coefficients.choose_spec.2.1
  have herr := coefficients.choose_spec.2.2
  refine ⟨coeff, hcoeff, fun j => (hcoeffnorm j).trans (Real.exp_le_exp.mpr hq_cost), ?_⟩
  have horbit := M.positivePolynomial_vector_error_of_lift J hJ p B hB hstable g h hproj
    n ψ coeff u epsilon herr
  intro x
  simpa only [T, M.positivePolynomialFactorNiltest_eval] using horbit x

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_canonical_positivePolynomial_splitting (t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I α σ L : Type*} [Fintype I] [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (p : ℝ), (∑ i, bound i) = t → M.ComplexityLE p →
      (Fintype.card α : ℝ) ≤ p + 2 →
      (∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥) →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      M.filtration.realification.polynomialOrbitEval 0 g = 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      (Fintype.card I : ℝ) ≤ Real.exp p →
      letI : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun _ => moduleTopology ℝ _
      letI : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun _ => IsModuleTopology.topologicalAddGroup ℝ _
      letI : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
        (∀ i, (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) p B hB hstable).ComplexityLE ((p + C) ^ C)) ∧
        ∃ h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit,
          M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
          ∃ n : α → ℕ, (∀ i, 0 < n i) ∧
            (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
            (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            ∃ T : ∀ i, Fin (n i) → (M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable).Niltest (fun _ : σ => 1),
              (∀ i j, (T i j).normBound = 1) ∧ (∀ i j, (T i j).UnitIntervalValued) ∧
              (∀ i j, (T i j).ComplexityLE ((p + C) ^ C)) ∧
              (∀ i j, (T i j).orbit =
                (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) p B hB hstable).orbitToOrdinary
                  (M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h)) ∧
              ∀ (u : I → D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
                (letI := D.metricSpace; ∀ k, LipschitzWith ell (u k)) →
                (∀ k x, ‖u k x‖ ≤ 1) →
                ∃ c : (∀ i, Fin (n i)) → EuclideanSpace ℂ I,
                  (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ Real.exp ((p + C) ^ C)) ∧
                  ∀ x, ‖(WithLp.toLp 2 (fun k => u k
                      (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g))) : EuclideanSpace ℂ I) -
                    ∑ j, (∏ i, (T i (j i)).eval x) • c j‖ ≤ epsilon := by
  obtain ⟨C, hC, hsplit⟩ := exists_uniform_positivePolynomial_splitting t a
  refine ⟨C, hC, ?_⟩
  intro I α σ L _ _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _
    p ht hM hα hcover g hg epsilon hepsilon hscale hI
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) := fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra) :=
    realification_moduleTopology_t2 (M.positivePolynomialFinBasis p)
  let : ∀ i, FiniteDimensional ℚ (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)) :=
    fun i => (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
    restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    realification_moduleTopology_t2 (Module.finBasis ℚ _)
  exact hsplit M J hJ p ht hM hα hcover g hg epsilon hepsilon hscale hI

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end OAI

end


