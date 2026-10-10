-- Prove2me | Definitions.Def_OAIErdos3B157
-- name    : OAIErdos3B157
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T00:41:51.151004+00:00
-- url     : https://prove2.me/theorems/9c6ce605-7bda-48d1-90e3-b15d8f33a496
-- title:
--   OpenAI Erdős-3 split, definitions bundle 158 of 177
-- statement:
--   Definitions bundle 158 of 177 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B156`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 158 available.
--
--   Modules: `OAI.Erdos3.BiasedChosenBasisStepDropSpec`, `OAI.Erdos3.NativeAnchoredRankFibers.exists_interval_pairs`, `OAI.Erdos3.NativeAnchoredRankFibers.fiber`, `OAI.Erdos3.NativeAnchoredRankFibers.fiber_anchor`, `OAI.Erdos3.NativeAnchoredRankFibers.fiber_branch`, `OAI.Erdos3.NativeAnchoredRankFibers.fiber_nonempty`, `OAI.Erdos3.NativeAnchoredRankFibers.fiber_parameter`, `OAI.Erdos3.NativeAnchoredRankFibers.fiber_shift_injective`, `OAI.Erdos3.NativeAnchoredRankFibers.noConfusion`, `OAI.Erdos3.NativePolynomialOrbitFactors.frozenMiddleValue`, `OAI.Erdos3.NativeRankInterval`, `OAI.Erdos3.NativeRankInterval.length_exp_lower_bound`, `OAI.Erdos3.NativeRankInterval.length_lower_bound`, `OAI.Erdos3.NativeRankInterval.mono`, `OAI.Erdos3.NativeRankInterval.monomialScale_modulus_bound`, `OAI.Erdos3.NativeRankInterval.norm_bound_on_modulus`, `OAI.Erdos3.NativeRankInterval.select_lower_term`, `OAI.Erdos3.NativeRankRelation.mono`, `OAI.Erdos3.NativeRankRelation.rec`, `OAI.Erdos3.NativeWeightedRankIntervals.exists_anchored_fibers`, `OAI.Erdos3.NativeWeightedRankIntervals.rec`, `OAI.Erdos3.NativeWeightedRankIntervals.remove_weight`, `OAI.Erdos3.NilpotentLieBCHGroup.exists_bounded_kernel_net`, `OAI.Erdos3.NilpotentLieBCHGroup.exists_bounded_kernel_net_with_budget`, `OAI.Erdos3.NilpotentLieBCHGroup.exists_bounded_subgroup_net`, `OAI.Erdos3.NilpotentLieFiltration.adaptedPolynomialRealValueHom_weightedChart`, `OAI.Erdos3.NilpotentLieFiltration.adapted_realChartSubstitute_homogeneous`, `OAI.Erdos3.NilpotentLieFiltration.adapted_realChartSubstitute_weightedSupport`, `OAI.Erdos3.NilpotentLieFiltration.exists_actual_marked_slow_kernel_cells`, `OAI.Erdos3.NilpotentLieFiltration.exists_chartwise_controlled_globalMarkedNativeFactors`, `OAI.Erdos3.NilpotentLieFiltration.exists_polynomial_chart_outer_iteration_bounds`, `OAI.Erdos3.NilpotentLieFiltration.exists_refiltration_bases_in_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.exists_restricted_chart_iteration_bounds`, `OAI.Erdos3.NilpotentLieFiltration.exists_restricted_chart_prefix_control`, `OAI.Erdos3.NilpotentLieFiltration.exists_slow_kernel_cells`, `OAI.Erdos3.NilpotentLieFiltration.exists_uniform_slow_kernel_cells`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousAdaptedRealChartHom`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousAdaptedRealChartHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousAdaptedRealChartLie`, `OAI.Erdos3.NilpotentLieFiltration.homogeneousAdaptedRealChartLie_coe`, `OAI.Erdos3.NilpotentLieFiltration.polynomialChartOuterIteration`, `OAI.Erdos3.NilpotentLieFiltration.polynomialChartOuterIteration_eq_products`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomialHom_restrictedMajorCorrection`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomialHom_restrictedMajorCorrection_chart`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomial_degreeLE_one`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolHom_weightedAdaptedRealChart`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolHomogeneousPullback_mem_of_range`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolHomogeneousPullback_mem_pointwise`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfPolynomial_chart_eq_top`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfPolynomial_inhomogeneousChart`, `OAI.Erdos3.NilpotentLieFiltration.restrictedMajorChartCorrection`, `OAI.Erdos3.NilpotentLieFiltration.restrictedMajorChartCorrection_adapted`, `OAI.Erdos3.NilpotentLieFiltration.restrictedMajorChartCorrection_adapted_one`, `OAI.Erdos3.NilpotentLieFiltration.restrictedMajorChartCorrection_coord`, `OAI.Erdos3.NilpotentLieFiltration.restrictedMajorChartCorrection_graded`, `OAI.Erdos3.NilpotentLieFiltration.restrictedMajorChartCorrection_substitute`, `OAI.Erdos3.NilpotentLieFiltration.restrictedMajorOuterFactors_chart_representation`, `OAI.Erdos3.NilpotentLieFiltration.restrictedMajorOuterFactors_congr`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial_family_exists_coefficient_grid`, `OAI.Erdos3.NilpotentLieFiltration.scalarSymbolPolynomial_family_rational_coefficients`, `OAI.Erdos3.NilpotentLieFiltration.symbolRationalGrid_homogeneousPullback_rational_of_coefficientGrid`, `OAI.Erdos3.NilpotentLieFiltration.weightedAdaptedRealChartHom`, `OAI.Erdos3.NilpotentLieFiltration.weightedAdaptedRealChartHom_comp`, `OAI.Erdos3.NilpotentLieFiltration.weightedAdaptedRealChartHom_constant`, `OAI.Erdos3.NilpotentLieFiltration.weightedAdaptedRealChartHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.weightedAdaptedRealChartLie`, `OAI.Erdos3.NilpotentLieFiltration.weightedAdaptedRealChartLie_coe`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.symbol_of_native`, `OAI.Erdos3.RationalFilteredNilmanifold.frozen_refiltered_top_invariant`, `OAI.Erdos3.VectorPolynomial.CoefficientGrid.realChartSubstitute_rational`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalGridCondition`, `OAI.Erdos3.VectorPolynomial.coordinate_coeff_realChartSubstitute_freeze_zero`, `OAI.Erdos3.VectorPolynomial.realChartSubstitute_map`, `OAI.Erdos3.VectorPolynomial.realChartSubstitute_weightedHomogeneousPart`, `OAI.Erdos3.VectorPolynomial.realCoefficientEquiv_symm_weightedHomogeneousPart`, `OAI.Erdos3.VectorPolynomial.realCoefficientEquiv_weightedHomogeneousPart`, `OAI.Erdos3.VectorPolynomial.substitute_weightedHomogeneousPart`, `OAI.Erdos3.coeff_aeval_frozenCoordinate_zero`, `OAI.Erdos3.coeff_aeval_monomial_eq_top`, `OAI.Erdos3.coeff_freezePolynomial_zero`, `OAI.Erdos3.exists_biased_chosen_basis_step_drop`, `OAI.Erdos3.exists_native_frozen_middle_expansion`, `OAI.Erdos3.exists_rank_interval_raised_lower_term`, `OAI.Erdos3.exists_rank_relation_budget`, `OAI.Erdos3.exists_real_module_topology`, `OAI.Erdos3.exists_slow_kernel_net_geometry_budget`, `OAI.Erdos3.exists_translated_step_drop`, `OAI.Erdos3.exists_translated_step_drop_succ`, `OAI.Erdos3.freezePolynomial_zero_eq_killCompl`, `OAI.Erdos3.horizontalCoordinateBudget`, `OAI.Erdos3.horizontalCoordinateBudget_nonneg`, `OAI.Erdos3.horizontalCoordinateHeight_bound`, `OAI.Erdos3.nativeCoordinateBaseBudget`, `OAI.Erdos3.nativeCoordinateBaseBudget_bounds`, `OAI.Erdos3.nativeCoordinateInputBudget`, `OAI.Erdos3.nativeCoordinateInputBudget_bounds`, `OAI.Erdos3.nativeCoordinateInputBudget_nonneg`, `OAI.Erdos3.nativeCoordinateSeparationBudget`, `OAI.Erdos3.nativeCoordinateSeparationBudget_cutoffs`, `OAI.Erdos3.nativeCoordinate_denominator_bound`, `OAI.Erdos3.nativeCoordinate_slow_bound`, `OAI.Erdos3.nativeDependentBudget`, `OAI.Erdos3.nativeDependentBudget_nonneg`, `OAI.Erdos3.nativeDependentDenominatorBudget`, `OAI.Erdos3.nativeDependentSlowBudget`, `OAI.Erdos3.nativeDependentSlowBudget_bound`, `OAI.Erdos3.rank_pair_density_loss`, `OAI.Erdos3.refiltrationCoordinateBudget`, `OAI.Erdos3.refiltrationCoordinateBudget_nonneg`, `OAI.Erdos3.weightedRealChart_comp_support`, `OAI.Erdos3.weightedTop_aeval_monomial`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B155

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BiasedChosenBasisStepDrop
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def BiasedChosenBasisStepDropSpec (s C : ℕ) : Prop :=
  ∀ (_hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
        (Fintype.card σ : ℝ) ≤ p →
        (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
        Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
        D.filtration.ControlledSymbolFactorization e ω hF η (fun i => (lengths i : ℝ))
          (D.filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
            (D.filtration.realAdaptedPolynomialGroupHom (fun _ => 1) g)) ((p + C) ^ C)

theorem exists_biased_chosen_basis_step_drop (s c : ℕ)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ BiasedChosenBasisStepDropSpec.{uσ, uL} s C := by
  obtain ⟨a, _, hfamily⟩ := exists_biased_native_terminal s c hI
  obtain ⟨b, _, hcompose⟩ := exists_controlled_symbol_composition (s + 1)
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Q : Polynomial ℕ := B + (Polynomial.X + 4) ^ 11 + Polynomial.X + 2
  let P : Polynomial ℕ := B + (Q + 1) + (Q + 1 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let k : ℝ := (p + a) ^ a
  let q : ℝ := k + (p + 4) ^ 11 + p + 2
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have h11 : 0 ≤ (p + 4) ^ 11 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hkq : k ≤ q := by dsimp [q]; linarith
  have h11q : (p + 4) ^ 11 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq1 : 0 ≤ q + 1 := by linarith
  have hlast : 0 ≤ (q + 1 + b) ^ b := by positivity
  have hbound : k + (q + 1) + (q + 1 + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Q, B, k, q, Polynomial.eval₂_pow] using hfinal p hp
  have hkC : k ≤ (p + C) ^ C := by linarith
  have hbC : (q + 1 + b) ^ b ≤ (p + C) ^ C := by linarith
  have hkq1 : k ≤ q + 1 := by linarith
  have hpq1 : p ≤ q + 1 := by linarith
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, hconstruct⟩ := hfamily hs D p hp T hT
  obtain ⟨hdim, _, hstructure⟩ := D.basis_geometry_of_forward_height e hp hT.1 he
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, ?_⟩
  intro g hgOrbit η hvert origin lengths hlengths hσ hlarge hbias
  have hTpos : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  obtain ⟨l, W, A, M, R, hl, hlk, hprod, hA, hR, hterminal⟩ :=
    hconstruct g hgOrbit η hvert origin lengths hlengths hσ
      (fun i => (Real.exp_le_exp.mpr hkC).trans (hlarge i)) hbias
  let H := ⌈Real.exp q⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp q
  have hHp : (H : ℝ) ≤ Real.exp (q + 1) := ceil_exp_le_exp_add_one hq
  have hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H :=
    fun i j k => rationalHeightLE_ceil_exp ((hstructure i j k).trans h11q)
  let φ : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1) →*
      D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1) :=
    (D.filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)).comp
      (D.filtration.realAdaptedPolynomialGroupHom (fun _ => 1))
  have hinner : D.filtration.ControlledSymbolFactorization e ω hF η
      (fun i => (lengths i : ℝ)) (φ M) (k + 1) :=
    SymbolTerminalFactorization.controlled D.filtration e ω hF W hk hTpos hterminal
  have hinner' := ControlledSymbolFactorization.mono D.filtration e ω hF hinner
    (show k + 1 ≤ q + 1 by linarith) hTpos
  have houter : D.filtration.SymbolSlowBound e ω hF (fun _ => 1)
      (fun i => (lengths i : ℝ)) (Real.exp (q + 1)) (φ A) :=
    D.filtration.symbolSlowBound_mono e ω hF (fun _ => 1) (fun i => (lengths i : ℝ)) hTpos
      (Real.exp_le_exp.mpr hkq1) (φ A)
      (D.filtration.native_symbol_slow e ω hF (fun _ => 1) (fun i => (lengths i : ℝ)) hTpos
        (Real.exp_nonneg k) A hA)
  have hrat : D.filtration.SymbolRationalGrid e ω hF (fun _ => 1) l (φ R) :=
    D.filtration.native_symbol_grid e ω hF (fun _ => 1) l R hR
  have hfull := hcompose D.filtration e ω hF H (q + 1) hH hq1
    (hdim.trans hpq1) (hσ.trans hpq1) hHp hc (fun i => (lengths i : ℝ)) hTpos η
    l hl (hlk.trans (Real.exp_le_exp.mpr hkq1)) (φ A) (φ M) (φ R) houter hrat hinner'
  have heq : φ A * φ M * φ R = φ g := by
    rw [← map_mul, ← map_mul, hprod]
  rw [heq] at hfull
  exact ControlledSymbolFactorization.mono D.filtration e ω hF hfull hbC hTpos

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionalStepDrop
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e : ℕ}
  (D : RationalFilteredNilmanifold L s d)
  (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra U) s e)
  (hEF : E.filtration = D.filtration.gradedRefiltration U)
  (u : D.Space → ℂ)
  (hu : ∀ z : D.RealGroup,
    z.coord ∈ D.filtration.realGradedRefiltrationLayer U s → ∀ x, u (z • x) = u x)

include hEF hu in
theorem frozen_refiltered_top_invariant (a r : D.RealGroup)
    (z : E.RealGroup) (hz : z ∈ E.filtration.realification.subgroup s) (x : E.RealGroup) :
    u (QuotientGroup.mk (a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra U).incl (z * x) * r)) =
    u (QuotientGroup.mk (a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra U).incl x * r)) := by
  let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot)
    (D.filtration.gradedRefiltrationSubalgebra U).incl
  have hz' : (φ z).coord ∈ D.filtration.realGradedRefiltrationLayer U s := by
    apply (D.filtration.mem_native_refiltration_layer U s z.coord).mp
    have h : z.coord ∈ E.filtration.realification.layer s := hz
    simpa only [hEF] using h
  have hcomm := D.filtration.realification.top_commutes (φ z)
    (D.filtration.realGradedRefiltrationLayer_le U s hz') a
  have heq : a * φ (z * x) * r = φ z * (a * φ x * r) := by
    calc
      a * φ (z * x) * r = (a * φ z) * φ x * r := by simp only [map_mul, mul_assoc]
      _ = (φ z * a) * φ x * r := by rw [← hcomm.eq]
      _ = φ z * (a * φ x * r) := by simp only [mul_assoc]
  change u (QuotientGroup.mk (a * φ (z * x) * r)) = _
  rw [heq]
  exact hu (φ z) hz' (QuotientGroup.mk (a * φ x * r))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_real_module_topology {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V] (b : Basis ι ℚ V) :
    ∃ τ : TopologicalSpace (ℝ ⊗[ℚ] V),
      letI := τ
      IsTopologicalAddGroup (ℝ ⊗[ℚ] V) ∧ ContinuousSMul ℝ (ℝ ⊗[ℚ] V) ∧ T2Space (ℝ ⊗[ℚ] V) := by
  let τ := moduleTopology ℝ (ℝ ⊗[ℚ] V)
  let : TopologicalSpace (ℝ ⊗[ℚ] V) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V) := IsModuleTopology.topologicalAddGroup ℝ _
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] V) := (b.baseChange ℝ).finiteDimensional_of_finite
  have hc : Continuous (b.baseChange ℝ).equivFun :=
    IsModuleTopology.continuous_of_linearMap (b.baseChange ℝ).equivFun.toLinearMap
  let : T2Space (ℝ ⊗[ℚ] V) := T2Space.of_injective_continuous (b.baseChange ℝ).equivFun.injective hc
  exact ⟨τ, inferInstance, inferInstance, inferInstance⟩

namespace RationalFilteredNilmanifold.Niltest

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem symbol_of_native (T : D.Niltest w) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (g : D.filtration.RealAdaptedPolynomialGroup w) (hg : D.filtration.nativePolynomialOrbit w g = T.orbit) :
    T.symbol b ω hF = D.filtration.realPolynomialSymbolHom b ω hF w
      (D.filtration.realAdaptedPolynomialGroupHom w g) := by
  have he := congrArg (fun a : D.filtration.realification.PolynomialOrbit w =>
    D.filtration.realPolynomialSymbolHom b ω hF w ⟨⟨a.log, a.property⟩⟩) hg
  exact he.symm

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.NativeAntisymmetricOrbitFactors

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p q : ℝ}
  {N e : ℕ}
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
  [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]

end Erdos3.NativeAntisymmetricOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

namespace NativePolynomialOrbitFactors

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
  {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}

noncomputable def frozenMiddleValue (R : NativePolynomialOrbitFactors D g eta A p)
    (a r : D.RealGroup) (x : σ → ℤ) : D.RealGroup :=
  a * D.filtration.adaptedPolynomialRealValueHom
    (fun _ : σ => 1) (fun i => (x i : ℝ)) R.middle * r

end NativePolynomialOrbitFactors

theorem exists_native_frozen_middle_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      {g : (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p)
      (T : D.Niltest (fun _ : σ => 1)), 0 ≤ p → T.ComplexityLE p →
      (∀ z : D.RealGroup,
        z.coord ∈ D.filtration.realGradedRefiltrationLayer R.subalgebra (s + 1) →
        ∀ x, T.observable (z • x) = T.observable x) →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp p → ∀ a r : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp p) →
        (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m →
        Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C)
          (fun x => T.observable (QuotientGroup.mk (R.frozenMiddleValue a r x)))) := by
  obtain ⟨B, _, hmodel⟩ := exists_native_middle_model
  obtain ⟨K, _, hdesc⟩ := exists_uniform_frozen_descent s 1
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + Polynomial.C B) ^ B + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ d D g eta A p R T hp hT hinv m hm hmb a r ha hr
  obtain ⟨E, hEF, _hEL, hE, hinc, h, hh⟩ := hmodel D R hp hT.1
  let : TopologicalSpace (ℝ ⊗[ℚ]
      D.filtration.gradedRefiltrationSubalgebra R.subalgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      D.filtration.gradedRefiltrationSubalgebra R.subalgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let t := p + (p + B) ^ B + 4
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith [pow_nonneg (by positivity : 0 ≤ p + B) B]
  have hEt : (p + B) ^ B ≤ t := by dsimp [t]; linarith
  obtain ⟨_Λ, _hΛ, _hchar, _hnormal, _hfinite, _hindex,
      n, _hn, Q, hQF, _hQL, _hQ, hfamily⟩ :=
    hdesc E D (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl T h ht
      (hE.mono E hEt) (hT.mono hpt) (fun i j => (hinc j i).trans hEt)
      m hm (hmb.trans (Real.exp_le_exp.mpr hpt))
  let : TopologicalSpace (ℝ ⊗[ℚ]
      (D.filtration.gradedRefiltrationSubalgebra R.subalgebra ⧸
        E.filtration.layerIdeal (s + 1))) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      (D.filtration.gradedRefiltrationSubalgebra R.subalgebra ⧸
        E.filtration.layerIdeal (s + 1))) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  have ha' : ∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((t + 2) ^ 1) :=
    fun i => (ha i).trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  obtain ⟨S, _hSo, _hSn, hSc, hSe⟩ := hfamily a r ha' hr
    (D.frozen_refiltered_top_invariant R.subalgebra E hEF T.observable hinv a r)
  have hcost : (t + K) ^ K ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨NativeIntegerExpansion.ofTest S (hSc.mono hcost) ?_⟩
  intro x
  exact ((hSe x).trans (congrArg
    (fun z : D.RealGroup => T.observable (QuotientGroup.mk (a * z * r))) (hh x))).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

universe uσ uL

theorem exists_translated_step_drop_succ (s c : ℕ) (hs : 1 ≤ s)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ TranslatedStepDropSpec.{uσ, uL} (s + 1) C := by
  obtain ⟨a, _, hchosen⟩ := exists_biased_chosen_basis_step_drop s c hI
  obtain ⟨b, _, hchange⟩ := exists_controlled_symbol_basis_change (s + 1)
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let U : Polynomial ℕ := B + Polynomial.X + 3
  let P : Polynomial ℕ := B + U + (U + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d _ _ _ _ D ν hD p hp hσ T hT η _hη hvertical origin lengths hlengths hlarge hbias
  let k : ℝ := (p + a) ^ a
  let u : ℝ := k + p + 3
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hku : k ≤ u := by dsimp [u]; linarith
  have hpu : p ≤ u := by dsimp [u]; linarith
  have hp2u : p + 2 ≤ u := by dsimp [u]; linarith
  have hlast : 0 ≤ (u + b) ^ b := by positivity
  have hbound : k + u + (u + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, U, B, k, u, Polynomial.eval₂_pow] using hfinal p hp
  have hkC : k ≤ (p + C) ^ C := by linarith
  have hbC : (u + b) ^ b ≤ (p + C) ^ C := by linarith
  obtain ⟨τS, hSA, hSM, hST⟩ := exists_real_module_topology
    (D.filtration.squareFinBasis D.basis ν (hD 2))
  let : TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := τS
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hSA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hSM
  let : T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hST
  obtain ⟨τQ, hQA, hQM, hQT⟩ := exists_real_module_topology
    (D.filtration.reducedSquareBasis D.basis ν hD)
  let : TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1))) := τQ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1))) := hQA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1))) := hQM
  let : T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1))) := hQT
  obtain ⟨e, ω, hF, _N, _hN, _hin, _hout, he, _hgeometry, hconstruct⟩ := hchosen hs D p hp T hT
  obtain ⟨g, hg⟩ := D.filtration.nativePolynomialOrbit_surjective (fun _ : σ => 1) D.basis ν hD T.orbit
  have hTpos : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  have hfactor := hconstruct g hg η hvertical origin lengths hlengths hσ
    (fun i => (Real.exp_le_exp.mpr hkC).trans (hlarge i)) hbias
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp (p + 1)
  have hHp : (H : ℝ) ≤ Real.exp u := by
    have he := ceil_exp_le_exp_add_one (show 0 ≤ p + 1 by linarith)
    exact he.trans (Real.exp_le_exp.mpr (by linarith))
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ u := by
    rw [Fintype.card_fin, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hT.1.1.trans hpu
  have hd : (Fintype.card (Fin d) : ℝ) ≤ u := by
    simpa only [Fintype.card_fin] using hT.1.1.trans hpu
  have hentries : ∀ i j, RationalHeightLE (D.basis.repr (e i) j) H :=
    fun i j => rationalHeightLE_ceil_exp (he i j)
  have hfactor' := ControlledSymbolFactorization.mono D.filtration e ω hF hfactor hku hTpos
  have hdeclared := hchange D.filtration e ω hF D.basis ν hD H u hH hu hdim hd (hσ.trans hpu)
    hHp hentries (fun i => (lengths i : ℝ)) hTpos η _ hfactor'
  have hsym : D.filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
      (D.filtration.realAdaptedPolynomialGroupHom (fun _ => 1) g) = T.symbol D.basis ν hD := by
    exact (D.filtration.native_symbol_basis_independent e ω hF D.basis ν hD (fun _ => 1) g).symm.trans
      (T.symbol_of_native D.basis ν hD g hg).symm
  rw [hsym] at hdeclared
  exact ControlledSymbolFactorization.mono D.filtration D.basis ν hD hdeclared hbC hTpos

theorem exists_translated_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ TranslatedStepDropSpec.{uσ, uL} s C := by
  have h : ∀ n : ℕ, ∃ C : ℕ, 2 ≤ C ∧ TranslatedStepDropSpec.{uσ, uL} (n + 1) C := by
    intro n
    induction n with
    | zero => exact ⟨4, by decide, translatedStepDropSpec_one⟩
    | succ n ih =>
      obtain ⟨C, _hC, hI⟩ := ih
      exact exists_translated_step_drop_succ (n + 1) C (by omega) hI
  cases s with
  | zero => omega
  | succ n => exact h n

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RestrictedChartPrefixControl
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

theorem substitute_weightedHomogeneousPart
    {σ τ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (w : σ → ℕ) (v : τ → ℕ) (f : σ → MvPolynomial τ R)
    (hf : ∀ i, (f i).IsWeightedHomogeneous v (w i))
    (d : ℕ) (p : VectorPolynomial σ R V) :
    substitute f (weightedHomogeneousPart w d p) =
      weightedHomogeneousPart v d (substitute f p) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul P x =>
    rw [weightedHomogeneousPart_tmul, substitute_tmul, substitute_tmul,
      weightedHomogeneousPart_tmul, aeval_weightedHomogeneousComponent w v f hf]
  | add p q hp hq => simp only [map_add, hp, hq]

variable {σ τ V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]

theorem realChartSubstitute_map
    {W : Type*} [AddCommGroup W] [Module ℚ W] [Module ℝ W] [IsScalarTower ℚ ℝ W]
    (f : σ → MvPolynomial τ ℝ) (S : V →ₗ[ℝ] W) (p : VectorPolynomial σ ℚ V) :
    realChartSubstitute f (map (S.restrictScalars ℚ) p) =
      map (S.restrictScalars ℚ) (realChartSubstitute f p) := by
  have hmap : realCoefficientEquiv (map (S.restrictScalars ℚ) p) =
      map S (realCoefficientEquiv p) := by
    apply coefficients.injective
    ext α
    simp only [coefficients_realCoefficientEquiv, coefficients_map,
      LinearMap.restrictScalars_apply]
  have hsymm (q : VectorPolynomial τ ℝ V) :
      realCoefficientEquiv.symm (map S q) =
        map (S.restrictScalars ℚ) (realCoefficientEquiv.symm q) := by
    apply coefficients.injective
    ext α
    simp only [coefficients_realCoefficientEquiv_symm, coefficients_map,
      LinearMap.restrictScalars_apply]
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, hmap, ← map_substitute, hsymm]

theorem realCoefficientEquiv_weightedHomogeneousPart (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ ℚ V) :
    realCoefficientEquiv (weightedHomogeneousPart w d p) =
      weightedHomogeneousPart w d (realCoefficientEquiv p) := by
  apply coefficients.injective
  ext α
  simp only [coefficients_realCoefficientEquiv, coefficients_weightedHomogeneousPart]

theorem realCoefficientEquiv_symm_weightedHomogeneousPart (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ ℝ V) :
    realCoefficientEquiv.symm (weightedHomogeneousPart w d p) =
      weightedHomogeneousPart w d (realCoefficientEquiv.symm p) := by
  apply coefficients.injective
  ext α
  simp only [coefficients_realCoefficientEquiv_symm, coefficients_weightedHomogeneousPart]

theorem realChartSubstitute_weightedHomogeneousPart (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous v (w i))
    (d : ℕ) (p : VectorPolynomial σ ℚ V) :
    realChartSubstitute f (weightedHomogeneousPart w d p) =
      weightedHomogeneousPart v d (realChartSubstitute f p) := by
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, realCoefficientEquiv_weightedHomogeneousPart,
    substitute_weightedHomogeneousPart w v f hf,
    realCoefficientEquiv_symm_weightedHomogeneousPart]

end Erdos3.VectorPolynomial

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial

variable {U B : Type*}

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute realPolynomialChartSubstitution

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

noncomputable def polynomialChartOuterIteration (F : NilpotentLieFiltration L s)
    (f : σ → MvPolynomial σ ℝ)
    (a r : ℕ → PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot) :
    ℕ → PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot ×
      PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot
  | 0 => (1, 1)
  | n + 1 =>
    let previous := polynomialChartOuterIteration F f a r n
    (previous.1 * realPolynomialChartSubstitution F.realification.lowerCentralSeries_eq_bot f (a n),
      r n * previous.2)

theorem polynomialChartOuterIteration_eq_products (F : NilpotentLieFiltration L s)
    (f : σ → MvPolynomial σ ℝ)
    (a r : ℕ → PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot) (n : ℕ) :
    F.polynomialChartOuterIteration f a r n =
      (realPolynomialChartSubstitution F.realification.lowerCentralSeries_eq_bot f
        ((List.range n).map a).prod, ((List.range n).map r).reverse.prod) := by
  induction n with
  | zero => simp only [polynomialChartOuterIteration, List.range_zero, List.map_nil,
      List.prod_nil, List.reverse_nil, map_one]
  | succ n ih =>
    simp only [polynomialChartOuterIteration, ih, List.range_succ, List.map_append,
      List.map_singleton, List.prod_append, List.prod_singleton, List.reverse_append,
      List.reverse_singleton, map_mul]

theorem exists_polynomial_chart_outer_iteration_bounds (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (f : σ → MvPolynomial σ ℝ)
          (q r : ℕ → PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
        (∀ j < s, (q j).coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ j < s, (r j).coord ∈ F.realification.adaptedLieSubalgebra (fun _ => 1)) →
        (∀ j < s, CoefficientBound (b.baseChange ℝ) (fun _ => 1)
          (Real.exp ((p + 2) ^ a)) (q j).coord) →
        (∀ j < s, CoefficientGrid (b.baseChange ℝ) l (r j).coord) →
        ∀ n ≤ s, ∃ Echart : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
          (F.polynomialChartOuterIteration f q r n).1 =
            realPolynomialChartSubstitution F.realification.lowerCentralSeries_eq_bot f Echart ∧
          CoefficientBound (b.baseChange ℝ) (fun _ => 1)
            (Real.exp ((p + C) ^ C)) Echart.coord ∧
          CoefficientGrid (b.baseChange ℝ) m (F.polynomialChartOuterIteration f q r n).2.coord := by
  obtain ⟨C, hC, hproducts⟩ := exists_outer_polynomial_product_bounds s a s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  obtain ⟨m, hm, hmp, hlm, hprod⟩ := hproducts F b ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro f q r hqa hra hqb hrb n hn
  have hmem (v : ℕ → PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
      (g : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
      (hg : g ∈ (List.range n).map v) :
      ∃ j, j < s ∧ v j = g := by
    obtain ⟨j, hj, heq⟩ := List.mem_map.mp hg
    exact ⟨j, lt_of_lt_of_le (List.mem_range.mp hj) hn, heq⟩
  obtain ⟨hs, hr⟩ := hprod ((List.range n).map q) ((List.range n).map r)
    (by simpa using hn) (by simpa using hn)
    (fun g hg => by obtain ⟨j, hj, rfl⟩ := hmem q g hg; exact hqa j hj)
    (fun g hg => by obtain ⟨j, hj, rfl⟩ := hmem r g hg; exact hra j hj)
    (fun g hg => by obtain ⟨j, hj, rfl⟩ := hmem q g hg; exact hqb j hj)
    (fun g hg => by obtain ⟨j, hj, rfl⟩ := hmem r g hg; exact hrb j hj)
  refine ⟨((List.range n).map q).prod, ?_, hs, ?_⟩
  · rw [F.polynomialChartOuterIteration_eq_products]
  · rw [F.polynomialChartOuterIteration_eq_products]
    exact hr

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute realPolynomialChartSubstitution

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)
  (U : Submodule ℚ F.AssociatedGraded)
  (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)

noncomputable def restrictedMajorChartCorrection (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot :=
  ⟨F.homogeneousQuotientGradedPolynomial b ω hF k (S.baseChange ℝ)
    (weightedHomogeneousPart w k p)⟩

@[simp] theorem restrictedMajorChartCorrection_coord (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    (F.restrictedMajorChartCorrection b ω hF w U S k p).coord =
      F.homogeneousQuotientGradedPolynomial b ω hF k (S.baseChange ℝ)
        (weightedHomogeneousPart w k p) := rfl

theorem restrictedMajorChartCorrection_graded (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    (F.restrictedMajorChartCorrection b ω hF w U S k p).coord ∈
      gradedPolynomialSubmodule ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w := by
  rw [F.restrictedMajorChartCorrection_coord]
  apply F.homogeneousQuotientGradedPolynomial_graded
  exact weightedHomogeneousPart_homogeneous w k p

theorem restrictedMajorChartCorrection_adapted (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    (F.restrictedMajorChartCorrection b ω hF w U S k p).coord ∈
      F.associatedGradedFiltration.realification.adaptedLieSubalgebra w :=
  F.associatedGradedFiltration.gradedPolynomial_mem_adapted
    (F.associatedGradedBasis b ω hF) ω (F.associatedGradedFiltration_layer b ω hF) w _
    (F.restrictedMajorChartCorrection_graded b ω hF w U S k p)

theorem restrictedMajorChartCorrection_adapted_one (hw : ∀ i, 0 < w i) (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    (F.restrictedMajorChartCorrection b ω hF w U S k p).coord ∈
      F.associatedGradedFiltration.realification.adaptedLieSubalgebra (fun _ => 1) := by
  have ha := F.restrictedMajorChartCorrection_adapted b ω hF w U S k p
  intro α
  apply F.associatedGradedFiltration.realification.antitone
    (show Finsupp.weight (fun _ : σ => 1) α ≤ Finsupp.weight w α from ?_) (ha α)
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, mul_one]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right (α i) (hw i))

theorem realGradedSymbolPolynomialHom_restrictedMajorCorrection (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    F.realGradedSymbolPolynomialHom b ω hF w
        (F.restrictedMajorCorrection b ω hF w U S k p) =
      F.restrictedMajorChartCorrection b ω hF w U S k p := by
  apply NilpotentLieBCHGroup.ext
  exact F.realGradedSymbolPolynomial_homogeneousQuotientSymbolLift b ω hF w k
    (S.baseChange ℝ) _ (weightedHomogeneousPart_homogeneous w k p)

theorem restrictedMajorChartCorrection_substitute
    (f : σ → MvPolynomial σ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (w i)) (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    F.restrictedMajorChartCorrection b ω hF w U S k (realChartSubstitute f p) =
      realPolynomialChartSubstitution
        F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot f
        (F.restrictedMajorChartCorrection b ω hF w U S k p) := by
  apply NilpotentLieBCHGroup.ext
  rw [F.restrictedMajorChartCorrection_coord, realPolynomialChartSubstitution_coord,
    F.restrictedMajorChartCorrection_coord]
  rw [← realChartSubstitute_weightedHomogeneousPart w w f hf]
  simp only [homogeneousQuotientGradedPolynomial, realChartSubstitute_map]

theorem realGradedSymbolPolynomialHom_restrictedMajorCorrection_chart
    (f : σ → MvPolynomial σ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (w i)) (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    F.realGradedSymbolPolynomialHom b ω hF w
        (F.restrictedMajorCorrection b ω hF w U S k (realChartSubstitute f p)) =
      realPolynomialChartSubstitution
        F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot f
        (F.restrictedMajorChartCorrection b ω hF w U S k p) := by
  rw [F.realGradedSymbolPolynomialHom_restrictedMajorCorrection,
    F.restrictedMajorChartCorrection_substitute b ω hF w U S f hf]

theorem restrictedMajorOuterFactors_chart_representation
    (f : σ → MvPolynomial σ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (w i))
    (qS pR : ℕ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) (n : ℕ) :
    let outer := F.restrictedMajorOuterFactors b ω hF w U S
      (fun j => realChartSubstitute f (qS j)) pR n
    (F.realGradedSymbolPolynomialHom b ω hF w outer.1,
      F.realGradedSymbolPolynomialHom b ω hF w outer.2) =
      F.associatedGradedFiltration.polynomialChartOuterIteration f
        (fun j => F.restrictedMajorChartCorrection b ω hF w U S (j + 1) (qS j))
        (fun j => F.restrictedMajorChartCorrection b ω hF w U S (j + 1) (pR j)) n := by
  induction n with
  | zero => simp only [restrictedMajorOuterFactors, polynomialChartOuterIteration, map_one]
  | succ n ih =>
    have hleft := congrArg Prod.fst ih
    have hright := congrArg Prod.snd ih
    dsimp only at hleft hright ⊢
    simp only [restrictedMajorOuterFactors, polynomialChartOuterIteration, map_mul,
      F.realGradedSymbolPolynomialHom_restrictedMajorCorrection_chart b ω hF w U S f hf,
      F.realGradedSymbolPolynomialHom_restrictedMajorCorrection, hleft, hright]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_restricted_chart_iteration_bounds (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr
        ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆ z) H) →
      ∀ (U : Submodule ℚ F.AssociatedGraded)
        (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)
        (eQ : Basis κ ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) (B M : ℝ)
        (qS qP : ℕ), 0 ≤ M → 0 < qS * qP → ((qS * qP : ℕ) : ℝ) ≤ Real.exp p →
      (Fintype.card κ : ℝ) * B * M ≤ Real.exp ((p + 2) ^ a) →
      (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (S.baseChange ℝ (eQ j)) i| ≤ B) →
      (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (S.baseChange ℝ (eQ j)) i) ∈ realDenominatorGrid qS) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ qS * qP ∣ m ∧
        ∀ (f : σ → MvPolynomial σ ℝ),
        (∀ i, (f i).IsWeightedHomogeneous w (w i)) →
        ∀ pS pR : ℕ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)),
        (∀ j < s, ∀ α i, |eQ.repr (coefficients (pS j) α) i| ≤ M) →
        (∀ j < s, ∀ α, (fun i => eQ.repr (coefficients (pR j) α) i) ∈ realDenominatorGrid qP) →
        ∀ n ≤ s,
        let outer := F.restrictedMajorOuterFactors b ω hF w U S
          (fun j => realChartSubstitute f (pS j)) pR n
        ∃ Echart : PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot,
          F.realGradedSymbolPolynomialHom b ω hF w outer.1 =
            realPolynomialChartSubstitution
              F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot f Echart ∧
          CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
            (Real.exp ((p + C) ^ C)) Echart.coord ∧
          CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) m
            (F.realGradedSymbolPolynomialHom b ω hF w outer.2).coord := by
  obtain ⟨C, hC, hiteration⟩ := exists_polynomial_chart_outer_iteration_bounds s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hstructure
    U S eQ B M qS qP hM hqpos hqp hcost hSbound hSgrid
  obtain ⟨m, hm, hmp, hqm, hbound⟩ := hiteration F.associatedGradedFiltration
    (F.associatedGradedBasis b ω hF) ω (F.associatedGradedFiltration_layer b ω hF)
    H p hH hp hι hσ hHp hstructure (qS * qP) hqpos hqp
  refine ⟨m, hm, hmp, hqm, ?_⟩
  intro f hf pS pR hpS hpR n hn
  let q := fun j => F.restrictedMajorChartCorrection b ω hF w U S (j + 1) (pS j)
  let r := fun j => F.restrictedMajorChartCorrection b ω hF w U S (j + 1) (pR j)
  have hslow : ∀ j < s, CoefficientBound
      ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
        (Real.exp ((p + 2) ^ a)) (q j).coord := by
    intro j hj
    dsimp only [q]
    rw [F.restrictedMajorChartCorrection_coord]
    have hpbase : ∀ α i, |eQ.repr (coefficients (pS j) α) i| ≤
        M / monomialScale (fun _ => 1) α := by
      simpa [monomialScale] using hpS j hj
    have hc := F.homogeneousQuotientGradedPolynomial_coefficientBound b ω hF eQ
      (j + 1) (S.baseChange ℝ) (weightedHomogeneousPart w (j + 1) (pS j))
      (fun _ => 1) (fun _ => zero_lt_one) hM hSbound
      (weightedHomogeneousPart_coordinateBound eQ (fun _ => 1) (fun _ => zero_lt_one)
        hM (pS j) hpbase w (j + 1))
    intro α i
    exact (hc α i).trans (div_le_div_of_nonneg_right hcost
      (monomialScale_pos (fun _ => 1) (fun _ => zero_lt_one) α).le)
  have hgrid : ∀ j < s, CoefficientGrid
      ((F.associatedGradedBasis b ω hF).baseChange ℝ) (qS * qP) (r j).coord := by
    intro j hj
    dsimp only [r]
    rw [F.restrictedMajorChartCorrection_coord]
    apply F.homogeneousQuotientGradedPolynomial_coefficientGrid b ω hF eQ (j + 1)
      (S.baseChange ℝ) (weightedHomogeneousPart w (j + 1) (pR j)) qS qP hSgrid
    exact weightedHomogeneousPart_coordinateGrid eQ (pR j) qP (hpR j hj) w (j + 1)
  obtain ⟨Echart, hE, hEb, hRg⟩ := hbound f q r
    (fun j _ => F.restrictedMajorChartCorrection_adapted_one b ω hF w U S hw (j + 1) (pS j))
    (fun j _ => F.restrictedMajorChartCorrection_adapted_one b ω hF w U S hw (j + 1) (pR j))
    hslow hgrid n hn
  have hrep := F.restrictedMajorOuterFactors_chart_representation b ω hF w U S f hf pS pR n
  have hleft := congrArg Prod.fst hrep
  have hright := congrArg Prod.snd hrep
  dsimp only at hleft hright ⊢
  refine ⟨Echart, hleft.trans hE, hEb, ?_⟩
  rw [hright]
  exact hRg

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

section PrefixCongruence

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : Submodule ℚ F.AssociatedGraded)
    (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)

theorem restrictedMajorOuterFactors_congr
    (pS pR qS qR : ℕ → VectorPolynomial σ ℚ
      (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
    (n : ℕ) (hleft : ∀ j < n, pS j = qS j) (hright : ∀ j < n, pR j = qR j) :
    F.restrictedMajorOuterFactors b ω hF w U S pS pR n =
      F.restrictedMajorOuterFactors b ω hF w U S qS qR n := by
  revert hleft hright
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro hleft hright
    have hprev := ih
      (fun j hj => hleft j (Nat.lt_succ_of_lt hj))
      (fun j hj => hright j (Nat.lt_succ_of_lt hj))
    simp only [restrictedMajorOuterFactors, hprev,
      hleft n (Nat.lt_succ_self n), hright n (Nat.lt_succ_self n)]

end PrefixCongruence

theorem exists_restricted_chart_prefix_control (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr
        ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆ z) H) →
      ∀ (U : Submodule ℚ F.AssociatedGraded)
        (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)
        (eQ : Basis κ ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
        (B Bphase : ℝ) (qS : ℕ), 0 ≤ Bphase → 0 < qS →
      (qS : ℝ) * Real.exp ((s : ℝ) * (Fintype.card κ : ℝ) * Bphase) ≤ Real.exp p →
      (Fintype.card κ : ℝ) * B * Real.exp Bphase ≤ Real.exp ((p + 2) ^ a) →
      (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (S.baseChange ℝ (eQ j)) i| ≤ B) →
      (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (S.baseChange ℝ (eQ j)) i) ∈ realDenominatorGrid qS) →
      ∀ (f : σ → MvPolynomial σ ℝ),
      (∀ i, (f i).IsWeightedHomogeneous w (w i)) →
      ∀ (pS pR : ℕ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
        (q : ℕ → ℕ) (n : ℕ), n ≤ s →
      (∀ j < n, 0 < q j) →
      (∀ j < n, (q j : ℝ) ≤ Real.exp ((Fintype.card κ : ℝ) * Bphase)) →
      (∀ j < n, ∀ α i, |eQ.repr (coefficients (pS j) α) i| ≤ Real.exp Bphase) →
      (∀ j < n, ∀ α, (fun i => eQ.repr (coefficients (pR j) α) i) ∈
        realDenominatorGrid (q j)) →
      let outer := F.restrictedMajorOuterFactors b ω hF w U S
        (fun j => realChartSubstitute f (pS j)) pR n
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        qS * (∏ j : Fin n, q j.val) ∣ m ∧
        ∃ Echart : PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot,
          F.realGradedSymbolPolynomialHom b ω hF w outer.1 =
            realPolynomialChartSubstitution
              F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot f Echart ∧
          CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
            (Real.exp ((p + C) ^ C)) Echart.coord ∧
          CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) m
            (F.realGradedSymbolPolynomialHom b ω hF w outer.2).coord := by
  obtain ⟨C, hC, hiteration⟩ := exists_restricted_chart_iteration_bounds s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hstructure
    U S eQ B Bphase qS hBphase hqS hdenbudget hcost hSbound hSgrid f hf
    pS pR q n hn hqpos hqbound hpS hpR
  classical
  let Q : ℕ := ∏ j : Fin n, q j.val
  have hQpos : 0 < Q := majorPhaseCoordinateDenominator_pos
    (fun j : Fin n => q j.val) (fun j => hqpos j.val j.isLt)
  have hQbound : (Q : ℝ) ≤ Real.exp ((s : ℝ) * (Fintype.card κ : ℝ) * Bphase) := by
    have hbase : (Q : ℝ) ≤ Real.exp ((n : ℝ) * (Fintype.card κ : ℝ) * Bphase) := by
      simpa only [Fintype.card_fin, mul_assoc] using
        majorPhaseCoordinateDenominator_le_exp (fun j : Fin n => q j.val)
          ((Fintype.card κ : ℝ) * Bphase) (fun j => hqbound j.val j.isLt)
    apply hbase.trans (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) (Nat.cast_nonneg _)) hBphase
  have hqQ (j : ℕ) (hj : j < n) : q j ∣ Q :=
    Finset.dvd_prod_of_mem (fun j : Fin n => q j.val) (Finset.mem_univ (⟨j, hj⟩ : Fin n))
  have htotal : ((qS * Q : ℕ) : ℝ) ≤ Real.exp p := by
    rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hQbound (Nat.cast_nonneg qS)).trans hdenbudget
  obtain ⟨m, hm, hmp, hdiv, hbound⟩ := hiteration F b ω hF w hw H p hH hp hι hσ hHp
    hstructure U S eQ B (Real.exp Bphase) qS Q (Real.exp_nonneg _)
    (Nat.mul_pos hqS hQpos) htotal hcost hSbound hSgrid
  let pS' := fun j => if j < n then pS j else 0
  let pR' := fun j => if j < n then pR j else 0
  have hpS' : ∀ j < s, ∀ α i, |eQ.repr (coefficients (pS' j) α) i| ≤ Real.exp Bphase := by
    intro j _ α i
    by_cases hj : j < n
    · simpa only [pS', if_pos hj] using hpS j hj α i
    · simpa only [pS', if_neg hj, map_zero, Finsupp.zero_apply, abs_zero] using
        Real.exp_nonneg Bphase
  have hpR' : ∀ j < s, ∀ α,
      (fun i => eQ.repr (coefficients (pR' j) α) i) ∈ realDenominatorGrid Q := by
    intro j _ α
    by_cases hj : j < n
    · simpa only [pR', if_pos hj] using
        realDenominatorGrid_subset_of_dvd (hqpos j hj) (hqQ j hj) (hpR j hj α)
    · refine ⟨0, ?_⟩
      funext i
      simp [pR', hj]
  have hprefix : F.restrictedMajorOuterFactors b ω hF w U S
      (fun j => realChartSubstitute f (pS' j)) pR' n =
      F.restrictedMajorOuterFactors b ω hF w U S
        (fun j => realChartSubstitute f (pS j)) pR n := by
    apply F.restrictedMajorOuterFactors_congr
    · intro j hj
      simp only [pS', if_pos hj]
    · intro j hj
      simp only [pR', if_pos hj]
  have hout := hbound f hf pS' pR' hpS' hpR' n hn
  dsimp only at hout ⊢
  rw [hprefix] at hout
  exact ⟨m, hm, hmp, hdiv, hout⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GlobalChartNativeFactorization
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

theorem weightedTop_aeval_monomial (w : σ → ℕ) (v : τ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) (γ : σ →₀ ℕ) (r : R) :
    weightedHomogeneousComponent v (Finsupp.weight w γ) (aeval β (monomial γ r)) =
      aeval (fun i => weightedHomogeneousComponent v (w i) (β i)) (monomial γ r) := by
  apply weightedHomogeneousComponent_eq_of_sub_lower
  · apply weightedComparison_monomial w v (aeval β)
      (aeval (fun i => weightedHomogeneousComponent v (w i) (β i)))
    · intro i
      simpa only [aeval_X] using hβ i
    · intro i
      simpa only [aeval_X] using weightedTopPart_preserves_degree v v (w i) (hβ i)
    · intro i
      simpa only [aeval_X] using weightedTopPart_remainder_lt v (hβ i)
  · exact isWeightedHomogeneous_aeval_monomial w v _
      (fun i => weightedHomogeneousComponent_isWeightedHomogeneous _ _) γ r

theorem coeff_aeval_monomial_eq_top (w : σ → ℕ) (v : τ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) (γ : σ →₀ ℕ) (r : R)
    (α : τ →₀ ℕ) (hweight : Finsupp.weight v α = Finsupp.weight w γ) :
    (aeval β (monomial γ r)).coeff α =
      (aeval (fun i => weightedHomogeneousComponent v (w i) (β i))
        (monomial γ r)).coeff α := by
  have h := congrArg (fun polynomial : MvPolynomial τ R => polynomial.coeff α)
    (weightedTop_aeval_monomial w v β hβ γ r)
  simpa only [coeff_weightedHomogeneousComponent, if_pos hweight] using h

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adapted_realChartSubstitute_homogeneous
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    {p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)} (hp : F.realification.Adapted w p) :
    F.realification.Adapted v (realChartSubstitute β p) := by
  classical
  apply (F.realification.adapted_iff_coefficients v _).mpr
  intro α
  rw [coefficients_realChartSubstitute]
  apply Submodule.sum_mem
  intro γ _
  by_cases hweight : Finsupp.weight v α = Finsupp.weight w γ
  · have hc := (F.realification.adapted_iff_coefficients w p).mp hp γ
    change _ ∈ (F.realLayer (Finsupp.weight v α)).toSubmodule
    rw [hweight]
    exact (F.realLayer _).toSubmodule.smul_mem _ hc
  · rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero _ hweight,
      zero_smul]
    exact Submodule.zero_mem _

attribute [local irreducible] realChartSubstitute

noncomputable def homogeneousAdaptedRealChartLie
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i)) :
    F.realification.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.realification.adaptedLieSubalgebra v where
  toLinearMap := ((realChartSubstitute β).comp
    (F.realification.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
      (F.realification.adaptedSubmodule v) (fun p =>
        (F.realification.mem_adaptedSubmodule v _).mpr
          (F.adapted_realChartSubstitute_homogeneous w v β hβ
            ((F.realification.mem_adaptedSubmodule w _).mp p.property)))
  map_lie' := by
    intro p q
    apply Subtype.ext
    exact realChartSubstitute_lie β (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
      (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))

@[simp] theorem homogeneousAdaptedRealChartLie_coe
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (p : F.realification.adaptedLieSubalgebra w) :
    (F.homogeneousAdaptedRealChartLie w v β hβ p : VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute β (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

noncomputable def homogeneousAdaptedRealChartHom
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i)) :
    (F.realification.adaptedPolynomialFiltration w).Group →*
      (F.realification.adaptedPolynomialFiltration v).Group :=
  NilpotentLieBCHGroup.map (F.homogeneousAdaptedRealChartLie w v β hβ)

@[simp] theorem homogeneousAdaptedRealChartHom_coord
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    ((F.homogeneousAdaptedRealChartHom w v β hβ g).coord :
        VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute β (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial
open scoped TensorProduct

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

theorem adapted_realChartSubstitute_weightedSupport
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    {p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)} (hp : F.realification.Adapted w p) :
    F.realification.Adapted v (realChartSubstitute β p) := by
  classical
  apply (F.realification.adapted_iff_coefficients v _).mpr
  intro α
  rw [coefficients_realChartSubstitute]
  apply Submodule.sum_mem
  intro γ _
  by_cases hc : (aeval β (monomial γ (1 : ℝ))).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · change _ ∈ (F.realLayer (Finsupp.weight v α)).toSubmodule
    apply (F.realLayer _).toSubmodule.smul_mem
    exact F.realLayer_antitone
      (aeval_monomial_weightedSupport β w v hβ γ (mem_support_iff.mpr hc))
      ((F.realification.adapted_iff_coefficients w p).mp hp γ)

attribute [local irreducible] realChartSubstitute

noncomputable def weightedAdaptedRealChartLie
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    F.realification.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.realification.adaptedLieSubalgebra v where
  toLinearMap := ((realChartSubstitute β).comp
    (F.realification.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
      (F.realification.adaptedSubmodule v) (fun p =>
        (F.realification.mem_adaptedSubmodule v _).mpr
          (F.adapted_realChartSubstitute_weightedSupport w v β hβ
            ((F.realification.mem_adaptedSubmodule w _).mp p.property)))
  map_lie' := by
    intro p q
    apply Subtype.ext
    exact realChartSubstitute_lie β (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
      (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))

@[simp] theorem weightedAdaptedRealChartLie_coe
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (p : F.realification.adaptedLieSubalgebra w) :
    (F.weightedAdaptedRealChartLie w v β hβ p : VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute β (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

noncomputable def weightedAdaptedRealChartHom
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    (F.realification.adaptedPolynomialFiltration w).Group →*
      (F.realification.adaptedPolynomialFiltration v).Group :=
  NilpotentLieBCHGroup.map (F.weightedAdaptedRealChartLie w v β hβ)

@[simp] theorem weightedAdaptedRealChartHom_coord
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    ((F.weightedAdaptedRealChartHom w v β hβ g).coord :
        VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute β (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial
open scoped TensorProduct BigOperators

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

attribute [local irreducible] realChartSubstitute realSymbolOfPolynomial

theorem realSymbolOfPolynomial_chart_eq_top
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hp : F.realification.Adapted w p) :
    F.realSymbolOfPolynomial b ω hF v (realChartSubstitute β p) =
      F.realSymbolOfPolynomial b ω hF v
        (realChartSubstitute (fun i => weightedHomogeneousComponent v (w i) (β i)) p) := by
  classical
  apply ((F.polynomialSymbolBasis b ω hF v).baseChange ℝ).repr.injective
  ext z
  rw [F.realSymbolOfPolynomial_coordinate, F.realSymbolOfPolynomial_coordinate,
    coefficients_realChartSubstitute, coefficients_realChartSubstitute]
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro γ _
  rcases lt_trichotomy (Finsupp.weight w γ) (ω z.val.2) with hlt | heq | hgt
  · have hzero : (aeval β (monomial γ (1 : ℝ))).coeff z.val.1 = 0 := by
      by_contra hc
      have hle := aeval_monomial_weightedSupport β w v hβ γ (mem_support_iff.mpr hc)
      have hz := z.property
      omega
    have htop : (aeval (fun i => weightedHomogeneousComponent v (w i) (β i))
        (monomial γ (1 : ℝ))).IsWeightedHomogeneous v (Finsupp.weight w γ) :=
      isWeightedHomogeneous_aeval_monomial w v _
        (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _) γ 1
    rw [hzero, htop.coeff_eq_zero _ (by have hz := z.property; omega)]
  · rw [coeff_aeval_monomial_eq_top w v β hβ γ 1 z.val.1
      (z.property.trans heq.symm)]
  · have hzero := (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp
      ((F.realification.adapted_iff_coefficients w p).mp hp γ) z.val.2 (by omega)
    rw [hzero, mul_zero, mul_zero]

theorem realSymbolOfPolynomial_inhomogeneousChart
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hp : F.realification.Adapted w p) :
    F.realSymbolOfPolynomial b ω hF v (realChartSubstitute β p) =
      F.realSymbolHomogeneousPullback b ω hF w v
        (fun i => weightedHomogeneousComponent v (w i) (β i))
        (F.realSymbolOfPolynomial b ω hF w p) := by
  rw [F.realSymbolOfPolynomial_chart_eq_top b ω hF w v β hβ p hp]
  exact F.realSymbolOfPolynomial_homogeneousChart b ω hF w v _
    (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _) p

theorem realPolynomialSymbolHom_weightedAdaptedRealChart
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialSymbolHom b ω hF v (F.weightedAdaptedRealChartHom w v β hβ g) =
      F.realSymbolHomogeneousPullbackHom b ω hF w v
        (fun i => weightedHomogeneousComponent v (w i) (β i))
        (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        (F.realPolynomialSymbolHom b ω hF w g) := by
  apply NilpotentLieBCHGroup.ext
  change F.realSymbolOfPolynomial b ω hF v
      ((F.weightedAdaptedRealChartHom w v β hβ g).coord :
        VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) = _
  rw [F.weightedAdaptedRealChartHom_coord]
  exact F.realSymbolOfPolynomial_inhomogeneousChart b ω hF w v β hβ _
    ((F.realification.mem_adaptedSubmodule w _).mp g.coord.property)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

theorem weightedRealChart_comp_support
    {σ τ υ : Type*} (w : σ → ℕ) (v : τ → ℕ) (u : υ → ℕ)
    (β : σ → MvPolynomial τ ℝ) (γ : τ → MvPolynomial υ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (hγ : ∀ i, γ i ∈ weightedSupportLE u (v i)) :
    ∀ i, MvPolynomial.aeval γ (β i) ∈ weightedSupportLE u (w i) :=
  fun i => weightedSupportLE_aeval v u γ hγ (hβ i)

namespace NilpotentLieFiltration
open VectorPolynomial
open scoped TensorProduct

variable {σ τ υ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

attribute [local irreducible] realChartSubstitute weightedAdaptedRealChartLie weightedAdaptedRealChartHom

theorem weightedAdaptedRealChartHom_comp
    (w : σ → ℕ) (v : τ → ℕ) (u : υ → ℕ)
    (β : σ → MvPolynomial τ ℝ) (γ : τ → MvPolynomial υ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (hγ : ∀ i, γ i ∈ weightedSupportLE u (v i))
    (hcomp : ∀ i, MvPolynomial.aeval γ (β i) ∈ weightedSupportLE u (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.weightedAdaptedRealChartHom w u (fun i => MvPolynomial.aeval γ (β i)) hcomp g =
      F.weightedAdaptedRealChartHom v u γ hγ (F.weightedAdaptedRealChartHom w v β hβ g) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  simp only [weightedAdaptedRealChartHom_coord]
  exact (realChartSubstitute_comp β γ _).symm

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realSymbolHomogeneousPullback_mem_pointwise
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded) (P : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U)) :
    (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ P).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v U) := by
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF v U _).mpr
  intro t
  rw [F.realSymbolHomogeneousPullbackHom_coord,
    F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
    eval₂_realChartSubstitute]
  exact (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w U P.coord).mp hP _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom realSymbolHomogeneousPullbackHom realPolynomialSymbolLift

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adaptedPolynomialRealValueHom_weightedChart
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (t : τ → ℝ) :
    F.adaptedPolynomialRealValueHom v t (F.weightedAdaptedRealChartHom w v β hβ g) =
      F.adaptedPolynomialRealValueHom w (fun i => MvPolynomial.eval t (β i)) g := by
  apply NilpotentLieBCHGroup.ext
  rw [F.adaptedPolynomialRealValueHom_coord, F.weightedAdaptedRealChartHom_coord,
    eval₂_realChartSubstitute, F.adaptedPolynomialRealValueHom_coord]

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realSymbolHomogeneousPullback_mem_of_range
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (K : Set (σ → ℝ)) (P : F.RealPolynomialSymbolGroup w)
    (hP : ∀ t ∈ K, eval₂ t (F.realGradedSymbolPolynomial b ω hF w P.coord) ∈
      W.toSubmodule.baseChange ℝ)
    (hK : ∀ t : τ → ℝ, (fun i => MvPolynomial.eval t (β i)) ∈ K) :
    (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ P).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v W) := by
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF v W _).mpr
  intro t
  rw [F.realSymbolHomogeneousPullbackHom_coord,
    F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
    eval₂_realChartSubstitute]
  exact hP _ (hK t)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GlobalMarkedChartwiseNormalization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem weightedAdaptedRealChartHom_constant
    (w : σ → ℕ) (v : τ → ℕ) (γ : σ → MvPolynomial τ ℝ)
    (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i)) (a : F.realification.Group) :
    F.weightedAdaptedRealChartHom w v γ hγ (F.realification.adaptedConstantGroupHom w a) =
      F.realification.adaptedConstantGroupHom v a := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  rw [F.weightedAdaptedRealChartHom_coord, F.realification.adaptedConstantGroupHom_log,
    F.realification.adaptedConstantGroupHom_log]
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro t
  simp only [map_sub, eval₂_realChartSubstitute, VectorPolynomial.eval₂_monomial,
    Finsupp.prod_zero_index, one_smul, sub_self]

theorem exists_chartwise_controlled_globalMarkedNativeFactors (s a : ℕ) :
    ∃ Ce Cr : ℕ, 2 ≤ Ce ∧ 2 ≤ Cr ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + Cr) ^ Cr) ∧ l ∣ n ∧
      ∀ (W : LieSubalgebra ℚ F.AssociatedGraded)
        (g e₀ r₀ : (F.realification.adaptedPolynomialFiltration w).Group)
        (E R : F.RealPolynomialSymbolGroup w),
      F.realPolynomialSymbolHom b ω hF w e₀ = E →
      F.realPolynomialSymbolHom b ω hF w r₀ = R →
      (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈
        realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W) →
      F.PolynomialRationalGrid b w l r₀ →
      ∃ A : GlobalMarkedNativeFactors F b ω hF w W g E R,
        F.PolynomialRationalGrid b w n A.right ∧
        ∀ {τ : Type*} [Fintype τ] (v : τ → ℕ), (∀ i, 0 < v i) →
          (Fintype.card τ : ℝ) ≤ p →
          ∀ (γ : σ → MvPolynomial τ ℝ)
            (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i))
            (T : τ → ℝ), (∀ i, 0 < T i) →
          F.PolynomialSlowBound b v T (Real.exp ((p + 2) ^ a))
            (F.weightedAdaptedRealChartHom w v γ hγ e₀) →
          F.PolynomialSlowBound b v T (Real.exp ((p + Ce) ^ Ce))
            (F.weightedAdaptedRealChartHom w v γ hγ A.left) := by
  obtain ⟨Ce, hCe, hslow⟩ := exists_polynomial_slow_product_bound s a 2
  obtain ⟨Cr, hCr, hrat⟩ := exists_polynomial_rational_product_bound s 2
  refine ⟨Ce, Cr, hCe, hCr, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H l p hH hl hp hι hσ hHp hlp hbracket
  obtain ⟨n, hn, hnp, hln, hproduct⟩ :=
    hrat F b ω hF w hw H p hH hp hι hσ hHp hbracket l hl hlp
  refine ⟨n, hn, hnp, hln, ?_⟩
  intro W g e₀ r₀ E R he hr hfast hrGrid
  obtain ⟨u, z, A, hu, hz, hleft, hright⟩ :=
    F.exists_globalMarkedNativeFactors_of_outer_lifts b ω hF w W hw g e₀ r₀ E R he hr hfast
  have hzGrid : (fun i => (b.baseChange ℝ).repr ((1 : ℝ) ⊗ₜ[ℚ] z) i) ∈
      realDenominatorGrid 1 := by
    classical
    choose k hk using hz
    refine ⟨k, ?_⟩
    funext i
    change (k i : ℝ) = (1 : ℕ) * (b.baseChange ℝ).repr ((1 : ℝ) ⊗ₜ[ℚ] z) i
    rw [Basis.baseChange_repr_tmul (S := ℝ), hk]
    simp only [Rat.smul_def, Rat.cast_intCast, mul_one, Nat.cast_one, one_mul]
  have hzPolynomial := F.polynomialRationalGrid_constant b w 1
    (⟨(1 : ℝ) ⊗ₜ[ℚ] z⟩ : F.realification.Group) hzGrid
  have hzPolynomial' := F.polynomialRationalGrid_of_dvd b w
    (by decide : 0 < 1) (one_dvd l) _ hzPolynomial
  have hrFinal := hproduct
    [F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] z⟩, r₀] (by simp)
    (by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact hzPolynomial'
      · exact hrGrid)
  refine ⟨A, ?_, ?_⟩
  · simpa only [List.prod_cons, List.prod_nil, mul_one, ← hright] using hrFinal
  · intro τ _ v hv hτ γ hγ T hT heSlow
    have huBound : ∀ i, |(b.baseChange ℝ).repr u i| ≤ Real.exp ((p + 2) ^ a) := by
      intro i
      rw [abs_of_nonneg (hu i).1]
      exact (hu i).2.le.trans (Real.one_le_exp (by positivity))
    have huSlow := F.polynomialSlowBound_constant b v T hT (Real.exp_nonneg _)
      (⟨u⟩ : F.realification.Group) huBound
    have heFinal := hslow F b ω hF v hv H p hH hp hι hτ hHp hbracket T hT
      [F.weightedAdaptedRealChartHom w v γ hγ e₀,
        F.realification.adaptedConstantGroupHom v ⟨u⟩] (by simp)
      (by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact heSlow
        · exact huSlow)
    rw [hleft, map_mul, F.weightedAdaptedRealChartHom_constant]
    simpa only [List.prod_cons, List.prod_nil, mul_one] using heFinal

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateEstimates
namespace OAI

section

namespace Erdos3

def refiltrationCoordinateBudget (p : ℝ) : ℝ :=
  ((p + 1 + (p + 3) ^ 7 + 2) ^ 9 + p + 4) ^ 4

theorem refiltrationCoordinateBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ refiltrationCoordinateBudget p := by
  unfold refiltrationCoordinateBudget
  positivity

namespace NilpotentLieFiltration

open Module

theorem exists_refiltration_bases_in_coordinates
    {ι κ ν L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis ν ℚ L) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (v : κ → F.AssociatedGraded) (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hv : ∀ i j, rationalLogHeight ((F.associatedGradedBasis e ω hF).repr (v i) j) ≤ p)
    (he : ∀ i j, rationalLogHeight (b.repr (e i) j) ≤ p) :
    ∀ d, ∃ a : Basis (Fin (finrank ℚ (F.gradedRefiltrationLayer U d))) ℚ
        (F.gradedRefiltrationLayer U d),
      ∀ i j, rationalLogHeight (b.repr (a i : L) j) ≤ refiltrationCoordinateBudget p := by
  let H := ⌈Real.exp p⌉₊
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  obtain ⟨B, _, hB, hbasis⟩ := F.exists_uniform_refiltration_layer_bases e ω hF U v hspan
    (one_le_ceil_exp p) (fun i j => rationalHeightLE_ceil_exp (hv i j))
    (by linarith : 0 ≤ p + 1) (hd.trans (by linarith)) (hκ.trans (by linarith)) hHp
  let r := (p + 1 + (p + 3) ^ 7 + 2) ^ 9
  have hBr : (B : ℝ) ≤ Real.exp r := by
    simpa only [r, show p + 1 + 2 = p + 3 by ring] using hB
  let t := r + p + 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hrt : r ≤ t := by dsimp [t]; linarith
  have hHt : (H : ℝ) ≤ Real.exp t :=
    hHp.trans (Real.exp_le_exp.mpr (by dsimp [t]; linarith))
  intro d
  obtain ⟨a, ha⟩ := hbasis d
  refine ⟨a, ?_⟩
  intro i j
  have hx : ∀ k, rationalLogHeight (e.repr (a i : L) k) ≤ t := fun k =>
    (rationalLogHeight_le_of_height (ha i k) hBr).trans hrt
  have h := rational_basis_coordinates_logHeight e b ht (hd.trans hpt) hHt
    (fun i j => rationalHeightLE_ceil_exp (he i j)) (a i : L) hx j
  have hshape : t + 2 = r + p + 4 := by dsimp [t]; ring
  rw [hshape] at h
  exact h

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3

def horizontalCoordinateBudget (p : ℝ) : ℝ :=
  p + p * (refiltrationCoordinateBudget p + 1 + (p + 3) ^ 7)

theorem horizontalCoordinateBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ horizontalCoordinateBudget p := by
  have h := refiltrationCoordinateBudget_nonneg hp
  unfold horizontalCoordinateBudget
  positivity

theorem horizontalCoordinateHeight_bound {p : ℝ} (hp : 0 ≤ p)
    (n H K : ℕ) (hn : (n : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp (refiltrationCoordinateBudget p + 1))
    (hK : (K : ℝ) ≤ Real.exp ((p + 3) ^ 7)) :
    (((n + 1) * (H * K) ^ n : ℕ) : ℝ) ≤ Real.exp (horizontalCoordinateBudget p) := by
  have hcount : (n : ℝ) + 1 ≤ Real.exp p := by
    linarith [Real.add_one_le_exp p]
  have hsum : 0 ≤ refiltrationCoordinateBudget p + 1 + (p + 3) ^ 7 := by
    have h := refiltrationCoordinateBudget_nonneg hp
    positivity
  calc
    _ ≤ Real.exp p * (Real.exp (refiltrationCoordinateBudget p + 1) *
        Real.exp ((p + 3) ^ 7)) ^ n := by
      push_cast
      gcongr
    _ = Real.exp (p + (n : ℝ) * (refiltrationCoordinateBudget p + 1 + (p + 3) ^ 7)) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (add_le_add le_rfl (mul_le_mul_of_nonneg_right hn hsum))

end Erdos3

end

section

namespace Erdos3

def nativeCoordinateBaseBudget (s : ℕ) (P : ℝ) : ℝ :=
  4 * P + (P + 3) ^ 7 + horizontalCoordinateBudget P +
    (s : ℝ) * P + (P + 3) ^ 2 + 4

def nativeCoordinateInputBudget (s : ℕ) (P : ℝ) : ℝ :=
  nativeCoordinateBaseBudget s P + (nativeCoordinateBaseBudget s P + 2) ^ 3 + P + 2

noncomputable def nativeDependentBudget (s : ℕ) (P : ℝ) : ℝ :=
  let Z := rankDependentInputBudget (nativeCoordinateInputBudget s P)
  Z + sparseGeneratorBudget Z

noncomputable def nativeCoordinateSeparationBudget (s : ℕ) (P : ℝ) : ℝ :=
  separationBudget (nativeCoordinateInputBudget s P) + separationBudget (nativeDependentBudget s P)

noncomputable def nativeDependentDenominatorBudget (s : ℕ) (P : ℝ) : ℝ :=
  nativeDependentBudget s P + (nativeDependentBudget s P + 2) ^ 3 +
    (nativeDependentBudget s P + 2) ^ 36

noncomputable def nativeDependentSlowBudget (s : ℕ) (P : ℝ) : ℝ :=
  (nativeDependentBudget s P + 2) ^ 3 + (nativeDependentBudget s P + 2) ^ 18 +
    nativeDependentBudget s P + 1

theorem nativeCoordinateBaseBudget_bounds (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ nativeCoordinateBaseBudget s P ∧ 4 * P ≤ nativeCoordinateBaseBudget s P ∧
      P ≤ nativeCoordinateBaseBudget s P ∧ (P + 3) ^ 7 + 1 ≤ nativeCoordinateBaseBudget s P ∧
      horizontalCoordinateBudget P + 1 ≤ nativeCoordinateBaseBudget s P ∧
      (P + 3) ^ 2 + (s : ℝ) * P ≤ nativeCoordinateBaseBudget s P := by
  have hH := horizontalCoordinateBudget_nonneg hP
  have h₇ : 0 ≤ (P + 3) ^ 7 := by positivity
  have h₂ : 0 ≤ (P + 3) ^ 2 := sq_nonneg _
  have hs : 0 ≤ (s : ℝ) * P := mul_nonneg (Nat.cast_nonneg s) hP
  unfold nativeCoordinateBaseBudget
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem nativeCoordinateInputBudget_bounds (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    nativeCoordinateBaseBudget s P ≤ nativeCoordinateInputBudget s P ∧
      (nativeCoordinateBaseBudget s P + 2) ^ 3 + P ≤ nativeCoordinateInputBudget s P ∧
      1 + (nativeCoordinateBaseBudget s P + 2) ^ 3 + nativeCoordinateBaseBudget s P ≤
        nativeCoordinateInputBudget s P := by
  have hU := (nativeCoordinateBaseBudget_bounds s hP).1
  have hc : 0 ≤ (nativeCoordinateBaseBudget s P + 2) ^ 3 := by positivity
  unfold nativeCoordinateInputBudget
  constructor
  · linarith
  constructor <;> linarith

theorem nativeCoordinateInputBudget_nonneg (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ nativeCoordinateInputBudget s P :=
  (nativeCoordinateBaseBudget_bounds s hP).1.trans (nativeCoordinateInputBudget_bounds s hP).1

theorem nativeDependentBudget_nonneg (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ nativeDependentBudget s P := by
  have hZ := (rankDependentInputBudget_bounds (nativeCoordinateInputBudget_nonneg s hP)).1
  exact add_nonneg hZ (sparseGeneratorBudget_nonneg hZ)

theorem nativeCoordinateSeparationBudget_cutoffs (s : ℕ) {P N : ℝ} (hP : 0 ≤ P)
    (hN : Real.exp (nativeCoordinateSeparationBudget s P) ≤ N) :
    Real.exp (separationBudget (nativeCoordinateInputBudget s P)) ≤ N ∧
      Real.exp (separationBudget (nativeDependentBudget s P)) ≤ N := by
  have h₁ := separationBudget_nonneg (nativeCoordinateInputBudget_nonneg s hP)
  have h₂ := separationBudget_nonneg (nativeDependentBudget_nonneg s hP)
  constructor
  · exact (Real.exp_le_exp.mpr (le_add_of_nonneg_right h₂)).trans hN
  · exact (Real.exp_le_exp.mpr (le_add_of_nonneg_left h₁)).trans hN

theorem nativeDependentSlowBudget_bound (s : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    Real.exp (nativeDependentBudget s P) +
        Real.exp ((nativeDependentBudget s P + 2) ^ 3 + (nativeDependentBudget s P + 2) ^ 18 +
          nativeDependentBudget s P) ≤ Real.exp (nativeDependentSlowBudget s P) := by
  let Q := nativeDependentBudget s P
  let L := (Q + 2) ^ 3 + (Q + 2) ^ 18 + Q
  have hQ : 0 ≤ Q := nativeDependentBudget_nonneg s hP
  have hQL : Q ≤ L := by
    have h₁ : 0 ≤ (Q + 2) ^ 3 := by positivity
    have h₂ : 0 ≤ (Q + 2) ^ 18 := by positivity
    dsimp only [L]
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    Real.exp Q + Real.exp L ≤ 2 * Real.exp L := by linarith [Real.exp_le_exp.mpr hQL]
    _ ≤ Real.exp 1 * Real.exp L := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (L + 1) := (mul_comm _ _).trans (Real.exp_add L 1).symm

end Erdos3

end

section

namespace Erdos3

theorem nativeCoordinate_denominator_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ] (s : ℕ) {P : ℝ} (hP : 0 ≤ P)
    (A : Matrix ι κ ℚ) (l : ℕ) (hl : (l : ℝ) ≤ Real.exp P)
    (hrows : (Fintype.card ι : ℝ) ≤ P) (hcols : (Fintype.card κ : ℝ) ≤ P)
    (hA : ∀ i j, rationalLogHeight (A i j) ≤ (P + 3) ^ 7) :
    ((matrixDenominator A * l : ℕ) : ℝ) ≤ Real.exp (nativeCoordinateInputBudget s P) := by
  obtain ⟨hU, _, hPU, hFU, _, _⟩ := nativeCoordinateBaseBudget_bounds s hP
  have hden : (matrixDenominator A : ℝ) ≤ Real.exp ((nativeCoordinateBaseBudget s P + 2) ^ 3) :=
    matrixDenominator_le_exp_power A hU 1 (hrows.trans hPU) (hcols.trans hPU) (by
      intro i j
      apply ((rationalLogHeight_le_iff (A i j) _).mp (hA i j)).2.trans
      apply Real.exp_le_exp.mpr
      simp only [pow_one]
      linarith)
  rw [Nat.cast_mul]
  calc
    (matrixDenominator A : ℝ) * l ≤
        Real.exp ((nativeCoordinateBaseBudget s P + 2) ^ 3) * Real.exp P :=
      mul_le_mul hden hl (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((nativeCoordinateBaseBudget s P + 2) ^ 3 + P) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (nativeCoordinateInputBudget_bounds s hP).2.1

theorem nativeCoordinate_slow_bound (s : ℕ) {P p : ℝ} (hP : 0 ≤ P) (hpP : p ≤ P)
    (n K : ℕ) (hn : (n : ℝ) ≤ P) (hK : (K : ℝ) ≤ Real.exp ((P + 3) ^ 7 + 1)) :
    2 * (((n : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)) ≤
      Real.exp (nativeCoordinateInputBudget s P) := by
  obtain ⟨hU, _, hPU, hFU, _, hSU⟩ := nativeCoordinateBaseBudget_bounds s hP
  let U := nativeCoordinateBaseBudget s P
  have hKU : (K : ℝ) ≤ Real.exp ((U + 2) ^ 1) := by
    apply hK.trans
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    linarith
  have hfac : ((n : ℝ) + 1) * (K + 1) ≤ Real.exp ((U + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power n hU (hn.trans hPU) 1 (by decide))
    exact mul_le_mul_of_nonneg_left (add_le_add hKU le_rfl) (by positivity)
  have hSU' : (P + 3) ^ 2 + (s : ℝ) * p ≤ U :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hpP (Nat.cast_nonneg s))).trans hSU
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    2 * (((n : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)) ≤
        Real.exp 1 * (Real.exp ((U + 2) ^ 3) * Real.exp U) :=
      mul_le_mul htwo (mul_le_mul hfac (Real.exp_le_exp.mpr hSU')
        (Real.exp_pos _).le (Real.exp_pos _).le) (by positivity) (Real.exp_pos _).le
    _ = Real.exp (1 + (U + 2) ^ 3 + U) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (nativeCoordinateInputBudget_bounds s hP).2.2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankRelationBudget
namespace OAI

section

namespace Erdos3

theorem exists_rank_relation_budget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let K := (p + a) ^ a
      let q := K + (K + c) ^ c + 2
      11 * q + 7 ≤ (p + C) ^ C ∧ mixedErrorPairBudget q ≤ (p + C) ^ C := by
  obtain ⟨b, _, hpair⟩ := exists_mixed_error_budget
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C a) ^ a
  let Z := Y + (Y + Polynomial.C c) ^ c + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (11 * Z + 7 + (Z + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp K q
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hterm : 0 ≤ (q + b) ^ b := by positivity
  have hbound : 11 * q + 7 + (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Y, Z, K, q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hterm, hbound],
    (hpair q hq).1.trans (by linarith only [hq, hbound])⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankRelationExistence
namespace OAI

section

namespace Erdos3

theorem rank_pair_density_loss (p : ℝ) :
    Real.exp (-(11 * p + 7)) ≤ Real.exp (-p) / 4 *
      (Real.exp (-(8 * p + 1)) * (Real.exp (-p) / 4) ^ 2) := by
  have he : Real.exp (-(8 * p + 1)) * Real.exp (-p) ^ 3 = Real.exp (-(11 * p + 1)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hright : Real.exp (-p) / 4 *
      (Real.exp (-(8 * p + 1)) * (Real.exp (-p) / 4) ^ 2) = Real.exp (-(11 * p + 1)) / 64 := by
    calc
      _ = (Real.exp (-(8 * p + 1)) * Real.exp (-p) ^ 3) / 64 := by ring
      _ = _ := by rw [he]
  rw [hright]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr
  have h64 := two_pow_le_exp_of_le 6 le_rfl
  norm_num at h64
  calc
    _ ≤ Real.exp (-(11 * p + 7)) * Real.exp 6 :=
      mul_le_mul_of_nonneg_left h64 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

structure NativeWeightedRankIntervals {s r N : ℕ} [NeZero N] {b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (out : Fin W.outputDim)
    (H : Finset (ZMod N)) (p : ℝ) where
  budget_two : 2 ≤ p
  count : ℕ
  count_pos : 0 < count
  index : Fin count → ZMod N × ZMod N × ZMod N
  index_injective : Function.Injective index
  density : Real.exp (-p) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ count
  first_mem : ∀ i, (index i).2.1 ∈ H
  second_mem : ∀ i, (index i).2.1 - (index i).1 ∈ H
  third_mem : ∀ i, (index i).2.2 ∈ H
  fourth_mem : ∀ i, (index i).2.2 - (index i).1 ∈ H
  integer_relation : ∀ i,
    -((index i).2.1.val : ℤ) + ((index i).2.1 - (index i).1).val +
      (index i).2.2.val - ((index i).2.2 - (index i).1).val = 0
  branch : Fin count → Bool
  start : Fin count → ℕ
  length : Fin count → ℕ
  length_pos : ∀ i, 0 < length i
  endpoint_le : ∀ i, start i + length i ≤ N
  length_short : ∀ i, 2 * ((length i : ℤ) - 1) < N
  length_ratio : ∀ i, Real.exp (-p) ≤ (length i : ℝ) / N
  weight : ℤ → ℂ
  weight_norm : ∀ n, ‖weight n‖ ≤ 1
  lower : Fin count → ℤ → ℂ
  expansion : ∀ i, NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) p (fun x => lower i (x ()))
  correlation : ∀ i, Real.exp (-p) ≤ ‖𝔼 n ∈ Finset.Ico (start i : ℤ) (start i + length i),
    fourPointProduct (W.eval out (index i).2.1) (W.eval out ((index i).2.1 - (index i).1))
      (W.eval out (index i).2.2) (W.eval out ((index i).2.2 - (index i).1))
      (cyclicBranchOffset (index i).1 (branch i)) n * weight n * lower i n‖

end Erdos3

end

section

namespace Erdos3

structure NativeAnchoredRankFibers {s r N : ℕ} [NeZero N] {b p : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} (F : NativeWeightedRankIntervals W out H p) where
  anchor : ZMod N
  branch : Bool
  selected : Finset (Fin F.count)
  parameters : Finset (ZMod N)
  parameters_nonempty : parameters.Nonempty
  parameters_density : Real.exp (-p) / 4 * (Fintype.card (ZMod N) : ℝ) ≤ parameters.card
  anchor_eq : ∀ i ∈ selected, (F.index i).2.2 = anchor
  branch_eq : ∀ i ∈ selected, F.branch i = branch
  pair_injective : Set.InjOn (fun i => ((F.index i).1, (F.index i).2.1)) (selected : Set (Fin F.count))
  fiber_density : ∀ a ∈ parameters, Real.exp (-p) / 4 * (Fintype.card (ZMod N) : ℝ) ≤
    ((selected.filter (fun i => (F.index i).1 = a)).card : ℝ)

namespace NativeWeightedRankIntervals

theorem exists_anchored_fibers {s r N : ℕ} [NeZero N] {b p : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} (F : NativeWeightedRankIntervals W out H p) :
    Nonempty (NativeAnchoredRankFibers F) := by
  have hindex : Function.Injective (fun i => ((F.index i).1, (F.index i).2.1, (F.index i).2.2)) :=
    F.index_injective
  have hsize : Real.exp (-p) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ Fintype.card (Fin F.count) := by
    simpa only [Fintype.card_fin] using F.density
  obtain ⟨anchor, branch, T, A, hA, hAsize, hT, hinj, hfiber⟩ := exists_dense_anchored_fibers
    (fun i => (F.index i).1) (fun i => (F.index i).2.1) (fun i => (F.index i).2.2)
    F.branch hindex (Real.exp_pos (-p)) hsize
  exact ⟨{
    anchor := anchor
    branch := branch
    selected := T
    parameters := A
    parameters_nonempty := hA
    parameters_density := hAsize
    anchor_eq := fun i hi => (hT i hi).1
    branch_eq := fun i hi => (hT i hi).2
    pair_injective := hinj
    fiber_density := hfiber }⟩

end NativeWeightedRankIntervals

namespace NativeAnchoredRankFibers

variable {s r N : ℕ} [NeZero N] {b p : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim} {H : Finset (ZMod N)}
  {F : NativeWeightedRankIntervals W out H p} (A : NativeAnchoredRankFibers F)

noncomputable def fiber (a : ZMod N) : Finset (Fin F.count) :=
  A.selected.filter (fun i => (F.index i).1 = a)

theorem fiber_nonempty (a : ZMod N) (ha : a ∈ A.parameters) : (A.fiber a).Nonempty := by
  have hN : (0 : ℝ) < Fintype.card (ZMod N) := by exact_mod_cast Fintype.card_pos
  have hpos : (0 : ℝ) < (A.fiber a).card :=
    lt_of_lt_of_le (by positivity) (A.fiber_density a ha)
  exact Finset.card_pos.mp (by exact_mod_cast hpos)

theorem fiber_parameter (a : ZMod N) (i : A.fiber a) : (F.index i.val).1 = a :=
  (Finset.mem_filter.mp i.property).2

theorem fiber_anchor (a : ZMod N) (i : A.fiber a) : (F.index i.val).2.2 = A.anchor :=
  A.anchor_eq i.val (Finset.mem_filter.mp i.property).1

theorem fiber_branch (a : ZMod N) (i : A.fiber a) : F.branch i.val = A.branch :=
  A.branch_eq i.val (Finset.mem_filter.mp i.property).1

theorem fiber_shift_injective (a : ZMod N) :
    Function.Injective (fun i : A.fiber a => (F.index i.val).2.1) := by
  intro i j hij
  apply Subtype.ext
  apply A.pair_injective (Finset.mem_filter.mp i.property).1 (Finset.mem_filter.mp j.property).1
  exact Prod.ext ((A.fiber_parameter a i).trans (A.fiber_parameter a j).symm) hij

end NativeAnchoredRankFibers

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

structure NativeRankInterval {s r N : ℕ} [NeZero N] {b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (out : Fin W.outputDim)
    (H : Finset (ZMod N)) (t : ZMod N × ZMod N × ZMod N)
    (branch : Bool) (p q : ℝ) where
  first_mem : t.2.1 ∈ H
  second_mem : t.2.1 - t.1 ∈ H
  third_mem : t.2.2 ∈ H
  fourth_mem : t.2.2 - t.1 ∈ H
  integer_relation :
    -(t.2.1.val : ℤ) + (t.2.1 - t.1).val + t.2.2.val - (t.2.2 - t.1).val = 0
  start : ℕ
  length : ℕ
  length_pos : 0 < length
  endpoint_le : start + length ≤ N
  length_short : 2 * ((length : ℤ) - 1) < N
  length_ratio : Real.exp (-p) ≤ (length : ℝ) / N
  lower : ℤ → ℂ
  expansion : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) q (fun x => lower (x ()))
  correlation : Real.exp (-p) ≤ ‖𝔼 n ∈ Finset.Ico (start : ℤ) (start + length),
    fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
      (W.eval out t.2.2) (W.eval out (t.2.2 - t.1))
      (cyclicBranchOffset t.1 branch) n * lower n‖

namespace NativeRankInterval

noncomputable def mono {s r N : ℕ} [NeZero N] {b p q p' q' : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
    (I : NativeRankInterval W out H t branch p q) (hp : p ≤ p') (hq : q ≤ q') :
    NativeRankInterval W out H t branch p' q' :=
  { I with
    length_ratio := (Real.exp_le_exp.mpr (neg_le_neg hp)).trans I.length_ratio
    expansion := I.expansion.mono hq
    correlation := (Real.exp_le_exp.mpr (neg_le_neg hp)).trans I.correlation }

end NativeRankInterval

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

namespace NativeAnchoredRankFibers

variable {s r N : ℕ} [NeZero N] {b p : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim} {H : Finset (ZMod N)}
  {F : NativeWeightedRankIntervals W out H p} (A : NativeAnchoredRankFibers F)

theorem exists_interval_pairs (a : ZMod N) (ha : a ∈ A.parameters) :
    ∃ Q : Finset (ZMod N × ZMod N), Q.Nonempty ∧
      Real.exp (-(8 * p + 1)) * ((A.fiber a).card : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, Nonempty (NativeRankInterval W out H (a, t) A.branch
        (8 * p + 1) (mixedErrorPairBudget p)) := by
  classical
  obtain ⟨i₀, hi₀⟩ := A.fiber_nonempty a ha
  let : Nonempty (A.fiber a) := ⟨⟨i₀, hi₀⟩⟩
  obtain ⟨Q, hQ, hQsize, hpair⟩ := native_interval_weight_pairs W out a A.anchor
    (cyclicBranchOffset a A.branch) (fun i : A.fiber a => (F.index i.val).2.1)
    (fun i => F.start i.val) (fun i => F.length i.val) F.weight
    (fun i => F.lower i.val) (fun i => F.expansion i.val) F.budget_two F.weight_norm
    (fun i => F.endpoint_le i.val) (fun i => F.length_short i.val)
    (fun i => F.length_ratio i.val) (fun i => by
      simpa only [A.fiber_parameter a i, A.fiber_anchor a i, A.fiber_branch a i]
        using F.correlation i.val)
  let e : (A.fiber a × A.fiber a) ↪ ZMod N × ZMod N := {
    toFun := fun t => ((F.index t.1.val).2.1, (F.index t.2.val).2.1)
    inj' := by
      intro t u htu
      obtain ⟨h₁, h₂⟩ := Prod.mk.inj htu
      exact Prod.ext (A.fiber_shift_injective a h₁) (A.fiber_shift_injective a h₂) }
  refine ⟨Q.map e, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hQ
    exact ⟨e t, Finset.mem_map.mpr ⟨t, ht, rfl⟩⟩
  · simpa only [Finset.card_map, Fintype.card_coe] using hQsize
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨c, len, hlen, hN, hshort, hsize, ⟨E⟩, hc⟩ := hpair u hu
    refine ⟨{
      first_mem := F.first_mem u.1.val
      second_mem := ?_
      third_mem := F.first_mem u.2.val
      fourth_mem := ?_
      integer_relation := ?_
      start := c
      length := len
      length_pos := hlen
      endpoint_le := hN
      length_short := hshort
      length_ratio := hsize
      lower := fun n => F.lower u.1.val n * star (F.lower u.2.val n)
      expansion := E
      correlation := hc }⟩
    · change (F.index u.1.val).2.1 - a ∈ H
      simpa only [A.fiber_parameter a u.1] using F.second_mem u.1.val
    · change (F.index u.2.val).2.1 - a ∈ H
      simpa only [A.fiber_parameter a u.2] using F.second_mem u.2.val
    · have h₁ := F.integer_relation u.1.val
      have h₂ := F.integer_relation u.2.val
      rw [A.fiber_parameter a u.1, A.fiber_anchor a u.1] at h₁
      rw [A.fiber_parameter a u.2, A.fiber_anchor a u.2] at h₂
      change -((F.index u.1.val).2.1.val : ℤ) + ((F.index u.1.val).2.1 - a).val +
        (F.index u.2.val).2.1.val - ((F.index u.2.val).2.1 - a).val = 0
      omega

end NativeAnchoredRankFibers

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}

theorem select_lower_term (I : NativeRankInterval W out H t branch p q) :
    ∃ i : Fin I.expansion.count, Real.exp (-(p + q)) ≤
      ‖𝔼 n ∈ Finset.Ico (I.start : ℤ) (I.start + I.length),
        fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
          (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n *
            (I.expansion.test i).eval (fun _ => n)‖ :=
  I.expansion.select_sample_product_correlation
    (Finset.Ico (I.start : ℤ) (I.start + I.length)) (fun n _ => n)
    (fun n => fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
      (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n)
    I.correlation

end NativeRankInterval

theorem exists_rank_interval_raised_lower_term (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
      (I : NativeRankInterval W out H t branch p q),
      ∃ i : Fin I.expansion.count,
        ∃ R : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r,
          R.ComplexityLE ((q + C) ^ C) ∧ R.realSubgroup s r = ⊥ ∧
          ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).ComplexityLE (raisedNiltestBudget q) ∧
          Real.exp (-(p + q)) ≤
            ‖𝔼 n ∈ Finset.Ico (I.start : ℤ) (I.start + I.length),
              fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
                (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n *
                  ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).eval (fun _ => n)‖ := by
  obtain ⟨C, hC, hraise⟩ := RationalFilteredNilmanifold.exists_raised_degree_rank_structure s
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q W out H t branch I
  obtain ⟨i, hi⟩ := I.select_lower_term
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans (I.expansion.complexity i).1.1
  have hsmall : s - 1 < s := by omega
  obtain ⟨R, hR, hzero⟩ := hraise (I.expansion.model i) hsmall
    W.rank.filtration.rank_le_degree hq (I.expansion.complexity i).1
  refine ⟨i, R, hR, hzero,
    (I.expansion.test i).raiseStep_complexity (Nat.sub_le s 1) hq (I.expansion.complexity i), ?_⟩
  simpa only [RationalFilteredNilmanifold.Niltest.raiseStep_eval] using hi

end Erdos3

end

section

namespace Erdos3

structure NativeRankRelation {s r N : ℕ} [NeZero N] {b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (out : Fin W.outputDim)
    (H : Finset (ZMod N)) (p q : ℝ) where
  quadruples : Finset (ZMod N × ZMod N × ZMod N)
  quadruples_nonempty : quadruples.Nonempty
  density : Real.exp (-p) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ quadruples.card
  branch : Bool
  interval : ∀ t : quadruples, NativeRankInterval W out H t.val branch p q

namespace NativeRankRelation

noncomputable def mono {s r N : ℕ} [NeZero N] {b p q p' q' : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} (R : NativeRankRelation W out H p q) (hp : p ≤ p') (hq : q ≤ q') :
    NativeRankRelation W out H p' q' :=
  { R with
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hp))
      (by positivity)).trans R.density
    interval := fun t => (R.interval t).mono hp hq }

end NativeRankRelation

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q)

theorem monomialScale_modulus_bound (hp : 0 ≤ p) (α : Unit →₀ ℕ)
    (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s) :
    monomialScale (fun _ : Unit => (N : ℝ)) α ≤
      Real.exp ((s : ℝ) * p) * monomialScale (fun _ : Unit => (I.length : ℝ)) α := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hlength : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hlower : Real.exp (-p) * (N : ℝ) ≤ I.length :=
    (le_div_iff₀ hN).mp I.length_ratio
  have hratio : (N : ℝ) ≤ Real.exp p * I.length := by
    calc
      (N : ℝ) = Real.exp p * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp p * I.length := mul_le_mul_of_nonneg_left hlower (Real.exp_pos _).le
  exact monomialScale_le_exp_mul _ _ (fun _ => hlength) (fun _ => hN) hp
    (fun _ => hratio) α hα

theorem norm_bound_on_modulus {ι : Type*} [Fintype ι]
    (hp : 0 ≤ p) (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    {M : ℝ} (hM : 0 ≤ M) (x : ι → ℝ)
    (hx : ‖x‖ ≤ M / monomialScale (fun _ : Unit => (I.length : ℝ)) α) :
    ‖x‖ ≤ (M * Real.exp ((s : ℝ) * p)) / monomialScale (fun _ : Unit => (N : ℝ)) α := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hlength : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  apply hx.trans
  apply (div_le_div_iff₀ (monomialScale_pos _ (fun _ => hlength) α)
    (monomialScale_pos _ (fun _ => hN) α)).mpr
  exact (mul_le_mul_of_nonneg_left (I.monomialScale_modulus_bound hp α hα) hM).trans_eq
    (mul_assoc _ _ _).symm

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q)

theorem length_lower_bound : Real.exp (-p) * N ≤ (I.length : ℝ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  exact (le_div_iff₀ hN).mp I.length_ratio

theorem length_exp_lower_bound {A : ℝ} (hN : Real.exp (p + A) ≤ N) :
    Real.exp A ≤ (I.length : ℝ) := by
  calc
    Real.exp A = Real.exp (-p) * Real.exp (p + A) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-p) * N := mul_le_mul_of_nonneg_left hN (Real.exp_pos _).le
    _ ≤ I.length := I.length_lower_bound

end Erdos3.NativeRankInterval

end

section

namespace Erdos3

namespace NativeWeightedRankIntervals

theorem remove_weight {s r N : ℕ} [NeZero N] {b p : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} (F : NativeWeightedRankIntervals W out H p) :
    Nonempty (NativeRankRelation W out H (11 * p + 7) (mixedErrorPairBudget p)) := by
  classical
  obtain ⟨A⟩ := F.exists_anchored_fibers
  have hdata (a : A.parameters) := A.exists_interval_pairs a.val a.property
  choose P _ hPsize hP using hdata
  have hpair (a : A.parameters) :
      (Real.exp (-(8 * p + 1)) * (Real.exp (-p) / 4) ^ 2) *
        (Fintype.card (ZMod N) : ℝ) ^ 2 ≤ ((P a).card : ℝ) := by
    have hf := A.fiber_density a.val a.property
    calc
      _ = Real.exp (-(8 * p + 1)) *
          (Real.exp (-p) / 4 * (Fintype.card (ZMod N) : ℝ)) ^ 2 := by ring
      _ ≤ Real.exp (-(8 * p + 1)) * ((A.fiber a.val).card : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        exact pow_le_pow_left₀ (by positivity) hf 2
      _ ≤ _ := hPsize a
  obtain ⟨Q, hQsize, hQmem⟩ := dense_triple_fibers A.parameters P
    (by positivity) A.parameters_density hpair
  have hdense : Real.exp (-(11 * p + 7)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) :=
    (mul_le_mul_of_nonneg_right (rank_pair_density_loss p) (by positivity)).trans hQsize
  have hN : (0 : ℝ) < Fintype.card (ZMod N) := by exact_mod_cast Fintype.card_pos
  have hQpos : (0 : ℝ) < Q.card := lt_of_lt_of_le (by positivity) hdense
  have hbudget : 8 * p + 1 ≤ 11 * p + 7 := by linarith only [F.budget_two]
  have hinterval (t : Q) : Nonempty
      (NativeRankInterval W out H t.val A.branch (11 * p + 7) (mixedErrorPairBudget p)) := by
    obtain ⟨a, ha, ht⟩ := (hQmem t.val).mp t.property
    obtain ⟨I⟩ := hP a t.val.2 ht
    have heq : (a.val, t.val.2) = t.val := Prod.ext ha rfl
    rw [heq] at I
    exact ⟨I.mono hbudget le_rfl⟩
  exact ⟨{
    quadruples := Q
    quadruples_nonempty := Finset.card_pos.mp (by exact_mod_cast hQpos)
    density := hdense
    branch := A.branch
    interval := fun t => Classical.choice (hinterval t) }⟩

end NativeWeightedRankIntervals

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ScalarSymbolFamilyCoefficientGrid
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι J L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
  (w : σ → ℕ)

theorem scalarSymbolPolynomial_family_rational_coefficients [Fintype ι] [Fintype J]
    (θ : J → F.AssociatedGraded →ₗ[ℚ] ℚ) (m : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w m g)
    (j : J) :
    realPolynomialCoefficientGrid
      (matrixDenominator (fun j i => θ j (F.associatedGradedBasis b ω hF i)) * m)
      (F.scalarSymbolPolynomial b ω hF w (θ j) g) := by
  classical
  let ℓ : F.AssociatedGraded →ₗ[ℚ] (J → ℚ) := LinearMap.pi θ
  have h : ∀ α : σ →₀ ℕ, ∃ z : J → ℤ,
      (fun j => (z j : ℝ)) =
        ((matrixDenominator (fun j i => θ j (F.associatedGradedBasis b ω hF i)) * m : ℕ) : ℝ) •
          realifyCoordinateMap ℓ
            (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) := by
    intro α
    exact realifyCoordinateMap_grid (F.associatedGradedBasis b ω hF) ℓ m _
      (F.realGradedSymbolPolynomial_rational_coordinates b ω hF w m g hg α)
  choose z hz using h
  refine ⟨fun α => z α j, funext fun α => ?_⟩
  change (z α j : ℝ) =
    ((matrixDenominator (fun j i => θ j (F.associatedGradedBasis b ω hF i)) * m : ℕ) : ℝ) *
      (F.scalarSymbolPolynomial b ω hF w (θ j) g).coeff α
  rw [F.coeff_scalarSymbolPolynomial]
  have hθ : (LinearMap.proj j).comp ℓ = θ j := by ext; rfl
  have hα := congrFun (hz α) j
  change (z α j : ℝ) = _ * realifyFunctional ((LinearMap.proj j).comp ℓ) _ at hα
  rwa [hθ] at hα

theorem scalarSymbolPolynomial_family_exists_coefficient_grid [Fintype ι] [Fintype J]
    (θ : J → F.AssociatedGraded →ₗ[ℚ] ℚ) {H : ℕ}
    (hθ : ∀ j i, RationalHeightLE (θ j (F.associatedGradedBasis b ω hF i)) H)
    (m : ℕ) (hm : 0 < m) (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolRationalGrid b ω hF w m g) :
    ∃ q : ℕ, 0 < q ∧ q ≤ H ^ (Fintype.card J * Fintype.card ι) * m ∧
      ∀ j, realPolynomialCoefficientGrid q (F.scalarSymbolPolynomial b ω hF w (θ j) g) := by
  refine ⟨_, Nat.mul_pos (matrixDenominator_pos _) hm,
    Nat.mul_le_mul_right m (matrixDenominator_le _ hθ), ?_⟩
  exact F.scalarSymbolPolynomial_family_rational_coefficients b ω hF w θ m g hg

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SymbolCoordinateFreezeBounds
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {I R : Type*} [CommRing R]

theorem freezePolynomial_zero_eq_killCompl (keep : I → Prop) :
    freezePolynomial keep (0 : {i // ¬keep i} → R) =
      MvPolynomial.killCompl (f := (Subtype.val : {i // keep i} → I)) Subtype.val_injective := by
  classical
  apply MvPolynomial.algHom_ext
  intro i
  simp only [freezePolynomial, MvPolynomial.killCompl, aeval_X]
  by_cases hi : keep i
  · have hr : i ∈ Set.range (Subtype.val : {i // keep i} → I) := ⟨⟨i, hi⟩, rfl⟩
    simp only [frozenCoordinate, dif_pos hi, dif_pos hr]
    congr 1
    exact (Equiv.ofInjective_symm_apply Subtype.val_injective ⟨i, hi⟩).symm
  · have hr : i ∉ Set.range (Subtype.val : {i // keep i} → I) := by
      rintro ⟨⟨j, hj⟩, rfl⟩
      exact hi hj
    simp only [frozenCoordinate, dif_neg hi, dif_neg hr, Pi.zero_apply, map_zero]

theorem coeff_freezePolynomial_zero (keep : I → Prop) (P : MvPolynomial I R)
    (α : {i // keep i} →₀ ℕ) :
    (freezePolynomial keep (0 : {i // ¬keep i} → R) P).coeff α =
      P.coeff (α.mapDomain Subtype.val) := by
  rw [freezePolynomial_zero_eq_killCompl]
  exact MvPolynomial.coeff_killCompl Subtype.val_injective

theorem coeff_aeval_frozenCoordinate_zero (keep : I → Prop) (P : MvPolynomial I R)
    (α : {i // keep i} →₀ ℕ) :
    (aeval (frozenCoordinate keep (0 : {i // ¬keep i} → R)) P).coeff α =
      P.coeff (α.mapDomain Subtype.val) :=
  coeff_freezePolynomial_zero keep P α

end Erdos3

end

section

namespace Erdos3
open Module
open scoped Classical

namespace VectorPolynomial

variable {I ι V : Type*} [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V]
  [IsScalarTower ℚ ℝ V]

theorem coordinate_coeff_realChartSubstitute_freeze_zero
    (keep : I → Prop) (b : Basis ι ℝ V) (P : VectorPolynomial I ℚ V)
    (α : {i // keep i} →₀ ℕ) (i : ι) :
    b.repr (coefficients (realChartSubstitute (frozenCoordinate keep 0) P) α) i =
      b.repr (coefficients P (α.mapDomain Subtype.val)) i := by
  have h := congrArg (fun Q : MvPolynomial {i // keep i} ℝ => Q.coeff α)
    (coordinate_realChartSubstitute_for_grid (frozenCoordinate keep 0) (b.coord i) P)
  rw [coeff_aeval_frozenCoordinate_zero] at h
  simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe, Basis.coord_apply] using h

end VectorPolynomial

namespace NilpotentLieFiltration
open VectorPolynomial

attribute [local irreducible] realChartSubstitute realGradedSymbolPolynomial realSymbolHomogeneousPullback realGradedSymbolPolynomialHom

variable {I ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualMarkedSlowKernelCells
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_bounded_subgroup_net
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H : ℕ}
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (K : Subgroup (NilpotentLieBCHGroup L s hnil))
    (B : ℝ≥0) (hB : 1 ≤ B) {N : ℕ} (hN : 0 < N) :
    let := rightMetricSpace (hnil := hnil) e
    ∃ center : (ι → Fin (N + 1)) → NilpotentLieBCHGroup L s hnil,
      (∀ j, center j ∈ K) ∧
      (∀ j i, |e.repr (center j).coord i| ≤ B) ∧
      ∀ g : NilpotentLieBCHGroup L s hnil, g ∈ K →
        (∀ i, |e.repr g.coord i| ≤ B) →
        ∃ j, dist g (center j) ≤
          bchBoxMetricConstant s (Fintype.card ι) H B * (4 * B / N) := by
  classical
  let := rightMetricSpace (hnil := hnil) e
  let Ω := {g : NilpotentLieBCHGroup L s hnil //
    g ∈ K ∧ ∀ i, |e.repr g.coord i| ≤ B}
  have hBr : (1 : ℝ) ≤ B := hB
  let : Nonempty Ω := ⟨⟨1, K.one_mem, by simp⟩⟩
  obtain ⟨code, rep, hrep⟩ := exists_uniform_parameter_net
    (fun g : Ω => e.equivFun g.val.coord) (by positivity : (0 : ℝ) < B)
    (fun g i => g.property.2 i) hN
  refine ⟨fun j => (rep j).val, fun j => (rep j).property.1,
    fun j i => (rep j).property.2 i, ?_⟩
  intro g hg hgb
  let x : Ω := ⟨g, hg, hgb⟩
  refine ⟨code x, ?_⟩
  apply dist_le_bchBoxMetricConstant e c hstructure hc B hB (by positivity)
    g (rep (code x)).val hgb (rep (code x)).property.2
  intro i
  exact (show |e.repr g.coord i - e.repr (rep (code x)).val.coord i| ≤
      dist (e.equivFun x.val.coord) (e.equivFun (rep (code x)).val.coord) from
    by simpa only [Real.dist_eq, Basis.equivFun_apply, x] using
      dist_le_pi_dist (e.equivFun x.val.coord)
        (e.equivFun (rep (code x)).val.coord) i).trans (hrep x)

theorem exists_bounded_kernel_net {G : Type*} [Group G]
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H : ℕ}
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (π : NilpotentLieBCHGroup L s hnil →* G)
    (B : ℝ≥0) (hB : 1 ≤ B) {N : ℕ} (hN : 0 < N) :
    let := rightMetricSpace (hnil := hnil) e
    ∃ center : (ι → Fin (N + 1)) → NilpotentLieBCHGroup L s hnil,
      (∀ j, π (center j) = 1) ∧
      (∀ j i, |e.repr (center j).coord i| ≤ B) ∧
      ∀ g : NilpotentLieBCHGroup L s hnil, π g = 1 →
        (∀ i, |e.repr g.coord i| ≤ B) →
        ∃ j, dist g (center j) ≤
          bchBoxMetricConstant s (Fintype.card ι) H B * (4 * B / N) := by
  exact exists_bounded_subgroup_net e c hstructure hc π.ker B hB hN

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_bounded_kernel_net_with_budget {G : Type*} [Group G]
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H : ℕ}
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (π : NilpotentLieBCHGroup L s hnil →* G)
    (B : ℝ≥0) (hB : 1 ≤ B) {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hd : (Fintype.card ι : ℝ) ≤ p) (hBp : (B : ℝ) ≤ Real.exp p)
    (hK : (bchBoxMetricConstant s (Fintype.card ι) H B : ℝ) ≤ Real.exp p)
    (hεinv : 1 / ε ≤ Real.exp p) :
    letI := rightMetricSpace (hnil := hnil) e
    ∃ N : ℕ, 0 < N ∧
      (Fintype.card (ι → Fin (N + 1)) : ℝ) ≤
        Real.exp ((p + 1) * (3 * (p + 1) + 4)) ∧
      ∃ center : (ι → Fin (N + 1)) → NilpotentLieBCHGroup L s hnil,
        (∀ j, π (center j) = 1) ∧
        (∀ j i, |e.repr (center j).coord i| ≤ B) ∧
        ∀ g : NilpotentLieBCHGroup L s hnil, π g = 1 →
          (∀ i, |e.repr g.coord i| ≤ B) →
          ∃ j, dist g (center j) ≤ ε := by
  classical
  let := rightMetricSpace (hnil := hnil) e
  let K := bchBoxMetricConstant s (Fintype.card ι) H B
  let N := boxCoverMeshCount (2 * B) K ε
  have hN : 0 < N := boxCoverMeshCount_pos _ _ _
  have hexp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hBp' : 2 * (B : ℝ) ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    exact (mul_le_mul_of_nonneg_left hBp (by norm_num)).trans
      (by nlinarith [Real.exp_pos p])
  have hcard := boxCoverCount_dimension_bound (Fintype.card ι) K
    (by positivity : 0 ≤ 2 * (B : ℝ)) hε (by linarith : 0 ≤ p + 1)
    (by linarith : (Fintype.card ι : ℝ) ≤ p + 1) hBp' (hK.trans hexp)
    (hεinv.trans hexp)
  obtain ⟨center, hmark, hbound, hnet⟩ :=
    exists_bounded_kernel_net e c hstructure hc π B hB hN
  refine ⟨N, hN, ?_, center, hmark, hbound, ?_⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hcard
  · intro g hg hgb
    obtain ⟨j, hj⟩ := hnet g hg hgb
    refine ⟨j, hj.trans ?_⟩
    have hm := boxCoverMeshCount_error (B := 2 * (B : ℝ)) K hε
    dsimp only [N, K] at *
    simpa only [show (2 : ℝ) * (2 * B) = 4 * B by ring] using hm

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3
open scoped NNReal

theorem exists_slow_kernel_net_geometry_budget (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d n H : ℕ) (p A : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (n : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      0 ≤ A → A ≤ Real.exp ((p + 2) ^ r) →
      ∃ B : ℝ≥0, 1 ≤ B ∧
        ((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * A ≤ B ∧
        (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (bchBoxMetricConstant s d H B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (bchBoxMetricConstant s d H B : ℝ) *
          (((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * A * n * s) ≤
            Real.exp ((p + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let P := Polynomial.C s * (X + 1) + (X + 2) ^ r
  obtain ⟨a, _, hP⟩ := exists_natPolynomial_eval_budget P
  obtain ⟨b, _, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s a
  let Q := (X + Polynomial.C a + Polynomial.C b) ^ b + P + X + Polynomial.C s
  obtain ⟨C, hC, hQ⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro d n H p A hp hd hn hH hA hAp
  let q : ℝ := s * (p + 1) + (p + 2) ^ r
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let B : ℝ≥0 := ⟨Real.exp q, (Real.exp_pos _).le⟩
  have hB : 1 ≤ B := Real.one_le_exp hq
  have hn1 : (n : ℝ) + 1 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hAM : ((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * A ≤ Real.exp q := by
    calc
      _ ≤ Real.exp s * (Real.exp p) ^ s * Real.exp ((p + 2) ^ r) :=
        mul_le_mul (mul_le_mul (Real.add_one_le_exp (s : ℝ))
          (pow_le_pow_left₀ (by positivity) hn1 _) (by positivity) (Real.exp_pos _).le)
          hAp hA (by positivity)
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [q]
        ring
  have hpA : p ≤ p + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hBa : (B : ℝ) ≤ Real.exp (((p + a) + 2) ^ a) := by
    apply Real.exp_le_exp.mpr
    have h' : q ≤ (p + a) ^ a := by simpa [P, X, q, Polynomial.eval₂_pow] using hP p hp
    exact h'.trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
  have hBC : (bchBoxMetricConstant s d H B : ℝ) ≤ Real.exp ((p + a + b) ^ b) :=
    hbox d H B (p + a) (hp.trans hpA) (hd.trans hpA)
      (hH.trans (Real.exp_le_exp.mpr hpA)) hBa
  have hfinal : (p + a + b) ^ b + q + p + s ≤ (p + C) ^ C := by
    simpa [Q, P, X, q, Polynomial.eval₂_pow] using hQ p hp
  have hbase : 0 ≤ (p + a + b) ^ b := by positivity
  have hnexp : (n : ℝ) ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hsexp : (s : ℝ) ≤ Real.exp s := by linarith [Real.add_one_le_exp (s : ℝ)]
  refine ⟨B, hB, hAM, Real.exp_le_exp.mpr (by linarith),
    hBC.trans (Real.exp_le_exp.mpr (by linarith)), ?_⟩
  calc
    _ ≤ Real.exp ((p + a + b) ^ b) * (Real.exp q * Real.exp p * Real.exp s) := by
      apply mul_le_mul hBC
        (mul_le_mul (mul_le_mul hAM hnexp (Nat.cast_nonneg _) (Real.exp_pos _).le)
          hsexp (Nat.cast_nonneg _) (by positivity))
        (by positivity) (Real.exp_pos _).le
    _ = Real.exp (((p + a + b) ^ b) + q + p + s) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hfinal

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ ι L G : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] [_root_.Group G] {s : ℕ}

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ ι L G : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
  [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] [_root_.Group G] {s : ℕ}

theorem exists_slow_kernel_cells
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (π : F.realification.Group →* G)
    (H : ℕ) (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A : ℝ} (hA : 0 ≤ A)
    (B : ℝ≥0) (hB : 1 ≤ B)
    (hAB : ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * A ≤ B)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hd : (Fintype.card ι : ℝ) ≤ p) (hn : (Fintype.card σ : ℝ) ≤ p)
    (hBp : (B : ℝ) ≤ Real.exp p)
    (hK : (bchBoxMetricConstant s (Fintype.card ι) H B : ℝ) ≤ Real.exp p)
    (hmove : (bchBoxMetricConstant s (Fintype.card ι) H B : ℝ) *
      (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * A * Fintype.card σ * s) ≤
        Real.exp p)
    (hεinv : 1 / ε ≤ Real.exp p) :
    letI := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
    ∃ N M : ℕ, 0 < N ∧ 0 < M ∧
      (Fintype.card (ι → Fin (N + 1)) : ℝ) ≤ Real.exp ((p + 2) * (3 * (p + 2) + 4)) ∧
      (Fintype.card (σ → Fin (M + 1)) : ℝ) ≤ Real.exp ((p + 1) * (3 * (p + 1) + 4)) ∧
      ∃ center : (ι → Fin (N + 1)) → F.realification.Group,
        (∀ j, π (center j) = 1) ∧
        (∀ j i, |(b.baseChange ℝ).repr (center j).coord i| ≤ B) ∧
        ∀ g : (F.realification.adaptedPolynomialFiltration w).Group,
          F.PolynomialSlowBound b w T A g →
          (∀ z, π (F.adaptedPolynomialRealValueHom w z g) = 1) →
          ∃ label : (σ → Fin (M + 1)) → (ι → Fin (N + 1)),
            ∀ j (v : σ → ℝ), (∀ i, |v i| ≤ T i) →
              (∀ i, |v i - normalizedRealBoxGrid T M j i| ≤ T i * (2 / M)) →
              dist (F.adaptedPolynomialRealValueHom w v g) (center (label j)) ≤ ε := by
  classical
  let := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
  have hhalf : 0 < ε / 2 := by positivity
  have hexp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  have hinv : 1 / (ε / 2) ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * (1 / ε) := by ring
      _ ≤ 2 * Real.exp p := mul_le_mul_of_nonneg_left hεinv (by norm_num)
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  obtain ⟨N, hN, hNcard, center, hmark, hbound, hnet⟩ :=
    exists_bounded_kernel_net_with_budget (b.baseChange ℝ) (lieStructureConstants b)
      (fun i j k => (realLieBasis_structure b i j k).symm) hc π B hB hhalf
      (by linarith : 0 ≤ p + 1) (by linarith : (Fintype.card ι : ℝ) ≤ p + 1)
      (hBp.trans hexp) (hK.trans hexp) hinv
  let K : ℝ≥0 := ⟨(bchBoxMetricConstant s (Fintype.card ι) H B : ℝ) *
    (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * A * Fintype.card σ * s),
      by positivity⟩
  let M := boxCoverMeshCount 1 K (ε / 2)
  have hM : 0 < M := boxCoverMeshCount_pos _ _ _
  have hMcard := boxCoverCount_dimension_bound (Fintype.card σ) K
    (by norm_num : (0 : ℝ) ≤ 1) hhalf (by linarith : 0 ≤ p + 1)
    (by linarith : (Fintype.card σ : ℝ) ≤ p + 1)
    (Real.one_le_exp (by linarith)) (hmove.trans hexp) hinv
  refine ⟨N, M, hN, hM, ?_, ?_, center, hmark, hbound, ?_⟩
  · simpa only [add_assoc, one_add_one_eq_two] using hNcard
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hMcard
  · intro g hg hker
    have hz (j : σ → Fin (M + 1)) (i : σ) :
        |normalizedRealBoxGrid T M j i| ≤ T i := normalizedRealBoxGrid_bound T hT hM j i
    choose label hlabel using fun j : σ → Fin (M + 1) =>
      hnet (F.adaptedPolynomialRealValueHom w (normalizedRealBoxGrid T M j) g)
        (hker _) (fun i =>
          (F.polynomialSlowBound_value b w hw T hT hA g hg _ (hz j) i).trans hAB)
    refine ⟨label, ?_⟩
    intro j v hv hvz
    have hm := F.polynomialSlowBound_dist_le b w hw H hc T hT hA
      (by positivity : (0 : ℝ) ≤ 2 / M) B hB hAB g hg v
      (normalizedRealBoxGrid T M j) hv (hz j) hvz
    have herr : dist (F.adaptedPolynomialRealValueHom w v g)
        (F.adaptedPolynomialRealValueHom w (normalizedRealBoxGrid T M j) g) ≤ ε / 2 := by
      apply hm.trans
      have he := boxCoverMeshCount_error (B := (1 : ℝ)) K hhalf
      change (K : ℝ) * (2 / (M : ℝ)) ≤ ε / 2
      simpa only [mul_one] using he
    calc
      _ ≤ dist (F.adaptedPolynomialRealValueHom w v g)
          (F.adaptedPolynomialRealValueHom w (normalizedRealBoxGrid T M j) g) +
        dist (F.adaptedPolynomialRealValueHom w (normalizedRealBoxGrid T M j) g)
          (center (label j)) := dist_triangle _ _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add herr (hlabel j)
      _ = ε := by ring

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_slow_kernel_cells (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ ι L G : Type*}
      [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] [_root_.Group G]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (π : F.realification.Group →* G) (H : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      letI := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
      ∃ N M : ℕ, 0 < N ∧ 0 < M ∧
        (Fintype.card (ι → Fin (N + 1)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (Fintype.card (σ → Fin (M + 1)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ center : (ι → Fin (N + 1)) → F.realification.Group,
          (∀ j, π (center j) = 1) ∧
          (∀ j i, |(b.baseChange ℝ).repr (center j).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∀ g : (F.realification.adaptedPolynomialFiltration w).Group,
            F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ r)) g →
            (∀ z, π (F.adaptedPolynomialRealValueHom w z g) = 1) →
            ∃ label : (σ → Fin (M + 1)) → (ι → Fin (N + 1)),
              ∀ j (v : σ → ℝ), (∀ i, |v i| ≤ T i) →
                (∀ i, |v i - normalizedRealBoxGrid T M j i| ≤ T i * (2 / M)) →
                dist (F.adaptedPolynomialRealValueHom w v g) (center (label j)) ≤
                  Real.exp (-((p + 2) ^ r)) := by
  obtain ⟨a, ha, hgeometry⟩ := exists_slow_kernel_net_geometry_budget s r
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C a) ^ a + (X + 2) ^ r
  let P := Q + (Q + 2) * (3 * (Q + 2) + 4)
  obtain ⟨C, hC, hP⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι L G _ _ _ _ _ _ _ _ _ _ _ F b w hw π H p hp hd hn hH hc T hT
  let := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
  obtain ⟨B, hB, hAB, hBcap, hK, hmove⟩ := hgeometry
    (Fintype.card ι) (Fintype.card σ) H p (Real.exp ((p + 2) ^ r))
    hp hd hn hH (Real.exp_nonneg _) le_rfl
  let q : ℝ := p + (p + a) ^ a + (p + 2) ^ r
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ha0 : 0 ≤ (p + a) ^ a := by positivity
  have hr0 : 0 ≤ (p + 2) ^ r := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have haq : (p + a) ^ a ≤ q := by dsimp [q]; linarith
  have hrq : (p + 2) ^ r ≤ q := by dsimp [q]; linarith
  have hinv : 1 / Real.exp (-((p + 2) ^ r)) ≤ Real.exp q := by
    rw [Real.exp_neg]
    simpa only [one_div, inv_inv] using Real.exp_le_exp.mpr hrq
  obtain ⟨N, M, hN, hM, hNcard, hMcard, center, hmark, hbound, hfreeze⟩ :=
    F.exists_slow_kernel_cells b w hw π H hc T hT (Real.exp_nonneg _) B hB hAB
      (Real.exp_pos _) hq (hd.trans hpq) (hn.trans hpq)
      (hBcap.trans (Real.exp_le_exp.mpr haq))
      (hK.trans (Real.exp_le_exp.mpr haq))
      (hmove.trans (Real.exp_le_exp.mpr haq)) hinv
  have hbudget : q + (q + 2) * (3 * (q + 2) + 4) ≤ (p + C) ^ C := by
    simpa [P, Q, X, q, Polynomial.eval₂_pow] using hP p hp
  have hcard : (q + 2) * (3 * (q + 2) + 4) ≤ (p + C) ^ C := by linarith
  have hqcap : q ≤ (p + C) ^ C := by
    have : 0 ≤ (q + 2) * (3 * (q + 2) + 4) := by positivity
    linarith
  refine ⟨N, M, hN, hM, hNcard.trans (Real.exp_le_exp.mpr hcard),
    hMcard.trans (Real.exp_le_exp.mpr ?_), center, hmark, ?_, hfreeze⟩
  · exact (show (q + 1) * (3 * (q + 1) + 4) ≤ (q + 2) * (3 * (q + 2) + 4) by
      nlinarith).trans hcard
  · intro j i
    exact (hbound j i).trans (hBcap.trans (Real.exp_le_exp.mpr (haq.trans hqcap)))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_actual_marked_slow_kernel_cells (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ ι κ L M : Type*}
      [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {t : ℕ}
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
      (b : Basis ι ℚ L) (c : Basis κ ℚ M) (ω : ι → ℕ),
      (∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) →
      ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
        (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j),
      Function.RightInverse S φ →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) →
      (∀ i j, |(b.repr (S (c j)) i : ℝ)| ≤ Real.exp ((p + 2) ^ a)) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      letI := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
      ∃ N Q : ℕ, 0 < N ∧ 0 < Q ∧
        (Fintype.card (ι → Fin (N + 1)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ center : (ι → Fin (N + 1)) → F.realification.Group,
          (∀ j, realificationMap (hnil := F.lowerCentralSeries_eq_bot)
            (hM := G.lowerCentralSeries_eq_bot) φ (center j) = 1) ∧
          (∀ j i, |(b.baseChange ℝ).repr (center j).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∀ (E : (F.realification.adaptedPolynomialFiltration w).Group)
            (EF : (G.realification.adaptedPolynomialFiltration w).Group),
            F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a)) E →
            G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ a)) EF →
            F.realPolynomialGroupMap G φ hφ w E = EF →
            ∃ label : (σ → Fin (Q + 1)) → (ι → Fin (N + 1)),
              ∀ j (v : σ → ℝ), (∀ i, |v i| ≤ T i) →
                (∀ i, |v i - normalizedRealBoxGrid T Q j i| ≤ T i * (2 / Q)) →
                dist (F.adaptedPolynomialRealValueHom w v
                  (E * (F.filteredRealPolynomialSection G w S hS EF)⁻¹))
                  (center (label j)) ≤ Real.exp (-((p + 2) ^ u)) := by
  obtain ⟨A, hA, hslow⟩ := exists_marked_polynomial_kernel_slow_bound s a
  obtain ⟨B, hB, hnet⟩ := exists_uniform_slow_kernel_cells s (A + u)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ _ _ _ _ _ _ t F G b c ω hF w hw φ hφ S hS
    hsection H p hH hp hι hκ hσ hHp hc hSbound T hT
  let := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
  let π := realificationMap (hnil := F.lowerCentralSeries_eq_bot)
    (hM := G.lowerCentralSeries_eq_bot) φ
  have hpA : p ≤ p + A := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hpA0 : 0 ≤ p + A := hp.trans hpA
  obtain ⟨N, Q, hN, hQ, hNcard, hQcard, center, hmark, hcap, hfreeze⟩ :=
    hnet F b w hw π H (p + A) hpA0 (hι.trans hpA) (hσ.trans hpA)
      (hHp.trans (Real.exp_le_exp.mpr hpA)) hc T hT
  have hcost : (p + A + B) ^ B ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨N, Q, hN, hQ, hNcard.trans (Real.exp_le_exp.mpr hcost),
    hQcard.trans (Real.exp_le_exp.mpr hcost), center, hmark,
    fun j i => (hcap j i).trans (Real.exp_le_exp.mpr hcost), ?_⟩
  intro E EF hE hEF hproj
  have hKE := (hslow F G b c ω hF w hw H p hH hp hι hκ hσ hHp hc S hS
    (by simpa only [scalarExtension_basis_coordinates] using hSbound) T hT E EF hE hEF).1
  have hbound : (p + A) ^ A ≤ (p + A + 2) ^ (A + u) :=
    (pow_le_pow_left₀ hpA0 (by linarith : p + A ≤ p + A + 2) A).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + A + 2) (by omega))
  have hKEslow := F.polynomialSlowBound_mono b w T hT
    (Real.exp_le_exp.mpr hbound) _ hKE
  have hmap : F.realPolynomialGroupMap G φ hφ w
      (E * (F.filteredRealPolynomialSection G w S hS EF)⁻¹) = 1 := by
    rw [map_mul, map_inv, hproj,
      F.realPolynomialGroupMap_filteredSection G w φ hφ S hS hsection EF, mul_inv_cancel]
  have hker (v : σ → ℝ) : π (F.adaptedPolynomialRealValueHom w v
      (E * (F.filteredRealPolynomialSection G w S hS EF)⁻¹)) = 1 := by
    rw [← F.realPolynomialGroupMap_value G φ hφ w, hmap, map_one]
  obtain ⟨label, hlabel⟩ := hfreeze _ hKEslow hker
  refine ⟨label, ?_⟩
  intro j v hv hvj
  apply (hlabel j v hv hvj).trans
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ p + 2)
    (by linarith : p + 2 ≤ p + A + 2) u).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + A + 2) (by omega))

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedPhysicalGridMask
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]
variable (T : Fin m → ℝ)

noncomputable def allocatedPhysicalGridCondition
    (z : AllocatedFrozenJetRows B U b S O) : Prop :=
  ∀ (j : Fin m) (i : Fin (n j)) (hg : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (t : O j), |(z ⟨⟨j, Sum.inr i⟩, hg⟩ t : ℝ) / basisAxisScale (b j) i| ≤ T j * R j

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [∀ j, DecidableEq (O j)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (hT : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalHomogeneousSymbolPullbackGrid
namespace OAI

section

namespace Erdos3
open Module _root_.MvPolynomial
open scoped TensorProduct

namespace VectorPolynomial

variable {σ τ ι V : Type*} [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V]
  [IsScalarTower ℚ ℝ V]

theorem CoefficientGrid.realChartSubstitute_rational
    (b : Basis ι ℝ V) (q D d : ℕ) (P : VectorPolynomial σ ℚ V)
    (hdegree : DegreeLE (fun _ => 1) d P) (hP : CoefficientGrid b q P)
    (A : σ → MvPolynomial τ ℝ)
    (hA : ∀ i, realPolynomialCoefficientGrid D (A i)) :
    CoefficientGrid b (q * D ^ d) (realChartSubstitute A P) := by
  rw [coefficientGrid_iff_coordinate]
  intro i
  rw [coordinate_realChartSubstitute_for_grid]
  exact realPolynomialCoefficientGrid_substitute
    (coordinate (b.coord i).toAddMonoidHom P) A q D d
    ((degreeLE_one_iff_basis_totalDegree b d P).mp hdegree i)
    ((coefficientGrid_iff_coordinate b q P).mp hP i) hA

end VectorPolynomial

namespace NilpotentLieFiltration
open VectorPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (v : τ → ℕ)

theorem realGradedSymbolPolynomial_degreeLE_one
    (hw : ∀ i, 0 < w i) (R : F.RealPolynomialSymbolGroup w) :
    DegreeLE (fun _ => 1) s (F.realGradedSymbolPolynomial b ω hF w R.coord) := by
  intro α hα
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  apply F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w R.coord α i
  have hi := F.adaptedBasis_weight_le_step b ω hF i
  have hweight := exponentSum_le_positive_weight w hw α
  have hone : Finsupp.weight (fun _ : σ => 1) α = α.sum (fun _ n => n) := by
    simp [Finsupp.weight_apply]
  rw [hone] at hα
  omega

theorem symbolRationalGrid_homogeneousPullback_rational_of_coefficientGrid
    (hw : ∀ i, 0 < w i)
    (A : σ → MvPolynomial τ ℝ)
    (hA : ∀ i, (A i).IsWeightedHomogeneous v (w i))
    (q D : ℕ) (hAD : ∀ i, realPolynomialCoefficientGrid D (A i))
    (R : F.RealPolynomialSymbolGroup w)
    (hR : CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
      (F.realGradedSymbolPolynomial b ω hF w R.coord)) :
    F.SymbolRationalGrid b ω hF v (q * D ^ s)
      (F.realSymbolHomogeneousPullbackHom b ω hF w v A hA R) := by
  apply F.symbolRationalGrid_of_gradedPolynomial b ω hF v (q * D ^ s)
  change CoefficientGrid _ (q * D ^ s)
    (F.realGradedSymbolPolynomial b ω hF v
      (F.realSymbolHomogeneousPullback b ω hF w v A R.coord))
  rw [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v A hA]
  with_reducible exact (CoefficientGrid.realChartSubstitute_rational
    (V := ℝ ⊗[ℚ] F.AssociatedGraded)
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) q D s
    (F.realGradedSymbolPolynomial b ω hF w R.coord)
    (F.realGradedSymbolPolynomial_degreeLE_one b ω hF w hw R) hR A hAD)

end NilpotentLieFiltration
end Erdos3

end

end OAI

end


