-- Prove2me | Definitions.Def_OAIErdos3B117
-- name    : OAIErdos3B117
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T01:38:27.437532+00:00
-- url     : https://prove2.me/theorems/85df742e-c4fa-4bba-890d-4ca4194bcf73
-- title:
--   OpenAI Erdős-3 split, definitions bundle 118 of 132
-- statement:
--   Definitions bundle 118 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B116`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 118 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.FastCoefficientCoordinateSpec`, `OAI.Erdos3.NilpotentLieFiltration.UniformFastCoefficientCoordinateSpec`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_real_fast_coefficient_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.exists_fast_coefficient_coordinate_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_real_fast_coefficient_unitriangular_basis`, `OAI.Erdos3.NilpotentLieFiltration.exists_uniform_fast_coefficient_coordinate_bound`, `OAI.Erdos3.NilpotentLieFiltration.fastCoefficientAdjoint_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.fastCoefficientDerivative_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.fastCoefficientDirectionCoordinates`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientIndex_grade_eq_of_monomial_eq`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientAdjoint_unitriangular`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_common_integral_models`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_common_rational_model_coordinates`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_common_rational_model_power`, `OAI.Erdos3.SpatialMatrixBlockIndex`, `OAI.Erdos3.VectorPolynomial.allocatedSeparatedCongruencePolynomial`, `OAI.Erdos3.VectorPolynomial.allocatedSpatialRankPolynomial_kernel_selected_long`, `OAI.Erdos3.VectorPolynomial.allocatedUnconditionedCongruenceIntegerPolynomial`, `OAI.Erdos3.centeredFinite_spatial_modular_good_set`, `OAI.Erdos3.clippedSelectedDeterminant`, `OAI.Erdos3.clippedSelectedDeterminant_lipschitz`, `OAI.Erdos3.common_subalgebra_cost_le_budget`, `OAI.Erdos3.determinantCutoff_lip_le_exp`, `OAI.Erdos3.exists_common_bounded_moduli`, `OAI.Erdos3.exists_common_fast_subalgebra`, `OAI.Erdos3.exists_common_fast_subalgebra_and_denominator`, `OAI.Erdos3.exists_common_height_bounded_subalgebra`, `OAI.Erdos3.exists_common_log_height_subalgebra`, `OAI.Erdos3.exists_common_positive_nat`, `OAI.Erdos3.exists_jointSpatialError_polynomial_budget`, `OAI.Erdos3.jointExceptionalGainBudget`, `OAI.Erdos3.jointSpatialError`, `OAI.Erdos3.jointSpatialError_inverse_le_exp`, `OAI.Erdos3.jointSpatialError_pos`, `OAI.Erdos3.latticeBasis_integerCoordinates`, `OAI.Erdos3.latticeGaussian_integer_periodic`, `OAI.Erdos3.nat_mul_factorial_le_exp_square`, `OAI.Erdos3.normalizedDeterminantCutoff`, `OAI.Erdos3.normalizedDeterminantCutoff_eq_one`, `OAI.Erdos3.normalizedDeterminantCutoff_eq_zero`, `OAI.Erdos3.normalizedDeterminantCutoff_indicator_bounds`, `OAI.Erdos3.normalizedDeterminantCutoff_lipschitz`, `OAI.Erdos3.normalizedDeterminantCutoff_range`, `OAI.Erdos3.realRationalCoordinateSpan_iInf`, `OAI.Erdos3.realRationalCoordinateSpan_iInf_basis`, `OAI.Erdos3.realRationalCoordinateSpan_top`, `OAI.Erdos3.rectangularLatticePoint_reindex`, `OAI.Erdos3.samplerFrozenRaw`, `OAI.Erdos3.samplerLong_killCompl_common`, `OAI.Erdos3.samplerSeparatedVariable`, `OAI.Erdos3.samplerSeparatedVariable_active`, `OAI.Erdos3.samplerSeparatedVariable_common`, `OAI.Erdos3.samplerSeparatedVariable_inactive`, `OAI.Erdos3.shiftedSmoothProductPMF_reindex`, `OAI.Erdos3.spatialKernelRankSlot`, `OAI.Erdos3.spatialKernelRankSlot_injective`, `OAI.Erdos3.spatialMatrixBlockBad`, `OAI.Erdos3.spatialMatrixBlockCutoff`, `OAI.Erdos3.spatialMatrixBlockCutoff_indicator_bounds`, `OAI.Erdos3.spatialMatrixBlockCutoff_lip_exp_budget`, `OAI.Erdos3.spatialMatrixBlockCutoff_lipschitz`, `OAI.Erdos3.spatialMatrixBlockCutoff_range`, `OAI.Erdos3.spatialMatrixBlockEntry`, `OAI.Erdos3.spatialMatrixBlockEntry_apply`, `OAI.Erdos3.spatialMatrixBlockEntry_reindex_eval`, `OAI.Erdos3.spatialMatrixBlockEntry_symm`, `OAI.Erdos3.spatialMatrixBlockEquiv`, `OAI.Erdos3.spatialMatrixBlockSlot`, `OAI.Erdos3.spatialMatrixBlockThreshold`, `OAI.Erdos3.spatialMatrixBlockThreshold_inverse_le_exp`, `OAI.Erdos3.spatialMatrixBlockThreshold_pos`, `OAI.Erdos3.spatialMatrixBlock_bad_probability`, `OAI.Erdos3.spatialMatrixBlock_bad_probability_of_exp_width`, `OAI.Erdos3.spatialMatrixBlock_cellMass_pos`, `OAI.Erdos3.spatialMatrixBlock_flat_bad_probability`, `OAI.Erdos3.spatialMatrixBlock_residue_bad_probability`, `OAI.Erdos3.spatialMatrixIndexCenter`, `OAI.Erdos3.spatialMatrixIndexMass_pos`, `OAI.Erdos3.spatialMatrixIndexPMF_marginal`, `OAI.Erdos3.spatialMatrixIndexWidth`, `OAI.Erdos3.spatialMatrixIndexWidth_pos`, `OAI.Erdos3.spatialMatrixNormalizedEntries`, `OAI.Erdos3.spatialMatrixNormalizedEntries_residue`, `OAI.Erdos3.spatialMatrixNormalizedEntries_residue_law`, `OAI.Erdos3.spatialRankExponent`, `OAI.Erdos3.spatialRankPolynomial`, `OAI.Erdos3.spatialRankPolynomial_conditioned_top_congr`, `OAI.Erdos3.spatialRankPolynomial_degree`, `OAI.Erdos3.spatialRankPolynomial_eq`, `OAI.Erdos3.spatialRankPolynomial_kernel_selected`, `OAI.Erdos3.spatialRankPolynomial_kernel_selected_long`, `OAI.Erdos3.spatialRankPolynomial_kernel_selected_top`, `OAI.Erdos3.spatialRankPolynomial_top`, `OAI.Erdos3.spatialRankPolynomial_top_congr`, `OAI.Erdos3.unitTestClip_eq_self`, `OAI.Erdos3.unitTestClip_lipschitz`, `OAI.Erdos3.unitTestClip_norm_le_one`, `_private.Dynamics.JointExceptionalGainBudget.0.OAI.Erdos3.jointExceptional_exp_eight`, `_private.Estimates.NormalizedDeterminantCutoff.0.OAI.Erdos3.real_perm_sign_norm`, `_private.Estimates.RationalTagConstraintSpaces.0.OAI.Erdos3.VectorPolynomial.RationalTagConstraint.exists_function_spanning_logHeight`, `_private.Linear.SpatialMatrixBlockWideProbability.0.OAI.Erdos3.spatialMatrix_decide_eq_classical`, `_private.Linear.SpatialMatrixBlockWideProbability.0.OAI.Erdos3.spatial_kernel_selected_raw`, `_private.Linear.SpatialMatrixBlockWideProbability.0.OAI.Erdos3.spatial_kernel_selected_sum`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B037

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonRationalModelCoordinates
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_common_rational_model_coordinates
    {G : Type*} {L : G → Type*} [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)]
    {s d : ℕ} (D : ∀ h, RationalFilteredNilmanifold (L h) s d)
    (H : Finset G) (hH : H.Nonempty) {p : ℝ} (hp : 0 ≤ p)
    (hD : ∀ h ∈ H, (D h).GeometryComplexityLE p) :
    ∃ h₀ ∈ H, ∃ H' : Finset G, H' ⊆ H ∧ h₀ ∈ H' ∧
      (∀ h ∈ H', (D h).rationalModelCoordinates = (D h₀).rationalModelCoordinates) ∧
      Real.exp (-(3 * (d ^ 3 + (s + 1) * d ^ 2 : ℕ) * (p + 2))) * H.card ≤ (H'.card : ℝ) := by
  let S : Set (RationalModelCoordinateIndex s d → ℚ) :=
    {c | ∀ z, rationalLogHeight (c z) ≤ p}
  obtain ⟨hfinite, hcount⟩ := finite_card_bounded_height_arrays S ⌈Real.exp p⌉₊
    (fun _ hc z => rationalHeightLE_ceil_exp (hc z))
  have hcount' : (S.ncard : ℝ) ≤ Real.exp (3 * (d ^ 3 + (s + 1) * d ^ 2 : ℕ) * (p + 2)) := by
    have hh := (Nat.cast_le.mpr hcount).trans
      (rational_log_height_count_exp_bound (Fintype.card (RationalModelCoordinateIndex s d)) hp)
    have hdim : Fintype.card (RationalModelCoordinateIndex s d) = d ^ 3 + (s + 1) * d ^ 2 := by
      simp only [RationalModelCoordinateIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      ring
    simpa only [hdim] using hh
  obtain ⟨c, _, H', hsub, hnonempty, hcode, hlarge⟩ :=
    exists_exponential_constant_fiber H hH (fun h => (D h).rationalModelCoordinates)
      S hfinite (fun h hh => (D h).rationalModelCoordinates_height hp (hD h hh)) hcount'
  obtain ⟨h₀, hh₀⟩ := hnonempty
  exact ⟨h₀, hsub hh₀, H', hsub, hh₀,
    (fun h hh => (hcode h hh).trans (hcode h₀ hh₀).symm), hlarge⟩

theorem exists_common_rational_model_power (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)] {d : ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s d) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h ∈ H, (D h).GeometryComplexityLE p) →
      ∃ h₀ ∈ H, ∃ H' : Finset G, H' ⊆ H ∧ h₀ ∈ H' ∧
        (∀ h ∈ H', (D h).rationalModelCoordinates = (D h₀).rationalModelCoordinates) ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) := by
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (3 * (X ^ 3 + Polynomial.C (s + 1) * X ^ 2) * (X + 2))
  refine ⟨C, hC, ?_⟩
  intro G L _ _ d D H hH p hp hD
  obtain ⟨h₀, hh₀, H', hsub, hh₀', heq, hlarge⟩ :=
    exists_common_rational_model_coordinates D H hH hp hD
  have hd := (hD h₀ hh₀).1
  have hb : 3 * (d ^ 3 + (s + 1) * d ^ 2 : ℕ) * (p + 2) ≤ (p + C) ^ C := by
    have hb' : 3 * (p ^ 3 + (s + 1 : ℕ) * p ^ 2) * (p + 2) ≤ (p + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget p hp
    apply le_trans _ hb'
    push_cast
    gcongr
  exact ⟨h₀, hh₀, H', hsub, hh₀', heq,
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hb))
      (Nat.cast_nonneg _)).trans hlarge⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonIntegralModelEquivalences
namespace OAI

section

namespace Erdos3

open Module

variable {α ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  (e : Basis ι ℚ L) (S : Finset α) (hS : S.Nonempty) (K : α → LieSubalgebra ℚ L)

include hS in
theorem exists_common_height_bounded_subalgebra (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hK : ∀ a ∈ S, K a ∈ heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      Real.exp (-(3 * (m : ℝ) * Fintype.card ι * (A + 2))) * S.card ≤ (T.card : ℝ) := by
  obtain ⟨U, _, T, hTS, hT, hU, hlarge⟩ := exists_exponential_constant_fiber S hS K
    (heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊)
    (finite_card_heightBoundedLieSubalgebras e m ⌈Real.exp A⌉₊).1 hK
    (heightBoundedLieSubalgebras_ncard_exp_bound e m hA)
  obtain ⟨a₀, ha₀⟩ := hT
  exact ⟨a₀, hTS ha₀, T, hTS, ha₀, fun a ha => (hU a ha).trans (hU a₀ ha₀).symm, hlarge⟩

include hS in
theorem exists_common_log_height_subalgebra (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hK : ∀ a ∈ S, ∃ v : Fin m → L,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ A) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      Real.exp (-(3 * (m : ℝ) * Fintype.card ι * (A + 2))) * S.card ≤ (T.card : ℝ) := by
  apply exists_common_height_bounded_subalgebra e S hS K m hA
  intro a ha
  obtain ⟨v, hv, hh⟩ := hK a ha
  exact (mem_heightBoundedSubspaces e m ⌈Real.exp A⌉₊ (K a).toSubmodule).mpr
    ⟨v, hv, fun i j => rationalHeightLE_ceil_exp (hh i j)⟩

theorem common_subalgebra_cost_le_budget (m d : ℕ) {A p : ℝ} (hp : 0 ≤ p)
    (hm : (m : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) (hA : 0 ≤ A) (hAp : A ≤ p) :
    3 * (m : ℝ) * d * (A + 2) ≤ (p + 2) ^ 5 := by
  have hm' : (m : ℝ) ≤ p + 2 := by linarith
  have hd' : (d : ℝ) ≤ p + 2 := by linarith
  calc
    _ ≤ 3 * (p + 2) * (p + 2) * (p + 2) := by gcongr
    _ = 3 * (p + 2) ^ 3 := by ring
    _ ≤ (p + 2) ^ 2 * (p + 2) ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    _ = (p + 2) ^ 5 := by ring

include hS in
theorem exists_common_fast_subalgebra (m : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hm : (m : ℝ) ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hK : ∀ a ∈ S, ∃ v : Fin m → L,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ p) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      Real.exp (-((p + 2) ^ 5)) * S.card ≤ (T.card : ℝ) := by
  obtain ⟨a₀, ha₀, T, hTS, haT, hcommon, hlarge⟩ :=
    exists_common_log_height_subalgebra e S hS K m hp hK
  refine ⟨a₀, ha₀, T, hTS, haT, hcommon, ?_⟩
  apply le_trans _ hlarge
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (common_subalgebra_cost_le_budget m (Fintype.card ι) hp hm hd hp le_rfl)

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {α σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (e : Basis ι ℚ (F.squareFiltration.PolynomialSymbol w))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

theorem exists_common_bounded_moduli {G κ : Type*} [Fintype κ]
    (S : Finset G) (hS : S.Nonempty) (moduli : G → κ → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hmoduli : ∀ a ∈ S, ∀ i, (moduli a i : ℝ) ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset G, T ⊆ S ∧ a₀ ∈ T ∧
      (∀ a ∈ T, moduli a = moduli a₀) ∧
      Real.exp (-((p + 1) * Fintype.card κ)) * S.card ≤ (T.card : ℝ) := by
  classical
  let N := ⌊Real.exp p⌋₊
  let tag : G → κ → Fin (N + 1) := fun a i =>
    ⟨min (moduli a i) N, (min_le_right _ _).trans_lt (Nat.lt_succ_self _)⟩
  have htag : ∀ a ∈ S, ∀ i, (tag a i).val = moduli a i := by
    intro a ha i
    exact min_eq_left (Nat.le_floor (hmoduli a ha i))
  have hbase : ((N + 1 : ℕ) : ℝ) ≤ Real.exp (p + 1) := by
    have h1 : 1 ≤ Real.exp p := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hp
    have h2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    rw [Nat.cast_add, Nat.cast_one]
    calc
      (N : ℝ) + 1 ≤ Real.exp p + Real.exp p :=
        add_le_add (Nat.floor_le (Real.exp_pos p).le) h1
      _ = Real.exp p * 2 := by ring
      _ ≤ Real.exp p * Real.exp 1 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos p).le
      _ = _ := (Real.exp_add p 1).symm
  have hcount : ((Set.univ : Set (κ → Fin (N + 1))).ncard : ℝ) ≤
      Real.exp ((p + 1) * Fintype.card κ) := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (p + 1) ^ Fintype.card κ := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨q, _, T, hTS, hT, hconstant, hlarge⟩ := exists_exponential_constant_fiber
    S hS tag Set.univ Set.finite_univ (fun _ _ => Set.mem_univ _) hcount
  obtain ⟨a₀, ha₀⟩ := hT
  refine ⟨a₀, hTS ha₀, T, hTS, ha₀, ?_, hlarge⟩
  intro a ha
  funext i
  have h := congrArg (fun f : κ → Fin (N + 1) => (f i).val)
    ((hconstant a ha).trans (hconstant a₀ ha₀).symm)
  simpa only [htag a (hTS ha) i, htag a₀ (hTS ha₀) i] using h

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {α σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (e : Basis ι ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

theorem exists_common_positive_nat {α : Type*} (S : Finset α) (hS : S.Nonempty)
    (n : α → ℕ) {p : ℝ} (hn : ∀ a ∈ S, 0 < n a ∧ (n a : ℝ) ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, n a = n a₀) ∧
      Real.exp (-p) * S.card ≤ (T.card : ℝ) := by
  let A := Finset.Icc 1 ⌊Real.exp p⌋₊
  have hA : ((A : Set ℕ).ncard : ℝ) ≤ Real.exp p := by
    simpa only [A, Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel] using
      (Nat.floor_le (Real.exp_nonneg p))
  obtain ⟨k, _, T, hTS, hT, hk, hlarge⟩ := exists_exponential_constant_fiber S hS n
    (A : Set ℕ) A.finite_toSet
    (fun a ha => Finset.mem_Icc.mpr ⟨(hn a ha).1, Nat.le_floor (hn a ha).2⟩) hA
  obtain ⟨a₀, ha₀⟩ := hT
  exact ⟨a₀, hTS ha₀, T, hTS, ha₀, fun a ha => (hk a ha).trans (hk a₀ ha₀).symm, hlarge⟩

theorem exists_common_fast_subalgebra_and_denominator
    {α ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (S : Finset α) (hS : S.Nonempty)
    (K : α → LieSubalgebra ℚ L) (n : α → ℕ) (m : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hK : ∀ a ∈ S, ∃ v : Fin m → L,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ p)
    (hn : ∀ a ∈ S, 0 < n a ∧ (n a : ℝ) ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧
      (∀ a ∈ T, K a = K a₀ ∧ n a = n a₀) ∧
      Real.exp (-((p + 2) ^ 5 + p)) * S.card ≤ (T.card : ℝ) := by
  obtain ⟨b, _, U, hUS, hbU, hKsame, hUlarge⟩ :=
    exists_common_fast_subalgebra e S hS K m hp hm hd hK
  obtain ⟨a₀, haU, T, hTU, haT, hnsame, hTlarge⟩ :=
    exists_common_positive_nat U ⟨b, hbU⟩ n (fun a ha => hn a (hUS ha))
  refine ⟨a₀, hUS haU, T, hTU.trans hUS, haT, ?_, ?_⟩
  · intro a ha
    exact ⟨(hKsame a (hTU ha)).trans (hKsame a₀ haU).symm, hnsame a ha⟩
  · calc
      Real.exp (-((p + 2) ^ 5 + p)) * S.card =
          Real.exp (-p) * (Real.exp (-((p + 2) ^ 5)) * S.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-p) * U.card := mul_le_mul_of_nonneg_left hUlarge (Real.exp_pos _).le
      _ ≤ T.card := hTlarge

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

theorem exists_common_integral_models (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)] {d : ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s d) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h, (D h).GeometryComplexityLE p) →
      ∃ (B : G → ℕ) (Λ : ∀ h, Subgroup (D h).filtration.Group)
        (hB : ∀ h, 0 < B h)
        (hin : ∀ h, scaledIntegerGrid (B h) ⊆ bchSubgroupCoordinates (D h).basis (Λ h))
        (hout : ∀ h, bchSubgroupCoordinates (D h).basis (Λ h) ⊆ denominatorGrid (B h)),
        (∀ h, (B h : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ Λ h ≤ (D h).lattice ∧
          bchSubgroupCoordinates (D h).basis (Λ h) = scaledIntegerGrid (B h) ∧
          ((D h).withLattice (Λ h) (B h) (hB h) (hin h) (hout h)).GeometryComplexityLE ((p + C) ^ C)) ∧
        ∃ h₀ ∈ H, ∃ H' : Finset G, H' ⊆ H ∧ h₀ ∈ H' ∧
          (∀ h ∈ H', B h = B h₀ ∧ (D h).rationalModelCoordinates = (D h₀).rationalModelCoordinates) ∧
          Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) := by
  classical
  obtain ⟨c, _, hcover⟩ := exists_native_integral_model_cover s
  obtain ⟨k, _, hmodel⟩ := exists_common_rational_model_power s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C c) ^ c + (X + Polynomial.C k) ^ k + X)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ d D H hH p hp hD
  let q := (p + c) ^ c
  let r := (p + k) ^ k
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hbud : q + r + p ≤ (p + C) ^ C := by
    simpa [q, r, X, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hqrC : q + r ≤ (p + C) ^ C := by linarith
  choose B Λ hB hin hout hBb hΛ hcoords hgeom using fun h => hcover (D h) hp (hD h)
  obtain ⟨h₁, _, H₁, hsub₁, hh₁, hcodes, hlarge₁⟩ :=
    hmodel D H hH hp (fun h _ => hD h)
  obtain ⟨h₀, hh₀, H', hsub₂, hh₀', hmoduli, hlarge₂⟩ :=
    exists_common_positive_nat H₁ ⟨h₁, hh₁⟩ B (p := q)
      (fun h _ => ⟨hB h, hBb h⟩)
  refine ⟨B, Λ, hB, hin, hout, ?_, h₀, hsub₁ hh₀, H', hsub₂.trans hsub₁, hh₀', ?_, ?_⟩
  · intro h
    exact ⟨(hBb h).trans (Real.exp_le_exp.mpr hqC), hΛ h, hcoords h,
      (hgeom h).mono _ hqC⟩
  · intro h hh
    exact ⟨hmoduli h hh, (hcodes h (hsub₂ hh)).trans (hcodes h₀ hh₀).symm⟩
  · calc
      Real.exp (-((p + C) ^ C)) * H.card ≤ Real.exp (-(q + r)) * H.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqrC)) (Nat.cast_nonneg _)
      _ = Real.exp (-q) * (Real.exp (-r) * H.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-q) * H₁.card := mul_le_mul_of_nonneg_left hlarge₁ (Real.exp_pos _).le
      _ ≤ H'.card := hlarge₂

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTagConstraintSpaces
namespace OAI

section

namespace Erdos3.VectorPolynomial

namespace RationalTagConstraint

variable {m : ℕ} {J : Fin m → Type*}

end RationalTagConstraint

namespace RationalTaggedConstraintCertificate

variable {m : ℕ} {J : Fin m → Type*} {X : Type*}
  {K₀ K₁ K₂ : Set ((X ⊕ (Σ j, J j)) → ℝ)} {B B' : ℝ} {C C₁ C₂ : ℕ}

end RationalTaggedConstraintCertificate

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.RationalTagConstraint

variable {m : ℕ} {J : Fin m → Type*} {X : Type*}

end Erdos3.VectorPolynomial.RationalTagConstraint

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.RationalTagConstraint

open Module

variable {m : ℕ} {J : Fin m → Type*}

theorem exists_function_spanning_logHeight
    {B η : Type*} [Fintype B] (U : Submodule ℚ (B → ℚ)) (v : η → B → ℚ)
    (hspan : Submodule.span ℚ (Set.range v) = U) {p : ℝ} (hp : 0 ≤ p)
    (hv : ∀ a i, rationalLogHeight (v a i) ≤ p) :
    ∃ w : Fin (Fintype.card B) → B → ℚ,
      Submodule.span ℚ (Set.range w) = U ∧ ∀ a i, rationalLogHeight (w a i) ≤ p := by
  let H := ⌊Real.exp p⌋₊
  have hH : 1 ≤ H := (Nat.le_floor_iff (Real.exp_nonneg p)).mpr (by
    simpa using Real.exp_le_exp.mpr hp)
  have hentry (a : η) (i : B) : RationalHeightLE (v a i) H := by
    obtain ⟨hn, hd⟩ := (rationalLogHeight_le_iff (v a i) p).mp (hv a i)
    exact ⟨(Nat.le_floor_iff (Real.exp_nonneg p)).mpr hn,
      (Nat.le_floor_iff (Real.exp_nonneg p)).mpr hd⟩
  obtain ⟨w, hw, hwH⟩ := exists_bounded_submodule_ambient_spanning
    (Pi.basisFun ℚ B) U v hspan hH hentry
  exact ⟨w, hw, fun a i => rationalLogHeight_le_of_height (hwH a i)
    (Nat.floor_le (Real.exp_nonneg p))⟩

end Erdos3.VectorPolynomial.RationalTagConstraint

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagConstraintBasis
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {η B κ : Type*} [Fintype η] [Fintype B]

theorem realRationalCoordinateSpan_iInf (U : η → Submodule ℚ (B → ℚ)) :
    realRationalCoordinateSpan (⨅ a, U a) = ⨅ a, realRationalCoordinateSpan (U a) := by
  unfold realRationalCoordinateSpan
  rw [real_baseChange_iInf]
  apply Submodule.map_iInf_of_ker_le realRationalCoordinateEquiv.surjective
  rw [LinearMap.ker_eq_bot.mpr realRationalCoordinateEquiv.injective]
  exact bot_le

theorem realRationalCoordinateSpan_top :
    realRationalCoordinateSpan (⊤ : Submodule ℚ (B → ℚ)) = ⊤ := by
  unfold realRationalCoordinateSpan
  rw [Submodule.baseChange_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr realRationalCoordinateEquiv.surjective

theorem realRationalCoordinateSpan_iInf_basis (U : η → Submodule ℚ (B → ℚ))
    (b : Basis κ ℚ ↥(⨅ a, U a)) :
    Submodule.span ℝ (Set.range (fun i j => ((b i : B → ℚ) j : ℝ))) =
      ⨅ a, realRationalCoordinateSpan (U a) := by
  have hb : Submodule.span ℚ (Set.range (fun i => (b i : B → ℚ))) = ⨅ a, U a := by
    simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def, Submodule.subtype_apply,
      Submodule.map_top, Submodule.range_subtype] using
      congrArg (Submodule.map (⨅ a, U a).subtype) b.span_eq
  exact (realRationalCoordinateSpan_span (fun i => (b i : B → ℚ))).symm.trans
    ((congrArg realRationalCoordinateSpan hb).trans (realRationalCoordinateSpan_iInf U))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledRealFastCoefficientAction
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem firstCoefficientIndex_grade_eq_of_monomial_eq {σ ι : Type*}
    (w : σ → ℕ) (ω : ι → ℕ) (i j : FirstCoefficientIndex w ω)
    (h : i.val.1 = j.val.1) : ω i.val.2 = ω j.val.2 :=
  i.property.symm.trans ((congrArg (fun α => Finsupp.weight w α + 1) h).trans j.property)

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
  [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
  [Fintype κ] [DecidableEq κ] (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem realFastCoefficientAdjoint_unitriangular
    (rows : κ → FirstCoefficientIndex w ω)
    (b : Basis κ ℝ (F.RealFirstCoefficientModule w ⧸
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)))
    (D : Matrix κ (FirstCoefficientIndex w ω) ℚ)
    (S : Matrix (FirstCoefficientIndex w ω) κ ℚ)
    (hD : LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w) b
      (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ =
      D.map (Rat.castHom ℝ))
    (hDS : D * S = 1)
    (hDb : ∀ a i, (rows a).val.1 ≠ i.val.1 → D a i = 0)
    (hSb : ∀ i a, i.val.1 ≠ (rows a).val.1 → S i a = 0)
    (g : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (a c : κ) (hac : ω (rows a).val.2 ≤ ω (rows c).val.2) :
    LinearMap.toMatrix b b
        (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
      (1 : Matrix κ κ ℝ) a c := by
  rw [F.realFastCoefficientAdjoint_matrix e ω hF w hw U b D S hD hDS g hg]
  apply block_quotient_unitriangular (fun i : FirstCoefficientIndex w ω => ω i.val.2)
    (fun a => ω (rows a).val.2) _ _ _ ?_ ?_ (real_matrix_right_inverse D S hDS) ?_ a c hac
  · intro a i hai
    change (D a i : ℝ) = 0
    have h := hDb a i (fun he => hai (firstCoefficientIndex_grade_eq_of_monomial_eq w ω _ _ he))
    rw [h, Rat.cast_zero]
  · intro i a hia
    change (S i a : ℝ) = 0
    have h := hSb i a (fun he => hia (firstCoefficientIndex_grade_eq_of_monomial_eq w ω _ _ he))
    rw [h, Rat.cast_zero]
  · intro i j hij
    rw [F.realFirstCoefficientAdjoint_matrix_entry e ω hF w g j i hij]
    simp only [Matrix.one_apply, eq_comm]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_real_fast_coefficient_unitriangular_basis
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hd : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ p)
    (hdm : ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card (FirstCoefficientIndex w ω) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
        F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)),
      ∃ D : Matrix (Fin d) (FirstCoefficientIndex w ω) ℚ,
      ∃ S : Matrix (FirstCoefficientIndex w ω) (Fin d) ℚ,
        LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w) b
          (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ = D.map (Rat.castHom ℝ) ∧
        D * S = 1 ∧
        (∀ i j, (rows i).val.1 ≠ j.val.1 → D i j = 0) ∧
        (∀ i j, i.val.1 ≠ (rows j).val.1 → S i j = 0) ∧
        (∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 420) ∧
          ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 420)) ∧
        (∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 2954) ∧
          ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 2954)) ∧
        (∀ y : Fin d → ℝ, b.equivFun.symm y =
          (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
            ((F.realFirstCoefficientBasis e ω hF w).equivFun.symm
              (S.map (Rat.castHom ℝ) *ᵥ y))) ∧
        ∀ (g : F.RealAdaptedPolynomialGroup w)
          (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
            realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
          (a c : Fin d), ω (rows a).val.2 ≤ ω (rows c).val.2 →
            LinearMap.toMatrix b b (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
              (1 : Matrix (Fin d) (Fin d) ℝ) a c := by
  have h := F.exists_real_fast_coefficient_quotient_basis e ω hF w hw U.toSubmodule hU
    v hspan hH hv hp hn hm hq hd hdm hHp
  rw [← F.realFirstCoefficientFastSubmodule_relative w hw U] at h
  obtain ⟨d, hdim, rows, hinj, b, D, S, hD, hDS, hDb, hSb, hDh, hSh, hrep⟩ := h
  refine ⟨d, hdim, rows, hinj, b, D, S, hD, hDS, hDb, hSb, hDh, hSh, hrep, ?_⟩
  intro g hg a c hac
  exact F.realFastCoefficientAdjoint_unitriangular e ω hF w hw U rows b D S hD hDS
    hDb hSb g hg a c hac

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FastCoefficientDerivativeCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem exists_controlled_real_fast_coefficient_coordinates
    {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hd : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ p)
    (hdm : ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card (FirstCoefficientIndex w ω) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
        F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)),
      ∃ R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w,
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 2958) ∧ l ∣ m ∧
        (∀ x, F.FirstCoefficientGrid e ω hF w l x →
          b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) ∈ realDenominatorGrid m) ∧
        (∀ y : Fin d → ℝ, y ∈ realDenominatorGrid l →
          F.FirstCoefficientGrid e ω hF w m (R y)) ∧
        (∀ y : Fin d → ℝ, (F.realFirstCoefficientFastSubmodule w hw
          (F.reducedSquareFastRelativeSubmodule w U)).mkQ (R y) = b.equivFun.symm y) ∧
        (∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
          (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
            |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
              (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) i| ≤
                Real.exp ((p + 2) ^ 2958) * M / monomialScale T (rows i).val.1) ∧
          (∀ y : Fin d → ℝ, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
            F.FirstCoefficientSlowBound e ω hF w T (Real.exp ((p + 2) ^ 2958) * M) (R y))) ∧
        (∀ i j, (rows j).val.1 ≠ i.val.1 →
          b.repr ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ
              (F.realFirstCoefficientBasis e ω hF w i)) j = 0) ∧
        ∀ (g : F.RealAdaptedPolynomialGroup w)
          (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
            realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
          (a c : Fin d), ω (rows a).val.2 ≤ ω (rows c).val.2 →
            LinearMap.toMatrix b b (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
              (1 : Matrix (Fin d) (Fin d) ℝ) a c := by
  have hb := F.exists_real_fast_coefficient_unitriangular_basis e ω hF w hw U hU
    v hspan hH hv hp hn hm hq hd hdm hHp
  obtain ⟨d, hdim, rows, hinj, b, D, S, hD, hDS, hDb, hSb, hDh, hSh, _, haction⟩ := hb
  have hDh' : ∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 2954) ∧
      ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 2954) := by
    have hpow : Real.exp ((p + 2) ^ 420) ≤ Real.exp ((p + 2) ^ 2954) :=
      Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith) (by decide))
    exact fun i j => ⟨(hDh i j).1.trans hpow, (hDh i j).2.trans hpow⟩
  have hd' : (Fintype.card (Fin d) : ℝ) ≤ p := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr hdim).trans hd
  have hc := controlled_weighted_quotient_coordinates (F.realFirstCoefficientBasis e ω hF w) b
    (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
    (fun i => i.val.1) (fun i => (rows i).val.1) D S hD hDS hDb hSb hp hd hd'
    2954 (by decide) hDh' hSh l hl hlp
  obtain ⟨m, hmpos, hmbound, hlm, hgrid, hRgrid, hR, hweighted⟩ := hc
  refine ⟨d, hdim, rows, hinj, b, rationalCoordinateSection (F.realFirstCoefficientBasis e ω hF w) S,
    m, hmpos, hmbound, hlm, hgrid, hRgrid, hR, ?_, ?_, haction⟩
  · intro T hT M hM
    exact hweighted (monomialScale T) (monomialScale_pos T hT) M hM
  · intro i j hij
    have h := congrArg (fun A => A j i) hD
    simpa only [LinearMap.toMatrix_apply, Matrix.map_apply, hDb j i hij, map_zero] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

def FastCoefficientCoordinateSpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (_hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (_hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) {H : ℕ} (_hH : 1 ≤ H)
    (_hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p),
    ∃ d : ℕ, d ≤ Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
        F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)),
      ∃ R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w,
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ x, F.FirstCoefficientGrid e ω hF w l x →
          b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) ∈ realDenominatorGrid m) ∧
        (∀ y : Fin d → ℝ, y ∈ realDenominatorGrid l →
          F.FirstCoefficientGrid e ω hF w m (R y)) ∧
        (∀ y : Fin d → ℝ, (F.realFirstCoefficientFastSubmodule w hw
          (F.reducedSquareFastRelativeSubmodule w U)).mkQ (R y) = b.equivFun.symm y) ∧
        (∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
          (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
            |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
              (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) i| ≤
                Real.exp ((p + C) ^ C) * M / monomialScale T (rows i).val.1) ∧
          (∀ y : Fin d → ℝ, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
            F.FirstCoefficientSlowBound e ω hF w T (Real.exp ((p + C) ^ C) * M) (R y))) ∧
        (∀ i j, (rows j).val.1 ≠ i.val.1 →
          b.repr ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ
              (F.realFirstCoefficientBasis e ω hF w i)) j = 0) ∧
        ∀ (g : F.RealAdaptedPolynomialGroup w)
          (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
            realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
          (a c : Fin d), ω (rows a).val.2 ≤ ω (rows c).val.2 →
            LinearMap.toMatrix b b (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
              (1 : Matrix (Fin d) (Fin d) ℝ) a c

theorem exists_fast_coefficient_coordinate_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ FastCoefficientCoordinateSpec s C := by
  let Q : Polynomial ℕ :=
    3 * (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) * (Polynomial.X + 1) +
    2 * Polynomial.X + 2 +
    (Polynomial.X + Polynomial.C (s + 3)) ^ (s + 3) * (Polynomial.X + 1) + Polynomial.X + 2
  let B : Polynomial ℕ := (Q + 2) ^ 2958
  have hexists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hexists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U hU v hspan H hH hv p hp hι hσ hκ hHp l hl hlp
  classical
  let : Finite (ReducedSquareSymbolIndex s w ω) := F.reducedSquareSymbolIndex_finite e ω hF w hw
  let : Fintype (ReducedSquareSymbolIndex s w ω) := Fintype.ofFinite _
  let : Finite (QuotientTopSymbolIndex s w ω) := F.quotientTopSymbolIndex_finite e ω hF w hw
  let : Fintype (QuotientTopSymbolIndex s w ω) := Fintype.ofFinite _
  let : Fintype (FirstCoefficientIndex w ω) :=
    firstCoefficientIndexFintype w ω (s + 1) hw (F.adaptedBasis_weight_le_step e ω hF)
  let q := fastCoefficientMatrixParameter s p
  have hq : 0 ≤ q := fastCoefficientMatrixParameter_nonneg s hp
  have hpq : p ≤ q := le_fastCoefficientMatrixParameter s hp
  have hdims := F.fastCoefficient_matrix_dimensions e ω hF w hw hp hι hσ hκ
  have hfinal : (q + 2) ^ 2958 ≤ (p + C) ^ C := by
    simpa [B, Q, q, fastCoefficientMatrixParameter, reducedMatrixParameter, Polynomial.eval₂_pow]
      using hbound p hp
  have hraw := F.exists_controlled_real_fast_coefficient_coordinates e ω hF w hw U hU
    v hspan hH hv hq hdims.1 (hκ.trans hpq) hdims.2.1 hdims.2.2.1 hdims.2.2.2
    (hHp.trans (Real.exp_le_exp.mpr hpq)) l hl (hlp.trans (Real.exp_le_exp.mpr hpq))
  obtain ⟨d, hdim, rows, hinj, b, R, m, hm, hmp, hlm, hgrid, hRgrid, hR, hweighted, hblock, haction⟩ := hraw
  have hdim' : d ≤ Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1) := by
    exact hdim.trans (firstCoefficientIndex_card_le w ω (s + 1) hw
      (F.adaptedBasis_weight_le_step e ω hF))
  have hbudget : Real.exp ((q + 2) ^ 2958) ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hfinal
  refine ⟨d, hdim', rows, hinj, b, R, m, hm, hmp.trans hbudget, hlm,
    hgrid, hRgrid, hR, ?_, hblock, haction⟩
  intro T hT M hM
  obtain ⟨hproj, hlift⟩ := hweighted T hT M hM
  constructor
  · intro x hx i
    exact (hproj x hx i).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbudget hM) (monomialScale_pos T hT _).le)
  · intro y hy i
    exact (hlift y hy i).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbudget hM) (monomialScale_pos T hT _).le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

variable {σ κ L : Type*} [Fintype σ] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
  (b : Basis κ ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1) ⧸
    F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)))

noncomputable def fastCoefficientDirectionCoordinates
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) : (σ → ℝ) →ₗ[ℝ] (κ → ℝ) :=
  b.equivFun.toLinearMap.comp
    ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ.comp
        (F.realFirstCoefficientDirectionMap B.coord))

omit [Fintype σ] in
theorem fastCoefficientAdjoint_coordinates [DecidableEq κ]
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (x : F.RealFirstCoefficientModule (fun _ : σ => 1)) :
    b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
        (F.realFirstCoefficientAdjoint (fun _ => 1) B x)) =
      LinearMap.toMatrix b b (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap *ᵥ
        b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) := by
  have h := LinearMap.toMatrix_mulVec_repr b b
    (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap
    ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x)
  exact (congrArg b.equivFun (F.realFastCoefficientAdjoint_mk (fun _ => 1) (by simp) U B hB x)).symm.trans
    h.symm

theorem fastCoefficientDerivative_coordinates [DecidableEq κ]
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (h : σ → ℝ) (S R : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (heq : F.realFirstCoefficientDirectionMap B.coord h -
      (S + F.realFirstCoefficientAdjoint (fun _ => 1) B R) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)) :
    F.fastCoefficientDirectionCoordinates U b B h =
      b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ S) +
      LinearMap.toMatrix b b (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap *ᵥ
        b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ R) := by
  have hq := (Submodule.Quotient.eq
    (F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))).mpr heq
  let q := (F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
  have hadd := (b.equivFun.toLinearMap.comp q).map_add S (F.realFirstCoefficientAdjoint (fun _ => 1) B R)
  have hadj := F.fastCoefficientAdjoint_coordinates U b B hB R
  exact (congrArg b.equivFun hq).trans (hadd.trans (congrArg₂ (· + ·) rfl hadj))

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFastCoefficientSpec
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

def UniformFastCoefficientCoordinateSpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (_hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun i => i.val.1) U.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (_hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) {H : ℕ} (_hH : 1 ≤ H)
    (_hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p),
    ∃ d : ℕ, d ≤ Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
        F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)),
      ∃ R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w,
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ l x, F.FirstCoefficientGrid e ω hF w l x →
          b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) ∈ realDenominatorGrid (m * l)) ∧
        (∀ l (y : Fin d → ℝ), y ∈ realDenominatorGrid l →
          F.FirstCoefficientGrid e ω hF w (m * l) (R y)) ∧
        (∀ y : Fin d → ℝ, (F.realFirstCoefficientFastSubmodule w hw
          (F.reducedSquareFastRelativeSubmodule w U)).mkQ (R y) = b.equivFun.symm y) ∧
        (∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
          (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
            |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw
              (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) i| ≤
                Real.exp ((p + C) ^ C) * M / monomialScale T (rows i).val.1) ∧
          (∀ y : Fin d → ℝ, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
            F.FirstCoefficientSlowBound e ω hF w T (Real.exp ((p + C) ^ C) * M) (R y))) ∧
        (∀ i j, (rows j).val.1 ≠ i.val.1 →
          b.repr ((F.realFirstCoefficientFastSubmodule w hw
            (F.reducedSquareFastRelativeSubmodule w U)).mkQ
              (F.realFirstCoefficientBasis e ω hF w i)) j = 0) ∧
        ∀ (g : F.RealAdaptedPolynomialGroup w)
          (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
            realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
          (a c : Fin d), ω (rows a).val.2 ≤ ω (rows c).val.2 →
            LinearMap.toMatrix b b (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
              (1 : Matrix (Fin d) (Fin d) ℝ) a c

theorem exists_uniform_fast_coefficient_coordinate_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ UniformFastCoefficientCoordinateSpec s C := by
  obtain ⟨C, hC, hspec⟩ := exists_fast_coefficient_coordinate_bound s
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U hU v hspan H hH hv p hp hι hσ hκ hHp
  have hOne : ((1 : ℕ) : ℝ) ≤ Real.exp p := by simpa only [Nat.cast_one] using Real.one_le_exp hp
  have hraw := hspec F e ω hF w hw U hU v hspan hH hv hp hι hσ hκ hHp 1 (by decide) hOne
  obtain ⟨d, hdim, rows, hinj, b, R, m, hm, hmp, _, hproj, hlift, hright, hweighted, hblock, haction⟩ := hraw
  classical
  let : Fintype (FirstCoefficientIndex w ω) :=
    firstCoefficientIndexFintype w ω (s + 1) hw (F.adaptedBasis_weight_le_step e ω hF)
  refine ⟨d, hdim, rows, hinj, b, R, m, hm, hmp, ?_, ?_, hright, hweighted, hblock, haction⟩
  · intro l x hx
    exact linearMap_grid_of_integer (F.realFirstCoefficientBasis e ω hF w).equivFun.toLinearMap
      (b.equivFun.toLinearMap.comp (F.realFirstCoefficientFastSubmodule w hw
        (F.reducedSquareFastRelativeSubmodule w U)).mkQ) m hproj l x hx
  · intro l y hy
    exact linearMap_grid_of_integer (LinearMap.id : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
      ((F.realFirstCoefficientBasis e ω hF w).equivFun.toLinearMap.comp R) m hlift l y hy

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def spatialRankExponent {K : Type*} : Option K → K →₀ ℕ
  | none => 0
  | some k => Finsupp.single k 1

noncomputable def spatialRankPolynomial {K R : Type*} [Fintype K] [CommRing R]
    (c : Option K → R) : MvPolynomial K R :=
  ∑ e, monomial (spatialRankExponent e) (c e)

theorem spatialRankPolynomial_degree {K R : Type*} [Fintype K] [CommRing R]
    (c : Option K → R) : (spatialRankPolynomial c).totalDegree ≤ 1 := by
  unfold spatialRankPolynomial
  apply totalDegree_finsetSum_le
  intro e _
  apply (totalDegree_monomial_le _ _).trans
  cases e <;> simp [spatialRankExponent]

theorem spatialRankPolynomial_eq {K R : Type*} [Fintype K] [CommRing R]
    (c : Option K → R) :
    spatialRankPolynomial c = C (c none) + ∑ k, C (c (some k)) * X k := by
  rw [spatialRankPolynomial, Fintype.sum_option]
  simp only [spatialRankExponent, monomial_zero', C_mul_X_eq_monomial]

theorem spatialRankPolynomial_top {K R : Type*} [Fintype K] [CommRing R]
    (base : R) (c : Option K → R) :
    homogeneousComponent 1 (C base + spatialRankPolynomial c) =
      ∑ k, C (c (some k)) * X k := by
  rw [spatialRankPolynomial_eq, map_add, map_add, map_sum]
  have hc (r : R) : homogeneousComponent 1 (C r : MvPolynomial K R) = 0 :=
    homogeneousComponent_eq_zero 1 (C r) (by simp)
  simp only [hc, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [C_mul_X_eq_monomial]
  exact homogeneousComponent_eq_self (isHomogeneous_monomial _ (by simp))

def spatialKernelRankSlot {G P A : Type*} (e : A ↪ G) (a : A) : Option (G ⊕ P) :=
  some (.inl (e a))

theorem spatialKernelRankSlot_injective {G P A : Type*} (e : A ↪ G) :
    Function.Injective (spatialKernelRankSlot (P := P) e) := by
  intro a b hab
  exact e.injective (Sum.inl.inj (Option.some.inj hab))

theorem spatial_kernel_selected_sum {G P A R : Type*}
    [Fintype A] [CommRing R] (e : A ↪ G) (c : A → R) :
    (∑ a, monomial (spatialRankExponent (spatialKernelRankSlot (P := P) e a)) (c a) :
      MvPolynomial (G ⊕ P) R) = ∑ a, c a • X (.inl (e a)) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_eq_C_mul, C_mul_X_eq_monomial]
  rfl

theorem spatial_kernel_selected_raw {G P A R : Type*}
    [Fintype G] [Fintype P] [Fintype A] [CommRing R]
    (e : A ↪ G) (fixed : Option (G ⊕ P) → R) (c : A → R) :
    spatialRankPolynomial (Function.extend (spatialKernelRankSlot e) c fixed) =
      (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range (spatialKernelRankSlot (P := P) e)),
        monomial (spatialRankExponent d) (fixed d)) +
      ∑ a, monomial (spatialRankExponent (spatialKernelRankSlot (P := P) e a)) (c a) := by
  unfold spatialRankPolynomial
  convert modularMonomialArrayPolynomial_selected (E := Option (G ⊕ P))
    (K := G ⊕ P) (R := R) (A := A) spatialRankExponent
    (spatialKernelRankSlot e) (spatialKernelRankSlot_injective (P := P) e) fixed c using 1
  congr 1
  apply Finset.sum_congr
  · congr 1
  · intro d _
    rfl

theorem spatialRankPolynomial_kernel_selected {G P A R : Type*}
    [Fintype G] [Fintype P] [Fintype A] [CommRing R]
    (e : A ↪ G) (fixed : Option (G ⊕ P) → R) (c : A → R) :
    spatialRankPolynomial (Function.extend (spatialKernelRankSlot e) c fixed) =
      (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range (spatialKernelRankSlot (P := P) e)),
        monomial (spatialRankExponent d) (fixed d)) +
      ∑ a, c a • (X (.inl (e a)) : MvPolynomial (G ⊕ P) R) := by
  rw [spatial_kernel_selected_raw e fixed c, spatial_kernel_selected_sum e c]

theorem spatialRankPolynomial_kernel_selected_top {G P A R : Type*}
    [Fintype G] [Fintype P] [Fintype A] [CommRing R]
    (e : A ↪ G) (fixed : Option (G ⊕ P) → R) (c : A → R) :
    homogeneousComponent 1 (spatialRankPolynomial (Function.extend (spatialKernelRankSlot e) c fixed)) =
      homogeneousComponent 1
        (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range (spatialKernelRankSlot (P := P) e)),
          monomial (spatialRankExponent d) (fixed d)) +
      ∑ a, c a • (X (.inl (e a)) : MvPolynomial (G ⊕ P) R) := by
  rw [spatialRankPolynomial_kernel_selected e fixed c, map_add]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_eq_C_mul, C_mul_X_eq_monomial]
  exact homogeneousComponent_eq_self (isHomogeneous_monomial _ (by simp))

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G A R : Type*} {B : D → Type*} [CommRing R]

theorem samplerLong_killCompl_common (inactive : D → Prop) (h : D → ℕ) (g : G) :
    killCompl (samplerLongEmbedding (B := B) inactive h).injective
      (X (.inl g) : MvPolynomial (SamplerTupleIndex G B h) R) = X (.inl g) := by
  change killCompl (samplerLongEmbedding (B := B) inactive h).injective
    (X (samplerLongEmbedding inactive h (.inl g))) = _
  rw [← rename_X, killCompl_rename_app]

theorem spatialRankPolynomial_kernel_selected_long
    [Fintype D] [Fintype G] [∀ d, Fintype (B d)] [Fintype A]
    (inactive : D → Prop) (h : D → ℕ) (e : A ↪ G)
    (fixed : Option (SamplerTupleIndex G B h) → R) (c : A → R)
    (v : SamplerTupleIndex G B h → R) :
    homogeneousComponent 1
      (conditionPolynomial (samplerLongEmbedding inactive h)
        (samplerLongEmbedding inactive h).injective v
        (spatialRankPolynomial (Function.extend (spatialKernelRankSlot e) c fixed))) =
      killCompl (samplerLongEmbedding inactive h).injective
        (homogeneousComponent 1
          (∑ d ∈ Finset.univ.filter
            (fun d => d ∉ Set.range (spatialKernelRankSlot (P := PrincipalTupleIndex B h) e)),
            MvPolynomial.monomial (spatialRankExponent d) (fixed d))) +
      ∑ a, c a • (X (.inl (e a)) : MvPolynomial (SamplerLongVariables inactive G B h) R) := by
  rw [homogeneousComponent_conditionPolynomial_top _ _ _ v 1
    (spatialRankPolynomial_degree _), spatialRankPolynomial_kernel_selected_top, map_add]
  apply congrArg₂ (fun P Q => P + Q)
  · apply congrArg (killCompl (samplerLongEmbedding inactive h).injective)
    apply congrArg (homogeneousComponent 1)
    apply Finset.sum_congr
    · exact Finset.filter_congr_decidable _ _ _
    · intro d _
      rfl
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [map_smul, samplerLong_killCompl_common]

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem allocatedSpatialRankPolynomial_kernel_selected_long
    [∀ j, Fintype (I j)] [Fintype G] [∀ d, Fintype (B d)] [Fintype A]
    (inactive : LayerSamplerAxis I n → Prop) (e : A ↪ G)
    (fixed : Option (LayerSamplerVariables G I n B) → R) (c : A → R)
    (v : LayerSamplerVariables G I n B → R) :
    homogeneousComponent 1
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (spatialRankPolynomial (Function.extend (spatialKernelRankSlot e) c fixed))) =
      killCompl (allocatedLongEmbedding inactive).injective
        (homogeneousComponent 1
          (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range
            (spatialKernelRankSlot (P := PrincipalTupleIndex B (layerSamplerDegree I n)) e)),
            MvPolynomial.monomial (spatialRankExponent d) (fixed d))) +
      ∑ a, c a • (X (.inl (e a)) : MvPolynomial (LayerSamplerLongVariables inactive G B) R) := by
  convert spatialRankPolynomial_kernel_selected_long inactive (layerSamplerDegree I n) e fixed c v using 1
  · rfl
  · apply congrArg₂ (fun P Q => P + Q)
    · apply congrArg (killCompl (allocatedLongEmbedding inactive).injective)
      apply congrArg (homogeneousComponent 1)
      apply Finset.sum_congr
      · congr 1
      · intro d _
        rfl
    · rfl

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {K J R : Type*} [Fintype K] [CommRing R]

theorem spatialRankPolynomial_top_congr (f g : Option K → R)
    (hfg : ∀ k, f (some k) = g (some k)) :
    homogeneousComponent 1 (spatialRankPolynomial f) =
      homogeneousComponent 1 (spatialRankPolynomial g) := by
  have hf := spatialRankPolynomial_top (0 : R) f
  have hg := spatialRankPolynomial_top (0 : R) g
  simp only [map_zero, zero_add] at hf hg
  rw [hf, hg]
  apply Finset.sum_congr rfl
  intro k _
  rw [hfg k]

theorem spatialRankPolynomial_conditioned_top_congr (e : J ↪ K)
    (f g : Option K → R) (hfg : ∀ k, f (some k) = g (some k))
    (v w : K → R) :
    homogeneousComponent 1 (conditionPolynomial e e.injective v (spatialRankPolynomial f)) =
      homogeneousComponent 1 (conditionPolynomial e e.injective w (spatialRankPolynomial g)) := by
  rw [homogeneousComponent_conditionPolynomial_top e e.injective _ v 1
      (spatialRankPolynomial_degree f),
    homogeneousComponent_conditionPolynomial_top e e.injective _ w 1
      (spatialRankPolynomial_degree g),
    spatialRankPolynomial_top_congr f g hfg]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open BooleanCubeKernel

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

abbrev SpatialMatrixBlockIndex (X : Type*) := Fin 2 × X × X

def spatialMatrixBlockSlot {G P X : Type*} (e : Fin 2 × X ↪ G) :
    SpatialMatrixBlockIndex X ↪ Option (G ⊕ P) × X where
  toFun t := (some (.inl (e (t.1,t.2.1))),t.2.2)
  inj' := by
    rintro ⟨b,j,x⟩ ⟨c,k,y⟩ h
    have hx : x = y := congrArg Prod.snd h
    have hbj : (b,j) = (c,k) := e.injective
      (Sum.inl.inj (Option.some.inj (congrArg Prod.fst h)))
    have hb : b = c := congrArg Prod.fst hbj
    have hj : j = k := congrArg Prod.snd hbj
    subst c
    subst k
    subst y
    rfl

noncomputable def spatialMatrixNormalizedEntries {G P X : Type*} (e : Fin 2 × X ↪ G)
    (V : Option (G ⊕ P) × X → ℝ) (z : Option (G ⊕ P) × X → ℤ) :
    SpatialMatrixBlockIndex X → ℝ :=
  fun t => (z (spatialMatrixBlockSlot e t) : ℝ) / V (spatialMatrixBlockSlot e t)

noncomputable def spatialMatrixIndexCenter {G P X : Type*} (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) : SpatialMatrixBlockIndex X → ℝ :=
  fun t => -(residue (spatialMatrixBlockSlot e t) : ℝ) / q t.2.2

noncomputable def spatialMatrixIndexWidth {G P X : Type*} (e : Fin 2 × X ↪ G)
    (q : X → ℕ) (V : Option (G ⊕ P) × X → ℝ) : SpatialMatrixBlockIndex X → ℝ :=
  fun t => V (spatialMatrixBlockSlot e t) / q t.2.2

theorem spatialMatrixIndexWidth_pos {G P X : Type*} (e : Fin 2 × X ↪ G)
    (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z) (t : SpatialMatrixBlockIndex X) :
    0 < spatialMatrixIndexWidth e q V t :=
  div_pos (hV _) (by exact_mod_cast hq t.2.2)

variable {G P X : Type*} [Fintype G] [Fintype P] [Fintype X]

theorem spatialMatrixIndexMass_pos (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V)) :
    0 < shiftedSmoothProductMass (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V) :=
  shiftedSmoothProductMass_restrict_pos (spatialMatrixBlockSlot e)
    (residueProfileCenter residue q) (residueProfileWidth q V)
    (residueProfileWidth_pos q V hq hV) hZ

theorem spatialMatrixNormalizedEntries_residue (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (t : Option (G ⊕ P) × X → ℤ) :
    spatialMatrixNormalizedEntries e V (residueLatticeArray residue q t) =
      rectangularLatticePoint (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)
        (fun i => t (spatialMatrixBlockSlot e i)) := by
  funext i
  exact (congrFun (residueProfile_point residue q hq V hV t) (spatialMatrixBlockSlot e i)).symm

theorem spatialMatrixIndexPMF_marginal (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V)) :
    (residueSmoothIndexPMF residue q hq V hV hZ).map
      (fun t i => t (spatialMatrixBlockSlot e i)) =
      shiftedSmoothProductPMF (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)
        (spatialMatrixIndexWidth_pos e q hq V hV) (spatialMatrixIndexMass_pos e residue q hq V hV hZ) := by
  exact shiftedSmoothProductPMF_selected_marginal (spatialMatrixBlockSlot e)
    (residueProfileCenter residue q) (residueProfileWidth q V)
    (residueProfileWidth_pos q V hq hV) hZ

theorem spatialMatrixNormalizedEntries_residue_law (e : Fin 2 × X ↪ G)
    (residue : Option (G ⊕ P) × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V)) :
    (residueSmoothPMF residue q hq V hV hZ).map (spatialMatrixNormalizedEntries e V) =
      (shiftedSmoothProductPMF (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)
        (spatialMatrixIndexWidth_pos e q hq V hV) (spatialMatrixIndexMass_pos e residue q hq V hV hZ)).map
        (rectangularLatticePoint (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)) := by
  rw [residueSmoothPMF, PMF.map_comp]
  have hf : spatialMatrixNormalizedEntries e V ∘ residueLatticeArray residue q =
      rectangularLatticePoint (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V) ∘
        (fun t i => t (spatialMatrixBlockSlot e i)) := by
    funext t
    exact spatialMatrixNormalizedEntries_residue e residue q hq V hV t
  rw [hf, ← PMF.map_comp, spatialMatrixIndexPMF_marginal]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def spatialMatrixBlockEquiv (n : ℕ) :
    SpatialMatrixBlockIndex (Fin n) ≃ Fin (2 * n * n) :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_assoc 2 n n).symm))

def spatialMatrixBlockEntry (n : ℕ) (b : Fin 2) :
    Fin n × Fin n ↪ Fin (2 * n * n) where
  toFun rc := spatialMatrixBlockEquiv n (b, rc.2, rc.1)
  inj' := by
    intro x y h
    have hs := (spatialMatrixBlockEquiv n).injective h
    have hp := congrArg Prod.snd hs
    exact Prod.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp)

@[simp] theorem spatialMatrixBlockEntry_apply (n : ℕ) (b : Fin 2) (r c : Fin n) :
    spatialMatrixBlockEntry n b (r,c) = spatialMatrixBlockEquiv n (b,c,r) := rfl

@[simp] theorem spatialMatrixBlockEntry_symm (n : ℕ) (b : Fin 2) (r c : Fin n) :
    (spatialMatrixBlockEquiv n).symm (spatialMatrixBlockEntry n b (r,c)) = (b,c,r) :=
  (spatialMatrixBlockEquiv n).symm_apply_apply _

theorem spatialMatrixBlockEntry_reindex_eval {R : Type*}
    (n : ℕ) (z : SpatialMatrixBlockIndex (Fin n) → R) (b : Fin 2) (r c : Fin n) :
    z ((spatialMatrixBlockEquiv n).symm (spatialMatrixBlockEntry n b (r,c))) = z (b,c,r) := by
  rw [spatialMatrixBlockEntry_symm]

theorem shiftedSmoothProductPMF_reindex {D J : Type*} [Fintype D] [Fintype J]
    (e : D ≃ J) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) :
    (shiftedSmoothProductPMF a S hS hZ).map (fun z d => z (e d)) =
      shiftedSmoothProductPMF (fun d => a (e d)) (fun d => S (e d))
        (fun d => hS (e d)) (shiftedSmoothProductMass_restrict_pos e a S hS hZ) :=
  shiftedSmoothProductPMF_selected_marginal e.toEmbedding a S hS hZ

theorem rectangularLatticePoint_reindex {D J : Type*} (e : D → J)
    (a S : J → ℝ) (z : J → ℤ) :
    rectangularLatticePoint (fun d => a (e d)) (fun d => S (e d)) (fun d => z (e d)) =
      fun d => rectangularLatticePoint a S z (e d) := rfl

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem spatialMatrix_decide_eq_classical (p : Prop) [d : Decidable p] :
    @decide p d = @decide p (Classical.propDecidable p) := by
  cases Subsingleton.elim d (Classical.propDecidable p)
  rfl

noncomputable def spatialMatrixBlockThreshold (n : ℕ) (η : ℝ) : ℝ :=
  shiftedSmoothSublevelThreshold (2 * n * n) n 2 η

theorem spatialMatrixBlockThreshold_pos {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    0 < spatialMatrixBlockThreshold n η :=
  shiftedSmoothSublevelThreshold_pos (by positivity) n 2 hη

def spatialMatrixBlockBad {G P : Type*} {n : ℕ} (e : Fin 2 × Fin n ↪ G)
    (V : Option (G ⊕ P) × Fin n → ℝ) (κ : ℝ)
    (z : Option (G ⊕ P) × Fin n → ℤ) : Prop :=
  ∃ b : Fin 2, |Matrix.det (fun i j : Fin n => spatialMatrixNormalizedEntries e V z (b,j,i))| ≤ κ

theorem spatialMatrixBlock_flat_bad_probability {n : ℕ} (hn : 0 < n)
    (a S : SpatialMatrixBlockIndex (Fin n) → ℝ) (hS : ∀ i, 0 < S i)
    (hZ : 0 < shiftedSmoothProductMass a S)
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : embeddedMatrixDeterminantLip n (2*n*n) * δ ≤ spatialMatrixBlockThreshold n η) :
    ((shiftedSmoothProductPMF a S hS hZ).map (fun k => decide
      (∃ b : Fin 2, |Matrix.det (fun i j : Fin n => rectangularLatticePoint a S k (b,j,i))| ≤
        spatialMatrixBlockThreshold n η)) true).toReal ≤ η / 2 := by
  unfold spatialMatrixBlockThreshold at hsmall ⊢
  simp only [spatialMatrix_decide_eq_classical]
  have h := smoothMatrixBlock_bad_probability hn (show 0 < 2*n*n by positivity)
    (spatialMatrixBlockEntry n)
    (fun k => a ((spatialMatrixBlockEquiv n).symm k))
    (fun k => S ((spatialMatrixBlockEquiv n).symm k))
    (fun k => hS ((spatialMatrixBlockEquiv n).symm k))
    (shiftedSmoothProductMass_restrict_pos (spatialMatrixBlockEquiv n).symm a S hS hZ)
    (fun k => hlarge ((spatialMatrixBlockEquiv n).symm k)) hδ hδ1 hη
    (fun k => hmesh ((spatialMatrixBlockEquiv n).symm k))
    (by simpa only [Fintype.card_fin, spatialMatrixBlockThreshold] using hsmall)
  rw [← shiftedSmoothProductPMF_reindex (spatialMatrixBlockEquiv n).symm a S hS hZ,
    PMF.map_comp] at h
  simpa only [Function.comp_def, rectangularLatticePoint_reindex,
    spatialMatrixBlockEntry_reindex_eval, Fintype.card_fin, spatialMatrixBlockThreshold,
    spatialMatrix_decide_eq_classical] using h

variable {G P : Type*} [Fintype G] [Fintype P] {n : ℕ}

theorem spatialMatrixBlock_residue_bad_probability (hn : 0 < n) (e : Fin 2 × Fin n ↪ G)
    (residue : Option (G ⊕ P) × Fin n → ℤ) (q : Fin n → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × Fin n → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V))
    (hlarge : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ spatialMatrixIndexWidth e q V i)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (hmesh : ∀ i, 1 / spatialMatrixIndexWidth e q V i ≤ δ)
    (hsmall : embeddedMatrixDeterminantLip n (2*n*n) * δ ≤ spatialMatrixBlockThreshold n η) :
    ((residueSmoothPMF residue q hq V hV hZ).map
      (fun z => decide (spatialMatrixBlockBad e V (spatialMatrixBlockThreshold n η) z)) true).toReal ≤ η / 2 := by
  let test : (SpatialMatrixBlockIndex (Fin n) → ℝ) → Bool := fun z => decide
    (∃ b : Fin 2, |Matrix.det (fun i j : Fin n => z (b,j,i))| ≤ spatialMatrixBlockThreshold n η)
  have heq := congrArg (fun law : PMF (SpatialMatrixBlockIndex (Fin n) → ℝ) =>
      (law.map test true).toReal)
    (spatialMatrixNormalizedEntries_residue_law e residue q hq V hV hZ)
  have hbound := spatialMatrixBlock_flat_bad_probability hn
    (spatialMatrixIndexCenter e residue q) (spatialMatrixIndexWidth e q V)
    (spatialMatrixIndexWidth_pos e q hq V hV) (spatialMatrixIndexMass_pos e residue q hq V hV hZ)
    hlarge hδ hδ1 hη hmesh hsmall
  simp only [PMF.map_comp, Function.comp_def, test, spatialMatrixBlockBad,
    spatialMatrix_decide_eq_classical] at heq hbound ⊢
  exact heq.trans_le hbound

theorem spatialMatrixBlock_cellMass_pos
    (q : Fin n → ℕ) (hq : ∀ x, 0 < q x)
    (V : Option (G ⊕ P) × Fin n → ℝ) (hV : ∀ z, 0 < V z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (residue : Option (G ⊕ P) × Fin n → ℤ) :
    0 < shiftedSmoothProductMass (residueProfileCenter residue q) (residueProfileWidth q V) := by
  rw [shiftedSmoothProductMass_eq_prod _ _ (residueProfileWidth_pos q V hq hV)]
  exact Finset.prod_pos (fun z _ => shiftedSmoothSampleSum_pos _ (hscale z))

theorem spatialMatrixBlock_bad_probability (hn : 0 < n) (e : Fin 2 × Fin n ↪ G)
    (q : Fin n → ℕ) (hq : ∀ x, 0 < q x)
    (T : Finset (ColumnResiduePattern (Option (G ⊕ P)) (Fin n) q))
    (V : Option (G ⊕ P) × Fin n → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (hmesh : ∀ i, 1 / spatialMatrixIndexWidth e q V i ≤ δ)
    (hsmall : embeddedMatrixDeterminantLip n (2*n*n) * δ ≤ spatialMatrixBlockThreshold n η) :
    ((selectedResidueSmoothPMF q T V hV hZ).map
      (fun z => decide (spatialMatrixBlockBad e V (spatialMatrixBlockThreshold n η) z)) true).toReal ≤ η / 2 := by
  let hc (r : T) := spatialMatrixBlock_cellMass_pos q hq V hV hscale
    (boundedColumnResidueRepresentative q r.val)
  apply selectedResidueSmoothPMF_bind_le_of_cells q hq T V hV hZ hc
    (fun z => PMF.pure (decide (spatialMatrixBlockBad e V (spatialMatrixBlockThreshold n η) z))) true (η/2)
  intro r
  exact spatialMatrixBlock_residue_bad_probability hn e _ q hq V hV (hc r)
    (fun i => hscale (spatialMatrixBlockSlot e i)) hδ hδ1 hη hmesh hsmall

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem spatialMatrixBlockThreshold_inverse_le_exp {n : ℕ} (hn : 0 < n)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E) :
    (spatialMatrixBlockThreshold n η)⁻¹ ≤
      Real.exp (smoothMatrixBlockThresholdLogBudget (2 * n * n) n 2 E) :=
  smoothMatrixBlock_threshold_inverse_le_exp (by positivity) hn 2 hη hE hηb

theorem spatialMatrixBlock_bad_probability_of_exp_width
    {G P : Type*} [Fintype G] [Fintype P] {n : ℕ} (hn : 0 < n)
    (e : Fin 2 × Fin n ↪ G)
    (q : Fin n → ℕ) (hq : ∀ x, 0 < q x)
    (T : Finset (ColumnResiduePattern (Option (G ⊕ P)) (Fin n) q))
    (V : Option (G ⊕ P) × Fin n → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E)
    (hwide : ∀ i, Real.exp (smoothMatrixBlockWidthLogBudget (2 * n * n) n 2 E) ≤
      spatialMatrixIndexWidth e q V i) :
    ((selectedResidueSmoothPMF q T V hV hZ).map
      (fun z => decide (spatialMatrixBlockBad e V (spatialMatrixBlockThreshold n η) z)) true).toReal ≤ η / 2 := by
  have hκ := spatialMatrixBlockThreshold_pos hn hη
  have hδ := smoothMatrixBlockMesh_spec n (2 * n * n) hκ
  have hwide' (i) := smoothMatrixBlockMesh_width_spec n (2 * n * n) hκ
    ((smoothMatrixBlock_actual_width_le_exp (by positivity) hn 2 hη hE hηb).trans (hwide i))
  exact spatialMatrixBlock_bad_probability hn e q hq T V hV hZ hscale
    hδ.1.le hδ.2.1 hη (fun i => (hwide' i).2.2) hδ.2.2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedDeterminantCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem unitTestClip_lipschitz : LipschitzWith 1 unitTestClip :=
  (LipschitzWith.id.const_min 1).const_max (-1)

theorem unitTestClip_eq_self {x : ℝ} (hx : |x| ≤ 1) : unitTestClip x = x := by
  rcases abs_le.mp hx with ⟨hl, hu⟩
  simp only [unitTestClip, min_eq_right hu, max_eq_right hl]

theorem unitTestClip_norm_le_one (x : ℝ) : ‖unitTestClip x‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs, abs_le, Set.mem_Icc] using unitTestClip_mem x

noncomputable def clippedSelectedDeterminant {A : Type*} (n : ℕ)
    (coords : Fin n → Fin n → A) (x : A → ℝ) : ℝ :=
  Matrix.det (Matrix.of (fun i j => unitTestClip (x (coords i j))))

theorem real_perm_sign_norm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ‖((Equiv.Perm.sign σ : ℤ) : ℝ)‖ = 1 := by
  rw [Real.norm_eq_abs, ← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one]

theorem clippedSelectedDeterminant_lipschitz {A : Type*} [Fintype A]
    (n : ℕ) (coords : Fin n → Fin n → A) :
    LipschitzWith ((n * n.factorial : ℕ) : ℝ≥0) (clippedSelectedDeterminant n coords) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hprod (σ : Equiv.Perm (Fin n)) :
      ‖(∏ i, unitTestClip (x (coords (σ i) i))) -
        ∏ i, unitTestClip (y (coords (σ i) i))‖ ≤ (n : ℝ) * dist x y := by
    calc
      _ ≤ ∑ i : Fin n, ‖unitTestClip (x (coords (σ i) i)) -
          unitTestClip (y (coords (σ i) i))‖ :=
        VectorPolynomial.norm_finset_prod_sub_prod_le_sum Finset.univ _ _
          (fun i _ => unitTestClip_norm_le_one _) (fun i _ => unitTestClip_norm_le_one _)
      _ ≤ ∑ _i : Fin n, dist x y := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← dist_eq_norm]
        exact (unitTestClip_lipschitz.dist_le_mul _ _).trans (by
          simpa using dist_le_pi_dist x y (coords (σ i) i))
      _ = (n : ℝ) * dist x y := by simp
  rw [dist_eq_norm, clippedSelectedDeterminant, clippedSelectedDeterminant,
    Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin n),
        ‖((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ i, unitTestClip (x (coords (σ i) i))) -
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ i, unitTestClip (y (coords (σ i) i)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), (n : ℝ) * dist x y := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [← mul_sub, norm_mul, real_perm_sign_norm, one_mul]
      exact hprod σ
    _ = ↑((n * n.factorial : ℕ) : ℝ≥0) * dist x y := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, NNReal.coe_mul, NNReal.coe_natCast]
      ring

end Erdos3

end

section

namespace Erdos3
open scoped NNReal Classical

noncomputable def normalizedDeterminantCutoff {A : Type*} (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) (κ : ℝ) (x : A → ℝ) : ℝ :=
  max (scalarBadSublevelRamp κ (clippedSelectedDeterminant n (coords 0) x))
    (scalarBadSublevelRamp κ (clippedSelectedDeterminant n (coords 1) x))

theorem normalizedDeterminantCutoff_range {A : Type*} (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) (κ : ℝ) (x : A → ℝ) :
    normalizedDeterminantCutoff n coords κ x ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨(scalarBadSublevelRamp_range κ _).1.trans (le_max_left _ _),
    max_le (scalarBadSublevelRamp_range κ _).2 (scalarBadSublevelRamp_range κ _).2⟩

theorem normalizedDeterminantCutoff_lipschitz {A : Type*} [Fintype A] (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) {κ : ℝ} (hκ : 0 < κ) :
    LipschitzWith (⟨2 / κ, by positivity⟩ * ((n * n.factorial : ℕ) : ℝ≥0))
      (normalizedDeterminantCutoff n coords κ) := by
  unfold normalizedDeterminantCutoff
  have h (b : Fin 2) := (scalarBadSublevelRamp_lipschitz hκ).comp
    (clippedSelectedDeterminant_lipschitz n (coords b))
  simpa only [max_self, Function.comp_def] using (h 0).max (h 1)

theorem normalizedDeterminantCutoff_eq_one {A : Type*} (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) {κ : ℝ} (hκ : 0 < κ)
    (x : A → ℝ) (hx : ∀ b i j, |x (coords b i j)| ≤ 1)
    (hbad : ∃ b : Fin 2, |Matrix.det (fun i j => x (coords b i j))| ≤ κ / 2) :
    normalizedDeterminantCutoff n coords κ x = 1 := by
  obtain ⟨b, hb⟩ := hbad
  have he : clippedSelectedDeterminant n (coords b) x = Matrix.det (fun i j => x (coords b i j)) := by
    unfold clippedSelectedDeterminant
    congr 1
    funext i j
    exact unitTestClip_eq_self (hx b i j)
  have hb1 : scalarBadSublevelRamp κ (clippedSelectedDeterminant n (coords b) x) = 1 :=
    scalarBadSublevelRamp_eq_one hκ (by rw [he]; exact hb)
  apply le_antisymm (normalizedDeterminantCutoff_range n coords κ x).2
  fin_cases b
  · exact hb1 ▸ le_max_left _ _
  · exact hb1 ▸ le_max_right _ _

theorem normalizedDeterminantCutoff_eq_zero {A : Type*} (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) {κ : ℝ} (hκ : 0 < κ)
    (x : A → ℝ) (hx : ∀ b i j, |x (coords b i j)| ≤ 1)
    (hgood : ∀ b : Fin 2, κ ≤ |Matrix.det (fun i j => x (coords b i j))|) :
    normalizedDeterminantCutoff n coords κ x = 0 := by
  have he (b : Fin 2) : clippedSelectedDeterminant n (coords b) x =
      Matrix.det (fun i j => x (coords b i j)) := by
    unfold clippedSelectedDeterminant
    congr 1
    funext i j
    exact unitTestClip_eq_self (hx b i j)
  have hz (b : Fin 2) : scalarBadSublevelRamp κ (clippedSelectedDeterminant n (coords b) x) = 0 :=
    scalarBadSublevelRamp_eq_zero hκ (by rw [he]; exact hgood b)
  simp only [normalizedDeterminantCutoff, hz, max_self]

theorem normalizedDeterminantCutoff_indicator_bounds {A : Type*} (n : ℕ)
    (coords : Fin 2 → Fin n → Fin n → A) {κ : ℝ} (hκ : 0 < κ)
    (x : A → ℝ) (hx : ∀ b i j, |x (coords b i j)| ≤ 1) :
    (if ∃ b : Fin 2, |Matrix.det (fun i j => x (coords b i j))| ≤ κ / 2 then (1 : ℝ) else 0) ≤
      normalizedDeterminantCutoff n coords κ x ∧
    normalizedDeterminantCutoff n coords κ x ≤
      (if ∃ b : Fin 2, |Matrix.det (fun i j => x (coords b i j))| ≤ κ then (1 : ℝ) else 0) := by
  constructor
  · split_ifs with hbad
    · exact (normalizedDeterminantCutoff_eq_one n coords hκ x hx hbad).ge
    · exact (normalizedDeterminantCutoff_range n coords κ x).1
  · split_ifs with hbad
    · exact (normalizedDeterminantCutoff_range n coords κ x).2
    · exact (normalizedDeterminantCutoff_eq_zero n coords hκ x hx
        (fun b => le_of_lt (lt_of_not_ge (fun h => hbad ⟨b,h⟩)))).le

noncomputable def spatialMatrixBlockCutoff {G P : Type*} {n : ℕ}
    (e : Fin 2 × Fin n ↪ G) (κ : ℝ) (x : Option (G ⊕ P) × Fin n → ℝ) : ℝ :=
  normalizedDeterminantCutoff n (fun b i j => spatialMatrixBlockSlot e (b,j,i)) κ x

theorem spatialMatrixBlockCutoff_range {G P : Type*} {n : ℕ}
    (e : Fin 2 × Fin n ↪ G) (κ : ℝ) (x : Option (G ⊕ P) × Fin n → ℝ) :
    spatialMatrixBlockCutoff e κ x ∈ Set.Icc (0 : ℝ) 1 := by
  exact normalizedDeterminantCutoff_range n
    (fun b i j => spatialMatrixBlockSlot (P := P) e (b,j,i)) κ x

theorem spatialMatrixBlockCutoff_lipschitz {G P : Type*} [Fintype G] [Fintype P] {n : ℕ}
    (e : Fin 2 × Fin n ↪ G) {κ : ℝ} (hκ : 0 < κ) :
    LipschitzWith (⟨2 / κ, by positivity⟩ * ((n * n.factorial : ℕ) : ℝ≥0))
      (spatialMatrixBlockCutoff (P := P) e κ) := by
  unfold spatialMatrixBlockCutoff
  exact normalizedDeterminantCutoff_lipschitz n
    (fun b i j => spatialMatrixBlockSlot (P := P) e (b,j,i)) hκ

theorem spatialMatrixBlockCutoff_indicator_bounds {G P : Type*} {n : ℕ}
    (e : Fin 2 × Fin n ↪ G) (V : Option (G ⊕ P) × Fin n → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (z : Option (G ⊕ P) × Fin n → ℤ)
    (hz : ∀ t, |(z t : ℝ) / V t| ≤ 1) :
    (if spatialMatrixBlockBad e V (κ / 2) z then (1 : ℝ) else 0) ≤
      spatialMatrixBlockCutoff e κ (fun t => (z t : ℝ) / V t) ∧
    spatialMatrixBlockCutoff e κ (fun t => (z t : ℝ) / V t) ≤
      (if spatialMatrixBlockBad e V κ z then (1 : ℝ) else 0) := by
  unfold spatialMatrixBlockBad spatialMatrixBlockCutoff spatialMatrixNormalizedEntries
  have hh := normalizedDeterminantCutoff_indicator_bounds n
    (fun b i j => spatialMatrixBlockSlot (P := P) e (b,j,i)) hκ
    (fun t => (z t : ℝ) / V t) (fun _ _ _ => hz _)
  split_ifs at hh ⊢ <;> exact hh

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixCutoffBudget
namespace OAI

section

namespace Erdos3

theorem nat_mul_factorial_le_exp_square (n : ℕ) :
    ((n * n.factorial : ℕ) : ℝ) ≤ Real.exp (((n : ℝ) + 1) ^ 2) := by
  have hn : (n : ℝ) ≤ Real.exp (n : ℝ) := by
    have h := Real.add_one_le_exp (n : ℝ)
    linarith
  have hf : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast n.factorial_le_pow
  have hp : (n : ℝ) ^ n ≤ Real.exp ((n : ℝ) * n) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hn n
  calc
    _ = (n : ℝ) * n.factorial := by push_cast; rfl
    _ ≤ Real.exp (n : ℝ) * Real.exp ((n : ℝ) * n) :=
      mul_le_mul hn (hf.trans hp) (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ) + (n : ℝ) * n) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

theorem determinantCutoff_lip_le_exp (n : ℕ) {κ K : ℝ}
    (hκ : 0 < κ) (hK : κ⁻¹ ≤ Real.exp K) :
    (2 / κ) * ((n * n.factorial : ℕ) : ℝ) ≤
      Real.exp (K + ((n : ℝ) + 1) ^ 2 + 1) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  calc
    _ = (2 * κ⁻¹) * ((n * n.factorial : ℕ) : ℝ) := by rw [div_eq_mul_inv]
    _ ≤ (Real.exp 1 * Real.exp K) * Real.exp (((n : ℝ) + 1) ^ 2) := by
      gcongr
      exact nat_mul_factorial_le_exp_square n
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem spatialMatrixBlockCutoff_lip_exp_budget {n : ℕ} (hn : 0 < n)
    {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hηb : η⁻¹ ≤ Real.exp E) :
    (2 / spatialMatrixBlockThreshold n η) * ((n * n.factorial : ℕ) : ℝ) ≤
      Real.exp (smoothMatrixBlockThresholdLogBudget (2 * n * n) n 2 E +
        ((n : ℝ) + 1) ^ 2 + 1) :=
  determinantCutoff_lip_le_exp n (spatialMatrixBlockThreshold_pos hn hη)
    (spatialMatrixBlockThreshold_inverse_le_exp hn hη hE hηb)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointExceptionalGainBudget
namespace OAI

section

namespace Erdos3

noncomputable def jointSpatialError (gainLog : ℝ) : ℝ :=
  Real.exp (-gainLog) / 128

theorem jointExceptional_exp_eight : (256 : ℝ) ≤ Real.exp 8 := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h 8
  norm_num [← Real.exp_nat_mul] at hp ⊢
  exact hp

theorem jointSpatialError_pos (gainLog : ℝ) : 0 < jointSpatialError gainLog := by
  unfold jointSpatialError
  positivity

theorem jointSpatialError_inverse_le_exp (gainLog : ℝ) :
    (jointSpatialError gainLog)⁻¹ ≤ Real.exp (gainLog + 8) := by
  have he : 0 < Real.exp gainLog := Real.exp_pos _
  calc
    (jointSpatialError gainLog)⁻¹ = 128 * Real.exp gainLog := by
      simp [jointSpatialError, Real.exp_neg]
    _ ≤ Real.exp 8 * Real.exp gainLog := by
      exact mul_le_mul_of_nonneg_right (by linarith [jointExceptional_exp_eight]) he.le
    _ = Real.exp (gainLog + 8) := by rw [← Real.exp_add]; congr 1; ring

theorem jointExceptionalGainBudget {gainLog gain P : ℝ}
    (hg : 0 ≤ gainLog) (hP : gainLog + 8 ≤ P)
    (hgain : Real.exp (-gainLog) ≤ gain) :
    Real.exp (-(gainLog + 8)) + jointSpatialError gainLog / 2 +
      6 * positiveProjectionAccuracy P ≤ (gain / 4) / 4 := by
  have he : 0 < Real.exp (-gainLog) := Real.exp_pos _
  have hshift : Real.exp (-(gainLog + 8)) ≤ Real.exp (-gainLog) / 256 := by
    rw [neg_add, Real.exp_add, Real.exp_neg (8 : ℝ), ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left he.le (by norm_num) jointExceptional_exp_eight
  have hprecision : positiveProjectionAccuracy P ≤ Real.exp (-gainLog) / 256 := by
    apply le_trans _ hshift
    apply Real.exp_le_exp.mpr
    change -(2 * P + 4) ≤ -(gainLog + 8)
    linarith
  unfold jointSpatialError
  linarith

theorem exists_jointSpatialError_polynomial_budget :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {P₀ gainLog : ℝ} {n : ℕ}, 0 ≤ P₀ →
      0 < n → (n : ℝ) ≤ P₀ → 0 ≤ gainLog → gainLog ≤ P₀ →
      (spatialMatrixBlockThreshold n (jointSpatialError gainLog))⁻¹ ≤
          Real.exp ((P₀ + A)^A) ∧
      (2 / spatialMatrixBlockThreshold n (jointSpatialError gainLog)) *
          ((n * n.factorial : ℕ) : ℝ) ≤ Real.exp ((P₀ + A)^A) ∧
      smoothMatrixBlockWidthLogBudget (2*n*n) n 2 (gainLog+8) ≤ (P₀+A)^A := by
  obtain ⟨A, hA, hbudget⟩ := exists_jointExceptional_polynomial_budget
  refine ⟨A, hA, ?_⟩
  intro P₀ gainLog n hP hn hnP hg hgP
  obtain ⟨hthreshold, hwidth⟩ := hbudget hP hnP hg hgP
  have hη := jointSpatialError_pos gainLog
  have hηb := jointSpatialError_inverse_le_exp gainLog
  have hE : 0 ≤ gainLog + 8 := by linarith
  have hthreshold' : smoothMatrixBlockThresholdLogBudget (2*n*n) n 2
      (gainLog+8) ≤ (P₀+A)^A := by nlinarith [sq_nonneg ((n : ℝ)+1)]
  exact ⟨(spatialMatrixBlockThreshold_inverse_le_exp hn hη hE hηb).trans
      (Real.exp_le_exp.mpr hthreshold'),
    (spatialMatrixBlockCutoff_lip_exp_budget hn hη hE hηb).trans
      (Real.exp_le_exp.mpr hthreshold), hwidth⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LatticeTorusFourierCoefficient
namespace OAI

section

namespace Erdos3

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeBasis_integerCoordinates (b : Module.Basis ι ℤ Λ) (n : ι → ℤ) :
    (b.ofZLatticeBasis ℝ Λ).equivFun.symm (fun i => (n i : ℝ)) = (b.equivFun.symm n : E) := by
  apply (b.ofZLatticeBasis ℝ Λ).equivFun.injective
  ext i
  rw [LinearEquiv.apply_symm_apply]
  change (n i : ℝ) = (b.ofZLatticeBasis ℝ Λ).repr (b.equivFun.symm n : E) i
  rw [Module.Basis.ofZLatticeBasis_repr_apply]
  exact (congrArg (fun z : ℤ => (z : ℝ)) (congrFun (b.equivFun.apply_symm_apply n) i)).symm

theorem latticeGaussian_integer_periodic (b : Module.Basis ι ℤ Λ) (t : ℝ)
    (x : ι → ℝ) (n : ι → ℤ) :
    latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm (fun i => x i + (n i : ℝ))) =
      latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x) := by
  change latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm (x + (fun i => (n i : ℝ)))) = _
  rw [map_add, latticeBasis_integerCoordinates]
  exact latticeGaussianMass_add_lattice Λ t _ _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CenteredFiniteSpatialModularGoodSet
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Classical

theorem centeredFinite_spatial_modular_good_set
    {C Ω G P : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {n : ℕ}
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (noise : Ω → (Option (G ⊕ P) × Fin n → ℤ))
    (V : Option (G ⊕ P) × Fin n → ℝ)
    (e : Fin 2 × Fin n ↪ G) (κ : ℝ)
    (modularBad : Set (C × Ω)) (hmeas : MeasurableSet modularBad)
    {εmod εsp : ℝ}
    (hmodmass : (centeredFiniteProbabilityMeasure μ law).real modularBad ≤ εmod)
    (hspmass : (centeredFiniteProbabilityMeasure μ law).real
      {z | spatialMatrixBlockBad e V (κ / 2) (noise z.2)} ≤ εsp)
    (charge : C × Ω → ℕ) (cutoff : ℕ)
    (hmodular : ∀ c x, 0 < (law c).weight x →
      ((c, x) ∈ modularBad ↔ cutoff < charge (c, x)))
    (recovered : C × Ω → Prop)
    (hae : ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, recovered z) :
    let bad := modularBad ∪ {z | spatialMatrixBlockBad e V (κ / 2) (noise z.2)}
    MeasurableSet bad ∧
      (centeredFiniteProbabilityMeasure μ law).real bad ≤ εmod + εsp ∧
      ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law,
        z ∉ bad → recovered z ∧ charge z ≤ cutoff ∧
          ∀ block : Fin 2, κ / 2 < |Matrix.det (fun i j : Fin n =>
            spatialMatrixNormalizedEntries e V (noise z.2) (block, j, i))| := by
  have hspmeas : MeasurableSet
      {z : C × Ω | spatialMatrixBlockBad e V (κ / 2) (noise z.2)} :=
    (Set.toFinite {x : Ω | spatialMatrixBlockBad e V (κ / 2) (noise x)}).measurableSet.preimage
      measurable_snd
  refine ⟨hmeas.union hspmeas, ?_, ?_⟩
  · exact (measureReal_union_le _ _).trans (add_le_add hmodmass hspmass)
  · filter_upwards [centeredFiniteProbabilityMeasure_ae_positive_weight μ law hweight, hae]
      with z hz hrec
    intro hgood
    have hmod : z ∉ modularBad := fun h => hgood (Or.inl h)
    have hsp : ¬spatialMatrixBlockBad e V (κ / 2) (noise z.2) :=
      fun h => hgood (Or.inr h)
    refine ⟨hrec, le_of_not_gt (fun h => hmod ((hmodular z.1 z.2 hz).mpr h)), ?_⟩
    intro block
    exact lt_of_not_ge (fun h => hsp ⟨block, h⟩)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplerSeparatedVariables
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {D G : Type*} {B : D → Type*}

noncomputable def samplerSeparatedVariable (inactive : D → Prop) (h : D → ℕ) :
    SamplerTupleIndex G B h →
      SamplerLongVariables inactive G B h ⊕ (PrincipalTupleIndex B h × Option Empty) := by
  classical
  exact fun
    | .inl g => .inl (.inl g)
    | .inr ⟨d, b, v⟩ =>
        if hd : inactive d then .inr (⟨d, b, v⟩, none)
        else .inl (.inr ⟨⟨d, hd⟩, b, v⟩)

@[simp] theorem samplerSeparatedVariable_common (inactive : D → Prop)
    (h : D → ℕ) (g : G) :
    samplerSeparatedVariable (B := B) inactive h (.inl g) = .inl (.inl g) := rfl

@[simp] theorem samplerSeparatedVariable_inactive (inactive : D → Prop)
    (h : D → ℕ) (d : D) (b : B d) (v : Fin (h d)) (hd : inactive d) :
    samplerSeparatedVariable (G := G) inactive h (.inr ⟨d, b, v⟩) =
      .inr (⟨d, b, v⟩, none) := by
  simp only [samplerSeparatedVariable, hd, dite_true]

@[simp] theorem samplerSeparatedVariable_active (inactive : D → Prop)
    (h : D → ℕ) (d : D) (b : B d) (v : Fin (h d)) (hd : ¬ inactive d) :
    samplerSeparatedVariable (G := G) inactive h (.inr ⟨d, b, v⟩) =
      .inl (.inr ⟨⟨d, hd⟩, b, v⟩) := by
  simp only [samplerSeparatedVariable, hd, dite_false]

def samplerFrozenRaw {R : Type*} [Zero R] (h : D → ℕ)
    (raw : PrincipalTupleIndex B h × Option Empty → R) :
    SamplerTupleIndex G B h → R :=
  fun
    | .inl _ => 0
    | .inr k => raw (k, none)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedSeparatedCongruencePolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]

noncomputable def allocatedUnconditionedCongruenceIntegerPolynomial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ) :
    AllocatedCongruenceRankOutput X E inactive j →
      MvPolynomial (LayerSamplerVariables G I n B) ℤ
  | .inl x => C (base x.val) + spatialRankPolynomial (fun d => noise (d, x.val))
  | .inr (.inl i) => modularBoundedCoefficientPolynomial (j.val + 1) (fun q => r j q i)
  | .inr (.inr a) => modularBoundedCoefficientPolynomial (j.val + 1)
      (projection (allocatedCongruenceIntegerEmbedding inactive j a))

noncomputable def allocatedSeparatedCongruencePolynomial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    MvPolynomial (LayerSamplerLongVariables inactive G B ⊕
      (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ :=
  rename (samplerSeparatedVariable inactive (layerSamplerDegree I n))
    (allocatedUnconditionedCongruenceIntegerPolynomial inactive j base noise r projection o)

variable (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j)

end Erdos3.VectorPolynomial

end

end OAI

end


