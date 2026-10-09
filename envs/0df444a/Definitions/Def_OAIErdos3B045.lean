-- Prove2me | Definitions.Def_OAIErdos3B045
-- name    : OAIErdos3B045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T06:55:24.912766+00:00
-- url     : https://prove2.me/theorems/c898aa34-0c7e-4460-be6c-dd0e56e68b9d
-- title:
--   OpenAI Erdős-3 split, definitions bundle 46 of 132
-- statement:
--   Definitions bundle 46 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B044`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 46 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.current_correction_derivative_terms_vanish`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_bracket_to_current_layer`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_current_layer_polynomial_step`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_formal_current_layer_step`, `OAI.Erdos3.NilpotentLieFiltration.exists_formal_derivative_removal_control`, `OAI.Erdos3.NilpotentLieFiltration.exists_uniform_controlled_current_stage`, `OAI.Erdos3.NilpotentLieFiltration.exists_uniform_formal_current_layer_step`, `OAI.Erdos3.NilpotentLieFiltration.formal_bracket_correction_preserves_log_conditions`, `OAI.Erdos3.NilpotentLieFiltration.formal_bracket_to_current_layer`, `OAI.Erdos3.NilpotentLieFiltration.formal_correction_advances_log_conditions`, `OAI.Erdos3.NilpotentLieFiltration.formal_correction_preserves_bracket_remainder`, `OAI.Erdos3.NilpotentLieFiltration.formal_correction_preserves_horizontal_extra`, `OAI.Erdos3.NilpotentLieFiltration.formal_correction_preserves_projected_log`, `OAI.Erdos3.NilpotentLieFiltration.formal_correction_sub_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.formal_current_layer_correction_preserves_lifts_mod`, `OAI.Erdos3.NilpotentLieFiltration.formal_current_layer_derivative_equation`, `OAI.Erdos3.NilpotentLieFiltration.formal_current_layer_derivative_equation_mod`, `OAI.Erdos3.NilpotentLieFiltration.formal_invariant_bracket_derivative_step`, `OAI.Erdos3.NilpotentLieFiltration.formal_invariant_correction_preserves_derivative_remainder`, `OAI.Erdos3.VectorPolynomial.homogeneous_pderiv_coordinate_bound`, `OAI.Erdos3.VectorPolynomial.pderiv_coordinate_grid`, `OAI.Erdos3.VectorPolynomial.reconstructDerivatives_coordinate_bound`, `OAI.Erdos3.VectorPolynomial.reconstructDerivatives_coordinate_grid`, `OAI.Erdos3.bracketTransitionBudget`, `OAI.Erdos3.bracketTransitionBudget_nonneg`, `OAI.Erdos3.bracket_transition_budget_bounds`, `OAI.Erdos3.controlled_zero_sum_separation`, `OAI.Erdos3.current_derivative_polynomials_separate`, `OAI.Erdos3.current_derivative_terms_vanish_of_invariant_polynomial`, `OAI.Erdos3.eval₂_lie_mem_of_coefficients`, `OAI.Erdos3.exists_formal_stage_budget`, `OAI.Erdos3.exists_homogeneous_subspace_corrections_from_derivatives`, `OAI.Erdos3.le_bracketTransitionBudget`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B115

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousSubspaceCorrections
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ V : Type*} [Fintype σ] [AddCommGroup V] [Module ℚ V]

theorem reconstructDerivatives_coordinate_bound {d : ℕ} (hd : 0 < d)
    (f : V →ₗ[ℚ] ℝ) (P : σ → VectorPolynomial σ ℚ V)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (hP : ∀ i α, |f (coefficients (P i) α)| ≤ M / (T i * monomialScale T α))
    (β : σ →₀ ℕ) :
    |f (coefficients (reconstructDerivatives d P) β)| ≤
      ((Fintype.card σ : ℝ) / d * M) / monomialScale T β := by
  classical
  have hscale (i : σ) (hi : i ∈ β.support) :
      T i * monomialScale T (β - Finsupp.single i 1) = monomialScale T β := by
    calc
      _ = monomialScale T ((β - Finsupp.single i 1) + Finsupp.single i 1) := by
        rw [monomialScale_add]
        simp [monomialScale, mul_comm]
      _ = _ := by rw [Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hi)]
  have hc : f (coefficients (reconstructDerivatives d P) β) =
      (d : ℝ)⁻¹ * ∑ i, if i ∈ β.support then f (coefficients (P i) (β - Finsupp.single i 1)) else 0 := by
    rw [coefficients_reconstructDerivatives, map_smul, map_sum]
    simp only [apply_ite, map_zero, Rat.smul_def, Rat.cast_inv, Rat.cast_natCast]
  have hsum : |∑ i, if i ∈ β.support then f (coefficients (P i) (β - Finsupp.single i 1)) else 0| ≤
      (Fintype.card σ : ℝ) * (M / monomialScale T β) := by
    calc
      _ ≤ ∑ i, |if i ∈ β.support then f (coefficients (P i) (β - Finsupp.single i 1)) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : σ, M / monomialScale T β := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hi
        · exact (hP i (β - Finsupp.single i 1)).trans_eq
            (congrArg (fun q : ℝ => M / q) (hscale i hi))
        · rw [abs_zero]
          exact div_nonneg hM (monomialScale_pos T hT β).le
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hc, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_pos.mpr hd).le)]
  calc
    _ ≤ (d : ℝ)⁻¹ * ((Fintype.card σ : ℝ) * (M / monomialScale T β)) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_pos.mpr hd).le)
    _ = _ := by ring

theorem reconstructDerivatives_coordinate_grid {ι : Type*} {d : ℕ} (hd : 0 < d)
    (f : V →ₗ[ℚ] (ι → ℝ)) (P : σ → VectorPolynomial σ ℚ V) (l : ℕ)
    (hP : ∀ i α, f (coefficients (P i) α) ∈ realDenominatorGrid l) (β : σ →₀ ℕ) :
    f (coefficients (reconstructDerivatives d P) β) ∈ realDenominatorGrid (l * d) := by
  classical
  let v : σ → ι → ℝ := fun i =>
    if i ∈ β.support then f (coefficients (P i) (β - Finsupp.single i 1)) else 0
  have hv (i : σ) : v i ∈ realDenominatorGrid l := by
    dsimp [v]
    split_ifs
    · exact hP i _
    · exact ⟨0, by ext j; simp⟩
  have hsum : (∑ i, v i) ∈ realDenominatorGrid l := by
    have h := realDenominatorGrid_linear_combination 1 l (fun _ : σ => (1 : ℝ)) v
      (by exact ⟨fun _ => 1, by ext i; simp⟩) hv
    simpa only [one_smul, Nat.mul_one] using h
  have hc : f (coefficients (reconstructDerivatives d P) β) = (d : ℝ)⁻¹ • ∑ i, v i := by
    rw [coefficients_reconstructDerivatives, map_smul, map_sum]
    simp only [apply_ite, map_zero]
    change (d : ℚ)⁻¹ • (∑ i, v i) = (d : ℝ)⁻¹ • ∑ i, v i
    ext j
    simp [Pi.smul_apply, Rat.smul_def]
  rw [hc]
  exact realDenominatorGrid_div_nat l d hd _ hsum

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ V ι : Type*} [Fintype σ] [AddCommGroup V] [Module ℚ V]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype ν] [Fintype σ] {E V : Submodule ℚ L}

theorem exists_homogeneous_subspace_corrections_from_derivatives
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    {H J l d : ℕ} (hH : 1 ≤ H) (hl : 0 < l) (hd : 0 < d)
    (hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) J)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : ((l * d : ℕ) : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hPE : ∀ α, coefficients P α ∈ E.baseChange ℝ)
    (hP : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients P α = 0)
    (S R : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hS : ∀ i α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d - 1 → coefficients (S i) α = 0)
    (hR : ∀ i α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d - 1 → coefficients (R i) α = 0)
    (hsplit : ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P - S i - R i) α ∈ V.baseChange ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hbudget : (Fintype.card σ : ℝ) / d * M ≤ Real.exp p)
    (hslow : ∀ i α n, |realQuotientCoordinateMap f (coefficients (S i) α) n| ≤
      M / (T i * monomialScale T α))
    (hrational : ∀ i α, realQuotientCoordinateMap f (coefficients (R i) α) ∈
      realDenominatorGrid l) :
    ∃ (m : ℕ) (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      map ((realQuotientCoordinateMap f).restrictScalars ℚ) A =
        map ((realQuotientCoordinateMap f).restrictScalars ℚ) (reconstructDerivatives d S) ∧
      map ((realQuotientCoordinateMap f).restrictScalars ℚ) B =
        map ((realQuotientCoordinateMap f).restrictScalars ℚ) (reconstructDerivatives d R) ∧
      (∀ α, coefficients A α ∈ E.baseChange ℝ ∧ coefficients B α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients A α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients B α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) *
          Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      ∀ α, coefficients (P - A - B) α ∈ (E ⊓ V).baseChange ℝ := by
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  let q := (realQuotientCoordinateMap f).restrictScalars ℚ
  have hShom := reconstructDerivatives_homogeneous hd S hS
  have hRhom := reconstructDerivatives_homogeneous hd R hR
  have hS0 : coefficients (reconstructDerivatives d S) 0 = 0 :=
    hShom 0 (by simpa using Nat.ne_of_lt hd)
  have hR0 : coefficients (reconstructDerivatives d R) 0 = 0 :=
    hRhom 0 (by simpa using Nat.ne_of_lt hd)
  have hSnorm (α : σ →₀ ℕ) :
      ‖realQuotientCoordinateMap f (coefficients (reconstructDerivatives d S) α)‖ ≤
        Real.exp p / monomialScale T α := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg (Real.exp_nonneg _)
      (monomialScale_pos T hTpos α).le)).mpr
    intro n
    rw [Real.norm_eq_abs]
    have hbound := reconstructDerivatives_coordinate_bound hd ((LinearMap.proj n).comp q)
      S T hTpos hM (fun i β => hslow i β n) α
    exact hbound.trans (div_le_div_of_nonneg_right hbudget (monomialScale_pos T hTpos α).le)
  have hRgrid (α : σ →₀ ℕ) :
      realQuotientCoordinateMap f (coefficients (reconstructDerivatives d R) α) ∈
        realDenominatorGrid (l * d) :=
    reconstructDerivatives_coordinate_grid hd q R l hrational α
  have hres := homogeneous_derivative_split_mod ((V.baseChange ℝ).restrictScalars ℚ)
    hd P hP S R hsplit
  have h := exists_controlled_subspace_correction_polynomials b e f hH (Nat.mul_pos hl hd)
    hA he hp hrows hcols hHp hlp T hT P (reconstructDerivatives d S)
    (reconstructDerivatives d R) hPE hS0 hR0 hSnorm hRgrid hres
  obtain ⟨m, A, B, hm, hmp, hAQ, hBQ, hE, hAz, hBz, hAnorm, hBgrid, hresidual⟩ := h
  exact ⟨m, A, B, hm, hmp, hAQ, hBQ, hE,
    fun α hα => hAz α (hShom α hα), fun α hα => hBz α (hRhom α hα),
    hAnorm, hBgrid, hresidual⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledCurrentLayerPolynomialStep
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct Matrix

variable {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype ν] [Fintype σ] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {E V : Submodule ℚ L}

include hlayers in
theorem exists_controlled_current_layer_polynomial_step
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    (hgraded : BasisHomogeneousBrackets (b.baseChange ℝ) w)
    {j H J l : ℕ} (hj : 0 < j)
    (hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : ((l * j : ℕ) : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P Pj : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hPU : ∀ α, coefficients P α ∈ U)
    (hPgraded : P ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (hPj : Pj = map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P)
    (hPjE : ∀ α, coefficients Pj α ∈ E.baseChange ℝ)
    (S R : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hS : ∀ i α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients (S i) α = 0)
    (hR : ∀ i α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients (R i) α = 0)
    (hsplit : ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) Pj - S i - R i) α ∈ V.baseChange ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hbudget : (Fintype.card σ : ℝ) / j * M ≤ Real.exp p)
    (hslow : ∀ i α n, |realQuotientCoordinateMap f (coefficients (S i) α) n| ≤
      M / (T i * monomialScale T α))
    (hrational : ∀ i α, realQuotientCoordinateMap f (coefficients (R i) α) ∈ realDenominatorGrid l) :
    ∃ (m : ℕ) (A B P' : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      (∀ α, coefficients A α ∈ E.baseChange ℝ ∧ coefficients B α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients A α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients B α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) *
          Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      P' = bchRemove s A P B ∧ lieBCH s (lieBCH s A P') B = P ∧
      coefficients P' 0 = coefficients P 0 ∧
      P' ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
      (∀ α, coefficients P' α ∈ U) ∧
      (∀ α, coefficients (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P') α ∈
        (E ⊓ V).baseChange ℝ) ∧
      ∀ d < j, map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P' =
        map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P := by
  have hPjhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients Pj α = 0 := by
    intro α hα
    rw [hPj]
    exact gradedPolynomialSubmodule_projection_homogeneous (b.baseChange ℝ) w (fun _ => 1)
      P hPgraded j α hα
  have h := exists_homogeneous_subspace_corrections_from_derivatives b e f hH hl hj
    hA he hp hrows hcols hHp hlp T hT Pj hPjE hPjhom S R hS hR hsplit hM hbudget hslow hrational
  obtain ⟨m, A, B, hm, hmp, _, _, hAB, hAhom, hBhom, hAnorm, hBgrid, hres⟩ := h
  have hA0 : coefficients A 0 = 0 := hAhom 0 (by simpa using Nat.ne_of_lt hj)
  have hB0 : coefficients B 0 = 0 := hBhom 0 (by simpa using Nat.ne_of_lt hj)
  have hgrades := F.polynomial_bchRemove_grades b w hlayers (E.baseChange ℝ) j hE A P B
    (fun α => (hAB α).1) (fun α => (hAB α).2)
  have hAgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1)
    j A hAhom (fun α => hE _ (hAB α).1)
  have hBgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1)
    j B hBhom (fun α => hE _ (hAB α).2)
  refine ⟨m, A, B, bchRemove s A P B, hm, hmp, hAB, hAhom, hBhom, hAnorm, hBgrid, rfl,
    bchRemove_factorization F.realification.lowerCentralSeries_eq_bot A P B,
    bchRemove_constant F.realification.lowerCentralSeries_eq_bot A P B hA0 hB0,
    bchRemove_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w hgraded (fun _ => 1) s A P B
      hAgraded hPgraded hBgraded,
    bchRemove_coefficients_mem U s A P B (fun α => hEU _ (hAB α).1) hPU
      (fun α => hEU _ (hAB α).2), ?_, hgrades.2⟩
  intro α
  rw [hgrades.1, ← hPj]
  exact hres α

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFormalCurrentLayerStep
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem controlled_zero_sum_separation {ι : Type*} [Fintype ι]
    {l : ℕ} (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hlp : (l : ℝ) ≤ Real.exp p)
    (a b : ι → ℝ) (ha : ‖a‖ ≤ Real.exp p / Real.exp (separationBudget p))
    (hb : b ∈ realDenominatorGrid l) (hsum : a + b = 0) : a = 0 ∧ b = 0 := by
  have h := controlled_small_vector_separation (0 : Matrix ι Empty ℚ)
    (H := 1) (by omega) hl (by intro i j; exact j.elim) hp hι
    (by simpa using hp) (by simpa using Real.one_le_exp hp) hlp a b ha hb
    (by rw [hsum]; exact Submodule.zero_mem _)
  simpa only [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] using h

theorem current_derivative_polynomials_separate
    {L ι σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
    (V : Submodule ℚ L) (f : Basis ι ℚ (L ⧸ V))
    {l : ℕ} (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (S R : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i α, ‖realQuotientCoordinateMap f (coefficients (S i) α)‖ ≤
      Real.exp p / (T i * monomialScale T α))
    (hrational : ∀ i α, realQuotientCoordinateMap f (coefficients (R i) α) ∈
      realDenominatorGrid l)
    (hsum : ∀ i α, coefficients (S i + R i) α ∈ V.baseChange ℝ) :
    ∀ i α, coefficients (S i) α ∈ V.baseChange ℝ ∧
      coefficients (R i) α ∈ V.baseChange ℝ := by
  have hTone (i : σ) : 1 ≤ T i :=
    (Real.one_le_exp (separationBudget_nonneg hp)).trans (hT i)
  intro i α
  have hscale : Real.exp (separationBudget p) ≤ T i * monomialScale T α :=
    (hT i).trans (le_mul_of_one_le_right (zero_le_one.trans (hTone i))
      (one_le_monomialScale T hTone α))
  have hnorm : ‖realQuotientCoordinateMap f (coefficients (S i) α)‖ ≤
      Real.exp p / Real.exp (separationBudget p) :=
    (hsmall i α).trans (div_le_div_of_nonneg_left (Real.exp_nonneg _) (Real.exp_pos _) hscale)
  have hzero : realQuotientCoordinateMap f (coefficients (S i) α) +
      realQuotientCoordinateMap f (coefficients (R i) α) = 0 := by
    have h := (realQuotientCoordinateMap_eq_zero_iff f _).mpr (hsum i α)
    simpa only [map_add, Finsupp.add_apply] using h
  obtain ⟨hS, hR⟩ := controlled_zero_sum_separation hl hp hι hlp _ _ hnorm (hrational i α) hzero
  exact ⟨(realQuotientCoordinateMap_eq_zero_iff f _).mp hS,
    (realQuotientCoordinateMap_eq_zero_iff f _).mp hR⟩

theorem current_derivative_terms_vanish_of_invariant_polynomial
    {L ι σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
    (V : Submodule ℚ L) (f : Basis ι ℚ (L ⧸ V))
    {l : ℕ} (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : ∀ α, coefficients P α ∈ V.baseChange ℝ)
    (S R : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i α, ‖realQuotientCoordinateMap f (coefficients (S i) α)‖ ≤
      Real.exp p / (T i * monomialScale T α))
    (hrational : ∀ i α, realQuotientCoordinateMap f (coefficients (R i) α) ∈
      realDenominatorGrid l)
    (hsplit : ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P - S i - R i) α ∈ V.baseChange ℝ) :
    ∀ i α, coefficients (S i) α ∈ V.baseChange ℝ ∧
      coefficients (R i) α ∈ V.baseChange ℝ := by
  apply current_derivative_polynomials_separate V f hl hp hι hlp T hT S R hsmall hrational
  intro i α
  have hD : coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P) α ∈
      V.baseChange ℝ := by
    rw [coefficients_pderiv]
    exact ((V.baseChange ℝ).restrictScalars ℚ).smul_mem _ (hP _)
  have h := (V.baseChange ℝ).sub_mem hD (hsplit i α)
  simp only [map_sub, Finsupp.sub_apply] at h
  simp only [map_add, Finsupp.add_apply]
  convert h using 1
  abel

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem eval₂_lie_mem_of_coefficients {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
    (V : Submodule ℝ L) (P : VectorPolynomial σ ℚ L) (x : L)
    (hP : ∀ α, ⁅coefficients P α, x⁆ ∈ V) (t : σ → ℝ) : ⁅eval₂ t P, x⁆ ∈ V := by
  classical
  rw [← sum_monomial_coefficients P]
  simp only [Finsupp.sum, map_sum, eval₂_monomial, sum_lie, smul_lie]
  exact V.sum_mem (fun α _ => V.smul_mem _ (hP α))

namespace NilpotentLieFiltration

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem formal_current_layer_derivative_equation (hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) {j : ℕ} (hj : 2 ≤ j)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hU : ∀ α, coefficients P.coord α ∈ U)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V)
    (hbracket : ∀ α k, k ∈ K →
      ⁅coefficients P.coord α, k⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hsystem : PolynomialDerivativeSystem P small rational extra) :
    ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
          (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P.coord) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α ∈ V := by
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  have hUvalue (t : σ → ℝ) : eval₂ t P.coord ∈ Uq :=
    (eval₂_mem_iff_coefficients U.toSubmodule P.coord).mpr hU t
  apply F.real_current_layer_polynomial_derivative_equation b w hlayers hs Uq V K hUV hV hj
    P.coord hUvalue hK hlower
    (fun t k hk => eval₂_lie_mem_of_coefficients _ P.coord k (fun α => hbracket α k hk) t)
    small rational hrational (fun i t => eval₂ t (extra i))
    (fun i t => realPolynomialJet i t P)
    (fun i t => realPolynomialJet_base i t P) (fun i t => realPolynomialJet_tangent i t P)
  · intro i t
    have h := (eval₂_mem_iff_coefficients _ _).mpr (hextra i) t
    simpa only [map_sub, eval₂_map] using h
  · intro i t
    simpa only [realPolynomialJet_baseHom] using
      PolynomialDerivativeSystem.real_evaluation P small rational extra hsystem i t

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem formal_current_layer_derivative_equation_mod (hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) {j : ℕ} (hj : 2 ≤ j)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hU : ∀ α, coefficients P.coord α ∈ U)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V)
    (hbracket : ∀ α k, k ∈ K →
      ⁅coefficients P.coord α, k⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational extra) :
    ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
          (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P.coord) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α ∈ V := by
  obtain ⟨error, herror, hexact⟩ := PolynomialDerivativeSystemMod.exact_system
    (V.restrictScalars ℚ) P small rational extra hsystem
  apply F.formal_current_layer_derivative_equation b w hlayers hs U V K hUV hV hj
    P hU hK hlower hbracket small rational (fun i => extra i + error i) hrational _ hexact
  intro i α
  have heq : extra i + error i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord) =
      (extra i - VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) + error i := by abel
  rw [heq, map_add, Finsupp.add_apply]
  exact Submodule.add_mem _ (hextra i α) (Submodule.mem_sup_left (herror i α))

theorem formal_current_layer_correction_preserves_lifts_mod {κ : Type*} (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℚ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.realification.layer j)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : κ → ℝ ⊗[ℚ] L)
    (hSR : PolynomialLiftSystemMod V P S R)
    (hS : ∀ t α, coefficients (S t - monomial 0 (k t)) α ∈ V ⊔ F.realification.layer (j + 1))
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ F.realification.layer (j + 1)) :
    PolynomialLiftSystemMod V (A⁻¹ * P * B⁻¹)
        (fun t => dualAdjoint A⁻¹ (S t)) (fun t => dualAdjoint B (R t)) ∧
      ∀ t α,
        coefficients (dualAdjoint A⁻¹ (S t) - monomial 0 (k t)) α ∈ V ⊔ F.realification.layer (j + 1) ∧
        coefficients (dualAdjoint B (R t) - monomial 0 (k t)) α ∈ V ⊔ F.realification.layer (j + 1) := by
  refine ⟨PolynomialLiftSystemMod.remove U V hUV P A B hAU S R hSR, ?_⟩
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ F.realification.layer j :=
    (coefficientSubmodule (F.realification.layer j)).neg_mem hA
  intro t α
  have hleft := F.realification.polynomialFiltration.adjoint_correction_sub_mem_layer hs j A⁻¹ hAi (S t)
  have hright := F.realification.polynomialFiltration.adjoint_correction_sub_mem_layer hs j B hB (R t)
  constructor
  · have h := (V ⊔ F.realification.layer (j + 1)).add_mem (Submodule.mem_sup_right (hleft α)) (hS t α)
    convert h using 1
    simp only [map_sub, Finsupp.sub_apply]
    abel
  · have h := (V ⊔ F.realification.layer (j + 1)).add_mem (Submodule.mem_sup_right (hright α)) (hR t α)
    convert h using 1
    simp only [map_sub, Finsupp.sub_apply]
    abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem homogeneous_pderiv_coordinate_bound [Fintype σ] [Fintype ι]
    (q : L →ₗ[ℚ] (ι → ℝ)) (P : VectorPolynomial σ ℚ L) (j : ℕ)
    (hP : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients P α = 0)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ α, ‖q (coefficients P α)‖ ≤ M / monomialScale T α)
    (i : σ) (α : σ →₀ ℕ) :
    ‖q (coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor L P) α)‖ ≤
      j * M / (T i * monomialScale T α) := by
  classical
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg j) hM)
    (mul_pos (hT i) (monomialScale_pos T hT α)).le)).mpr
  intro n
  let f := (LinearMap.proj n).comp q
  have hdegree : ∀ (β : σ →₀ ℕ) k, j < β k → f (coefficients P β) = 0 := by
    intro β k hk
    have hw := Finsupp.le_weight (fun _ : σ => (1 : ℕ)) (s := k) (by decide) β
    have hne : Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ j := by omega
    rw [hP β hne, map_zero]
  have hcoord (β : σ →₀ ℕ) : |f (coefficients P β)| ≤ M / monomialScale T β := by
    exact (norm_le_pi_norm (q (coefficients P β)) n).trans (hbound β)
  have h := directionalDerivative_single_scaled_bound f P j hdegree T hT M hM hcoord i α
  rw [directionalDerivative_single] at h
  change |f (coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor L P) α)| ≤ _
  convert h using 1
  ring

theorem pderiv_coordinate_grid (q : L →ₗ[ℚ] (ι → ℝ)) (P : VectorPolynomial σ ℚ L) (l : ℕ)
    (hP : ∀ α, q (coefficients P α) ∈ realDenominatorGrid l) (i : σ) (α : σ →₀ ℕ) :
    q (coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor L P) α) ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hP (α + Finsupp.single i 1)
  rw [coefficients_pderiv, map_smul]
  refine ⟨fun n => (α i + 1 : ℤ) * z n, ?_⟩
  funext n
  have hzn : (z n : ℝ) = (l : ℝ) * q (coefficients P (α + Finsupp.single i 1)) n := congrFun hz n
  change (((α i + 1 : ℤ) * z n : ℤ) : ℝ) =
    (l : ℝ) * (((α i + 1 : ℚ) : ℝ) * q (coefficients P (α + Finsupp.single i 1)) n)
  simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Rat.cast_add, Rat.cast_natCast, Rat.cast_one, hzn]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem formal_correction_sub_mem_layer (j : ℕ)
    (P A B : PolynomialGroup σ F.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.layer j) :
    ∀ α, coefficients ((A⁻¹ * P * B⁻¹).coord - P.coord) α ∈ F.layer j := by
  have h := F.polynomialFiltration.correction_removal_preserves_lower_layers (j := j + 1)
    A P B (by rw [Nat.add_sub_cancel]; exact hA)
    (by rw [Nat.add_sub_cancel]; exact hB) (by omega)
  rw [Nat.add_sub_cancel] at h
  exact h

theorem formal_correction_preserves_bracket_remainder (V : Submodule ℚ L) (j : ℕ)
    (P A B : PolynomialGroup σ F.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.layer j)
    (x : L) (hbracket : ∀ α, ⁅coefficients P.coord α, x⁆ ∈ V ⊔ F.layer (j + 1)) :
    ∀ α, ⁅coefficients (A⁻¹ * P * B⁻¹).coord α, x⁆ ∈ V ⊔ F.layer (j + 1) := by
  intro α
  have hx : x ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hdiff := F.formal_correction_sub_mem_layer j P A B hA hB α
  have hlie := F.lie_mem hdiff hx
  have h := (V ⊔ F.layer (j + 1)).add_mem (Submodule.mem_sup_right hlie) (hbracket α)
  simp only [map_sub, Finsupp.sub_apply, sub_lie, sub_add_cancel] at h
  exact h

variable {μ : Type*} (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem formal_correction_preserves_projected_log {j : ℕ}
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.realification.layer j) :
    ∀ d < j, VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ)
        (A⁻¹ * P * B⁻¹).coord =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord := by
  intro d hd
  apply F.polynomial_grade_eq_of_sub_mem_next b w hlayers d
  intro α
  exact F.realification.antitone (Nat.succ_le_of_lt hd)
    (F.realification.formal_correction_sub_mem_layer j P A B hA hB α)

include hlayers in
theorem formal_correction_advances_log_conditions {j : ℕ} (hj : 2 ≤ j)
    (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.realification.layer j)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V)
    (hcurrent : ∀ α, coefficients (VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (A⁻¹ * P * B⁻¹).coord) α ∈ V) :
    (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients (A⁻¹ * P * B⁻¹).coord α) ∈ K) ∧
      ∀ α d, 2 ≤ d → d < j + 1 →
        basisGradeProjection (b.baseChange ℝ) w d (coefficients (A⁻¹ * P * B⁻¹).coord α) ∈ V := by
  have hbelow := F.formal_correction_preserves_projected_log b w hlayers P A B hA hB
  have hcoef (d : ℕ) (hd : d < j) (α : σ →₀ ℕ) :
      basisGradeProjection (b.baseChange ℝ) w d (coefficients (A⁻¹ * P * B⁻¹).coord α) =
        basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) := by
    have h := congrArg (fun X : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients X α) (hbelow d hd)
    simp only [coefficients_map, LinearMap.restrictScalars_apply] at h
    exact h
  constructor
  · intro α
    rw [hcoef 1 (by omega)]
    exact hK α
  · intro α d hd hdj
    rcases lt_or_eq_of_le (show d ≤ j by omega) with hlt | rfl
    · rw [hcoef d hlt]
      exact hlower α d hd hlt
    · have h := hcurrent α
      simp only [coefficients_map, LinearMap.restrictScalars_apply] at h
      exact h

include hlayers in
theorem formal_correction_preserves_horizontal_extra (hs : 2 ≤ s) {j : ℕ} (hj : 2 ≤ j)
    (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.realification.layer j)
    (extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    ∀ i α, coefficients (dualAdjoint A⁻¹ (extra i) - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) (A⁻¹ * P * B⁻¹).coord)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  have hlow := F.formal_correction_preserves_projected_log b w hlayers P A B hA hB 1 (by omega)
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ F.realification.layer j :=
    (coefficientSubmodule (F.realification.layer j)).neg_mem hA
  intro i α
  rw [← pderiv_map, hlow, pderiv_map]
  have hdiff := F.realification.polynomialFiltration.adjoint_correction_sub_mem_layer hs j A⁻¹ hAi (extra i)
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem
    (Submodule.mem_sup_right (hdiff α)) (hextra i α)
  convert h using 1
  simp only [map_sub, Finsupp.sub_apply]
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ ι σ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype σ] [Fintype ι] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem current_correction_derivative_terms_vanish (hs : 2 ≤ s)
    (V : Submodule ℚ L) (f : Basis ι ℚ (L ⧸ V)) {j l m : ℕ} (hj : 0 < j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients B.coord α) = coefficients B.coord α)
    (hAhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients A.coord α = 0)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsplit : ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
        (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P.coord) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α ∈ V.baseChange ℝ)
    (hnew : ∀ α, coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (A⁻¹ * P * B⁻¹).coord) α ∈ V.baseChange ℝ)
    {p M C : ℝ} (hp : 0 ≤ p) (hC : 0 ≤ C)
    (hdim : (Fintype.card ι : ℝ) ≤ p) (hl : 0 < l) (hm : 0 < m)
    (hden : ((l * m : ℕ) : ℝ) ≤ Real.exp p) (hsize : M + j * C ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (hsmall : ∀ i α, ‖realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i)) α)‖ ≤
        M / (T i * monomialScale T α))
    (hrational : ∀ i α, realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α) ∈
        realDenominatorGrid l)
    (hAnorm : ∀ α, ‖realQuotientCoordinateMap f (coefficients A.coord α)‖ ≤ C / monomialScale T α)
    (hBgrid : ∀ α, realQuotientCoordinateMap f (coefficients B.coord α) ∈ realDenominatorGrid m) :
    ∀ i α, coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (dualAdjoint A⁻¹ (small i - formalLogDerivative i A))) α ∈ V.baseChange ℝ ∧
      coefficients (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (dualAdjoint B (rational i) - formalLogDerivative i B)) α ∈ V.baseChange ℝ := by
  let π := VectorPolynomial.map (σ := σ) ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
  let q := (realQuotientCoordinateMap f).restrictScalars ℚ
  let small' := fun i => π (dualAdjoint A⁻¹ (small i - formalLogDerivative i A))
  let rational' := fun i => π (dualAdjoint B (rational i) - formalLogDerivative i B)
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hparts (i : σ) := F.current_derivative_removal_projection b w hlayers hs hj i A B hA hB (small i) (rational i)
  have hsmall' : ∀ i α, ‖realQuotientCoordinateMap f (coefficients (small' i) α)‖ ≤
      Real.exp p / (T i * monomialScale T α) := by
    intro i α
    have hD := homogeneous_pderiv_coordinate_bound q A.coord j hAhom T hTpos hC hAnorm i α
    have he : small' i = π (small i) - (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) A.coord :=
      (hparts i).1
    rw [he, map_sub, Finsupp.sub_apply, map_sub]
    calc
      _ ≤ ‖realQuotientCoordinateMap f (coefficients (π (small i)) α)‖ +
          ‖realQuotientCoordinateMap f (coefficients
            ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) A.coord) α)‖ := norm_sub_le _ _
      _ ≤ M / (T i * monomialScale T α) + j * C / (T i * monomialScale T α) := add_le_add (hsmall i α) hD
      _ = (M + j * C) / (T i * monomialScale T α) := by ring
      _ ≤ Real.exp p / (T i * monomialScale T α) :=
        div_le_div_of_nonneg_right hsize (mul_pos (hTpos i) (monomialScale_pos T hTpos α)).le
  have hrational' : ∀ i α, realQuotientCoordinateMap f (coefficients (rational' i) α) ∈
      realDenominatorGrid (l * m) := by
    intro i α
    have he : rational' i = π (rational i) - (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) B.coord :=
      (hparts i).2
    rw [he, map_sub, Finsupp.sub_apply, map_sub]
    exact realDenominatorGrid_sub_product l m _ _ (hrational i α)
      (pderiv_coordinate_grid q B.coord m hBgrid i α)
  apply current_derivative_terms_vanish_of_invariant_polynomial V f (Nat.mul_pos hl hm) hp hdim hden T hT
    (π (A⁻¹ * P * B⁻¹).coord) hnew small' rational' hsmall' hrational'
  intro i α
  have he := F.current_derivative_defect_preserved b w hlayers hs hj i P A B hA hB (small i) (rational i)
  change coefficients
    ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) (π (A⁻¹ * P * B⁻¹).coord) - small' i - rational' i) α ∈ _
  rw [he]
  exact hsplit i α

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype ν] [Fintype σ] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {E V : Submodule ℚ L}

include hlayers in
theorem exists_controlled_formal_current_layer_step
    (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    {j H J Q l : ℕ} (hj : 2 ≤ j)
    (hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    {p q M : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hrows : (Fintype.card ι : ℝ) ≤ p) (hcols : (Fintype.card ν : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : ((l * j : ℕ) : ℝ) ≤ Real.exp p)
    (hbudget : (Fintype.card σ : ℝ) / j * M ≤ Real.exp p)
    (hrowsq : (Fintype.card ι : ℝ) ≤ q)
    (hden : ((l * matrixDenominator (quotientCoordinateMatrix b f) *
        matrixDenominator (bracketLiftMatrix b e) : ℕ) : ℝ) * Real.exp ((p + 2) ^ 36) ≤ Real.exp q)
    (hsize : M + j * ((((Fintype.card μ : ℝ) + 1) * (Q + 1)) *
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) * Real.exp ((p + 2) ^ 18 + p)) ≤ Real.exp q)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (hTq : ∀ i, Real.exp (separationBudget q) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients P.coord α) ∈ E.baseChange ℝ)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V.baseChange ℝ)
    (hbracket : ∀ α k, k ∈ K →
      ⁅coefficients P.coord α, k⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hsystem : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P small rational extra)
    (hSgraded : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hRgraded : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hslow : ∀ i α, ‖realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i)) α)‖ ≤
        M / (T i * monomialScale T α))
    (hgrid : ∀ i α, realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α) ∈
        realDenominatorGrid l) :
    ∃ (m : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) * Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      let P' := A⁻¹ * P * B⁻¹
      let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
      let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
      let extra' := fun i => dualAdjoint A⁻¹ (extra i)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ α, coefficients (VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P'.coord) α ∈ (E ⊓ V).baseChange ℝ) ∧
        (∀ d < j, VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' small' rational' extra' ∧
        (∀ i, small' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          rational' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) ∧
        (∀ i α, coefficients (small' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (rational' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P'.coord α) ∈ K) ∧
        (∀ α d, 2 ≤ d → d < j + 1 →
          basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) ∈ V.baseChange ℝ) ∧
        (∀ α k, k ∈ K → ⁅coefficients P'.coord α, k⁆ ∈
          V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        ∀ i α, coefficients (extra' i - VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
            V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  let π := VectorPolynomial.map (σ := σ) ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
  have hjpos : 0 < j := by omega
  have hsplit := F.formal_current_layer_derivative_equation_mod b w hlayers hs U (V.baseChange ℝ) K
    hUV hV hj P hPU hK hlower hbracket small rational extra hrational hextra hsystem
  have h := F.exists_controlled_current_layer_polynomial_step b w hlayers Uq e f (hgraded.baseChange b w)
    hjpos hE hEU hH hl hA he hp hrows hcols hHp hlp T hT P.coord (π P.coord) hPU hPgraded rfl
    (fun α => by rw [coefficients_map]; exact hPE α) (fun i => π (small i)) (fun i => π (rational i))
    (fun i => shifted_one_projection_homogeneous (b.baseChange ℝ) w _ (hSgraded i) hjpos)
    (fun i => shifted_one_projection_homogeneous (b.baseChange ℝ) w _ (hRgraded i) hjpos)
    hsplit hM hbudget
    (fun i α n => (norm_le_pi_norm (realQuotientCoordinateMap f (coefficients (π (small i)) α)) n).trans (hslow i α)) hgrid
  obtain ⟨m, a, c, Pnew, hm, hmp, hac, hahom, hchom, hanorm, hcgrid,
    hremove, _, hconstant, hnewgraded, hnewU, hnewV, hbelow⟩ := h
  let A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot := ⟨a⟩
  let B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot := ⟨c⟩
  let P' := A⁻¹ * P * B⁻¹
  have hcoord : P'.coord = Pnew := hremove.symm
  have hApure : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients A.coord α) = coefficients A.coord α :=
    fun α => hE _ (hac α).1
  have hBpure : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients B.coord α) = coefficients B.coord α :=
    fun α => hE _ (hac α).2
  have hAU : ∀ α, coefficients A.coord α ∈ Uq := fun α => hEU _ (hac α).1
  have hBU : ∀ α, coefficients B.coord α ∈ Uq := fun α => hEU _ (hac α).2
  have hAlayer : ∀ α, coefficients A.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hApure α]
    exact F.realGradeProjection_mem_layer b w hlayers j _
  have hBlayer : ∀ α, coefficients B.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hBpure α]
    exact F.realGradeProjection_mem_layer b w hlayers j _
  let C : ℝ := (((Fintype.card μ : ℝ) + 1) * (Q + 1)) *
    (((Fintype.card ν : ℝ) + 1) * (J + 1)) * Real.exp ((p + 2) ^ 18 + p)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hAnorm : ∀ α, ‖realQuotientCoordinateMap f (coefficients A.coord α)‖ ≤ C / monomialScale T α := by
    intro α
    calc
      _ ≤ (((Fintype.card μ : ℝ) + 1) * (Q + 1)) * ‖(b.baseChange ℝ).equivFun (coefficients a α)‖ :=
        realQuotientCoordinateMap_norm_bound b f hf _
      _ ≤ (((Fintype.card μ : ℝ) + 1) * (Q + 1)) *
          ((((Fintype.card ν : ℝ) + 1) * (J + 1)) * Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) :=
        mul_le_mul_of_nonneg_left (hanorm α) (by positivity)
      _ = C / monomialScale T α := by dsimp [C]; ring
  let n := matrixDenominator (quotientCoordinateMatrix b f) * (matrixDenominator (bracketLiftMatrix b e) * m)
  have hn : 0 < n := Nat.mul_pos (matrixDenominator_pos _) (Nat.mul_pos (matrixDenominator_pos _) hm)
  have hBgrid : ∀ α, realQuotientCoordinateMap f (coefficients B.coord α) ∈ realDenominatorGrid n :=
    fun α => realQuotientCoordinateMap_grid b f _ _ (hcgrid α)
  have hden' : ((l * n : ℕ) : ℝ) ≤ Real.exp q := by
    calc
      _ = ((l * matrixDenominator (quotientCoordinateMatrix b f) *
          matrixDenominator (bracketLiftMatrix b e) : ℕ) : ℝ) * (m : ℝ) := by
        dsimp [n]
        push_cast
        ring
      _ ≤ ((l * matrixDenominator (quotientCoordinateMatrix b f) *
          matrixDenominator (bracketLiftMatrix b e) : ℕ) : ℝ) * Real.exp ((p + 2) ^ 36) :=
        mul_le_mul_of_nonneg_left hmp (by positivity)
      _ ≤ Real.exp q := hden
  have hnew : ∀ α, coefficients (π P'.coord) α ∈ V.baseChange ℝ := by
    intro α
    rw [hcoord]
    exact Submodule.baseChange_mono ℝ inf_le_right (hnewV α)
  have hvanish := F.current_correction_derivative_terms_vanish b w hlayers hs V f hjpos P A B
    hApure hBpure hahom small rational hsplit hnew hq hC hrowsq hl hn hden' hsize T hTq hslow hgrid hAnorm hBgrid
  have hadvance := F.formal_current_derivative_advance b w hlayers Uq (V.baseChange ℝ) hUV hV j A B
    hAU hBU hAlayer hBlayer small rational hsmall hrational hvanish
  have hAgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    j a hahom hApure
  have hBgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    j c hchom hBpure
  have hlog := F.formal_correction_advances_log_conditions b w hlayers hj (V.baseChange ℝ) K
    P A B hAlayer hBlayer hK hlower hnew
  have hWiff (x : ℝ ⊗[ℚ] L) :
      x ∈ (V.baseChange ℝ).restrictScalars ℚ ⊔ F.realification.layer (j + 1) ↔
        x ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
    change x ∈ (V.baseChange ℝ).restrictScalars ℚ ⊔
      (F.realLayer (j + 1)).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have hbracket' : ∀ α k, k ∈ K → ⁅coefficients P'.coord α, k⁆ ∈
      V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
    intro α k hk
    exact (hWiff _).mp (F.realification.formal_correction_preserves_bracket_remainder
      ((V.baseChange ℝ).restrictScalars ℚ) j P A B hAlayer hBlayer k
      (fun β => (hWiff _).mpr (hbracket β k hk)) α)
  refine ⟨m, A, B, hm, hmp, hac, hahom, hchom, hanorm, hcgrid, ?_, ?_, ?_, ?_, ?_, ?_,
    PolynomialDerivativeSystemMod.remove Uq ((V.baseChange ℝ).restrictScalars ℚ) hUV P A B hAU
      small rational extra hsystem, ?_, hadvance, hlog.1, hlog.2, hbracket',
    F.formal_correction_preserves_horizontal_extra b w hlayers hs hj (V.baseChange ℝ)
      P A B hAlayer hBlayer extra hextra⟩
  · group
  · change coefficients P'.coord 0 = _
    rw [hcoord]
    exact hconstant
  · change P'.coord ∈ _
    rw [hcoord]
    exact hnewgraded
  · intro α
    change coefficients P'.coord α ∈ _
    rw [hcoord]
    exact hnewU α
  · intro α
    change coefficients (π P'.coord) α ∈ _
    rw [hcoord]
    exact hnewV α
  · intro d hd
    change VectorPolynomial.map _ P'.coord = _
    rw [hcoord]
    exact hbelow d hd
  · intro i
    exact polynomial_derivative_removal_preserves_shifted_grading (b.baseChange ℝ) w (hgraded.baseChange b w)
      i A B (small i) (rational i) hAgraded hBgraded (hSgraded i) (hRgraded i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_formal_current_layer_step :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype ν] [Fintype σ] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    {E V : Submodule ℚ L}
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    {j H J Q l : ℕ} (_hj : 2 ≤ j)
    (_hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (_hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (_hH : 1 ≤ H) (_hl : 0 < l)
    (_hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (_he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (_hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    {p M : ℝ} (_hp : 0 ≤ p) (_hM : 0 ≤ M)
    (_hambient : (Fintype.card μ : ℝ) ≤ p) (_hrows : (Fintype.card ι : ℝ) ≤ p)
    (_hcols : (Fintype.card ν : ℝ) ≤ p) (_hvariables : (Fintype.card σ : ℝ) ≤ p)
    (_hjp : (j : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hJp : (J : ℝ) ≤ Real.exp p) (_hQp : (Q : ℝ) ≤ Real.exp p)
    (_hlp : (l : ℝ) ≤ Real.exp p) (_hMp : M ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (_hPU : ∀ α, coefficients P.coord α ∈ U)
    (_hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (_hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients P.coord α) ∈ E.baseChange ℝ)
    (_hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (_hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V.baseChange ℝ)
    (_hbracket : ∀ α k, k ∈ K →
      ⁅coefficients P.coord α, k⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (_hsmall : ∀ i α, coefficients (small i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hrational : ∀ i α, coefficients (rational i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (_hsystem : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P small rational extra)
    (_hSgraded : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hRgraded : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hslow : ∀ i α, ‖realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i)) α)‖ ≤
        M / (T i * monomialScale T α))
    (_hgrid : ∀ i α, realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α) ∈
        realDenominatorGrid l),
    ∃ (n : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        Real.exp ((p + C) ^ C) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈
        realDenominatorGrid n) ∧
      let P' := A⁻¹ * P * B⁻¹
      let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
      let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
      let extra' := fun i => dualAdjoint A⁻¹ (extra i)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ α, coefficients (VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P'.coord) α ∈ (E ⊓ V).baseChange ℝ) ∧
        (∀ d < j, VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' small' rational' extra' ∧
        (∀ i, small' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          rational' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) ∧
        (∀ i α, coefficients (small' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (rational' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P'.coord α) ∈ K) ∧
        (∀ α d, 2 ≤ d → d < j + 1 →
          basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) ∈ V.baseChange ℝ) ∧
        (∀ α k, k ∈ K → ⁅coefficients P'.coord α, k⁆ ∈
          V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        ∀ i α, coefficients (extra' i - VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
            V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  obtain ⟨C, hC, hCbound⟩ := exists_current_layer_uniform_budget
  refine ⟨C, hC, ?_⟩
  intro L μ ι ν σ _ _ _ _ _ _ s F b w hlayers E V
    hgraded hs U K hUV hV e f j H J Q l hj hE hEU hH hl hA he hf
    p M hp hM hambient hrows hcols hvariables hjp hHp hJp hQp hlp hMp T hT
    P hPU hPgraded hPE hK hlower hbracket small rational extra hsmall hrational hextra
    hsystem hSgraded hRgraded hslow hgrid
  let t := currentLayerConstructionBudget p
  let q := currentLayerRemovalBudget p
  have ht : 0 ≤ t := currentLayerConstructionBudget_nonneg hp
  have hq : 0 ≤ q := currentLayerRemovalBudget_nonneg hp
  have hpt : p ≤ t := le_currentLayerConstructionBudget hp
  have hEt : Real.exp p ≤ Real.exp t := Real.exp_le_exp.mpr hpt
  have hconstruction := current_layer_construction_budget_bounds hM (Fintype.card σ) j l
    hvariables (by omega) hjp hlp hMp
  have hpplus : Real.exp p ≤ Real.exp ((p + 2) ^ 1) := by
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    linarith
  have hD := matrixDenominator_le_exp_power (quotientCoordinateMatrix b f) hp 1 hrows hambient (fun i n => by
    have hden : (((quotientCoordinateMatrix b f i n).den) : ℝ) ≤ Q := Nat.cast_le.mpr (hf i n).2
    exact (hden.trans hQp).trans hpplus)
  have hEden := matrixDenominator_le_exp_power (bracketLiftMatrix b e) hp 1 hambient hcols (fun i n => by
    have hden : (((bracketLiftMatrix b e i n).den) : ℝ) ≤ J := Nat.cast_le.mpr (he i n).2
    exact (hden.trans hJp).trans hpplus)
  obtain ⟨hpq, hden, hsize, _, haCap, hbCap⟩ := current_layer_removal_budget_bounds hp
    (Fintype.card μ) (Fintype.card ν) j J Q l
    (matrixDenominator (quotientCoordinateMatrix b f)) (matrixDenominator (bracketLiftMatrix b e))
    hambient hcols hjp hJp hQp hlp hMp hD hEden
  have hCval : separationBudget t + separationBudget q + q ≤ (p + C) ^ C := hCbound p hp
  have hst := separationBudget_nonneg ht
  have hsq := separationBudget_nonneg hq
  have htCut : separationBudget t ≤ (p + C) ^ C := by linarith
  have hqCut : separationBudget q ≤ (p + C) ^ C := by linarith
  have hqBound : q ≤ (p + C) ^ C := by linarith
  have hTt : ∀ i, Real.exp (separationBudget t) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr htCut).trans (hT i)
  have hTq : ∀ i, Real.exp (separationBudget q) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hqCut).trans (hT i)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hstep := F.exists_controlled_formal_current_layer_step b w hlayers (p := t) (q := q)
    hgraded hs U K hUV hV e f hj hE hEU hH hl hA he hf ht hq hM
    (hrows.trans hpt) (hcols.trans hpt) (hHp.trans hEt) hconstruction.1 hconstruction.2
    (hrows.trans hpq) hden hsize T hTt hTq P hPU hPgraded hPE hK hlower hbracket
    small rational extra hsmall hrational hextra hsystem hSgraded hRgraded hslow hgrid
  obtain ⟨m, A, B, hm, hmp, hAB, hAhom, hBhom, hAnorm, hBgrid,
    hprod, hconstant, hnewgraded, hnewU, hnewV, hbelow, hnewsystem, hnewshift,
    hnewderivative, hnewK, hnewlower, hnewbracket, hnewextra⟩ := hstep
  let n := matrixDenominator (bracketLiftMatrix b e) * m
  have hn : 0 < n := Nat.mul_pos (matrixDenominator_pos _) hm
  have hnbound : (n : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ = (matrixDenominator (bracketLiftMatrix b e) : ℝ) * (m : ℝ) := by dsimp [n]; rw [Nat.cast_mul]
      _ ≤ (matrixDenominator (bracketLiftMatrix b e) : ℝ) * Real.exp ((t + 2) ^ 36) :=
        mul_le_mul_of_nonneg_left hmp (Nat.cast_nonneg _)
      _ ≤ Real.exp q := hbCap
      _ ≤ _ := Real.exp_le_exp.mpr hqBound
  refine ⟨n, A, B, hn, hnbound, hAB, hAhom, hBhom, ?_, hBgrid,
    hprod, hconstant, hnewgraded, hnewU, hnewV, hbelow, hnewsystem, hnewshift,
    hnewderivative, hnewK, hnewlower, hnewbracket, hnewextra⟩
  intro α
  exact (hAnorm α).trans (div_le_div_of_nonneg_right
    (haCap.trans (Real.exp_le_exp.mpr hqBound)) (monomialScale_pos T hTpos α).le)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.ControlledBracketToCurrentLayer
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ σ κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

theorem formal_invariant_correction_preserves_derivative_remainder
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hAV : ∀ α, coefficients A.coord α ∈ V) (hBV : ∀ α, coefficients B.coord α ∈ V)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule) :
    ∀ i α, coefficients (dualAdjoint A⁻¹ (small i - formalLogDerivative i A)) α ∈
        V ⊔ (F.realLayer j).toSubmodule ∧
      coefficients (dualAdjoint B (rational i) - formalLogDerivative i B) α ∈
        V ⊔ (F.realLayer j).toSubmodule := by
  let W := V.restrictScalars ℚ ⊔ F.realification.layer j
  have hWiff (x : ℝ ⊗[ℚ] L) : x ∈ W ↔ x ∈ V ⊔ (F.realLayer j).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer j).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  intro i α
  have h := polynomial_derivative_removal_preserves_coefficients U W
    (F.realification.invariant_sup_layer U (V.restrictScalars ℚ) hUV j)
    i A B (small i) (rational i) hAU hBU
    (fun β => Submodule.mem_sup_left (hAV β)) (fun β => Submodule.mem_sup_left (hBV β))
    (fun β => (hWiff _).mpr (hsmall i β)) (fun β => (hWiff _).mpr (hrational i β))
  exact ⟨(hWiff _).mp (h.1 α), (hWiff _).mp (h.2 α)⟩

include hF in
theorem formal_invariant_bracket_derivative_step (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    {j : ℕ} (hj : 2 ≤ j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hAV : ∀ α, coefficients A.coord α ∈ V) (hBV : ∀ α, coefficients B.coord α ∈ V)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : σ → κ) (I : κ → ℝ ⊗[ℚ] L)
    (hI : ∀ x, basisGradeProjection (b.baseChange ℝ) w 1 (I x) = I x)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational (fun i => S (k i)))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hS : ∀ x α, coefficients (dualAdjoint A⁻¹ (S x) - monomial 0 (I x)) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    let P' := A⁻¹ * P * B⁻¹
    let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
    let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
    let extra' := fun i => dualAdjoint A⁻¹ (S (k i))
    PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P' small' rational' extra' ∧
      (∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer j).toSubmodule ∧
        coefficients (rational' i) α ∈ V ⊔ (F.realLayer j).toSubmodule) ∧
      ∀ i α, coefficients (extra' i - VectorPolynomial.map
        ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
          V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro P' small' rational' extra'
  have hnew := PolynomialDerivativeSystemMod.remove U (V.restrictScalars ℚ) hUV P A B hAU
    small rational (fun i => S (k i)) hsystem
  have hrem := F.formal_invariant_correction_preserves_derivative_remainder U V hUV j A B
    hAU hBU hAV hBV small rational hsmall hrational
  have hmono : V ⊔ (F.realLayer j).toSubmodule ≤ V ⊔ (F.realLayer 2).toSubmodule := by
    apply sup_le_sup_left _ V
    intro x hx
    exact F.realification.antitone hj hx
  refine ⟨hnew, hrem, ?_⟩
  apply F.formal_extra_horizontal_equation b w hF hs V hV j P' small' rational' extra'
    hnew (fun i α => hmono (hrem i α).1) (fun i α => hmono (hrem i α).2)
  intro i
  exact F.formal_lift_nonhorizontal_remainder b w hF V hV (by omega : 1 ≤ j)
    (extra' i) (I (k i)) (hI _) (hS _)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hF in
theorem formal_bracket_correction_preserves_log_conditions
    (V K : Submodule ℝ (ℝ ⊗[ℚ] L)) {j : ℕ} (hj : 2 ≤ j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients B.coord α) = coefficients B.coord α)
    (hAK : j = 2 → ∀ α, coefficients A.coord α ∈ K)
    (hBK : j = 2 → ∀ α, coefficients B.coord α ∈ K)
    (hAV : 2 < j → ∀ α, coefficients A.coord α ∈ V)
    (hBV : 2 < j → ∀ α, coefficients B.coord α ∈ V)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V) :
    (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients (A⁻¹ * P * B⁻¹).coord α) ∈ K) ∧
      ∀ α d, 2 ≤ d → d < j →
        basisGradeProjection (b.baseChange ℝ) w d (coefficients (A⁻¹ * P * B⁻¹).coord α) ∈ V := by
  let E := LinearMap.ker (basisGradeProjection (b.baseChange ℝ) w (j - 1) - LinearMap.id)
  have hE : ∀ x ∈ E, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x :=
    fun _ hx => sub_eq_zero.mp hx
  have hgrades := F.polynomial_bchRemove_grades b w hF E (j - 1) hE A.coord P.coord B.coord
    (fun α => sub_eq_zero.mpr (hA α)) (fun α => sub_eq_zero.mpr (hB α))
  have hcurrent (α : σ →₀ ℕ) :
      basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients (A⁻¹ * P * B⁻¹).coord α) =
        basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α) -
          coefficients A.coord α - coefficients B.coord α := by
    have h := congrArg (fun Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients Q α) hgrades.1
    simp only [coefficients_map, map_sub, Finsupp.sub_apply, LinearMap.restrictScalars_apply] at h
    exact h
  have hbelow (d : ℕ) (hd : d < j - 1) (α : σ →₀ ℕ) :
      basisGradeProjection (b.baseChange ℝ) w d (coefficients (A⁻¹ * P * B⁻¹).coord α) =
        basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) := by
    have h := congrArg (fun Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients Q α) (hgrades.2 d hd)
    simp only [coefficients_map, LinearMap.restrictScalars_apply] at h
    exact h
  constructor
  · intro α
    by_cases hj2 : j = 2
    · have h := hcurrent α
      rw [hj2] at h
      change basisGradeProjection (b.baseChange ℝ) w 1 (coefficients (A⁻¹ * P * B⁻¹).coord α) = _ at h
      rw [h]
      exact K.sub_mem (K.sub_mem (hK α) (hAK hj2 α)) (hBK hj2 α)
    · rw [hbelow 1 (by omega)]
      exact hK α
  · intro α d hd hdj
    rcases lt_or_eq_of_le (show d ≤ j - 1 by omega) with hlt | rfl
    · rw [hbelow d hlt]
      exact hlower α d hd hdj
    · rw [hcurrent]
      exact V.sub_mem (V.sub_mem (hlower α (j - 1) hd hdj) (hAV (by omega) α)) (hBV (by omega) α)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ σ K L : Type*} [AddCommGroup K] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hF in
theorem formal_bracket_to_current_layer (hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V H : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (I : K →+ ℝ ⊗[ℚ] L) (hI : ∀ x, basisGradeProjection (b.baseChange ℝ) w 1 (I x) = I x)
    {j : ℕ} (hj : 2 ≤ j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients B.coord α) = coefficients B.coord α)
    (hAhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients A.coord α = 0)
    (hBhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients B.coord α = 0)
    (hAH : j = 2 → ∀ α, coefficients A.coord α ∈ H)
    (hBH : j = 2 → ∀ α, coefficients B.coord α ∈ H)
    (hAV : 2 < j → ∀ α, coefficients A.coord α ∈ V)
    (hBV : 2 < j → ∀ α, coefficients B.coord α ∈ V)
    (hH : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ H)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V)
    (S R : K →+ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k a c : σ → K)
    (ha : j = 2 → ∀ i, I (a i) = coefficients A.coord (Finsupp.single i 1))
    (hc : j = 2 → ∀ i, I (c i) = coefficients B.coord (Finsupp.single i 1))
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational (fun i => S (k i)))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hS : ∀ x α, coefficients (dualAdjoint A⁻¹ (S x) - monomial 0 (I x)) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hR : ∀ x α, coefficients (dualAdjoint B (R x) - monomial 0 (I x)) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hbracket : ∀ α x, x ∈ H → ⁅coefficients (A⁻¹ * P * B⁻¹).coord α, x⁆ ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    let P' := A⁻¹ * P * B⁻¹
    let S' := (dualAdjointAddEquiv A⁻¹).toAddMonoidHom.comp S
    let R' := (dualAdjointAddEquiv B).toAddMonoidHom.comp R
    let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A) + if j = 2 then S' (a i) else 0
    let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B + if j = 2 then R' (c i) else 0
    let k' := fun i => if j = 2 then k i - a i - c i else k i
    let extra' := fun i => S' (k' i)
    (∀ α, coefficients P'.coord α ∈ U) ∧
      (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P'.coord α) ∈ H) ∧
      (∀ α d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) ∈ V) ∧
      PolynomialLiftSystemMod (V.restrictScalars ℚ) P' S' R' ∧
      PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P' small' rational' extra' ∧
      (∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer j).toSubmodule ∧
        coefficients (rational' i) α ∈ V ⊔ (F.realLayer j).toSubmodule) ∧
      (∀ i α, coefficients (extra' i - VectorPolynomial.map
        ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
          V ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
      ∀ i α, coefficients
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
          (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P'.coord) -
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small' i) -
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational' i)) α ∈ V := by
  intro P' S' R' small' rational' k' extra'
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  have hnewU : ∀ α, coefficients P'.coord α ∈ U :=
    bchRemove_coefficients_mem Uq s A.coord P.coord B.coord hAU hPU hBU
  have hlogs := F.formal_bracket_correction_preserves_log_conditions b w hF V H hj P A B
    hA hB hAH hBH hAV hBV hH hlower
  have hlifts : PolynomialLiftSystemMod (V.restrictScalars ℚ) P' S' R' :=
    PolynomialLiftSystemMod.remove Uq (V.restrictScalars ℚ) hUV P A B hAU S R hSR
  have hderivatives :
      PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P' small' rational' extra' ∧
      (∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer j).toSubmodule ∧
        coefficients (rational' i) α ∈ V ⊔ (F.realLayer j).toSubmodule) ∧
      ∀ i α, coefficients (extra' i - VectorPolynomial.map
        ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
          V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    by_cases hj2 : j = 2
    · subst j
      have h := F.formal_degree_two_reabsorption b w hF hs Uq V hUV hV I hI P A B hAU
        hAhom hBhom S R small rational k a c (ha rfl) (hc rfl) hSR hsystem hsmall hrational hS hR
      simp only [P', S', R', small', rational', k', extra', ite_true]
      exact h.2
    · have h := F.formal_invariant_bracket_derivative_step b w hF hs Uq V hUV hV hj P A B
        hAU hBU (hAV (by omega)) (hBV (by omega)) S k I hI small rational hsystem hsmall hrational hS
      simp only [P', S', small', rational', k', extra', if_neg hj2, add_zero]
      exact h
  refine ⟨hnewU, hlogs.1, hlogs.2, hlifts, hderivatives.1, hderivatives.2.1, hderivatives.2.2, ?_⟩
  exact F.formal_current_layer_derivative_equation_mod b w hF hs U V H hUV hV hj P'
    hnewU hlogs.1 hlogs.2 hbracket small' rational' extra'
    (fun i α => (hderivatives.2.1 i α).2) hderivatives.2.2 hderivatives.1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

def bracketTransitionBudget (p : ℝ) : ℝ :=
  4 * p + (p + 2) ^ 8 + (p + 2) ^ 9 + 1

theorem bracket_transition_budget_bounds {p : ℝ} (hp : 0 ≤ p)
    (k m d : ℕ) (hk : (k : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hd : (d : ℝ) ≤ Real.exp ((p + 2) ^ 9)) :
    Real.exp p ≤ Real.exp (bracketTransitionBudget p) ∧
      Real.exp p + (k : ℝ) * Real.exp p * Real.exp ((p + 2) ^ 8) ≤
        Real.exp (bracketTransitionBudget p) ∧
      ((m * (m * d) : ℕ) : ℝ) ≤ Real.exp (bracketTransitionBudget p) := by
  have h8 : 0 ≤ (p + 2) ^ 8 := by positivity
  have h9 : 0 ≤ (p + 2) ^ 9 := by positivity
  have hpE : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hterm : (k : ℝ) * Real.exp p * Real.exp ((p + 2) ^ 8) ≤
      Real.exp (2 * p + (p + 2) ^ 8) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp ((p + 2) ^ 8) := by
        gcongr
        exact hk.trans hpE
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  refine ⟨Real.exp_le_exp.mpr (by unfold bracketTransitionBudget; linarith), ?_, ?_⟩
  · calc
      _ ≤ Real.exp (2 * p + (p + 2) ^ 8) + Real.exp (2 * p + (p + 2) ^ 8) :=
        add_le_add (Real.exp_le_exp.mpr (by linarith)) hterm
      _ = Real.exp (2 * p + (p + 2) ^ 8) * 2 := by ring
      _ ≤ Real.exp (2 * p + (p + 2) ^ 8) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = Real.exp (2 * p + (p + 2) ^ 8 + 1) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold bracketTransitionBudget; linarith)
  · calc
      _ = (m : ℝ) * ((m : ℝ) * (d : ℝ)) := by simp only [Nat.cast_mul]
      _ ≤ Real.exp p * (Real.exp p * Real.exp ((p + 2) ^ 9)) :=
        mul_le_mul hm (mul_le_mul hm hd (Nat.cast_nonneg _) (Real.exp_nonneg _))
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.exp_nonneg _)
      _ = Real.exp (2 * p + (p + 2) ^ 9) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold bracketTransitionBudget; linarith)

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype κ] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {K : Submodule ℚ L}

include hF in
theorem exists_controlled_bracket_to_current_layer (hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (e : Basis κ ℚ K)
    (hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {j H m : ℕ} (hj : 2 ≤ j) (hH : 1 ≤ H) (hm : 0 < m)
    (he : ∀ i z, RationalHeightLE (b.repr (e z : L) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hambient : (Fintype.card μ : ℝ) ≤ p)
    (hkernel : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hmp : (m : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients B.coord α) = coefficients B.coord α)
    (hAhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients A.coord α = 0)
    (hBhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients B.coord α = 0)
    (hAK : j = 2 → ∀ α, coefficients A.coord α ∈ K.baseChange ℝ)
    (hBK : j = 2 → ∀ α, coefficients B.coord α ∈ K.baseChange ℝ)
    (hAV : 2 < j → ∀ α, coefficients A.coord α ∈ V)
    (hBV : 2 < j → ∀ α, coefficients B.coord α ∈ V)
    (hPK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K.baseChange ℝ)
    (hlower : ∀ α d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : σ → κ → ℝ)
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational
      (fun i => basisPolynomialLift (Pi.basisFun ℝ κ) S (k i)))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hS : ∀ z α, coefficients (dualAdjoint A⁻¹ (S z) - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] (e z : L))) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hR : ∀ z α, coefficients (dualAdjoint B (R z) - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] (e z : L))) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hbracket : ∀ z α, ⁅coefficients (A⁻¹ * P * B⁻¹).coord α, (1 : ℝ) ⊗ₜ[ℚ] (e z : L)⁆ ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hAbound : CoefficientBound (b.baseChange ℝ) T (Real.exp p) A.coord)
    (hBgrid : CoefficientGrid (b.baseChange ℝ) m B.coord)
    (hSbound : ∀ z, CoefficientBound (b.baseChange ℝ) T (Real.exp p) (dualAdjoint A⁻¹ (S z)))
    (hRgrid : ∀ z, CoefficientGrid (b.baseChange ℝ) m (dualAdjoint B (R z)))
    (hsmallBound : ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp p / T i)
      (dualAdjoint A⁻¹ (small i - formalLogDerivative i A)))
    (hrationalGrid : ∀ i, CoefficientGrid (b.baseChange ℝ) m
      (dualAdjoint B (rational i) - formalLogDerivative i B))
    (hSshift : ∀ z, dualAdjoint A⁻¹ (S z) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hRshift : ∀ z, dualAdjoint B (R z) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hsmallShift : ∀ i, dualAdjoint A⁻¹ (small i - formalLogDerivative i A) ∈
      shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hrationalShift : ∀ i, dualAdjoint B (rational i) - formalLogDerivative i B ∈
      shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) :
    let S₀ := basisPolynomialLift (Pi.basisFun ℝ κ) S
    let R₀ := basisPolynomialLift (Pi.basisFun ℝ κ) R
    let S' := (dualAdjointAddEquiv A⁻¹).toAddMonoidHom.comp S₀.toAddMonoidHom
    let R' := (dualAdjointAddEquiv B).toAddMonoidHom.comp R₀.toAddMonoidHom
    ∃ (a c : σ → κ → ℝ) (n : ℕ),
      0 < n ∧ (n : ℝ) ≤ Real.exp (bracketTransitionBudget p) ∧
      let P' := A⁻¹ * P * B⁻¹
      let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A) + if j = 2 then S' (a i) else 0
      let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B + if j = 2 then R' (c i) else 0
      let k' := fun i => if j = 2 then k i - a i - c i else k i
      let extra' := fun i => S' (k' i)
      (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P'.coord α) ∈ K.baseChange ℝ) ∧
        (∀ α d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) ∈ V) ∧
        PolynomialLiftSystemMod (V.restrictScalars ℚ) P' S' R' ∧
        PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P' small' rational' extra' ∧
        (∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer j).toSubmodule ∧
          coefficients (rational' i) α ∈ V ⊔ (F.realLayer j).toSubmodule) ∧
        (∀ i α, coefficients (extra' i - VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
            V ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ i α, coefficients
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
            (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P'.coord) -
            VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small' i) -
            VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational' i)) α ∈ V) ∧
        (∀ α x, x ∈ K.baseChange ℝ → ⁅coefficients P'.coord α, x⁆ ∈
          V ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp (bracketTransitionBudget p) / T i) (small' i) ∧
          CoefficientGrid (b.baseChange ℝ) n (rational' i) ∧
          small' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          rational' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) ∧
        ∀ z, CoefficientBound (b.baseChange ℝ) T (Real.exp (bracketTransitionBudget p)) (dualAdjoint A⁻¹ (S z)) ∧
          CoefficientGrid (b.baseChange ℝ) n (dualAdjoint B (R z)) := by
  classical
  intro S₀ R₀ S' R'
  let I := bracketSystemLift e
  have hchoice : ∃ (a c : σ → κ → ℝ) (d : ℕ), 0 < d ∧
      (d : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      (j = 2 → ∀ i, I (a i) = coefficients A.coord (Finsupp.single i 1) ∧
        I (c i) = coefficients B.coord (Finsupp.single i 1)) ∧
      ∀ i, ‖a i‖ ≤ Real.exp ((p + 2) ^ 8) / T i ∧ c i ∈ realDenominatorGrid d := by
    by_cases hj2 : j = 2
    · obtain ⟨a, c, d, hd, hdp, hdirs⟩ := exists_uniform_polynomial_kernel_directions b e hH hm he hp
        (Real.exp_nonneg p) hambient hkernel hHp hmp le_rfl A.coord B.coord (hAK hj2) (hBK hj2)
        T hT hAbound hBgrid
      exact ⟨a, c, d, hd, hdp, fun _ i => ⟨(hdirs i).1, (hdirs i).2.1⟩,
        fun i => ⟨(hdirs i).2.2.1, (hdirs i).2.2.2⟩⟩
    · refine ⟨0, 0, 1, by decide, ?_, fun h => (hj2 h).elim, fun i => ?_⟩
      · simpa only [Nat.cast_one] using Real.one_le_exp (by positivity : 0 ≤ (p + 2) ^ 9)
      · constructor
        · simp only [Pi.zero_apply, norm_zero]
          exact div_nonneg (Real.exp_nonneg _) (hT i).le
        · exact ⟨0, by ext z; simp⟩
  obtain ⟨a, c, d, hd, hdp, hdirs, hcoordinates⟩ := hchoice
  let n := m * (m * d)
  have hn : 0 < n := Nat.mul_pos hm (Nat.mul_pos hm hd)
  have hmdiv : m ∣ n := dvd_mul_right m (m * d)
  obtain ⟨hbase, habsorb, hnbound⟩ := bracket_transition_budget_bounds hp (Fintype.card κ) m d hkernel hmp hdp
  refine ⟨a, c, n, hn, hnbound, ?_⟩
  intro P' small' rational' k' extra'
  have hI : ∀ x, basisGradeProjection (b.baseChange ℝ) w 1 (I x) = I x :=
    fun x => hK _ (bracketSystemLift_mem e x)
  have hSR₀ : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S₀ R₀ :=
    hSR.extend_basis (Pi.basisFun ℝ κ) V P S R
  have hSall : ∀ x α, coefficients (dualAdjoint A⁻¹ (S₀ x) - monomial 0 (I x)) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    apply basisPolynomialLift_adjoint_residual (Pi.basisFun ℝ κ) A⁻¹ S I
      (V ⊔ (F.realLayer (j + 1)).toSubmodule)
    intro z α
    simpa only [I, Pi.basisFun_apply, bracketSystemLift_single] using hS z α
  have hRall : ∀ x α, coefficients (dualAdjoint B (R₀ x) - monomial 0 (I x)) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    apply basisPolynomialLift_adjoint_residual (Pi.basisFun ℝ κ) B R I
      (V ⊔ (F.realLayer (j + 1)).toSubmodule)
    intro z α
    simpa only [I, Pi.basisFun_apply, bracketSystemLift_single] using hR z α
  have hbracketall : ∀ α x, x ∈ K.baseChange ℝ → ⁅coefficients P'.coord α, x⁆ ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    intro α x hx
    obtain ⟨v, rfl⟩ := exists_subspace_basis_coordinates e x hx
    apply real_bracket_mem_of_basis (Pi.basisFun ℝ κ) I
      (V ⊔ (F.realLayer (j + 1)).toSubmodule) (coefficients P'.coord α) _ v
    intro z
    simpa only [I, Pi.basisFun_apply, bracketSystemLift_single] using hbracket z α
  have hgeometry := F.formal_bracket_to_current_layer b w hF hs U V (K.baseChange ℝ) hUV hV
    I.toAddMonoidHom hI hj P A B hPU hAU hBU hA hB hAhom hBhom hAK hBK hAV hBV hPK hlower
    S₀.toAddMonoidHom R₀.toAddMonoidHom small rational k a c
    (fun h i => (hdirs h i).1) (fun h i => (hdirs h i).2)
    hSR₀ hsystem hsmall hrational hSall hRall hbracketall
  refine ⟨hgeometry.1, hgeometry.2.1, hgeometry.2.2.1, hgeometry.2.2.2.1,
    hgeometry.2.2.2.2.1, hgeometry.2.2.2.2.2.1, hgeometry.2.2.2.2.2.2.1,
    hgeometry.2.2.2.2.2.2.2, hbracketall, ?_, ?_⟩
  · intro i
    by_cases hj2 : j = 2
    · have ha : ‖(Pi.basisFun ℝ κ).equivFun (a i)‖ ≤ Real.exp ((p + 2) ^ 8) / T i := by
        rw [Pi.basisFun_equivFun]
        exact (hcoordinates i).1
      have hc : (Pi.basisFun ℝ κ).equivFun (c i) ∈ realDenominatorGrid d := by
        rw [Pi.basisFun_equivFun]
        exact (hcoordinates i).2
      have hbound := basisPolynomialLift_reabsorption_bound (Pi.basisFun ℝ κ)
        (fun z => dualAdjoint A⁻¹ (S z)) (b.baseChange ℝ) T hT (Real.exp p) (Real.exp p)
        (Real.exp ((p + 2) ^ 8)) (T i) (Real.exp_nonneg p) hSbound _ (hsmallBound i) (a i) ha
      have hgrid := basisPolynomialLift_reabsorption_grid (Pi.basisFun ℝ κ)
        (fun z => dualAdjoint B (R z)) (b.baseChange ℝ) d m m hRgrid _ (hrationalGrid i) (c i) hc
      have hSsh := basisPolynomialLift_shiftedGraded (Pi.basisFun ℝ κ)
        (fun z => dualAdjoint A⁻¹ (S z)) (b.baseChange ℝ) w (fun _ : σ => 1) 1 hSshift (a i)
      have hRsh := basisPolynomialLift_shiftedGraded (Pi.basisFun ℝ κ)
        (fun z => dualAdjoint B (R z)) (b.baseChange ℝ) w (fun _ : σ => 1) 1 hRshift (c i)
      rw [basisPolynomialLift_adjoint (hnil := F.realification.lowerCentralSeries_eq_bot)
        (Pi.basisFun ℝ κ) A⁻¹ S] at hbound hSsh
      rw [basisPolynomialLift_adjoint (hnil := F.realification.lowerCentralSeries_eq_bot)
        (Pi.basisFun ℝ κ) B R] at hgrid hRsh
      simp only [small', rational', if_pos hj2]
      exact ⟨hbound.mono _ T hT (div_le_div_of_nonneg_right habsorb (hT i).le), hgrid,
        (shiftedGradedPolynomialSubmodule _ _ _ _).add_mem (hsmallShift i) hSsh,
        (shiftedGradedPolynomialSubmodule _ _ _ _).add_mem (hrationalShift i) hRsh⟩
    · simp only [small', rational', if_neg hj2, add_zero]
      exact ⟨(hsmallBound i).mono _ T hT (div_le_div_of_nonneg_right hbase (hT i).le),
        fun α => realDenominatorGrid_subset_of_dvd hm hmdiv (hrationalGrid i α),
        hsmallShift i, hrationalShift i⟩
  · intro z
    exact ⟨(hSbound z).mono _ T hT hbase,
      fun α => realDenominatorGrid_subset_of_dvd hm hmdiv (hRgrid z α)⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FormalStageBudget
namespace OAI

section

namespace Erdos3

theorem bracketTransitionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ bracketTransitionBudget p := by unfold bracketTransitionBudget; positivity

theorem le_bracketTransitionBudget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ bracketTransitionBudget p := by
  have h8 : 0 ≤ (p + 2) ^ 8 := by positivity
  have h9 : 0 ≤ (p + 2) ^ 9 := by positivity
  unfold bracketTransitionBudget
  linarith

theorem exists_formal_stage_budget (D E : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let d := (p + D) ^ D
      let u := bracketTransitionBudget (p + d)
      let q := u + bracketConstructionBudget u
      d + (q + E) ^ E + 1 ≤ (p + C) ^ C := by
  let Pd : Polynomial ℕ := (Polynomial.X + Polynomial.C D) ^ D
  let Pt : Polynomial ℕ := Polynomial.X + Pd
  let Pu : Polynomial ℕ := 4 * Pt + (Pt + 2) ^ 8 + (Pt + 2) ^ 9 + 1
  let Pq : Polynomial ℕ := Pu + ((Pu + 2) ^ 3 + 3 * Pu + 2)
  let P : Polynomial ℕ := Pd + (Pq + Polynomial.C E) ^ E + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, Pd, Pt, Pu, Pq, bracketTransitionBudget, bracketConstructionBudget,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformControlledCurrentStage
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_derivative_removal_control (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
      BasisHomogeneousBrackets b ω →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
      A.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) →
      B.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) →
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) A.coord →
      CoefficientGrid (b.baseChange ℝ) l B.coord →
      ∀ {κ : Type*} (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
        (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      (∀ k, S k ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1) →
      (∀ k, R k ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1) →
      (∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1) →
      (∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1) →
      (∀ k, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) (S k)) →
      (∀ k, CoefficientGrid (b.baseChange ℝ) l (R k)) →
      (∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a) / T i) (small i)) →
      (∀ i, CoefficientGrid (b.baseChange ℝ) l (rational i)) →
      (∀ k, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) (dualAdjoint A⁻¹ (S k)) ∧
        CoefficientGrid (b.baseChange ℝ) m (dualAdjoint B (R k))) ∧
      (∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C) / T i)
          (dualAdjoint A⁻¹ (small i - formalLogDerivative i A)) ∧
        CoefficientGrid (b.baseChange ℝ) m (dualAdjoint B (rational i) - formalLogDerivative i B)) ∧
      (∀ k, dualAdjoint A⁻¹ (S k) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1 ∧
        dualAdjoint B (R k) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1) ∧
      ∀ i, dualAdjoint A⁻¹ (small i - formalLogDerivative i A) ∈
          shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1 ∧
        dualAdjoint B (rational i) - formalLogDerivative i B ∈
          shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1 := by
  obtain ⟨D, _, hbound⟩ := exists_formal_polynomial_operation_bound s a
  obtain ⟨E, _, hgrid⟩ := exists_formal_polynomial_operation_grid s
  let P : Polynomial ℕ := 2 * (Polynomial.X + Polynomial.C D) ^ D +
    (Polynomial.X + 2) ^ a + (Polynomial.X + Polynomial.C E) ^ E + Polynomial.C (s + 2)
  obtain ⟨C, hC, hCbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF hgraded H p hH hp hι hσ hHp hc l hl hlp
  have hbig : 2 * (p + D) ^ D + (p + 2) ^ a + (p + E) ^ E + (s + 2 : ℝ) ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hCbound p hp
  let d := (p + D) ^ D
  let n := (p + 2) ^ a
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have he : 0 ≤ (p + E) ^ E := by positivity
  have hgridCap : (p + E) ^ E ≤ (p + C) ^ C := by
    have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
    change 2 * d + n + (p + E) ^ E + (s + 2 : ℝ) ≤ _ at hbig
    linarith
  have hliftCap : d + n ≤ (p + C) ^ C := by
    have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
    change 2 * d + n + (p + E) ^ E + (s + 2 : ℝ) ≤ _ at hbig
    linarith
  have hremCap : 2 * d + n + (s + 1 : ℝ) ≤ (p + C) ^ C := by
    change 2 * d + n + (p + E) ^ E + (s + 2 : ℝ) ≤ _ at hbig
    linarith
  have hslowCap : Real.exp d * (Real.exp n + Real.exp d * ((s : ℝ) * Real.exp n)) ≤
      Real.exp ((p + C) ^ C) := by
    have h1 : 1 ≤ Real.exp d := Real.one_le_exp hd
    calc
      _ = Real.exp d * Real.exp n * (1 + Real.exp d * s) := by ring
      _ ≤ Real.exp d * Real.exp n * (Real.exp d * (1 + s)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      _ = (Real.exp d * Real.exp d * Real.exp n) * (s + 1) := by ring
      _ ≤ (Real.exp d * Real.exp d * Real.exp n) * Real.exp (s + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (s + 1 : ℝ)]) (by positivity)
      _ = Real.exp (2 * d + n + (s + 1 : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hremCap
  obtain ⟨m, hm, hmp, hlm, hlogGrid, hadGrid⟩ := hgrid F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hgridCap), hlm, ?_⟩
  intro T hT A B hA hB hAbound hBgrid κ S R small rational hS hR hsmall hrational hSbound hRgrid hsmallBound hrationalGrid
  have hg := hgraded.baseChange b ω
  have hAi : A⁻¹.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ : σ => 1) :=
    (gradedPolynomialSubmodule (b.baseChange ℝ) ω _).neg_mem hA
  have hAa := F.gradedPolynomial_mem_adapted b ω hF (fun _ : σ => 1) A.coord hA
  have hAia := F.gradedPolynomial_mem_adapted b ω hF (fun _ : σ => 1) A⁻¹.coord hAi
  have hBa := F.gradedPolynomial_mem_adapted b ω hF (fun _ : σ => 1) B.coord hB
  have hAib : CoefficientBound (b.baseChange ℝ) T (Real.exp n) A⁻¹.coord :=
    CoefficientBound.neg _ _ hAbound
  have hoperations := hbound F b ω hF H p hH hp hι hσ hHp hc T hT
  have hYA (i : σ) := formalLogDerivative_mem_shiftedGradedPolynomialSubmodule
    (b.baseChange ℝ) ω hg i A hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    have hslow := hoperations.1 A⁻¹ hAia hAib (Real.exp n) (Real.exp_nonneg _) (S k)
      (F.shiftedGradedPolynomial_mem_adapted b ω hF _ 1 _ (hS k)) (hSbound k)
    have hfactor : Real.exp d * Real.exp n ≤ Real.exp ((p + C) ^ C) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hliftCap
    exact ⟨CoefficientBound.mono _ T hT hslow hfactor,
      hadGrid B (R k) hBa (F.shiftedGradedPolynomial_mem_adapted b ω hF _ 1 _ (hR k)) hBgrid (hRgrid k)⟩
  · intro i
    have hyBound := hoperations.2 A hAa hAbound i
    have hdiff := CoefficientBound.sub (b.baseChange ℝ) T (hsmallBound i) hyBound
    have hdiffGrade := (shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ : σ => 1) 1).sub_mem
      (hsmall i) (hYA i)
    have hslow := hoperations.1 A⁻¹ hAia hAib
      (Real.exp n / T i + Real.exp d * ((s : ℝ) * Real.exp n / T i)) (by have hTi := hT i; positivity)
      (small i - formalLogDerivative i A)
      (F.shiftedGradedPolynomial_mem_adapted b ω hF _ 1 _ hdiffGrade) hdiff
    have hfactor : Real.exp d * (Real.exp n / T i + Real.exp d * ((s : ℝ) * Real.exp n / T i)) ≤
        Real.exp ((p + C) ^ C) / T i := by
      calc
        _ = (Real.exp d * (Real.exp n + Real.exp d * ((s : ℝ) * Real.exp n))) / T i := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hslowCap (hT i).le
    exact ⟨CoefficientBound.mono _ T hT hslow hfactor,
      CoefficientGrid.sub _ m
        (hadGrid B (rational i) hBa (F.shiftedGradedPolynomial_mem_adapted b ω hF _ 1 _ (hrational i))
          hBgrid (hrationalGrid i)) (hlogGrid B hBa hBgrid i)⟩
  · intro k
    exact ⟨dualAdjoint_mem_shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω hg _ 1 A⁻¹ (S k) hAi (hS k),
      dualAdjoint_mem_shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω hg _ 1 B (R k) hB (hR k)⟩
  · intro i
    exact polynomial_derivative_removal_preserves_shifted_grading (b.baseChange ℝ) ω hg i A B
      (small i) (rational i) hA hB (hsmall i) (hrational i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_controlled_current_stage (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype ν] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    {E V : Submodule ℚ L}
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    {j H J Q l : ℕ} (_hj : 2 ≤ j)
    (_hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (_hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (_hH : 1 ≤ H) (_hl : 0 < l)
    (_hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (_he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (_hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    (_hstructure : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    {p M : ℝ} (_hp : 0 ≤ p) (_hM : 0 ≤ M)
    (_hambient : (Fintype.card μ : ℝ) ≤ p) (_hrows : (Fintype.card ι : ℝ) ≤ p)
    (_hcols : (Fintype.card ν : ℝ) ≤ p) (_hvariables : (Fintype.card σ : ℝ) ≤ p)
    (_hjp : (j : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hJp : (J : ℝ) ≤ Real.exp p) (_hQp : (Q : ℝ) ≤ Real.exp p)
    (_hlp : (l : ℝ) ≤ Real.exp p) (_hMp : M ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (_hPU : ∀ α, coefficients P.coord α ∈ U)
    (_hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (_hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients P.coord α) ∈ E.baseChange ℝ)
    (_hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (_hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V.baseChange ℝ)
    (_hbracket : ∀ α k, k ∈ K →
      ⁅coefficients P.coord α, k⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (_hsmall : ∀ i α, coefficients (small i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hrational : ∀ i α, coefficients (rational i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (_hsystem : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P small rational extra)
    (_hSgraded : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hRgraded : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hslow : ∀ i α, ‖realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i)) α)‖ ≤
        M / (T i * monomialScale T α))
    (_hgrid : ∀ i α, realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α) ∈
        realDenominatorGrid l)
    {κ : Type*} (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : κ → ℝ ⊗[ℚ] L)
    (_hS : ∀ t, S t ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1) 1)
    (_hR : ∀ t, R t ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1) 1)
    (_hSR : PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P S R)
    (_hSres : ∀ t α, coefficients (S t - monomial 0 (k t)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (_hRres : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (_hSbound : ∀ t, CoefficientBound (b.baseChange ℝ) T (Real.exp p) (S t))
    (_hRgrid : ∀ t, CoefficientGrid (b.baseChange ℝ) l (R t))
    (_hsmallBound : ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp p / T i) (small i))
    (_hrationalGrid : ∀ i, CoefficientGrid (b.baseChange ℝ) l (rational i)),
    ∃ (n : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        Real.exp ((p + C) ^ C) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈
        realDenominatorGrid n) ∧
      let P' := A⁻¹ * P * B⁻¹
      let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
      let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
      let extra' := fun i => dualAdjoint A⁻¹ (extra i)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ α, coefficients (VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P'.coord) α ∈ (E ⊓ V).baseChange ℝ) ∧
        (∀ d < j, VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' small' rational' extra' ∧
        (∀ i, small' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          rational' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) ∧
        (∀ i α, coefficients (small' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (rational' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P'.coord α) ∈ K) ∧
        (∀ α d, 2 ≤ d → d < j + 1 →
          basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) ∈ V.baseChange ℝ) ∧
        (∀ α k, k ∈ K → ⁅coefficients P'.coord α, k⁆ ∈
          V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ i α, coefficients (extra' i - VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
            V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P'
          (fun t => dualAdjoint A⁻¹ (S t)) (fun t => dualAdjoint B (R t)) ∧
        (∀ t α, coefficients (dualAdjoint A⁻¹ (S t) - monomial 0 (k t)) α ∈
            V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (dualAdjoint B (R t) - monomial 0 (k t)) α ∈
            V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ t, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) (dualAdjoint A⁻¹ (S t)) ∧
          CoefficientGrid (b.baseChange ℝ) n (dualAdjoint B (R t)) ∧
          dualAdjoint A⁻¹ (S t) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1) 1 ∧
          dualAdjoint B (R t) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1) 1) ∧
        ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C) / T i) (small' i) ∧
          CoefficientGrid (b.baseChange ℝ) n (rational' i) := by
  obtain ⟨D, _, hstage⟩ := exists_uniform_formal_current_layer_step
  obtain ⟨E, _, hremove⟩ := exists_formal_derivative_removal_control s 1
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C D) ^ D
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C D) ^ D + (Q + Polynomial.C E) ^ E + 1
  obtain ⟨C, hC, hCbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro L μ ι ν σ _ _ _ _ _ _ F b w hF Vsource V hgraded hs U K hUV hV e f j H J Qheight l
    hj hE hEU hH hl hA he hf hstructure p M hp hM hambient hrows hcols hvariables hjp
    hHp hJp hQp hlp hMp T hT P hPU hPgraded hPE hK hlower hbracket small rational extra
    hsmall hrational hextra hsystem hSgraded hRgraded hslow hgrid κ S R k hS hR hSR hSres hRres
    hSbound hRgrid hsmallBound hrationalGrid
  let d := (p + D) ^ D
  let q := p + d
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hqE : 0 ≤ (q + E) ^ E := by positivity
  have htotal : d + (q + E) ^ E + 1 ≤ (p + C) ^ C := by
    simpa [B, Q, q, d, Polynomial.eval₂_pow] using hCbound p hp
  have hdCap : d ≤ (p + C) ^ C := by linarith
  have hremCap : (q + E) ^ E ≤ (p + C) ^ C := by linarith
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hTD : ∀ i, Real.exp ((p + D) ^ D) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hdCap).trans (hT i)
  obtain ⟨n₀, A, Bcorr, hn₀, hn₀bound, hAB, hAhom, hBhom, hAnorm, hBgrid,
    hprod, hconstant, hnewgraded, hnewU, hnewV, hbelow, hnewsystem, hnewshift,
    hnewderivative, hnewK, hnewlower, hnewbracket, hnewextra⟩ :=
    hstage F b w hF hgraded hs U K hUV hV e f hj hE hEU hH hl hA he hf hp hM
      hambient hrows hcols hvariables hjp hHp hJp hQp hlp hMp T hTD
      P hPU hPgraded hPE hK hlower hbracket small rational extra hsmall hrational hextra
      hsystem hSgraded hRgraded hslow hgrid
  let Lden := l * n₀
  have hLden : 0 < Lden := Nat.mul_pos hl hn₀
  have hLbound : (Lden : ℝ) ≤ Real.exp q := by
    calc
      _ = (l : ℝ) * (n₀ : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp p * Real.exp d := mul_le_mul hlp hn₀bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp q := (Real.exp_add _ _).symm
  obtain ⟨m, hm, hmbound, hLm, hcontrol⟩ := hremove F b w hF hgraded H q hH hq
    (hambient.trans hpq) (hvariables.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq))
    hstructure Lden hLden hLbound
  have hlL : l ∣ Lden := dvd_mul_right l n₀
  have hnL : n₀ ∣ Lden := dvd_mul_left n₀ l
  have hAg := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    j A.coord hAhom (fun α => hE _ (hAB α).1)
  have hBg := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    j Bcorr.coord hBhom (fun α => hE _ (hAB α).2)
  have hAraw : CoefficientBound (b.baseChange ℝ) T (Real.exp d) A.coord :=
    (coefficientBound_iff_norm _ T hTpos (Real.exp_nonneg _) A.coord).mpr hAnorm
  have hAinput : CoefficientBound (b.baseChange ℝ) T (Real.exp ((q + 2) ^ 1)) A.coord := by
    apply CoefficientBound.mono _ T hTpos hAraw
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    dsimp [q]
    linarith
  have hBinput : CoefficientGrid (b.baseChange ℝ) Lden Bcorr.coord :=
    fun α => realDenominatorGrid_subset_of_dvd hn₀ hnL (hBgrid α)
  have hinputCap : Real.exp p ≤ Real.exp ((q + 2) ^ 1) := by
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    linarith
  obtain ⟨hboundLifts, hboundDerivative, hshiftLifts, _⟩ := hcontrol T hTpos A Bcorr hAg hBg hAinput hBinput
    S R small rational hS hR hSgraded hRgraded
    (fun t => CoefficientBound.mono _ T hTpos (hSbound t) hinputCap)
    (fun t α => realDenominatorGrid_subset_of_dvd hl hlL (hRgrid t α))
    (fun i => CoefficientBound.mono _ T hTpos (hsmallBound i)
      (div_le_div_of_nonneg_right hinputCap (hTpos i).le))
    (fun i α => realDenominatorGrid_subset_of_dvd hl hlL (hrationalGrid i α))
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  have hAlayer : ∀ α, coefficients A.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hE _ (hAB α).1]
    exact F.realGradeProjection_mem_layer b w hF j _
  have hBlayer : ∀ α, coefficients Bcorr.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hE _ (hAB α).2]
    exact F.realGradeProjection_mem_layer b w hF j _
  have hWiff (x : ℝ ⊗[ℚ] L) :
      x ∈ (V.baseChange ℝ).restrictScalars ℚ ⊔ F.realification.layer (j + 1) ↔
        x ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
    change x ∈ (V.baseChange ℝ).restrictScalars ℚ ⊔
      (F.realLayer (j + 1)).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have hkeep := F.formal_current_layer_correction_preserves_lifts_mod hs Uq
    ((V.baseChange ℝ).restrictScalars ℚ) hUV j P A Bcorr
    (fun α => hEU _ (hAB α).1) hAlayer hBlayer S R k hSR
    (fun t α => (hWiff _).mpr (hSres t α)) (fun t α => (hWiff _).mpr (hRres t α))
  have hfinalCap : Real.exp ((q + E) ^ E) ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hremCap
  refine ⟨m, A, Bcorr, hm, hmbound.trans hfinalCap, hAB, hAhom, hBhom, ?_, ?_,
    hprod, hconstant, hnewgraded, hnewU, hnewV, hbelow, hnewsystem, hnewshift,
    hnewderivative, hnewK, hnewlower, hnewbracket, hnewextra, hkeep.1, ?_, ?_, ?_⟩
  · intro α
    exact (hAnorm α).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hdCap)
      (monomialScale_pos T hTpos α).le)
  · intro α
    exact realDenominatorGrid_subset_of_dvd hn₀ (dvd_trans hnL hLm) (hBgrid α)
  · intro t α
    exact ⟨(hWiff _).mp (hkeep.2 t α).1, (hWiff _).mp (hkeep.2 t α).2⟩
  · intro t
    exact ⟨CoefficientBound.mono _ T hTpos (hboundLifts t).1 hfinalCap,
      (hboundLifts t).2, (hshiftLifts t).1, (hshiftLifts t).2⟩
  · intro i
    exact ⟨CoefficientBound.mono _ T hTpos (hboundDerivative i).1
      (div_le_div_of_nonneg_right hfinalCap (hTpos i).le), (hboundDerivative i).2⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end


