-- Prove2me | Definitions.Def_OAIE3v2B053
-- name    : OAIE3v2B053
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:13:01.336252+00:00
-- url     : https://prove2.me/theorems/6af2067b-71d0-454f-8e8a-57e7b9aaee66
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 54 of 311
-- statement:
--   Definitions bundle 54 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B004`, `OAIE3v2B009`, `OAIE3v2B010`, `OAIE3v2B018`, `OAIE3v2B019`, `OAIE3v2B021`, `OAIE3v2B022`, `OAIE3v2B023` of this split.
--
--   Modules: `Dynamics/CommonInitialBudget.lean`, `Dynamics/CommonTerminalBudget.lean`, `Dynamics/FastCoefficientDimensionBudget.lean`, `Dynamics/FastTerminalBudget.lean`, `Dynamics/SynchronizedCorrectionBudget.lean`, `Dynamics/TerminalCompositionBudget.lean`, `Estimates/CyclicCutNeighborhood.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/PositiveCyclicCorrelation.lean`, `Estimates/SplitGroupRelative.lean`, `Estimates/StepDropTerminalContainment.lean`, `Geometry/HorizontalCoordinateBounds.lean`, `Geometry/RealFastCoefficientCoordinates.lean`, `Geometry/RealSubspaceCoordinateRetraction.lean`, `Lattices/NativeRetainedIntegerMultilinearQuadruples.lean`, `Linear/CoordinateProjectionBounds.lean`, `Nilpotent/FilteredAdjointFirstBracket.lean`, `Nilpotent/SquarefreeBracketHeight.lean`, `Polynomial/AffinePhaseBias.lean`, `Polynomial/SubspacePolynomialCoordinates.lean`, `Polynomial/VectorPolynomialReconstruction.lean`, `Sampling/RationalSpanGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B003
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B009
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B018
import Definitions.Def_OAIE3v2B019
import Definitions.Def_OAIE3v2B021
import Definitions.Def_OAIE3v2B022
import Definitions.Def_OAIE3v2B023

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CommonInitialBudget
namespace OAI

section

namespace Erdos3

theorem commonExtractionParameter_products {p C M : ℝ} (hp : 0 ≤ p)
    (_hC : 0 ≤ C) (hCp : C ≤ Real.exp p) (hM : 0 ≤ M) (hMp : M ≤ Real.exp p)
    (δ l : ℕ) (hδ : (δ : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    max 2 (C * (M + M)) ≤ Real.exp (commonExtractionParameter p) ∧
      ((δ * l : ℕ) : ℝ) ≤ Real.exp (commonExtractionParameter p) := by
  have hq := commonExtractionParameter_controls hp
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  constructor
  · apply max_le (htwo.trans (Real.exp_le_exp.mpr hq.2.2.1))
    calc
      _ ≤ Real.exp p * (Real.exp p + Real.exp p) :=
        mul_le_mul hCp (add_le_add hMp hMp) (add_nonneg hM hM) (Real.exp_nonneg _)
      _ = 2 * (Real.exp p * Real.exp p) := by ring
      _ ≤ Real.exp 1 * (Real.exp p * Real.exp p) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = Real.exp (1 + (p + p)) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold commonExtractionParameter; linarith)
  · rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hδ hl (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hq.2.1

theorem exists_commonInitialParameter_budget (C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      commonInitialParameter p + 1 ≤ (p + D) ^ D ∧
      (commonInitialParameter p + 2) ^ 3 ≤ (p + D) ^ D ∧
      (commonInitialParameter p + C) ^ C ≤ (p + D) ^ D := by
  let Q : Polynomial ℕ := (3 * Polynomial.X + 3 + 2) ^ 3
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + 1 + (Q + 2) ^ 3 + (Q + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  have hq : 0 ≤ commonInitialParameter p :=
    (hp.trans (commonExtractionParameter_controls hp).1).trans
      (commonExtractionParameter_controls hp).2.2.2
  have h2 : 0 ≤ (commonInitialParameter p + 2) ^ 3 := by positivity
  have hC : 0 ≤ (commonInitialParameter p + C) ^ C := by positivity
  have hsum : commonInitialParameter p + 1 + (commonInitialParameter p + 2) ^ 3 +
      (commonInitialParameter p + C) ^ C ≤ (p + D) ^ D := by
    simpa [Q, commonInitialParameter, commonExtractionParameter, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CommonTerminalBudget
namespace OAI

section

namespace Erdos3

theorem fullInitialParameter_controls (s C : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ fullInitialParameter s C p ∧
      p * (s + 2) * (p + 1) ^ (s + 1) ≤ fullInitialParameter s C p ∧
      (p + C) ^ C ≤ fullInitialParameter s C p := by
  have hdim : 0 ≤ p * (s + 2) * (p + 1) ^ (s + 1) := by positivity
  have hC : 0 ≤ (p + C) ^ C := by positivity
  unfold fullInitialParameter
  exact ⟨by linarith, by linarith, by linarith⟩

theorem exists_fullInitialParameter_budget (s c C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      (fullInitialParameter s c p + C) ^ C ≤ (p + D) ^ D := by
  let Q : Polynomial ℕ := Polynomial.X + Polynomial.X * Polynomial.C (s + 2) *
    (Polynomial.X + 1) ^ (s + 1) + (Polynomial.X + Polynomial.C c) ^ c + 2
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  simpa [Q, fullInitialParameter, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

section

namespace Erdos3

def commonTerminalParameter (s c : ℕ) (p : ℝ) : ℝ := fullInitialParameter s c p + (s + 1)

theorem commonTerminalParameter_controls (s c : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ commonTerminalParameter s c p ∧
      p * (s + 2) * (p + 1) ^ (s + 1) ≤ commonTerminalParameter s c p ∧
      (p + c) ^ c ≤ commonTerminalParameter s c p ∧
      (s + 1 : ℕ) ≤ commonTerminalParameter s c p := by
  have h := fullInitialParameter_controls s c hp
  have hle : fullInitialParameter s c p ≤ commonTerminalParameter s c p :=
    le_add_of_nonneg_right (by positivity)
  refine ⟨h.1.trans hle, h.2.1.trans hle, h.2.2.trans hle, ?_⟩
  have hnonneg : 0 ≤ fullInitialParameter s c p := hp.trans h.1
  simpa only [commonTerminalParameter, Nat.cast_add, Nat.cast_one] using
    (le_add_of_nonneg_left hnonneg : ((s : ℝ) + 1) ≤ fullInitialParameter s c p + ((s : ℝ) + 1))

theorem exists_commonTerminalParameter_budget (s c C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      commonTerminalParameter s c p ≤ (p + D) ^ D ∧
      (commonTerminalParameter s c p + C) ^ C ≤ (p + D) ^ D := by
  let Q : Polynomial ℕ := Polynomial.X + Polynomial.X * Polynomial.C (s + 2) *
    (Polynomial.X + 1) ^ (s + 1) + (Polynomial.X + Polynomial.C c) ^ c + 2 + Polynomial.C (s + 1)
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  have hq : 0 ≤ commonTerminalParameter s c p := hp.trans (commonTerminalParameter_controls s c hp).1
  have hpow : 0 ≤ (commonTerminalParameter s c p + C) ^ C := by positivity
  have hsum : commonTerminalParameter s c p + (commonTerminalParameter s c p + C) ^ C ≤ (p + D) ^ D := by
    simpa [Q, commonTerminalParameter, fullInitialParameter, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V]

theorem coefficients_multiplyVariable [DecidableEq σ] (i : σ)
    (P : VectorPolynomial σ ℚ V) (β : σ →₀ ℕ) :
    coefficients (multiplyVariable i P) β =
      if i ∈ β.support then coefficients P (β - Finsupp.single i 1) else 0 := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | tmul p v =>
    rw [multiplyVariable_tmul, coefficients_tmul, MvPolynomial.coeff_X_mul', coefficients_tmul]
    split_ifs <;> simp
  | add P Q hP hQ =>
    simp only [map_add, Finsupp.add_apply, hP, hQ]
    split_ifs <;> simp

noncomputable def eulerSum [Fintype σ] :
    VectorPolynomial σ ℚ V →ₗ[ℚ] VectorPolynomial σ ℚ V :=
  ∑ i, (multiplyVariable i).comp ((MvPolynomial.pderiv i).toLinearMap.rTensor V)

theorem eulerSum_monomial [Fintype σ] (β : σ →₀ ℕ) (v : V) :
    eulerSum (monomial (R := ℚ) β v) =
      (Finsupp.weight (fun _ : σ => (1 : ℕ)) β : ℚ) • monomial β v := by
  have hdegree : β.degree = Finsupp.weight (fun _ : σ => (1 : ℕ)) β :=
    DFunLike.congr_fun Finsupp.degree_eq_weight_one β
  have h := (MvPolynomial.isHomogeneous_monomial (1 : ℚ) hdegree).sum_X_mul_pderiv
  simp only [eulerSum, LinearMap.sum_apply, LinearMap.comp_apply, monomial,
    LinearMap.rTensor_tmul, multiplyVariable_tmul]
  change (∑ i, (MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.monomial β (1 : ℚ))) ⊗ₜ[ℚ] v) = _
  rw [← TensorProduct.sum_tmul, h]
  simp only [Nat.cast_smul_eq_nsmul, TensorProduct.smul_tmul']

theorem eulerSum_eq_degree_smul [Fintype σ] (d : ℕ) (P : VectorPolynomial σ ℚ V)
    (hP : ∀ β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d → coefficients P β = 0) :
    eulerSum P = (d : ℚ) • P := by
  classical
  conv_lhs => rw [← sum_monomial_coefficients P]
  conv_rhs => rw [← sum_monomial_coefficients P]
  simp only [Finsupp.sum, map_sum, eulerSum_monomial, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  have he : Finsupp.weight (fun _ : σ => (1 : ℕ)) β = d := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hβ) (hP β hn)
  rw [he]

noncomputable def reconstructDerivatives [Fintype σ] (d : ℕ) :
    (σ → VectorPolynomial σ ℚ V) →ₗ[ℚ] VectorPolynomial σ ℚ V :=
  (d : ℚ)⁻¹ • ∑ i, (multiplyVariable i).comp (LinearMap.proj i)

theorem reconstructDerivatives_apply [Fintype σ] (d : ℕ)
    (P : σ → VectorPolynomial σ ℚ V) :
    reconstructDerivatives d P = (d : ℚ)⁻¹ • ∑ i, multiplyVariable i (P i) := by
  simp only [reconstructDerivatives, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

theorem reconstructDerivatives_partial [Fintype σ] {d : ℕ} (hd : 0 < d)
    (P : VectorPolynomial σ ℚ V)
    (hP : ∀ β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d → coefficients P β = 0) :
    reconstructDerivatives d (fun i => (MvPolynomial.pderiv i).toLinearMap.rTensor V P) = P := by
  rw [reconstructDerivatives_apply]
  have he := eulerSum_eq_degree_smul d P hP
  simp only [eulerSum, LinearMap.sum_apply, LinearMap.comp_apply] at he
  rw [he, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd.ne'), one_smul]

theorem coefficients_reconstructDerivatives [Fintype σ] [DecidableEq σ] (d : ℕ)
    (P : σ → VectorPolynomial σ ℚ V) (β : σ →₀ ℕ) :
    coefficients (reconstructDerivatives d P) β =
      (d : ℚ)⁻¹ • ∑ i, if i ∈ β.support then coefficients (P i) (β - Finsupp.single i 1) else 0 := by
  rw [reconstructDerivatives_apply]
  simp only [map_smul, Finsupp.smul_apply, map_sum, Finsupp.finsetSum_apply,
    coefficients_multiplyVariable]

theorem reconstructDerivatives_mem [Fintype σ] (W : Submodule ℚ V) (d : ℕ)
    (P : σ → VectorPolynomial σ ℚ V)
    (hP : ∀ i β, coefficients (P i) β ∈ W) :
    ∀ β, coefficients (reconstructDerivatives d P) β ∈ W := by
  classical
  intro β
  rw [coefficients_reconstructDerivatives]
  apply W.smul_mem
  apply W.sum_mem
  intro i _
  split_ifs
  · exact hP i _
  · exact W.zero_mem

theorem reconstructDerivatives_homogeneous [Fintype σ] {d : ℕ} (hd : 0 < d)
    (P : σ → VectorPolynomial σ ℚ V)
    (hP : ∀ i β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d - 1 → coefficients (P i) β = 0) :
    ∀ β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d →
      coefficients (reconstructDerivatives d P) β = 0 := by
  classical
  intro β hβ
  rw [coefficients_reconstructDerivatives]
  suffices (∑ i, if i ∈ β.support then coefficients (P i) (β - Finsupp.single i 1) else 0) = 0 by
    rw [this, smul_zero]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · apply hP
    have hw := Finsupp.weight_sub_single_add (w := fun _ : σ => (1 : ℕ))
      (Finsupp.mem_support_iff.mp hi)
    omega
  · rfl

theorem homogeneous_derivative_split_mod [Fintype σ] (W : Submodule ℚ V)
    {d : ℕ} (hd : 0 < d) (P : VectorPolynomial σ ℚ V)
    (hP : ∀ β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d → coefficients P β = 0)
    (S R : σ → VectorPolynomial σ ℚ V)
    (hsplit : ∀ i β, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor V P - S i - R i) β ∈ W) :
    ∀ β, coefficients (P - reconstructDerivatives d S - reconstructDerivatives d R) β ∈ W := by
  let D : σ → VectorPolynomial σ ℚ V := fun i => (MvPolynomial.pderiv i).toLinearMap.rTensor V P
  have he : reconstructDerivatives d (D - S - R) =
      P - reconstructDerivatives d S - reconstructDerivatives d R := by
    rw [map_sub, map_sub, reconstructDerivatives_partial hd P hP]
  rw [← he]
  exact reconstructDerivatives_mem W d (D - S - R) hsplit

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

theorem realDenominatorGrid_nat_smul_iff {ι : Type*} (l m : ℕ) (x : ι → ℝ) :
    (l : ℝ) • x ∈ realDenominatorGrid m ↔ x ∈ realDenominatorGrid (m * l) := by
  change (m : ℝ) • ((l : ℝ) • x) ∈ realIntegerGrid ↔ ((m * l : ℕ) : ℝ) • x ∈ realIntegerGrid
  rw [Nat.cast_mul, mul_smul]

theorem linearMap_grid_of_integer {ι κ V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : V →ₗ[ℝ] (ι → ℝ)) (f : V →ₗ[ℝ] (κ → ℝ)) (δ : ℕ)
    (hf : ∀ x, c x ∈ realDenominatorGrid 1 → f x ∈ realDenominatorGrid δ)
    (l : ℕ) (x : V) (hx : c x ∈ realDenominatorGrid l) :
    f x ∈ realDenominatorGrid (δ * l) := by
  have hc : c ((l : ℝ) • x) ∈ realDenominatorGrid 1 := by
    rw [map_smul, realDenominatorGrid_nat_smul_iff, one_mul]
    exact hx
  have h := hf ((l : ℝ) • x) hc
  rw [map_smul, realDenominatorGrid_nat_smul_iff] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem quarter_bounds (N : ℕ) (i : Fin 4) :
    quarterLower N i ≤ quarterUpper N i ∧ quarterUpper N i ≤ N := by
  fin_cases i <;> simp only [quarterLower, quarterUpper] <;> omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffinePhaseBias
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerBox_expect_eq_fin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (f : (ι → ℤ) → ℂ) :
    (𝔼 x ∈ integerBox T, f x) = 𝔼 t : ∀ i, Fin (T i), f (fun i => ((t i : ℕ) : ℤ)) := by
  symm
  apply Finset.expect_bij (fun t _ i => ((t i : ℕ) : ℤ))
  · intro t _
    rw [mem_integerBox]
    exact fun i => ⟨Int.natCast_nonneg _, by exact_mod_cast (t i).isLt⟩
  · intro t _
    rfl
  · intro t _ u _ h
    funext i
    apply Fin.ext
    exact_mod_cast congrFun h i
  · intro x hx
    have hx' := (mem_integerBox T x).mp hx
    let t : ∀ i, Fin (T i) := fun i => ⟨(x i).toNat, by have := hx' i; omega⟩
    refine ⟨t, Finset.mem_univ _, ?_⟩
    funext i
    change ((x i).toNat : ℤ) = x i
    exact Int.toNat_of_nonneg (hx' i).1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SquarefreeBracketHeight
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

variable {L ι κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  {E V : Submodule ℚ L}

theorem bracketSystemMatrix_real_apply [Fintype ν] (e : Basis ν ℚ E)
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) (x : ν → ℝ) :
    (fun bi n => (bracketSystemMatrix e f k bi n : ℝ)) *ᵥ x =
      realBracketSystem f k (bracketSystemLift e x) := by
  classical
  have h : Matrix.mulVecLin (fun bi n => (bracketSystemMatrix e f k bi n : ℝ)) =
      (realBracketSystem f k).comp (bracketSystemLift e) := by
    apply (Pi.basisFun ℝ ν).ext
    intro n
    change (fun bi t => (bracketSystemMatrix e f k bi t : ℝ)) *ᵥ Pi.single n 1 =
      realBracketSystem f k (bracketSystemLift e (Pi.single n 1))
    rw [bracketSystemLift_single]
    change Matrix.of (fun bi t => (bracketSystemMatrix e f k bi t : ℝ)) *ᵥ Pi.single n 1 = _
    rw [Matrix.mulVec_single_one]
    funext bi
    rw [realBracketSystem_apply, LieAlgebra.ExtendScalars.bracket_tmul, one_mul,
      LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
    change (f.repr (V.mkQ ⁅(e n : L), k bi.1⁆) bi.2 : ℝ) =
      (f.repr (V.mkQ ⁅(e n : L), k bi.1⁆) bi.2) • (1 : ℝ)
    simp [Algebra.smul_def]
  exact DFunLike.congr_fun h x

theorem realBracketSystem_eq_zero_iff (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (x : ℝ ⊗[ℚ] L) :
    realBracketSystem f k x = 0 ↔ ∀ b, ⁅x, (1 : ℝ) ⊗ₜ[ℚ] k b⁆ ∈ V.baseChange ℝ := by
  constructor
  · intro h b
    apply (realification_mkQ_eq_zero_iff V _).mp
    apply (f.baseChange ℝ).repr.injective
    ext i
    simpa only [realBracketSystem_apply, map_zero, Finsupp.zero_apply, Pi.zero_apply]
      using congrFun h (b, i)
  · intro h
    funext bi
    rw [realBracketSystem_apply, (realification_mkQ_eq_zero_iff V _).mpr (h bi.1)]
    rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FilteredAdjointFirstBracket
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem centralPairSpan_lie_mem (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0)
    (hb : ⁅b, ⁅a, b⁆⁆ = 0) {x y : L}
    (hx : x ∈ centralPairSpan a b) (hy : y ∈ centralPairSpan a b) :
    ⁅x, y⁆ ∈ Submodule.span ℚ {⁅a, b⁆} := by
  let W := Submodule.span ℚ {⁅a, b⁆}
  have hc : ⁅a, b⁆ ∈ W := Submodule.subset_span (by simp)
  have hba : ⁅b, a⁆ = -⁅a, b⁆ := (lie_skew b a).symm
  have hca : ⁅⁅a, b⁆, a⁆ = 0 := by rw [← lie_skew ⁅a, b⁆ a, ha, neg_zero]
  have hcb : ⁅⁅a, b⁆, b⁆ = 0 := by rw [← lie_skew ⁅a, b⁆ b, hb, neg_zero]
  change x ∈ Submodule.span ℚ {a, b, ⁅a, b⁆} at hx
  change y ∈ Submodule.span ℚ {a, b, ⁅a, b⁆} at hy
  change ⁅x, y⁆ ∈ W
  induction hx using Submodule.span_induction generalizing y with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        try simp only [lie_self, ha, hb, hba, hca, hcb]
      all_goals first | exact W.zero_mem | exact hc | exact W.neg_mem hc
    | zero => simpa only [lie_zero] using W.zero_mem
    | add y z _ _ hy hz => simpa only [lie_add] using W.add_mem hy hz
    | smul r y _ hy => simpa only [lie_smul] using W.smul_mem r hy
  | zero => simpa only [zero_lie] using W.zero_mem
  | add x z _ _ hx hz => simpa only [add_lie] using W.add_mem (hx hy) (hz hy)
  | smul r x _ hx => simpa only [smul_lie] using W.smul_mem r (hx hy)

theorem centralPairSpan_lie_eq_zero (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0)
    (hb : ⁅b, ⁅a, b⁆⁆ = 0) {x y : L}
    (hx : x ∈ centralPairSpan a b) (hy : y ∈ Submodule.span ℚ {⁅a, b⁆}) :
    ⁅x, y⁆ = 0 := by
  have hc : ⁅x, ⁅a, b⁆⁆ = 0 := by
    change x ∈ Submodule.span ℚ {a, b, ⁅a, b⁆} at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact lie_self _
    | zero => exact zero_lie _
    | add x y _ _ hx hy => rw [add_lie, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_lie, hx, smul_zero]
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [lie_smul, hc, smul_zero]

def centralPairSubalgebra (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0)
    (hb : ⁅b, ⁅a, b⁆⁆ = 0) : LieSubalgebra ℚ L :=
  { centralPairSpan a b with
    lie_mem' := fun hx hy =>
      (Submodule.span_mono (by simp)) (centralPairSpan_lie_mem a b ha hb hx hy) }

theorem centralPairSubalgebra_step_two (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0)
    (hb : ⁅b, ⁅a, b⁆⁆ = 0) :
    let K := centralPairSubalgebra a b ha hb
    LieModule.lowerCentralSeries ℚ K K 2 = ⊥ := by
  intro K
  have hcenter : LieModule.lowerCentralSeries ℚ K K 1 ≤ LieAlgebra.center ℚ K := by
    rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_le_iff]
    intro x _ y _
    rw [LieModule.mem_maxTrivSubmodule]
    intro z
    apply Subtype.ext
    exact centralPairSpan_lie_eq_zero a b ha hb z.property
      (centralPairSpan_lie_mem a b ha hb x.property y.property)
  apply bot_unique
  rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_le_iff]
  intro x _ y hy
  exact (LieSubmodule.mem_bot _).mpr ((hcenter hy) x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CoordinateProjectionBounds
namespace OAI

section

namespace Erdos3

open Module

theorem basisCoordinateProjection_abs_repr_le {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Basis ι ℝ V) (S : Set ι) (x : V) (i : ι) :
    |b.repr (basisCoordinateProjection b S x) i| ≤ |b.repr x i| := by
  classical
  rw [basisCoordinateProjection_repr]
  split_ifs
  · exact le_rfl
  · simpa only [abs_zero] using abs_nonneg (b.repr x i)

theorem basisCoordinateProjection_norm_le {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι]
    (b : Basis ι ℝ V) (S : Set ι) (x : V) :
    ‖b.equivFun (basisCoordinateProjection b S x)‖ ≤ ‖b.equivFun x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact (basisCoordinateProjection_abs_repr_le b S x i).trans (norm_le_pi_norm (b.equivFun x) i)

theorem basisCoordinateProjection_real_grid {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Basis ι ℝ V) (S : Set ι) (l : ℕ) (x : V) (hx : (fun i => b.repr x i) ∈ realDenominatorGrid l) :
    (fun i => b.repr (basisCoordinateProjection b S x) i) ∈ realDenominatorGrid l := by
  classical
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => if i ∈ S then z i else 0, ?_⟩
  funext i
  have hi := congrFun hz i
  change (z i : ℝ) = (l : ℝ) * b.repr x i at hi
  change ((if i ∈ S then z i else 0 : ℤ) : ℝ) = (l : ℝ) * b.repr (basisCoordinateProjection b S x) i
  rw [basisCoordinateProjection_repr]
  by_cases h : i ∈ S <;> simp only [h, ↓reduceIte, Int.cast_zero, mul_zero]
  exact hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitGroupRelative
namespace OAI

section

namespace Erdos3

variable {G H : Type*} [Group G] [Group H] (q : G →* H) (d : H →* G)

theorem splitRelativePart_mul (g h : G) :
    splitRelativePart q d (g * h) =
      splitRelativePart q d g * (d (q g) * splitRelativePart q d h * (d (q g))⁻¹) := by
  simp only [splitRelativePart, map_mul]
  group

end Erdos3

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

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FastTerminalBudget
namespace OAI

section

namespace Erdos3

theorem exists_doublePowerParameter_budget (a b C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      (doublePowerParameter a b p + C) ^ C ≤ (p + D) ^ D := by
  let Q : Polynomial ℕ := Polynomial.X + (3 * Polynomial.X + 2) ^ a + (Polynomial.X + 2) ^ b + 2
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  simpa [Q, doublePowerParameter, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

section

namespace Erdos3

theorem exists_fastTerminalParameter_budget (C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      (fastTerminalParameter p + C) ^ C ≤ (p + D) ^ D :=
  exists_doublePowerParameter_budget 294 7 C

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SynchronizedCorrectionBudget
namespace OAI

section

namespace Erdos3

theorem exists_synchronizedCorrection_budget (a d r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + a) ^ a + p + (p + d) ^ d + 2 ≤ (p + C) ^ C ∧
      (p + r) ^ r ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + Polynomial.X +
    (Polynomial.X + Polynomial.C d) ^ d + 2 + (Polynomial.X + Polynomial.C r) ^ r
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have ha : 0 ≤ (p + a) ^ a := by positivity
  have hd : 0 ≤ (p + d) ^ d := by positivity
  have hr : 0 ≤ (p + r) ^ r := by positivity
  have hsum : (p + a) ^ a + p + (p + d) ^ d + 2 + (p + r) ^ r ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TerminalCompositionBudget
namespace OAI

section

namespace Erdos3

theorem exists_terminalComposition_budget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      p ≤ (p + C) ^ C ∧ (2 * p + a) ^ a ≤ (p + C) ^ C ∧ (2 * p + b) ^ b ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := Polynomial.X +
    (2 * Polynomial.X + Polynomial.C a) ^ a + (2 * Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have ha : 0 ≤ (2 * p + a) ^ a := by positivity
  have hb : 0 ≤ (2 * p + b) ^ b := by positivity
  have hsum : p + (2 * p + a) ^ a + (2 * p + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveCyclicCorrelation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] {N : ℕ}

def commonCyclicCuts (h : ι → ZMod N) : Finset ℕ :=
  (Finset.univ.image (quarterLower N)) ∪ (Finset.univ.image (quarterUpper N)) ∪
    (Finset.univ.image (fun i => N - (h i).val))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L ι μ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  {E V : Submodule ℚ L}

theorem realQuotientCoordinateMap_eq_zero_iff (f : Basis ι ℚ (L ⧸ V)) (x : ℝ ⊗[ℚ] L) :
    realQuotientCoordinateMap f x = 0 ↔ x ∈ V.baseChange ℝ := by
  rw [← realification_mkQ_eq_zero_iff]
  constructor
  · intro h
    apply (f.baseChange ℝ).repr.injective
    ext i
    simpa only [realQuotientCoordinateMap_apply, map_zero, Finsupp.zero_apply, Pi.zero_apply]
      using congrFun h i
  · intro h
    funext i
    simp only [realQuotientCoordinateMap_apply, h, map_zero, Finsupp.zero_apply, Pi.zero_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SubspacePolynomialCoordinates
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {L ν σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ν] {E : Submodule ℚ L}

theorem bracketSystemLift_injective (e : Basis ν ℚ E) : Function.Injective (bracketSystemLift e) := by
  intro x y h
  apply (e.baseChange ℝ).equivFun.symm.injective
  exact realification_subtype_injective E h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix NNReal

variable {ι κ δ V W : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  (e : Basis ι ℝ V) (f : Basis κ ℝ W) (q : V →ₗ[ℝ] W)
  (D : Matrix κ ι ℚ) (hD : LinearMap.toMatrix e f q = D.map (Rat.castHom ℝ))

include hD

theorem rational_coordinate_map (x : V) :
    f.equivFun (q x) = D.map (Rat.castHom ℝ) *ᵥ e.equivFun x := by
  have h := LinearMap.toMatrix_mulVec_repr e f q x
  rw [hD] at h
  exact h.symm

theorem rational_coordinate_map_weighted (c : ι → δ) (r : κ → δ)
    (hblock : ∀ i j, r i ≠ c j → D i j = 0)
    (H : ℝ≥0) (hH : ∀ i j, ((D i j).num.natAbs : ℝ) ≤ H)
    (scale : δ → ℝ) (hscale : ∀ d, 0 < scale d) {M : ℝ} (hM : 0 ≤ M)
    (x : V) (hx : ∀ j, |e.equivFun x j| ≤ M / scale (c j)) (i : κ) :
    |f.equivFun (q x) i| ≤
      ((Fintype.card ι : ℝ) + 1) * (H + 1) * M / scale (r i) := by
  rw [rational_coordinate_map e f q D hD]
  exact weighted_matrix_mulVec_bound r c (D.map (Rat.castHom ℝ))
    (fun i j h => by change (D i j : ℝ) = 0; rw [hblock i j h, Rat.cast_zero])
    H (fun i j => (rational_abs_real_le_numerator (D i j)).trans (hH i j))
    scale hscale hM (e.equivFun x) hx i

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ δ V : Type*} [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module ℝ V] (e : Basis ι ℝ V) (S : Matrix ι κ ℚ)

theorem rationalCoordinateSection_rightInverse [DecidableEq ι] [DecidableEq κ]
    {W : Type*} [AddCommGroup W] [Module ℝ W] (f : Basis κ ℝ W)
    (q : V →ₗ[ℝ] W) (D : Matrix κ ι ℚ)
    (hD : LinearMap.toMatrix e f q = D.map (Rat.castHom ℝ))
    (hDS : D * S = 1) (y : κ → ℝ) :
    q (rationalCoordinateSection e S y) = f.equivFun.symm y :=
  (quotient_basis_representative e f q (D.map (Rat.castHom ℝ)) (S.map (Rat.castHom ℝ))
    hD (real_matrix_right_inverse D S hDS) y).symm

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L μ κ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype κ] {E : Submodule ℚ L}

theorem realSubspaceCoordinateMap_lift [DecidableEq κ] (b : Basis μ ℚ L) (e : Basis κ ℚ E)
    (Q : Matrix κ μ ℚ) (hQ : Q * bracketLiftMatrix b e = 1) (x : κ → ℝ) :
    realSubspaceCoordinateMap b Q (bracketSystemLift e x) = x := by
  classical
  rw [realSubspaceCoordinateMap_apply, bracketSystemLift_coordinates]
  change Q.map (Rat.castHom ℝ) *ᵥ ((bracketLiftMatrix b e).map (Rat.castHom ℝ) *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, real_matrix_right_inverse Q (bracketLiftMatrix b e) hQ,
    Matrix.one_mulVec]

theorem lift_realSubspaceCoordinateMap [DecidableEq κ] (b : Basis μ ℚ L) (e : Basis κ ℚ E)
    (Q : Matrix κ μ ℚ) (hQ : Q * bracketLiftMatrix b e = 1)
    (x : ℝ ⊗[ℚ] L) (hx : x ∈ E.baseChange ℝ) :
    bracketSystemLift e (realSubspaceCoordinateMap b Q x) = x := by
  obtain ⟨v, rfl⟩ := exists_subspace_basis_coordinates e x hx
  rw [realSubspaceCoordinateMap_lift b e Q hQ]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StepDropTerminalContainment
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem stepDropBracketKernel_eq_iInf {R L κ : Type*} [Field R] [LieRing L] [LieAlgebra R L]
    [Fintype κ] (K V : Submodule R L) (e : Basis κ R K) :
    stepDropBracketKernel K V = ⨅ z, V.comap (rightLieLinear (e z : L)) := by
  classical
  ext x
  change (∀ k ∈ K, ⁅x, k⁆ ∈ V) ↔ _
  simp only [Submodule.mem_iInf, Submodule.mem_comap, rightLieLinear_apply]
  constructor
  · intro h z
    exact h (e z) (e z).property
  · intro h k hk
    have he : (∑ z, e.repr ⟨k, hk⟩ z • (e z : L)) = k := by
      simpa only [map_sum, map_smul, Submodule.subtype_apply] using
        congrArg K.subtype (e.sum_repr ⟨k, hk⟩)
    rw [← he, lie_sum]
    apply V.sum_mem
    intro z _
    rw [lie_smul]
    exact V.smul_mem _ (h z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealFastCoefficientCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {K E H : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup H] [Module K H] {a d : ℕ}

noncomputable def initialHorizontalEquiv (ha : a ≤ d) (b : Basis (Fin d) K E)
    (P : E →ₗ[K] H) (S : H →ₗ[K] E)
    (hsection : ∀ x, P (S x) = x)
    (hproj : ∀ x j, b.equivFun (S (P x)) j =
      if j.val < a then b.equivFun x j else 0) : (Fin a → K) ≃ₗ[K] H where
  toFun y := P (b.equivFun.symm (extendInitialCoordinates y))
  invFun x i := b.equivFun (S x) (Fin.castLE ha i)
  left_inv y := by
    funext i
    change b.equivFun (S (P (b.equivFun.symm (extendInitialCoordinates y))))
      (Fin.castLE ha i) = y i
    rw [hproj]
    simp only [LinearEquiv.apply_symm_apply, Fin.val_castLE, i.isLt, ite_true,
      extendInitialCoordinates_castLE]
  right_inv x := by
    have he : b.equivFun.symm
        (extendInitialCoordinates (fun i => b.equivFun (S x) (Fin.castLE ha i))) = S x := by
      apply b.equivFun.injective
      funext j
      rw [LinearEquiv.apply_symm_apply]
      change (if h : j.val < a then
        b.equivFun (S x) (Fin.castLE ha ⟨j.val, h⟩) else 0) = b.equivFun (S x) j
      split_ifs with hj
      · rfl
      · have h := hproj (S x) j
        simpa only [hsection, hj, ite_false] using h.symm
    change P (b.equivFun.symm
      (extendInitialCoordinates (fun i => b.equivFun (S x) (Fin.castLE ha i)))) = x
    rw [he, hsection]
  map_add' x y := by simp only [map_add]
  map_smul' c x := by simp only [map_smul, RingHom.id_apply]

theorem initialHorizontalEquiv_symm_projection (ha : a ≤ d) (b : Basis (Fin d) K E)
    (P : E →ₗ[K] H) (S : H →ₗ[K] E)
    (hsection : ∀ x, P (S x) = x)
    (hproj : ∀ x j, b.equivFun (S (P x)) j =
      if j.val < a then b.equivFun x j else 0) (x : E) :
    (initialHorizontalEquiv ha b P S hsection hproj).symm (P x) =
      fun i => b.equivFun x (Fin.castLE ha i) := by
  funext i
  change b.equivFun (S (P x)) (Fin.castLE ha i) = _
  rw [hproj]
  simp only [Fin.val_castLE, i.isLt, ite_true]

theorem initialHorizontalEquiv_projection (ha : a ≤ d) (b : Basis (Fin d) K E)
    (P : E →ₗ[K] H) (S : H →ₗ[K] E)
    (hsection : ∀ x, P (S x) = x)
    (hproj : ∀ x j, b.equivFun (S (P x)) j =
      if j.val < a then b.equivFun x j else 0) (x : E) :
    initialHorizontalEquiv ha b P S hsection hproj
      (fun i => b.equivFun x (Fin.castLE ha i)) = P x := by
  rw [← initialHorizontalEquiv_symm_projection ha b P S hsection hproj x,
    LinearEquiv.apply_symm_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeRetainedIntegerMultilinearQuadruples
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem cyclicTranslationOffset_eq_branch {N : ℕ} (h : ZMod N) (a : ℕ) :
    cyclicTranslationOffset h a = cyclicBranchOffset h (decide (N - h.val ≤ a)) := by
  by_cases hwrap : N - h.val ≤ a <;> simp [cyclicTranslationOffset, cyclicBranchOffset, hwrap]

end Erdos3

end

end OAI
end


