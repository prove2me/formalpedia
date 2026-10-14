-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0338_parallel1
-- name    : PNT_ZeroFree_433_0338_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:20:44.0865+00:00
-- url     : https://prove2.me/theorems/d8284b6a-70eb-48e7-9aa5-c919ee43db36
-- title:
--   Zero-free region foundations: CubicSieve.Factorization, CubicSieve.Operator, CubicSieve.Blocks [0338_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.Factorization
--   - OAI.NumberTheory.DirichletL.CubicSieve.Operator
--   - OAI.NumberTheory.DirichletL.CubicSieve.Blocks
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/Factorization.lean#L15-L100
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/Operator.lean#L12-L85
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/Blocks.lean#L13-L88

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_PNT_ZeroFree_433_0147
import Definitions.Def_PNT_ZeroFree_433_0149
import Definitions.Def_PNT_ZeroFree_433_0345_parallel1
import Definitions.Def_PNT_ZeroFree_433_0377_parallel1
import Definitions.Def_PNT_ZeroFree_433_0419_parallel1
import Definitions.Def_PNT_ZeroFree_433_0475_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/Factorization.lean#L15-L100
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/Operator.lean#L12-L85
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/Blocks.lean#L13-L88
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.Factorization
section
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open UniqueFactorizationMonoid
noncomputable section

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [NormalizationMonoid M] [Subsingleton Mˣ]

def firstPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 1), p

def secondPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 2), p

def cubePart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset, p ^ ((normalizedFactors x).count p / 3)

theorem count_mod_three (k : ℕ) :
    k = (if k % 3 = 1 then 1 else 0) +
      2 * (if k % 3 = 2 then 1 else 0) + 3 * (k / 3) := by
  have h := Nat.mod_add_div k 3
  have hlt := Nat.mod_lt k (by decide : 0 < 3)
  split_ifs <;> omega

omit [Subsingleton Mˣ] in
private theorem residual_squarefree (x : M) (r : ℕ) :
    Squarefree (∏ p ∈ (normalizedFactors x).toFinset.filter
      (fun p => (normalizedFactors x).count p % 3 = r), p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hp' : p ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hq' : q ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hq).1
    apply (irreducible_of_normalized_factor p hp').isRelPrime_iff_not_dvd.mpr
    intro hd
    exact hpq (normalizedFactors_eq_of_dvd x p hp' q hq' hd)
  · intro p hp
    exact (irreducible_of_normalized_factor p
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1)).squarefree

omit [Subsingleton Mˣ] in
theorem firstPart_squarefree (x : M) : Squarefree (firstPart x) :=
  residual_squarefree x 1

omit [Subsingleton Mˣ] in
theorem secondPart_squarefree (x : M) : Squarefree (secondPart x) :=
  residual_squarefree x 2

omit [Subsingleton Mˣ] in
theorem residual_parts_isRelPrime (x : M) : IsRelPrime (firstPart x) (secondPart x) := by
  unfold firstPart secondPart
  apply IsRelPrime.prod_left
  intro p hp
  apply IsRelPrime.prod_right
  intro q hq
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  apply (irreducible_of_normalized_factor p (Multiset.mem_toFinset.mp hp'.1)).isRelPrime_iff_not_dvd.mpr
  intro hd
  have heq := normalizedFactors_eq_of_dvd x p (Multiset.mem_toFinset.mp hp'.1)
    q (Multiset.mem_toFinset.mp hq'.1) hd
  subst q
  omega

theorem cubic_factorization (x : M) (hx : x ≠ 0) :
    x = firstPart x * secondPart x ^ 2 * cubePart x ^ 3 := by
  have hp : (∏ p ∈ (normalizedFactors x).toFinset,
      p ^ (normalizedFactors x).count p) = x := by
    rw [← Finset.prod_multiset_count]
    exact associated_iff_eq.mp (prod_normalizedFactors hx)
  have hper (p : M) : p ^ (normalizedFactors x).count p =
      (if (normalizedFactors x).count p % 3 = 1 then p else 1) *
      (if (normalizedFactors x).count p % 3 = 2 then p else 1) ^ 2 *
      (p ^ ((normalizedFactors x).count p / 3)) ^ 3 := by
    conv_lhs => rw [count_mod_three ((normalizedFactors x).count p)]
    rw [pow_add, pow_add, Nat.mul_comm 3, pow_mul]
    split_ifs <;> simp [pow_mul]
  calc
    x = ∏ p ∈ (normalizedFactors x).toFinset,
        p ^ (normalizedFactors x).count p := hp.symm
    _ = firstPart x * secondPart x ^ 2 * cubePart x ^ 3 := by
      simp_rw [hper]
      simp only [Finset.prod_mul_distrib, Finset.prod_pow]
      simp only [firstPart, secondPart, cubePart, Finset.prod_filter]

theorem extraction_injective_on_nonzero :
    Set.InjOn (fun x : M => (firstPart x, secondPart x, cubePart x)) {x | x ≠ 0} := by
  intro x hx y hy h
  have h1 := congrArg (fun t : M × M × M => t.1) h
  have h2 := congrArg (fun t : M × M × M => t.2.1) h
  have h3 := congrArg (fun t : M × M × M => t.2.2) h
  dsimp only at h1 h2 h3
  rw [cubic_factorization x hx, cubic_factorization y hy, h1, h2, h3]

end
end SevenEighths.CubicSieve

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.Operator
section
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def operator (A : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  A.toEuclideanLin.toContinuousLinearMap

omit [DecidableEq m] in
@[simp] theorem operator_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) (i : m) :
    operator A x i = ∑ j, A i j * x j := rfl

def squaredNorm (A : Matrix m n ℂ) : ℝ := ‖operator A‖ ^ 2

def conjugateVector (x : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 (fun j => star (x j))

omit [Fintype n] [DecidableEq n] in
@[simp] theorem conjugateVector_apply (x : EuclideanSpace ℂ n) (j : n) :
    conjugateVector x j = star (x j) := rfl

omit [DecidableEq n] in
@[simp] theorem norm_conjugateVector (x : EuclideanSpace ℂ n) :
    ‖conjugateVector x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, conjugateVector_apply, norm_star]

omit [DecidableEq m] in
theorem operator_conjugate_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    operator (fun i j => star (A i j)) x = conjugateVector (operator A (conjugateVector x)) := by
  ext i
  change (∑ j, star (A i j) * x j) = star (∑ j, A i j * star (x j))
  simp only [star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

omit [DecidableEq m] in
theorem operator_conjugate_norm_le (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [operator_conjugate_apply, norm_conjugateVector]
  simpa only [norm_conjugateVector] using (operator A).le_opNorm (conjugateVector x)

omit [DecidableEq m] in
theorem operator_conjugate_norm (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ = ‖operator A‖ := by
  apply le_antisymm (operator_conjugate_norm_le A)
  simpa only [star_star] using operator_conjugate_norm_le (fun i j => star (A i j))

theorem operator_conjTranspose_norm (A : Matrix m n ℂ) :
    ‖operator A.conjTranspose‖ = ‖operator A‖ := by
  have heq : operator A.conjTranspose = (operator A).adjoint := by
    unfold operator
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]
  rw [heq]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem squaredNorm_transpose (A : Matrix m n ℂ) :
    squaredNorm A.transpose = squaredNorm A := by
  unfold squaredNorm
  have h := operator_conjugate_norm A.transpose
  change ‖operator A.conjTranspose‖ = ‖operator A.transpose‖ at h
  rw [operator_conjTranspose_norm] at h
  exact congrArg (fun x : ℝ => x ^ 2) h.symm

theorem squaredNorm_reciprocity (A : Matrix m n ℂ) (B : Matrix n m ℂ)
    (hrecip : ∀ i j, A i j = B j i) : squaredNorm A = squaredNorm B := by
  have h : A = B.transpose := by ext i j; exact hrecip i j
  rw [h, squaredNorm_transpose]

omit [DecidableEq m] in
theorem energy_le_squaredNorm (A : Matrix m n ℂ) (c : n → ℂ) :
    (∑ i, ‖∑ j, A i j * c j‖ ^ 2) ≤ squaredNorm A * ∑ j, ‖c j‖ ^ 2 := by
  let x : EuclideanSpace ℂ n := WithLp.toLp 2 c
  have h := (operator A).le_opNorm x
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [squaredNorm, mul_pow, EuclideanSpace.norm_sq_eq, operator_apply, x] using hs

end
end SevenEighths.CubicSieve

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.Blocks
section
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section

variable {a b n : Type*} [Fintype a] [Fintype b] [Fintype n]
  [DecidableEq n]

theorem squaredNorm_nonneg (A : Matrix a n ℂ) : 0 ≤ squaredNorm A := sq_nonneg _

theorem masked_energy_le (A : Matrix a n ℂ) (coef phase : n → ℂ)
    (hphase : ∀ j, ‖phase j‖ ≤ 1) :
    (∑ i, ‖∑ j, A i j * (coef j * phase j)‖ ^ 2) ≤
      squaredNorm A * ∑ j, ‖coef j‖ ^ 2 := by
  apply (energy_le_squaredNorm A (fun j => coef j * phase j)).trans
  apply mul_le_mul_of_nonneg_left _ (squaredNorm_nonneg A)
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul]
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_of_le_one_right (norm_nonneg _) (hphase j)

theorem rectangular_block_energy_le
    (A : Matrix a n ℂ) (B : Matrix b n ℂ) (coef mask : n → ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ k j, ‖B k j‖ ≤ 1)
    (hmask : ∀ j, ‖mask j‖ ≤ 1) :
    (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
      min ((Fintype.card b : ℝ) * squaredNorm A)
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
  have hleft :
      (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
        ((Fintype.card b : ℝ) * squaredNorm A) * ∑ j, ‖coef j‖ ^ 2 := by
    calc
      _ ≤ ∑ k : b, squaredNorm A * ∑ j, ‖coef j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have h := masked_energy_le A coef (fun j => star (B k j) * mask j) (by
          intro j
          rw [norm_mul, norm_star]
          exact (mul_le_mul_of_nonneg_right (hB k j) (norm_nonneg _)).trans (by simpa using hmask j))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by simp [mul_assoc]
  have hright :
      (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ i : a, squaredNorm (fun k j => star (B k j)) * ∑ j, ‖coef j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := masked_energy_le (fun k j => star (B k j)) coef
          (fun j => A i j * mask j) (by
            intro j
            rw [norm_mul]
            exact (mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)).trans (by simpa using hmask j))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by
        have hn : squaredNorm (fun k j => star (B k j)) = squaredNorm B := by
          unfold squaredNorm
          rw [operator_conjugate_norm]
        rw [hn]
        simp [mul_assoc]
  rcases le_total ((Fintype.card b : ℝ) * squaredNorm A)
      ((Fintype.card a : ℝ) * squaredNorm B) with h | h
  · rw [min_eq_left h]
    exact hleft
  · rw [min_eq_right h]
    exact hright

theorem cube_family_block_energy_le {c : Type*} [Fintype c]
    (A : Matrix a n ℂ) (B : Matrix b n ℂ) (coef : n → ℂ) (mask : c → n → ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ k j, ‖B k j‖ ≤ 1)
    (hmask : ∀ l j, ‖mask l j‖ ≤ 1) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask l j‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm A)
          ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
  calc
    _ ≤ ∑ l : c, min ((Fintype.card b : ℝ) * squaredNorm A)
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro l _
      exact rectangular_block_energy_le A B coef (mask l) hA hB (hmask l)
    _ = _ := by simp [mul_assoc]

end
end SevenEighths.CubicSieve

end OAI

end


