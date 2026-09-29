-- Prove2me | Definitions.Def_RandKaczmarz_core
-- name    : RandKaczmarz_core
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-25T16:13:51.34492+00:00
-- url     : https://prove2.me/theorems/1aa1d3b5-75cc-4d0f-81be-2aafb73d0794
-- title:
--   Randomized Kaczmarz: rows, row-sampling distribution, projection step, scaled condition number $\kappa(A)$, and the expected squared error
-- statement:
--   The objects of Strohmer–Vershynin used by every statement in this mission. Throughout, $A\in\mathbb{C}^{m\times n}$ and $b\in\mathbb{C}^m$.
--
--   1. **Rows.** $a_i\in\mathbb{C}^n$ is the conjugate of row $i$, so $(Ax)_i=\langle a_i,x\rangle$ (proved as a lemma).
--   2. **Frobenius norm.** $\|A\|_F^2=\sum_{i,j}|A_{ij}|^2=\sum_i\|a_i\|_2^2$.
--   3. **Row probabilities.** $p_i=\|a_i\|_2^2/\|A\|_F^2$. They are nonnegative and, when $A\ne0$, sum to $1$.
--   4. **Condition number.** $\sigma_{\min}(A)=\inf_{\|z\|_2=1}\|Az\|_2$ and $\kappa(A)=\|A\|_F/\sigma_{\min}(A)$.
--   5. **Step.** $\mathrm{step}_i(x)=x+\dfrac{b_i-\langle a_i,x\rangle}{\|a_i\|_2^2}\,a_i$, the projection of $x$ onto the hyperplane $\{y:\langle a_i,y\rangle=b_i\}$.
--   6. **Runs.** A list of rows is applied left to right. Its probability is the product of the $p_i$ of its entries.
--   7. **Expected squared error.**
--   $$\mathbb{E}\,\|x_k-x\|_2^2=\sum_{q:\{1,\dots,k\}\to\{1,\dots,m\}}\Bigl(\prod_{t=1}^k p_{q(t)}\Bigr)\bigl\|\mathrm{step}_{q(k)}\cdots\mathrm{step}_{q(1)}(x_0)-x\bigr\|_2^2 .$$
--   At $k=0$ it equals $\|x_0-x\|_2^2$.
--
--   **Formalization Note** Mathlib's inner product is conjugate-linear in its first argument, which is why $a_i$ is a conjugated row. The Frobenius norm is defined directly as a double sum. The expectation is a finite sum, so no measure theory is needed. Lean's junk values: a zero row makes the step the identity, which is harmless because that row has probability $0$; and $\sigma_{\min}(A)=0$ gives $\kappa(A)=0$, which the full-rank hypothesis of every theorem rules out.
-- source:
--   Strohmer & Vershynin, A randomized Kaczmarz algorithm with exponential convergence, arXiv:math/0702226v1 [math.NA], https://arxiv.org/abs/math/0702226 (published: J. Fourier Anal. Appl. 15 (2009), 262-278), pp. 2-4: system (1), condition numbers (Section 1, last two paragraphs), Algorithm 1 and eq. (4), Theorem 2 and eq. (5)

import Mathlib

open scoped InnerProductSpace ComplexConjugate
open WithLp Matrix

namespace RandKaczmarz

variable {m n : ℕ}

/-- `A x`, viewed as an element of the Euclidean space `ℂ^m`. -/
noncomputable def mulVecE (A : Matrix (Fin m) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin m) :=
  toLp 2 (A *ᵥ ofLp x)

/-- The vector `a i` of Strohmer–Vershynin: the `i`-th row of `A` is `(a i)^*`,
so that the `i`-th equation of `A x = b` reads `⟪a i, x⟫ = b i`. -/
noncomputable def krow (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) : EuclideanSpace ℂ (Fin n) :=
  toLp 2 (fun j => conj (A i j))

@[simp] lemma krow_apply (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    krow A i j = conj (A i j) := rfl

@[simp] lemma mulVecE_apply (A : Matrix (Fin m) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n))
    (i : Fin m) : mulVecE A x i = ∑ j, A i j * x j :=
  Matrix.mulVec_apply_eq_sum A (ofLp x) i

/-- The `i`-th coordinate of `A x` is the inner product of `a i` with `x`. -/
lemma inner_krow (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (x : EuclideanSpace ℂ (Fin n)) :
    ⟪krow A i, x⟫_ℂ = mulVecE A x i := by
  simp only [PiLp.inner_apply, mulVecE_apply, RCLike.inner_apply, krow_apply,
    starRingEnd_apply, star_star]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The squared Frobenius norm `‖A‖_F ^ 2 = ∑ i ∑ j |A i j| ^ 2`. -/
noncomputable def frobSq (A : Matrix (Fin m) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

lemma frobSq_eq_sum_krow (A : Matrix (Fin m) (Fin n) ℂ) :
    frobSq A = ∑ i, ‖krow A i‖ ^ 2 := by
  simp [frobSq, EuclideanSpace.norm_sq_eq]

lemma frobSq_nonneg (A : Matrix (Fin m) (Fin n) ℂ) : 0 ≤ frobSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The sampling distribution of Algorithm 1: row `i` is drawn with probability
proportional to `‖a i‖ ^ 2`. -/
noncomputable def rowProb (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) : ℝ :=
  ‖krow A i‖ ^ 2 / frobSq A

lemma rowProb_nonneg (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) : 0 ≤ rowProb A i :=
  div_nonneg (sq_nonneg _) (frobSq_nonneg A)

lemma sum_rowProb (A : Matrix (Fin m) (Fin n) ℂ) (hA : frobSq A ≠ 0) :
    ∑ i, rowProb A i = 1 := by
  simp only [rowProb]
  rw [← Finset.sum_div, ← frobSq_eq_sum_krow, div_self hA]

/-- The smallest singular value of `A`, i.e. `‖A⁻¹‖₂⁻¹`: the largest constant `σ`
with `‖A z‖ ≥ σ ‖z‖` for all `z`. -/
noncomputable def sigmaMin (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ⨅ z : {z : EuclideanSpace ℂ (Fin n) // ‖z‖ = 1}, ‖mulVecE A (z : EuclideanSpace ℂ (Fin n))‖

/-- Demmel's scaled condition number `κ(A) = ‖A‖_F ‖A⁻¹‖₂`. -/
noncomputable def scaledCond (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  Real.sqrt (frobSq A) / sigmaMin A

/-- One randomized Kaczmarz projection (equation (4)): the orthogonal projection of `x`
onto the solution hyperplane `{y : ⟪a i, y⟫ = b i}` of the `i`-th equation. -/
noncomputable def step (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ) (i : Fin m)
    (x : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  x + ((b i - ⟪krow A i, x⟫_ℂ) / ((‖krow A i‖ ^ 2 : ℝ) : ℂ)) • krow A i

/-- Running Algorithm 1 along a prescribed list of row choices. -/
noncomputable def runSteps (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ) :
    List (Fin m) → EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)
  | [], x => x
  | i :: is, x => runSteps A b is (step A b i x)

/-- The probability that Algorithm 1 draws a prescribed list of rows, the rows being
drawn independently with distribution `rowProb A`. -/
noncomputable def pathProb (A : Matrix (Fin m) (Fin n) ℂ) : List (Fin m) → ℝ
  | [] => 1
  | i :: is => rowProb A i * pathProb A is

/-- `expErrSq A b x k x₀` is `E ‖x_k - x‖ ^ 2`, the expected squared error after `k`
iterations of Algorithm 1 started at `x₀`, where `x` is the solution of `A x = b`. -/
noncomputable def expErrSq (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (x : EuclideanSpace ℂ (Fin n)) (k : ℕ) (x₀ : EuclideanSpace ℂ (Fin n)) : ℝ :=
  ∑ p : Fin k → Fin m, pathProb A (List.ofFn p) * ‖runSteps A b (List.ofFn p) x₀ - x‖ ^ 2

@[simp] lemma expErrSq_zero (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (x x₀ : EuclideanSpace ℂ (Fin n)) : expErrSq A b x 0 x₀ = ‖x₀ - x‖ ^ 2 := by
  simp [expErrSq, pathProb, runSteps]

end RandKaczmarz


