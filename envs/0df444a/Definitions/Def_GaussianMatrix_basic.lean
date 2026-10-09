-- Prove2me | Definitions.Def_GaussianMatrix_basic
-- name    : GaussianMatrix_basic
-- status  : Definition
-- author  : @tc
-- created : 2026-10-09T02:25:54.817695+00:00
-- url     : https://prove2.me/theorems/74a83eea-999c-43f1-b951-707784cedad4
-- title:
--   Standard Gaussian matrices: law, Frobenius and spectral norms, smallest singular value, pseudoinverse
-- statement:
--   This bundle fixes the shared vocabulary of the *Gaussian Random Matrices* mission series (namespace `GaussianMatrix`).
--
--   **The Gaussian matrix law.** For $p,m\in\mathbb N$, $\gamma_{p,m}$ denotes the law of a $p\times m$ matrix whose $pm$ entries are independent standard normal $\mathcal N(0,1)$ random variables. It is realized as the product measure $\bigotimes_{i<p}\bigotimes_{j<m}\mathcal N(0,1)$ on the function space $\mathbb R^{p}\to\mathbb R^{m}\to\mathbb R$; a sample $G$ is turned into a matrix by the identity map $\mathrm{of}(G)\in\mathbb R^{p\times m}$. It is a probability measure (instance provided).
--
--   **Norms.** For a real matrix $A$,
--   $$\|A\|_F^2=\sum_{i,j}A_{ij}^2,\qquad \|A\|_F=\sqrt{\|A\|_F^2},\qquad \|A\|=\max_{\|x\|_2=1}\|Ax\|_2 ,$$
--   where $\|A\|$ (the spectral norm, i.e. the largest singular value) is Mathlib's $\ell_2\to\ell_2$ operator norm (`Matrix.Norms.L2Operator`).
--
--   **Smallest singular value.** For a (tall) matrix $A\in\mathbb R^{N\times n}$,
--   $$\sigma_{\min}(A)=\inf\{\|Ax\|_2 : x\in\mathbb R^{n},\ \|x\|_2=1\},$$
--   so that $\sigma_{\min}(A)$ is the $n$-th singular value when $N\ge n$, and $0$ when $N<n$. For a wide matrix $G$ the usual $\sigma_{\min}(G)$ is $\sigma_{\min}(G^{\mathsf T})$.
--
--   **Pseudoinverse of a full-row-rank matrix.** For $G\in\mathbb R^{m\times n}$,
--   $$G^{\dagger}=G^{\mathsf T}(GG^{\mathsf T})^{-1},$$
--   which is the Moore–Penrose pseudoinverse whenever $GG^{\mathsf T}$ is invertible (i.e. $G$ has full row rank).
--
--   These are the objects appearing in the Gaussian moment identities of Halko–Martinsson–Tropp and Tropp–Webber and in Gordon's theorem on extreme singular values.
--
--   **Formalization Note.** Mathlib's matrix inverse is total: $(GG^{\mathsf T})^{-1}=0$ when $GG^{\mathsf T}$ is singular, so $G^{\dagger}=0$ on that null set. The infimum defining $\sigma_{\min}$ is over the unit sphere of $\mathbb R^n$; for $n=0$ the sphere is empty and the real-valued infimum is $0$ by Lean's convention. Sample spaces are function types rather than `Matrix` types because Mathlib equips the former, not the latter, with the product $\sigma$-algebra.
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), §10.1 p. 55 (standard Gaussian matrix, rotational invariance) and §A.2 p. 64–65 (pseudoinverse $G^\dagger$, $\|G^\dagger\|_F^2=\operatorname{tr}(GG^*)^{-1}$); R. Vershynin, *Introduction to the non-asymptotic analysis of random matrices*, Chapter 5 of Compressed Sensing: Theory and Applications (Y. Eldar, G. Kutyniok, eds.), Cambridge University Press, 2012, https://arxiv.org/abs/1011.3027 (v7), §5.1 p. 2 (singular values $s_{\min}(A)=\inf_{\|x\|_2=1}\|Ax\|_2$, $s_{\max}(A)=\|A\|$).

import Mathlib

/-!
# Standard Gaussian matrices: basic definitions

Shared vocabulary for the "Gaussian Random Matrices" mission series.

* `GaussianMatrix.gaussianMatrix p m` — the law of a `p × m` matrix with independent
  standard normal entries, as the product measure on `Fin p → Fin m → ℝ`. A sample `G` is
  viewed as a matrix via `Matrix.of G`.
* `GaussianMatrix.frobSq`, `frobNorm` — squared Frobenius norm `∑ᵢⱼ Aᵢⱼ²` and its square root.
* `GaussianMatrix.specNorm` — the spectral norm (largest singular value), i.e. Mathlib's
  `ℓ₂ → ℓ₂` operator norm `Matrix.Norms.L2Operator`.
* `GaussianMatrix.sMin` — the smallest singular value of a tall `N × n` matrix,
  `inf { ‖A x‖₂ : ‖x‖₂ = 1 }` (for a wide matrix apply it to the transpose).
* `GaussianMatrix.pinvR` — `Gᵀ (G Gᵀ)⁻¹`, the Moore–Penrose pseudoinverse of a matrix with
  full row rank (Mathlib's `⁻¹` is total, returning `0` on a singular input).
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace GaussianMatrix

/-- The law of a `p × m` standard Gaussian matrix: independent `N(0,1)` entries, as a product
measure on `Fin p → Fin m → ℝ`. `Matrix.of G` is the matrix view of a sample `G`. -/
noncomputable def gaussianMatrix (p m : ℕ) : Measure (Fin p → Fin m → ℝ) :=
  Measure.pi fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal 0 1

instance gaussianMatrix_isProbabilityMeasure (p m : ℕ) :
    IsProbabilityMeasure (gaussianMatrix p m) := by
  unfold gaussianMatrix; infer_instance

/-- Squared Frobenius norm `‖A‖_F² = ∑ᵢ ∑ⱼ Aᵢⱼ²`. -/
def frobSq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- Frobenius norm `‖A‖_F = √(∑ᵢⱼ Aᵢⱼ²)`. -/
noncomputable def frobNorm {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) : ℝ :=
  Real.sqrt (frobSq A)

/-- Spectral norm `‖A‖ = max_{‖x‖₂ = 1} ‖A x‖₂` (largest singular value): Mathlib's
`ℓ₂ → ℓ₂` operator norm of a real matrix. -/
noncomputable def specNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) : ℝ := ‖A‖

/-- Smallest singular value of a tall matrix `A : Matrix N n`:
`σ_min(A) = inf { ‖A x‖₂ : x ∈ ℝⁿ, ‖x‖₂ = 1 }` (equal to `0` when `n = 0`, by the real
convention `inf ∅ = 0`). For a wide matrix use `sMin Aᵀ`. -/
noncomputable def sMin {N n : Type*} [Fintype N] [Fintype n] (A : Matrix N n ℝ) : ℝ :=
  ⨅ x : {x : n → ℝ // x ⬝ᵥ x = 1}, Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1))

/-- Right pseudoinverse `G† = Gᵀ (G Gᵀ)⁻¹` of a matrix `G : Matrix m n`; it is the Moore–Penrose
pseudoinverse whenever `G Gᵀ` is invertible (full row rank), and `0` otherwise. -/
noncomputable def pinvR {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (G : Matrix m n ℝ) : Matrix n m ℝ :=
  Gᵀ * (G * Gᵀ)⁻¹

end GaussianMatrix


