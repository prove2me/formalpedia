-- Prove2me | Definitions.Def_KLTNuclear_RankRecovery_Model
-- name    : KLTNuclear_RankRecovery_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:48.866979+00:00
-- url     : https://prove2.me/theorems/6ebbd6a4-6df0-4791-b5ed-f1557e3b2721
-- title:
--   Matrix completion data, the matrix $\mathbf X$ and the estimator (3.1), the matrix $\mathbf M$ of (2.2), singular values and the rank-one span projector
-- statement:
--   This module fixes the objects of the matrix completion setting of Koltchinskii, Lounici and Tsybakov in which Theorem 8 (p. 20) is stated. Everything is realization-wise: the data are fixed numbers.
--
--   Let $m_1,m_2,n\ge1$. A sample consists of observed positions $(j_i,k_i)\in\{1,\dots,m_1\}\times\{1,\dots,m_2\}$ and real responses $Y_i$, $i=1,\dots,n$. Write $\langle A,B\rangle=\operatorname{tr}(A^\top B)$, $\|A\|_2$ for the Frobenius norm, $\|A\|_1$ for the nuclear norm and $\|A\|_\infty$ for the operator norm.
--
--   1. **Design (1.3).** $X_i=e_{j_i}(m_1)e_{k_i}(m_2)^\top$, the matrix with a single entry $1$ at position $(j_i,k_i)$.
--   2. **The matrix $\mathbf X$ (p. 12).** $$\mathbf X=\frac{m_1m_2}{n}\sum_{i=1}^nY_iX_i .$$
--   3. **The matrix $\mathbf M$ (2.2).** For a matrix $A_0\in\mathbb R^{m_1\times m_2}$,
--   $$\mathbf M=\frac1n\sum_{i=1}^nY_iX_i-\frac{A_0}{m_1m_2}.$$
--   4. **The estimator (3.1).** For $\lambda\in\mathbb R$, $F(A)=\|A-\mathbf X\|_2^2+\lambda m_1m_2\|A\|_1$, and $\hat A$ is the estimator $\hat A^\lambda$ when $F(\hat A)\le F(A)$ for every $A\in\mathbb R^{m_1\times m_2}$.
--   5. **Singular values.** $\sigma_1(B)\ge\sigma_2(B)\ge\dots\ge\sigma_{m_1\wedge m_2}(B)\ge0$ are the singular values of $B$ with multiplicity, in decreasing order.
--   6. **Span projector (p. 20).** For vectors $u_k\in\mathbb R^{m_1}$, $v_k\in\mathbb R^{m_2}$, $k$ in a finite index set, $\mathcal P B=\sum_k\langle u_kv_k^\top,B\rangle\,u_kv_k^\top$. When both families are orthonormal, $\mathcal P$ is the orthogonal projector onto the linear span of the matrices $u_kv_k^\top$.
--
--   These are the objects in which the rank-recovery theorem and every step of its proof are stated.
--
--   **Formalization Note** The matrix layer (`RealMatrix`, `coordinateMatrix`, `frobeniusNormSq`, `nuclearNorm`, `spectralNorm`, `SVD`) is imported from the published `MatrixCompletion` definitions. In the paper $\mathbf M=\frac1n\sum_i(Y_iX_i-\mathbb E(Y_iX_i))$ is random; under the trace regression model (1.1) and the uniform design on the matrix completion basis, $\mathbb E(Y_iX_i)=\mathbb E(\langle A_0,X_i\rangle X_i)=A_0/(m_1m_2)$, which is item 3 (and gives the paper's identity $\mathbf X-A_0=m_1m_2\mathbf M$). (3.1) is used in its second form; the first form is $(m_1m_2)^{-1}(F(A)-\|\mathbf X\|_2^2)$ and has the same minimizers. `singularValue B j` is **0-based**: it is the paper's $\sigma_{j+1}(B)$, Mathlib's `LinearMap.singularValues` of $B$ acting $\mathbb R^{m_2}\to\mathbb R^{m_1}$; it is antitone in $j$ and $0$ for $j\ge\operatorname{rank}B$. `IsEstimator` only says $\hat A$ minimizes; existence and uniqueness are not asserted.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 2 (1.3), p. 6 (2.2), p. 12 (3.1) and the definition of X, p. 20 proof of Theorem 8 (projector 𝒫)

import Mathlib
import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

namespace KLTNuclear.RankRecovery

/-!
Matrix completion objects of Koltchinskii, Lounici and Tsybakov (arXiv:1011.6256v4), used by
Theorem 8 (p. 20): the design `X_i = e_{j_i}(m₁) e_{k_i}(m₂)ᵀ` of (1.3), the matrix
`𝐗 = (m₁m₂/n) Σ Y_i X_i` and the objective of (3.1) (p. 12), the matrix `𝐌` of (2.2) under the
uniform design, the `j`-th singular value, and the projector onto the span of rank-one
matrices `u_k v_kᵀ`.

All objects are realization-wise: the sample is the list of observed positions
`idx : Fin n → Fin m₁ × Fin m₂` and the list of responses `y : Fin n → ℝ`.
-/

/-- (1.3), p. 2: the `i`-th design matrix `X_i = e_j(m₁) e_k(m₂)ᵀ`, `(j, k) = idx i`. -/
def designMatrix {m₁ m₂ n : ℕ} (idx : Fin n → Fin m₁ × Fin m₂) (i : Fin n) :
    RealMatrix m₁ m₂ :=
  coordinateMatrix (idx i).1 (idx i).2

/-- p. 12: the matrix `𝐗 = (m₁m₂/n) Σ_{i=1}^n Y_i X_i`. -/
noncomputable def bigX {m₁ m₂ n : ℕ} (idx : Fin n → Fin m₁ × Fin m₂) (y : Fin n → ℝ) :
    RealMatrix m₁ m₂ :=
  ((m₁ * m₂ : ℝ) / n) • ∑ i, y i • designMatrix idx i

/-- (2.2), p. 6, under the uniform design on the matrix completion basis and the model (1.1):
`𝐌 = (1/n) Σ (Y_i X_i − E(Y_i X_i))` with `E(Y_i X_i) = E(⟨A₀, X_i⟩ X_i) = A₀/(m₁m₂)`, i.e.
`𝐌 = (1/n) Σ Y_i X_i − A₀/(m₁m₂)`. -/
noncomputable def noiseMatrix {m₁ m₂ n : ℕ} (idx : Fin n → Fin m₁ × Fin m₂) (y : Fin n → ℝ)
    (A₀ : RealMatrix m₁ m₂) : RealMatrix m₁ m₂ :=
  (1 / (n : ℝ)) • ∑ i, y i • designMatrix idx i - (m₁ * m₂ : ℝ)⁻¹ • A₀

/-- (3.1), p. 12, second line: the objective `F(A) = ‖A − 𝐗‖₂² + λ m₁ m₂ ‖A‖₁`. -/
noncomputable def objective {m₁ m₂ n : ℕ} (idx : Fin n → Fin m₁ × Fin m₂) (y : Fin n → ℝ)
    (lam : ℝ) (A : RealMatrix m₁ m₂) : ℝ :=
  frobeniusNormSq (A - bigX idx y) + lam * (m₁ * m₂ : ℝ) * nuclearNorm A

/-- (3.1), p. 12: `Â` is the estimator `Â^λ`, i.e. a minimizer of `F` over all of `ℝ^{m₁×m₂}`. -/
def IsEstimator {m₁ m₂ n : ℕ} (idx : Fin n → Fin m₁ × Fin m₂) (y : Fin n → ℝ)
    (lam : ℝ) (Ahat : RealMatrix m₁ m₂) : Prop :=
  ∀ A : RealMatrix m₁ m₂, objective idx y lam Ahat ≤ objective idx y lam A

/-- The singular values of `B`, **0-based**: `singularValue B j` is the paper's `σ_{j+1}(B)`,
the `(j+1)`-st largest singular value of `B` (with multiplicity), and it is `0` for
`j ≥ min m₁ m₂`. It is Mathlib's `LinearMap.singularValues` of `B` acting `ℝ^{m₂} → ℝ^{m₁}`. -/
noncomputable def singularValue {m₁ m₂ : ℕ} (B : RealMatrix m₁ m₂) (j : ℕ) : ℝ :=
  (Matrix.toEuclideanLin B).singularValues j

/-- p. 20: for families `u_k ∈ ℝ^{m₁}`, `v_k ∈ ℝ^{m₂}`, the map
`𝒫 B = Σ_k ⟨u_k v_kᵀ, B⟩ u_k v_kᵀ`; when both families are orthonormal it is the orthogonal
projector (for the Frobenius inner product) onto the linear span of the `u_k v_kᵀ`. -/
noncomputable def spanProjector {m₁ m₂ : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → Fin m₁ → ℝ) (v : ι → Fin m₂ → ℝ) (B : RealMatrix m₁ m₂) : RealMatrix m₁ m₂ :=
  ∑ k, matrixInner (Matrix.vecMulVec (u k) (v k)) B • Matrix.vecMulVec (u k) (v k)

end KLTNuclear.RankRecovery


