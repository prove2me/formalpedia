-- Prove2me | Definitions.Def_IncentiveFinNet_Supplement_matK
-- name    : IncentiveFinNet_Supplement_matK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:29:38.409419+00:00
-- url     : https://prove2.me/theorems/e8e15553-6542-55cd-beb6-37be45fac68c
-- title:
--   The $n^2\times n^2$ matrices $K$, $L$, $L^{\dagger}$, $R$ and the vectorization $\mathrm{vec}$
-- statement:
--   For a network setting with matrices $Q_r$, define the $n^2\times n^2$ matrices of Theorems 4 and 9, with rows and columns indexed by the pairs $(i,j)$ (the position $(i-1)n+j$):
--
--   1. $K = \sum_{r=1}^n \bigl(e_re_r^{\top}\otimes Q_r + Q_r\otimes e_re_r^{\top}\bigr)$, where $(A\otimes B)_{(i,j),(k,\ell)} = A_{ik}B_{j\ell}$;
--   2. $L$ diagonal with $L_{(i,j),(i,j)} = Q_{i;j,j}+Q_{j;i,i}$;
--   3. $L^{\dagger}$, the pseudoinverse of $L$: diagonal with entries $1/L_{(i,j),(i,j)}$ where these are nonzero and $0$ elsewhere;
--   4. $R$ diagonal with $R_{(i,j),(i,j)} = s_{ij}$, where $s_{ij}=1$ if $\{i,j\}$ is a permitted edge ($j\in J_i$, including $i=j$ when $i\in J_i$) and $0$ otherwise.
--
--   The vectorization $\mathrm{vec}(X)\in\mathbb R^{n^2}$ stacks the columns of $X$: its entry at position $(i-1)n+j$ is $X_{ji}$.
--
--   These matrices describe the linear dynamics of the price increments in pairwise negotiations (Theorem 9) and its convergence (Theorem 4).
--
--   **Formalization Note** Vectors of length $n^2$ are functions on `Fin n × Fin n`, so `vecPair X (i, j) = X j i`. With this indexing Mathlib's `kroneckerMap (· * ·)` is the paper's $\otimes$ (Notation, p.7), and $\mathrm{vec}(AXB) = (B^{\top}\otimes A)\,\mathrm{vec}(X)$. $L^{\dagger}$ uses Lean's $0^{-1}=0$, which gives the Moore–Penrose pseudoinverse of a diagonal matrix.
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Theorem 4, p.15 (K, L, L†); Theorem 9, A.8, pp.38–39 (L, R, s_ij, L†, K); Notation, p.7 (⊗, vec)

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Q

open Matrix

namespace IncentiveFinNet.Supplement

variable {n : ℕ}

/-- `vec(X)`, the vectorization of `X` stacking its columns (arXiv:2212.06808v3, Notation, p.7).

**Formalization Note** Vectors of length `n²` are indexed by pairs `(i, j) : Fin n × Fin n`; the
pair `(i, j)` stands for the paper's position `(i − 1)n + j`. Column stacking puts `X_ji` at
position `(i − 1)n + j`, so `vecPair X (i, j) = X j i`. With this indexing Mathlib's
`Matrix.kroneckerMap (· * ·) A B` has entries `A_ik B_jℓ` at `((i, j), (k, ℓ))`, which is the
paper's `A ⊗ B` (p.7), and `vec(AXB) = (Bᵀ ⊗ A) vec(X)` holds. -/
def vecPair (X : Matrix (Fin n) (Fin n) ℝ) : Fin n × Fin n → ℝ :=
  fun p => X p.2 p.1

/-- `K := Σ_{r=1}^n e_r e_rᵀ ⊗ Q_r + Q_r ⊗ e_r e_rᵀ`, the `n² × n²` matrix of Theorem 4 (p.15) and
Theorem 9 (A.8, p.39). `e_r e_rᵀ` is `vecMulVec (Pi.single r 1) (Pi.single r 1)` and `⊗` is
`Matrix.kroneckerMap (· * ·)`. -/
noncomputable def matK (S : NetworkSetting n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  ∑ r, (Matrix.kroneckerMap (· * ·) (vecMulVec (Pi.single r 1) (Pi.single r 1)) (Q S r) +
    Matrix.kroneckerMap (· * ·) (Q S r) (vecMulVec (Pi.single r 1) (Pi.single r 1)))

/-- The diagonal matrix `L` of Theorems 4 and 9 (pp.15, 38): `L_{(i−1)n+j,(i−1)n+j} = Q_{i;j,j} + Q_{j;i,i}`. -/
noncomputable def matL (S : NetworkSetting n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  Matrix.diagonal fun p => (Q S p.1) p.2 p.2 + (Q S p.2) p.1 p.1

/-- `L†`, the (Moore–Penrose) pseudoinverse of the diagonal matrix `L` (pp.15, 38).

**Formalization Note** The pseudoinverse of a diagonal matrix is the diagonal matrix of the
entrywise inverses of its nonzero entries, with `0` where the entry is `0`; Lean's `x⁻¹` with
`0⁻¹ = 0` gives exactly that. -/
noncomputable def matLpinv (S : NetworkSetting n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  Matrix.diagonal fun p => ((Q S p.1) p.2 p.2 + (Q S p.2) p.1 p.1)⁻¹

/-- The diagonal matrix `R` of Theorem 9 (A.8, p.38): `R_{(i−1)n+j,(i−1)n+j} = s_ij`, with
`s_ij = 1` if `{i, j}` is a permitted edge (`j ∈ J_i`, self-loops included) and `0` otherwise. -/
noncomputable def matR (S : NetworkSetting n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  Matrix.diagonal fun p => if p.2 ∈ S.J p.1 then 1 else 0

end IncentiveFinNet.Supplement


