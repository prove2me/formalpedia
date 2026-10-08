-- Prove2me | Definitions.Def_ExtensionComplexity_TSP_CorrelationMatrix
-- name    : ExtensionComplexity_TSP_CorrelationMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:47:33.546719+00:00
-- url     : https://prove2.me/theorems/35375487-98e8-48ee-a75c-318bcd2d0d62
-- title:
--   The $2^n\times 2^n$ matrix $M(n)_{ab}=(1-a^\top b)^2$ and its support
-- statement:
--   For $n$-bit strings $a,b\in\{0,1\}^n$ let $a^\top b$ be the number of positions $i$ with $a_i=b_i=1$. The $2^n\times 2^n$ matrix $M=M(n)$, with rows and columns indexed by $n$-bit strings, has entries
--
--   $$M_{ab}:=(1-a^\top b)^2 .$$
--
--   Its **support matrix** has a $1$ in position $(a,b)$ exactly when $M_{ab}\neq 0$, i.e. when $a^\top b\neq 1$. The file also fixes, for a bit string $b$, the $0/1$ vector $b\in\mathbb R^n$ and the rank-one binary symmetric matrix $bb^\top\in\mathbb R^{n\times n}$, and, for a bit string $a$, the coefficient matrix
--
--   $$2\,\mathrm{diag}(a)-aa^\top,\qquad (2\,\mathrm{diag}(a)-aa^\top)_{ij}=2[i=j]\,a_i-a_ia_j ,$$
--
--   of inequality (5).
--
--   $M(n)$ is the matrix whose support needs exponentially many rectangles to cover (Theorem 1); it appears as a submatrix of a slack matrix of the correlation polytope (Lemma 6), which is how the combinatorial bound becomes a geometric one.
--
--   **Formalization Note** Bit strings are `Fin n → Bool`. Matrices in $\mathbb R^{n\times n}$ are vectors indexed by ordered pairs `Fin n × Fin n`, so the Frobenius inner product $\langle X,Y\rangle$ (the component-wise inner product) is the dot product `⬝ᵥ` over pairs. The support predicate `suppM n a b` is defined from $M$ as `matM n a b ≠ 0`, as in the paper.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:8, §2 (M(n), eq. (4), suppmat(M), footnote 5); p. 17:12 (bb^T, inequality (5))

import Mathlib

namespace ExtensionComplexity.TSP

/-- `aᵀb` for `n`-bit strings `a, b ∈ {0,1}^n` (p. 17:8): the number of positions where both
strings have a one. Bit strings are `Fin n → Bool`. -/
def bitDot {n : ℕ} (a b : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => a i && b i).card

/-- The 0/1 vector in `ℝ^n` of an `n`-bit string. -/
def bitVec {n : ℕ} (a : Fin n → Bool) : Fin n → ℝ :=
  fun i => if a i then 1 else 0

/-- The rank-one binary symmetric matrix `bbᵀ ∈ ℝ^{n×n}` of a bit string `b` (p. 17:12), as a
vector indexed by ordered pairs `(i, j)`. -/
def outerBits {n : ℕ} (b : Fin n → Bool) : Fin n × Fin n → ℝ :=
  fun p => bitVec b p.1 * bitVec b p.2

/-- The coefficient matrix `2 diag(a) − aaᵀ` of inequality (5) (p. 17:8 eq. (4), p. 17:12),
indexed by ordered pairs `(i, j)`: its `(i, j)` entry is `2·[i = j]·a_i − a_i a_j`. Paired with
`x ∈ ℝ^{n×n}` by `⬝ᵥ` it gives the Frobenius inner product `⟨2 diag(a) − aaᵀ, x⟩` (footnote 5,
p. 17:8: the component-wise inner product of two matrices). -/
def corIneqCoeff {n : ℕ} (a : Fin n → Bool) : Fin n × Fin n → ℝ :=
  fun p => 2 * (if p.1 = p.2 then bitVec a p.1 else 0) - bitVec a p.1 * bitVec a p.2

/-- The `2^n × 2^n` matrix `M = M(n)` (p. 17:8, §2), rows and columns indexed by `n`-bit strings:
`M_ab := (1 − aᵀb)²`. -/
def matM (n : ℕ) (a b : Fin n → Bool) : ℝ :=
  (1 - (bitDot a b : ℝ)) ^ 2

/-- The support of `M(n)`: `suppmat(M)_ab = 1` iff `M_ab ≠ 0` (p. 17:8), as a predicate. -/
def suppM (n : ℕ) (a b : Fin n → Bool) : Prop :=
  matM n a b ≠ 0

end ExtensionComplexity.TSP


