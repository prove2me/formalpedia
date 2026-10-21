-- Prove2me | Definitions.Def_MatrixAnalytic_FiniteQBD_QBD
-- name    : MatrixAnalytic_FiniteQBD_QBD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:45:24.508252+00:00
-- url     : https://prove2.me/theorems/f2fff76b-db31-44b4-b012-b4757988263f
-- title:
--   The finite QBD (10.2), its levels ℓ(n) and sets S_i, the blocks π_n, and the matrices C_i, U^{(i)}, R^{(i)} of (10.3), (10.8)–(10.9)
-- statement:
--   Fix $M \ge 1$ and a finite set of phases $\iota$. A **finite QBD** with levels $0, \dots, M$ is a Markov chain on the states $(n, j)$, $0 \le n \le M$, $j \in \iota$; the **level** $\ell(n)$ is the set of states $(n, j)$, and $S_i = \bigcup_{i \le n \le M} \ell(n)$. Given five real $\iota \times \iota$ matrices $P_{00}, A_0, A_1, A_2, P_{MM}$, its transition matrix is the block tridiagonal matrix (10.2)
--   $$P = \begin{bmatrix} P_{00} & A_0 & & & \\ A_2 & A_1 & A_0 & & \\ & \ddots & \ddots & \ddots & \\ & & A_2 & A_1 & A_0 \\ & & & A_2 & P_{MM}\end{bmatrix},$$
--   that is $P_{(n,j),(n+1,k)} = (A_0)_{jk}$, $P_{(n+1,j),(n,k)} = (A_2)_{jk}$, $P_{(n,j),(n,k)}$ equal to $(P_{00})_{jk}$ for $n = 0$, $(P_{MM})_{jk}$ for $n = M$ and $(A_1)_{jk}$ for $0 < n < M$, and all other entries $0$.
--
--   For a row vector $\pi$ on the states, $\pi_n = (\pi_{(n,j)})_{j \in \iota}$ is its block at level $n$.
--
--   The matrices of Lemma 10.1.1 and Theorem 10.1.3 are defined by the book's recursions:
--   $$C_0 = P_{00}, \qquad C_i = A_1 + A_2(I - C_{i-1})^{-1}A_0 \ (1 \le i \le M-1), \qquad C_M = P_{MM} + A_2(I - C_{M-1})^{-1}A_0,$$
--   $$U^{(M)} = P_{MM}, \qquad U^{(i)} = A_1 + A_0(I - U^{(i+1)})^{-1}A_2 \ (1 \le i \le M-1), \qquad U^{(0)} = P_{00} + A_0(I - U^{(1)})^{-1}A_2,$$
--   and $R^{(i)} = A_0(I - U^{(i)})^{-1}$ for $1 \le i \le M$.
--
--   **Formalization Note** The state space is `Fin (M + 1) × ι` (levels counted from $0$), with `ι` a `Fintype`. Row vectors act on the left (`vecMul`). The inverses are Mathlib's `Matrix` inverse, which returns $0$ on a singular matrix; nothing here asserts invertibility: the theorems of the mission conclude it (Lemma 10.1.1 for $I - C_i$, $0 \le i \le M-1$; Theorem 10.1.3 for $I - U^{(i)}$, $1 \le i \le M$) and give $C_i$, $U^{(i)}$ their probabilistic meaning as taboo path sums. $U^{(i)}$ is computed by recursion on $k = M - i$. Values of $C_i$, $U^{(i)}$, $R^{(i)}$ and $\pi_n$ outside $0 \le i, n \le M$ are never used. When $M = 1$ the block $A_1$ does not occur in (10.2).
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 222 (Eq. (10.2), S_i), p. 223 (Lemma 10.1.1, Eq. (10.3)), p. 224 (Theorem 10.1.3, Eqs. (10.8)–(10.9))

import Mathlib

namespace MatrixAnalytic.FiniteQBD

noncomputable section

/-!
The finite QBD of Chapter 10 of Latouche & Ramaswami (pp. 221–222, (10.2)), on the state space
`⋃_{0 ≤ n ≤ M} ℓ(n)`, encoded as `Fin (M + 1) × ι` (level `n`, phase `j`), with the phase set `ι`
finite. The transition matrix is block tridiagonal: `P₀₀` at level `0`, `A₁` at the interior
levels and `P_{MM}` at level `M` on the diagonal, `A₀` one level up and `A₂` one level down.
Also the level sets `ℓ(n)`, the sets `S_i = ⋃_{i ≤ n ≤ M} ℓ(n)`, the block `π_n` of a row vector,
and the matrices `C_i` of (10.3) and `U^{(i)}`, `R^{(i)}` of (10.8)–(10.9), defined by the
book's recursions with Mathlib's matrix inverse `⁻¹` (theorems assert the invertibility).
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The transition matrix (10.2) of a finite QBD with levels `0, …, M`:
`P_{(n,j),(n+1,k)} = (A₀)_{jk}`, `P_{(n+1,j),(n,k)} = (A₂)_{jk}`, `P_{(n,j),(n,k)}` equal to
`(P₀₀)_{jk}` for `n = 0`, `(P_{MM})_{jk}` for `n = M` and `(A₁)_{jk}` otherwise, and `0` when
the levels differ by more than one. -/
def qbdMatrix (M : ℕ) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) :
    Matrix (Fin (M + 1) × ι) (Fin (M + 1) × ι) ℝ :=
  fun x y =>
    if (y.1 : ℕ) = (x.1 : ℕ) + 1 then A0 x.2 y.2
    else if (x.1 : ℕ) = (y.1 : ℕ) + 1 then A2 x.2 y.2
    else if (x.1 : ℕ) = (y.1 : ℕ) then
      (if (x.1 : ℕ) = 0 then P00 else if (x.1 : ℕ) = M then PMM else A1) x.2 y.2
    else 0

/-- The level `ℓ(n) = {(n, j) : j}`. -/
def level (M : ℕ) (ι : Type*) (n : ℕ) : Set (Fin (M + 1) × ι) :=
  {x | (x.1 : ℕ) = n}

/-- `S_i = ⋃_{i ≤ n ≤ M} ℓ(n)`, the levels `i` and above (p. 222). -/
def levelsFrom (M : ℕ) (ι : Type*) (i : ℕ) : Set (Fin (M + 1) × ι) :=
  {x | i ≤ (x.1 : ℕ)}

/-- The block `π_n = (π_{(n,j)})_j` of a row vector `π` on the state space, for `0 ≤ n ≤ M`
(and `0` for `n > M`, a value never used). -/
def block {M : ℕ} (π : Fin (M + 1) × ι → ℝ) (n : ℕ) : ι → ℝ :=
  fun j => if h : n < M + 1 then π (⟨n, h⟩, j) else 0

/-- The matrices `C_i` of Lemma 10.1.1, (10.3): `C₀ = P₀₀`,
`C_i = A₁ + A₂(I − C_{i−1})⁻¹A₀` for `1 ≤ i ≤ M − 1`, `C_M = P_{MM} + A₂(I − C_{M−1})⁻¹A₀`.
Values at `i > M` are never used. -/
def Cmat (M : ℕ) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => P00
  | i + 1 => (if i + 1 = M then PMM else A1) + A2 * (1 - Cmat M P00 A0 A1 A2 PMM i)⁻¹ * A0

/-- The backward recursion (10.8)–(10.9) indexed by `k = M − i`: `k = 0` gives `U^{(M)} = P_{MM}`,
`k = M` gives `U^{(0)} = P₀₀ + A₀(I − U^{(1)})⁻¹A₂`, and `1 ≤ k ≤ M − 1` gives
`U^{(i)} = A₁ + A₀(I − U^{(i+1)})⁻¹A₂`. -/
def UmatAux (M : ℕ) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => PMM
  | k + 1 => (if k + 1 = M then P00 else A1) + A0 * (1 - UmatAux M P00 A0 A1 A2 PMM k)⁻¹ * A2

/-- The matrices `U^{(i)}`, `0 ≤ i ≤ M`, of Theorem 10.1.3, (10.8)–(10.9). -/
def Umat (M : ℕ) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) (i : ℕ) : Matrix ι ι ℝ :=
  UmatAux M P00 A0 A1 A2 PMM (M - i)

/-- The matrices `R^{(i)} = A₀(I − U^{(i)})⁻¹`, `1 ≤ i ≤ M`, of Theorem 10.1.3. -/
def Rmat (M : ℕ) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) (i : ℕ) : Matrix ι ι ℝ :=
  A0 * (1 - Umat M P00 A0 A1 A2 PMM i)⁻¹

end

end MatrixAnalytic.FiniteQBD


