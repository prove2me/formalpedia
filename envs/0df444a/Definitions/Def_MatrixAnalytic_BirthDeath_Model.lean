-- Prove2me | Definitions.Def_MatrixAnalytic_BirthDeath_Model
-- name    : MatrixAnalytic_BirthDeath_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:01.793441+00:00
-- url     : https://prove2.me/theorems/0767a526-ccb4-47c2-a8eb-b57b394fd8cd
-- title:
--   Discrete-time birth-and-death chains (4.5) and the spatially homogeneous chain (4.9)
-- statement:
--   A **discrete-time birth-and-death chain** is a Markov chain on the nonnegative integers $\{0,1,2,\dots\}$ that, from any state, moves only to an adjacent state or stays put. Its transition matrix (4.5) is tridiagonal,
--   $$P=\begin{bmatrix}a_{00}&a_{01}&0&0&\cdots\\ a_{10}&a_{11}&a_{12}&0&\cdots\\ 0&a_{21}&a_{22}&a_{23}&\cdots\\ \vdots&&\ddots&\ddots&\ddots\end{bmatrix}.$$
--   Throughout the chapter the chain is assumed irreducible, which for this matrix means $a_{i,i+1}>0$ and $a_{i+1,i}>0$ for every $i\ge0$. The predicate `IsBirthDeath P` says: $P$ is stochastic, $a_{ij}=0$ whenever $|i-j|>1$, $a_{i,i+1}>0$ and $a_{i+1,i}>0$ for all $i\ge0$.
--
--   The **spatially homogeneous** chain (4.9) has transition matrix
--   $$P=\begin{bmatrix}b_0&a_0&0&0&\cdots\\ a_2&a_1&a_0&0&\cdots\\ 0&a_2&a_1&a_0&\cdots\\ \vdots&&\ddots&\ddots&\ddots\end{bmatrix},$$
--   that is, $P(0,0)=b_0$, $P(0,1)=a_0$, and for $n\ge1$: $P(n,n-1)=a_2$, $P(n,n)=a_1$, $P(n,n+1)=a_0$, all other entries $0$. The predicate `IsHomParams b₀ a₀ a₁ a₂` collects the conditions under which this is an irreducible stochastic matrix: $a_0>0$, $a_2>0$, $a_1\ge0$, $b_0+a_0=1$ and $a_0+a_1+a_2=1$ (so $b_0 = 1-a_0 > 0$).
--
--   **Formalization Note** States are natural numbers and the transition matrix is a function `ℕ → ℕ → ℝ`, with `P i j` the book's $a_{ij}$. The standing irreducibility assumption of p. 87 is part of `IsBirthDeath` and of `IsHomParams`.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 87, Eq. (4.5) and the standing irreducibility assumption; p. 91, Eq. (4.9)

import Mathlib
import Definitions.Def_MatrixAnalytic_BirthDeath_Chain

namespace MatrixAnalytic.BirthDeath

/-- A discrete-time birth-and-death chain on `ℕ` with transition matrix (4.5), `P i j = a_{ij}`,
under the chapter's standing assumption of irreducibility (p. 87): `P` is stochastic, the chain
moves only to adjacent states (`a_{ij} = 0` when `|i - j| > 1`), and `a_{i,i+1} > 0`,
`a_{i+1,i} > 0` for every `i`. -/
structure IsBirthDeath (P : ℕ → ℕ → ℝ) : Prop where
  /-- `P` is a stochastic matrix on `ℕ`. -/
  stochastic : IsStochasticC P
  /-- Skip-free: only transitions to adjacent states (or staying put) have positive probability. -/
  skipFree : ∀ i j : ℕ, i + 1 < j ∨ j + 1 < i → P i j = 0
  /-- `a_{i,i+1} > 0` for all `i ≥ 0`. -/
  up_pos : ∀ i : ℕ, 0 < P i (i + 1)
  /-- `a_{i+1,i} > 0` for all `i ≥ 0`, i.e. `a_{n,n-1} > 0` for all `n ≥ 1`. -/
  down_pos : ∀ i : ℕ, 0 < P (i + 1) i

/-- The spatially homogeneous transition matrix (4.9): first row `(b₀, a₀, 0, …)`, and for
`n ≥ 1` row `n` has `a₂` in column `n - 1`, `a₁` in column `n`, `a₀` in column `n + 1`, and `0`
elsewhere. -/
def homP (b₀ a₀ a₁ a₂ : ℝ) : ℕ → ℕ → ℝ := fun i j =>
  if i = 0 then (if j = 0 then b₀ else if j = 1 then a₀ else 0)
  else if j + 1 = i then a₂ else if j = i then a₁ else if j = i + 1 then a₀ else 0

/-- The parameters of (4.9) make a stochastic matrix and the chain irreducible (the standing
assumption of p. 87): `a₀ > 0`, `a₂ > 0`, `a₁ ≥ 0`, and the rows sum to one, `b₀ + a₀ = 1` and
`a₀ + a₁ + a₂ = 1` (so `b₀ = 1 - a₀ > 0`). -/
structure IsHomParams (b₀ a₀ a₁ a₂ : ℝ) : Prop where
  a₀_pos : 0 < a₀
  a₁_nonneg : 0 ≤ a₁
  a₂_pos : 0 < a₂
  row_zero : b₀ + a₀ = 1
  row_sum : a₀ + a₁ + a₂ = 1

end MatrixAnalytic.BirthDeath


