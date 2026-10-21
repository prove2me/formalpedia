-- Prove2me | Definitions.Def_MatrixAnalytic_Nonhomogeneous_QBD
-- name    : MatrixAnalytic_Nonhomogeneous_QBD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:29.277982+00:00
-- url     : https://prove2.me/theorems/e90d3f40-21f4-4b1f-8db6-a1e542585805
-- title:
--   Nonhomogeneous QBD (12.1) with level-dependent rectangular blocks A₀⁽ⁿ⁾, A₁⁽ⁿ⁾, A₂⁽ⁿ⁾, its levels, and nonnegative matrix algebra with (I − M)⁻¹ := Σ M^ν
-- statement:
--   A **nonhomogeneous** (level-dependent) **QBD** is a Markov chain on the states $(n, i)$, where $n\ge0$ is the **level** and $i$ ranges over a countable, possibly infinite, set $\iota_n$ of **phases** of level $n$; different levels may have different sets of phases. Its transition matrix is block tridiagonal,
--   $$P = \begin{bmatrix} A_1^{(0)} & A_0^{(0)} & & & \\ A_2^{(1)} & A_1^{(1)} & A_0^{(1)} & & \\ & A_2^{(2)} & A_1^{(2)} & A_0^{(2)} & \\ & & \ddots & \ddots & \ddots \end{bmatrix}, \tag{12.1}$$
--   where $A_0^{(n)}$ (an $\iota_n\times\iota_{n+1}$ matrix) records the transitions from level $n$ to level $n+1$, $A_1^{(n)}$ (square, $\iota_n\times\iota_n$) those within level $n$, and $A_2^{(n)}$ ($\iota_n\times\iota_{n-1}$, for $n\ge1$) those from level $n$ to level $n-1$; every other transition has probability $0$. The **level** $\ell(n)$ is the set of states $\{(n,i): i\in\iota_n\}$, and $\ell(0)\cup\dots\cup\ell(n)$ is the set of states with level at most $n$.
--
--   Nonnegative matrices are multiplied with entries in $[0,\infty]$: $(MM')_{ij} = \sum_k M_{ik}M'_{kj}$ for rectangular $M$, $M'$ of matching dimensions, $(vM)_j = \sum_i v_iM_{ij}$ for a row vector $v$, $M^0 = I$, $M^{\nu+1} = M^\nu M$. Following the book's convention for substochastic matrices of any order,
--   $$(I - M)^{-1} := \sum_{\nu\ge0} M^\nu,$$
--   entrywise in $[0,\infty]$; an entry is $\infty$ exactly when its series diverges. For matrices $M^{(k)}$ from level $k-1$ to level $k$, the ordered product $\prod_{1\le k\le n}M^{(k)} = M^{(1)}M^{(2)}\cdots M^{(n)}$ is a matrix from level $0$ to level $n$; the empty product ($n=0$) is the identity matrix.
--
--   **Formalization Note** The state space is the dependent pair type $\Sigma\, n : \mathbb N,\ \iota_n$ for a family of phase types $\iota : \mathbb N \to$ `Type`, so the off-diagonal blocks are genuinely rectangular. The blocks are passed as `A₀ n` $=A_0^{(n)}$, `A₁ n` $=A_1^{(n)}$ and `A₂ m` $= A_2^{(m+1)}$ (from level $m+1$ to level $m$): the downward block is indexed by the lower of the two levels, so that no level $n-1$ with $n = 0$ is ever formed. A real matrix with nonnegative entries is read into $[0,\infty]$ entrywise (`ennMat`).
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 259, Eq. (12.1); empty product convention p. 262; convention (I − X)⁻¹ = Σ X^ν, p. 171 (Lemma 5.1.2, p. 109)

import Mathlib

namespace MatrixAnalytic.Nonhomogeneous

noncomputable section

open scoped ENNReal

/-!
The nonhomogeneous (level-dependent) discrete-time QBD (12.1) of Latouche & Ramaswami
(p. 259): a Markov chain on the states `⟨n, i⟩ : Σ n : ℕ, ι n`, `n ≥ 0` the level and
`i : ι n` a phase of level `n`. Different levels may have different (finite or countably
infinite) sets of phases, so the blocks off the main diagonal are rectangular.

Indexing of the blocks. `A₀ n : ι n → ι (n + 1) → ℝ` is the book's `A₀^{(n)}` (level `n` to
level `n + 1`) and `A₁ n : ι n → ι n → ℝ` is `A₁^{(n)}` (within level `n`), for `n ≥ 0`. The
block `A₂^{(n)}` (level `n` to level `n − 1`) exists for `n ≥ 1` only; it is
`A₂ (n - 1)`, i.e. `A₂ m : ι (m + 1) → ι m → ℝ` is the book's `A₂^{(m+1)}`.

Matrices with nonnegative entries are handled with values in `ℝ≥0∞`, where every product and
every series of nonnegative terms is defined (a divergent entry is `⊤`, never a junk value):
`matMulE` (rectangular), `matPowE`, the book's convention `(I − M)⁻¹ := Σ_{ν ≥ 0} M^ν`
(pp. 109, 171) as `seriesInvE`, and ordered products of rectangular matrices along the levels
as `levelProdE`.
-/

variable {ι : ℕ → Type*}

/-- The transition matrix (12.1) of a nonhomogeneous QBD: from a state `⟨n, i⟩` the chain
moves to `⟨n + 1, j⟩` with probability `A₀^{(n)}_{ij}`, to `⟨n, j⟩` with probability
`A₁^{(n)}_{ij}` and, when `n = m + 1 ≥ 1`, to `⟨m, j⟩` with probability `A₂^{(m+1)}_{ij}`
(the argument `A₂ m`); every other transition has probability `0`. In particular the level-`0`
row is `(A₁^{(0)}, A₀^{(0)})`. -/
def ndqbdP (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ) : (Σ n, ι n) → (Σ n, ι n) → ℝ :=
  fun x y =>
    if h : y.1 = x.1 + 1 then A₀ x.1 x.2 (cast (congrArg ι h) y.2)
    else if h : y.1 = x.1 then A₁ x.1 x.2 (cast (congrArg ι h) y.2)
    else if h : y.1 + 1 = x.1 then A₂ y.1 (cast (congrArg ι h.symm) x.2) y.2
    else 0

/-- The level `ℓ(n) = {⟨n, i⟩ : i ∈ ι n}`. -/
def level (n : ℕ) : Set (Σ k, ι k) := {x | x.1 = n}

/-- The levels `ℓ(0) ∪ ⋯ ∪ ℓ(n)`. -/
def levelsUpTo (n : ℕ) : Set (Σ k, ι k) := {x | x.1 ≤ n}

/-- A real (possibly rectangular) matrix read entrywise in `ℝ≥0∞` (used for matrices with
nonnegative entries). -/
def ennMat {α β : Type*} (A : α → β → ℝ) : α → β → ℝ≥0∞ := fun i j => ENNReal.ofReal (A i j)

/-- Product of (possibly rectangular) matrices in `ℝ≥0∞`: `(MM')_{ij} = Σ_k M_{ik} M'_{kj}`. -/
def matMulE {α β γ : Type*} (M : α → β → ℝ≥0∞) (M' : β → γ → ℝ≥0∞) : α → γ → ℝ≥0∞ :=
  fun i j => ∑' k, M i k * M' k j

/-- A row vector times a matrix in `ℝ≥0∞`: `(vM)_j = Σ_i v_i M_{ij}`. -/
def vecMulE {α β : Type*} (v : α → ℝ≥0∞) (M : α → β → ℝ≥0∞) : β → ℝ≥0∞ :=
  fun j => ∑' i, v i * M i j

/-- The identity matrix in `ℝ≥0∞`. -/
def matOneE {α : Type*} [DecidableEq α] : α → α → ℝ≥0∞ := fun i j => if i = j then 1 else 0

/-- Powers of a square matrix in `ℝ≥0∞`: `M⁰ = I`, `M^{ν+1} = M^ν M`. -/
def matPowE {α : Type*} [DecidableEq α] (M : α → α → ℝ≥0∞) : ℕ → α → α → ℝ≥0∞
  | 0 => matOneE
  | ν + 1 => matMulE (matPowE M ν) M

/-- The book's convention `(I − M)⁻¹ := Σ_{ν ≥ 0} M^ν` (p. 109; used for substochastic matrices
of any order, p. 171), entrywise in `ℝ≥0∞`. An entry is `⊤` exactly when its series diverges. -/
def seriesInvE {α : Type*} [DecidableEq α] (M : α → α → ℝ≥0∞) : α → α → ℝ≥0∞ :=
  fun i j => ∑' ν : ℕ, matPowE M ν i j

/-- The ordered product `∏_{1 ≤ k ≤ n} M^{(k)} = M^{(1)} M^{(2)} ⋯ M^{(n)}` of matrices
`M^{(k)}` from level `k − 1` to level `k`, given as `M (k - 1) : ι (k - 1) → ι k → ℝ≥0∞`; the
result is a matrix from level `0` to level `n`. The empty product (`n = 0`) is the identity
matrix (p. 262). -/
def levelProdE [∀ n, DecidableEq (ι n)] (M : (k : ℕ) → ι k → ι (k + 1) → ℝ≥0∞) :
    (n : ℕ) → ι 0 → ι n → ℝ≥0∞
  | 0 => matOneE
  | n + 1 => matMulE (levelProdE M n) (M n)

end

end MatrixAnalytic.Nonhomogeneous


