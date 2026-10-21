-- Prove2me | Definitions.Def_MatrixAnalytic_MatrixGeometric_QBD
-- name    : MatrixAnalytic_MatrixGeometric_QBD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:57.028172+00:00
-- url     : https://prove2.me/theorems/74545ba4-d3d3-4d1a-9ea8-8613c2d1efb3
-- title:
--   Homogeneous discrete-time QBD (6.1), levels ℓ(n), and nonnegative matrix algebra in ℝ≥0∞
-- statement:
--   Let $\iota$ be a set of **phases** (finite or countably infinite, $m = |\iota|$) and let $B, A_0, A_1, A_2$ be square matrices indexed by $\iota$. The **homogeneous quasi-birth-and-death process (QBD)** is the Markov chain on the states $(n,i)$, $n\ge0$ the **level** and $i\in\iota$ the phase, whose transition matrix is block-tridiagonal,
--   $$P = \begin{pmatrix} B & A_0 & 0 & 0 & \cdots\\ A_2 & A_1 & A_0 & 0 & \cdots\\ 0 & A_2 & A_1 & A_0 & \cdots\\ \vdots & & \ddots & \ddots & \ddots\end{pmatrix}:$$
--   from level $0$ the chain moves within level $0$ with probabilities $B$ and to level $1$ with probabilities $A_0$; from level $n\ge1$ it moves to level $n+1$, stays in level $n$, or moves to level $n-1$ with probabilities $A_0$, $A_1$, $A_2$ respectively; every other transition has probability zero.
--
--   The **level** $\ell(n)$ is the set $\{(n,i): i\in\iota\}$, and $\ell(0)\cup\cdots\cup\ell(n)$ is the set of states of level at most $n$.
--
--   For matrices with nonnegative entries indexed by $\iota$ the file also fixes the products $(vM)_j=\sum_i v_iM_{ij}$ and $(MM')_{ij}=\sum_kM_{ik}M'_{kj}$, the identity, the powers $M^0=I$, $M^{\nu+1}=M^\nu M$, and the book's convention
--   $$(I-M)^{-1} := \sum_{\nu\ge0}M^\nu,$$
--   all computed in the extended nonnegative reals, so that every sum exists and an infinite value is recorded as $+\infty$.
--
--   **Formalization Note** The phase set is an arbitrary type (the book allows $m=\infty$); levels are counted from $0$. The transition matrix is the function `qbdP B A₀ A₁ A₂` on `ℕ × ι`. A real matrix with nonnegative entries is read in `ℝ≥0∞` through `ENNReal.ofReal` (`ennMat`); `seriesInvE M` is the entrywise series $\sum_\nu M^\nu$ in `ℝ≥0∞`, the meaning the book gives to $(I-M)^{-1}$ on p. 109, never Lean's matrix inverse.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 129–130, Section 6.1, Eq. (6.1); convention (I − M)⁻¹ = Σ M^ν of p. 109 (Lemma 5.1.2)

import Mathlib

namespace MatrixAnalytic.MatrixGeometric

noncomputable section

open scoped ENNReal

/-!
The homogeneous discrete-time QBD of §6.1 of Latouche & Ramaswami (pp. 129–130): a Markov chain
on the states `(n, i)`, `n ≥ 0` the level and `i` the phase, with block-tridiagonal transition
matrix (6.1). The phase set is an arbitrary type `ι` (the book allows `m = ∞`); levels are
counted from `0`.

Matrices with nonnegative entries indexed by phases are also handled with values in `ℝ≥0∞`,
where every product and every series of nonnegative terms is defined (an infinite expectation
is `⊤`, never a junk value): `matMulE`, `matPowE`, and the book's convention
`(I − M)⁻¹ := Σ_{ν ≥ 0} M^ν` (p. 109) as `seriesInvE`.
-/

variable {ι : Type*}

/-- The transition matrix (6.1) of a homogeneous QBD with blocks `B, A₀, A₁, A₂`:
from level `0` the chain moves to level `0` with probabilities `B` and to level `1` with
probabilities `A₀`; from a level `n ≥ 1` it moves to level `n + 1` with probabilities `A₀`,
stays in level `n` with probabilities `A₁` and moves to level `n − 1` with probabilities `A₂`;
every other transition has probability `0`. -/
def qbdP (B A₀ A₁ A₂ : ι → ι → ℝ) : ℕ × ι → ℕ × ι → ℝ :=
  fun x y =>
    if x.1 = 0 then
      (if y.1 = 0 then B x.2 y.2 else if y.1 = 1 then A₀ x.2 y.2 else 0)
    else
      (if y.1 = x.1 + 1 then A₀ x.2 y.2
        else if y.1 = x.1 then A₁ x.2 y.2
        else if y.1 + 1 = x.1 then A₂ x.2 y.2
        else 0)

/-- The level `ℓ(n) = {(n, 1), …, (n, m)}`. -/
def level (n : ℕ) : Set (ℕ × ι) := {x | x.1 = n}

/-- The set of levels `ℓ(0) ∪ ⋯ ∪ ℓ(n)`. -/
def levelsUpTo (n : ℕ) : Set (ℕ × ι) := {x | x.1 ≤ n}

/-- A real matrix read entrywise in `ℝ≥0∞` (used for matrices with nonnegative entries). -/
def ennMat (A : ι → ι → ℝ) : ι → ι → ℝ≥0∞ := fun i j => ENNReal.ofReal (A i j)

/-- Row vector times matrix in `ℝ≥0∞`: `(vM)_j = Σ_i v_i M_{ij}`. -/
def vecMulE (v : ι → ℝ≥0∞) (M : ι → ι → ℝ≥0∞) : ι → ℝ≥0∞ :=
  fun j => ∑' i, v i * M i j

/-- Matrix product in `ℝ≥0∞`: `(MM')_{ij} = Σ_k M_{ik} M'_{kj}`. -/
def matMulE (M M' : ι → ι → ℝ≥0∞) : ι → ι → ℝ≥0∞ :=
  fun i j => ∑' k, M i k * M' k j

/-- The identity matrix in `ℝ≥0∞`. -/
def matOneE [DecidableEq ι] : ι → ι → ℝ≥0∞ := fun i j => if i = j then 1 else 0

/-- Matrix powers in `ℝ≥0∞`: `M⁰ = I`, `M^{ν+1} = M^ν M`. -/
def matPowE [DecidableEq ι] (M : ι → ι → ℝ≥0∞) : ℕ → ι → ι → ℝ≥0∞
  | 0 => matOneE
  | ν + 1 => matMulE (matPowE M ν) M

/-- The book's convention (p. 109) `(I − M)⁻¹ := Σ_{ν ≥ 0} M^ν`, entrywise in `ℝ≥0∞`
(an entry is `⊤` exactly when its series diverges). -/
def seriesInvE [DecidableEq ι] (M : ι → ι → ℝ≥0∞) : ι → ι → ℝ≥0∞ :=
  fun i j => ∑' ν : ℕ, matPowE M ν i j

end

end MatrixAnalytic.MatrixGeometric


