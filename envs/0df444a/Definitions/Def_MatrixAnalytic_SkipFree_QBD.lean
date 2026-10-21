-- Prove2me | Definitions.Def_MatrixAnalytic_SkipFree_QBD
-- name    : MatrixAnalytic_SkipFree_QBD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:42.412984+00:00
-- url     : https://prove2.me/theorems/8ca87601-e37e-4723-b949-12f84a284b85
-- title:
--   Homogeneous QBD transition matrix (13.3), levels, and nonnegative matrix algebra in ℝ≥0∞
-- statement:
--   Let $\kappa$ be a set of phases (possibly infinite) and $B, A_0, A_1, A_2$ real matrices indexed by $\kappa$. The **homogeneous QBD** with these blocks is the Markov chain on the states $(n,a)$, $n\ge0$ a level and $a\in\kappa$ a phase, with block-tridiagonal transition matrix
--   $$P=\begin{bmatrix}B&A_0\\A_2&A_1&A_0\\&A_2&A_1&\ddots\\&&\ddots&\ddots\end{bmatrix}:$$
--   from level $0$ the chain moves within level $0$ according to $B$ and to level $1$ according to $A_0$; from a level $n\ge1$ it moves to level $n+1$ according to $A_0$, stays in level $n$ according to $A_1$ and moves to level $n-1$ according to $A_2$; all other transitions have probability zero. The **level** $\ell(n)$ is the set of states with first coordinate $n$, and $\ell(0)\cup\dots\cup\ell(n)$ the set of states with level at most $n$.
--
--   For matrices with nonnegative entries the file also fixes the algebra used in the chapter, with values in $[0,\infty]$: the row-vector–matrix product $(vM)_j=\sum_i v_iM_{ij}$, the matrix product $(MM')_{ij}=\sum_kM_{ik}M'_{kj}$, the identity, powers $M^0=I$, $M^{\nu+1}=M^\nu M$, and the book's convention (p. 109)
--   $$(I-M)^{-1}:=\sum_{\nu\ge0}M^\nu$$
--   entrywise, an entry being $+\infty$ exactly when its series diverges. A real matrix is read in $[0,\infty]$ entrywise through $x\mapsto\max(x,0)$.
--
--   **Formalization Note** Levels are counted from $0$ as in the book. Computing products and series of nonnegative matrices in $[0,\infty]$ makes every such expression meaningful for infinitely many phases (the QBD embedding an M/G/1-type chain has phases $(d,j)$ with $d\ge0$) without summability side conditions; finiteness is stated as a conclusion wherever the book asserts it.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 270, Eq. (13.3); Section 6.1 (pp. 129–130); convention (I − M)⁻¹ = Σ Mᵛ, p. 109

import Mathlib

namespace MatrixAnalytic.SkipFree

noncomputable section

open scoped ENNReal

/-!
The homogeneous discrete-time QBD (13.3) of Latouche & Ramaswami (p. 270; Section 6.1, pp. 129–130):
a Markov chain on the states `(n, a)`, `n ≥ 0` the level and `a` the phase, with block-tridiagonal
transition matrix. The phase set is an arbitrary type `κ` (in Chapter 13 the phase of the QBD
embedding an M/G/1-type chain is two-dimensional, `(d, j)` with `d ≥ 0`, so there are infinitely
many phases); levels are counted from `0`.

Matrices with nonnegative entries indexed by phases are also handled with values in `ℝ≥0∞`,
where every product and every series of nonnegative terms is defined (an infinite value is `⊤`,
never a junk value): `matMulE`, `matPowE`, and the book's convention
`(I − M)⁻¹ := Σ_{ν ≥ 0} M^ν` (p. 109) as `seriesInvE`.
-/

variable {κ : Type*}

/-- The transition matrix of a homogeneous QBD with blocks `B, A₀, A₁, A₂` (as in (13.3)):
from level `0` the chain moves to level `0` with probabilities `B` and to level `1` with
probabilities `A₀`; from a level `n ≥ 1` it moves to level `n + 1` with probabilities `A₀`,
stays in level `n` with probabilities `A₁` and moves to level `n − 1` with probabilities `A₂`;
every other transition has probability `0`. -/
def qbdP (B A₀ A₁ A₂ : κ → κ → ℝ) : ℕ × κ → ℕ × κ → ℝ :=
  fun x y =>
    if x.1 = 0 then
      (if y.1 = 0 then B x.2 y.2 else if y.1 = 1 then A₀ x.2 y.2 else 0)
    else
      (if y.1 = x.1 + 1 then A₀ x.2 y.2
        else if y.1 = x.1 then A₁ x.2 y.2
        else if y.1 + 1 = x.1 then A₂ x.2 y.2
        else 0)

/-- The level `ℓ(n) = {(n, a) : a a phase}`. -/
def level (n : ℕ) : Set (ℕ × κ) := {x | x.1 = n}

/-- The set of levels `ℓ(0) ∪ ⋯ ∪ ℓ(n)`. -/
def levelsUpTo (n : ℕ) : Set (ℕ × κ) := {x | x.1 ≤ n}

/-- A real matrix read entrywise in `ℝ≥0∞` (used for matrices with nonnegative entries). -/
def ennMat (A : κ → κ → ℝ) : κ → κ → ℝ≥0∞ := fun i j => ENNReal.ofReal (A i j)

/-- Row vector times matrix in `ℝ≥0∞`: `(vM)_j = Σ_i v_i M_{ij}`. -/
def vecMulE (v : κ → ℝ≥0∞) (M : κ → κ → ℝ≥0∞) : κ → ℝ≥0∞ :=
  fun j => ∑' i, v i * M i j

/-- Matrix product in `ℝ≥0∞`: `(MM')_{ij} = Σ_k M_{ik} M'_{kj}`. -/
def matMulE (M M' : κ → κ → ℝ≥0∞) : κ → κ → ℝ≥0∞ :=
  fun i j => ∑' k, M i k * M' k j

/-- The identity matrix in `ℝ≥0∞`. -/
def matOneE [DecidableEq κ] : κ → κ → ℝ≥0∞ := fun i j => if i = j then 1 else 0

/-- Matrix powers in `ℝ≥0∞`: `M⁰ = I`, `M^{ν+1} = M^ν M`. -/
def matPowE [DecidableEq κ] (M : κ → κ → ℝ≥0∞) : ℕ → κ → κ → ℝ≥0∞
  | 0 => matOneE
  | ν + 1 => matMulE (matPowE M ν) M

/-- The book's convention (p. 109) `(I − M)⁻¹ := Σ_{ν ≥ 0} M^ν`, entrywise in `ℝ≥0∞`
(an entry is `⊤` exactly when its series diverges). -/
def seriesInvE [DecidableEq κ] (M : κ → κ → ℝ≥0∞) : κ → κ → ℝ≥0∞ :=
  fun i j => ∑' ν : ℕ, matPowE M ν i j

end

end MatrixAnalytic.SkipFree


