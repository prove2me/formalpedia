-- Prove2me | Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
-- name    : MatrixAnalytic_MinimalSolutions_QBD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:26.594189+00:00
-- url     : https://prove2.me/theorems/074f26f5-6536-4086-a04f-4804a5aab4b2
-- title:
--   Homogeneous discrete-time QBD (8.1) with blocks B, A₀, A₁, A₂, its levels, and nonnegative matrix algebra with (I − M)⁻¹ := Σ M^ν
-- statement:
--   Let $\iota$ be a set of phases (finite or countably infinite; the book allows $m=\infty$) and let $B, A_0, A_1, A_2$ be real matrices indexed by $\iota$. The **homogeneous QBD** with these blocks is the Markov chain on the states $(n,i)$, $n\ge 0$ the level and $i\in\iota$ the phase, with block-tridiagonal transition matrix
--
--   $$P = \begin{bmatrix} B & A_0 & & \\ A_2 & A_1 & A_0 & \\ & A_2 & A_1 & \ddots \\ & & \ddots & \ddots \end{bmatrix}. \tag{8.1}$$
--
--   That is, from level $0$ the chain moves within level $0$ with probabilities $B$ and up to level $1$ with probabilities $A_0$; from a level $n\ge1$ it moves up with $A_0$, stays with $A_1$ and moves down with $A_2$; all other transitions have probability $0$. The **level** $\ell(n)$ is the set of states $(n,i)$, $i \in \iota$. The **level-reversed QBD** (8.25), with an arbitrary boundary block $\hat B_1$, is the QBD with blocks $\hat B_1, A_2, A_1, A_0$: up and down moves exchanged.
--
--   For matrices with nonnegative entries indexed by phases, the file also defines products $(MM')_{ij} = \sum_k M_{ik}M'_{kj}$, the identity, powers $M^0 = I$, $M^{\nu+1} = M^\nu M$, and the book's convention
--
--   $$(I - M)^{-1} := \sum_{\nu\ge0} M^\nu,$$
--
--   used for any nonnegative matrix, of finite or infinite order. A real matrix with nonnegative entries is read entrywise as such a matrix.
--
--   **Formalization Note** Nonnegative matrices are computed with entries in $[0,\infty]$, where every product and every series of nonnegative terms has a value: an entry of $\sum_\nu M^\nu$ is $\infty$ exactly when its series diverges, so "the series converges" is the statement that every entry is finite. Levels are counted from $0$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 165, Eq. (8.1) (= (6.1), pp. 129–130); level-reversed QBD Eq. (8.25), p. 176; convention (I − X)⁻¹ = Σ X^ν, p. 171 (Lemma 5.1.2, p. 109)

import Mathlib

namespace MatrixAnalytic.MinimalSolutions

noncomputable section

open scoped ENNReal

/-!
The homogeneous discrete-time QBD (8.1) = (6.1) of Latouche & Ramaswami (pp. 129–130, 165): a
Markov chain on the states `(n, i)`, `n ≥ 0` the level and `i` the phase, with block-tridiagonal
transition matrix. The phase set is an arbitrary type `ι` (the book allows `m = ∞`, p. 166);
levels are counted from `0`.

Matrices with nonnegative entries indexed by phases are also handled with values in `ℝ≥0∞`,
where every product and every series of nonnegative terms is defined (a divergent entry is `⊤`,
never a junk value): `matMulE`, `matPowE`, and the book's convention
`(I − M)⁻¹ := Σ_{ν ≥ 0} M^ν` (pp. 109, 171) as `seriesInvE`.
-/

variable {ι : Type*}

/-- The transition matrix (8.1) of a homogeneous QBD with blocks `B, A₀, A₁, A₂`:
from level `0` the chain moves to level `0` with probabilities `B` and to level `1` with
probabilities `A₀`; from a level `n ≥ 1` it moves to level `n + 1` with probabilities `A₀`,
stays in level `n` with probabilities `A₁` and moves to level `n − 1` with probabilities `A₂`;
every other transition has probability `0`. The level-reversed QBD (8.25), with boundary block
`B̂₁`, is `qbdP B̂₁ A₂ A₁ A₀` (`A₀` and `A₂` exchanged). -/
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

/-- A real matrix read entrywise in `ℝ≥0∞` (used for matrices with nonnegative entries). -/
def ennMat (A : ι → ι → ℝ) : ι → ι → ℝ≥0∞ := fun i j => ENNReal.ofReal (A i j)

/-- Matrix product in `ℝ≥0∞`: `(MM')_{ij} = Σ_k M_{ik} M'_{kj}`. -/
def matMulE (M M' : ι → ι → ℝ≥0∞) : ι → ι → ℝ≥0∞ :=
  fun i j => ∑' k, M i k * M' k j

/-- The identity matrix in `ℝ≥0∞`. -/
def matOneE [DecidableEq ι] : ι → ι → ℝ≥0∞ := fun i j => if i = j then 1 else 0

/-- Matrix powers in `ℝ≥0∞`: `M⁰ = I`, `M^{ν+1} = M^ν M`. -/
def matPowE [DecidableEq ι] (M : ι → ι → ℝ≥0∞) : ℕ → ι → ι → ℝ≥0∞
  | 0 => matOneE
  | ν + 1 => matMulE (matPowE M ν) M

/-- The book's convention `(I − M)⁻¹ := Σ_{ν ≥ 0} M^ν` (p. 109; "the same notation for any
substochastic matrix, even of infinite order", p. 171), entrywise in `ℝ≥0∞`. An entry is `⊤`
exactly when its series diverges, so "the series converges" is `∀ i j, seriesInvE M i j ≠ ⊤`. -/
def seriesInvE [DecidableEq ι] (M : ι → ι → ℝ≥0∞) : ι → ι → ℝ≥0∞ :=
  fun i j => ∑' ν : ℕ, matPowE M ν i j

end

end MatrixAnalytic.MinimalSolutions


