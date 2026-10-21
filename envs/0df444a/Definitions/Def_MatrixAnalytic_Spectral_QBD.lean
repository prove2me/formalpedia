-- Prove2me | Definitions.Def_MatrixAnalytic_Spectral_QBD
-- name    : MatrixAnalytic_Spectral_QBD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:45:15.538975+00:00
-- url     : https://prove2.me/theorems/3d3e7f20-5bac-4e8f-abf7-7dfffcce6029
-- title:
--   The homogeneous QBD (6.1), its first-passage matrix G and its rate matrix R, as trajectory sums
-- statement:
--   A **homogeneous quasi-birth-and-death process (QBD)** is a Markov chain on the states $(n, i)$, where $n \ge 0$ is the **level** and $i$ the **phase**, ranging over a set of $m$ phases. Its transition matrix (6.1) is block tridiagonal with blocks $B, A_0, A_1, A_2$ (square matrices indexed by phases): from level $0$ the chain moves within level $0$ with probabilities $B$ and to level $1$ with probabilities $A_0$; from a level $n \ge 1$ it moves to level $n+1$ with probabilities $A_0$, stays in level $n$ with probabilities $A_1$ and moves to level $n - 1$ with probabilities $A_2$. The level $n$ is the set $\ell(n) = \{(n, i)\}$, and $A = A_0 + A_1 + A_2$.
--
--   The two matrices of Chapter 9 are defined by what they mean.
--
--   1. The **first-passage matrix** $G$, (6.6): $G_{ij}$ is the probability, starting from $(1, i)$, that the chain reaches the level $\ell(0)$ in a finite time and does so first in the state $(0, j)$. It is the sum over $k \ge 0$ of the weights (products of one-step transition probabilities) of the trajectories $(1, i) = \omega_0, \omega_1, \dots, \omega_k = (0, j)$ that do not visit $\ell(0)$ before time $k$.
--   2. The **rate matrix** $R$ (Theorem 6.2.1): $R_{ij}$ is the expected number of visits to the state $(1, j)$, starting from $(0, i)$, before the first return to $\ell(0)$, that is, the sum over $t \ge 0$ of the probabilities that $X_t = (1, j)$ and $X_1, \dots, X_t \notin \ell(0)$, given $X_0 = (0, i)$.
--
--   By homogeneity these are the matrices $G$ and $R$ of the passage between any two adjacent levels $n+1 \to n$ and $n \to n+1$, since the trajectories involved only use the blocks $A_0, A_1, A_2$.
--
--   **Formalization Note** The phase set is a type `ι`; the theorems of Chapter 9 make it finite. Probabilities and expectations are computed in $[0, \infty]$ (`ℝ≥0∞`), where every series of nonnegative terms has a value, and then read as complex matrices `matGc`, `matRc` through `toReal`. The entries of $G$ are probabilities, hence finite; every statement about $R$ also asserts that its entries are finite. Neither matrix is defined through an equation of Chapters 6 or 9.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 129–130, Eq. (6.1); p. 131, Theorem 6.2.1; p. 136, Eq. (6.6)

import Mathlib

namespace MatrixAnalytic.Spectral

noncomputable section

open scoped ENNReal

/-!
The homogeneous discrete-time QBD (6.1) of Latouche & Ramaswami (pp. 129–130), the object of
Chapter 9, with its first-passage matrix `G` ((6.6), p. 136) and rate matrix `R` (Theorem 6.2.1,
p. 131). The phase set is an arbitrary type `ι` here; Chapter 9 restricts to `m < ∞` (p. 204), and
the theorems add `[Fintype ι]`. Levels are counted from `0`.

`G` and `R` are defined by what they mean: `G_{ij}` is a sum over first-passage trajectories of
products of one-step transition probabilities, and `R_{ij}` an expected number of visits written as
a sum over taboo trajectories. Both are computed in `ℝ≥0∞`, where every series of nonnegative terms
has a value, and read in `ℂ` (`toReal`, then the coercion) for the spectral statements. Neither is
defined through an equation of Chapter 6 or 9.
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

/-- The phase matrix `A = A₀ + A₁ + A₂` (p. 152; irreducible by the standing restriction of
Chapter 9, p. 204). -/
def matA (A₀ A₁ A₂ : ι → ι → ℝ) : ι → ι → ℝ :=
  fun i j => A₀ i j + A₁ i j + A₂ i j

variable [Countable ι] [DecidableEq ι]

/-- The weight `P_{ω₀ω₁} ⋯ P_{ω_{t-1}ω_t}` of a trajectory of length `t`, in `ℝ≥0∞`: the
probability, starting from `ω₀`, that `X₁ = ω₁, …, X_t = ω_t`. -/
def pathWeightE (P : ℕ × ι → ℕ × ι → ℝ) {t : ℕ} (ω : Fin (t + 1) → ℕ × ι) : ℝ≥0∞ :=
  ∏ s : Fin t, ENNReal.ofReal (P (ω s.castSucc) (ω s.succ))

open Classical in
/-- `P[δ₀ = k, X_{δ₀} = (0, j) | X₀ = (1, i)]`, where `δ₀ = inf{t ≥ 0 : X_t ∈ ℓ(0)}` is the first
passage time to the level `0`: the sum of the weights of the trajectories
`(1, i) = ω₀, ω₁, …, ω_k = (0, j)` with `ω₀, …, ω_{k−1} ∉ ℓ(0)`. -/
def passageProb (P : ℕ × ι → ℕ × ι → ℝ) (k : ℕ) (i j : ι) : ℝ≥0∞ :=
  ∑' ω : Fin (k + 1) → ℕ × ι,
    if ω 0 = (1, i) ∧ ω (Fin.last k) = (0, j) ∧
        ∀ s : Fin (k + 1), s ≠ Fin.last k → ω s ∉ level 0
    then pathWeightE P ω else 0

/-- The first-passage matrix `G` of (6.6), p. 136: `G_{ij}` is the probability, starting from
`(1, i)`, of reaching the level `0` in a finite time and doing so first in `(0, j)`. For the
homogeneous QBD this is the matrix `G` of the passage from any level `n + 1` to `n`, since a
trajectory from `ℓ(1)` that avoids `ℓ(0)` only uses the blocks `A₀, A₁, A₂`. -/
def matG (P : ℕ × ι → ℕ × ι → ℝ) : ι → ι → ℝ≥0∞ :=
  fun i j => ∑' k : ℕ, passageProb P k i j

open Classical in
/-- The expected number of visits to the state `y`, starting from `X₀ = x`, before the first
visit to the set `T` (after time `0`): `Σ_{t ≥ 0} P[X_t = y, X_1 ∉ T, …, X_t ∉ T | X_0 = x]`.
The visit at time `0` counts when `y = x`. -/
def expVisitsAvoid (P : ℕ × ι → ℕ × ι → ℝ) (T : Set (ℕ × ι)) (x y : ℕ × ι) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 1) → ℕ × ι,
    if ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ s : Fin (t + 1), s ≠ 0 → ω s ∉ T
    then pathWeightE P ω else 0

/-- The rate matrix `R` (Theorem 6.2.1, p. 131, at `n = 0`): `R_{ij}` is the expected number of
visits to `(1, j)`, starting from `(0, i)`, before the first return to `ℓ(0)`. -/
def matR (P : ℕ × ι → ℕ × ι → ℝ) : ι → ι → ℝ≥0∞ :=
  fun i j => expVisitsAvoid P (level 0) (0, i) (1, j)

/-- `G` as a complex matrix (its entries are probabilities, hence finite). -/
def matGc (P : ℕ × ι → ℕ × ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => (((matG P i j).toReal : ℝ) : ℂ)

/-- `R` as a complex matrix. Its entries are read through `toReal`, so every statement about it
also asserts (or assumes, where the book has it) that they are finite. -/
def matRc (P : ℕ × ι → ℕ × ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => (((matR P i j).toReal : ℝ) : ℂ)

end

end MatrixAnalytic.Spectral


