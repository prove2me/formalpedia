-- Prove2me | Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage
-- name    : MatrixAnalytic_MinimalSolutions_Passage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:52.141113+00:00
-- url     : https://prove2.me/theorems/d650df53-5ab6-4d7a-9783-52a6dce0925f
-- title:
--   First-passage matrices G, U, R, G(k), U(k), F(k) of a QBD as taboo path sums
-- statement:
--   Let $P$ be a transition matrix on the level–phase states $(n,i)$ and $\gamma(i) = \inf\{t\ge1 : X_t\in\ell(i)\}$ the first passage time to level $i$. Every quantity below is a probability (or an expected number of visits) for the chain $X$ with transition matrix $P$, computed as a sum over finite trajectories of products of one-step transition probabilities; all are matrices indexed by an initial phase $i$ and a final phase $j$.
--
--   1. The **first entrance** into a set $T$ at $y$ from $x$ is $\mathrm P[\sigma<\infty,\ X_\sigma = y \mid X_0 = x]$ with $\sigma=\inf\{t\ge1: X_t\in T\}$.
--   2. The **expected number of visits** to $y$ from $x$ before the first visit (after time $0$) to $T$ is $\sum_{t\ge0}\mathrm P[X_t = y,\ X_1,\dots,X_t\notin T\mid X_0=x]$.
--   3. $G_{ij} = \mathrm P[\gamma(0)<\infty\ \&\ X_{\gamma(0)} = (0,j)\mid X_0=(1,i)]$ (8.3).
--   4. $U_{ij} = \mathrm P[\gamma(1)<\gamma(0)\ \&\ \gamma(1)<\infty\ \&\ X_{\gamma(1)}=(1,j)\mid X_0=(1,i)]$ (8.4).
--   5. $R_{ij}$ is the expected number of visits to $(1,j)$ before the first return to $\ell(0)$, starting from $(0,i)$ (the matrix $R$ of Theorem 6.2.1, at level $0$).
--   6. For $k\ge1$, $U_{ij}(k) = \mathrm P[\gamma(1)<\gamma(0)\ \&\ \gamma(1)<\gamma(k+1)\ \&\ X_{\gamma(1)}=(1,j)\mid X_0=(1,i)]$ (8.10).
--   7. For $k\ge1$, $G_{ij}(k) = \mathrm P[\gamma(0)<\gamma(k+1)\ \&\ X_{\gamma(0)}=(0,j)\mid X_0=(1,i)]$ (8.11).
--   8. For $k\ge1$, $F_{ij}(k) = \mathrm P[\gamma(0)>\gamma(k+1)\ \&\ X_{\gamma(k+1)}=(k+1,j)\mid X_0=(k,i)]$, the first passage from $\ell(k)$ to $\ell(k+1)$ under taboo of $\ell(0)$ (8.22).
--
--   The matrix $\hat G$ of the level-reversed QBD is the matrix $G$ of item 3 for the transition matrix (8.25).
--
--   **Formalization Note** Each quantity is defined directly as a taboo path sum with values in $[0,\infty]$, never as the solution of an equation of the chapter. The probabilities are written as first entrances: $U(k)$ is the first entrance into $\ell(0)\cup\ell(1)\cup\ell(k+1)$ occurring in $\ell(1)$, $G(k)$ and $F(k)$ are the first entrance into $\ell(0)\cup\ell(k+1)$ occurring in $\ell(0)$, respectively $\ell(k+1)$. The book sets $G(0)=0$ by (8.7); the path sum is meant for $k\ge1$ only and the theorems use it only there.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 167, Eqs. (8.3)–(8.4); pp. 168–169, Eqs. (8.10)–(8.11); p. 176, Eq. (8.22); R as in Theorem 6.2.1, p. 131

import Mathlib
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD

namespace MatrixAnalytic.MinimalSolutions

noncomputable section

open scoped ENNReal

/-!
The first-passage quantities of §§8.1–8.2 of Latouche & Ramaswami (pp. 167–176) for a Markov
chain with transition matrix `P` on the level–phase states `ℕ × ι`, with
`γ(i) = inf{t ≥ 1 : X_t ∈ ℓ(i)}` (p. 167). Every probability is a sum, over finite trajectories,
of products of one-step transition probabilities, and every expected number of visits is a sum
over epochs of such probabilities; all take values in `ℝ≥0∞`. None of them is defined through an
equation of the chapter.
-/

variable {ι : Type*} [Countable ι] [DecidableEq ι]

/-- The weight `P_{ω₀ω₁} ⋯ P_{ω_{t-1}ω_t}` of a trajectory of length `t`, in `ℝ≥0∞`: the
probability, starting from `ω₀`, that `X₁ = ω₁, …, X_t = ω_t`. -/
def pathWeightE (P : ℕ × ι → ℕ × ι → ℝ) {t : ℕ} (ω : Fin (t + 1) → ℕ × ι) : ℝ≥0∞ :=
  ∏ m : Fin t, ENNReal.ofReal (P (ω m.castSucc) (ω m.succ))

open Classical in
/-- First entrance into a set `T`: `P[σ < ∞ and X_σ = y | X_0 = x]` where
`σ = inf{t ≥ 1 : X_t ∈ T}`, i.e. the sum over `t ≥ 1` of the probabilities of the trajectories
`x = ω₀, ω₁, …, ω_t = y` with `y ∈ T` and `ω₁, …, ω_{t-1} ∉ T`. -/
def firstEntrance (P : ℕ × ι → ℕ × ι → ℝ) (T : Set (ℕ × ι)) (x y : ℕ × ι) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 2) → ℕ × ι,
    if ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
        ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
    then pathWeightE P ω else 0

open Classical in
/-- The expected number of visits to the state `y`, starting from `X₀ = x`, before the first
visit to the set `T` (after time `0`): `Σ_{t ≥ 0} P[X_t = y, X_1 ∉ T, …, X_t ∉ T | X_0 = x]`.
The visit at time `0` counts when `y = x`. -/
def expVisitsAvoid (P : ℕ × ι → ℕ × ι → ℝ) (T : Set (ℕ × ι)) (x y : ℕ × ι) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 1) → ℕ × ι,
    if ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ T
    then pathWeightE P ω else 0

/-- `G` (8.3), p. 167: `G_{ij} = P[γ(0) < ∞ & X_{γ(0)} = (0, j) | X₀ = (1, i)]`, the probability,
starting from `(1, i)`, of reaching `ℓ(0)` in a finite time and doing so first in `(0, j)`. -/
def matG (P : ℕ × ι → ℕ × ι → ℝ) : ι → ι → ℝ≥0∞ :=
  fun i j => firstEntrance P (level 0) (1, i) (0, j)

/-- `U` (8.4), pp. 167–168: `U_{ij} = P[γ(1) < γ(0) & γ(1) < ∞ & X_{γ(1)} = (1, j) | X₀ = (1, i)]`,
i.e. the first entrance into `ℓ(0) ∪ ℓ(1)` after time `0` happens at `(1, j)`. -/
def matU (P : ℕ × ι → ℕ × ι → ℝ) : ι → ι → ℝ≥0∞ :=
  fun i j => firstEntrance P (level 0 ∪ level 1) (1, i) (1, j)

/-- `R` of Theorem 6.2.1 (p. 131), taken at level `0`: `R_{ij}` is the expected number of visits
to `(1, j)` before the first return to `ℓ(0)`, given that the process starts in `(0, i)`. -/
def matR (P : ℕ × ι → ℕ × ι → ℝ) : ι → ι → ℝ≥0∞ :=
  fun i j => expVisitsAvoid P (level 0) (0, i) (1, j)

/-- `U(k)` (8.10), p. 168:
`U_{ij}(k) = P[γ(1) < γ(0) & γ(1) < γ(k + 1) & X_{γ(1)} = (1, j) | X₀ = (1, i)]`, the first return
to `ℓ(1)` at `(1, j)` under taboo of `ℓ(0)` and `ℓ(k + 1)`, i.e. the first entrance into
`ℓ(0) ∪ ℓ(1) ∪ ℓ(k + 1)` happens at `(1, j)`. Meant for `k ≥ 1`. -/
def matUk (P : ℕ × ι → ℕ × ι → ℝ) (k : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => firstEntrance P (level 0 ∪ level 1 ∪ level (k + 1)) (1, i) (1, j)

/-- `G(k)` (8.11), p. 169: `G_{ij}(k) = P[γ(0) < γ(k + 1) & X_{γ(0)} = (0, j) | X₀ = (1, i)]`,
the first passage to `ℓ(0)` at `(0, j)` under taboo of `ℓ(k + 1)`, i.e. the first entrance into
`ℓ(0) ∪ ℓ(k + 1)` happens at `(0, j)`. Meant for `k ≥ 1` (the book sets `G(0) = 0` by (8.7)). -/
def matGk (P : ℕ × ι → ℕ × ι → ℝ) (k : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => firstEntrance P (level 0 ∪ level (k + 1)) (1, i) (0, j)

/-- `F(k) = F(k, k + 1)` (8.22), p. 176:
`F_{ij}(k) = P[γ(0) > γ(k + 1) & X_{γ(k+1)} = (k + 1, j) | X₀ = (k, i)]`, the first passage from
`ℓ(k)` to `ℓ(k + 1)` at `(k + 1, j)` under taboo of `ℓ(0)`, i.e. the first entrance into
`ℓ(0) ∪ ℓ(k + 1)` happens at `(k + 1, j)`. Meant for `k ≥ 1`. -/
def matF (P : ℕ × ι → ℕ × ι → ℝ) (k : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => firstEntrance P (level 0 ∪ level (k + 1)) (k, i) (k + 1, j)

end

end MatrixAnalytic.MinimalSolutions


