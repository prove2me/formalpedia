-- Prove2me | Definitions.Def_MatrixAnalytic_MatrixGeometric_Passage
-- name    : MatrixAnalytic_MatrixGeometric_Passage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:29.22582+00:00
-- url     : https://prove2.me/theorems/c16472f7-4f6d-4a67-9cab-28b4cd2364e8
-- title:
--   The taboo matrices N, R, N_{1k}, U (6.5) and G (6.6) of a QBD as sums over taboo trajectories
-- statement:
--   Let $P$ be a transition matrix on the level–phase states $(n,i)$, $n\ge0$, $i\in\iota$, and write $\ell(n)$ for level $n$. Probabilities of events of the chain are sums, over finite trajectories, of products of one-step transition probabilities, and expected numbers of visits are sums over epochs of such probabilities, all valued in $[0,+\infty]$.
--
--   1. For a set $T$ of states, the **expected number of visits to $y$ before the first visit to $T$**, starting from $x$, is $\sum_{t\ge0}P[X_t=y,\ X_1\notin T,\dots,X_t\notin T\mid X_0=x]$ (the visit at time $0$ counts if $y=x$).
--   2. The **first entrance into $T$** at $y$, starting from $x$, is $P[\sigma<\infty,\ X_\sigma=y\mid X_0=x]$ with $\sigma=\inf\{t\ge1:X_t\in T\}$.
--   3. $N$ at level $n\ge1$: $N_{ij}$ is the expected number of visits to $(n,j)$, starting from $(n,i)$, before the first visit to $\ell(n-1)$.
--   4. $R$ at level $n\ge0$: $R_{ij}$ is the expected number of visits to $(n+1,j)$ before a return to $\ell(0)\cup\cdots\cup\ell(n)$, starting from $(n,i)$.
--   5. $N_{1k}$ for a fixed $n\ge0$ and $k\ge1$: $(N_{1k})_{ij}$ is the expected number of visits to $(n+k,j)$, starting from $(n+1,i)$, before the first visit to $\ell(0)\cup\cdots\cup\ell(n)$.
--   6. $U$ at level $n\ge1$, (6.5): with $\tau$ the first epoch of visit to $\ell(n-1)$ and $\theta$ the first epoch of return to $\ell(n)$, $$U_{ij}=P[\theta<\tau\text{ and }X_\theta=(n,j)\mid X_0=(n,i)].$$
--   7. $G$ at level $n\ge1$, (6.6): $$G_{ij}=P[\tau<\infty\text{ and }X_\tau=(n-1,j)\mid X_0=(n,i)].$$
--
--   These are the objects of which Chapter 6 proves the matrix-geometric property and the relations among $U$, $G$ and $R$; none of them is defined through any of those relations.
--
--   **Formalization Note** All quantities are valued in `ℝ≥0∞` and depend on the level `n` explicitly; their independence of `n` is a theorem (Theorem 6.2.1), not part of the definition. $U$ is encoded as the first entrance into $\ell(n)\cup\ell(n-1)$ occurring at $(n,j)$, which is the event $\{\theta<\tau, X_\theta=(n,j)\}$. For $n=0$ the definitions of $N$, $U$, $G$ use $\ell(0)$ in place of the nonexistent $\ell(-1)$ (natural-number subtraction) and are not meant; every theorem uses them only for $n\ge1$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 131 (Theorem 6.2.1: N and R), p. 132 (blocks N_{kk'}), p. 136 (Eqs. (6.5), (6.6))

import Mathlib
import Definitions.Def_MatrixAnalytic_MatrixGeometric_QBD

namespace MatrixAnalytic.MatrixGeometric

noncomputable section

open scoped ENNReal

/-!
The taboo quantities of §6.2 of Latouche & Ramaswami (pp. 131–137) for a Markov chain with
transition matrix `P` on the level–phase states `ℕ × ι`. Every probability is a sum, over finite
trajectories, of products of one-step transition probabilities, and every expected number of
visits is a sum over epochs of such probabilities; all take values in `ℝ≥0∞`. None of them is
defined through an equation of the chapter.
-/

variable {ι : Type*} [Countable ι] [DecidableEq ι]

/-- The weight `P_{ω₀ω₁} ⋯ P_{ω_{t-1}ω_t}` of a trajectory of length `t`, in `ℝ≥0∞`: the
probability, starting from `ω₀`, that `X₁ = ω₁, …, X_t = ω_t`. -/
def pathWeightE (P : ℕ × ι → ℕ × ι → ℝ) {t : ℕ} (ω : Fin (t + 1) → ℕ × ι) : ℝ≥0∞ :=
  ∏ m : Fin t, ENNReal.ofReal (P (ω m.castSucc) (ω m.succ))

open Classical in
/-- The expected number of visits to the state `y`, starting from `X₀ = x`, before the first
visit to the set `T` (after time `0`): `Σ_{t ≥ 0} P[X_t = y, X_1 ∉ T, …, X_t ∉ T | X_0 = x]`.
The visit at time `0` counts when `y = x`. -/
def expVisitsAvoid (P : ℕ × ι → ℕ × ι → ℝ) (T : Set (ℕ × ι)) (x y : ℕ × ι) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 1) → ℕ × ι,
    if ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ T
    then pathWeightE P ω else 0

open Classical in
/-- First entrance into a set `T`: `P[σ < ∞ and X_σ = y | X_0 = x]` where
`σ = inf{t ≥ 1 : X_t ∈ T}`, i.e. the sum over `t ≥ 1` of the probabilities of the trajectories
`x = ω₀, ω₁, …, ω_t = y` with `y ∈ T` and `ω₁, …, ω_{t-1} ∉ T`. -/
def firstEntrance (P : ℕ × ι → ℕ × ι → ℝ) (T : Set (ℕ × ι)) (x y : ℕ × ι) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 2) → ℕ × ι,
    if ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
        ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
    then pathWeightE P ω else 0

/-- `N` at level `n` (Theorem 6.2.1, p. 131): `[matN P n]_{ij}` is the expected number of visits
to `(n, j)`, starting from `(n, i)`, before the first visit to any of the states in `ℓ(n − 1)`.
Meant for `n ≥ 1`. -/
def matN (P : ℕ × ι → ℕ × ι → ℝ) (n : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => expVisitsAvoid P (level (n - 1)) (n, i) (n, j)

/-- `R` at level `n` (Theorem 6.2.1, p. 131): `[matR P n]_{ij}` is the expected number of visits
to `(n + 1, j)` before a return to `ℓ(0) ∪ ⋯ ∪ ℓ(n)`, given that the process starts in `(n, i)`. -/
def matR (P : ℕ × ι → ℕ × ι → ℝ) (n : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => expVisitsAvoid P (levelsUpTo n) (n, i) (n + 1, j)

/-- The block `N_{1k}` of `N_{T^c} = (I − P_{T^c})⁻¹` for the partition
`T = ℓ(0) ∪ ⋯ ∪ ℓ(n)`, `T^c = ℓ(n + 1) ∪ ℓ(n + 2) ∪ ⋯` (proof of Theorem 6.2.1, p. 132):
`[matNblock P n k]_{ij}` is the expected number of visits to `(n + k, j)`, starting from
`(n + 1, i)`, before the first visit to any of the states in `T`. Meant for `k ≥ 1`. -/
def matNblock (P : ℕ × ι → ℕ × ι → ℝ) (n k : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => expVisitsAvoid P (levelsUpTo n) (n + 1, i) (n + k, j)

/-- `U` at level `n` (6.5), p. 136: with `X₀ ∈ ℓ(n)`, `τ` the first epoch of visit to `ℓ(n − 1)`
and `θ` the first epoch of return to `ℓ(n)`, `U_{ij} = P[θ < τ and X_θ = (n, j) | X₀ = (n, i)]`,
i.e. the first entrance into `ℓ(n) ∪ ℓ(n − 1)` after time `0` happens at `(n, j)`.
Meant for `n ≥ 1`. -/
def matU (P : ℕ × ι → ℕ × ι → ℝ) (n : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => firstEntrance P (level n ∪ level (n - 1)) (n, i) (n, j)

/-- `G` at level `n` (6.6), p. 136: `G_{ij} = P[τ < ∞ and X_τ = (n − 1, j) | X₀ = (n, i)]`, the
probability, starting from `(n, i)`, of visiting `ℓ(n − 1)` in a finite time and doing so first
in `(n − 1, j)`. Meant for `n ≥ 1`. -/
def matG (P : ℕ × ι → ℕ × ι → ℝ) (n : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => firstEntrance P (level (n - 1)) (n, i) (n - 1, j)

end

end MatrixAnalytic.MatrixGeometric


