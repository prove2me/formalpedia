-- Prove2me | Definitions.Def_MatrixAnalytic_Nonhomogeneous_Passage
-- name    : MatrixAnalytic_Nonhomogeneous_Passage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:08.072528+00:00
-- url     : https://prove2.me/theorems/b68ba6f1-a82c-4a96-8501-17dab4af13bb
-- title:
--   First-passage matrices G⁽ⁿ⁾, U⁽ⁿ⁾, R⁽ⁿ⁾ of a nonhomogeneous QBD as taboo path sums
-- statement:
--   Let $P$ be a transition matrix on the level–phase states $(n,i)$ of a nonhomogeneous QBD, and $\gamma(m) = \inf\{t\ge1 : X_t\in\ell(m)\}$ the first passage time to level $m$. All quantities below are sums, over finite trajectories, of products of one-step transition probabilities, with values in $[0,\infty]$.
--
--   1. The **first entrance** into a set $T$ from $x$ at $y\in T$ is the probability, starting from $X_0=x$, that the first time $t\ge1$ at which $X_t\in T$ is finite and $X_t = y$: the sum over $t\ge1$ of the weights of the trajectories $x=\omega_0,\omega_1,\dots,\omega_t=y$ with $\omega_1,\dots,\omega_{t-1}\notin T$.
--   2. The **expected number of visits** to $y$ before the first visit to $T$, starting from $x$: $\sum_{t\ge0}\mathrm P[X_t=y,\ X_1\notin T,\dots,X_t\notin T\mid X_0=x]$ (the visit at time $0$ counts when $y=x$).
--   3. For $n\ge1$, $G^{(n)}$ records the **first passage probabilities from $\ell(n)$ to $\ell(n-1)$**: $G^{(n)}_{ij} = \mathrm P[\gamma(n-1)<\infty\ \&\ X_{\gamma(n-1)} = (n-1,j)\mid X_0=(n,i)]$.
--   4. For $n\ge1$, $U^{(n)}$ records the **first return probabilities to $\ell(n)$ under taboo of the levels $\ell(0),\dots,\ell(n-1)$**: $U^{(n)}_{ij}$ is the probability, starting from $(n,i)$, that the first visit after time $0$ to $\ell(0)\cup\dots\cup\ell(n)$ happens, and happens at $(n,j)$.
--   5. For $n\ge1$, $R^{(n)}_{ij}$ is the **expected number of visits to $(n,j)$ between two visits to the levels $\ell(0)\cup\dots\cup\ell(n-1)$**, starting from $(n-1,i)$, that is, before the first return to $\ell(0)\cup\dots\cup\ell(n-1)$.
--
--   None of these matrices is defined through an equation of the chapter.
--
--   **Formalization Note** `matG P m` is $G^{(m+1)}$ and `matR P m` is $R^{(m+1)}$, both indexed by the lower of the two levels they connect ($m\ge0$); `matU P n` is $U^{(n)}$, meaningful for $n\ge1$ (at $n=0$ it is the matrix of first returns to $\ell(0)$, which no statement of the mission uses). Taking the taboo set $\ell(0)\cup\dots\cup\ell(n-1)$ in $R^{(n)}$ rather than $\ell(n-1)$ alone does not change the matrix, since the QBD cannot reach level $n$ from level $n-2$ without passing through level $n-1$; it is the set $T$ of Theorem 5.2.1 that the book's proof of Theorem 12.1.1 uses.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 260 (G⁽ⁿ⁾, U⁽ⁿ⁾ after Theorem 12.1.1; R⁽ⁿ⁾ in Theorem 12.1.1); γ(n) as recalled on p. 265

import Mathlib
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_QBD

namespace MatrixAnalytic.Nonhomogeneous

noncomputable section

open scoped ENNReal

/-!
The first-passage matrices `G^{(n)}`, `U^{(n)}`, `R^{(n)}` of §12.1 of Latouche & Ramaswami
(pp. 260–261) for a Markov chain with transition matrix `P` on the level–phase states
`Σ n : ℕ, ι n`. Every probability is a sum, over finite trajectories, of products of one-step
transition probabilities, and every expected number of visits is a sum over epochs of such
probabilities; all take values in `ℝ≥0∞`. None of them is defined through an equation of the
chapter.

Indexing: `matG P m` is the book's `G^{(m+1)}` and `matR P m` is the book's `R^{(m+1)}`
(both indexed by the lower of the two levels they connect, so that no subtraction of levels
occurs); `matU P n` is the book's `U^{(n)}` (meant for `n ≥ 1`).
-/

section General

variable {V : Type*} [DecidableEq V]

/-- The weight `P_{ω₀ω₁} ⋯ P_{ω_{t-1}ω_t}` of a trajectory of length `t`, in `ℝ≥0∞`: the
probability, starting from `ω₀`, that `X₁ = ω₁, …, X_t = ω_t`. -/
def pathWeightE (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ m : Fin t, ENNReal.ofReal (P (ω m.castSucc) (ω m.succ))

open Classical in
/-- First entrance into a set `T`: `P[σ < ∞ and X_σ = y | X_0 = x]` where
`σ = inf{t ≥ 1 : X_t ∈ T}`, i.e. the sum over `t ≥ 1` of the probabilities of the trajectories
`x = ω₀, ω₁, …, ω_t = y` with `y ∈ T` and `ω₁, …, ω_{t-1} ∉ T`. -/
def firstEntrance (P : V → V → ℝ) (T : Set V) (x y : V) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 2) → V,
    if ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
        ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
    then pathWeightE P ω else 0

open Classical in
/-- The expected number of visits to the state `y`, starting from `X₀ = x`, before the first
visit to the set `T` (after time `0`): `Σ_{t ≥ 0} P[X_t = y, X_1 ∉ T, …, X_t ∉ T | X_0 = x]`.
The visit at time `0` counts when `y = x`. -/
def expVisitsAvoid (P : V → V → ℝ) (T : Set V) (x y : V) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ T
    then pathWeightE P ω else 0

end General

variable {ι : ℕ → Type*} [∀ n, DecidableEq (ι n)]

/-- `G^{(m+1)}` (p. 260): the first passage probabilities from `ℓ(m + 1)` to `ℓ(m)`,
`G^{(m+1)}_{ij} = P[γ(m) < ∞ & X_{γ(m)} = ⟨m, j⟩ | X₀ = ⟨m + 1, i⟩]` with
`γ(m) = inf{t ≥ 1 : X_t ∈ ℓ(m)}`. -/
def matG (P : (Σ n, ι n) → (Σ n, ι n) → ℝ) (m : ℕ) : ι (m + 1) → ι m → ℝ≥0∞ :=
  fun i j => firstEntrance P (level m) ⟨m + 1, i⟩ ⟨m, j⟩

/-- `U^{(n)}` (p. 260): the first return probabilities to `ℓ(n)` under taboo of the levels
`ℓ(0), …, ℓ(n − 1)`: `U^{(n)}_{ij}` is the probability, starting from `⟨n, i⟩`, that the first
entrance after time `0` into `ℓ(0) ∪ ⋯ ∪ ℓ(n)` happens at `⟨n, j⟩`. Meant for `n ≥ 1`. -/
def matU (P : (Σ n, ι n) → (Σ n, ι n) → ℝ) (n : ℕ) : ι n → ι n → ℝ≥0∞ :=
  fun i j => firstEntrance P (levelsUpTo n) ⟨n, i⟩ ⟨n, j⟩

/-- `R^{(m+1)}` (p. 260, Theorem 12.1.1): `R^{(m+1)}_{ij}` is the expected number of visits to
`⟨m + 1, j⟩` between two visits to the levels `ℓ(0) ∪ ⋯ ∪ ℓ(m)`, starting from `⟨m, i⟩`, i.e.
before the first return to `ℓ(0) ∪ ⋯ ∪ ℓ(m)`. -/
def matR (P : (Σ n, ι n) → (Σ n, ι n) → ℝ) (m : ℕ) : ι m → ι (m + 1) → ℝ≥0∞ :=
  fun i j => expVisitsAvoid P (levelsUpTo m) ⟨m, i⟩ ⟨m + 1, j⟩

end

end MatrixAnalytic.Nonhomogeneous


