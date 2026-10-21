-- Prove2me | Definitions.Def_MatrixAnalytic_SkipFree_Passage
-- name    : MatrixAnalytic_SkipFree_Passage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:10.880672+00:00
-- url     : https://prove2.me/theorems/53df5d58-44ac-4235-b4a4-1062ae835457
-- title:
--   Taboo path sums — expected visits before a set, first-entrance probabilities, and the first-passage matrix G of a QBD
-- statement:
--   Let $P$ be a transition matrix on a state space $V$. The **weight** of a trajectory $\omega_0,\omega_1,\dots,\omega_t$ is $\prod_{s<t}P_{\omega_s\omega_{s+1}}$, the probability that the chain started at $\omega_0$ follows it.
--
--   1. For a set $T\subseteq V$ and states $x,y$, the **expected number of visits to $y$ before the first visit to $T$**, starting from $x$, is
--   $$\sum_{t\ge0}\mathrm P[X_t=y,\ X_1\notin T,\dots,X_t\notin T\mid X_0=x],$$
--   each probability being the total weight of the corresponding trajectories (the visit at time $0$ counts when $y=x$).
--   2. The **first-entrance probability** into $T$ at $y$, starting from $x$, is $\mathrm P[\sigma<\infty,\ X_\sigma=y\mid X_0=x]$ with $\sigma=\inf\{t\ge1:X_t\in T\}$: the total weight of the trajectories $x=\omega_0,\omega_1,\dots,\omega_t=y$, $t\ge1$, with $y\in T$ and $\omega_1,\dots,\omega_{t-1}\notin T$.
--   3. For a QBD and a level $n\ge1$, the **first-passage matrix** $G$ has entries $G_{ab}=\mathrm P[\tau<\infty,\ X_\tau=(n-1,b)\mid X_0=(n,a)]$, $\tau$ the first passage time from $\ell(n)$ to $\ell(n-1)$.
--
--   These are the probabilistic objects on which Chapter 13's matrices $G$, $H$ and $K$ are built.
--
--   **Formalization Note** All quantities take values in $[0,\infty]$ (an expected number of visits may be infinite) and are defined as sums over finite trajectories of products of one-step transition probabilities, never through an equation of the chapter. $G$ is meant for $n\ge1$; at $n=0$ the natural-number subtraction $n-1=0$ makes it meaningless and it is never used there.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 136, Eq. (6.6) (G); p. 131 (expected visits, Theorem 6.2.1); used in Section 13.1 (pp. 271–272) and Section 13.2 (p. 279)

import Mathlib
import Definitions.Def_MatrixAnalytic_SkipFree_QBD

namespace MatrixAnalytic.SkipFree

noncomputable section

open scoped ENNReal

/-!
Taboo quantities for a Markov chain with transition matrix `P` on a state space `V`: every
probability is a sum, over finite trajectories, of products of one-step transition
probabilities, and every expected number of visits is a sum over epochs of such probabilities;
all take values in `ℝ≥0∞`. None of them is defined through an equation of Chapter 13.
-/

/-- The weight `P_{ω₀ω₁} ⋯ P_{ω_{t-1}ω_t}` of a trajectory of length `t`, in `ℝ≥0∞`: the
probability, starting from `ω₀`, that `X₁ = ω₁, …, X_t = ω_t`. -/
def pathWeightE {V : Type*} (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ m : Fin t, ENNReal.ofReal (P (ω m.castSucc) (ω m.succ))

open Classical in
/-- The expected number of visits to the state `y`, starting from `X₀ = x`, before the first
visit to the set `T` (after time `0`): `Σ_{t ≥ 0} P[X_t = y, X_1 ∉ T, …, X_t ∉ T | X_0 = x]`.
The visit at time `0` counts when `y = x`. -/
def expVisitsAvoid {V : Type*} (P : V → V → ℝ) (T : Set V) (x y : V) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ T
    then pathWeightE P ω else 0

open Classical in
/-- First entrance into a set `T`: `P[σ < ∞ and X_σ = y | X_0 = x]` where
`σ = inf{t ≥ 1 : X_t ∈ T}`, i.e. the sum over `t ≥ 1` of the probabilities of the trajectories
`x = ω₀, ω₁, …, ω_t = y` with `y ∈ T` and `ω₁, …, ω_{t-1} ∉ T`. -/
def firstEntrance {V : Type*} (P : V → V → ℝ) (T : Set V) (x y : V) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 2) → V,
    if ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
        ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
    then pathWeightE P ω else 0

/-- The first-passage matrix `G` of a QBD at level `n` ((6.6), p. 136, used in Theorem 13.1.3):
`[matG P n]_{ab} = P[τ < ∞ and X_τ = (n − 1, b) | X₀ = (n, a)]`, `τ` the first passage time from
`ℓ(n)` to `ℓ(n − 1)`. Meant for `n ≥ 1`. -/
def matG {κ : Type*} (P : ℕ × κ → ℕ × κ → ℝ) (n : ℕ) : κ → κ → ℝ≥0∞ :=
  fun a b => firstEntrance P (level (n - 1)) (n, a) (n - 1, b)

end

end MatrixAnalytic.SkipFree


