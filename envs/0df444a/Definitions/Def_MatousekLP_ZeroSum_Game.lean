-- Prove2me | Definitions.Def_MatousekLP_ZeroSum_Game
-- name    : MatousekLP_ZeroSum_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T12:04:54.171372+00:00
-- url     : https://prove2.me/theorems/cfeea68b-3a16-4a5b-a513-926133efed8a
-- title:
--   Zero-sum games: payoff, β, α, best responses, mixed Nash equilibria, worst-case optimality
-- statement:
--   A **zero-sum game** between Alice and Bob is given by a real $m \times n$ **payoff matrix** $M = (m_{ij})$: Alice has $m$ pure strategies, Bob has $n$, and $m_{ij}$ is Alice's gain (and Bob's loss) when Alice plays her $i$th and Bob his $j$th pure strategy. A **mixed strategy** of Alice is a probability vector
--   $$
--   \mathbf x = (x_1,\dots,x_m),\qquad \sum_{i=1}^m x_i = 1,\quad \mathbf x \ge \mathbf 0,
--   $$
--   and a mixed strategy of Bob is a vector $\mathbf y \in \mathbb R^n$ with $\sum_{j=1}^n y_j = 1$, $\mathbf y \ge \mathbf 0$. The **expected payoff** when $\mathbf x$ is played against $\mathbf y$ is $\mathbf x^T M \mathbf y = \sum_{i,j} m_{ij} x_i y_j$.
--
--   This file defines:
--
--   1. the worst-case payoff functions
--   $$
--   \beta(\mathbf x) = \min_{\mathbf y} \mathbf x^T M \mathbf y, \qquad \alpha(\mathbf y) = \max_{\mathbf x} \mathbf x^T M \mathbf y,
--   $$
--   the minimum and maximum being over all mixed strategies of Bob, respectively Alice;
--   2. **best responses**: a mixed strategy $\mathbf x_0$ of Alice is a best response against $\mathbf y$ if it maximizes $\mathbf x^T M \mathbf y$ over all mixed strategies $\mathbf x$; a mixed strategy $\mathbf y_0$ of Bob is a best response against $\mathbf x$ if it minimizes $\mathbf x^T M \mathbf y$ over all mixed strategies $\mathbf y$;
--   3. a **mixed Nash equilibrium** (Definition 8.1.1): a pair $(\tilde{\mathbf x}, \tilde{\mathbf y})$ of mixed strategies such that $\tilde{\mathbf x}$ is a best response against $\tilde{\mathbf y}$ and $\tilde{\mathbf y}$ is a best response against $\tilde{\mathbf x}$;
--   4. **worst-case optimality**: Alice's mixed strategy $\tilde{\mathbf x}$ is worst-case optimal if $\beta(\tilde{\mathbf x}) = \max_{\mathbf x} \beta(\mathbf x)$, and Bob's mixed strategy $\tilde{\mathbf y}$ is worst-case optimal if $\alpha(\tilde{\mathbf y}) = \min_{\mathbf y} \alpha(\mathbf y)$.
--
--   These are the objects of Section 8.1 of Matoušek–Gärtner, on which Lemma 8.1.2 and the minimax theorem (Theorem 8.1.3) are stated.
--
--   **Formalization Note** Strategies are indexed by `Fin m` and `Fin n` (the book's $x_1,\dots,x_m$ are `x 0, …, x (m-1)`); mixed strategies are the points of Mathlib's `stdSimplex ℝ (Fin m)`. The payoff is `x ⬝ᵥ (M *ᵥ y)`. $\beta(\mathbf x)$ is the real infimum `sInf` of the set $\{\mathbf x^T M \mathbf y : \mathbf y \text{ mixed}\}$ and $\alpha(\mathbf y)$ the real supremum `sSup` of $\{\mathbf x^T M \mathbf y : \mathbf x \text{ mixed}\}$; these sets are compact and, for $m, n \ge 1$ (the book's standing assumption, carried as a hypothesis by every theorem of the mission), nonempty, so the infimum and supremum are attained minimum and maximum. Best responses and worst-case optimal strategies are required to be mixed strategies. Definition 8.1.1 is encoded in its verbal form (mutual best responses); the book's formula $\beta(\tilde{\mathbf x}) = \tilde{\mathbf x}^T M \tilde{\mathbf y} = \alpha(\tilde{\mathbf y})$ is an equivalent reformulation.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, pp. 134–135 (§8.1: mixed strategies, expected payoff, best response, β and α), p. 135, Definition 8.1.1 (mixed Nash equilibrium), p. 135 (worst-case optimal)

import Mathlib

open Matrix

namespace MatousekLP.ZeroSum

/-- The expected payoff `xᵀ M y` (Alice's expected gain) when Alice plays the mixed strategy
`x` against Bob's mixed strategy `y`, for the `m × n` payoff matrix `M`
(Matoušek–Gärtner, §8.1, p. 134). Mixed strategies are points of `stdSimplex ℝ (Fin m)`
resp. `stdSimplex ℝ (Fin n)`: nonnegative vectors whose entries sum to `1`. -/
def payoff {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  x ⬝ᵥ (M *ᵥ y)

/-- `β(x) = min_y xᵀ M y`, the minimum over all mixed strategies `y` of Bob (p. 135),
written as the infimum of the image of Bob's simplex. The simplex is compact, and nonempty
when `n ≥ 1`, so this infimum is attained. -/
noncomputable def beta {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) : ℝ :=
  sInf ((fun y => payoff M x y) '' stdSimplex ℝ (Fin n))

/-- `α(y) = max_x xᵀ M y`, the maximum over all mixed strategies `x` of Alice (p. 135),
written as the supremum of the image of Alice's simplex. -/
noncomputable def alpha {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) : ℝ :=
  sSup ((fun x => payoff M x y) '' stdSimplex ℝ (Fin m))

/-- The mixed strategy `x₀` of Alice is a best response against Bob's mixed strategy `y`:
it maximizes `xᵀ M y` over all mixed strategies `x` of Alice (p. 134). -/
def IsBestResponseAlice {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ)
    (x₀ : Fin m → ℝ) : Prop :=
  x₀ ∈ stdSimplex ℝ (Fin m) ∧ ∀ x ∈ stdSimplex ℝ (Fin m), payoff M x y ≤ payoff M x₀ y

/-- The mixed strategy `y₀` of Bob is a best response against Alice's mixed strategy `x`:
it minimizes `xᵀ M y` over all mixed strategies `y` of Bob (p. 134). -/
def IsBestResponseBob {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ)
    (y₀ : Fin n → ℝ) : Prop :=
  y₀ ∈ stdSimplex ℝ (Fin n) ∧ ∀ y ∈ stdSimplex ℝ (Fin n), payoff M x y₀ ≤ payoff M x y

/-- Definition 8.1.1 (p. 135): a pair `(xt, yt)` of mixed strategies is a mixed Nash
equilibrium if `xt` is a best response against `yt` and `yt` is a best response against `xt`. -/
def IsMixedNash {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (xt : Fin m → ℝ) (yt : Fin n → ℝ) :
    Prop :=
  IsBestResponseAlice M yt xt ∧ IsBestResponseBob M xt yt

/-- Alice's mixed strategy `xt` is worst-case optimal if `β(xt) = max_x β(x)` (p. 135):
`xt` is a mixed strategy and `β(x) ≤ β(xt)` for every mixed strategy `x` of Alice. -/
def IsWorstCaseOptimalAlice {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (xt : Fin m → ℝ) :
    Prop :=
  xt ∈ stdSimplex ℝ (Fin m) ∧ ∀ x ∈ stdSimplex ℝ (Fin m), beta M x ≤ beta M xt

/-- Bob's mixed strategy `yt` is worst-case optimal if `α(yt) = min_y α(y)` (p. 135):
`yt` is a mixed strategy and `α(yt) ≤ α(y)` for every mixed strategy `y` of Bob. -/
def IsWorstCaseOptimalBob {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (yt : Fin n → ℝ) :
    Prop :=
  yt ∈ stdSimplex ℝ (Fin n) ∧ ∀ y ∈ stdSimplex ℝ (Fin n), alpha M yt ≤ alpha M y

end MatousekLP.ZeroSum


