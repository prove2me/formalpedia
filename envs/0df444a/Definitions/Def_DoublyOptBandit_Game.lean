-- Prove2me | Definitions.Def_DoublyOptBandit_Game
-- name    : DoublyOptBandit_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:11.162455+00:00
-- url     : https://prove2.me/theorems/4c339d62-fb45-4d31-bfa5-11572c7e79cc
-- title:
--   Smooth and concave game, Nash equilibrium and $(\beta,\{\lambda_i\})$-strong monotonicity (Definitions 3.1, 3.2, 3.4)
-- statement:
--   There are $N$ players $i\in\{1,\dots,N\}$. Player $i$ chooses an action $x_i$ in a set $X_i\subseteq\mathbb R^{n_i}$, and the joint space $\mathbb R^{n_1}\times\cdots\times\mathbb R^{n_N}$ carries the Euclidean norm $\|x\|^2=\sum_i\|x_i\|^2$. Write $(y;x_{-i})$ for the profile in which player $i$ plays $y$ and the others play as in $x$.
--
--   A **smooth and concave game** $G=(\mathcal N, X=\prod_iX_i,\{u_i\})$ consists of convex compact sets $X_i\subseteq\mathbb R^{n_i}$ and reward functions $u_i:X\to\mathbb R$ such that
--
--   1. $u_i(x_i;x_{-i})$ is continuous in $x$ and concave in $x_i$ for each fixed $x_{-i}$;
--   2. $u_i(x_i;x_{-i})$ is continuously differentiable in $x_i$, and the individual reward gradient $v_i(x)=\nabla_iu_i(x_i;x_{-i})$ is Lipschitz continuous.
--
--   A profile $x^\star\in X$ is a (pure-strategy) **Nash equilibrium** if $u_i(x_i^\star;x_{-i}^\star)\ge u_i(x_i;x_{-i}^\star)$ for all $x_i\in X_i$ and all players $i$. The game is **$(\beta,\{\lambda_i\})$-strongly monotone** if
--   $$
--   \sum_{i}\lambda_i\langle x_i'-x_i,\ v_i(x')-v_i(x)\rangle\le-\beta\|x-x'\|^2\qquad\text{for all }x,x'\in X.
--   $$
--
--   These are the games in which the paper's multi-agent bandit algorithm converges in the last iterate to the Nash equilibrium.
--
--   **Formalization Note** Players are indexed by $\mathrm{Fin}\,N$ and the joint space is `PiLp 2`, so its norm is the Euclidean one, not the sup norm. Rewards and gradients are total functions, and every condition is imposed on $X$ only; the gradient is a gradient within $X_i$. The Lipschitz constant in (2) is existential. The sign conditions $\beta>0$, $\lambda_i\ge0$ of footnote 6 are stated by the theorems that need them.
-- source:
--   Ba, Lin, Zhang & Zhou, Doubly Optimal No-Regret Online Learning in Strongly Monotone Games with Bandit Feedback, arXiv:2112.02856v4, Definition 3.1, p.10; Definition 3.2, p.10; Definition 3.4 and footnote 6, p.11; joint norm §3.1, p.10

import Mathlib

open scoped InnerProductSpace

namespace DoublyOptBandit

/-- The joint action space `ℝ^{n₁} × ⋯ × ℝ^{n_N}` of `N` players with the Euclidean norm of the
product, `‖x‖² = Σᵢ ‖xᵢ‖²` (Ba, Lin, Zhang & Zhou, arXiv:2112.02856v4, §3.1, p.10: "We denote
∥·∥ as the Euclidean norm").

**Formalization Note** The players are `Fin N`; player `i`'s space is
`EuclideanSpace ℝ (Fin (n i))`; the product carries the `ℓ²` norm (`PiLp 2`), not the sup norm
of the plain Pi type. -/
abbrev Joint {N : ℕ} (n : Fin N → ℕ) : Type :=
  PiLp 2 (fun i : Fin N => EuclideanSpace ℝ (Fin (n i)))

/-- The joint action set `X = ∏ᵢ Xᵢ` (arXiv:2112.02856v4, Definition 3.1, p.10). -/
def jointSet {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (EuclideanSpace ℝ (Fin (n i)))) :
    Set (Joint n) :=
  {x | ∀ i, x i ∈ X i}

/-- The profile `(y; x₋ᵢ)`: player `i` plays `y`, every other player keeps its action in `x`
(arXiv:2112.02856v4, notation `uᵢ(xᵢ; x₋ᵢ)`, p.10). -/
def update {N : ℕ} {n : Fin N → ℕ} (x : Joint n) (i : Fin N)
    (y : EuclideanSpace ℝ (Fin (n i))) : Joint n :=
  WithLp.toLp 2 (Function.update (WithLp.ofLp x) i y)

/-- A **smooth and concave game** `G = (N, X = ∏ᵢ Xᵢ, {uᵢ})` (Ba, Lin, Zhang & Zhou,
arXiv:2112.02856v4, Definition 3.1, p.10): `N` players, a convex and compact action set
`Xᵢ ⊆ ℝ^{nᵢ}` for each player, and reward functions `uᵢ : X → ℝ` such that (i) `uᵢ(xᵢ; x₋ᵢ)` is
continuous in `x` and concave in `xᵢ` for every fixed `x₋ᵢ`; (ii) `uᵢ(xᵢ; x₋ᵢ)` is continuously
differentiable in `xᵢ` and the individual reward gradient `vᵢ(x) = ∇ᵢuᵢ(xᵢ; x₋ᵢ)` is Lipschitz
continuous. The field `v` is the profile `v = (v₁, …, v_N)`.

**Formalization Note** `uᵢ` and `v` are total functions on the joint space and every condition
is imposed on `X` only. The gradient is a gradient *within* `Xᵢ` (`HasGradientWithinAt`), so no
differentiable extension of `uᵢ` outside `X` is assumed; together with the Lipschitz continuity of
`v` on `X` this is continuous differentiability in `xᵢ` on `Xᵢ`. The Lipschitz constant of each
`vᵢ` is existentially quantified, as in the definition; theorems that need a named constant `ℓᵢ`
assume it separately. Lipschitz continuity is with respect to the Euclidean norm of the product. -/
structure SmoothConcaveGame {N : ℕ} (n : Fin N → ℕ) where
  /-- The action set `Xᵢ ⊆ ℝ^{nᵢ}` of player `i`. -/
  X : ∀ i, Set (EuclideanSpace ℝ (Fin (n i)))
  /-- The reward function `uᵢ` of player `i`. -/
  u : Fin N → Joint n → ℝ
  /-- The individual reward gradients `v(x) = (∇₁u₁(x), …, ∇_N u_N(x))`. -/
  v : Joint n → Joint n
  convex : ∀ i, Convex ℝ (X i)
  compact : ∀ i, IsCompact (X i)
  /-- (i) `uᵢ` is continuous in `x` on `X`. -/
  u_continuous : ∀ i, ContinuousOn (u i) (jointSet X)
  /-- (i) `uᵢ(xᵢ; x₋ᵢ)` is concave in `xᵢ ∈ Xᵢ` for every fixed `x₋ᵢ`. -/
  u_concave : ∀ i, ∀ x ∈ jointSet X, ConcaveOn ℝ (X i) (fun y => u i (update x i y))
  /-- (ii) `vᵢ(x)` is the gradient of `xᵢ ↦ uᵢ(xᵢ; x₋ᵢ)` within `Xᵢ`. -/
  hasGradient : ∀ i, ∀ x ∈ jointSet X,
    HasGradientWithinAt (fun y => u i (update x i y)) (v x i) (X i) (x i)
  /-- (ii) each `vᵢ` is Lipschitz continuous on `X`. -/
  v_lipschitz : ∀ i, ∃ K : NNReal, LipschitzOnWith K (fun x => v x i) (jointSet X)

variable {N : ℕ} {n : Fin N → ℕ}

/-- A (pure-strategy) **Nash equilibrium**: `x⋆ ∈ X` with `uᵢ(x⋆ᵢ; x⋆₋ᵢ) ≥ uᵢ(xᵢ; x⋆₋ᵢ)` for all
`xᵢ ∈ Xᵢ` and every player `i` (arXiv:2112.02856v4, Definition 3.2, p.10; rewards are
maximized). -/
def IsNash (G : SmoothConcaveGame n) (xs : Joint n) : Prop :=
  xs ∈ jointSet G.X ∧ ∀ i, ∀ y ∈ G.X i, G.u i (update xs i y) ≤ G.u i xs

/-- The game is **`(β, {λᵢ})`-strongly monotone** if
`Σᵢ λᵢ⟨x′ᵢ − xᵢ, vᵢ(x′) − vᵢ(x)⟩ ≤ −β‖x − x′‖²` for all `x, x′ ∈ X`
(arXiv:2112.02856v4, Definition 3.4, p.11).

**Formalization Note** `‖x − x′‖` is the Euclidean norm of the product (`PiLp 2`). Footnote 6
("we assume that β > 0 and λᵢ ≥ 0") is not part of the predicate; theorems state the sign
conditions on `β` and `λ` they need. -/
def IsStronglyMonotone (G : SmoothConcaveGame n) (β : ℝ) (lam : Fin N → ℝ) : Prop :=
  ∀ x ∈ jointSet G.X, ∀ x' ∈ jointSet G.X,
    ∑ i, lam i * ⟪x' i - x i, G.v x' i - G.v x i⟫_ℝ ≤ -β * ‖x - x'‖ ^ 2

end DoublyOptBandit


