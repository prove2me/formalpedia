-- Prove2me | Definitions.Def_AdaOGD_ContinuousGame
-- name    : AdaOGD_ContinuousGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:23.068994+00:00
-- url     : https://prove2.me/theorems/a32b67e6-9a53-44cb-aaf0-cf1beded2551
-- title:
--   Continuous games, $\beta$-strong monotonicity, Nash equilibrium and the diameter bound
-- statement:
--   Let $\mathcal N=\{1,\dots,N\}$ be a set of agents. Agent $i$ chooses an **action** $x_i$ from a nonempty, convex and bounded set $\mathcal X_i\subseteq\mathbb R^{d_i}$, and the joint action is $x=(x_i;x_{-i})=(x_1,\dots,x_N)\in\mathcal X=\prod_{i=1}^N\mathcal X_i$. The joint space carries the Euclidean norm, $\|x\|^2=\sum_i\|x_i\|^2$, and the inner product $\langle x,y\rangle=\sum_i\langle x_i,y_i\rangle$.
--
--   A **continuous game** $\mathcal G=\{\mathcal N,\mathcal X,\{u_i\}_{i=1}^N\}$ has cost functions $u_i:\mathcal X\to\mathbb R$ such that
--
--   1. $u_i$ is continuous in $x$ on $\mathcal X$;
--   2. $x_i\mapsto u_i(x_i;x_{-i})$ is differentiable on $\mathcal X_i$ with gradient $v_i(x)=\nabla_{x_i}u_i(x_i;x_{-i})$, and the joint gradient profile $v=(v_1,\dots,v_N)$ is continuous on $\mathcal X$.
--
--   The game is **$\beta$-strongly monotone** if
--   $$
--   \langle x'-x,\,v(x')-v(x)\rangle\ \ge\ \beta\|x'-x\|^2\qquad\text{for all }x,x'\in\mathcal X .
--   $$
--   An action profile $x^\star\in\mathcal X$ is a **Nash equilibrium** if $u_i(x_i^\star;x_{-i}^\star)\le u_i(x_i;x_{-i}^\star)$ for all $x_i\in\mathcal X_i$ and every agent $i$. The action set has **diameter at most $D$** if $\|x-x'\|\le D$ for all $x,x'\in\mathcal X$.
--
--   These are the objects of §3.1 of the paper; every theorem of the mission is about such a game.
--
--   **Formalization Note** Agents are `Fin N`, agent $i$'s space is `EuclideanSpace ℝ (Fin (d i))`, and the joint space is `PiLp 2` (the $\ell^2$ product norm, not the sup norm). $u_i$ and $v$ are total functions on the joint space, constrained on $\mathcal X$ only; the gradient is a gradient within $\mathcal X_i$ (`HasGradientWithinAt`), so no differentiable extension outside $\mathcal X$ is assumed. Closedness of $\mathcal X_i$ is not part of the definition: theorems that need it assume $\mathcal X_i$ compact, as on p.1 of the paper. `update x i y` is the joint action $(y;x_{-i})$.
-- source:
--   Jordan, Lin & Zhou, Adaptive, Doubly Optimal No-Regret Learning in Strongly Monotone and Exp-Concave Games with Gradient Feedback, arXiv:2310.14085v4, §3.1, p.13, Definition 3.1 and feedback model item 2; p.14, Definitions 3.2 and 3.3

import Mathlib

namespace AdaOGD

open scoped InnerProductSpace

/-- The joint action space `ℝ^{d₁} × ⋯ × ℝ^{d_N}` of `N` agents with the Euclidean norm of the
product, `‖x‖² = ∑ᵢ ‖xᵢ‖²` (Jordan, Lin & Zhou, Adaptive, Doubly Optimal No-Regret Learning…,
arXiv:2310.14085v4, §3.1, p.13, "We let ‖ · ‖ denote the Euclidean norm").

**Formalization Note** The agents are `Fin N`; agent `i`'s space is `EuclideanSpace ℝ (Fin (d i))`;
the product carries the `ℓ²` norm (`PiLp 2`), not the sup norm of the plain Pi type. -/
abbrev Joint {N : ℕ} (d : Fin N → ℕ) : Type :=
  PiLp 2 (fun i : Fin N => EuclideanSpace ℝ (Fin (d i)))

/-- The joint action set `𝒳 = ∏ᵢ 𝒳ᵢ` (arXiv:2310.14085v4, Definition 3.1, p.13). -/
def jointSet {N : ℕ} {d : Fin N → ℕ} (X : ∀ i, Set (EuclideanSpace ℝ (Fin (d i)))) :
    Set (Joint d) :=
  {x | ∀ i, x i ∈ X i}

/-- The joint action `(y; x₋ᵢ)`: agent `i` plays `y` and every other agent keeps its action in `x`
(arXiv:2310.14085v4, notation `uᵢ(xᵢ; x₋ᵢ)`, p.13). -/
def update {N : ℕ} {d : Fin N → ℕ} (x : Joint d) (i : Fin N)
    (y : EuclideanSpace ℝ (Fin (d i))) : Joint d :=
  WithLp.toLp 2 (Function.update (WithLp.ofLp x) i y)

/-- A continuous game `𝒢 = {𝒩, 𝒳 = ∏ᵢ 𝒳ᵢ, {uᵢ}}` (Jordan, Lin & Zhou, arXiv:2310.14085v4,
Definition 3.1, p.13): `N` agents, a convex bounded action set `𝒳ᵢ ⊆ ℝ^{dᵢ}` for each agent, and
cost functions `uᵢ : 𝒳 → ℝ` such that (i) `uᵢ` is continuous in `x` and continuously differentiable
in `xᵢ`; (ii) the individual gradient `vᵢ(x) = ∇_{xᵢ} uᵢ(xᵢ; x₋ᵢ)` is continuous in `x`. The field
`v` is the joint gradient profile `v = (v₁, …, v_N)`.

**Formalization Note** `uᵢ` and `v` are total functions on the joint space; every condition is
imposed on `𝒳` only. The gradient is a gradient *within* `𝒳ᵢ` (`HasGradientWithinAt`), so no
differentiable extension of `uᵢ` outside `𝒳` is assumed; with (ii) this is continuous
differentiability in `xᵢ` on `𝒳ᵢ`. Each `𝒳ᵢ` is nonempty (the standing convention for action sets;
Algorithm 3 starts from `x¹ᵢ ∈ 𝒳ᵢ`). Closedness of `𝒳ᵢ` is not part of the definition; the theorems
that need it assume `IsCompact (X i)` (the paper's p.1 "convex and compact"). -/
structure ContinuousGame {N : ℕ} (d : Fin N → ℕ) where
  /-- The action set `𝒳ᵢ ⊆ ℝ^{dᵢ}` of agent `i`. -/
  X : ∀ i, Set (EuclideanSpace ℝ (Fin (d i)))
  /-- The cost function `uᵢ` of agent `i`. -/
  u : Fin N → Joint d → ℝ
  /-- The joint gradient profile `v(x) = (∇_{x₁}u₁(x), …, ∇_{x_N}u_N(x))`. -/
  v : Joint d → Joint d
  nonempty : ∀ i, (X i).Nonempty
  convex : ∀ i, Convex ℝ (X i)
  bounded : ∀ i, Bornology.IsBounded (X i)
  /-- (i) `uᵢ` is continuous in `x` on `𝒳`. -/
  u_continuous : ∀ i, ContinuousOn (u i) (jointSet X)
  /-- (i)–(ii) `vᵢ(x)` is the gradient of `xᵢ ↦ uᵢ(xᵢ; x₋ᵢ)` within `𝒳ᵢ`. -/
  hasGradient : ∀ x ∈ jointSet X, ∀ i,
    HasGradientWithinAt (fun y => u i (update x i y)) (v x i) (X i) (x i)
  /-- (ii) `v` is continuous in `x` on `𝒳`. -/
  v_continuous : ContinuousOn v (jointSet X)

variable {N : ℕ} {d : Fin N → ℕ}

/-- A continuous game is `β`-strongly monotone if `⟨x' − x, v(x') − v(x)⟩ ≥ β‖x' − x‖²` for all
`x, x' ∈ 𝒳` (arXiv:2310.14085v4, Definition 3.2, p.14).

**Formalization Note** The inequality is required on `𝒳` only; `β > 0` is a separate hypothesis
of every theorem. -/
def IsStronglyMonotone (G : ContinuousGame d) (β : ℝ) : Prop :=
  ∀ x ∈ jointSet G.X, ∀ x' ∈ jointSet G.X, β * ‖x' - x‖ ^ 2 ≤ ⟪x' - x, G.v x' - G.v x⟫_ℝ

/-- An action profile `x⋆ ∈ 𝒳` is a Nash equilibrium if `uᵢ(x⋆ᵢ; x⋆₋ᵢ) ≤ uᵢ(xᵢ; x⋆₋ᵢ)` for all
`xᵢ ∈ 𝒳ᵢ` and every agent `i` (arXiv:2310.14085v4, Definition 3.3, p.14). -/
def IsNash (G : ContinuousGame d) (xs : Joint d) : Prop :=
  xs ∈ jointSet G.X ∧ ∀ i, ∀ y ∈ G.X i, G.u i xs ≤ G.u i (update xs i y)

/-- The action set `𝒳` is bounded by a diameter `D`: `‖x − x'‖ ≤ D` for all `x, x' ∈ 𝒳`
(arXiv:2310.14085v4, p.13, feedback model item 2). -/
def DiamLe (G : ContinuousGame d) (D : ℝ) : Prop :=
  ∀ x ∈ jointSet G.X, ∀ x' ∈ jointSet G.X, ‖x - x'‖ ≤ D

end AdaOGD


