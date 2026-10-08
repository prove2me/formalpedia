-- Prove2me | Definitions.Def_LeiBR_Rand_Game
-- name    : LeiBR_Rand_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:43.364987+00:00
-- url     : https://prove2.me/theorems/cc9120dc-5366-422c-8d01-87fdd47ba06f
-- title:
--   §2.1 — $N$-player game on Euclidean strategy sets, Nash equilibrium, and the norm of the vector of block norms
-- statement:
--   There are $N$ players indexed by $i \in \mathcal N = \{1,\dots,N\}$. Player $i$ chooses a strategy $x_i$ in a set $X_i \subseteq \mathbb R^{n_i}$, and a **strategy profile** is $x = (x_1,\dots,x_N)$. Each player has a cost $f_i(x_i, x_{-i})$ that depends on its own strategy and on the rivals' strategies $x_{-i} = \{x_j\}_{j \ne i}$; player $i$ wants to minimize it. Write $X = \prod_i X_i$.
--
--   A profile $x^*$ is a **Nash equilibrium** (NE) if $x^* \in X$ and, for every player $i$,
--   $$f_i(x_i^*, x_{-i}^*) \le f_i(z, x_{-i}^*) \qquad \text{for all } z \in X_i,$$
--   that is, $x_i^*$ solves player $i$'s problem $\min_{x_i \in X_i} f_i(x_i, x_{-i}^*)$ and no player can lower its cost by deviating unilaterally.
--
--   For a profile $v = (v_1,\dots,v_N)$ the paper repeatedly uses the Euclidean norm of the vector of block norms,
--   $$\big\|(\|v_1\|,\dots,\|v_N\|)\big\| = \Big(\sum_{i=1}^N \|v_i\|^2\Big)^{1/2}.$$
--
--   These are the general game-theoretic objects on which the stochastic Nash game of the mission is built.
--
--   **Formalization Note** Players are `Fin N`, player $i$'s space is `EuclideanSpace ℝ (Fin (n i))` and a profile is a dependent function. Costs are functions of the whole profile; $f_i(z, y_{-i})$ is `f i (Function.update y i z)`. Lean's default norm on the product type is the sup norm, so the Euclidean norm of the block norms is written out as `blockNorm`.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 4, §2.1 (NE of (SNash)); p. 7, (9)/(12) (vector of block norms)

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame

namespace LeiBR.Rand

/-- An `N`-player game in which player `i` chooses `x_i` in a strategy set `X i ⊆ ℝ^{n_i}` and
minimizes a cost `f i` that depends on the whole profile; `f i (Function.update y i z)` is
`f_i(z, y_{-i})`. -/
structure Game (N : ℕ) (n : Fin N → ℕ) where
  /-- Strategy sets `X_i ⊆ ℝ^{n_i}`. -/
  X : ∀ i, Set (LeiBR.Sync.Strat n i)
  /-- Cost (payoff to be minimized) `f_i(x_i, x_{-i})`, as a function of the whole profile. -/
  f : Fin N → LeiBR.Sync.Profile n → ℝ

namespace Game

variable {N : ℕ} {n : Fin N → ℕ} (G : Game N n)

/-- `x ∈ X = ∏_i X_i`. -/
def Feasible (x : LeiBR.Sync.Profile n) : Prop := ∀ i, x i ∈ G.X i

/-- `x*` is a Nash equilibrium: it is feasible and, for every player `i`, `x*_i` minimizes
`f_i(·, x*_{-i})` over `X_i`. -/
def IsNE (x : LeiBR.Sync.Profile n) : Prop :=
  G.Feasible x ∧ ∀ i, ∀ z ∈ G.X i, G.f i x ≤ G.f i (Function.update x i z)

end Game

/-- The Euclidean norm of the vector of block norms,
`‖(‖v_1‖, …, ‖v_N‖)‖ = (∑_i ‖v_i‖²)^{1/2}`. -/
noncomputable def blockNorm {N : ℕ} {n : Fin N → ℕ} (v : LeiBR.Sync.Profile n) : ℝ :=
  Real.sqrt (∑ i, ‖v i‖ ^ 2)

end LeiBR.Rand


