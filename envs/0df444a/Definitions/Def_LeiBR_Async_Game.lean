-- Prove2me | Definitions.Def_LeiBR_Async_Game
-- name    : LeiBR_Async_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:36.532438+00:00
-- url     : https://prove2.me/theorems/98bb00f7-0ece-4dc7-b3e2-78c0b7f1a271
-- title:
--   The joint strategy set $X=\prod_i X_i$ and the partial gradient $\nabla_{x_i}$ on profiles
-- statement:
--   There are $N$ players. Player $i$ chooses a strategy $x_i$ in the Euclidean space $\mathbb R^{n_i}$, and a **strategy profile** is $x = (x_1,\dots,x_N)$. Each player has a feasible set $X_i \subseteq \mathbb R^{n_i}$, and the joint feasible set is the product
--   $$X = \prod_{i=1}^N X_i .$$
--   Player $i$ has a cost $f_i(x_i, x_{-i})$ depending on its own strategy and on the rivals' strategies $x_{-i} = (x_j)_{j\neq i}$; player $i$ minimizes it over $X_i$.
--
--   The Nash equilibrium of this game (a profile $x^* \in X$ from which no player can lower its cost by a unilateral deviation) is the shared definition `LeiBR.Sync.IsNashEq`, together with the strategy and profile types; this item adds only the two objects below.
--
--   For a function $g$ of the profile, $\nabla_{x_i} g(x) \in \mathbb R^{n_i}$ denotes the gradient at $x_i$ of $z \mapsto g(z, x_{-i})$.
--
--   These objects are the general substrate of the mission: every other definition and statement is written on them.
--
--   **Formalization Note** A cost $f_i$ is a function of the whole profile, and $f_i(z, x_{-i})$ is the profile $x$ with its $i$-th coordinate replaced by $z$ (`Function.update x i z`). Players are indexed by `Fin N`, and player $i$'s space is `EuclideanSpace ℝ (Fin (n i))`. The partial gradient is Mathlib's `gradient`, which is meaningful where $z \mapsto g(z, x_{-i})$ is differentiable.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 4, §2.1 (the players, X, X_{-i}, (SNash_i) and the definition of an NE)

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame

namespace LeiBR.Async

/-- The joint strategy set `X = ∏_i X_i` (§2.1, p. 4). -/
def profileSet {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i)) : Set (LeiBR.Sync.Profile n) :=
  Set.univ.pi X

/-- The partial gradient `∇_{x_i} g(x) ∈ ℝ^{n_i}`: the gradient at `x_i` of `z ↦ g(z, x_{-i})`. -/
noncomputable def partialGrad {N : ℕ} {n : Fin N → ℕ} (g : LeiBR.Sync.Profile n → ℝ) (i : Fin N)
    (x : LeiBR.Sync.Profile n) : LeiBR.Sync.Strat n i :=
  gradient (fun z : LeiBR.Sync.Strat n i => g (Function.update x i z)) (x i)

end LeiBR.Async


