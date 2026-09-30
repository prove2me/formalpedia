-- Prove2me | Definitions.Def_StochFictPlay_Supermodular_Dynamics
-- name    : StochFictPlay_Supermodular_Dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:14:58.171978+00:00
-- url     : https://prove2.me/theorems/b529c39d-fcec-4ce6-ba64-f9d6ff7fd291
-- title:
--   Solutions, rest points and the chain recurrent set of a dynamic $\dot x = F(x)$
-- statement:
--   Let $E$ be a real normed space, $F : E \to E$ a vector field and $X \subseteq E$ a state space.
--
--   1. **Solution.** A curve $\gamma : \mathbb R \to E$ is a (forward) solution of $\dot x = F(x)$ in $X$ if $\gamma(t) \in X$ for all $t \ge 0$ and $\gamma$ has right derivative $F(\gamma(t))$ at every $t \ge 0$.
--   2. **Rest points.** $RP = \{x \in X : F(x) = 0\}$.
--   3. **Chain recurrent set.** A point $x \in X$ is chain recurrent if for every $\varepsilon > 0$ there is an $\varepsilon$-chain from $x$ to itself: points $x = x_0, x_1, \dots, x_k = x$ in $X$ with $k \ge 1$ such that for each $i < k$ some solution $\gamma$ with $\gamma(0) = x_i$ satisfies
--   $$\|\gamma(t_i) - x_{i+1}\| < \varepsilon \quad \text{for some } t_i \ge 1.$$
--   $CR$ denotes the set of chain recurrent points.
--
--   These are the notions of §3.4 used to describe the long-run behavior of stochastic approximation processes through their mean dynamics.
--
--   **Formalization Note** The semiflow $\varphi(t,x)$ of the paper is represented by solutions; for the dynamics of this mission solutions from each initial point are unique (the fields are $C^1$), so "some solution" is "the solution". The norm is the ambient one (the sup norm on products of $\mathbb R$); on a compact state space the choice of norm does not affect $CR$.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, §3.4, pp. 12-13 (the dynamic (D), RP(D), epsilon-chains and CR(D))

import Mathlib

namespace StochFictPlay.Supermodular

/-- A (forward) solution of the dynamic `ẋ = F(x)` in the compact state space `X`
(Hofbauer–Sandholm 2002, manuscript §3.4, p. 12): a curve `γ` that stays in `X` for `t ≥ 0`
and has right derivative `F (γ t)` at every `t ≥ 0`. -/
def IsSolution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (X : Set E) (γ : ℝ → E) : Prop :=
  (∀ t : ℝ, 0 ≤ t → γ t ∈ X) ∧ ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt γ (F (γ t)) (Set.Ici t) t

/-- The rest points `RP(D) = {x ∈ X : F(x) = 0}` (§3.4, p. 12). -/
def restPoints {E : Type*} [AddCommGroup E] (F : E → E) (X : Set E) : Set E :=
  {x | x ∈ X ∧ F x = 0}

/-- The chain recurrent set `CR(D)` (§3.4, p. 13): `x ∈ X` is chain recurrent if for every
`ε > 0` there is an `ε`-chain `x = x₀, x₁, …, x_k = x` (`k ≥ 1`) in `X` such that for each
`i < k` the solution starting at `x_i` is within `ε` of `x_{i+1}` at some time `t_i ≥ 1`.
The norm is the ambient one (the sup norm on a product of copies of `ℝ`). -/
def chainRecurrentSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (X : Set E) : Set E :=
  {x | x ∈ X ∧ ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, 1 ≤ k ∧ ∃ xs : Fin (k + 1) → E,
    xs 0 = x ∧ xs (Fin.last k) = x ∧ (∀ i, xs i ∈ X) ∧
    ∀ i : Fin k, ∃ t : ℝ, 1 ≤ t ∧ ∃ γ : ℝ → E, IsSolution F X γ ∧ γ 0 = xs i.castSucc ∧
      ‖γ t - xs i.succ‖ < ε}

end StochFictPlay.Supermodular


