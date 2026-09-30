-- Prove2me | Definitions.Def_StochFictPlay_ZeroSumESS_Dynamics
-- name    : StochFictPlay_ZeroSumESS_Dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T09:10:33.122301+00:00
-- url     : https://prove2.me/theorems/a5f37b9a-7d45-4986-bfae-fd653f64e689
-- title:
--   Solutions, rest points, chain recurrence and strict Lyapunov functions of $\dot x = F(x)$
-- statement:
--   Let $E$ be a finite-dimensional normed real vector space, $F : E \to E$ a vector field and $X \subseteq E$ a (compact) state space for the dynamic $\dot x = F(x)$.
--
--   1. A **solution** is a curve $\gamma : \mathbb R \to E$ with $\gamma(t) \in X$ for all $t \ge 0$ and right derivative $\gamma'(t) = F(\gamma(t))$ at every $t \ge 0$.
--   2. The **rest points** are $RP = \{x \in X : F(x) = 0\}$.
--   3. $x \in X$ is **chain recurrent** if for every $\varepsilon > 0$ there are $k \ge 1$ and points $x = x_0, x_1, \dots, x_k = x$ of $X$ such that for each $i < k$ some solution $\gamma$ with $\gamma(0) = x_i$ satisfies $\|\gamma(t_i) - x_{i+1}\| < \varepsilon$ for some $t_i \ge 1$. $CR$ is the set of chain recurrent points.
--   4. $\Lambda : E \to \mathbb R$ is a **strict Lyapunov function** if along every solution that is not constant on $[0,\infty)$, $t \mapsto \Lambda(\gamma(t))$ is strictly increasing on $(0, \infty)$.
--
--   These are the notions of §3.4 and §4 in which the paper states the limit behaviour of the perturbed best response dynamics.
--
--   **Formalization Note** For the dynamics of this mission solutions are unique, so "some solution from $x_i$" is the paper's semiflow $\phi(t_i, x_i)$. The norm is the sup norm; on a compact set the chain recurrent set does not depend on the norm. Strict increase is required on $(0,\infty)$ rather than $[0,\infty)$ because the perturbations $V$ are defined only on the interior of the state space, which solutions from boundary points enter at once.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, pp. 12-13, §3.4 (semiflow, RP(D), ε-chains, CR(D)) and p. 15 (strict Lyapunov function)

import Mathlib

namespace StochFictPlay.ZeroSumESS

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
The norm is the ambient one (the sup norm on a product of `ℝ`'s). -/
def chainRecurrentSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (X : Set E) : Set E :=
  {x | x ∈ X ∧ ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, 1 ≤ k ∧ ∃ xs : Fin (k + 1) → E,
    xs 0 = x ∧ xs (Fin.last k) = x ∧ (∀ i, xs i ∈ X) ∧
    ∀ i : Fin k, ∃ t : ℝ, 1 ≤ t ∧ ∃ γ : ℝ → E, IsSolution F X γ ∧ γ 0 = xs i.castSucc ∧
      ‖γ t - xs i.succ‖ < ε}

/-- A strict Lyapunov function (manuscript p. 15): its value increases strictly along every
non-constant solution trajectory. Monotonicity is required on `(0, ∞)`: the deterministic
perturbations are only defined on the interior of the state space, and solutions of (PV) and
(SPV) from boundary points enter the interior at once. -/
def IsStrictLyapunov {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : E → ℝ) (F : E → E) (X : Set E) : Prop :=
  ∀ γ : ℝ → E, IsSolution F X γ → (∃ t : ℝ, 0 ≤ t ∧ γ t ≠ γ 0) →
    StrictMonoOn (Λ ∘ γ) (Set.Ioi 0)

end StochFictPlay.ZeroSumESS


