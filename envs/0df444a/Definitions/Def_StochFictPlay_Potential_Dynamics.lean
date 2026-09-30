-- Prove2me | Definitions.Def_StochFictPlay_Potential_Dynamics
-- name    : StochFictPlay_Potential_Dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:07:27.653859+00:00
-- url     : https://prove2.me/theorems/129c255a-b9cf-4604-a6d2-fe4a49dba9b1
-- title:
--   Solutions, rest points, chain recurrence and strict Lyapunov functions of a dynamic on a compact set
-- statement:
--   Let $E$ be a real normed space, $X \subseteq E$ a (compact) state space and $F : E \to E$ a vector field, defining the dynamic $(D)\ \dot x = F(x)$.
--
--   1. **Solution.** A curve $\gamma : \mathbb R \to E$ is a (forward) solution of (D) in $X$ if $\gamma(t) \in X$ for all $t \ge 0$ and $\gamma'(t) = F(\gamma(t))$ for all $t \ge 0$, the derivative being taken within $[0,\infty)$ (so $\gamma$ is differentiable at every $t > 0$ and right-differentiable at $0$).
--   2. **Rest points.** $RP(D) = \{x \in X : F(x) = 0\}$.
--   3. **Chain recurrence.** A sequence $x = x_0, x_1, \dots, x_k = y$ in $X$ is an $\varepsilon$-chain from $x$ to $y$ if for each $i \in \{1,\dots,k\}$ there are a time $t_i \ge 1$ and a solution $\gamma$ with $\gamma(0) = x_{i-1}$ and $\|\gamma(t_i) - x_i\| < \varepsilon$. A point $x\in X$ is chain recurrent if for every $\varepsilon > 0$ there is an $\varepsilon$-chain of length $k\ge1$ from $x$ to itself; $CR(D)$ is the set of chain recurrent points.
--   4. **Strict Lyapunov function.** $\Lambda : E \to \mathbb R$ is a strict Lyapunov function for (D) on $X$ if $\Lambda$ increases strictly along every non-constant solution: $t \mapsto \Lambda(\gamma(t))$ is strictly increasing on $(0,\infty)$ for every solution $\gamma$ that is not constant on $[0,\infty)$.
--
--   These are the dynamical notions of §3.4 and §4 in which Propositions 4.1–4.3 are stated.
--
--   **Formalization Note** The paper writes chain recurrence with the semiflow $\varphi(t, x)$; since the dynamics considered have unique solutions, "the solution from $x_{i-1}$" is written as an existentially quantified solution. The derivative is taken within $[0,\infty)$, not within $[t,\infty)$ at each $t$: a mere right derivative at every $t$ would admit discontinuous curves that jump from one trajectory to another, which would make every point chain recurrent. The norm is the ambient sup norm; on a compact set the choice of norm does not change $CR$. Monotonicity in the Lyapunov definition is required on $(0,\infty)$ because the deterministic perturbations are defined only on the interior of the state space, which solutions of (PV) enter immediately.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, §3.4, pp. 12-13 (rest points, ω-limits, ε-chains, chain recurrence); p. 15 (strict Lyapunov function)

import Mathlib

namespace StochFictPlay.Potential

/-- A (forward) solution of the dynamic `ẋ = F(x)` in the compact state space `X`
(Hofbauer–Sandholm 2002, manuscript §3.4, p. 12): a curve `γ` that stays in `X` for `t ≥ 0`
and satisfies `γ'(t) = F (γ t)` on `[0, ∞)`, the derivative being taken within `[0, ∞)`. So `γ`
is differentiable (two-sided) at every `t > 0` and right-differentiable at `t = 0`; in
particular it is continuous on `[0, ∞)`. (A right derivative within `[t, ∞)` at each `t` alone
would not force continuity and would admit curves that jump between trajectories.) -/
def IsSolution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (X : Set E) (γ : ℝ → E) : Prop :=
  (∀ t : ℝ, 0 ≤ t → γ t ∈ X) ∧ ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt γ (F (γ t)) (Set.Ici 0) t

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
perturbations `V^α` are only defined on the interior of the state space, and solutions of (PV)
from boundary points enter the interior at once. -/
def IsStrictLyapunov {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : E → ℝ) (F : E → E) (X : Set E) : Prop :=
  ∀ γ : ℝ → E, IsSolution F X γ → (∃ t : ℝ, 0 ≤ t ∧ γ t ≠ γ 0) →
    StrictMonoOn (Λ ∘ γ) (Set.Ioi 0)

end StochFictPlay.Potential


