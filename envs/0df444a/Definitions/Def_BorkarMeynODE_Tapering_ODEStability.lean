-- Prove2me | Definitions.Def_BorkarMeynODE_Tapering_ODEStability
-- name    : BorkarMeynODE_Tapering_ODEStability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:37:19.579613+00:00
-- url     : https://prove2.me/theorems/7505bfdf-46cd-46f2-af69-f7d768ce4a20
-- title:
--   Forward ODE solutions and (global, exponential) asymptotic stability of an equilibrium
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R^d$ and consider the autonomous ordinary differential equation
--   $$
--   \dot x(t) = f(x(t)), \qquad t \ge 0 .
--   $$
--   A **(forward) solution** is a curve $x:[0,\infty)\to\mathbb R^d$ that is differentiable on $[0,\infty)$ (one-sided at $t=0$) with $\dot x(t) = f(x(t))$ for every $t\ge 0$. For a point $x^*\in\mathbb R^d$ this file defines the following standard notions, each quantified over all forward solutions.
--
--   1. $x^*$ is an **equilibrium** if $f(x^*)=0$.
--   2. $x^*$ is **(Lyapunov) stable** if for every $\varepsilon>0$ there is $\delta>0$ such that $\|x(0)-x^*\|<\delta$ implies $\|x(t)-x^*\|<\varepsilon$ for all $t\ge0$.
--   3. $x^*$ is **asymptotically stable** if it is a stable equilibrium and there is $\delta>0$ such that every solution with $\|x(0)-x^*\|<\delta$ satisfies $x(t)\to x^*$ as $t\to\infty$.
--   4. $x^*$ is **globally asymptotically stable** if it is a stable equilibrium and every solution satisfies $x(t)\to x^*$.
--   5. $x^*$ is **globally exponentially asymptotically stable** if it is an equilibrium and there are constants $b$ and $\delta>0$ such that every solution satisfies
--   $$
--   \|x(t)-x^*\| \le b\, e^{-\delta t}\, \|x(0)-x^*\|, \qquad t\ge 0 .
--   $$
--
--   Borkar and Meyn use these notions without defining them: asymptotic stability of the origin for the fluid-limit ODE is part of assumption (A1), global asymptotic stability of $x^*$ for $\dot x = h(x)$ is the hypothesis of Theorem 2.2, and global exponential asymptotic stability is the conclusion of Lemma 4.1 (in the form the paper uses in its proof and in Lemma 2.6).
--
--   **Formalization Note** The state space is `EuclideanSpace ℝ (Fin d)`. A solution is a function `x : ℝ → ℝ^d` with `HasDerivWithinAt x (f (x t)) (Set.Ici 0) t` for every `t ≥ 0`; this makes `x` continuous on $[0,\infty)$ and leaves its values at negative times unconstrained (no notion looks at them). Every vector field of the paper is Lipschitz, so every initial condition has exactly one forward solution and the quantification over "all solutions" is neither vacuous nor ambiguous. Sanity checks (compiled separately): $\dot x=-x$ is globally exponentially and globally asymptotically stable at $0$, while $\dot x = 0$ is not asymptotically stable at $0$ when $d\ge1$.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 447, Eq. (1.2); p. 448, Eqs. (1.4)-(1.5); p. 449, Assumption (A1); p. 450, Theorem 2.2; p. 460, Lemma 4.1 (stability notions used there)

import Mathlib

namespace BorkarMeynODE.Tapering

open Filter Topology

/-- A forward solution on `[0, ∞)` of the autonomous ODE `ẋ(t) = f(x(t))` in `ℝ^d`
(Borkar–Meyn, (1.2), (1.4), (1.5)): at every `t ≥ 0` the curve `x` has derivative `f (x t)`
within `[0, ∞)`, i.e. a two-sided derivative for `t > 0` and a right derivative at `t = 0`.
This forces `x` to be continuous on `[0, ∞)`. Values at negative times are unconstrained;
every notion below looks only at `t ≥ 0`. For a Lipschitz `f` (all fields of the paper are
Lipschitz) every initial condition has exactly one such solution on `[0, ∞)`. -/
def IsODESolution {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : ℝ → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt x (f (x t)) (Set.Ici 0) t

/-- `xs` is an equilibrium of `ẋ = f(x)`: `f xs = 0`. -/
def IsEquilibrium {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) : Prop :=
  f xs = 0

/-- Lyapunov stability of `xs` for `ẋ = f(x)`: solutions that start close to `xs` stay
close to `xs` for all `t ≥ 0`. -/
def IsStableEquilibrium {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ → EuclideanSpace ℝ (Fin d),
    IsODESolution f x → ‖x 0 - xs‖ < δ → ∀ t : ℝ, 0 ≤ t → ‖x t - xs‖ < ε

/-- `xs` is an asymptotically stable equilibrium of `ẋ = f(x)` (assumption (A1)): it is an
equilibrium, it is Lyapunov stable, and every solution starting in some ball around `xs`
converges to `xs` as `t → ∞`. -/
def IsAsymptoticallyStable {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) : Prop :=
  IsEquilibrium f xs ∧ IsStableEquilibrium f xs ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ → EuclideanSpace ℝ (Fin d),
      IsODESolution f x → ‖x 0 - xs‖ < δ → Tendsto x atTop (𝓝 xs)

/-- `xs` is a globally asymptotically stable equilibrium of `ẋ = f(x)` (Theorem 2.2): it is
an equilibrium, it is Lyapunov stable, and every solution converges to `xs`. -/
def IsGloballyAsymptoticallyStable {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) : Prop :=
  IsEquilibrium f xs ∧ IsStableEquilibrium f xs ∧
    ∀ x : ℝ → EuclideanSpace ℝ (Fin d), IsODESolution f x → Tendsto x atTop (𝓝 xs)

/-- `xs` is a globally exponentially asymptotically stable equilibrium of `ẋ = f(x)`
(Lemma 4.1): it is an equilibrium and there are constants `b` and `δ > 0` such that every
solution satisfies `‖x(t) − xs‖ ≤ b e^{−δ t} ‖x(0) − xs‖` for all `t ≥ 0`. -/
def IsGloballyExpStable {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) : Prop :=
  IsEquilibrium f xs ∧ ∃ b δ : ℝ, 0 < δ ∧ ∀ x : ℝ → EuclideanSpace ℝ (Fin d),
    IsODESolution f x → ∀ t : ℝ, 0 ≤ t → ‖x t - xs‖ ≤ b * Real.exp (-δ * t) * ‖x 0 - xs‖

end BorkarMeynODE.Tapering


