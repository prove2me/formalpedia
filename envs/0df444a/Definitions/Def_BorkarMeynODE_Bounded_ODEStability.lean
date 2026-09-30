-- Prove2me | Definitions.Def_BorkarMeynODE_Bounded_ODEStability
-- name    : BorkarMeynODE_Bounded_ODEStability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:46:25.717475+00:00
-- url     : https://prove2.me/theorems/155c69ea-ea35-4334-b099-5af2079808e9
-- title:
--   Forward ODE solutions, stability notions and the scaled field $h_r$
-- statement:
--   Let $E$ be a real normed space and $f : E \to E$ a vector field. This file fixes the ODE vocabulary used throughout the mission.
--
--   1. A **forward solution** of $\dot x = f(x)$ is a map $x : \mathbb{R} \to E$ that is continuous on $[0,\infty)$ and has right derivative $f(x(t))$ at every $t \ge 0$.
--   2. A point $x^*$ is an **equilibrium** if $f(x^*) = 0$.
--   3. It is **(Lyapunov) stable** if for every $\varepsilon > 0$ there is $\delta > 0$ such that every forward solution with $\|x(0) - x^*\| < \delta$ satisfies $\|x(t) - x^*\| < \varepsilon$ for all $t \ge 0$.
--   4. It is **asymptotically stable** if it is a stable equilibrium and there is $\delta > 0$ such that every forward solution with $\|x(0) - x^*\| < \delta$ converges to $x^*$ as $t \to \infty$.
--   5. It is **globally asymptotically stable** if it is a stable equilibrium and every forward solution converges to $x^*$.
--   6. It is **globally exponentially asymptotically stable** if it is an equilibrium and there are constants $b$ and $\delta > 0$ such that every forward solution satisfies
--   $$\|x(t) - x^*\| \le b\, e^{-\delta t}\, \|x(0) - x^*\|, \qquad t \ge 0.$$
--   7. For $r > 0$ the **scaled field** (1.3) is $h_r(x) = r^{-1} h(r x)$.
--
--   The paper uses these standard notions without defining them: asymptotic stability of the origin for the fluid ODE (1.5) in assumption (A1), global asymptotic stability of $x^*$ for (1.2) and global exponential stability of $x^*$ in Theorem 2.3. The exponential form is the one used in the proof of Theorem 2.3(ii).
--
--   **Formalization Note** Continuity on $[0,\infty)$ is part of the notion of solution: right derivatives alone would admit functions that follow the flow and jump at isolated times, which would make every stability notion fail. For the Lipschitz fields of this paper, forward solutions exist and are unique, so quantifying over all of them is faithful.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 447 (ODE (1.2)), p. 448 (Eq. (1.3)), p. 449 (Assumption (A1)), p. 451 (Theorem 2.3), p. 466 (exponential stability in the proof of Theorem 2.3(ii))

import Mathlib

namespace BorkarMeynODE.Bounded

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A forward solution of the autonomous ODE `ẋ = f(x)` on `[0, ∞)`: `x` is continuous on
`[0, ∞)` and at every `t ≥ 0` has right derivative `f (x t)`. Values at negative times are
irrelevant. (Continuity is required: right derivatives alone would admit piecewise solutions
that jump at arbitrary times.) -/
def IsODESolution (f : E → E) (x : ℝ → E) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧ ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt x (f (x t)) (Set.Ici t) t

/-- `xs` is an equilibrium point of `ẋ = f(x)`. -/
def IsEquilibrium (f : E → E) (xs : E) : Prop :=
  f xs = 0

/-- Lyapunov stability of `xs` for `ẋ = f(x)`: solutions starting close to `xs` stay close
to `xs` for all forward time. -/
def IsLyapunovStable (f : E → E) (xs : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ → E, IsODESolution f x →
    ‖x 0 - xs‖ < δ → ∀ t : ℝ, 0 ≤ t → ‖x t - xs‖ < ε

/-- `xs` is an asymptotically stable equilibrium of `ẋ = f(x)`: an equilibrium, Lyapunov
stable, and locally attracting. -/
def IsAsymptoticallyStable (f : E → E) (xs : E) : Prop :=
  IsEquilibrium f xs ∧ IsLyapunovStable f xs ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ → E, IsODESolution f x → ‖x 0 - xs‖ < δ →
      Tendsto x atTop (𝓝 xs)

/-- `xs` is a globally asymptotically stable equilibrium of `ẋ = f(x)`: an equilibrium,
Lyapunov stable, and every solution converges to it. -/
def IsGloballyAsymptoticallyStable (f : E → E) (xs : E) : Prop :=
  IsEquilibrium f xs ∧ IsLyapunovStable f xs ∧
    ∀ x : ℝ → E, IsODESolution f x → Tendsto x atTop (𝓝 xs)

/-- `xs` is a globally exponentially asymptotically stable equilibrium of `ẋ = f(x)`: there are
constants `b` and `δ > 0` with `‖x(t) - xs‖ ≤ b e^{-δ t} ‖x(0) - xs‖` for every solution and
every `t ≥ 0`. -/
def IsGloballyExponentiallyStable (f : E → E) (xs : E) : Prop :=
  IsEquilibrium f xs ∧
    ∃ b δ : ℝ, 0 < δ ∧ ∀ x : ℝ → E, IsODESolution f x → ∀ t : ℝ, 0 ≤ t →
      ‖x t - xs‖ ≤ b * Real.exp (-δ * t) * ‖x 0 - xs‖

/-- The scaled vector field (1.3): `h_r(x) = r⁻¹ h(r x)`. -/
noncomputable def scaledField (f : E → E) (r : ℝ) : E → E :=
  fun x => r⁻¹ • f (r • x)

end BorkarMeynODE.Bounded


