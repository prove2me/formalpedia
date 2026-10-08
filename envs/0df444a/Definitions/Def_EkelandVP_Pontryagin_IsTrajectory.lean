-- Prove2me | Definitions.Def_EkelandVP_Pontryagin_IsTrajectory
-- name    : EkelandVP_Pontryagin_IsTrajectory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:08:08.406546+00:00
-- url     : https://prove2.me/theorems/cf76770b-0990-4d10-8e93-822bcc71cf69
-- title:
--   (7.1) — trajectory of the control system dx/dt = f(x, u, t), x(0) = x₀, driven by a control u
-- statement:
--   Let $f : \mathbb R^n \times K \times \mathbb R \to \mathbb R^n$, let $x_0 \in \mathbb R^n$, let $T$ be a real number and let $u : \mathbb R \to K$ be a control. A function $x : \mathbb R \to \mathbb R^n$ is a **trajectory** of the control system
--
--   $$
--   \frac{dx}{dt}(t) = f(x(t), u(t), t) \quad \text{a.e.}, \qquad x(0) = x_0 \qquad (7.1)
--   $$
--
--   on $[0, T]$ driven by $u$ if $x$ is continuous on $[0, T]$ and
--
--   $$
--   x(t) = x_0 + \int_0^t f(x(s), u(s), s)\, ds \qquad \text{for every } t \in [0, T].
--   $$
--
--   Only the values of $x$ and $u$ on $[0, T]$ matter.
--
--   This is the state equation of Ekeland's §7: every statement of the mission about "the trajectory corresponding to $u$" refers to this notion.
--
--   **Formalization Note** The differential equation is stated in integral form, which Ekeland himself uses in (7.13) (p. 350). For a measurable control the solution is absolutely continuous and satisfies the differential equation only almost everywhere, so a pointwise derivative condition at every $t$ would not be satisfiable; the integral form is equivalent to "absolutely continuous, $x(0) = x_0$, $\dot x = f(x, u, t)$ a.e." whenever the integrand is integrable, which is the case for a continuous $f$ and a continuous $x$ on the compact $[0, T]$.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 348, §7, (7.1); integral form as in (7.13), p. 350

import Mathlib

namespace EkelandVP.Pontryagin

/-- Ekeland (1974), §7, p. 348, (7.1), in the integral form (7.13) of p. 350: `x` is a trajectory
(solution of `dx/dt = f(x(t), u(t), t)` a.e., `x(0) = x₀`) of the control system on `[0, T]` driven by
the control `u`, i.e. `x` is continuous on `[0, T]` and `x(t) = x₀ + ∫₀ᵗ f(x(s), u(s), s) ds` for every
`t ∈ [0, T]`. Values of `x` and `u` outside `[0, T]` play no role. -/
def IsTrajectory {n : ℕ} {K : Type*}
    (f : EuclideanSpace ℝ (Fin n) → K → ℝ → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (T : ℝ) (u : ℝ → K)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ContinuousOn x (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T, x t = x₀ + ∫ s in (0 : ℝ)..t, f (x s) (u s) s

end EkelandVP.Pontryagin


