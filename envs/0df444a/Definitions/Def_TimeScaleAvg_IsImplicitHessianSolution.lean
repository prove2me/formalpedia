-- Prove2me | Definitions.Def_TimeScaleAvg_IsImplicitHessianSolution
-- name    : TimeScaleAvg_IsImplicitHessianSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:56.806503+00:00
-- url     : https://prove2.me/theorems/58386d20-bc3f-47b4-bebd-19ad7b699c7d
-- title:
--   Solution of the inertial dynamic with implicit Hessian damping (31)
-- statement:
--   Let $f:\mathcal H\to\mathbb R$ and $\alpha,s_0\in\mathbb R$. A trajectory $x$ with velocity $\dot x$ and acceleration $\ddot x$ is a solution of (31) on $[s_0,+\infty[$ when $x$ has derivative $\dot x(s)$ and $\dot x$ has derivative $\ddot x(s)$ at every $s\ge s_0$ (one-sided at $s_0$), and
--
--   $$
--   \ddot x(s)+\frac{\alpha}{s}\dot x(s)+\nabla f\Bigl(x(s)+\frac{s}{\alpha-1}\dot x(s)\Bigr)=0\qquad\text{for every }s\ge s_0.
--   $$
--
--   The Cauchy data of the proof are $x_0=x(s_0)$ and $x_1=\dot x(s_0)$. This is the dynamic of the goal theorem.
--
--   **Formalization Note** The solution is classical; continuity of $\ddot x$ is a consequence and is not required. Trajectories are maps $\mathbb R\to\mathcal H$ constrained on the half-line only.
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Eq. (31), Theorem 2, p.6

import Mathlib

namespace TimeScaleAvg

/-- `x`, with velocity `xdot` and acceleration `xddot`, is a solution trajectory on `[s₀, +∞[` of
the inertial dynamic with implicit Hessian damping (31),
`ẍ(s) + (α/s) ẋ(s) + ∇f(x(s) + (s/(α-1)) ẋ(s)) = 0`
(Attouch, Boţ & Nguyen, arXiv:2208.08260v3, Theorem 2, Eq. (31), p.6).

**Formalization Note.** A solution is classical: at every `s ≥ s₀` the map `x` has derivative
`xdot s`, the map `xdot` has derivative `xddot s`, both within `[s₀, +∞[` (one-sided at `s₀`), and
the equation holds there. Continuity of `xddot` is not asked for: it is a consequence. The
trajectories are maps `ℝ → H` tied down on the half-line only. The Cauchy data of the proof are
`x₀ = x s₀` and `x₁ = xdot s₀`. The hypotheses `0 < s₀` and `1 < α` are separate hypotheses of each
statement. -/
def IsImplicitHessianSolution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (α s₀ : ℝ) (x xdot xddot : ℝ → H) : Prop :=
  ∀ s ∈ Set.Ici s₀,
    HasDerivWithinAt x (xdot s) (Set.Ici s₀) s ∧
    HasDerivWithinAt xdot (xddot s) (Set.Ici s₀) s ∧
    xddot s + (α / s) • xdot s + gradient f (x s + (s / (α - 1)) • xdot s) = 0

end TimeScaleAvg


