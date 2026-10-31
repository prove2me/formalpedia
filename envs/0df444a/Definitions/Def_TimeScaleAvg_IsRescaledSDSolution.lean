-- Prove2me | Definitions.Def_TimeScaleAvg_IsRescaledSDSolution
-- name    : TimeScaleAvg_IsRescaledSDSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:54.609901+00:00
-- url     : https://prove2.me/theorems/a80760f5-ccd5-49ee-8e65-62935b43c961
-- title:
--   Solution of the time-rescaled steepest descent (25)
-- statement:
--   Let $f:\mathcal H\to\mathbb R$ and $\alpha,s_0\in\mathbb R$. A trajectory $y$ with velocity $\dot y$ is a solution of (25) on $[s_0,+\infty[$ when $y$ has derivative $\dot y(s)$ at every $s\ge s_0$ (one-sided at $s_0$), and
--
--   $$
--   \dot y(s)+\frac{s}{\alpha-1}\nabla f(y(s))=0\qquad\text{for every }s\ge s_0.
--   $$
--
--   This is steepest descent after the change of time $t=s^2/(2(\alpha-1))$.
--
--   **Formalization Note** The solution is classical. Trajectories are maps $\mathbb R\to\mathcal H$ constrained on the half-line only.
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Eq. (25), p.5; first line of Eq. (32), p.6

import Mathlib

namespace TimeScaleAvg

/-- `y`, with velocity `ydot`, is a solution trajectory on `[s₀, +∞[` of the time-rescaled steepest
descent (25), `ẏ(s) + (s/(α-1)) ∇f(y(s)) = 0`
(Attouch, Boţ & Nguyen, arXiv:2208.08260v3, Eq. (25), p.5; also the first line of (32), p.6).

**Formalization Note.** A solution is classical: at every `s ≥ s₀` the map `y` has derivative
`ydot s` within `[s₀, +∞[` (one-sided at `s₀`) and the equation holds there. Values before `s₀` play
no role. The hypotheses `0 < s₀` and `1 < α` are separate hypotheses of each statement. -/
def IsRescaledSDSolution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (α s₀ : ℝ) (y ydot : ℝ → H) : Prop :=
  ∀ s ∈ Set.Ici s₀,
    HasDerivWithinAt y (ydot s) (Set.Ici s₀) s ∧ ydot s + (s / (α - 1)) • gradient f (y s) = 0

end TimeScaleAvg


