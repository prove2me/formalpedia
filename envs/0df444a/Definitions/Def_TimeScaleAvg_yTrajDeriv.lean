-- Prove2me | Definitions.Def_TimeScaleAvg_yTrajDeriv
-- name    : TimeScaleAvg_yTrajDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:36.683748+00:00
-- url     : https://prove2.me/theorems/34b263b6-f731-4526-a734-d8bf58af5abc
-- title:
--   The right-hand side $-\frac{s}{\alpha-1}\nabla f(y(s))$ of (32)
-- statement:
--   With $y$ as in `yTraj`, this names the function
--
--   $$
--   s\mapsto-\frac{s}{\alpha-1}\nabla f(y(s)),
--   $$
--
--   which is the velocity of $y$ prescribed by (32).
--
--   **Formalization Note** The definition names the right-hand side only; that it is the derivative of $y$ is a milestone of the mission.
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Eq. (32), p.6

import Mathlib
import Definitions.Def_TimeScaleAvg_yTraj

namespace TimeScaleAvg

/-- The velocity of `yTraj α x xdot` as given by (32), `ẏ(s) = -(s/(α-1)) ∇f(y(s))`
(Attouch, Boţ & Nguyen, arXiv:2208.08260v3, Eq. (32), p.6).

**Formalization Note.** This names the right-hand side only. That it is the derivative of `yTraj`
for a solution of (31) is the content of `TimeScaleAvg.eq_32_33`. -/
noncomputable def yTrajDeriv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (α : ℝ) (x xdot : ℝ → H) (s : ℝ) : H :=
  -((s / (α - 1)) • gradient f (yTraj α x xdot s))

end TimeScaleAvg


