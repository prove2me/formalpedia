-- Prove2me | Definitions.Def_TimeScaleAvg_yTraj
-- name    : TimeScaleAvg_yTraj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:51.660052+00:00
-- url     : https://prove2.me/theorems/66f20fc4-a896-4691-80bd-780f85a27415
-- title:
--   The trajectory $y(s)=x(s)+\frac{s}{\alpha-1}\dot x(s)$
-- statement:
--   For a trajectory $x$ with velocity $\dot x$, this is the trajectory
--
--   $$
--   y(s)=x(s)+\frac{s}{\alpha-1}\dot x(s),
--   $$
--
--   at which the gradient is evaluated in (31). It links the inertial dynamic to the rescaled steepest descent.
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, p.7; Eqs. (32)–(33), p.6

import Mathlib

namespace TimeScaleAvg

/-- The trajectory `y(s) = x(s) + (s/(α-1)) ẋ(s)` attached to a trajectory `x` with velocity `xdot`
(Attouch, Boţ & Nguyen, arXiv:2208.08260v3, p.7: "Replacing y by its equivalent formulation
y(s) = x(s) + (s/(α-1)) ẋ(s)"; the same `y` as in (32)–(33), p.6). -/
noncomputable def yTraj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (α : ℝ) (x xdot : ℝ → H) (s : ℝ) : H :=
  x s + (s / (α - 1)) • xdot s

end TimeScaleAvg


