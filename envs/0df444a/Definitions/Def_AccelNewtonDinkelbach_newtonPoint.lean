-- Prove2me | Definitions.Def_AccelNewtonDinkelbach_newtonPoint
-- name    : AccelNewtonDinkelbach_newtonPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:58.274983+00:00
-- url     : https://prove2.me/theorems/4736d170-d707-43f4-bc74-f5bbc59d5cab
-- title:
--   Newton–Dinkelbach point $\delta-f(\delta)/g$
-- statement:
--   Given the current iterate $\delta$ and a supergradient $g\in\partial f(\delta)$, the **Newton–Dinkelbach point** is
--
--   $$\delta-\frac{f(\delta)}{g},$$
--
--   the root of the tangent line $x\mapsto f(\delta)+g\,(x-\delta)$. It is the point generated on line 3 of Algorithm 1 and by the classical method. The look-ahead guess of Algorithm 1 is $2\bigl(\delta-f(\delta)/g\bigr)-\delta$.
--
--   **Formalization Note** Lean's division sets $f(\delta)/0=0$; the step relations use this point only from iterates with $f(\delta)<0$ and $g<0$, where it is the paper's.
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, §3, p.6 and Algorithm 1, line 3, p.7

import Mathlib

namespace AccelNewtonDinkelbach

/-- **Newton–Dinkelbach point `δ(i) − f(δ(i))/g(i)`.**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, §3, p.6: "Otherwise, a new point
δ := δ(i) − f(δ(i))/g(i) is generated", and Algorithm 1, line 3, p.7.

`newtonPoint f δ g = δ − f δ / g`: the root of the tangent line `x ↦ f δ + g (x − δ)`.

**Formalization Note** Lean's division gives `f δ / 0 = 0`; the step relations of this mission use
this point only from an iterate with `f δ < 0` and a supergradient `g < 0`, where the division is
the paper's. -/
noncomputable def newtonPoint (f : ℝ → ℝ) (δ g : ℝ) : ℝ :=
  δ - f δ / g

end AccelNewtonDinkelbach


