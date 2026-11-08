-- Prove2me | Definitions.Def_GraphNNSphere_Irate
-- name    : GraphNNSphere_Irate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:30.277888+00:00
-- url     : https://prove2.me/theorems/84bc3f82-7482-4a7c-8ed7-d226d71791de
-- title:
--   Directional rate $I_\theta(\rho)$
-- statement:
--   For $0<\theta<\pi/2$ with $\cot\theta\tan(\rho/2)<1$,
--   $$I_\theta(\rho)=-\frac12\log\bigl(1-\cot^2\theta\tan^2(\rho/2)\bigr).$$
--   It controls the fraction of query directions for which a fixed point at distance at least $\rho$ from $x$ is closer to the query than $x$.
--
--   **Formalization Note** Outside the printed domain the logarithm takes a junk value. Every use has $\cot\theta\tan(\rho/2)<1$ among its hypotheses.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §3.3, p.23

import Mathlib

namespace GraphNNSphere

/-- The directional rate `I_θ(ρ) = -(1/2) log(1 - cot²θ tan²(ρ/2))`, for `0 < θ < π/2` with
`cot θ tan(ρ/2) < 1` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC
2027 submission (manuscript sha256 93565bc5…), §3.3, p.23).

**Formalization Note** Outside the printed domain the logarithm takes a junk value. Every use has
`cot θ tan(ρ/2) < 1` among its hypotheses. -/
noncomputable def Irate (θ ρ : ℝ) : ℝ :=
  -(1 / 2) * Real.log (1 - Real.cot θ ^ 2 * Real.tan (ρ / 2) ^ 2)

end GraphNNSphere


