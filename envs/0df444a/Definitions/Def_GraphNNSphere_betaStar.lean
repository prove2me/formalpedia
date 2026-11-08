-- Prove2me | Definitions.Def_GraphNNSphere_betaStar
-- name    : GraphNNSphere_betaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:12.022302+00:00
-- url     : https://prove2.me/theorems/683d096c-63a0-465c-80e8-80773b555f8e
-- title:
--   Critical exponent $\beta^*(c)$
-- statement:
--   The critical degree exponent of the logarithmic regime $d=\lfloor c\log n\rfloor$:
--   $$\beta^*(c)=\frac c2\log\bigl(2-e^{-2/c}\bigr).$$
--   It lies in $(0,1)$ for every $c>0$.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.1, p.2

import Mathlib

namespace GraphNNSphere

/-- The critical exponent `β*(c) = (c/2) log(2 - e^{-2/c})` of the logarithmic regime (Lu, *Sharp
Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript
sha256 93565bc5…), §1.1, p.2). -/
noncomputable def betaStar (c : ℝ) : ℝ := c / 2 * Real.log (2 - Real.exp (-2 / c))

end GraphNNSphere


