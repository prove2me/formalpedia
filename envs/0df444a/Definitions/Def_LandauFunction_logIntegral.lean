-- Prove2me | Definitions.Def_LandauFunction_logIntegral
-- name    : LandauFunction_logIntegral
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:27:00.941787+00:00
-- url     : https://prove2.me/theorems/56eeefbf-841e-4fa7-8c4d-e928c29a0d95
-- title:
--   Logarithmic integral $\mathrm{Li}$ and its inverse
-- statement:
--   The **(offset) logarithmic integral** is
--
--   $$\mathrm{Li}(x)=\int_2^x\frac{dt}{\ln t}\qquad(x\ge 2).$$
--
--   It is continuous and strictly increasing on $[2,\infty)$, with $\mathrm{Li}(2)=0$ and $\mathrm{Li}(x)\to\infty$, so it has an inverse $\mathrm{Li}^{-1}:[0,\infty)\to[2,\infty)$. These functions appear in the prime number theorem and in the refined asymptotics of Landau's function.
--
--   **Formalization Note** `logIntegral x` is the interval integral $\int_2^x dt/\ln t$ (for $x<2$ it is the oriented integral). `logIntegralInv y` is defined as $\inf\{x\ge2:\ y\le\mathrm{Li}(x)\}$, which equals $\mathrm{Li}^{-1}(y)$ for every $y\ge0$ (and is $2$ for $y<0$).
-- source:
--   Wikipedia, "Landau's function", revision oldid=1303222269 (https://en.wikipedia.org/w/index.php?title=Landau%27s_function&oldid=1303222269), paragraph "If π(x) − Li(x) = O(R(x)) …" (Li and Li⁻¹).

import Mathlib

namespace LandauFunction

/-- The (offset) logarithmic integral `Li(x) = ∫₂ˣ dt / ln t`. -/
noncomputable def logIntegral (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, 1 / Real.log t

/-- The inverse `Li⁻¹` of the logarithmic integral: for `y ≥ 0`, the unique `x ≥ 2`
with `Li(x) = y` (realised as the least `x ≥ 2` with `y ≤ Li(x)`). -/
noncomputable def logIntegralInv (y : ℝ) : ℝ :=
  sInf {x : ℝ | 2 ≤ x ∧ y ≤ logIntegral x}

end LandauFunction


