-- Prove2me | Definitions.Def_FarmerInfoProvision_coefA0
-- name    : FarmerInfoProvision_coefA0
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:29:44.613375+00:00
-- url     : https://prove2.me/theorems/62165f5c-f4cb-4993-b570-6986eada4dd2
-- title:
--   Equilibrium intercept $A_0=B_0=(a-c)/(b(n+1))$
-- statement:
--   In the Cournot game with $n$ farmers, inverse demand $a-bQ+u$ and unit cost $c$, every farmer's equilibrium quantity has the same intercept
--
--   $$
--   A_0=B_0=\frac{a-c}{b(n+1)},
--   $$
--
--   display (7) of Proposition 1. It is the full-information-free Cournot quantity and does not depend on who is informed.
--
--   **Formalization Note** $n$ is real; for $b>0$, $n\ge0$ the denominator is positive.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §4.1, Proposition 1, display (7), p. 12

import Mathlib

namespace FarmerInfoProvision

/-- **The intercept `A0 = B0` of the equilibrium production quantities.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §4.1, Proposition 1, display (7), p. 12:
"`A0 = B0 = (a − c)/(b(n + 1))`."

Here `a` is the market potential, `b` the price sensitivity, `c` the unit production cost and
`n` the number of farmers.

**Formalization Note.** `n` is a real number (see `Psi`); for `b > 0` and `n ≥ 0` the
denominator is positive. -/
noncomputable def coefA0 (a b c n : ℝ) : ℝ :=
  (a - c) / (b * (n + 1))

end FarmerInfoProvision


