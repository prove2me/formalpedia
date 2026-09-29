-- Prove2me | Definitions.Def_ModularCurve_LegendreJ
-- name    : ModularCurve_LegendreJ
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/ec89516e-21e6-5267-aec1-f4d5c89456ad
-- title:
--   The j-invariant of the Legendre curve as a rational function
-- statement:
--   This module introduces a single total function. For a field $K$ and an element $t \in K$, [`ModularCurve.legendreJ t`](../def/ModularCurve_LegendreJ.html#L7) is the element
--   $$2^{8}\,\frac{(t^{2}-t+1)^{3}}{t^{2}\,(t-1)^{2}} \in K,$$
--   written exactly as that quotient of polynomial expressions in $t$. Classically this is the $j$-invariant of the Legendre curve $E_t : y^{2} = x(x-1)(x-t)$, equivalently of the Weierstrass model $y^{2} = x^{3} - (1+t)x^{2} + t x$, so that $t \mapsto$ `legendreJ t` is the degree-six map from the $\lambda$-line to the $j$-line, invariant under the six substitutions $t,\ 1-t,\ 1/t,\ 1/(1-t),\ t/(t-1),\ (t-1)/t$.
--
--   The definition is made for an arbitrary field, with no hypothesis on $t$ and no hypothesis on the characteristic; it is a formula, not an assertion about a curve. Since division in a Lean field is total with $x/0 = 0$, the value at the two points $t = 0$ and $t = 1$, where the cubic $x(x-1)(x-t)$ acquires a double root and the Legendre curve degenerates, is $0$ by that convention and carries no geometric meaning. Accordingly, results about `legendreJ` elsewhere in the development are stated under the hypotheses $t \neq 0$ and $t \neq 1$, which also make the denominator invertible.
--
--   **Relation to Mathlib.** Mathlib provides the $j$-invariant of a Weierstrass curve, but no dedicated function for the Legendre family; [`ModularCurve.legendreJ`](../def/ModularCurve_LegendreJ.html#L7) is the project's own abbreviation for the rational expression in the parameter.
--
--   **Where it is used.** The $\lambda$-to-$j$ map is used to parametrise $j$-invariants of elliptic curves together with a chosen $2$-torsion structure, in particular to identify the supersingular $j$-invariants in characteristic $p$ as the images under `legendreJ` of the roots of the Deuring polynomial, which in turn feeds the mass formula for supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_LegendreJ.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ModularCurve

def legendreJ {K : Type*} [Field K] (t : K) : K :=
  2 ^ 8 * (t ^ 2 - t + 1) ^ 3 / (t ^ 2 * (t - 1) ^ 2)

end ModularCurve


