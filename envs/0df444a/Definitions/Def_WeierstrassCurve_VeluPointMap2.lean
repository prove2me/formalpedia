-- Prove2me | Definitions.Def_WeierstrassCurve_VeluPointMap2
-- name    : WeierstrassCurve_VeluPointMap2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/1a793c0a-1dbf-54c6-a5d7-cecd4a9f07dd
-- title:
--   Vélu coordinate maps for a point of order two
-- statement:
--   Fix a Weierstrass curve $W$ over a commutative ring $R$ and a pair $(x_0,y_0)$, and write $g_x = 3x_0^2 + 2a_2x_0 + a_4 - a_1y_0$ and $g_y = -(2y_0 + a_1x_0 + a_3)$ for the quantities `veluGx`, `veluGy`. Over $R$ the module defines the two numerator polynomials
--   $$\mathtt{velu2XNum}(x) = x(x-x_0)^2 + g_x(x-x_0),\qquad \mathtt{velu2YNum}(x,y) = y(x-x_0)^3 - g_x\bigl(a_1(x-x_0)+y-y_0\bigr)(x-x_0),$$
--   the first being visibly $(x-x_0)\bigl(x(x-x_0)+g_x\bigr)$. The identity `velu2_equation_cleared_four` asserts that, for $(x,y)$ and $(x_0,y_0)$ both satisfying the affine Weierstrass equation of $W$ and subject to $g_y = 0$, four times the homogenised left-hand side of the Weierstrass equation of the curve `veluQuotient2` evaluated at these numerators, with the powers $(x-x_0)^k$ supplying the denominators, equals four times the corresponding right-hand side; it is proved by an explicit large linear combination of the three hypotheses. Here `veluQuotient2` is the Weierstrass curve with the same $a_1,a_2,a_3$ and with $a_4 - 5g_x$, $a_6 - b_2g_x - 7x_0g_x$, the Vélu recipe with $t = g_x$, $w = x_0g_x$ appropriate to a point of order two.
--
--   Over a field $F$ the rational maps $\mathtt{velu2X} = x + g_x/(x-x_0)$ and $\mathtt{velu2Y} = y - g_x(a_1(x-x_0)+y-y_0)/(x-x_0)^2$ are defined, and identified for $x \neq x_0$ with the above numerators divided by $(x-x_0)^2$ and $(x-x_0)^3$. Assuming $2 \neq 0$ in $F$, `velu2_map_equation` states that these values satisfy the affine equation of `veluQuotient2` whenever $(x,y)$, $(x_0,y_0)$ lie on $W$, $g_y(x_0,y_0) = 0$ and $x \neq x_0$; adding the hypothesis that the discriminant of `veluQuotient2` is nonzero gives nonsingularity of the image point. Finally `veluPointMap2`, taking the hypotheses $2 \neq 0$, $(x_0,y_0)$ on $W$, $g_y(x_0,y_0) = 0$ and $\Delta \neq 0$ as arguments, is the function on affine points sending $0$ to $0$, sending any point with $x$-coordinate $x_0$ to $0$, and otherwise to the point with the Vélu coordinates; three lemmas record these three cases. No additivity is asserted at this stage.
--
--   **Relation to Mathlib.** Mathlib supplies the Weierstrass curve data, the affine equation and nonsingularity predicates, the discriminant and the type of affine points; the Vélu formulas, the quotient curve `veluQuotient2` and the point map are the project's own additions.
--
--   **Where it is used.** The construction gives the quotient of a Weierstrass curve by a rational point of order two in explicit coordinates, together with the induced map on affine points, for use where 2-isogenies of elliptic curves (kernels, surjectivity, the dual isogeny) are needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_VeluPointMap2.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x₀ y₀ : R)

def velu2XNum (x : R) : R :=
  x * (x - x₀) ^ 2 + W.veluGx x₀ y₀ * (x - x₀)

def velu2YNum (x y : R) : R :=
  y * (x - x₀) ^ 3 - W.veluGx x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * (x - x₀)

lemma velu2XNum_eq_mul (x : R) :
    W.velu2XNum x₀ y₀ x = (x - x₀) * (x * (x - x₀) + W.veluGx x₀ y₀) := by
  simp only [velu2XNum]; ring

theorem velu2_equation_cleared_four {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) :
    4 * (W.velu2YNum x₀ y₀ x y ^ 2
        + W.a₁ * W.velu2XNum x₀ y₀ x * W.velu2YNum x₀ y₀ x y * (x - x₀)
        + W.a₃ * W.velu2YNum x₀ y₀ x y * (x - x₀) ^ 3)
      = 4 * (W.velu2XNum x₀ y₀ x ^ 3 + W.a₂ * W.velu2XNum x₀ y₀ x ^ 2 * (x - x₀) ^ 2
        + (W.a₄ - 5 * W.veluGx x₀ y₀) * W.velu2XNum x₀ y₀ x * (x - x₀) ^ 4
        + (W.a₆ - W.b₂ * W.veluGx x₀ y₀ - 7 * (x₀ * W.veluGx x₀ y₀)) * (x - x₀) ^ 6) := by
  rw [Affine.equation_iff] at hP hQ
  simp only [veluGy] at hgy
  simp only [velu2XNum, velu2YNum, veluGx, b₂]
  linear_combination
    (4*W.a₁^2*x^2*y₀^2 - 8*W.a₁^2*x*x₀*y₀^2 + 4*W.a₁^2*x₀^2*y₀^2 - 16*W.a₁*W.a₂*x^2*x₀*y₀ + 32*W.a₁*W.a₂*x*x₀^2*y₀ - 16*W.a₁*W.a₂*x₀^3*y₀ - 8*W.a₁*W.a₄*x^2*y₀ + 16*W.a₁*W.a₄*x*x₀*y₀ - 8*W.a₁*W.a₄*x₀^2*y₀ + 8*W.a₁*x^4*y₀ - 32*W.a₁*x^3*x₀*y₀ + 24*W.a₁*x^2*x₀^2*y₀ + 16*W.a₁*x*x₀^3*y₀ - 16*W.a₁*x₀^4*y₀ + 16*W.a₂^2*x^2*x₀^2 - 32*W.a₂^2*x*x₀^3 + 16*W.a₂^2*x₀^4 + 16*W.a₂*W.a₄*x^2*x₀ - 32*W.a₂*W.a₄*x*x₀^2 + 16*W.a₂*W.a₄*x₀^3 - 16*W.a₂*x^4*x₀ + 64*W.a₂*x^3*x₀^2 - 48*W.a₂*x^2*x₀^3 - 32*W.a₂*x*x₀^4 + 32*W.a₂*x₀^5 + 4*W.a₄^2*x^2 - 8*W.a₄^2*x*x₀ + 4*W.a₄^2*x₀^2 - 8*W.a₄*x^4 + 32*W.a₄*x^3*x₀ - 24*W.a₄*x^2*x₀^2 - 16*W.a₄*x*x₀^3 + 16*W.a₄*x₀^4 + 4*x^6 - 24*x^5*x₀ + 36*x^4*x₀^2 + 16*x^3*x₀^3 - 48*x^2*x₀^4 + 16*x₀^6) * hP
    + (-W.a₁^4*x^2*x₀^2 + 2*W.a₁^4*x*x₀^3 - W.a₁^4*x₀^4 - 2*W.a₁^3*W.a₃*x^2*x₀ + 4*W.a₁^3*W.a₃*x*x₀^2 - 2*W.a₁^3*W.a₃*x₀^3 - 8*W.a₁^2*W.a₂*x^2*x₀^2 + 16*W.a₁^2*W.a₂*x*x₀^3 - 8*W.a₁^2*W.a₂*x₀^4 - W.a₁^2*W.a₃^2*x^2 + 2*W.a₁^2*W.a₃^2*x*x₀ - W.a₁^2*W.a₃^2*x₀^2 - 4*W.a₁^2*W.a₄*x^2*x₀ + 8*W.a₁^2*W.a₄*x*x₀^2 - 4*W.a₁^2*W.a₄*x₀^3 + 4*W.a₁^2*x^4*x₀ - 16*W.a₁^2*x^3*x₀^2 + 12*W.a₁^2*x^2*x₀^3 + 8*W.a₁^2*x*x₀^4 - 8*W.a₁^2*x₀^5 - 8*W.a₁*W.a₂*W.a₃*x^2*x₀ + 16*W.a₁*W.a₂*W.a₃*x*x₀^2 - 8*W.a₁*W.a₂*W.a₃*x₀^3 - 4*W.a₁*W.a₃*W.a₄*x^2 + 8*W.a₁*W.a₃*W.a₄*x*x₀ - 4*W.a₁*W.a₃*W.a₄*x₀^2 + 4*W.a₁*W.a₃*x^4 - 16*W.a₁*W.a₃*x^3*x₀ + 12*W.a₁*W.a₃*x^2*x₀^2 + 8*W.a₁*W.a₃*x*x₀^3 - 8*W.a₁*W.a₃*x₀^4 - 16*W.a₂^2*x^2*x₀^2 + 32*W.a₂^2*x*x₀^3 - 16*W.a₂^2*x₀^4 - 16*W.a₂*W.a₄*x^2*x₀ + 32*W.a₂*W.a₄*x*x₀^2 - 16*W.a₂*W.a₄*x₀^3 + 16*W.a₂*x^4*x₀ - 64*W.a₂*x^3*x₀^2 + 48*W.a₂*x^2*x₀^3 + 32*W.a₂*x*x₀^4 - 32*W.a₂*x₀^5 - 4*W.a₄^2*x^2 + 8*W.a₄^2*x*x₀ - 4*W.a₄^2*x₀^2 + 8*W.a₄*x^4 - 32*W.a₄*x^3*x₀ + 24*W.a₄*x^2*x₀^2 + 16*W.a₄*x*x₀^3 - 16*W.a₄*x₀^4 + 24*x^4*x₀^2 - 96*x^3*x₀^3 + 108*x^2*x₀^4 - 24*x*x₀^5 - 12*x₀^6) * hQ
    + (-W.a₁^4*x^2*x₀^2*y₀ + 2*W.a₁^4*x*x₀^3*y₀ - W.a₁^4*x₀^4*y₀ + W.a₁^3*W.a₂*x^2*x₀^3 - 2*W.a₁^3*W.a₂*x*x₀^4 + W.a₁^3*W.a₂*x₀^5 - 2*W.a₁^3*W.a₃*x^2*x₀*y₀ + 4*W.a₁^3*W.a₃*x*x₀^2*y₀ - 2*W.a₁^3*W.a₃*x₀^3*y₀ + W.a₁^3*W.a₄*x^2*x₀^2 - 2*W.a₁^3*W.a₄*x*x₀^3 + W.a₁^3*W.a₄*x₀^4 + W.a₁^3*W.a₆*x^2*x₀ - 2*W.a₁^3*W.a₆*x*x₀^2 + W.a₁^3*W.a₆*x₀^3 + W.a₁^3*x^2*x₀^4 + W.a₁^3*x^2*x₀*y₀^2 - 2*W.a₁^3*x*x₀^5 - 2*W.a₁^3*x*x₀^2*y₀^2 + W.a₁^3*x₀^6 + W.a₁^3*x₀^3*y₀^2 + W.a₁^2*W.a₂*W.a₃*x^2*x₀^2 - 2*W.a₁^2*W.a₂*W.a₃*x*x₀^3 + W.a₁^2*W.a₂*W.a₃*x₀^4 - 10*W.a₁^2*W.a₂*x^2*x₀^2*y₀ + 20*W.a₁^2*W.a₂*x*x₀^3*y₀ - 10*W.a₁^2*W.a₂*x₀^4*y₀ - W.a₁^2*W.a₃^2*x^2*y₀ + 2*W.a₁^2*W.a₃^2*x*x₀*y₀ - W.a₁^2*W.a₃^2*x₀^2*y₀ + W.a₁^2*W.a₃*W.a₄*x^2*x₀ - 2*W.a₁^2*W.a₃*W.a₄*x*x₀^2 + W.a₁^2*W.a₃*W.a₄*x₀^3 + W.a₁^2*W.a₃*W.a₆*x^2 - 2*W.a₁^2*W.a₃*W.a₆*x*x₀ + W.a₁^2*W.a₃*W.a₆*x₀^2 + W.a₁^2*W.a₃*x^2*x₀^3 + W.a₁^2*W.a₃*x^2*y₀^2 - 2*W.a₁^2*W.a₃*x*x₀^4 - 2*W.a₁^2*W.a₃*x*x₀*y₀^2 + W.a₁^2*W.a₃*x₀^5 + W.a₁^2*W.a₃*x₀^2*y₀^2 - 6*W.a₁^2*W.a₄*x^2*x₀*y₀ + 12*W.a₁^2*W.a₄*x*x₀^2*y₀ - 6*W.a₁^2*W.a₄*x₀^3*y₀ - 2*W.a₁^2*W.a₆*x^2*y₀ + 4*W.a₁^2*W.a₆*x*x₀*y₀ - 2*W.a₁^2*W.a₆*x₀^2*y₀ - 4*W.a₁^2*x^5*y₀ + 24*W.a₁^2*x^4*x₀*y₀ - 56*W.a₁^2*x^3*x₀^2*y₀ + 50*W.a₁^2*x^2*x₀^3*y₀ + 4*W.a₁^2*x^2*y*y₀^2 - 2*W.a₁^2*x^2*y₀^3 - 8*W.a₁^2*x*x₀^4*y₀ - 8*W.a₁^2*x*x₀*y*y₀^2 + 4*W.a₁^2*x*x₀*y₀^3 - 6*W.a₁^2*x₀^5*y₀ + 4*W.a₁^2*x₀^2*y*y₀^2 - 2*W.a₁^2*x₀^2*y₀^3 + 8*W.a₁*W.a₂^2*x^2*x₀^3 - 16*W.a₁*W.a₂^2*x*x₀^4 + 8*W.a₁*W.a₂^2*x₀^5 - 8*W.a₁*W.a₂*W.a₃*x^2*x₀*y₀ + 16*W.a₁*W.a₂*W.a₃*x*x₀^2*y₀ - 8*W.a₁*W.a₂*W.a₃*x₀^3*y₀ + 12*W.a₁*W.a₂*W.a₄*x^2*x₀^2 - 24*W.a₁*W.a₂*W.a₄*x*x₀^3 + 12*W.a₁*W.a₂*W.a₄*x₀^4 + 8*W.a₁*W.a₂*W.a₆*x^2*x₀ - 16*W.a₁*W.a₂*W.a₆*x*x₀^2 + 8*W.a₁*W.a₂*W.a₆*x₀^3 + 8*W.a₁*W.a₂*x^5*x₀ - 44*W.a₁*W.a₂*x^4*x₀^2 + 96*W.a₁*W.a₂*x^3*x₀^3 - 84*W.a₁*W.a₂*x^2*x₀^4 - 16*W.a₁*W.a₂*x^2*x₀*y*y₀ + 8*W.a₁*W.a₂*x^2*x₀*y₀^2 + 16*W.a₁*W.a₂*x*x₀^5 + 32*W.a₁*W.a₂*x*x₀^2*y*y₀ - 16*W.a₁*W.a₂*x*x₀^2*y₀^2 + 8*W.a₁*W.a₂*x₀^6 - 16*W.a₁*W.a₂*x₀^3*y*y₀ + 8*W.a₁*W.a₂*x₀^3*y₀^2 - 4*W.a₁*W.a₃*W.a₄*x^2*y₀ + 8*W.a₁*W.a₃*W.a₄*x*x₀*y₀ - 4*W.a₁*W.a₃*W.a₄*x₀^2*y₀ + 4*W.a₁*W.a₃*x^4*y₀ - 16*W.a₁*W.a₃*x^3*x₀*y₀ + 12*W.a₁*W.a₃*x^2*x₀^2*y₀ + 8*W.a₁*W.a₃*x*x₀^3*y₀ - 8*W.a₁*W.a₃*x₀^4*y₀ + 4*W.a₁*W.a₄^2*x^2*x₀ - 8*W.a₁*W.a₄^2*x*x₀^2 + 4*W.a₁*W.a₄^2*x₀^3 + 4*W.a₁*W.a₄*W.a₆*x^2 - 8*W.a₁*W.a₄*W.a₆*x*x₀ + 4*W.a₁*W.a₄*W.a₆*x₀^2 + 4*W.a₁*W.a₄*x^5 - 24*W.a₁*W.a₄*x^4*x₀ + 56*W.a₁*W.a₄*x^3*x₀^2 - 48*W.a₁*W.a₄*x^2*x₀^3 - 8*W.a₁*W.a₄*x^2*y*y₀ + 4*W.a₁*W.a₄*x^2*y₀^2 + 4*W.a₁*W.a₄*x*x₀^4 + 16*W.a₁*W.a₄*x*x₀*y*y₀ - 8*W.a₁*W.a₄*x*x₀*y₀^2 + 8*W.a₁*W.a₄*x₀^5 - 8*W.a₁*W.a₄*x₀^2*y*y₀ + 4*W.a₁*W.a₄*x₀^2*y₀^2 - 4*W.a₁*W.a₆*x^4 + 16*W.a₁*W.a₆*x^3*x₀ - 12*W.a₁*W.a₆*x^2*x₀^2 - 8*W.a₁*W.a₆*x*x₀^3 + 8*W.a₁*W.a₆*x₀^4 + 12*W.a₁*x^5*x₀^2 - 64*W.a₁*x^4*x₀^3 + 4*W.a₁*x^4*y*y₀ + 136*W.a₁*x^3*x₀^4 - 16*W.a₁*x^3*x₀*y*y₀ - 132*W.a₁*x^2*x₀^5 + 12*W.a₁*x^2*x₀^2*y₀^2 + 52*W.a₁*x*x₀^6 + 32*W.a₁*x*x₀^3*y*y₀ - 24*W.a₁*x*x₀^3*y₀^2 - 4*W.a₁*x₀^7 - 20*W.a₁*x₀^4*y*y₀ + 12*W.a₁*x₀^4*y₀^2 + 16*W.a₂^2*x^2*x₀^2*y - 16*W.a₂^2*x^2*x₀^2*y₀ - 32*W.a₂^2*x*x₀^3*y + 32*W.a₂^2*x*x₀^3*y₀ + 16*W.a₂^2*x₀^4*y - 16*W.a₂^2*x₀^4*y₀ + 16*W.a₂*W.a₄*x^2*x₀*y - 16*W.a₂*W.a₄*x^2*x₀*y₀ - 32*W.a₂*W.a₄*x*x₀^2*y + 32*W.a₂*W.a₄*x*x₀^2*y₀ + 16*W.a₂*W.a₄*x₀^3*y - 16*W.a₂*W.a₄*x₀^3*y₀ - 8*W.a₂*x^4*x₀*y + 8*W.a₂*x^4*x₀*y₀ + 32*W.a₂*x^3*x₀^2*y - 32*W.a₂*x^3*x₀^2*y₀ - 64*W.a₂*x*x₀^4*y + 64*W.a₂*x*x₀^4*y₀ + 40*W.a₂*x₀^5*y - 40*W.a₂*x₀^5*y₀ + 4*W.a₄^2*x^2*y - 4*W.a₄^2*x^2*y₀ - 8*W.a₄^2*x*x₀*y + 8*W.a₄^2*x*x₀*y₀ + 4*W.a₄^2*x₀^2*y - 4*W.a₄^2*x₀^2*y₀ - 4*W.a₄*x^4*y + 4*W.a₄*x^4*y₀ + 16*W.a₄*x^3*x₀*y - 16*W.a₄*x^3*x₀*y₀ - 32*W.a₄*x*x₀^3*y + 32*W.a₄*x*x₀^3*y₀ + 20*W.a₄*x₀^4*y - 20*W.a₄*x₀^4*y₀ - 12*x^4*x₀^2*y + 12*x^4*x₀^2*y₀ + 48*x^3*x₀^3*y - 48*x^3*x₀^3*y₀ - 36*x^2*x₀^4*y + 36*x^2*x₀^4*y₀ - 24*x*x₀^5*y + 24*x*x₀^5*y₀ + 24*x₀^6*y - 24*x₀^6*y₀) * hgy

end CommRing

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

noncomputable def velu2X (x₀ y₀ x : F) : F :=
  x + W.veluGx x₀ y₀ / (x - x₀)

noncomputable def velu2Y (x₀ y₀ x y : F) : F :=
  y - W.veluGx x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) / (x - x₀) ^ 2

lemma velu2X_eq_div (x₀ y₀ : F) {x : F} (hx : x ≠ x₀) :
    W.velu2X x₀ y₀ x = W.velu2XNum x₀ y₀ x / (x - x₀) ^ 2 := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [velu2X, velu2XNum]
  field_simp

lemma velu2Y_eq_div (x₀ y₀ : F) {x : F} (y : F) (hx : x ≠ x₀) :
    W.velu2Y x₀ y₀ x y = W.velu2YNum x₀ y₀ x y / (x - x₀) ^ 3 := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [velu2Y, velu2YNum]
  field_simp

theorem velu2_map_equation (hchar : (2 : F) ≠ 0) {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) :
    (W.veluQuotient2 x₀ y₀).toAffine.Equation
      (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y) := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have h4 : (4 : F) ≠ 0 := fun hcon =>
    hchar (mul_self_eq_zero.mp (by rw [show ((2 : F) * 2) = 4 from by norm_num, hcon]))
  have key := mul_left_cancel₀ h4 (W.velu2_equation_cleared_four hP hQ hgy)
  rw [Affine.equation_iff, W.velu2X_eq_div x₀ y₀ hx, W.velu2Y_eq_div x₀ y₀ y hx]
  simp only [veluQuotient2_a₁, veluQuotient2_a₂, veluQuotient2_a₃, veluQuotient2_a₄,
    veluQuotient2_a₆]
  field_simp
  linear_combination key

variable {W} in

theorem velu2_map_nonsingular (hchar : (2 : F) ≠ 0) {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    (W.veluQuotient2 x₀ y₀).toAffine.Nonsingular
      (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y) :=
  ((W.veluQuotient2 x₀ y₀).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
    (W.velu2_map_equation hchar hP hQ hgy hx)

variable {W}
variable (hchar : (2 : F) ≠ 0) {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀)
  (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)

open scoped Classical in
set_option linter.unusedVariables false in

noncomputable def veluPointMap2 :
    W.toAffine.Point → (W.veluQuotient2 x₀ y₀).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hx : x = x₀ then .zero
    else .some _ _ (velu2_map_nonsingular hchar h.1 hQ hgy hx hΔ)

@[simp] lemma veluPointMap2_zero : veluPointMap2 hchar hQ hgy hΔ .zero = .zero := rfl

lemma veluPointMap2_some_of_eq {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x = x₀) :
    veluPointMap2 hchar hQ hgy hΔ (.some x y h) = .zero := by
  simp only [veluPointMap2]
  exact dif_pos hx

lemma veluPointMap2_some_of_ne {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x ≠ x₀) :
    veluPointMap2 hchar hQ hgy hΔ (.some x y h)
      = .some _ _ (velu2_map_nonsingular hchar h.1 hQ hgy hx hΔ) := by
  simp only [veluPointMap2]
  exact dif_neg hx

end Field

end WeierstrassCurve


