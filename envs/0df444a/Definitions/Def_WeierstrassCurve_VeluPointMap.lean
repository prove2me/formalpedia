-- Prove2me | Definitions.Def_WeierstrassCurve_VeluPointMap
-- name    : WeierstrassCurve_VeluPointMap
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/9adbe525-66e5-519e-9c37-3d600c11d1a1
-- title:
--   Vélu point map for a singleton kernel
-- statement:
--   Throughout, $W$ is a Weierstrass curve over a commutative ring $R$, with the Vélu data of the imported modules: for a point $(x_0,y_0)$ one has $G_x = 3x_0^2 + 2a_2x_0 + a_4 - a_1y_0$, $G_y = -(2y_0 + a_1x_0 + a_3)$, $t = 2G_x - a_1G_y$, $u = G_y^2$, $w = u + x_0t$, and `veluQuotient {(x_0,y_0)}` is the curve with the same $a_1,a_2,a_3$ and with $a_4 - 5t$, $a_6 - b_2t - 7w$.
--
--   Two polynomial numerators are defined: `veluXNum` $= x(x-x_0)^2 + t(x-x_0) + u$ and `veluYNum` $= y(x-x_0)^3 - \bigl(u(2y + a_1x + a_3) + t(a_1(x-x_0) + y - y_0)(x-x_0) + (a_1u - G_xG_y)(x-x_0)\bigr)$. Over a field, `veluY` is the corresponding $y$-coordinate map for a finite set $S$ of pairs: $y$ minus the sum over $Q \in S$ of $u_Q(2y+a_1x+a_3)/(x-Q_1)^3 + t_Q(a_1(x-Q_1)+y-Q_2)/(x-Q_1)^2 + (a_1u_Q - G_x(Q)G_y(Q))/(x-Q_1)^2$; it reduces to $y$ for $S = \emptyset$, and for a singleton it equals `veluYNum`$/(x-x_0)^3$ when $x \neq x_0$ (with the companion statement `veluX` $=$ `veluXNum`$/(x-x_0)^2$).
--
--   The main identity `velu_singleton_equation_cleared` is the denominator-cleared form of the assertion that the pair lies on the quotient curve: if $(x,y)$ and $(x_0,y_0)$ satisfy the affine Weierstrass equation of $W$ and $x_0$ is a root of the division polynomial $\Psi_3$ of $W$, then with $X =$ `veluXNum`, $Y =$ `veluYNum`,
--   $$Y^2 + a_1XY(x-x_0) + a_3Y(x-x_0)^3 = X^3 + a_2X^2(x-x_0)^2 + (a_4-5t)X(x-x_0)^4 + (a_6-b_2t-7w)(x-x_0)^6,$$
--   proved by an explicit linear combination of the two curve equations and the relation $3x_0^4 + b_2x_0^3 + 3b_4x_0^2 + 3b_6x_0 + b_8 = 0$. Over a field, `velu_singleton_map_equation` divides this by $(x-x_0)^6$: under the same hypotheses and $x \neq x_0$, the point $(\mathrm{veluX}\,\{(x_0,y_0)\}\,x,\ \mathrm{veluY}\,\{(x_0,y_0)\}\,x\,y)$ satisfies the affine equation of `veluQuotient` $\{(x_0,y_0)\}$.
--
--   **Relation to Mathlib.** Mathlib supplies `WeierstrassCurve`, the affine equation `Affine.Equation` and the division polynomial $\Psi_3$; the Vélu quotient curve, the coordinate maps and their numerators are the project's own.
--
--   **Where it is used.** These formulas make the Vélu quotient of a Weierstrass curve by a kernel with a single non-trivial $x$-coordinate explicit at the level of points, the hypothesis $\Psi_3(x_0)=0$ selecting a kernel of order three; they are the point-map layer on which the project's explicit isogeny constructions build.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_VeluPointMap.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluQuotientMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow,
    eval_ofNat, evalEval])

namespace WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

private lemma eval_Ψ₃_eq (x : R) :
    (W.Ψ₃).eval x = 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ := by
  rw [Ψ₃]; eval_simp

def veluXNum (x₀ y₀ x : R) : R :=
  x * (x - x₀) ^ 2 + W.veluT x₀ y₀ * (x - x₀) + W.veluU x₀ y₀

def veluYNum (x₀ y₀ x y : R) : R :=
  y * (x - x₀) ^ 3 - (W.veluU x₀ y₀ * (2 * y + W.a₁ * x + W.a₃)
    + W.veluT x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * (x - x₀)
    + (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) * (x - x₀))

theorem velu_singleton_equation_cleared {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hΨ : (W.Ψ₃).eval x₀ = 0) :
    W.veluYNum x₀ y₀ x y ^ 2 + W.a₁ * W.veluXNum x₀ y₀ x * W.veluYNum x₀ y₀ x y * (x - x₀)
        + W.a₃ * W.veluYNum x₀ y₀ x y * (x - x₀) ^ 3
      = W.veluXNum x₀ y₀ x ^ 3 + W.a₂ * W.veluXNum x₀ y₀ x ^ 2 * (x - x₀) ^ 2
        + (W.a₄ - 5 * W.veluT x₀ y₀) * W.veluXNum x₀ y₀ x * (x - x₀) ^ 4
        + (W.a₆ - W.b₂ * W.veluT x₀ y₀ - 7 * W.veluW x₀ y₀) * (x - x₀) ^ 6 := by
  rw [Affine.equation_iff] at hP hQ
  rw [W.eval_Ψ₃_eq] at hΨ
  simp only [b₂, b₄, b₆, b₈] at hΨ
  simp only [veluXNum, veluYNum, veluT, veluU, veluW, veluGx, veluGy, b₂]
  linear_combination
    (W.a₁^4*x^2*x₀^2 + 2*W.a₁^4*x*x₀^3 + W.a₁^4*x₀^4 + 2*W.a₁^3*W.a₃*x^2*x₀ + 8*W.a₁^3*W.a₃*x*x₀^2 + 6*W.a₁^3*W.a₃*x₀^3 + 16*W.a₁^3*x*x₀^2*y₀ + 16*W.a₁^3*x₀^3*y₀ + 8*W.a₁^2*W.a₂*x^2*x₀^2 - 8*W.a₁^2*W.a₂*x₀^4 + W.a₁^2*W.a₃^2*x^2 + 10*W.a₁^2*W.a₃^2*x*x₀ + 13*W.a₁^2*W.a₃^2*x₀^2 + 32*W.a₁^2*W.a₃*x*x₀*y₀ + 64*W.a₁^2*W.a₃*x₀^2*y₀ + 4*W.a₁^2*W.a₄*x^2*x₀ - 4*W.a₁^2*W.a₄*x₀^3 - 2*W.a₁^2*x^4*x₀ + 4*W.a₁^2*x^3*x₀^2 + 12*W.a₁^2*x^2*x₀^3 - 4*W.a₁^2*x*x₀^4 + 16*W.a₁^2*x*x₀*y₀^2 - 10*W.a₁^2*x₀^5 + 80*W.a₁^2*x₀^2*y₀^2 + 8*W.a₁*W.a₂*W.a₃*x^2*x₀ + 16*W.a₁*W.a₂*W.a₃*x*x₀^2 - 24*W.a₁*W.a₂*W.a₃*x₀^3 + 64*W.a₁*W.a₂*x*x₀^2*y₀ - 64*W.a₁*W.a₂*x₀^3*y₀ + 4*W.a₁*W.a₃^3*x + 12*W.a₁*W.a₃^3*x₀ + 16*W.a₁*W.a₃^2*x*y₀ + 80*W.a₁*W.a₃^2*x₀*y₀ + 4*W.a₁*W.a₃*W.a₄*x^2 + 8*W.a₁*W.a₃*W.a₄*x*x₀ - 12*W.a₁*W.a₃*W.a₄*x₀^2 - 2*W.a₁*W.a₃*x^4 + 24*W.a₁*W.a₃*x^2*x₀^2 + 8*W.a₁*W.a₃*x*x₀^3 + 16*W.a₁*W.a₃*x*y₀^2 - 30*W.a₁*W.a₃*x₀^4 + 176*W.a₁*W.a₃*x₀*y₀^2 + 32*W.a₁*W.a₄*x*x₀*y₀ - 32*W.a₁*W.a₄*x₀^2*y₀ - 16*W.a₁*x^3*x₀*y₀ + 48*W.a₁*x^2*x₀^2*y₀ + 48*W.a₁*x*x₀^3*y₀ - 80*W.a₁*x₀^4*y₀ + 128*W.a₁*x₀*y₀^3 + 16*W.a₂^2*x^2*x₀^2 - 32*W.a₂^2*x*x₀^3 + 16*W.a₂^2*x₀^4 + 16*W.a₂*W.a₃^2*x*x₀ - 16*W.a₂*W.a₃^2*x₀^2 + 64*W.a₂*W.a₃*x*x₀*y₀ - 64*W.a₂*W.a₃*x₀^2*y₀ + 16*W.a₂*W.a₄*x^2*x₀ - 32*W.a₂*W.a₄*x*x₀^2 + 16*W.a₂*W.a₄*x₀^3 - 8*W.a₂*x^4*x₀ + 32*W.a₂*x^3*x₀^2 - 64*W.a₂*x*x₀^4 + 64*W.a₂*x*x₀*y₀^2 + 40*W.a₂*x₀^5 - 64*W.a₂*x₀^2*y₀^2 + 4*W.a₃^4 + 32*W.a₃^3*y₀ + 8*W.a₃^2*W.a₄*x - 8*W.a₃^2*W.a₄*x₀ - 4*W.a₃^2*x^3 + 12*W.a₃^2*x^2*x₀ + 12*W.a₃^2*x*x₀^2 - 20*W.a₃^2*x₀^3 + 96*W.a₃^2*y₀^2 + 32*W.a₃*W.a₄*x*y₀ - 32*W.a₃*W.a₄*x₀*y₀ - 16*W.a₃*x^3*y₀ + 48*W.a₃*x^2*x₀*y₀ + 48*W.a₃*x*x₀^2*y₀ - 80*W.a₃*x₀^3*y₀ + 128*W.a₃*y₀^3 + 4*W.a₄^2*x^2 - 8*W.a₄^2*x*x₀ + 4*W.a₄^2*x₀^2 - 4*W.a₄*x^4 + 16*W.a₄*x^3*x₀ - 32*W.a₄*x*x₀^3 + 32*W.a₄*x*y₀^2 + 20*W.a₄*x₀^4 - 32*W.a₄*x₀*y₀^2 + x^6 - 6*x^5*x₀ + 3*x^4*x₀^2 + 28*x^3*x₀^3 - 16*x^3*y₀^2 - 21*x^2*x₀^4 + 48*x^2*x₀*y₀^2 - 30*x*x₀^5 + 48*x*x₀^2*y₀^2 + 25*x₀^6 - 80*x₀^3*y₀^2 + 64*y₀^4) * hP
    + (2*W.a₁^4*x^3*x₀ - 4*W.a₁^4*x^2*x₀^2 - 2*W.a₁^4*x*x₀^3 + 2*W.a₁^3*W.a₃*x^3 - 2*W.a₁^3*W.a₃*x^2*x₀ - 14*W.a₁^3*W.a₃*x*x₀^2 - 2*W.a₁^3*W.a₃*x₀^3 + 12*W.a₁^3*x^2*x₀*y₀ - 40*W.a₁^3*x*x₀^2*y₀ - 4*W.a₁^3*x₀^3*y₀ + 16*W.a₁^2*W.a₂*x^3*x₀ - 44*W.a₁^2*W.a₂*x^2*x₀^2 + 24*W.a₁^2*W.a₂*x*x₀^3 + 4*W.a₁^2*W.a₂*x₀^4 + 2*W.a₁^2*W.a₃^2*x^2 - 16*W.a₁^2*W.a₃^2*x*x₀ - 10*W.a₁^2*W.a₃^2*x₀^2 + 12*W.a₁^2*W.a₃*x^2*y₀ - 56*W.a₁^2*W.a₃*x*x₀*y₀ - 52*W.a₁^2*W.a₃*x₀^2*y₀ + 4*W.a₁^2*W.a₄*x^3 - 16*W.a₁^2*W.a₄*x^2*x₀ + 12*W.a₁^2*W.a₄*x*x₀^2 + 12*W.a₁^2*W.a₆*x^2 - 24*W.a₁^2*W.a₆*x*x₀ + 12*W.a₁^2*W.a₆*x₀^2 - 6*W.a₁^2*x^5 + 32*W.a₁^2*x^4*x₀ - 28*W.a₁^2*x^3*x₀^2 - 12*W.a₁^2*x^2*x₀^3 + 12*W.a₁^2*x^2*y₀^2 - 14*W.a₁^2*x*x₀^4 - 40*W.a₁^2*x*x₀*y₀^2 + 28*W.a₁^2*x₀^5 - 68*W.a₁^2*x₀^2*y₀^2 + 8*W.a₁*W.a₂*W.a₃*x^3 - 8*W.a₁*W.a₂*W.a₃*x^2*x₀ - 40*W.a₁*W.a₂*W.a₃*x*x₀^2 + 40*W.a₁*W.a₂*W.a₃*x₀^3 + 48*W.a₁*W.a₂*x^2*x₀*y₀ - 160*W.a₁*W.a₂*x*x₀^2*y₀ + 112*W.a₁*W.a₂*x₀^3*y₀ - 4*W.a₁*W.a₃^3*x - 12*W.a₁*W.a₃^3*x₀ - 16*W.a₁*W.a₃^2*x*y₀ - 80*W.a₁*W.a₃^2*x₀*y₀ - 16*W.a₁*W.a₃*W.a₄*x^2 + 16*W.a₁*W.a₃*W.a₄*x*x₀ + 2*W.a₁*W.a₃*x^4 + 24*W.a₁*W.a₃*x^3*x₀ + 12*W.a₁*W.a₃*x^2*x₀^2 - 152*W.a₁*W.a₃*x*x₀^3 - 16*W.a₁*W.a₃*x*y₀^2 + 114*W.a₁*W.a₃*x₀^4 - 176*W.a₁*W.a₃*x₀*y₀^2 - 32*W.a₁*W.a₄*x*x₀*y₀ + 32*W.a₁*W.a₄*x₀^2*y₀ + 16*W.a₁*x^3*x₀*y₀ + 96*W.a₁*x^2*x₀^2*y₀ - 336*W.a₁*x*x₀^3*y₀ + 224*W.a₁*x₀^4*y₀ - 128*W.a₁*x₀*y₀^3 + 32*W.a₂^2*x^3*x₀ - 112*W.a₂^2*x^2*x₀^2 + 128*W.a₂^2*x*x₀^3 - 48*W.a₂^2*x₀^4 + 24*W.a₂*W.a₃^2*x^2 - 64*W.a₂*W.a₃^2*x*x₀ + 40*W.a₂*W.a₃^2*x₀^2 + 48*W.a₂*W.a₃*x^2*y₀ - 160*W.a₂*W.a₃*x*x₀*y₀ + 112*W.a₂*W.a₃*x₀^2*y₀ + 16*W.a₂*W.a₄*x^3 - 64*W.a₂*W.a₄*x^2*x₀ + 80*W.a₂*W.a₄*x*x₀^2 - 32*W.a₂*W.a₄*x₀^3 + 48*W.a₂*W.a₆*x^2 - 96*W.a₂*W.a₆*x*x₀ + 48*W.a₂*W.a₆*x₀^2 - 24*W.a₂*x^5 + 128*W.a₂*x^4*x₀ - 128*W.a₂*x^3*x₀^2 - 144*W.a₂*x^2*x₀^3 + 48*W.a₂*x^2*y₀^2 + 280*W.a₂*x*x₀^4 - 160*W.a₂*x*x₀*y₀^2 - 112*W.a₂*x₀^5 + 112*W.a₂*x₀^2*y₀^2 - 4*W.a₃^4 - 32*W.a₃^3*y₀ - 8*W.a₃^2*W.a₄*x + 8*W.a₃^2*W.a₄*x₀ + 4*W.a₃^2*x^3 + 60*W.a₃^2*x^2*x₀ - 156*W.a₃^2*x*x₀^2 + 92*W.a₃^2*x₀^3 - 96*W.a₃^2*y₀^2 - 32*W.a₃*W.a₄*x*y₀ + 32*W.a₃*W.a₄*x₀*y₀ + 16*W.a₃*x^3*y₀ + 96*W.a₃*x^2*x₀*y₀ - 336*W.a₃*x*x₀^2*y₀ + 224*W.a₃*x₀^3*y₀ - 128*W.a₃*y₀^3 - 16*W.a₄^2*x^2 + 32*W.a₄^2*x*x₀ - 16*W.a₄^2*x₀^2 + 4*W.a₄*x^4 + 32*W.a₄*x^3*x₀ - 72*W.a₄*x^2*x₀^2 + 32*W.a₄*x*x₀^3 - 32*W.a₄*x*y₀^2 + 4*W.a₄*x₀^4 + 32*W.a₄*x₀*y₀^2 + 144*W.a₆*x^2*x₀ - 288*W.a₆*x*x₀^2 + 144*W.a₆*x₀^3 - 72*x^5*x₀ + 372*x^4*x₀^2 - 624*x^3*x₀^3 + 16*x^3*y₀^2 + 360*x^2*x₀^4 + 96*x^2*x₀*y₀^2 + 24*x*x₀^5 - 336*x*x₀^2*y₀^2 - 60*x₀^6 + 224*x₀^3*y₀^2 - 64*y₀^4) * hQ
    + (2*W.a₁^2*x^3*x₀ - 3*W.a₁^2*x^2*x₀^2 + W.a₁^2*x₀^4 + 2*W.a₁*W.a₃*x^3 - 6*W.a₁*W.a₃*x*x₀^2 + 4*W.a₁*W.a₃*x₀^3 + 8*W.a₂*x^3*x₀ - 12*W.a₂*x^2*x₀^2 + 4*W.a₂*x₀^4 + 3*W.a₃^2*x^2 - 6*W.a₃^2*x*x₀ + 3*W.a₃^2*x₀^2 + 4*W.a₄*x^3 - 12*W.a₄*x*x₀^2 + 8*W.a₄*x₀^3 + 12*W.a₆*x^2 - 24*W.a₆*x*x₀ + 12*W.a₆*x₀^2 - 6*x^5 + 30*x^4*x₀ - 48*x^3*x₀^2 + 36*x^2*x₀^3 - 18*x*x₀^4 + 6*x₀^5) * hΨ

end CommRing

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

noncomputable def veluY (S : Finset (F × F)) (x y : F) : F :=
  y - ∑ Q ∈ S, (W.veluU Q.1 Q.2 * (2 * y + W.a₁ * x + W.a₃) / (x - Q.1) ^ 3
    + W.veluT Q.1 Q.2 * (W.a₁ * (x - Q.1) + y - Q.2) / (x - Q.1) ^ 2
    + (W.a₁ * W.veluU Q.1 Q.2 - W.veluGx Q.1 Q.2 * W.veluGy Q.1 Q.2) / (x - Q.1) ^ 2)

@[simp] lemma veluY_empty (x y : F) : W.veluY ∅ x y = y := by simp [veluY]

lemma veluX_singleton (x₀ y₀ : F) {x : F} (hx : x ≠ x₀) :
    W.veluX {(x₀, y₀)} x = W.veluXNum x₀ y₀ x / (x - x₀) ^ 2 := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [veluX, Finset.sum_singleton, veluXNum]
  field_simp
  ring

lemma veluY_singleton (x₀ y₀ : F) {x : F} (y : F) (hx : x ≠ x₀) :
    W.veluY {(x₀, y₀)} x y = W.veluYNum x₀ y₀ x y / (x - x₀) ^ 3 := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [veluY, Finset.sum_singleton, veluYNum]
  field_simp

theorem velu_singleton_map_equation {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hΨ : (W.Ψ₃).eval x₀ = 0) (hx : x ≠ x₀) :
    (W.veluQuotient {(x₀, y₀)}).toAffine.Equation
      (W.veluX {(x₀, y₀)} x) (W.veluY {(x₀, y₀)} x y) := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have key := W.velu_singleton_equation_cleared hP hQ hΨ
  rw [Affine.equation_iff, W.veluX_singleton x₀ y₀ hx, W.veluY_singleton x₀ y₀ y hx]
  simp only [veluQuotient_a₁, veluQuotient_a₂, veluQuotient_a₃, veluQuotient_a₄,
    veluQuotient_a₆, veluTSum, veluWSum, Finset.sum_singleton]
  field_simp
  linear_combination key

end Field

end WeierstrassCurve


