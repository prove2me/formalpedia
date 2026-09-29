-- Prove2me | Definitions.Def_WeierstrassCurve_LegendreModulus
-- name    : WeierstrassCurve_LegendreModulus
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/431e67d0-40a5-5d4a-8f82-200eedd6c16e
-- title:
--   Third two-torsion abscissa and Legendre modulus of a Weierstrass curve
-- statement:
--   For a Weierstrass curve $W$ over a field $F$, with coefficients $a_1,\dots,a_6$ and $b_2 = a_1^2 + 4a_2$, two quantities attached to an ordered pair $x_1,x_2 \in F$ are defined. First, `W.thirdTwoTorsionX x₁ x₂` is $-b_2/4 - x_1 - x_2$; since the abscissae of the three points of order two are the roots of $4x^3 + b_2x^2 + 2b_4x + b_6$, whose sum is $-b_2/4$, this is the abscissa of the third two-torsion point when $x_1,x_2$ are abscissae of two of them. Second, the Legendre modulus `W.legendreLambda x₁ x₂` is the ratio $(\mathrm{thirdTwoTorsionX}(x_1,x_2) - x_1)/(x_2 - x_1)$; a restatement lemma records it in the fully unfolded form $(-b_2/4 - x_1 - x_2 - x_1)/(x_2-x_1)$. Both are total functions of $x_1,x_2$ (with the usual value $0$ of division by zero when $x_1 = x_2$), meaningful in characteristic $\neq 2$. Third, for $w \neq 0$, `W.legendreVariableChange x₁ w hw` is the Weierstrass change of coordinates with data $(u,r,s,t) = (w,\ x_1,\ -a_1/2,\ -(a_3 + x_1a_1)/2)$; four component lemmas record these entries.
--
--   The module then establishes the expected behaviour. For $2 \neq 0$ in $F$, the Legendre curve $y^2 = x(x-1)(x-t)$, given by the coefficient tuple $(0,-(1+t),0,t,0)$, has third abscissa and Legendre modulus at $(x_1,x_2) = (0,1)$ both equal to $t$. Under a change of coordinates $C = (u,r,s,t)$ and with $2 \neq 0$, the third abscissa transforms by $x \mapsto u^2x + r$, namely $W.\mathrm{thirdTwoTorsionX}(u^2x_1+r, u^2x_2+r) = u^2\,(C \cdot W).\mathrm{thirdTwoTorsionX}(x_1,x_2) + r$, whence the modulus is invariant: $W.\mathrm{legendreLambda}(u^2x_1+r, u^2x_2+r) = (C\cdot W).\mathrm{legendreLambda}(x_1,x_2)$. Finally, for a ring homomorphism $\varphi : F \to K$ of fields, both quantities commute with base change along $\varphi$.
--
--   **Relation to Mathlib.** Built on Mathlib's `WeierstrassCurve`, its invariant `b₂`, the `VariableChange` action and base change `map`; the third two-torsion abscissa, the Legendre modulus and the associated coordinate change are the project's own definitions, as is `legendreCurve`.
--
--   **Where it is used.** These definitions provide the Legendre parametrisation of a Weierstrass curve equipped with an ordered pair of two-torsion abscissae, used in the treatment of curves with rational two-torsion and of the Hasse invariant on the Legendre family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_LegendreModulus.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve

variable {F : Type*} [Field F]

def thirdTwoTorsionX (W : WeierstrassCurve F) (x₁ x₂ : F) : F := -W.b₂ / 4 - x₁ - x₂

def legendreLambda (W : WeierstrassCurve F) (x₁ x₂ : F) : F :=
  (W.thirdTwoTorsionX x₁ x₂ - x₁) / (x₂ - x₁)

def legendreVariableChange (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) : VariableChange F :=
  ⟨Units.mk0 w hw, x₁, -W.a₁ / 2, -(W.a₃ + x₁ * W.a₁) / 2⟩

@[simp] theorem legendreVariableChange_u (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) :
    ((W.legendreVariableChange x₁ w hw).u : F) = w := rfl

@[simp] theorem legendreVariableChange_r (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) :
    (W.legendreVariableChange x₁ w hw).r = x₁ := rfl

@[simp] theorem legendreVariableChange_s (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) :
    (W.legendreVariableChange x₁ w hw).s = -W.a₁ / 2 := rfl

@[simp] theorem legendreVariableChange_t (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) :
    (W.legendreVariableChange x₁ w hw).t = -(W.a₃ + x₁ * W.a₁) / 2 := rfl

theorem legendreLambda_def (W : WeierstrassCurve F) (x₁ x₂ : F) :
    W.legendreLambda x₁ x₂ = (-W.b₂ / 4 - x₁ - x₂ - x₁) / (x₂ - x₁) := rfl

theorem thirdTwoTorsionX_legendreCurve (h2 : (2 : F) ≠ 0) (t : F) :
    (legendreCurve t).thirdTwoTorsionX 0 1 = t := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  simp only [thirdTwoTorsionX, legendreCurve, WeierstrassCurve.b₂]
  field_simp
  ring

theorem legendreLambda_legendreCurve (h2 : (2 : F) ≠ 0) (t : F) :
    (legendreCurve t).legendreLambda 0 1 = t := by
  rw [legendreLambda, thirdTwoTorsionX_legendreCurve h2]; simp

theorem thirdTwoTorsionX_variableChange (h2 : (2 : F) ≠ 0) (C : VariableChange F)
    (W : WeierstrassCurve F) (x₁ x₂ : F) :
    W.thirdTwoTorsionX ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
      = (C.u : F) ^ 2 * (C • W).thirdTwoTorsionX x₁ x₂ + C.r := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [thirdTwoTorsionX, variableChange_b₂, Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem legendreLambda_variableChange (h2 : (2 : F) ≠ 0) (C : VariableChange F)
    (W : WeierstrassCurve F) (x₁ x₂ : F) :
    W.legendreLambda ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
      = (C • W).legendreLambda x₁ x₂ := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hu2 : (C.u : F) ^ 2 ≠ 0 := pow_ne_zero 2 hu
  rw [legendreLambda, legendreLambda, thirdTwoTorsionX_variableChange h2]
  rw [show (C.u : F) ^ 2 * (C • W).thirdTwoTorsionX x₁ x₂ + C.r - ((C.u : F) ^ 2 * x₁ + C.r)
      = (C.u : F) ^ 2 * ((C • W).thirdTwoTorsionX x₁ x₂ - x₁) by ring,
    show (C.u : F) ^ 2 * x₂ + C.r - ((C.u : F) ^ 2 * x₁ + C.r) = (C.u : F) ^ 2 * (x₂ - x₁) by ring,
    mul_div_mul_left _ _ hu2]

theorem thirdTwoTorsionX_map {K : Type*} [Field K] (φ : F →+* K) (W : WeierstrassCurve F)
    (x₁ x₂ : F) :
    (W.map φ).thirdTwoTorsionX (φ x₁) (φ x₂) = φ (W.thirdTwoTorsionX x₁ x₂) := by
  simp [thirdTwoTorsionX, WeierstrassCurve.map_b₂, map_div₀, map_sub, map_neg, map_ofNat]

theorem legendreLambda_map {K : Type*} [Field K] (φ : F →+* K) (W : WeierstrassCurve F)
    (x₁ x₂ : F) :
    (W.map φ).legendreLambda (φ x₁) (φ x₂) = φ (W.legendreLambda x₁ x₂) := by
  rw [legendreLambda, legendreLambda, thirdTwoTorsionX_map, map_div₀, map_sub, map_sub]

end WeierstrassCurve


