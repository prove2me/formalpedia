-- Prove2me | Definitions.Def_WeierstrassCurve_AddFormula
-- name    : WeierstrassCurve_AddFormula
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/cca8eb70-6514-5146-a87a-333725fbd959
-- title:
--   Biquadratic x-coordinate addition identities for Weierstrass curves
-- statement:
--   For a Weierstrass curve $W$ in affine form over a field $F$, this module records identities for the $x$-coordinates produced by Mathlib's addition formulae, cleared of denominators. Two evaluation lemmas compute the relevant division polynomials at a point: `eval_Ψ₂Sq` gives $\Psi_2^2(x) = 4x^3 + b_2x^2 + 2b_4x + b_6$ and `eval_Φ_two` gives $\Phi_2(x) = x^4 - b_4x^2 - 2b_6x - b_8$; `sq_sub_negY_eq_eval_Ψ₂Sq` states that for $(x,y)$ satisfying the affine equation, $(y - \mathrm{negY}(x,y))^2 = \Psi_2^2(x)$, where $\mathrm{negY}(x,y) = -y - a_1x - a_3$. A preparatory lemma, `addX_mul_sq_of_X_ne`, expresses $\mathrm{addX}$ at the secant slope through $(x_1,y_1)$ and $(x_2,y_2)$ with $x_1 \neq x_2$, multiplied by $(x_1-x_2)^2$, as $(y_1-y_2)^2 + a_1(y_1-y_2)(x_1-x_2) - (a_2+x_1+x_2)(x_1-x_2)^2$; it assumes only $x_1 \neq x_2$ and no equation for the points.
--
--   The two main results are the biquadratic relations between the $x$-coordinates of the sum and the difference. For points $(x_1,y_1)$, $(x_2,y_2)$ on $W$ with $x_1 \neq x_2$, writing $X_+$ for $\mathrm{addX}$ at the slope through $(x_1,y_1)$ and $(x_2,y_2)$ and $X_-$ for $\mathrm{addX}$ at the slope through $(x_1,y_1)$ and $(x_2, \mathrm{negY}(x_2,y_2))$, one has
--   $$(X_+ + X_-)(x_1-x_2)^2 = 2x_1x_2(x_1+x_2) + b_2x_1x_2 + b_4(x_1+x_2) + b_6,$$
--   $$X_+X_-\,(x_1-x_2)^2 = (x_1x_2)^2 - b_4x_1x_2 - b_6(x_1+x_2) - b_8.$$
--   The doubling case is treated separately: for $(x_1,y_1)$ on $W$ with $y_1 \neq \mathrm{negY}(x_1,y_1)$, `addX_self_mul_sq_of_Y_ne` clears the tangent-slope denominator, and `addX_self_mul_Ψ₂Sq` together with its restatement `addX_self_mul_ΨSq_two` assert that the doubled $x$-coordinate satisfies $x(2P)\,\Psi_2^2(x_1) = \Phi_2(x_1)$, the second version phrasing $\Psi_2^2$ as the value of $\mathrm{ΨSq}\,2$.
--
--   **Relation to Mathlib.** No new notions are introduced: $W$, its coefficients $b_2,b_4,b_6,b_8$, the predicate `Equation`, `negY`, `slope`, `addX` and the division polynomials `Ψ₂Sq`, `ΨSq`, `Φ` are all Mathlib's; the module adds identities about them.
--
--   **Where it is used.** These identities are the curve-side input for arguments that work only with $x$-coordinates of points on a Weierstrass curve, for instance in comparing the group law with a uniformisation where sum and difference enter symmetrically.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_AddFormula.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

section evalLemmas

lemma eval_Ψ₂Sq (x : F) : W.Ψ₂Sq.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [Ψ₂Sq]

lemma eval_Φ_two (x : F) :
    (W.Φ 2).eval x = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
  simp [Φ_two]

lemma sq_sub_negY_eq_eval_Ψ₂Sq {x y : F} (h : W.Equation x y) :
    (y - W.negY x y) ^ 2 = W.Ψ₂Sq.eval x := by
  rw [equation_iff] at h
  rw [eval_Ψ₂Sq, negY, b₂, b₄, b₆]
  linear_combination 4 * h

end evalLemmas

section slope

variable [DecidableEq F]

lemma addX_mul_sq_of_X_ne {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ ≠ x₂) :
    W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) ^ 2 =
      (y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) - (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  rw [slope_of_X_ne hx, addX]
  field_simp
  ring

theorem addX_add_addX_negY_mul_sq {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁)
    (h₂ : W.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) +
        W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂))) * (x₁ - x₂) ^ 2 =
      2 * (x₁ * x₂) * (x₁ + x₂) + W.b₂ * (x₁ * x₂) + W.b₄ * (x₁ + x₂) + W.b₆ := by
    have e₁ := addX_mul_sq_of_X_ne (W := W) y₁ y₂ hx
    have e₂ := addX_mul_sq_of_X_ne (W := W) y₁ (W.negY x₂ y₂) hx
    rw [equation_iff] at h₁ h₂
    rw [add_mul, e₁, e₂, negY, b₂, b₄, b₆]
    linear_combination 2 * h₁ + 2 * h₂

theorem addX_mul_addX_negY_mul_sq {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁)
    (h₂ : W.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) *
        W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) * (x₁ - x₂) ^ 2 =
      (x₁ * x₂) ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈ := by
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hd2 : (x₁ - x₂) ^ 2 ≠ 0 := pow_ne_zero 2 hd
    have e₁ := addX_mul_sq_of_X_ne (W := W) y₁ y₂ hx
    have e₂ := addX_mul_sq_of_X_ne (W := W) y₁ (W.negY x₂ y₂) hx

    have key : ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
          (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) *
        ((y₁ - W.negY x₂ y₂) ^ 2 + W.a₁ * (y₁ - W.negY x₂ y₂) * (x₁ - x₂) -
          (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) =
        ((x₁ * x₂) ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈) * (x₁ - x₂) ^ 2 := by
      rw [equation_iff] at h₁ h₂
      rw [negY, b₄, b₆, b₈]
      linear_combination
        (W.a₁ ^ 2 * x₁ * x₂ - W.a₁ ^ 2 * x₂ ^ 2 + W.a₁ * W.a₃ * x₁ - W.a₁ * W.a₃ * x₂ +
            W.a₁ * x₁ * y₁ - 2 * W.a₁ * x₂ * y₂ - W.a₂ * x₁ ^ 2 + 4 * W.a₂ * x₁ * x₂ -
            2 * W.a₂ * x₂ ^ 2 + W.a₃ * y₁ - 2 * W.a₃ * y₂ + W.a₄ * x₁ + W.a₆ - x₁ ^ 3 +
            2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - 2 * x₂ ^ 3 + y₁ ^ 2 - 2 * y₂ ^ 2) * h₁ +
        (-W.a₁ ^ 2 * x₁ ^ 2 + W.a₁ ^ 2 * x₁ * x₂ - W.a₁ * W.a₃ * x₁ + W.a₁ * W.a₃ * x₂ +
            W.a₁ * x₂ * y₂ - 4 * W.a₂ * x₁ ^ 2 + 4 * W.a₂ * x₁ * x₂ - W.a₂ * x₂ ^ 2 +
            W.a₃ * y₂ - 2 * W.a₄ * x₁ + W.a₄ * x₂ - W.a₆ - 4 * x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ +
            2 * x₁ * x₂ ^ 2 - x₂ ^ 3 + y₂ ^ 2) * h₂
    apply mul_left_cancel₀ hd2
    calc (x₁ - x₂) ^ 2 * (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) *
            W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) * (x₁ - x₂) ^ 2)
        = (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) ^ 2) *
            (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) * (x₁ - x₂) ^ 2) := by ring
      _ = ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
              (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) *
            ((y₁ - W.negY x₂ y₂) ^ 2 + W.a₁ * (y₁ - W.negY x₂ y₂) * (x₁ - x₂) -
              (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) := by rw [e₁, e₂]
      _ = ((x₁ * x₂) ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈) * (x₁ - x₂) ^ 2 := key
      _ = (x₁ - x₂) ^ 2 *
            ((x₁ * x₂) ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈) := by ring

lemma addX_self_mul_sq_of_Y_ne {x₁ y₁ : F} (hy : y₁ ≠ W.negY x₁ y₁) :
    W.addX x₁ x₁ (W.slope x₁ x₁ y₁ y₁) * (y₁ - W.negY x₁ y₁) ^ 2 =
      (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) ^ 2 +
        W.a₁ * (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) * (y₁ - W.negY x₁ y₁) -
        (W.a₂ + x₁ + x₁) * (y₁ - W.negY x₁ y₁) ^ 2 := by
  have hψ : y₁ - W.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
  rw [slope_of_Y_ne rfl hy, addX]
  field_simp
  ring

theorem addX_self_mul_Ψ₂Sq {x₁ y₁ : F} (h₁ : W.Equation x₁ y₁) (hy : y₁ ≠ W.negY x₁ y₁) :
    W.addX x₁ x₁ (W.slope x₁ x₁ y₁ y₁) * W.Ψ₂Sq.eval x₁ = (W.Φ 2).eval x₁ := by
  rw [← sq_sub_negY_eq_eval_Ψ₂Sq h₁, addX_self_mul_sq_of_Y_ne hy, eval_Φ_two]
  rw [equation_iff] at h₁
  rw [negY, b₄, b₆, b₈]
  linear_combination (-W.a₁ ^ 2 - 4 * W.a₂ - 8 * x₁) * h₁

theorem addX_self_mul_ΨSq_two {x₁ y₁ : F} (h₁ : W.Equation x₁ y₁) (hy : y₁ ≠ W.negY x₁ y₁) :
    W.addX x₁ x₁ (W.slope x₁ x₁ y₁ y₁) * (W.ΨSq 2).eval x₁ = (W.Φ 2).eval x₁ := by
  rw [ΨSq_two]
  exact addX_self_mul_Ψ₂Sq h₁ hy

end slope

end WeierstrassCurve.Affine


