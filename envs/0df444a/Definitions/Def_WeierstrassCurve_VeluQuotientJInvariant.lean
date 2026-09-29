-- Prove2me | Definitions.Def_WeierstrassCurve_VeluQuotientJInvariant
-- name    : WeierstrassCurve_VeluQuotientJInvariant
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/090dabe9-cb90-54f5-838c-7bdfaa5d8e89
-- title:
--   Invariants c4​, c6​ and j of Vélu quotient curves
-- statement:
--   For a Weierstrass curve $W$ over a commutative ring $R$ and a finite set $S \subseteq R \times R$, the Vélu quotient $W/S$ is the curve with $a_1, a_2, a_3$ unchanged, $a_4' = a_4 - 5T$ and $a_6' = a_6 - b_2 T - 7U$, where $T =$ `veluTSum` $= \sum_{P \in S} (6x_P^2 + b_2 x_P + b_4)$ and $U =$ `veluWSum` $= \sum_{P \in S} \bigl(g_y(P)^2 + x_P(6x_P^2 + b_2x_P + b_4)\bigr)$, with $g_y(x,y) = -(2y + a_1x + a_3)$; no hypothesis is imposed on $S$ in this module. The lemmas `veluQuotient_c₄'` and `veluQuotient_c₆` record the resulting invariants: $c_4(W/S) = c_4(W) + 240\,T$ and $c_6(W/S) = c_6(W) + 504\,b_2(W)\,T + 6048\,U$. `Δ_mul_j` is the general identity $\Delta \cdot j = c_4^3$ for any Weierstrass curve carrying an `IsElliptic` instance (so that $\Delta$ is a unit and $j$ is defined), and `veluQuotient_Δ_mul_j` specialises it to $\Delta(W/S)\, j(W/S) = (c_4(W) + 240\,T)^3$. Over a field $F$, assuming only $\Delta(W/S) \neq 0$ (which supplies the ellipticity needed for $j$), `veluQuotient_j` gives $j(W/S) = (c_4(W) + 240\,T)^3/\Delta(W/S)$ and `veluQuotient_j_mul_Δ_of_ne_zero` the cleared-denominator form.
--
--   The namespace `VeluQuotientJGates` instantiates all of this on the curve $W : y^2 + y = x^3$ over $\mathbb{Q}$ (coefficients $(0,0,1,0,0)$) with $S_0 = \{(0,0)\}$, a point on the affine curve. There $T = 0$ and $U = 1$, the quotient is $y^2 + y = x^3 - 7$, and its invariants are $c_4 = 0$, $c_6 = 5832$, $\Delta = -19683$, so that the quotient is elliptic and $j(W/S_0) = 0$.
--
--   **Relation to Mathlib.** The curve type and the invariants $b_i$, $c_4$, $c_6$, $\Delta$, $\Delta'$, `IsElliptic` and $j$ are Mathlib's; `Δ_mul_j` is a general lemma about Mathlib's $j$ for elliptic Weierstrass curves. The Vélu data $g_x, g_y, T, U, W$ and the quotient curve `veluQuotient` are the project's own definitions, Mathlib having no Vélu construction.
--
--   **Where it is used.** These formulae make the invariants of a Vélu quotient explicit in terms of the invariants of the original curve and the sums $T$ and $U$ over the chosen finite set of points, as needed when passing between isogenous elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_VeluQuotientJInvariant.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluQuotientMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (S : Finset (R × R))

lemma veluQuotient_c₄' : (W.veluQuotient S).c₄ = W.c₄ + 240 * W.veluTSum S := by
  simp only [c₄, veluQuotient_b₂, veluQuotient_b₄]
  ring

lemma veluQuotient_c₆ :
    (W.veluQuotient S).c₆ = W.c₆ + 504 * W.b₂ * W.veluTSum S + 6048 * W.veluWSum S := by
  simp only [c₆, veluQuotient_b₂, veluQuotient_b₄, veluQuotient_b₆]
  ring

theorem Δ_mul_j (V : WeierstrassCurve R) [V.IsElliptic] : V.Δ * V.j = V.c₄ ^ 3 := by
  rw [j, ← coe_Δ', ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

theorem veluQuotient_Δ_mul_j [(W.veluQuotient S).IsElliptic] :
    (W.veluQuotient S).Δ * (W.veluQuotient S).j = (W.c₄ + 240 * W.veluTSum S) ^ 3 := by
  rw [Δ_mul_j, veluQuotient_c₄']

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F))

theorem veluQuotient_j (hΔ : (W.veluQuotient S).Δ ≠ 0) :
    haveI : (W.veluQuotient S).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (W.veluQuotient S).j = (W.c₄ + 240 * W.veluTSum S) ^ 3 / (W.veluQuotient S).Δ := by
  haveI : (W.veluQuotient S).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  rw [eq_div_iff hΔ, mul_comm]
  exact veluQuotient_Δ_mul_j W S

theorem veluQuotient_j_mul_Δ_of_ne_zero (hΔ : (W.veluQuotient S).Δ ≠ 0) :
    haveI : (W.veluQuotient S).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (W.veluQuotient S).j * (W.veluQuotient S).Δ = (W.c₄ + 240 * W.veluTSum S) ^ 3 := by
  haveI : (W.veluQuotient S).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  rw [mul_comm]; exact veluQuotient_Δ_mul_j W S

end Field

namespace VeluQuotientJGates

def W27a3 : WeierstrassCurve ℚ := ⟨0, 0, 1, 0, 0⟩

def S₀ : Finset (ℚ × ℚ) := {(0, 0)}

example : W27a3.toAffine.Equation 0 0 := by
  rw [Affine.equation_iff]; simp [W27a3]

lemma veluTSum_S₀ : W27a3.veluTSum S₀ = 0 := by
  simp [W27a3, S₀, veluTSum, veluT_eq, b₂, b₄]

lemma veluWSum_S₀ : W27a3.veluWSum S₀ = 1 := by
  simp [W27a3, S₀, veluWSum, veluW, veluU, veluGy, veluT_eq, b₂, b₄]

theorem veluQuotient_27a3_eq : W27a3.veluQuotient S₀ = ⟨0, 0, 1, 0, -7⟩ := by
  ext <;>
    simp only [veluQuotient_a₁, veluQuotient_a₂, veluQuotient_a₃, veluQuotient_a₄,
      veluQuotient_a₆, veluTSum_S₀, veluWSum_S₀] <;>
    simp [W27a3, b₂]

theorem c₄_veluQuotient_27a3 : (W27a3.veluQuotient S₀).c₄ = 0 := by
  rw [veluQuotient_c₄', veluTSum_S₀]
  simp [W27a3, c₄, b₂, b₄]

theorem c₆_veluQuotient_27a3 : (W27a3.veluQuotient S₀).c₆ = 5832 := by
  rw [veluQuotient_c₆, veluTSum_S₀, veluWSum_S₀]
  simp only [W27a3, c₆, b₂, b₄, b₆]
  norm_num

theorem Δ_veluQuotient_27a3 : (W27a3.veluQuotient S₀).Δ = -19683 := by
  rw [veluQuotient_Δ, veluTSum_S₀, veluWSum_S₀]
  simp only [W27a3, Δ, b₂, b₄, b₆, b₈]
  norm_num

instance instIsElliptic27a4 : (W27a3.veluQuotient S₀).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [Δ_veluQuotient_27a3]; norm_num)⟩

theorem j_veluQuotient_27a3 : (W27a3.veluQuotient S₀).j = 0 := by
  have hΔ : (W27a3.veluQuotient S₀).Δ ≠ 0 := by rw [Δ_veluQuotient_27a3]; norm_num
  rw [veluQuotient_j W27a3 S₀ hΔ, veluTSum_S₀]
  simp [W27a3, c₄, b₂, b₄]

example : (1728 : ℚ) * (-19683) = (0 : ℚ) ^ 3 - (5832 : ℚ) ^ 2 := by norm_num

example : S₀.Nonempty := ⟨(0, 0), Finset.mem_singleton_self _⟩

end VeluQuotientJGates

end WeierstrassCurve


