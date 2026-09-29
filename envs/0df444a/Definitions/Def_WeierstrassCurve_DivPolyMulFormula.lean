-- Prove2me | Definitions.Def_WeierstrassCurve_DivPolyMulFormula
-- name    : WeierstrassCurve_DivPolyMulFormula
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/d418c730-0a98-5bf5-ab94-64f11868bc3a
-- title:
--   Reduced division polynomials: multiplication formula predicates
-- statement:
--   Fix a Weierstrass curve $W$ and work with Mathlib's reduced division polynomials $\mathrm{pre\Psi}$, $\Psi^2 = \mathrm{\Psi Sq}$, $\Phi$, together with $\Psi_2^2$, $\Psi_3$, $\mathrm{pre\Psi}_4$. Three predicates are introduced. For a nonsingular affine point $(x,y)$ on $W$ over a field $F$ and $m : \mathbb{N}$, `MFred m h` asserts the conjunction $\Psi^2_m(x) \ne 0$ and $x(mP)\,\Psi^2_m(x) = \Phi_m(x)$, where $P = (x,y)$ and the left-hand factor is `xOrZero` of $m \bullet P$, i.e. the $x$-coordinate of the point, taken to be $0$ at the point at infinity. `LowTorsionFree m h` asserts that $kP \ne 0$ for every natural $k$ with $1 \le k \le m$; it is monotone in $m$. For $W$ over a commutative ring $R$ and $j : \mathbb{Z}$, `StarIdentity j` asserts the polynomial identity, evaluated at every $t \in R$,
--   $$2t\,\Phi_j(\Phi_j + t\Psi^2_j) + b_2 t\,\Phi_j\Psi^2_j + b_4(\Phi_j + t\Psi^2_j)\Psi^2_j + b_6 (\Psi^2_j)^2 = \Phi_{j+1}\Psi^2_{j-1} + \Phi_{j-1}\Psi^2_{j+1},$$
--   all terms evaluated at $t$.
--
--   The remaining declarations supply the algebra around these notions: parity-resolved forms of $\Psi^2_m$, $\Phi_m$ and of the recursions for $\mathrm{pre\Psi}$ at $2m\pm1$, $2m+2$; the consecutive-index identities $(X\Psi^2_m - \Phi_m)^2 = \Psi^2_{m+1}\Psi^2_{m-1}$, $\Phi_{m+1}\Psi^2_m - \Phi_m\Psi^2_{m+1} = -\mathrm{pre\Psi}_{2m+1}$ and $\Phi_{m+1}\Psi^2_{m-1} - \Phi_{m-1}\Psi^2_{m+1} = -\mathrm{pre\Psi}_{2m}\Psi_2^2$; closed forms at small index ($\mathrm{pre\Psi}'_5$, $\mathrm{pre\Psi}'_6$, $\mathrm{pre\Psi}'_7$, $\Psi^2_5$, $\Psi^2_7$, $\Phi_5$); the instances `ellipticNet_one` to `ellipticNet_four` of the above identity for $j \le 4$, each a long explicit expansion in $b_2,b_4,b_6,b_8$ modulo the relation $4b_8 = b_2b_6 - b_4^2$; doubling and addition formulae relating $\mathrm{addX}$ to $\Psi_2^2$ and $\Phi_2$; the induction producing `MFred` from `LowTorsionFree` together with the star identities; and the consequences linking vanishing of $\Psi^2_{m}(x)$ to $mP = 0$.
--
--   **Relation to Mathlib.** The division polynomials `preΨ`, `preΨ'`, `ΨSq`, `Φ`, `Ψ₂Sq`, `Ψ₃`, `preΨ₄` and the relation `b_relation` are Mathlib's; `xOrZero` is the project's $x$-coordinate function on affine points, extended by $0$ at infinity. The predicates `MFred`, `LowTorsionFree` and `StarIdentity` are the project's own, as are several variants of Mathlib-style lemmas on `addX` and `slope` restated for `W.toAffine`.
--
--   **Where it is used.** These identities and predicates underlie the comparison between the $x$-coordinate of $mP$ and the reduced division polynomials, and hence between torsion points and roots of $\Psi^2_m$; they feed the bounds on $p$-torsion of an elliptic curve and the Tate-curve $x$-coordinate alignment used in the net-pairing track.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_DivPolyMulFormula.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_AddFormula
import Definitions.Def_NetPairing_Basic
import Definitions.Def_TateCurve_XMultAlignment

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow,
    eval_ofNat, eval_zero, eval_one, evalEval])

universe u

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] {W : WeierstrassCurve F}

section Prerequisites

lemma sq_sub_negY' {x y : F} (h : W.toAffine.Equation x y) :
    (y - W.toAffine.negY x y) ^ 2 = (W.Ψ₂Sq).eval x := by
  rw [negY, Ψ₂Sq, b₂, b₄, b₆]
  eval_simp
  linear_combination (4 : F) * ((W.toAffine.equation_iff x y).mp h)

lemma Ψ₂Sq_eval_ne_zero' {x y : F} (h : W.toAffine.Equation x y)
    (hy : y ≠ W.toAffine.negY x y) : (W.Ψ₂Sq).eval x ≠ 0 := by
  rw [← sq_sub_negY' h]
  exact pow_ne_zero 2 (sub_ne_zero_of_ne hy)

lemma Ψ₂Sq_eval_eq_zero_iff_two_smul' [DecidableEq F] {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    (W.Ψ₂Sq).eval x = 0 ↔ (2 • Point.some x y h : W.toAffine.Point) = 0 := by
  rw [two_nsmul]
  constructor
  · intro h0
    have hy : y = W.toAffine.negY x y := by
      by_contra hy
      exact Ψ₂Sq_eval_ne_zero' h.left hy h0
    exact Point.add_self_of_Y_eq hy
  · intro h0
    by_cases hy : y = W.toAffine.negY x y
    · rw [← sq_sub_negY' h.left, sub_eq_zero.mpr hy]
      ring
    · exact absurd ((Point.add_self_of_Y_ne hy).symm.trans h0) (Point.some_ne_zero _)

lemma addX_self_mul_Ψ₂Sq' [DecidableEq F] {x y : F} (h : W.toAffine.Equation x y)
    (hy : y ≠ W.toAffine.negY x y) :
    W.toAffine.addX x x (W.toAffine.slope x x y y) * (W.Ψ₂Sq).eval x = (W.Φ 2).eval x := by
  have hd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero_of_ne hy
  have hℓ : W.toAffine.slope x x y y * (y - W.toAffine.negY x y) =
      3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [slope_of_Y_ne rfl hy, div_mul_cancel₀ _ hd]
  rw [addX, ← sq_sub_negY' h, Φ_two, b₄, b₆, b₈, negY] at *
  eval_simp
  linear_combination
    (W.toAffine.slope x x y y * (y - (-y - W.a₁ * x - W.a₃)) +
        (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) + W.a₁ * (y - (-y - W.a₁ * x - W.a₃))) * hℓ +
      (-(8 * x + W.a₁ ^ 2 + 4 * W.a₂)) * ((W.toAffine.equation_iff x y).mp h)

lemma Ψ₂Sq_comp_duplication' (x : F) :
    4 * (W.Φ 2).eval x ^ 3 + W.b₂ * ((W.Φ 2).eval x ^ 2 * (W.Ψ₂Sq).eval x) +
        2 * W.b₄ * ((W.Φ 2).eval x * (W.Ψ₂Sq).eval x ^ 2) + W.b₆ * (W.Ψ₂Sq).eval x ^ 3 =
      (W.preΨ₄).eval x ^ 2 := by
  rw [Φ_two, Ψ₂Sq, preΨ₄, b₂, b₄, b₆, b₈]
  eval_simp
  ring

end Prerequisites

section EvalLemmas

lemma eval_Ψ₂Sq' (t : F) :
    (W.Ψ₂Sq).eval t = 4 * t ^ 3 + W.b₂ * t ^ 2 + 2 * W.b₄ * t + W.b₆ := by
  rw [Ψ₂Sq]; eval_simp

lemma eval_Φ_two' (t : F) :
    (W.Φ 2).eval t = t ^ 4 - W.b₄ * t ^ 2 - 2 * W.b₆ * t - W.b₈ := by
  rw [Φ_two]; eval_simp

lemma preΨ'_five : W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
  rw [show (5 : ℕ) = 2 * (0 + 2) + 1 by rfl, preΨ'_odd]
  simp

lemma ΨSq_five : W.ΨSq 5 = (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) ^ 2 := by
  rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by rfl, ΨSq_ofNat, preΨ'_five,
    if_neg (by decide : ¬Even (5 : ℕ)), mul_one]

lemma X_mul_Ψ₂Sq_sub_Φ_two_eval (t : F) :
    t * (W.Ψ₂Sq).eval t - (W.Φ 2).eval t = (W.Ψ₃).eval t := by
  rw [Φ_two, Ψ₂Sq, Ψ₃]
  eval_simp
  ring

lemma X_mul_ΨSq_four_sub_Φ_four_eval (t : F) :
    t * ((W.preΨ₄).eval t ^ 2 * (W.Ψ₂Sq).eval t) - (W.Φ 4).eval t =
      (W.Ψ₃).eval t * ((W.preΨ₄).eval t * (W.Ψ₂Sq).eval t ^ 2 - (W.Ψ₃).eval t ^ 3) := by
  rw [Φ_four]
  eval_simp
  ring

end EvalLemmas
end WeierstrassCurve.Affine

open Polynomial WeierstrassCurve

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] {W : WeierstrassCurve F}

section Prerequisites

lemma eval_Ψ₂Sq'' (t : F) :
    (W.Ψ₂Sq).eval t = 4 * t ^ 3 + W.b₂ * t ^ 2 + 2 * W.b₄ * t + W.b₆ := by
  rw [Ψ₂Sq]; eval_simp

lemma eval_Φ_two'' (t : F) :
    (W.Φ 2).eval t = t ^ 4 - W.b₄ * t ^ 2 - 2 * W.b₆ * t - W.b₈ := by
  rw [Φ_two]; eval_simp

lemma sq_sub_negY_eq {x y : F} (h : W.toAffine.Equation x y) :
    (y - W.toAffine.negY x y) ^ 2 = (W.Ψ₂Sq).eval x := by
  rw [negY, Ψ₂Sq, b₂, b₄, b₆]
  eval_simp
  linear_combination (4 : F) * ((W.toAffine.equation_iff x y).mp h)

lemma addX_self_mul_Ψ₂Sq_eq [DecidableEq F] {x y : F} (h : W.toAffine.Equation x y)
    (hy : y ≠ W.toAffine.negY x y) :
    W.toAffine.addX x x (W.toAffine.slope x x y y) * (W.Ψ₂Sq).eval x = (W.Φ 2).eval x := by
  have hd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero_of_ne hy
  have hℓ : W.toAffine.slope x x y y * (y - W.toAffine.negY x y) =
      3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [slope_of_Y_ne rfl hy, div_mul_cancel₀ _ hd]
  rw [addX, ← sq_sub_negY_eq h, Φ_two, b₄, b₆, b₈, negY] at *
  eval_simp
  linear_combination
    (W.toAffine.slope x x y y * (y - (-y - W.a₁ * x - W.a₃)) +
        (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) + W.a₁ * (y - (-y - W.a₁ * x - W.a₃))) * hℓ +
      (-(8 * x + W.a₁ ^ 2 + 4 * W.a₂)) * ((W.toAffine.equation_iff x y).mp h)

lemma X_mul_Ψ₂Sq_sub_Φ_two (t : F) :
    t * (W.Ψ₂Sq).eval t - (W.Φ 2).eval t = (W.Ψ₃).eval t := by
  rw [Φ_two, Ψ₂Sq, Ψ₃]
  eval_simp
  ring

lemma Ψ₂Sq_comp_duplication_eq (t : F) :
    4 * (W.Φ 2).eval t ^ 3 + W.b₂ * ((W.Φ 2).eval t ^ 2 * (W.Ψ₂Sq).eval t) +
        2 * W.b₄ * ((W.Φ 2).eval t * (W.Ψ₂Sq).eval t ^ 2) + W.b₆ * (W.Ψ₂Sq).eval t ^ 3 =
      (W.preΨ₄).eval t ^ 2 := by
  rw [Φ_two, Ψ₂Sq, preΨ₄, b₂, b₄, b₆, b₈]
  eval_simp
  ring

set_option maxHeartbeats 1000000 in

lemma Φ_comp_duplication_eq (t : F) :
    (W.Φ 2).eval t ^ 4 - W.b₄ * ((W.Φ 2).eval t ^ 2 * (W.Ψ₂Sq).eval t ^ 2) -
        2 * W.b₆ * ((W.Φ 2).eval t * (W.Ψ₂Sq).eval t ^ 3) - W.b₈ * (W.Ψ₂Sq).eval t ^ 4 =
      (W.Φ 4).eval t := by
  rw [Φ_two, Φ_four, Ψ₂Sq, preΨ₄, Ψ₃, b₂, b₄, b₆, b₈]
  eval_simp
  ring

end Prerequisites

set_option maxHeartbeats 1000000 in

lemma ellipticNet_two (t : F) :
    2 * t * (W.Φ 2).eval t * ((W.Φ 2).eval t + t * (W.Ψ₂Sq).eval t) +
        W.b₂ * t * ((W.Φ 2).eval t * (W.Ψ₂Sq).eval t) +
        W.b₄ * (((W.Φ 2).eval t + t * (W.Ψ₂Sq).eval t) * (W.Ψ₂Sq).eval t) +
        W.b₆ * (W.Ψ₂Sq).eval t ^ 2 =
      (W.Φ 3).eval t + t * (W.Ψ₃).eval t ^ 2 := by
  rw [Φ_two, Φ_three, Ψ₂Sq, Ψ₃, preΨ₄, b₂, b₄, b₆, b₈]
  eval_simp
  ring

section EvalLemmas

lemma preΨ'_five_eq : W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
  rw [show (5 : ℕ) = 2 * (0 + 2) + 1 by rfl, preΨ'_odd]
  simp

lemma preΨ'_seven_eq :
    W.preΨ' 7 = (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) * W.Ψ₃ ^ 3 - W.preΨ₄ ^ 3 * W.Ψ₂Sq ^ 2 := by
  rw [show (7 : ℕ) = 2 * (1 + 2) + 1 by rfl, preΨ'_odd]
  simp only [Nat.reduceAdd, preΨ'_two, preΨ'_three, preΨ'_four, Nat.not_even_one, if_false,
    mul_one, one_mul, preΨ'_five_eq]

lemma ΨSq_seven_eq : W.ΨSq 7 =
    ((W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) * W.Ψ₃ ^ 3 - W.preΨ₄ ^ 3 * W.Ψ₂Sq ^ 2) ^ 2 := by
  rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) by rfl, ΨSq_ofNat, preΨ'_seven_eq,
    if_neg (by decide : ¬Even (7 : ℕ)), mul_one]

lemma eval_Φ_three (t : F) :
    (W.Φ 3).eval t = t * (W.Ψ₃).eval t ^ 2 - (W.preΨ₄).eval t * (W.Ψ₂Sq).eval t := by
  rw [Φ_three]; eval_simp

lemma eval_Φ_four (t : F) :
    (W.Φ 4).eval t = t * (W.preΨ₄).eval t ^ 2 * (W.Ψ₂Sq).eval t -
      (W.Ψ₃).eval t * ((W.preΨ₄).eval t * (W.Ψ₂Sq).eval t ^ 2 - (W.Ψ₃).eval t ^ 3) := by
  rw [Φ_four]; eval_simp

end EvalLemmas
end WeierstrassCurve.Affine

open Polynomial

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section ParityResolved

variable {m : ℤ}

lemma ΨSq_of_even (h : Even m) : W.ΨSq m = W.preΨ m ^ 2 * W.Ψ₂Sq := by
  rw [show W.ΨSq m = W.preΨ m ^ 2 * if Even m then W.Ψ₂Sq else 1 from rfl, if_pos h]

lemma ΨSq_of_odd (h : ¬Even m) : W.ΨSq m = W.preΨ m ^ 2 := by
  rw [show W.ΨSq m = W.preΨ m ^ 2 * if Even m then W.Ψ₂Sq else 1 from rfl, if_neg h, mul_one]

lemma Φ_of_even (h : Even m) :
    W.Φ m = X * W.ΨSq m - W.preΨ (m + 1) * W.preΨ (m - 1) := by
  rw [show W.Φ m = X * W.ΨSq m - W.preΨ (m + 1) * W.preΨ (m - 1) *
      if Even m then 1 else W.Ψ₂Sq from rfl, if_pos h, mul_one]

lemma Φ_of_odd (h : ¬Even m) :
    W.Φ m = X * W.ΨSq m - W.preΨ (m + 1) * W.preΨ (m - 1) * W.Ψ₂Sq := by
  rw [show W.Φ m = X * W.ΨSq m - W.preΨ (m + 1) * W.preΨ (m - 1) *
      if Even m then 1 else W.Ψ₂Sq from rfl, if_neg h]

lemma preΨ_odd_of_even (h : Even m) :
    W.preΨ (2 * m + 1) =
      W.preΨ (m + 2) * W.preΨ m ^ 3 * W.Ψ₂Sq ^ 2 - W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 := by
  rw [preΨ_odd, if_pos h, if_pos h, mul_one]

lemma preΨ_odd_of_odd (h : ¬Even m) :
    W.preΨ (2 * m + 1) =
      W.preΨ (m + 2) * W.preΨ m ^ 3 - W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 * W.Ψ₂Sq ^ 2 := by
  rw [preΨ_odd, if_neg h, if_neg h, mul_one]

end ParityResolved

section DoublingRewrite

variable (m : ℤ)

lemma Φ_two_mul :
    W.Φ (2 * m) = X * W.ΨSq (2 * m) - W.preΨ (2 * m + 1) * W.preΨ (2 * m - 1) :=
  W.Φ_of_even (even_two_mul m)

lemma Φ_two_mul_add_one :
    W.Φ (2 * m + 1) =
      X * W.ΨSq (2 * m + 1) - W.preΨ (2 * m + 2) * W.preΨ (2 * m) * W.Ψ₂Sq := by
  rw [W.Φ_of_odd m.not_even_two_mul_add_one, show 2 * m + 1 + 1 = 2 * m + 2 by ring,
    add_sub_cancel_right]

lemma preΨ_two_mul_sub_one_of_even {m : ℤ} (hm : Even m) :
    W.preΨ (2 * m - 1) =
      W.preΨ (m + 1) * W.preΨ (m - 1) ^ 3 - W.preΨ (m - 2) * W.preΨ m ^ 3 * W.Ψ₂Sq ^ 2 := by
  have h1 : ¬Even (m - 1) := fun h => (Int.even_sub_one.mp h) hm
  rw [show 2 * m - 1 = 2 * (m - 1) + 1 by ring, W.preΨ_odd_of_odd h1,
    show m - 1 + 2 = m + 1 by ring, show m - 1 - 1 = m - 2 by ring,
    show m - 1 + 1 = m by ring]

lemma preΨ_two_mul_sub_one_of_odd {m : ℤ} (hm : ¬Even m) :
    W.preΨ (2 * m - 1) =
      W.preΨ (m + 1) * W.preΨ (m - 1) ^ 3 * W.Ψ₂Sq ^ 2 - W.preΨ (m - 2) * W.preΨ m ^ 3 := by
  have h1 : Even (m - 1) := Int.even_sub_one.mpr hm
  rw [show 2 * m - 1 = 2 * (m - 1) + 1 by ring, W.preΨ_odd_of_even h1,
    show m - 1 + 2 = m + 1 by ring, show m - 1 - 1 = m - 2 by ring,
    show m - 1 + 1 = m by ring]

lemma preΨ_two_mul_add_two :
    W.preΨ (2 * m + 2) =
      W.preΨ m ^ 2 * W.preΨ (m + 1) * W.preΨ (m + 3) -
        W.preΨ (m - 1) * W.preΨ (m + 1) * W.preΨ (m + 2) ^ 2 := by
  rw [show 2 * m + 2 = 2 * (m + 1) by ring, preΨ_even, show m + 1 - 1 = m by ring,
    show m + 1 - 2 = m - 1 by ring, show m + 1 + 2 = m + 3 by ring,
    show m + 1 + 1 = m + 2 by ring]

end DoublingRewrite

section ConsecutiveIdentities

variable (m : ℤ)

lemma X_mul_ΨSq_sub_Φ :
    X * W.ΨSq m - W.Φ m = W.preΨ (m + 1) * W.preΨ (m - 1) * if Even m then 1 else W.Ψ₂Sq := by
  rw [show W.Φ m = X * W.ΨSq m - W.preΨ (m + 1) * W.preΨ (m - 1) *
      if Even m then 1 else W.Ψ₂Sq from rfl]
  ring

lemma X_mul_ΨSq_sub_Φ_sq :
    (X * W.ΨSq m - W.Φ m) ^ 2 = W.ΨSq (m + 1) * W.ΨSq (m - 1) := by
  rw [W.X_mul_ΨSq_sub_Φ m]
  by_cases hm : Even m
  · have hm1 : ¬Even (m + 1) := fun h => (Int.even_add_one.mp h) hm
    have hm2 : ¬Even (m - 1) := fun h => (Int.even_sub_one.mp h) hm
    rw [if_pos hm, W.ΨSq_of_odd hm1, W.ΨSq_of_odd hm2]
    ring
  · have hm1 : Even (m + 1) := Int.even_add_one.mpr hm
    have hm2 : Even (m - 1) := Int.even_sub_one.mpr hm
    rw [if_neg hm, W.ΨSq_of_even hm1, W.ΨSq_of_even hm2]
    ring

lemma Φ_succ_mul_ΨSq_sub_Φ_mul_ΨSq_succ :
    W.Φ (m + 1) * W.ΨSq m - W.Φ m * W.ΨSq (m + 1) = -W.preΨ (2 * m + 1) := by
  by_cases hm : Even m
  · have hm1 : ¬Even (m + 1) := fun h => (Int.even_add_one.mp h) hm
    rw [W.Φ_of_odd hm1, W.Φ_of_even hm, W.ΨSq_of_even hm, W.ΨSq_of_odd hm1,
      W.preΨ_odd_of_even hm, show m + 1 + 1 = m + 2 by ring, add_sub_cancel_right]
    ring
  · have hm1 : Even (m + 1) := Int.even_add_one.mpr hm
    rw [W.Φ_of_even hm1, W.Φ_of_odd hm, W.ΨSq_of_odd hm, W.ΨSq_of_even hm1,
      W.preΨ_odd_of_odd hm, show m + 1 + 1 = m + 2 by ring, add_sub_cancel_right]
    ring

lemma Φ_succ_mul_ΨSq_pred_sub_Φ_pred_mul_ΨSq_succ :
    W.Φ (m + 1) * W.ΨSq (m - 1) - W.Φ (m - 1) * W.ΨSq (m + 1) =
      -(W.preΨ (2 * m) * W.Ψ₂Sq) := by
  by_cases hm : Even m
  · have hm1 : ¬Even (m + 1) := fun h => (Int.even_add_one.mp h) hm
    have hm2 : ¬Even (m - 1) := fun h => (Int.even_sub_one.mp h) hm
    rw [W.Φ_of_odd hm1, W.Φ_of_odd hm2, W.ΨSq_of_odd hm1, W.ΨSq_of_odd hm2, preΨ_even,
      show m + 1 + 1 = m + 2 by ring, add_sub_cancel_right,
      show m - 1 + 1 = m by ring, show m - 1 - 1 = m - 2 by ring]
    ring
  · have hm1 : Even (m + 1) := Int.even_add_one.mpr hm
    have hm2 : Even (m - 1) := Int.even_sub_one.mpr hm
    rw [W.Φ_of_even hm1, W.Φ_of_even hm2, W.ΨSq_of_even hm1, W.ΨSq_of_even hm2, preΨ_even,
      show m + 1 + 1 = m + 2 by ring, add_sub_cancel_right,
      show m - 1 + 1 = m by ring, show m - 1 - 1 = m - 2 by ring]
    ring

end ConsecutiveIdentities

section SmallIndex

lemma preΨ'_five_eq : W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
  rw [show (5 : ℕ) = 2 * (0 + 2) + 1 by rfl, preΨ'_odd]
  simp

lemma preΨ'_six_eq :
    W.preΨ' 6 = W.Ψ₃ * (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 - W.preΨ₄ ^ 2) := by
  rw [show (6 : ℕ) = 2 * (0 + 3) by rfl, preΨ'_even]
  simp only [Nat.reduceAdd, preΨ'_one, preΨ'_two, preΨ'_three, preΨ'_four, W.preΨ'_five_eq,
    one_pow, one_mul]
  ring

lemma ΨSq_five_eq : W.ΨSq 5 = (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) ^ 2 := by
  rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by rfl, ΨSq_ofNat, W.preΨ'_five_eq,
    if_neg (by decide : ¬Even (5 : ℕ)), mul_one]

lemma Φ_five_eq :
    W.Φ 5 = X * (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) ^ 2 -
      W.Ψ₃ * (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 - W.preΨ₄ ^ 2) * W.preΨ₄ * W.Ψ₂Sq := by
  rw [show (5 : ℤ) = ((4 : ℕ) + 1 : ℤ) by rfl, Φ_ofNat, show (4 : ℕ) + 1 = 5 by rfl,
    show (4 : ℕ) + 2 = 6 by rfl, if_pos (by decide : Even (4 : ℕ)),
    if_pos (by decide : Even (4 : ℕ)), preΨ'_four, W.preΨ'_five_eq, W.preΨ'_six_eq]
  ring

end SmallIndex

section StarInstances

variable (t : R)

lemma ellipticNet_one :
    2 * t * (W.Φ 1).eval t * ((W.Φ 1).eval t + t * (W.ΨSq 1).eval t) +
        W.b₂ * t * ((W.Φ 1).eval t * (W.ΨSq 1).eval t) +
        W.b₄ * (((W.Φ 1).eval t + t * (W.ΨSq 1).eval t) * (W.ΨSq 1).eval t) +
        W.b₆ * (W.ΨSq 1).eval t ^ 2 =
      (W.Φ 2).eval t * (W.ΨSq 0).eval t + (W.Φ 0).eval t * (W.ΨSq 2).eval t := by
  rw [Φ_zero, Φ_one, ΨSq_zero, ΨSq_one, ΨSq_two, Ψ₂Sq]
  eval_simp
  ring

set_option maxHeartbeats 1600000 in

lemma ellipticNet_three :
    2 * t * (W.Φ 3).eval t * ((W.Φ 3).eval t + t * (W.ΨSq 3).eval t) +
        W.b₂ * t * ((W.Φ 3).eval t * (W.ΨSq 3).eval t) +
        W.b₄ * (((W.Φ 3).eval t + t * (W.ΨSq 3).eval t) * (W.ΨSq 3).eval t) +
        W.b₆ * (W.ΨSq 3).eval t ^ 2 =
      (W.Φ 4).eval t * (W.ΨSq 2).eval t + (W.Φ 2).eval t * (W.ΨSq 4).eval t := by
  rw [Φ_two, Φ_three, Φ_four, ΨSq_two, ΨSq_three, ΨSq_four, Ψ₂Sq, Ψ₃, preΨ₄]
  eval_simp
  linear_combination ((24) * t ^ 15 + (26) * t ^ 14 * W.b₂ + (9) * t ^ 13 * W.b₂ ^ 2 + (96) * t ^ 13 * W.b₄
        + t ^ 12 * W.b₂ ^ 3 + (63) * t ^ 12 * W.b₂ * W.b₄ + (150) * t ^ 12 * W.b₆
        + (10) * t ^ 11 * W.b₂ ^ 2 * W.b₄ + (93) * t ^ 11 * W.b₂ * W.b₆ + (102) * t ^ 11 * W.b₄ ^ 2
        + (128) * t ^ 11 * W.b₈ + (14) * t ^ 10 * W.b₂ ^ 2 * W.b₆ + (31) * t ^ 10 * W.b₂ * W.b₄ ^ 2
        + (88) * t ^ 10 * W.b₂ * W.b₈ + (261) * t ^ 10 * W.b₄ * W.b₆ + (18) * t ^ 9 * W.b₂ ^ 2 * W.b₈
        + (72) * t ^ 9 * W.b₂ * W.b₄ * W.b₆ + (30) * t ^ 9 * W.b₄ ^ 3 + (216) * t ^ 9 * W.b₄ * W.b₈
        + (144) * t ^ 9 * W.b₆ ^ 2 + t ^ 8 * W.b₂ ^ 3 * W.b₈ - t ^ 8 * W.b₂ ^ 2 * W.b₄ * W.b₆
        + (82) * t ^ 8 * W.b₂ * W.b₄ * W.b₈ + (36) * t ^ 8 * W.b₂ * W.b₆ ^ 2
        + (87) * t ^ 8 * W.b₄ ^ 2 * W.b₆ + (192) * t ^ 8 * W.b₆ * W.b₈
        + (6) * t ^ 7 * W.b₂ ^ 2 * W.b₄ * W.b₈ - t ^ 7 * W.b₂ ^ 2 * W.b₆ ^ 2
        + (-5) * t ^ 7 * W.b₂ * W.b₄ ^ 2 * W.b₆ + (66) * t ^ 7 * W.b₂ * W.b₆ * W.b₈
        + (88) * t ^ 7 * W.b₄ ^ 2 * W.b₈ + (72) * t ^ 7 * W.b₄ * W.b₆ ^ 2 + (40) * t ^ 7 * W.b₈ ^ 2
        + (4) * t ^ 6 * W.b₂ ^ 2 * W.b₆ * W.b₈ + (11) * t ^ 6 * W.b₂ * W.b₄ ^ 2 * W.b₈
        + (-9) * t ^ 6 * W.b₂ * W.b₄ * W.b₆ ^ 2 + (14) * t ^ 6 * W.b₂ * W.b₈ ^ 2
        + (-6) * t ^ 6 * W.b₄ ^ 3 * W.b₆ + (126) * t ^ 6 * W.b₄ * W.b₆ * W.b₈ + (15) * t ^ 6 * W.b₆ ^ 3
        + t ^ 5 * W.b₂ ^ 2 * W.b₈ ^ 2 + (12) * t ^ 5 * W.b₂ * W.b₄ * W.b₆ * W.b₈
        + (-4) * t ^ 5 * W.b₂ * W.b₆ ^ 3 + (6) * t ^ 5 * W.b₄ ^ 3 * W.b₈
        + (-15) * t ^ 5 * W.b₄ ^ 2 * W.b₆ ^ 2 + (24) * t ^ 5 * W.b₄ * W.b₈ ^ 2
        + (36) * t ^ 5 * W.b₆ ^ 2 * W.b₈ + (3) * t ^ 4 * W.b₂ * W.b₄ * W.b₈ ^ 2
        + (2) * t ^ 4 * W.b₂ * W.b₆ ^ 2 * W.b₈ + (7) * t ^ 4 * W.b₄ ^ 2 * W.b₆ * W.b₈
        + (-12) * t ^ 4 * W.b₄ * W.b₆ ^ 3 + (10) * t ^ 4 * W.b₆ * W.b₈ ^ 2
        + t ^ 3 * W.b₂ * W.b₆ * W.b₈ ^ 2 + (2) * t ^ 3 * W.b₄ ^ 2 * W.b₈ ^ 2 + (-3) * t ^ 3 * W.b₆ ^ 4
        + t ^ 2 * W.b₄ * W.b₆ * W.b₈ ^ 2 - t ^ 2 * W.b₆ ^ 3 * W.b₈) * W.b_relation

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in

lemma ellipticNet_four :
    2 * t * (W.Φ 4).eval t * ((W.Φ 4).eval t + t * (W.ΨSq 4).eval t) +
        W.b₂ * t * ((W.Φ 4).eval t * (W.ΨSq 4).eval t) +
        W.b₄ * (((W.Φ 4).eval t + t * (W.ΨSq 4).eval t) * (W.ΨSq 4).eval t) +
        W.b₆ * (W.ΨSq 4).eval t ^ 2 =
      (W.Φ 5).eval t * (W.ΨSq 3).eval t + (W.Φ 3).eval t * (W.ΨSq 5).eval t := by
  rw [Φ_three, Φ_four, W.Φ_five_eq, ΨSq_three, ΨSq_four, W.ΨSq_five_eq, Ψ₂Sq, Ψ₃, preΨ₄]
  eval_simp
  linear_combination ((80) * t ^ 29 + (180) * t ^ 28 * W.b₂ + (156) * t ^ 27 * W.b₂ ^ 2 + (936) * t ^ 27 * W.b₄
        + (65) * t ^ 26 * W.b₂ ^ 3 + (1560) * t ^ 26 * W.b₂ * W.b₄ + (2340) * t ^ 26 * W.b₆
        + (13) * t ^ 25 * W.b₂ ^ 4 + (936) * t ^ 25 * W.b₂ ^ 2 * W.b₄ + (3948) * t ^ 25 * W.b₂ * W.b₆
        + (3540) * t ^ 25 * W.b₄ ^ 2 + (2928) * t ^ 25 * W.b₈ + t ^ 24 * W.b₂ ^ 5
        + (239) * t ^ 24 * W.b₂ ^ 3 * W.b₄ + (2457) * t ^ 24 * W.b₂ ^ 2 * W.b₆
        + (4005) * t ^ 24 * W.b₂ * W.b₄ ^ 2 + (5388) * t ^ 24 * W.b₂ * W.b₈
        + (16344) * t ^ 24 * W.b₄ * W.b₆ + (22) * t ^ 23 * W.b₂ ^ 4 * W.b₄
        + (688) * t ^ 23 * W.b₂ ^ 3 * W.b₆ + (1413) * t ^ 23 * W.b₂ ^ 2 * W.b₄ ^ 2
        + (3864) * t ^ 23 * W.b₂ ^ 2 * W.b₈ + (18870) * t ^ 23 * W.b₂ * W.b₄ * W.b₆
        + (5094) * t ^ 23 * W.b₄ ^ 3 + (21096) * t ^ 23 * W.b₄ * W.b₈ + (17460) * t ^ 23 * W.b₆ ^ 2
        + (83) * t ^ 22 * W.b₂ ^ 4 * W.b₆ + (148) * t ^ 22 * W.b₂ ^ 3 * W.b₄ ^ 2
        + (1379) * t ^ 22 * W.b₂ ^ 3 * W.b₈ + (7107) * t ^ 22 * W.b₂ ^ 2 * W.b₄ * W.b₆
        + (3117) * t ^ 22 * W.b₂ * W.b₄ ^ 3 + (28380) * t ^ 22 * W.b₂ * W.b₄ * W.b₈
        + (20148) * t ^ 22 * W.b₂ * W.b₆ ^ 2 + (32385) * t ^ 22 * W.b₄ ^ 2 * W.b₆
        + (41628) * t ^ 22 * W.b₆ * W.b₈ + (3) * t ^ 21 * W.b₂ ^ 5 * W.b₆
        + (-3) * t ^ 21 * W.b₂ ^ 4 * W.b₄ ^ 2 + (260) * t ^ 21 * W.b₂ ^ 4 * W.b₈
        + (944) * t ^ 21 * W.b₂ ^ 3 * W.b₄ * W.b₆ + (324) * t ^ 21 * W.b₂ ^ 2 * W.b₄ ^ 3
        + (14124) * t ^ 21 * W.b₂ ^ 2 * W.b₄ * W.b₈ + (7737) * t ^ 21 * W.b₂ ^ 2 * W.b₆ ^ 2
        + (20436) * t ^ 21 * W.b₂ * W.b₄ ^ 2 * W.b₆ + (54684) * t ^ 21 * W.b₂ * W.b₆ * W.b₈
        + (1914) * t ^ 21 * W.b₄ ^ 4 + (47556) * t ^ 21 * W.b₄ ^ 2 * W.b₈
        + (62604) * t ^ 21 * W.b₄ * W.b₆ ^ 2 + (23136) * t ^ 21 * W.b₈ ^ 2
        + (25) * t ^ 20 * W.b₂ ^ 5 * W.b₈ + (18) * t ^ 20 * W.b₂ ^ 4 * W.b₄ * W.b₆
        + (-43) * t ^ 20 * W.b₂ ^ 3 * W.b₄ ^ 3 + (3296) * t ^ 20 * W.b₂ ^ 3 * W.b₄ * W.b₈
        + (1121) * t ^ 20 * W.b₂ ^ 3 * W.b₆ ^ 2 + (2682) * t ^ 20 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆
        + (26523) * t ^ 20 * W.b₂ ^ 2 * W.b₆ * W.b₈ + (-81) * t ^ 20 * W.b₂ * W.b₄ ^ 4
        + (42999) * t ^ 20 * W.b₂ * W.b₄ ^ 2 * W.b₈ + (38610) * t ^ 20 * W.b₂ * W.b₄ * W.b₆ ^ 2
        + (33240) * t ^ 20 * W.b₂ * W.b₈ ^ 2 + (13257) * t ^ 20 * W.b₄ ^ 3 * W.b₆
        + (167052) * t ^ 20 * W.b₄ * W.b₆ * W.b₈ + (37500) * t ^ 20 * W.b₆ ^ 3
        + t ^ 19 * W.b₂ ^ 6 * W.b₈ - t ^ 19 * W.b₂ ^ 5 * W.b₄ * W.b₆
        + (370) * t ^ 19 * W.b₂ ^ 4 * W.b₄ * W.b₈ + (39) * t ^ 19 * W.b₂ ^ 4 * W.b₆ ^ 2
        + (-195) * t ^ 19 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ + (6036) * t ^ 19 * W.b₂ ^ 3 * W.b₆ * W.b₈
        + (-219) * t ^ 19 * W.b₂ ^ 2 * W.b₄ ^ 4 + (13764) * t ^ 19 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₈
        + (5166) * t ^ 19 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 2 + (18552) * t ^ 19 * W.b₂ ^ 2 * W.b₈ ^ 2
        + (-936) * t ^ 19 * W.b₂ * W.b₄ ^ 3 * W.b₆ + (142614) * t ^ 19 * W.b₂ * W.b₄ * W.b₆ * W.b₈
        + (21654) * t ^ 19 * W.b₂ * W.b₆ ^ 3 + (-630) * t ^ 19 * W.b₄ ^ 5
        + (36486) * t ^ 19 * W.b₄ ^ 3 * W.b₈ + (25605) * t ^ 19 * W.b₄ ^ 2 * W.b₆ ^ 2
        + (98352) * t ^ 19 * W.b₄ * W.b₈ ^ 2 + (138384) * t ^ 19 * W.b₆ ^ 2 * W.b₈
        + (17) * t ^ 18 * W.b₂ ^ 5 * W.b₄ * W.b₈ - t ^ 18 * W.b₂ ^ 5 * W.b₆ ^ 2
        + (-16) * t ^ 18 * W.b₂ ^ 4 * W.b₄ ^ 2 * W.b₆ + (659) * t ^ 18 * W.b₂ ^ 4 * W.b₆ * W.b₈
        + (1912) * t ^ 18 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₈ + (-354) * t ^ 18 * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 2
        + (5234) * t ^ 18 * W.b₂ ^ 3 * W.b₈ ^ 2 + (-1833) * t ^ 18 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆
        + (42840) * t ^ 18 * W.b₂ ^ 2 * W.b₄ * W.b₆ * W.b₈ + (2637) * t ^ 18 * W.b₂ ^ 2 * W.b₆ ^ 3
        + (-465) * t ^ 18 * W.b₂ * W.b₄ ^ 5 + (21180) * t ^ 18 * W.b₂ * W.b₄ ^ 3 * W.b₈
        + (-7260) * t ^ 18 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 2 + (99504) * t ^ 18 * W.b₂ * W.b₄ * W.b₈ ^ 2
        + (109056) * t ^ 18 * W.b₂ * W.b₆ ^ 2 * W.b₈ + (-6801) * t ^ 18 * W.b₄ ^ 4 * W.b₆
        + (144555) * t ^ 18 * W.b₄ ^ 2 * W.b₆ * W.b₈ + (9486) * t ^ 18 * W.b₄ * W.b₆ ^ 3
        + (152760) * t ^ 18 * W.b₆ * W.b₈ ^ 2 + (29) * t ^ 17 * W.b₂ ^ 5 * W.b₆ * W.b₈
        + (107) * t ^ 17 * W.b₂ ^ 4 * W.b₄ ^ 2 * W.b₈ + (-45) * t ^ 17 * W.b₂ ^ 4 * W.b₄ * W.b₆ ^ 2
        + (798) * t ^ 17 * W.b₂ ^ 4 * W.b₈ ^ 2 + (-91) * t ^ 17 * W.b₂ ^ 3 * W.b₄ ^ 3 * W.b₆
        + (5412) * t ^ 17 * W.b₂ ^ 3 * W.b₄ * W.b₆ * W.b₈ + (-233) * t ^ 17 * W.b₂ ^ 3 * W.b₆ ^ 3
        + (4092) * t ^ 17 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₈
        + (-5643) * t ^ 17 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 2
        + (38928) * t ^ 17 * W.b₂ ^ 2 * W.b₄ * W.b₈ ^ 2 + (30204) * t ^ 17 * W.b₂ ^ 2 * W.b₆ ^ 2 * W.b₈
        + (-4692) * t ^ 17 * W.b₂ * W.b₄ ^ 4 * W.b₆ + (73728) * t ^ 17 * W.b₂ * W.b₄ ^ 2 * W.b₆ * W.b₈
        + (-17256) * t ^ 17 * W.b₂ * W.b₄ * W.b₆ ^ 3 + (142200) * t ^ 17 * W.b₂ * W.b₆ * W.b₈ ^ 2
        + (-350) * t ^ 17 * W.b₄ ^ 6 + (9396) * t ^ 17 * W.b₄ ^ 4 * W.b₈
        + (-28836) * t ^ 17 * W.b₄ ^ 3 * W.b₆ ^ 2 + (107784) * t ^ 17 * W.b₄ ^ 2 * W.b₈ ^ 2
        + (143712) * t ^ 17 * W.b₄ * W.b₆ ^ 2 * W.b₈ + (-9036) * t ^ 17 * W.b₆ ^ 4
        + (51744) * t ^ 17 * W.b₈ ^ 3 + (63) * t ^ 16 * W.b₂ ^ 5 * W.b₈ ^ 2
        + (241) * t ^ 16 * W.b₂ ^ 4 * W.b₄ * W.b₆ * W.b₈ + (-29) * t ^ 16 * W.b₂ ^ 4 * W.b₆ ^ 3
        + (313) * t ^ 16 * W.b₂ ^ 3 * W.b₄ ^ 3 * W.b₈
        + (-366) * t ^ 16 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ ^ 2
        + (7454) * t ^ 16 * W.b₂ ^ 3 * W.b₄ * W.b₈ ^ 2 + (3453) * t ^ 16 * W.b₂ ^ 3 * W.b₆ ^ 2 * W.b₈
        + (-222) * t ^ 16 * W.b₂ ^ 2 * W.b₄ ^ 4 * W.b₆
        + (11070) * t ^ 16 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ * W.b₈
        + (-7350) * t ^ 16 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 3 + (51642) * t ^ 16 * W.b₂ ^ 2 * W.b₆ * W.b₈ ^ 2
        + (3291) * t ^ 16 * W.b₂ * W.b₄ ^ 4 * W.b₈ + (-17049) * t ^ 16 * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 2
        + (80082) * t ^ 16 * W.b₂ * W.b₄ ^ 2 * W.b₈ ^ 2
        + (55956) * t ^ 16 * W.b₂ * W.b₄ * W.b₆ ^ 2 * W.b₈ + (-12561) * t ^ 16 * W.b₂ * W.b₆ ^ 4
        + (53416) * t ^ 16 * W.b₂ * W.b₈ ^ 3 + (-3789) * t ^ 16 * W.b₄ ^ 5 * W.b₆
        + (22476) * t ^ 16 * W.b₄ ^ 3 * W.b₆ * W.b₈ + (-55650) * t ^ 16 * W.b₄ ^ 2 * W.b₆ ^ 3
        + (216624) * t ^ 16 * W.b₄ * W.b₆ * W.b₈ ^ 2 + (5064) * t ^ 16 * W.b₆ ^ 3 * W.b₈
        + (2) * t ^ 15 * W.b₂ ^ 6 * W.b₈ ^ 2 + (-4) * t ^ 15 * W.b₂ ^ 5 * W.b₄ * W.b₆ * W.b₈
        + (2) * t ^ 15 * W.b₂ ^ 4 * W.b₄ ^ 2 * W.b₆ ^ 2 + (706) * t ^ 15 * W.b₂ ^ 4 * W.b₄ * W.b₈ ^ 2
        + (125) * t ^ 15 * W.b₂ ^ 4 * W.b₆ ^ 2 * W.b₈
        + (379) * t ^ 15 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ * W.b₈
        + (-463) * t ^ 15 * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 3 + (9260) * t ^ 15 * W.b₂ ^ 3 * W.b₆ * W.b₈ ^ 2
        + (444) * t ^ 15 * W.b₂ ^ 2 * W.b₄ ^ 4 * W.b₈
        + (-969) * t ^ 15 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ ^ 2
        + (22278) * t ^ 15 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₈ ^ 2
        + (3222) * t ^ 15 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 2 * W.b₈ + (-3486) * t ^ 15 * W.b₂ ^ 2 * W.b₆ ^ 4
        + (22528) * t ^ 15 * W.b₂ ^ 2 * W.b₈ ^ 3 + (-222) * t ^ 15 * W.b₂ * W.b₄ ^ 5 * W.b₆
        + (936) * t ^ 15 * W.b₂ * W.b₄ ^ 3 * W.b₆ * W.b₈
        + (-27453) * t ^ 15 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 3
        + (147804) * t ^ 15 * W.b₂ * W.b₄ * W.b₆ * W.b₈ ^ 2
        + (-12924) * t ^ 15 * W.b₂ * W.b₆ ^ 3 * W.b₈ + (414) * t ^ 15 * W.b₄ ^ 5 * W.b₈
        + (-14781) * t ^ 15 * W.b₄ ^ 4 * W.b₆ ^ 2 + (46764) * t ^ 15 * W.b₄ ^ 3 * W.b₈ ^ 2
        + (-27132) * t ^ 15 * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈ + (-46854) * t ^ 15 * W.b₄ * W.b₆ ^ 4
        + (80048) * t ^ 15 * W.b₄ * W.b₈ ^ 3 + (33288) * t ^ 15 * W.b₆ ^ 2 * W.b₈ ^ 2
        + (26) * t ^ 14 * W.b₂ ^ 5 * W.b₄ * W.b₈ ^ 2 + (-4) * t ^ 14 * W.b₂ ^ 5 * W.b₆ ^ 2 * W.b₈
        + (-48) * t ^ 14 * W.b₂ ^ 4 * W.b₄ ^ 2 * W.b₆ * W.b₈
        + (4) * t ^ 14 * W.b₂ ^ 4 * W.b₄ * W.b₆ ^ 3 + (829) * t ^ 14 * W.b₂ ^ 4 * W.b₆ * W.b₈ ^ 2
        + (22) * t ^ 14 * W.b₂ ^ 3 * W.b₄ ^ 3 * W.b₆ ^ 2
        + (2788) * t ^ 14 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₈ ^ 2
        + (-717) * t ^ 14 * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 2 * W.b₈ + (-188) * t ^ 14 * W.b₂ ^ 3 * W.b₆ ^ 4
        + (4990) * t ^ 14 * W.b₂ ^ 3 * W.b₈ ^ 3 + (-855) * t ^ 14 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ * W.b₈
        + (-1314) * t ^ 14 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 3
        + (37878) * t ^ 14 * W.b₂ ^ 2 * W.b₄ * W.b₆ * W.b₈ ^ 2
        + (-6495) * t ^ 14 * W.b₂ ^ 2 * W.b₆ ^ 3 * W.b₈ + (282) * t ^ 14 * W.b₂ * W.b₄ ^ 5 * W.b₈
        + (-765) * t ^ 14 * W.b₂ * W.b₄ ^ 4 * W.b₆ ^ 2 + (25854) * t ^ 14 * W.b₂ * W.b₄ ^ 3 * W.b₈ ^ 2
        + (-30768) * t ^ 14 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈
        + (-19005) * t ^ 14 * W.b₂ * W.b₄ * W.b₆ ^ 4 + (66664) * t ^ 14 * W.b₂ * W.b₄ * W.b₈ ^ 3
        + (16488) * t ^ 14 * W.b₂ * W.b₆ ^ 2 * W.b₈ ^ 2 + (-60) * t ^ 14 * W.b₄ ^ 6 * W.b₆
        + (-9309) * t ^ 14 * W.b₄ ^ 4 * W.b₆ * W.b₈ + (-26235) * t ^ 14 * W.b₄ ^ 3 * W.b₆ ^ 3
        + (82122) * t ^ 14 * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 2 + (-85284) * t ^ 14 * W.b₄ * W.b₆ ^ 3 * W.b₈
        + (-12519) * t ^ 14 * W.b₆ ^ 5 + (14536) * t ^ 14 * W.b₆ * W.b₈ ^ 3
        + (29) * t ^ 13 * W.b₂ ^ 5 * W.b₆ * W.b₈ ^ 2 + (127) * t ^ 13 * W.b₂ ^ 4 * W.b₄ ^ 2 * W.b₈ ^ 2
        + (-106) * t ^ 13 * W.b₂ ^ 4 * W.b₄ * W.b₆ ^ 2 * W.b₈ + (2) * t ^ 13 * W.b₂ ^ 4 * W.b₆ ^ 4
        + (612) * t ^ 13 * W.b₂ ^ 4 * W.b₈ ^ 3 + (-206) * t ^ 13 * W.b₂ ^ 3 * W.b₄ ^ 3 * W.b₆ * W.b₈
        + (73) * t ^ 13 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ ^ 3
        + (4312) * t ^ 13 * W.b₂ ^ 3 * W.b₄ * W.b₆ * W.b₈ ^ 2
        + (-925) * t ^ 13 * W.b₂ ^ 3 * W.b₆ ^ 3 * W.b₈ + (81) * t ^ 13 * W.b₂ ^ 2 * W.b₄ ^ 4 * W.b₆ ^ 2
        + (5004) * t ^ 13 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₈ ^ 2
        + (-6111) * t ^ 13 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈
        + (-471) * t ^ 13 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 4 + (22200) * t ^ 13 * W.b₂ ^ 2 * W.b₄ * W.b₈ ^ 3
        + (3174) * t ^ 13 * W.b₂ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 2
        + (-2484) * t ^ 13 * W.b₂ * W.b₄ ^ 4 * W.b₆ * W.b₈
        + (-105) * t ^ 13 * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 3
        + (40872) * t ^ 13 * W.b₂ * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 2
        + (-47340) * t ^ 13 * W.b₂ * W.b₄ * W.b₆ ^ 3 * W.b₈ + (-4074) * t ^ 13 * W.b₂ * W.b₆ ^ 5
        + (12536) * t ^ 13 * W.b₂ * W.b₆ * W.b₈ ^ 3 + (60) * t ^ 13 * W.b₄ ^ 6 * W.b₈
        + (108) * t ^ 13 * W.b₄ ^ 5 * W.b₆ ^ 2 + (9576) * t ^ 13 * W.b₄ ^ 4 * W.b₈ ^ 2
        + (-44412) * t ^ 13 * W.b₄ ^ 3 * W.b₆ ^ 2 * W.b₈ + (-21432) * t ^ 13 * W.b₄ ^ 2 * W.b₆ ^ 4
        + (44776) * t ^ 13 * W.b₄ ^ 2 * W.b₈ ^ 3 + (-24936) * t ^ 13 * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 2
        + (-33780) * t ^ 13 * W.b₆ ^ 4 * W.b₈ + (-3760) * t ^ 13 * W.b₈ ^ 4
        + (39) * t ^ 12 * W.b₂ ^ 5 * W.b₈ ^ 3 + (148) * t ^ 12 * W.b₂ ^ 4 * W.b₄ * W.b₆ * W.b₈ ^ 2
        + (-58) * t ^ 12 * W.b₂ ^ 4 * W.b₆ ^ 3 * W.b₈ + (307) * t ^ 12 * W.b₂ ^ 3 * W.b₄ ^ 3 * W.b₈ ^ 2
        + (-561) * t ^ 12 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈
        + (80) * t ^ 12 * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 4 + (3672) * t ^ 12 * W.b₂ ^ 3 * W.b₄ * W.b₈ ^ 3
        + (243) * t ^ 12 * W.b₂ ^ 3 * W.b₆ ^ 2 * W.b₈ ^ 2
        + (-408) * t ^ 12 * W.b₂ ^ 2 * W.b₄ ^ 4 * W.b₆ * W.b₈
        + (330) * t ^ 12 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ ^ 3
        + (7038) * t ^ 12 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 2
        + (-6657) * t ^ 12 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 3 * W.b₈ + (96) * t ^ 12 * W.b₂ ^ 2 * W.b₆ ^ 5
        + (4998) * t ^ 12 * W.b₂ ^ 2 * W.b₆ * W.b₈ ^ 3 + (123) * t ^ 12 * W.b₂ * W.b₄ ^ 5 * W.b₆ ^ 2
        + (4137) * t ^ 12 * W.b₂ * W.b₄ ^ 4 * W.b₈ ^ 2
        + (-10965) * t ^ 12 * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 2 * W.b₈
        + (2049) * t ^ 12 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 4 + (30798) * t ^ 12 * W.b₂ * W.b₄ ^ 2 * W.b₈ ^ 3
        + (-13416) * t ^ 12 * W.b₂ * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 2
        + (-14865) * t ^ 12 * W.b₂ * W.b₆ ^ 4 * W.b₈ + (-2956) * t ^ 12 * W.b₂ * W.b₈ ^ 4
        + (-1446) * t ^ 12 * W.b₄ ^ 5 * W.b₆ * W.b₈ + (1833) * t ^ 12 * W.b₄ ^ 4 * W.b₆ ^ 3
        + (5862) * t ^ 12 * W.b₄ ^ 3 * W.b₆ * W.b₈ ^ 2 + (-62310) * t ^ 12 * W.b₄ ^ 2 * W.b₆ ^ 3 * W.b₈
        + (-6903) * t ^ 12 * W.b₄ * W.b₆ ^ 5 + (2696) * t ^ 12 * W.b₄ * W.b₆ * W.b₈ ^ 3
        + (-29280) * t ^ 12 * W.b₆ ^ 3 * W.b₈ ^ 2 + t ^ 11 * W.b₂ ^ 6 * W.b₈ ^ 3
        + (-3) * t ^ 11 * W.b₂ ^ 5 * W.b₄ * W.b₆ * W.b₈ ^ 2
        + (3) * t ^ 11 * W.b₂ ^ 4 * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈
        + (294) * t ^ 11 * W.b₂ ^ 4 * W.b₄ * W.b₈ ^ 3 + (-27) * t ^ 11 * W.b₂ ^ 4 * W.b₆ ^ 2 * W.b₈ ^ 2
        - t ^ 11 * W.b₂ ^ 3 * W.b₄ ^ 3 * W.b₆ ^ 3
        + (167) * t ^ 11 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 2
        + (-418) * t ^ 11 * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 3 * W.b₈ + (29) * t ^ 11 * W.b₂ ^ 3 * W.b₆ ^ 5
        + (1020) * t ^ 11 * W.b₂ ^ 3 * W.b₆ * W.b₈ ^ 3
        + (393) * t ^ 11 * W.b₂ ^ 2 * W.b₄ ^ 4 * W.b₈ ^ 2
        + (-1152) * t ^ 11 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ ^ 2 * W.b₈
        + (468) * t ^ 11 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 4
        + (7956) * t ^ 11 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₈ ^ 3
        + (-2070) * t ^ 11 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 2
        + (-1512) * t ^ 11 * W.b₂ ^ 2 * W.b₆ ^ 4 * W.b₈ + (-788) * t ^ 11 * W.b₂ ^ 2 * W.b₈ ^ 4
        + (-378) * t ^ 11 * W.b₂ * W.b₄ ^ 5 * W.b₆ * W.b₈ + (558) * t ^ 11 * W.b₂ * W.b₄ ^ 4 * W.b₆ ^ 3
        + (3384) * t ^ 11 * W.b₂ * W.b₄ ^ 3 * W.b₆ * W.b₈ ^ 2
        + (-11775) * t ^ 11 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 3 * W.b₈
        + (2268) * t ^ 11 * W.b₂ * W.b₄ * W.b₆ ^ 5 + (8172) * t ^ 11 * W.b₂ * W.b₄ * W.b₆ * W.b₈ ^ 3
        + (-12984) * t ^ 11 * W.b₂ * W.b₆ ^ 3 * W.b₈ ^ 2 + (66) * t ^ 11 * W.b₄ ^ 6 * W.b₆ ^ 2
        + (1278) * t ^ 11 * W.b₄ ^ 5 * W.b₈ ^ 2 + (-5220) * t ^ 11 * W.b₄ ^ 4 * W.b₆ ^ 2 * W.b₈
        + (4671) * t ^ 11 * W.b₄ ^ 3 * W.b₆ ^ 4 + (12892) * t ^ 11 * W.b₄ ^ 3 * W.b₈ ^ 3
        + (-32682) * t ^ 11 * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 2
        + (-30126) * t ^ 11 * W.b₄ * W.b₆ ^ 4 * W.b₈ + (-6616) * t ^ 11 * W.b₄ * W.b₈ ^ 4
        + (-489) * t ^ 11 * W.b₆ ^ 6 + (-13264) * t ^ 11 * W.b₆ ^ 2 * W.b₈ ^ 3
        + (9) * t ^ 10 * W.b₂ ^ 5 * W.b₄ * W.b₈ ^ 3 + (-3) * t ^ 10 * W.b₂ ^ 5 * W.b₆ ^ 2 * W.b₈ ^ 2
        + (-24) * t ^ 10 * W.b₂ ^ 4 * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 2
        + (6) * t ^ 10 * W.b₂ ^ 4 * W.b₄ * W.b₆ ^ 3 * W.b₈ + (93) * t ^ 10 * W.b₂ ^ 4 * W.b₆ * W.b₈ ^ 3
        + (21) * t ^ 10 * W.b₂ ^ 3 * W.b₄ ^ 3 * W.b₆ ^ 2 * W.b₈
        + (-3) * t ^ 10 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ ^ 4
        + (864) * t ^ 10 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₈ ^ 3
        + (-432) * t ^ 10 * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 2
        + (-63) * t ^ 10 * W.b₂ ^ 3 * W.b₆ ^ 4 * W.b₈ + (-83) * t ^ 10 * W.b₂ ^ 3 * W.b₈ ^ 4
        + (-6) * t ^ 10 * W.b₂ ^ 2 * W.b₄ ^ 4 * W.b₆ ^ 3
        + (-243) * t ^ 10 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ * W.b₈ ^ 2
        + (-861) * t ^ 10 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 3 * W.b₈
        + (270) * t ^ 10 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 5
        + (3824) * t ^ 10 * W.b₂ ^ 2 * W.b₄ * W.b₆ * W.b₈ ^ 3
        + (-1689) * t ^ 10 * W.b₂ ^ 2 * W.b₆ ^ 3 * W.b₈ ^ 2
        + (255) * t ^ 10 * W.b₂ * W.b₄ ^ 5 * W.b₈ ^ 2
        + (-975) * t ^ 10 * W.b₂ * W.b₄ ^ 4 * W.b₆ ^ 2 * W.b₈
        + (909) * t ^ 10 * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 4 + (7356) * t ^ 10 * W.b₂ * W.b₄ ^ 3 * W.b₈ ^ 3
        + (-7668) * t ^ 10 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 2
        + (-3006) * t ^ 10 * W.b₂ * W.b₄ * W.b₆ ^ 4 * W.b₈ + (-3272) * t ^ 10 * W.b₂ * W.b₄ * W.b₈ ^ 4
        + (657) * t ^ 10 * W.b₂ * W.b₆ ^ 6 + (-4272) * t ^ 10 * W.b₂ * W.b₆ ^ 2 * W.b₈ ^ 3
        + (-132) * t ^ 10 * W.b₄ ^ 6 * W.b₆ * W.b₈ + (315) * t ^ 10 * W.b₄ ^ 5 * W.b₆ ^ 3
        + (-183) * t ^ 10 * W.b₄ ^ 4 * W.b₆ * W.b₈ ^ 2 + (-4077) * t ^ 10 * W.b₄ ^ 3 * W.b₆ ^ 3 * W.b₈
        + (4869) * t ^ 10 * W.b₄ ^ 2 * W.b₆ ^ 5 + (-426) * t ^ 10 * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 3
        + (-28800) * t ^ 10 * W.b₄ * W.b₆ ^ 3 * W.b₈ ^ 2 + (-4095) * t ^ 10 * W.b₆ ^ 5 * W.b₈
        + (-5340) * t ^ 10 * W.b₆ * W.b₈ ^ 4 + (3) * t ^ 9 * W.b₂ ^ 5 * W.b₆ * W.b₈ ^ 3
        + (33) * t ^ 9 * W.b₂ ^ 4 * W.b₄ ^ 2 * W.b₈ ^ 3
        + (-33) * t ^ 9 * W.b₂ ^ 4 * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 2
        + (3) * t ^ 9 * W.b₂ ^ 4 * W.b₆ ^ 4 * W.b₈ + (-3) * t ^ 9 * W.b₂ ^ 4 * W.b₈ ^ 4
        + (-75) * t ^ 9 * W.b₂ ^ 3 * W.b₄ ^ 3 * W.b₆ * W.b₈ ^ 2
        + (51) * t ^ 9 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ ^ 3 * W.b₈
        + (-3) * t ^ 9 * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 5 + (516) * t ^ 9 * W.b₂ ^ 3 * W.b₄ * W.b₆ * W.b₈ ^ 3
        + (-171) * t ^ 9 * W.b₂ ^ 3 * W.b₆ ^ 3 * W.b₈ ^ 2
        + (54) * t ^ 9 * W.b₂ ^ 2 * W.b₄ ^ 4 * W.b₆ ^ 2 * W.b₈
        + (-21) * t ^ 9 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ ^ 4
        + (1236) * t ^ 9 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₈ ^ 3
        + (-1569) * t ^ 9 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 2
        + (-54) * t ^ 9 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 4 * W.b₈
        + (-472) * t ^ 9 * W.b₂ ^ 2 * W.b₄ * W.b₈ ^ 4 + (51) * t ^ 9 * W.b₂ ^ 2 * W.b₆ ^ 6
        + (44) * t ^ 9 * W.b₂ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 3 + (-12) * t ^ 9 * W.b₂ * W.b₄ ^ 5 * W.b₆ ^ 3
        + (-576) * t ^ 9 * W.b₂ * W.b₄ ^ 4 * W.b₆ * W.b₈ ^ 2
        + (-426) * t ^ 9 * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 3 * W.b₈
        + (651) * t ^ 9 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 5
        + (4544) * t ^ 9 * W.b₂ * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 3
        + (-5760) * t ^ 9 * W.b₂ * W.b₄ * W.b₆ ^ 3 * W.b₈ ^ 2 + (300) * t ^ 9 * W.b₂ * W.b₆ ^ 5 * W.b₈
        + (-2404) * t ^ 9 * W.b₂ * W.b₆ * W.b₈ ^ 4 + (66) * t ^ 9 * W.b₄ ^ 6 * W.b₈ ^ 2
        + (-264) * t ^ 9 * W.b₄ ^ 5 * W.b₆ ^ 2 * W.b₈ + (543) * t ^ 9 * W.b₄ ^ 4 * W.b₆ ^ 4
        + (2460) * t ^ 9 * W.b₄ ^ 4 * W.b₈ ^ 3 + (-5100) * t ^ 9 * W.b₄ ^ 3 * W.b₆ ^ 2 * W.b₈ ^ 2
        + (1752) * t ^ 9 * W.b₄ ^ 2 * W.b₆ ^ 4 * W.b₈ + (-3164) * t ^ 9 * W.b₄ ^ 2 * W.b₈ ^ 4
        + (2232) * t ^ 9 * W.b₄ * W.b₆ ^ 6 + (-9792) * t ^ 9 * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 3
        + (-5460) * t ^ 9 * W.b₆ ^ 4 * W.b₈ ^ 2 + (-400) * t ^ 9 * W.b₈ ^ 5
        + (21) * t ^ 8 * W.b₂ ^ 4 * W.b₄ * W.b₆ * W.b₈ ^ 3
        + (-9) * t ^ 8 * W.b₂ ^ 4 * W.b₆ ^ 3 * W.b₈ ^ 2 + (63) * t ^ 8 * W.b₂ ^ 3 * W.b₄ ^ 3 * W.b₈ ^ 3
        + (-129) * t ^ 8 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 2
        + (39) * t ^ 8 * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 4 * W.b₈ + (-21) * t ^ 8 * W.b₂ ^ 3 * W.b₄ * W.b₈ ^ 4
        - t ^ 8 * W.b₂ ^ 3 * W.b₆ ^ 6 + (63) * t ^ 8 * W.b₂ ^ 3 * W.b₆ ^ 2 * W.b₈ ^ 3
        + (-114) * t ^ 8 * W.b₂ ^ 2 * W.b₄ ^ 4 * W.b₆ * W.b₈ ^ 2
        + (153) * t ^ 8 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ ^ 3 * W.b₈
        + (-27) * t ^ 8 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 5
        + (1050) * t ^ 8 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 3
        + (-924) * t ^ 8 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 3 * W.b₈ ^ 2
        + (63) * t ^ 8 * W.b₂ ^ 2 * W.b₆ ^ 5 * W.b₈ + (-307) * t ^ 8 * W.b₂ ^ 2 * W.b₆ * W.b₈ ^ 4
        + (60) * t ^ 8 * W.b₂ * W.b₄ ^ 5 * W.b₆ ^ 2 * W.b₈ + (-48) * t ^ 8 * W.b₂ * W.b₄ ^ 4 * W.b₆ ^ 4
        + (861) * t ^ 8 * W.b₂ * W.b₄ ^ 4 * W.b₈ ^ 3
        + (-2079) * t ^ 8 * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 2 * W.b₈ ^ 2
        + (522) * t ^ 8 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 4 * W.b₈
        + (-823) * t ^ 8 * W.b₂ * W.b₄ ^ 2 * W.b₈ ^ 4 + (192) * t ^ 8 * W.b₂ * W.b₄ * W.b₆ ^ 6
        + (-36) * t ^ 8 * W.b₂ * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 3
        + (-639) * t ^ 8 * W.b₂ * W.b₆ ^ 4 * W.b₈ ^ 2 + (-180) * t ^ 8 * W.b₂ * W.b₈ ^ 5
        + (-8) * t ^ 8 * W.b₄ ^ 6 * W.b₆ ^ 3 + (-285) * t ^ 8 * W.b₄ ^ 5 * W.b₆ * W.b₈ ^ 2
        + (153) * t ^ 8 * W.b₄ ^ 4 * W.b₆ ^ 3 * W.b₈ + (405) * t ^ 8 * W.b₄ ^ 3 * W.b₆ ^ 5
        + (1868) * t ^ 8 * W.b₄ ^ 3 * W.b₆ * W.b₈ ^ 3
        + (-3150) * t ^ 8 * W.b₄ ^ 2 * W.b₆ ^ 3 * W.b₈ ^ 2 + (2718) * t ^ 8 * W.b₄ * W.b₆ ^ 5 * W.b₈
        + (-4104) * t ^ 8 * W.b₄ * W.b₆ * W.b₈ ^ 4 + (369) * t ^ 8 * W.b₆ ^ 7
        + (-2616) * t ^ 8 * W.b₆ ^ 3 * W.b₈ ^ 3 + (3) * t ^ 7 * W.b₂ ^ 4 * W.b₆ ^ 2 * W.b₈ ^ 3
        + (57) * t ^ 7 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 3
        + (-63) * t ^ 7 * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 3 * W.b₈ ^ 2
        + (9) * t ^ 7 * W.b₂ ^ 3 * W.b₆ ^ 5 * W.b₈ + (-12) * t ^ 7 * W.b₂ ^ 3 * W.b₆ * W.b₈ ^ 4
        + (66) * t ^ 7 * W.b₂ ^ 2 * W.b₄ ^ 4 * W.b₈ ^ 3
        + (-231) * t ^ 7 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ ^ 2 * W.b₈ ^ 2
        + (153) * t ^ 7 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 4 * W.b₈
        + (-51) * t ^ 7 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₈ ^ 4 + (-15) * t ^ 7 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 6
        + (258) * t ^ 7 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 3
        + (-126) * t ^ 7 * W.b₂ ^ 2 * W.b₆ ^ 4 * W.b₈ ^ 2 + (-24) * t ^ 7 * W.b₂ ^ 2 * W.b₈ ^ 5
        + (-84) * t ^ 7 * W.b₂ * W.b₄ ^ 5 * W.b₆ * W.b₈ ^ 2
        + (192) * t ^ 7 * W.b₂ * W.b₄ ^ 4 * W.b₆ ^ 3 * W.b₈
        + (-75) * t ^ 7 * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 5
        + (936) * t ^ 7 * W.b₂ * W.b₄ ^ 3 * W.b₆ * W.b₈ ^ 3
        + (-1503) * t ^ 7 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 3 * W.b₈ ^ 2
        + (426) * t ^ 7 * W.b₂ * W.b₄ * W.b₆ ^ 5 * W.b₈
        + (-914) * t ^ 7 * W.b₂ * W.b₄ * W.b₆ * W.b₈ ^ 4 + (15) * t ^ 7 * W.b₂ * W.b₆ ^ 7
        + (-68) * t ^ 7 * W.b₂ * W.b₆ ^ 3 * W.b₈ ^ 3 + (24) * t ^ 7 * W.b₄ ^ 6 * W.b₆ ^ 2 * W.b₈
        + (-36) * t ^ 7 * W.b₄ ^ 5 * W.b₆ ^ 4 + (234) * t ^ 7 * W.b₄ ^ 5 * W.b₈ ^ 3
        + (-921) * t ^ 7 * W.b₄ ^ 4 * W.b₆ ^ 2 * W.b₈ ^ 2 + (642) * t ^ 7 * W.b₄ ^ 3 * W.b₆ ^ 4 * W.b₈
        + (-434) * t ^ 7 * W.b₄ ^ 3 * W.b₈ ^ 4 + (102) * t ^ 7 * W.b₄ ^ 2 * W.b₆ ^ 6
        + (372) * t ^ 7 * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 3 + (390) * t ^ 7 * W.b₄ * W.b₆ ^ 4 * W.b₈ ^ 2
        + (-280) * t ^ 7 * W.b₄ * W.b₈ ^ 5 + (678) * t ^ 7 * W.b₆ ^ 6 * W.b₈
        + (-1020) * t ^ 7 * W.b₆ ^ 2 * W.b₈ ^ 4 + (15) * t ^ 6 * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 3
        + (-9) * t ^ 6 * W.b₂ ^ 3 * W.b₆ ^ 4 * W.b₈ ^ 2 - t ^ 6 * W.b₂ ^ 3 * W.b₈ ^ 5
        + (75) * t ^ 6 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ * W.b₈ ^ 3
        + (-153) * t ^ 6 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 3 * W.b₈ ^ 2
        + (63) * t ^ 6 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 5 * W.b₈
        + (-49) * t ^ 6 * W.b₂ ^ 2 * W.b₄ * W.b₆ * W.b₈ ^ 4 + (-3) * t ^ 6 * W.b₂ ^ 2 * W.b₆ ^ 7
        + (27) * t ^ 6 * W.b₂ ^ 2 * W.b₆ ^ 3 * W.b₈ ^ 3 + (36) * t ^ 6 * W.b₂ * W.b₄ ^ 5 * W.b₈ ^ 3
        + (-192) * t ^ 6 * W.b₂ * W.b₄ ^ 4 * W.b₆ ^ 2 * W.b₈ ^ 2
        + (231) * t ^ 6 * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 4 * W.b₈
        + (-51) * t ^ 6 * W.b₂ * W.b₄ ^ 3 * W.b₈ ^ 4 + (-57) * t ^ 6 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 6
        + (368) * t ^ 6 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 3
        + (-345) * t ^ 6 * W.b₂ * W.b₄ * W.b₆ ^ 4 * W.b₈ ^ 2 + (-68) * t ^ 6 * W.b₂ * W.b₄ * W.b₈ ^ 5
        + (75) * t ^ 6 * W.b₂ * W.b₆ ^ 6 * W.b₈ + (-172) * t ^ 6 * W.b₂ * W.b₆ ^ 2 * W.b₈ ^ 4
        + (-24) * t ^ 6 * W.b₄ ^ 6 * W.b₆ * W.b₈ ^ 2 + (84) * t ^ 6 * W.b₄ ^ 5 * W.b₆ ^ 3 * W.b₈
        + (-66) * t ^ 6 * W.b₄ ^ 4 * W.b₆ ^ 5 + (309) * t ^ 6 * W.b₄ ^ 4 * W.b₆ * W.b₈ ^ 3
        + (-777) * t ^ 6 * W.b₄ ^ 3 * W.b₆ ^ 3 * W.b₈ ^ 2 + (462) * t ^ 6 * W.b₄ ^ 2 * W.b₆ ^ 5 * W.b₈
        + (-587) * t ^ 6 * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 4 + (-18) * t ^ 6 * W.b₄ * W.b₆ ^ 7
        + (452) * t ^ 6 * W.b₄ * W.b₆ ^ 3 * W.b₈ ^ 3 + (375) * t ^ 6 * W.b₆ ^ 5 * W.b₈ ^ 2
        + (-100) * t ^ 6 * W.b₆ * W.b₈ ^ 5 + t ^ 5 * W.b₂ ^ 3 * W.b₆ ^ 3 * W.b₈ ^ 3
        + (27) * t ^ 5 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 3
        + (-39) * t ^ 5 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 4 * W.b₈ ^ 2
        + (-4) * t ^ 5 * W.b₂ ^ 2 * W.b₄ * W.b₈ ^ 5 + (9) * t ^ 5 * W.b₂ ^ 2 * W.b₆ ^ 6 * W.b₈
        + (-7) * t ^ 5 * W.b₂ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 4
        + (48) * t ^ 5 * W.b₂ * W.b₄ ^ 4 * W.b₆ * W.b₈ ^ 3
        + (-153) * t ^ 5 * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 3 * W.b₈ ^ 2
        + (129) * t ^ 5 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 5 * W.b₈
        + (-60) * t ^ 5 * W.b₂ * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 4 + (-21) * t ^ 5 * W.b₂ * W.b₄ * W.b₆ ^ 7
        + (100) * t ^ 5 * W.b₂ * W.b₄ * W.b₆ ^ 3 * W.b₈ ^ 3
        + (-18) * t ^ 5 * W.b₂ * W.b₆ ^ 5 * W.b₈ ^ 2 + (-20) * t ^ 5 * W.b₂ * W.b₆ * W.b₈ ^ 5
        + (8) * t ^ 5 * W.b₄ ^ 6 * W.b₈ ^ 3 + (-60) * t ^ 5 * W.b₄ ^ 5 * W.b₆ ^ 2 * W.b₈ ^ 2
        + (114) * t ^ 5 * W.b₄ ^ 4 * W.b₆ ^ 4 * W.b₈ + (-18) * t ^ 5 * W.b₄ ^ 4 * W.b₈ ^ 4
        + (-63) * t ^ 5 * W.b₄ ^ 3 * W.b₆ ^ 6 + (172) * t ^ 5 * W.b₄ ^ 3 * W.b₆ ^ 2 * W.b₈ ^ 3
        + (-264) * t ^ 5 * W.b₄ ^ 2 * W.b₆ ^ 4 * W.b₈ ^ 2 + (-44) * t ^ 5 * W.b₄ ^ 2 * W.b₈ ^ 5
        + (108) * t ^ 5 * W.b₄ * W.b₆ ^ 6 * W.b₈ + (-132) * t ^ 5 * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 4
        + (-9) * t ^ 5 * W.b₆ ^ 8 + (196) * t ^ 5 * W.b₆ ^ 4 * W.b₈ ^ 3
        + (3) * t ^ 4 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 3 * W.b₈ ^ 3
        + (-3) * t ^ 4 * W.b₂ ^ 2 * W.b₆ ^ 5 * W.b₈ ^ 2 - t ^ 4 * W.b₂ ^ 2 * W.b₆ * W.b₈ ^ 5
        + (21) * t ^ 4 * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 2 * W.b₈ ^ 3
        + (-51) * t ^ 4 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 4 * W.b₈ ^ 2
        + (-5) * t ^ 4 * W.b₂ * W.b₄ ^ 2 * W.b₈ ^ 5 + (33) * t ^ 4 * W.b₂ * W.b₄ * W.b₆ ^ 6 * W.b₈
        + (-10) * t ^ 4 * W.b₂ * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 4 + (-3) * t ^ 4 * W.b₂ * W.b₆ ^ 8
        + (17) * t ^ 4 * W.b₂ * W.b₆ ^ 4 * W.b₈ ^ 3 + (12) * t ^ 4 * W.b₄ ^ 5 * W.b₆ * W.b₈ ^ 3
        + (-54) * t ^ 4 * W.b₄ ^ 4 * W.b₆ ^ 3 * W.b₈ ^ 2 + (75) * t ^ 4 * W.b₄ ^ 3 * W.b₆ ^ 5 * W.b₈
        + (-23) * t ^ 4 * W.b₄ ^ 3 * W.b₆ * W.b₈ ^ 4 + (-33) * t ^ 4 * W.b₄ ^ 2 * W.b₆ ^ 7
        + (70) * t ^ 4 * W.b₄ ^ 2 * W.b₆ ^ 3 * W.b₈ ^ 3 + (-51) * t ^ 4 * W.b₄ * W.b₆ ^ 5 * W.b₈ ^ 2
        + (-20) * t ^ 4 * W.b₄ * W.b₆ * W.b₈ ^ 5 + (3) * t ^ 4 * W.b₆ ^ 7 * W.b₈
        + (20) * t ^ 4 * W.b₆ ^ 3 * W.b₈ ^ 4 + (3) * t ^ 3 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 3 * W.b₈ ^ 3
        + (-6) * t ^ 3 * W.b₂ * W.b₄ * W.b₆ ^ 5 * W.b₈ ^ 2
        + (-2) * t ^ 3 * W.b₂ * W.b₄ * W.b₆ * W.b₈ ^ 5 + (3) * t ^ 3 * W.b₂ * W.b₆ ^ 7 * W.b₈
        + (2) * t ^ 3 * W.b₂ * W.b₆ ^ 3 * W.b₈ ^ 4 + (6) * t ^ 3 * W.b₄ ^ 4 * W.b₆ ^ 2 * W.b₈ ^ 3
        + (-21) * t ^ 3 * W.b₄ ^ 3 * W.b₆ ^ 4 * W.b₈ ^ 2 + (-2) * t ^ 3 * W.b₄ ^ 3 * W.b₈ ^ 5
        + (24) * t ^ 3 * W.b₄ ^ 2 * W.b₆ ^ 6 * W.b₈ + (-3) * t ^ 3 * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 4
        + (-9) * t ^ 3 * W.b₄ * W.b₆ ^ 8 + (14) * t ^ 3 * W.b₄ * W.b₆ ^ 4 * W.b₈ ^ 3
        + (-9) * t ^ 3 * W.b₆ ^ 6 * W.b₈ ^ 2 + t ^ 2 * W.b₄ ^ 3 * W.b₆ ^ 3 * W.b₈ ^ 3
        + (-3) * t ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 5 * W.b₈ ^ 2 - t ^ 2 * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 5
        + (3) * t ^ 2 * W.b₄ * W.b₆ ^ 7 * W.b₈ + (2) * t ^ 2 * W.b₄ * W.b₆ ^ 3 * W.b₈ ^ 4
        - t ^ 2 * W.b₆ ^ 9 - t ^ 2 * W.b₆ ^ 5 * W.b₈ ^ 3) * W.b_relation

end StarInstances

end WeierstrassCurve

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

section Statement

def MFred (m : ℕ) {x y : F} (h : W.toAffine.Nonsingular x y) : Prop :=
  (W.ΨSq (m : ℤ)).eval x ≠ 0 ∧
    (m • (Point.some x y h : W.toAffine.Point)).xOrZero * (W.ΨSq (m : ℤ)).eval x =
      (W.Φ (m : ℤ)).eval x

def LowTorsionFree (m : ℕ) {x y : F} (h : W.toAffine.Nonsingular x y) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ m → k • (Point.some x y h : W.toAffine.Point) ≠ 0

lemma LowTorsionFree.mono {m n : ℕ} (hmn : m ≤ n) {x y : F} {h : W.toAffine.Nonsingular x y}
    (hf : LowTorsionFree n h) : LowTorsionFree m h :=
  fun k hk1 hkm => hf k hk1 (hkm.trans hmn)

end Statement

section BaseCases

theorem mfred_one {x y : F} (h : W.toAffine.Nonsingular x y) : MFred 1 h := by
  constructor
  · rw [Nat.cast_one, ΨSq_one]
    simp
  · rw [Nat.cast_one, ΨSq_one, Φ_one, one_nsmul, Point.xOrZero_some]
    simp

theorem mfred_two {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2 : (2 • (Point.some x y h : W.toAffine.Point)) ≠ 0) : MFred 2 h := by

  have hy : y ≠ W.toAffine.negY x y := fun hy =>
    h2 (by rw [two_nsmul]; exact Point.add_self_of_Y_eq hy)
  have hcast : ((2 : ℕ) : ℤ) = 2 := by norm_num
  have hΨ2 : (W.Ψ₂Sq).eval x ≠ 0 := Ψ₂Sq_eval_ne_zero' h.left hy
  constructor
  · rw [hcast, ΨSq_two]
    exact hΨ2
  ·
    have hns2 : W.toAffine.Nonsingular (W.toAffine.addX x x (W.toAffine.slope x x y y))
        (W.toAffine.addY x x y (W.toAffine.slope x x y y)) :=
      nonsingular_add h h fun hxy => hy hxy.right
    have h2P : (2 • (Point.some x y h : W.toAffine.Point)) = Point.some _ _ hns2 := by
      rw [two_nsmul]; exact Point.add_self_of_Y_ne hy
    rw [hcast, ΨSq_two, h2P, Point.xOrZero_some]
    exact addX_self_mul_Ψ₂Sq' h.left hy

end BaseCases

section Step

theorem mfred_step {m : ℕ} (hm : 1 ≤ m) {x y : F} (h : W.toAffine.Nonsingular x y)
    (hfree : LowTorsionFree (m + 2) h)
    (ih1 : MFred m h) (ih2 : MFred (m + 1) h)
    (hstar :
      2 * x * (W.Φ ((m : ℤ) + 1)).eval x *
            ((W.Φ ((m : ℤ) + 1)).eval x + x * (W.ΨSq ((m : ℤ) + 1)).eval x) +
          W.b₂ * x * ((W.Φ ((m : ℤ) + 1)).eval x * (W.ΨSq ((m : ℤ) + 1)).eval x) +
          W.b₄ * (((W.Φ ((m : ℤ) + 1)).eval x + x * (W.ΨSq ((m : ℤ) + 1)).eval x) *
            (W.ΨSq ((m : ℤ) + 1)).eval x) +
          W.b₆ * (W.ΨSq ((m : ℤ) + 1)).eval x ^ 2 =
        (W.Φ ((m : ℤ) + 2)).eval x * (W.ΨSq (m : ℤ)).eval x +
          (W.Φ (m : ℤ)).eval x * (W.ΨSq ((m : ℤ) + 2)).eval x) :
    MFred (m + 2) h := by

  have hc1 : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
  have hc2 : ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 := by push_cast; ring

  have hS1ne : (W.ΨSq (m : ℤ)).eval x ≠ 0 := ih1.1
  have hS2ne : (W.ΨSq ((m : ℤ) + 1)).eval x ≠ 0 := by
    have h' := ih2.1; rwa [hc1] at h'

  have hQne : ((m + 1) • (Point.some x y h : W.toAffine.Point)) ≠ 0 :=
    hfree (m + 1) (by omega) (by omega)
  obtain ⟨xq, yq, hq, hQeq⟩ : ∃ (xq yq : F) (hq : W.toAffine.Nonsingular xq yq),
      ((m + 1) • (Point.some x y h : W.toAffine.Point)) = Point.some xq yq hq := by
    cases hQP : ((m + 1) • (Point.some x y h : W.toAffine.Point)) with
    | zero => exact absurd hQP hQne
    | @some xq yq hq => exact ⟨xq, yq, hq, rfl⟩

  have hIH2eq : xq * (W.ΨSq ((m : ℤ) + 1)).eval x = (W.Φ ((m : ℤ) + 1)).eval x := by
    have h2 := ih2.2
    rw [hQeq, Point.xOrZero_some, hc1] at h2
    exact h2

  have hxqx : xq ≠ x := by
    intro hxx
    rcases Y_eq_of_X_eq hq.left h.left hxx with hyy | hyy
    ·
      apply hfree m hm (by omega)
      have hQ1 : ((m + 1) • (Point.some x y h : W.toAffine.Point)) = Point.some x y h := by
        rw [hQeq]; subst hxx; subst hyy
        rw [Subsingleton.elim hq h]
      have h0 : (m • (Point.some x y h : W.toAffine.Point)) + Point.some x y h =
          0 + Point.some x y h := by
        rw [zero_add, ← succ_nsmul, hQ1]
      exact add_right_cancel h0
    ·
      apply hfree (m + 2) (by omega) le_rfl
      have hQ1 : ((m + 1) • (Point.some x y h : W.toAffine.Point)) =
          -(Point.some x y h : W.toAffine.Point) := by
        rw [hQeq, Point.neg_some]
        subst hxx; subst hyy
        exact congrArg _ (Subsingleton.elim _ _)
      have hsucc : ((m + 2) • (Point.some x y h : W.toAffine.Point)) =
          ((m + 1) • (Point.some x y h : W.toAffine.Point)) + Point.some x y h :=
        succ_nsmul _ _
      rw [hsucc, hQ1, neg_add_cancel]

  have hIH1eq : W.toAffine.addX xq x (W.toAffine.slope xq x yq (W.toAffine.negY x y)) *
      (W.ΨSq (m : ℤ)).eval x = (W.Φ (m : ℤ)).eval x := by
    have h1 := ih1.2
    have hrearr : (m • (Point.some x y h : W.toAffine.Point)) =
        ((m + 1) • (Point.some x y h : W.toAffine.Point)) +
          (-(Point.some x y h : W.toAffine.Point)) := by
      rw [succ_nsmul, add_neg_cancel_right]
    rw [hrearr, hQeq, Point.neg_some, Point.add_of_X_ne hxqx, Point.xOrZero_some] at h1
    exact h1

  have hsum := addX_add_addX_negY_mul_sq' (W := W) hq.left h.left hxqx

  have hpoly := W.X_mul_ΨSq_sub_Φ_sq ((m : ℤ) + 1)
  rw [show ((m : ℤ) + 1 + 1) = (m : ℤ) + 2 by ring,
    show ((m : ℤ) + 1 - 1) = (m : ℤ) by ring] at hpoly
  have hev := congrArg (Polynomial.eval x) hpoly
  simp only [eval_pow, eval_sub, eval_mul, eval_X] at hev
  have hd2 : ((xq - x) * (W.ΨSq ((m : ℤ) + 1)).eval x) ^ 2 =
      (W.ΨSq ((m : ℤ) + 2)).eval x * (W.ΨSq (m : ℤ)).eval x := by
    linear_combination ((xq - 2 * x) * (W.ΨSq ((m : ℤ) + 1)).eval x +
      (W.Φ ((m : ℤ) + 1)).eval x) * hIH2eq + hev

  have hd2ne : ((xq - x) * (W.ΨSq ((m : ℤ) + 1)).eval x) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero (sub_ne_zero_of_ne hxqx) hS2ne)
  have hS3ne : (W.ΨSq ((m : ℤ) + 2)).eval x ≠ 0 := by
    intro h0
    apply hd2ne
    rw [hd2, h0, zero_mul]

  have hkey : W.toAffine.addX xq x (W.toAffine.slope xq x yq y) *
        (W.ΨSq ((m : ℤ) + 2)).eval x * ((W.ΨSq (m : ℤ)).eval x) ^ 2 =
      (W.Φ ((m : ℤ) + 2)).eval x * ((W.ΨSq (m : ℤ)).eval x) ^ 2 := by
    linear_combination
      ((W.ΨSq (m : ℤ)).eval x * ((W.ΨSq ((m : ℤ) + 1)).eval x) ^ 2) * hsum +
      (-(W.toAffine.addX xq x (W.toAffine.slope xq x yq y) +
          W.toAffine.addX xq x (W.toAffine.slope xq x yq (W.toAffine.negY x y))) *
        (W.ΨSq (m : ℤ)).eval x) * hd2 +
      ((W.ΨSq (m : ℤ)).eval x) * hstar +
      (-((W.ΨSq ((m : ℤ) + 2)).eval x * (W.ΨSq (m : ℤ)).eval x)) * hIH1eq +
      ((W.ΨSq (m : ℤ)).eval x *
        (2 * x * ((W.Φ ((m : ℤ) + 1)).eval x + xq * (W.ΨSq ((m : ℤ) + 1)).eval x +
          x * (W.ΨSq ((m : ℤ) + 1)).eval x) +
          W.b₂ * x * (W.ΨSq ((m : ℤ) + 1)).eval x +
          W.b₄ * (W.ΨSq ((m : ℤ) + 1)).eval x)) * hIH2eq

  constructor
  · rw [hc2]
    exact hS3ne
  · have hsucc2 : ((m + 2) • (Point.some x y h : W.toAffine.Point)) =
        ((m + 1) • (Point.some x y h : W.toAffine.Point)) + Point.some x y h :=
      succ_nsmul _ _
    rw [hc2, hsucc2, hQeq, Point.add_of_X_ne hxqx, Point.xOrZero_some]
    exact mul_right_cancel₀ (pow_ne_zero 2 hS1ne) hkey

end Step

section Shell

theorem mfred_of_forall_star (M : ℕ) {x y : F} (h : W.toAffine.Nonsingular x y)
    (hfree : LowTorsionFree M h)
    (hstar : ∀ j : ℤ, 2 ≤ j → j + 1 ≤ (M : ℤ) →
      2 * x * (W.Φ j).eval x * ((W.Φ j).eval x + x * (W.ΨSq j).eval x) +
          W.b₂ * x * ((W.Φ j).eval x * (W.ΨSq j).eval x) +
          W.b₄ * (((W.Φ j).eval x + x * (W.ΨSq j).eval x) * (W.ΨSq j).eval x) +
          W.b₆ * (W.ΨSq j).eval x ^ 2 =
        (W.Φ (j + 1)).eval x * (W.ΨSq (j - 1)).eval x +
          (W.Φ (j - 1)).eval x * (W.ΨSq (j + 1)).eval x) :
    ∀ m : ℕ, 1 ≤ m → m ≤ M → MFred m h := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm1 hmM
    by_cases hone : m = 1
    · subst hone; exact mfred_one h
    by_cases htwo : m = 2
    · subst htwo; exact mfred_two h (hfree 2 one_le_two hmM)

    obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
    have ih1 : MFred (k + 1) h := ih (k + 1) (by omega) (by omega) (by omega)
    have ih2 : MFred (k + 2) h := ih (k + 2) (by omega) (by omega) (by omega)
    have hs := hstar (((k + 1 : ℕ) : ℤ) + 1) (by push_cast; omega) (by push_cast; omega)
    rw [show ((k + 1 : ℕ) : ℤ) + 1 + 1 = ((k + 1 : ℕ) : ℤ) + 2 by ring,
      add_sub_cancel_right] at hs
    exact mfred_step (by omega) h (hfree.mono (by omega)) ih1 ih2 hs

theorem mfred_three {x y : F} (h : W.toAffine.Nonsingular x y)
    (hfree : LowTorsionFree 3 h) : MFred 3 h := by
  refine mfred_of_forall_star 3 h hfree (fun j hj2 hj3 => ?_) 3 (by norm_num) le_rfl

  have hj : j = 2 := by omega
  subst hj
  rw [show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num,
    ΨSq_one, Φ_one, ΨSq_three, ΨSq_two]
  simp only [eval_one, eval_X, eval_pow, mul_one]
  linear_combination ellipticNet_two (W := W) x

end Shell

end WeierstrassCurve.Affine

open Polynomial

namespace WeierstrassCurve

section StarIdentityDef

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

def StarIdentity (j : ℤ) : Prop :=
  ∀ t : R,
    2 * t * (W.Φ j).eval t * ((W.Φ j).eval t + t * (W.ΨSq j).eval t) +
        W.b₂ * t * ((W.Φ j).eval t * (W.ΨSq j).eval t) +
        W.b₄ * (((W.Φ j).eval t + t * (W.ΨSq j).eval t) * (W.ΨSq j).eval t) +
        W.b₆ * (W.ΨSq j).eval t ^ 2 =
      (W.Φ (j + 1)).eval t * (W.ΨSq (j - 1)).eval t +
        (W.Φ (j - 1)).eval t * (W.ΨSq (j + 1)).eval t

end StarIdentityDef

section BaseSet

variable {F : Type u} [Field F] (W : WeierstrassCurve F)

theorem starIdentity_of_le_four (j : ℤ) (h1 : 1 ≤ j) (h4 : j ≤ 4) : W.StarIdentity j := by
  intro t
  have hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hj with rfl | rfl | rfl | rfl
  ·
    rw [show (1 : ℤ) + 1 = 2 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num]
    linear_combination W.ellipticNet_one t
  ·
    rw [show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num,
      ΨSq_one, Φ_one, ΨSq_three, ΨSq_two]
    simp only [eval_one, eval_X, eval_pow, mul_one]
    linear_combination Affine.ellipticNet_two (W := W) t
  ·
    rw [show (3 : ℤ) + 1 = 4 by norm_num, show (3 : ℤ) - 1 = 2 by norm_num]
    linear_combination W.ellipticNet_three t
  ·
    rw [show (4 : ℤ) + 1 = 5 by norm_num, show (4 : ℤ) - 1 = 3 by norm_num]
    linear_combination W.ellipticNet_four t

end BaseSet

namespace Affine

variable {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

theorem mfred_of_forall_starIdentity (M : ℕ) {x y : F} (h : W.toAffine.Nonsingular x y)
    (hfree : LowTorsionFree M h)
    (hstar : ∀ j : ℤ, 2 ≤ j → j + 1 ≤ (M : ℤ) → W.StarIdentity j) :
    ∀ m : ℕ, 1 ≤ m → m ≤ M → MFred m h :=
  mfred_of_forall_star M h hfree fun j hj2 hjM => hstar j hj2 hjM x

theorem mfred_of_le_five {M : ℕ} (hM : M ≤ 5) {x y : F} (h : W.toAffine.Nonsingular x y)
    (hfree : LowTorsionFree M h) :
    ∀ m : ℕ, 1 ≤ m → m ≤ M → MFred m h := by
  refine mfred_of_forall_starIdentity M h hfree fun j hj2 hjM => ?_
  have hM5 : (M : ℤ) ≤ 5 := by exact_mod_cast hM
  exact W.starIdentity_of_le_four j (by omega) (by omega)

theorem mfred_four {x y : F} (h : W.toAffine.Nonsingular x y)
    (hfree : LowTorsionFree 4 h) : MFred 4 h :=
  mfred_of_le_five (by norm_num) h hfree 4 (by norm_num) le_rfl

theorem mfred_five {x y : F} (h : W.toAffine.Nonsingular x y)
    (hfree : LowTorsionFree 5 h) : MFred 5 h :=
  mfred_of_le_five le_rfl h hfree 5 (by norm_num) le_rfl

end Affine

end WeierstrassCurve

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] {W : WeierstrassCurve F}

section AbstractCores

variable {x xa xb xg xd xs x2 Sk Sk1 Skm Sk2 Fk Fk1 Fkm Fk2 p1 p0 p2 pm Qe P2e S2 F2
  b2 b4 b6 b8 : F}

private lemma star_eval_core {xj xjm xjp Sj Sjm Sjp Fj Fjm Fjp : F}
    (hMj : xj * Sj = Fj) (hMjm : xjm * Sjm = Fjm) (hMjp : xjp * Sjp = Fjp)
    (hsum : (xjp + xjm) * (xj - x) ^ 2 =
      2 * (xj * x) * (xj + x) + b2 * (xj * x) + b4 * (xj + x) + b6)
    (hd3 : (x * Sj - Fj) ^ 2 = Sjp * Sjm) :
    2 * x * Fj * (Fj + x * Sj) + b2 * x * (Fj * Sj) + b4 * ((Fj + x * Sj) * Sj) +
        b6 * Sj ^ 2 = Fjp * Sjm + Fjm * Sjp := by
  linear_combination
    ((xjp + xjm) * (Sj * xj - 2 * x * Sj + Fj) -
      (2 * x * (Fj + xj * Sj) + 2 * x ^ 2 * Sj + b2 * x * Sj + b4 * Sj)) * hMj +
    (-Sj ^ 2) * hsum + (xjp + xjm) * hd3 + Sjm * hMjp + Sjp * hMjm

private lemma odd_step_core
    (hM0 : xa * Sk = Fk) (hMm : xg * Skm = Fkm) (hM1 : xb * Sk1 = Fk1) (hM2 : xd * Sk2 = Fk2)
    (hD1 : Fk1 * Sk - Fk * Sk1 = -p1)
    (hD2a : Fk1 * Skm - Fkm * Sk1 = -(p0 * Qe))
    (hD2b : Fk2 * Sk - Fk * Sk2 = -(p2 * Qe))
    (hD3a : (x * Sk - Fk) ^ 2 = Sk1 * Skm)
    (hD3b : (x * Sk1 - Fk1) ^ 2 = Sk2 * Sk)
    (hPsi : S2 = p1 ^ 2) (hPhi : F2 = x * S2 - p2 * p0 * Qe)
    (hg1 : (xs + x) * (xb - xa) ^ 2 =
      2 * (xb * xa) * (xb + xa) + b2 * (xb * xa) + b4 * (xb + xa) + b6)
    (hg2 : (xd + xa) * (xb - x) ^ 2 =
      2 * (xb * x) * (xb + x) + b2 * (xb * x) + b4 * (xb + x) + b6)
    (hg3 : (xb + xg) * (xa - x) ^ 2 =
      2 * (xa * x) * (xa + x) + b2 * (xa * x) + b4 * (xa + x) + b6)
    (hg3p : xb * xg * (xa - x) ^ 2 =
      (xa * x) ^ 2 - b4 * (xa * x) - b6 * (xa + x) - b8)
    (hbrel : 4 * b8 = b2 * b6 - b4 ^ 2)
    (hQv : Qe = 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6)
    (hSkne : Sk ≠ 0) (hSk1ne : Sk1 ≠ 0) (hbane : xb ≠ xa) :
    S2 ≠ 0 ∧ xs * S2 * Qe = F2 * Qe := by

  have hp1 : p1 = -(Sk * Sk1 * (xb - xa)) := by
    linear_combination hD1 + Sk * hM1 - Sk1 * hM0
  have hP0 : p0 * Qe = -(Sk1 * Skm * (xb - xg)) := by
    linear_combination hD2a + Skm * hM1 - Sk1 * hMm
  have hP2 : p2 * Qe = -(Sk * Sk2 * (xd - xa)) := by
    linear_combination hD2b + Sk * hM2 - Sk2 * hM0
  have hSpk : Sk1 * Skm = Sk ^ 2 * (x - xa) ^ 2 := by
    linear_combination -hD3a + (2 * x * Sk - Fk - xa * Sk) * hM0
  have hSpk1 : Sk2 * Sk = Sk1 ^ 2 * (x - xb) ^ 2 := by
    linear_combination -hD3b + (2 * x * Sk1 - Fk1 - xb * Sk1) * hM1

  have hcore : (xs - x) * (xb - xa) ^ 2 * Qe +
      (x - xa) ^ 2 * (x - xb) ^ 2 * (xd - xa) * (xb - xg) = 0 := by
    linear_combination Qe * hg1 + ((x - xa) ^ 2 * (xb - xg)) * hg2 +
      (-(2 * (xb * x) * (xb + x) + b2 * (xb * x) + b4 * (xb + x) + b6 -
        2 * xa * (xb - x) ^ 2) - 4 * xb * (x - xa) * (x - xb)) * hg3 +
      (4 * (x - xa) * (x - xb)) * hg3p + (-((x - xa) * (x - xb))) * hbrel +
      (2 * (xa * xb) * (xa + xb) + b2 * (xa * xb) + b4 * (xa + xb) + b6 -
        2 * x * (xa - xb) ^ 2) * hQv
  refine ⟨?_, ?_⟩
  · rw [hPsi, hp1]
    exact pow_ne_zero 2 (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hSkne hSk1ne)
      (sub_ne_zero.mpr hbane)))
  · linear_combination (-Qe) * hPhi + (Qe * (xs - x)) * hPsi +
      (Qe * (xs - x) * (Sk * Sk1 * xa - Sk * Sk1 * xb + p1)) * hp1 +
      (Qe * p0) * hP2 + (Sk * Sk2 * (xa - xd)) * hP0 +
      (-(Sk * Sk2 * (xa - xd) * (xb - xg))) * hSpk +
      (-(Sk ^ 2 * (x - xa) ^ 2 * (xa - xd) * (xb - xg))) * hSpk1 +
      (Sk ^ 2 * Sk1 ^ 2) * hcore

private lemma even_step_core
    (hM0 : xa * Sk = Fk) (hMm : xg * Skm = Fkm) (hM1 : xb * Sk1 = Fk1)
    (hD1 : Fk1 * Sk - Fk * Sk1 = -p1)
    (hD1m : Fk * Skm - Fkm * Sk = -pm)
    (hD2a : Fk1 * Skm - Fkm * Sk1 = -(p0 * Qe))
    (hD3a : (x * Sk - Fk) ^ 2 = Sk1 * Skm)
    (hPsi : S2 = p0 ^ 2 * Qe) (hPhi : F2 = x * S2 - p1 * pm)
    (hg4 : (xs + x2) * (xb - xg) ^ 2 =
      2 * (xb * xg) * (xb + xg) + b2 * (xb * xg) + b4 * (xb + xg) + b6)
    (hdup : x2 * Qe = P2e)
    (hg3 : (xb + xg) * (xa - x) ^ 2 =
      2 * (xa * x) * (xa + x) + b2 * (xa * x) + b4 * (xa + x) + b6)
    (hg3p : xb * xg * (xa - x) ^ 2 =
      (xa * x) ^ 2 - b4 * (xa * x) - b6 * (xa + x) - b8)
    (hbrel : 4 * b8 = b2 * b6 - b4 ^ 2)
    (hQv : Qe = 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6)
    (hP2v : P2e = x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8)
    (hQne : Qe ≠ 0) (hSk1ne : Sk1 ≠ 0) (hSkmne : Skm ≠ 0)
    (haxne : xa ≠ x) (hbgne : xb ≠ xg) :
    S2 ≠ 0 ∧ xs * S2 * Qe = F2 * Qe := by

  have hp1 : p1 = -(Sk * Sk1 * (xb - xa)) := by
    linear_combination hD1 + Sk * hM1 - Sk1 * hM0
  have hpm : pm = -(Sk * Skm * (xa - xg)) := by
    linear_combination hD1m + Skm * hM0 - Sk * hMm
  have hP0 : p0 * Qe = -(Sk1 * Skm * (xb - xg)) := by
    linear_combination hD2a + Skm * hM1 - Sk1 * hMm
  have hSpk : Sk1 * Skm = Sk ^ 2 * (x - xa) ^ 2 := by
    linear_combination -hD3a + (2 * x * Sk - Fk - xa * Sk) * hM0

  have hbig : ((xs - x) * (x - xa) ^ 2 * (xb - xg) ^ 2 + (xb - xa) * (xa - xg) * Qe) *
      (Qe * (xa - x) ^ 2) = 0 := by
    rw [hQv, hP2v] at hdup
    rw [hQv]
    linear_combination
      (b2 * x ^ 6 - 4 * b2 * x ^ 5 * xa + 6 * b2 * x ^ 4 * xa ^ 2 - 4 * b2 * x ^ 3 * xa ^ 3 +
        b2 * x ^ 2 * xa ^ 4 + 4 * x ^ 7 - 16 * x ^ 6 * xa + 24 * x ^ 5 * xa ^ 2 -
        16 * x ^ 4 * xa ^ 3 + 4 * x ^ 3 * xa ^ 4 + 2 * b4 * x ^ 5 - 8 * b4 * x ^ 4 * xa +
        12 * b4 * x ^ 3 * xa ^ 2 - 8 * b4 * x ^ 2 * xa ^ 3 + 2 * b4 * x * xa ^ 4 +
        b6 * x ^ 4 - 4 * b6 * x ^ 3 * xa + 6 * b6 * x ^ 2 * xa ^ 2 - 4 * b6 * x * xa ^ 3 +
        b6 * xa ^ 4) * hg4 +
      (-x ^ 4 * xb ^ 2 + 2 * x ^ 4 * xb * xg - x ^ 4 * xg ^ 2 + 4 * x ^ 3 * xa * xb ^ 2 -
        8 * x ^ 3 * xa * xb * xg + 4 * x ^ 3 * xa * xg ^ 2 - 6 * x ^ 2 * xa ^ 2 * xb ^ 2 +
        12 * x ^ 2 * xa ^ 2 * xb * xg - 6 * x ^ 2 * xa ^ 2 * xg ^ 2 + 4 * x * xa ^ 3 * xb ^ 2 -
        8 * x * xa ^ 3 * xb * xg + 4 * x * xa ^ 3 * xg ^ 2 - xa ^ 4 * xb ^ 2 +
        2 * xa ^ 4 * xb * xg - xa ^ 4 * xg ^ 2) * hdup +
      (b2 * x ^ 5 * xa - b2 * x ^ 5 * xb - b2 * x ^ 5 * xg - 2 * b2 * x ^ 4 * xa ^ 2 +
        2 * b2 * x ^ 4 * xa * xb + 2 * b2 * x ^ 4 * xa * xg + 2 * b2 * x ^ 4 * xb * xg -
        b2 * x ^ 3 * xa ^ 2 * xb - b2 * x ^ 3 * xa ^ 2 * xg - 4 * b2 * x ^ 3 * xa * xb * xg +
        2 * b2 * x ^ 2 * xa ^ 2 * xb * xg + 6 * x ^ 6 * xa - 5 * x ^ 6 * xb - 5 * x ^ 6 * xg -
        10 * x ^ 5 * xa ^ 2 + 10 * x ^ 5 * xa * xb + 10 * x ^ 5 * xa * xg +
        8 * x ^ 5 * xb * xg - 5 * x ^ 4 * xa ^ 2 * xb - 5 * x ^ 4 * xa ^ 2 * xg -
        16 * x ^ 4 * xa * xb * xg + 8 * x ^ 3 * xa ^ 2 * xb * xg + b2 * b4 * x ^ 2 * xa ^ 2 -
        b4 * x ^ 5 + b4 * x ^ 4 * xa - b4 * x ^ 4 * xb - b4 * x ^ 4 * xg +
        2 * b4 * x ^ 3 * xa ^ 2 + 2 * b4 * x ^ 3 * xa * xb + 2 * b4 * x ^ 3 * xa * xg +
        4 * b4 * x ^ 3 * xb * xg - b4 * x ^ 2 * xa ^ 2 * xb - b4 * x ^ 2 * xa ^ 2 * xg -
        8 * b4 * x ^ 2 * xa * xb * xg + 4 * b4 * x * xa ^ 2 * xb * xg - b2 * b6 * x ^ 3 +
        3 * b2 * b6 * x ^ 2 * xa + b4 ^ 2 * x ^ 3 - b4 ^ 2 * x ^ 2 * xa +
        2 * b4 ^ 2 * x * xa ^ 2 - 5 * b6 * x ^ 4 + 10 * b6 * x ^ 3 * xa + b6 * x ^ 3 * xb +
        b6 * x ^ 3 * xg + 2 * b6 * x ^ 2 * xa ^ 2 - 2 * b6 * x ^ 2 * xa * xb -
        2 * b6 * x ^ 2 * xa * xg + 2 * b6 * x ^ 2 * xb * xg + b6 * x * xa ^ 2 * xb +
        b6 * x * xa ^ 2 * xg - 4 * b6 * x * xa * xb * xg + 2 * b6 * xa ^ 2 * xb * xg +
        b2 * b8 * x * xa + b4 * b6 * x ^ 2 + 3 * b4 * b6 * x * xa + b4 * b6 * xa ^ 2 +
        2 * b8 * x ^ 2 * xa + b8 * x ^ 2 * xb + b8 * x ^ 2 * xg + 2 * b8 * x * xa ^ 2 -
        2 * b8 * x * xa * xb - 2 * b8 * x * xa * xg + b8 * xa ^ 2 * xb + b8 * xa ^ 2 * xg +
        b4 * b8 * x + b4 * b8 * xa + b6 ^ 2 * x + b6 ^ 2 * xa + b6 * b8) * hg3 +
      (b2 ^ 2 * x ^ 2 * xa ^ 2 - 4 * b2 * x ^ 4 * xa + 12 * b2 * x ^ 3 * xa ^ 2 + 4 * x ^ 6 -
        24 * x ^ 5 * xa + 36 * x ^ 4 * xa ^ 2 + 2 * b2 * b4 * x ^ 2 * xa +
        2 * b2 * b4 * x * xa ^ 2 - 4 * b4 * x ^ 4 + 8 * b4 * x ^ 3 * xa +
        12 * b4 * x ^ 2 * xa ^ 2 + b2 * b6 * x ^ 2 + b2 * b6 * xa ^ 2 + 4 * b4 ^ 2 * x * xa -
        4 * b6 * x ^ 3 + 12 * b6 * x ^ 2 * xa + 2 * b4 * b6 * x + 2 * b4 * b6 * xa -
        4 * b8 * x ^ 2 + 8 * b8 * x * xa - 4 * b8 * xa ^ 2 + b6 ^ 2) * hg3p +
      (b2 * x ^ 4 * xa - 2 * b2 * x ^ 3 * xa ^ 2 + b2 * x ^ 2 * xa ^ 3 - x ^ 6 +
        6 * x ^ 5 * xa - 9 * x ^ 4 * xa ^ 2 + 4 * x ^ 3 * xa ^ 3 + b4 * x ^ 4 -
        3 * b4 * x ^ 2 * xa ^ 2 + 2 * b4 * x * xa ^ 3 + 2 * b6 * x ^ 3 -
        3 * b6 * x ^ 2 * xa + b6 * xa ^ 3 + b8 * x ^ 2 - 2 * b8 * x * xa + b8 * xa ^ 2) * hbrel
  have hcoreE : (xs - x) * (x - xa) ^ 2 * (xb - xg) ^ 2 + (xb - xa) * (xa - xg) * Qe = 0 :=
    (mul_eq_zero.mp hbig).resolve_right
      (mul_ne_zero hQne (pow_ne_zero 2 (sub_ne_zero.mpr (fun hE => haxne hE))))

  have hp0ne : p0 * Qe ≠ 0 := by
    rw [hP0]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hSk1ne hSkmne) (sub_ne_zero.mpr hbgne))
  refine ⟨?_, ?_⟩
  · intro hS20
    apply hp0ne
    have h0 : p0 ^ 2 * Qe = 0 := by rw [← hPsi]; exact hS20
    rcases mul_eq_zero.mp h0 with h | h
    · rcases pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h with h'
      rw [h', zero_mul]
    · exact absurd h hQne
  · linear_combination (-Qe) * hPhi + (Qe * (xs - x)) * hPsi + (Qe * pm) * hp1 +
      (Qe * Sk * Sk1 * (xa - xb)) * hpm +
      ((xs - x) * (Qe * p0 - Sk1 * Skm * xb + Sk1 * Skm * xg)) * hP0 +
      ((xs - x) * (xb - xg) ^ 2 * (Sk ^ 2 * (xa - x) ^ 2 + Sk1 * Skm) -
        Qe * Sk ^ 2 * (xa - xb) * (xa - xg)) * hSpk +
      (Sk ^ 4 * (xa - x) ^ 2) * hcoreE

end AbstractCores

variable [DecidableEq F]

theorem addX_mul_addX_negY_mul_sq' {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) *
        W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) *
        (x₁ - x₂) ^ 2 =
      (x₁ * x₂) ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈ :=
  Affine.addX_mul_addX_negY_mul_sq (W := W.toAffine) h₁ h₂ hx

omit [DecidableEq F] in

lemma x_ne_of_ne_of_ne_neg {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hne : (Point.some x₁ y₁ h₁ : W.toAffine.Point) ≠ Point.some x₂ y₂ h₂)
    (hne' : (Point.some x₁ y₁ h₁ : W.toAffine.Point) ≠ -Point.some x₂ y₂ h₂) : x₁ ≠ x₂ := by
  intro hxx
  rcases Y_eq_of_X_eq h₁.left h₂.left hxx with hyy | hyy
  · subst hxx; subst hyy
    exact hne (by rw [Subsingleton.elim h₁ h₂])
  · subst hxx; subst hyy
    exact hne' (by rw [Point.neg_some])

set_option maxHeartbeats 800000 in

theorem mfred_double_succ {n : ℕ} (hn : 1 ≤ n) {x y : F} (h : W.toAffine.Nonsingular x y)
    (hfree : LowTorsionFree (2 * n + 3) h)
    (ih0 : MFred n h) (ih1 : MFred (n + 1) h) (ih2 : MFred (n + 2) h)
    (ih3 : MFred (n + 3) h) : MFred (2 * n + 3) h := by

  have hc1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  have hc2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
  have hc3 : ((n + 3 : ℕ) : ℤ) = (n : ℤ) + 3 := by push_cast; ring
  have hc23 : ((2 * n + 3 : ℕ) : ℤ) = 2 * (n : ℤ) + 3 := by push_cast; ring

  have hy2 : y ≠ W.toAffine.negY x y := fun hy =>
    hfree 2 one_le_two (by omega) (by rw [two_nsmul]; exact Point.add_self_of_Y_eq hy)
  have hQne : (W.Ψ₂Sq).eval x ≠ 0 := Ψ₂Sq_eval_ne_zero' h.left hy2

  obtain ⟨xa, ya, ha, haeq⟩ : ∃ (xa ya : F) (ha : W.toAffine.Nonsingular xa ya),
      ((n + 1) • (Point.some x y h : W.toAffine.Point)) = Point.some xa ya ha := by
    cases hE : ((n + 1) • (Point.some x y h : W.toAffine.Point)) with
    | zero => exact absurd hE (hfree (n + 1) (by omega) (by omega))
    | @some xa ya ha => exact ⟨xa, ya, ha, rfl⟩
  obtain ⟨xb, yb, hb, hbeq⟩ : ∃ (xb yb : F) (hb : W.toAffine.Nonsingular xb yb),
      ((n + 2) • (Point.some x y h : W.toAffine.Point)) = Point.some xb yb hb := by
    cases hE : ((n + 2) • (Point.some x y h : W.toAffine.Point)) with
    | zero => exact absurd hE (hfree (n + 2) (by omega) (by omega))
    | @some xb yb hb => exact ⟨xb, yb, hb, rfl⟩

  have hax : xa ≠ x := by
    refine x_ne_of_ne_of_ne_neg ha h ?_ ?_
    · intro hE
      refine hfree n hn (by omega) (add_right_cancel (b := (Point.some x y h)) ?_)
      rw [← succ_nsmul, haeq, hE, zero_add]
    · intro hE
      refine hfree (n + 2) (by omega) (by omega) ?_
      rw [show n + 2 = (n + 1) + 1 by ring, succ_nsmul, haeq, hE, neg_add_cancel]
  have hbx : xb ≠ x := by
    refine x_ne_of_ne_of_ne_neg hb h ?_ ?_
    · intro hE
      refine hfree (n + 1) (by omega) (by omega) (add_right_cancel (b := (Point.some x y h)) ?_)
      rw [← succ_nsmul, show (n + 1) + 1 = n + 2 by ring, hbeq, hE, zero_add]
    · intro hE
      refine hfree (n + 3) (by omega) (by omega) ?_
      rw [show n + 3 = (n + 2) + 1 by ring, succ_nsmul, hbeq, hE, neg_add_cancel]
  have hba : xb ≠ xa := by
    refine x_ne_of_ne_of_ne_neg hb ha ?_ ?_
    · intro hE
      refine hfree 1 le_rfl (by omega) ?_
      rw [one_nsmul]
      refine add_left_cancel (a := ((n + 1) • (Point.some x y h : W.toAffine.Point))) ?_
      rw [add_zero, ← succ_nsmul, show (n + 1) + 1 = n + 2 by ring, hbeq, hE, ← haeq]
    · intro hE
      refine hfree (2 * n + 3) (by omega) le_rfl ?_
      rw [show 2 * n + 3 = (n + 2) + (n + 1) by ring, add_nsmul, hbeq, haeq, hE,
        neg_add_cancel]

  have hrearr0 : (n • (Point.some x y h : W.toAffine.Point)) =
      ((n + 1) • (Point.some x y h : W.toAffine.Point)) + -(Point.some x y h) := by
    rw [succ_nsmul, add_neg_cancel_right]
  have hrearr3 : ((n + 3) • (Point.some x y h : W.toAffine.Point)) =
      ((n + 2) • (Point.some x y h : W.toAffine.Point)) + (Point.some x y h) := by
    rw [show n + 3 = (n + 2) + 1 by ring, succ_nsmul]
  have hrearrS : ((2 * n + 3) • (Point.some x y h : W.toAffine.Point)) =
      ((n + 2) • (Point.some x y h : W.toAffine.Point)) +
        ((n + 1) • (Point.some x y h : W.toAffine.Point)) := by
    rw [show 2 * n + 3 = (n + 2) + (n + 1) by ring, add_nsmul]
  have hM0 : xa * (W.ΨSq ((n : ℤ) + 1)).eval x = (W.Φ ((n : ℤ) + 1)).eval x := by
    have h1 := ih1.2
    rwa [haeq, Point.xOrZero_some, hc1] at h1
  have hM1 : xb * (W.ΨSq ((n : ℤ) + 2)).eval x = (W.Φ ((n : ℤ) + 2)).eval x := by
    have h1 := ih2.2
    rwa [hbeq, Point.xOrZero_some, hc2] at h1
  have hMm : W.toAffine.addX xa x (W.toAffine.slope xa x ya (W.toAffine.negY x y)) *
      (W.ΨSq (n : ℤ)).eval x = (W.Φ (n : ℤ)).eval x := by
    have h1 := ih0.2
    rwa [hrearr0, haeq, Point.neg_some, Point.add_of_X_ne hax, Point.xOrZero_some] at h1
  have hM2 : W.toAffine.addX xb x (W.toAffine.slope xb x yb y) *
      (W.ΨSq ((n : ℤ) + 3)).eval x = (W.Φ ((n : ℤ) + 3)).eval x := by
    have h1 := ih3.2
    rwa [hrearr3, hbeq, Point.add_of_X_ne hbx, Point.xOrZero_some, hc3] at h1

  have hbdec : ((n + 2) • (Point.some x y h : W.toAffine.Point)) =
      Point.some xa ya ha + Point.some x y h := by
    rw [show n + 2 = (n + 1) + 1 by ring, succ_nsmul, haeq]
  have hbid : W.toAffine.addX xa x (W.toAffine.slope xa x ya y) = xb := by
    rw [Point.add_of_X_ne hax] at hbdec
    simpa using congrArg Point.xOrZero (hbdec.symm.trans hbeq)
  have hadec : ((n + 1) • (Point.some x y h : W.toAffine.Point)) =
      Point.some xb yb hb + -(Point.some x y h) := by
    have h0 : ((n + 2) • (Point.some x y h : W.toAffine.Point)) =
        ((n + 1) • (Point.some x y h : W.toAffine.Point)) + (Point.some x y h) := by
      rw [show n + 2 = (n + 1) + 1 by ring, succ_nsmul]
    rw [← hbeq, h0]
    abel
  have haid : W.toAffine.addX xb x (W.toAffine.slope xb x yb (W.toAffine.negY x y)) = xa := by
    rw [Point.neg_some, Point.add_of_X_ne hbx] at hadec
    simpa using congrArg Point.xOrZero (hadec.symm.trans haeq)
  have hxdec : (Point.some x y h : W.toAffine.Point) =
      Point.some xb yb hb + -(Point.some xa ya ha) := by
    have h0 : (Point.some x y h : W.toAffine.Point) =
        ((n + 2) • (Point.some x y h : W.toAffine.Point)) -
          ((n + 1) • (Point.some x y h : W.toAffine.Point)) := by
      rw [show n + 2 = (n + 1) + 1 by ring, succ_nsmul]
      abel
    rw [h0, hbeq, haeq, sub_eq_add_neg]
  have hxid : W.toAffine.addX xb xa (W.toAffine.slope xb xa yb (W.toAffine.negY xa ya)) = x := by
    rw [Point.neg_some, Point.add_of_X_ne hba] at hxdec
    simpa using congrArg Point.xOrZero hxdec.symm

  have hg3 := addX_add_addX_negY_mul_sq' (W := W) ha.left h.left hax
  rw [hbid] at hg3
  have hg3p := addX_mul_addX_negY_mul_sq' (W := W) ha.left h.left hax
  rw [hbid] at hg3p
  have hg2 := addX_add_addX_negY_mul_sq' (W := W) hb.left h.left hbx
  rw [haid] at hg2
  have hg1 := addX_add_addX_negY_mul_sq' (W := W) hb.left ha.left hba
  rw [hxid] at hg1

  have hD1 : (W.Φ ((n : ℤ) + 2)).eval x * (W.ΨSq ((n : ℤ) + 1)).eval x -
      (W.Φ ((n : ℤ) + 1)).eval x * (W.ΨSq ((n : ℤ) + 2)).eval x =
      -(W.preΨ (2 * (n : ℤ) + 3)).eval x := by
    have hpoly := W.Φ_succ_mul_ΨSq_sub_Φ_mul_ΨSq_succ ((n : ℤ) + 1)
    rw [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring,
      show 2 * ((n : ℤ) + 1) + 1 = 2 * (n : ℤ) + 3 by ring] at hpoly
    have hev := congrArg (Polynomial.eval x) hpoly
    simpa only [eval_sub, eval_mul, eval_neg] using hev
  have hD2a : (W.Φ ((n : ℤ) + 2)).eval x * (W.ΨSq (n : ℤ)).eval x -
      (W.Φ (n : ℤ)).eval x * (W.ΨSq ((n : ℤ) + 2)).eval x =
      -((W.preΨ (2 * (n : ℤ) + 2)).eval x * (W.Ψ₂Sq).eval x) := by
    have hpoly := W.Φ_succ_mul_ΨSq_pred_sub_Φ_pred_mul_ΨSq_succ ((n : ℤ) + 1)
    rw [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring, show (n : ℤ) + 1 - 1 = (n : ℤ) by ring,
      show 2 * ((n : ℤ) + 1) = 2 * (n : ℤ) + 2 by ring] at hpoly
    have hev := congrArg (Polynomial.eval x) hpoly
    simpa only [eval_sub, eval_mul, eval_neg] using hev
  have hD2b : (W.Φ ((n : ℤ) + 3)).eval x * (W.ΨSq ((n : ℤ) + 1)).eval x -
      (W.Φ ((n : ℤ) + 1)).eval x * (W.ΨSq ((n : ℤ) + 3)).eval x =
      -((W.preΨ (2 * (n : ℤ) + 4)).eval x * (W.Ψ₂Sq).eval x) := by
    have hpoly := W.Φ_succ_mul_ΨSq_pred_sub_Φ_pred_mul_ΨSq_succ ((n : ℤ) + 2)
    rw [show (n : ℤ) + 2 + 1 = (n : ℤ) + 3 by ring, show (n : ℤ) + 2 - 1 = (n : ℤ) + 1 by ring,
      show 2 * ((n : ℤ) + 2) = 2 * (n : ℤ) + 4 by ring] at hpoly
    have hev := congrArg (Polynomial.eval x) hpoly
    simpa only [eval_sub, eval_mul, eval_neg] using hev
  have hD3a : (x * (W.ΨSq ((n : ℤ) + 1)).eval x - (W.Φ ((n : ℤ) + 1)).eval x) ^ 2 =
      (W.ΨSq ((n : ℤ) + 2)).eval x * (W.ΨSq (n : ℤ)).eval x := by
    have hpoly := W.X_mul_ΨSq_sub_Φ_sq ((n : ℤ) + 1)
    rw [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring,
      show (n : ℤ) + 1 - 1 = (n : ℤ) by ring] at hpoly
    have hev := congrArg (Polynomial.eval x) hpoly
    simpa only [eval_pow, eval_sub, eval_mul, eval_X] using hev
  have hD3b : (x * (W.ΨSq ((n : ℤ) + 2)).eval x - (W.Φ ((n : ℤ) + 2)).eval x) ^ 2 =
      (W.ΨSq ((n : ℤ) + 3)).eval x * (W.ΨSq ((n : ℤ) + 1)).eval x := by
    have hpoly := W.X_mul_ΨSq_sub_Φ_sq ((n : ℤ) + 2)
    rw [show (n : ℤ) + 2 + 1 = (n : ℤ) + 3 by ring,
      show (n : ℤ) + 2 - 1 = (n : ℤ) + 1 by ring] at hpoly
    have hev := congrArg (Polynomial.eval x) hpoly
    simpa only [eval_pow, eval_sub, eval_mul, eval_X] using hev
  have hPsi : (W.ΨSq (2 * (n : ℤ) + 3)).eval x = ((W.preΨ (2 * (n : ℤ) + 3)).eval x) ^ 2 := by
    have hodd : ¬ Even (2 * (n : ℤ) + 3) := by
      rintro ⟨r, hr⟩
      omega
    have hev := congrArg (Polynomial.eval x) (W.ΨSq_of_odd hodd)
    simpa only [eval_pow] using hev
  have hPhi : (W.Φ (2 * (n : ℤ) + 3)).eval x =
      x * (W.ΨSq (2 * (n : ℤ) + 3)).eval x -
        (W.preΨ (2 * (n : ℤ) + 4)).eval x * (W.preΨ (2 * (n : ℤ) + 2)).eval x *
          (W.Ψ₂Sq).eval x := by
    have hpoly := W.Φ_two_mul_add_one ((n : ℤ) + 1)
    rw [show 2 * ((n : ℤ) + 1) + 1 = 2 * (n : ℤ) + 3 by ring,
      show 2 * ((n : ℤ) + 1) + 2 = 2 * (n : ℤ) + 4 by ring,
      show 2 * ((n : ℤ) + 1) = 2 * (n : ℤ) + 2 by ring] at hpoly
    have hev := congrArg (Polynomial.eval x) hpoly
    simpa only [eval_sub, eval_mul, eval_X] using hev

  have hSkne : (W.ΨSq ((n : ℤ) + 1)).eval x ≠ 0 := by have h1 := ih1.1; rwa [hc1] at h1
  have hSk1ne : (W.ΨSq ((n : ℤ) + 2)).eval x ≠ 0 := by have h1 := ih2.1; rwa [hc2] at h1

  obtain ⟨hS2ne, hmain⟩ := odd_step_core hM0 hMm hM1 hM2 hD1 hD2a hD2b hD3a hD3b hPsi hPhi
    hg1 hg2 hg3 hg3p W.b_relation (eval_Ψ₂Sq' x) hSkne hSk1ne hba
  constructor
  · rwa [hc23]
  · rw [hc23, hrearrS, hbeq, haeq, Point.add_of_X_ne hba, Point.xOrZero_some]
    exact mul_right_cancel₀ hQne hmain

set_option maxHeartbeats 800000 in

theorem mfred_double {n : ℕ} (hn : 1 ≤ n) {x y : F} (h : W.toAffine.Nonsingular x y)
    (hfree : LowTorsionFree (2 * n + 2) h)
    (ih0 : MFred n h) (ih1 : MFred (n + 1) h) (ih2 : MFred (n + 2) h) :
    MFred (2 * n + 2) h := by

  have hc1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  have hc2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
  have hc22 : ((2 * n + 2 : ℕ) : ℤ) = 2 * (n : ℤ) + 2 := by push_cast; ring

  have hy2 : y ≠ W.toAffine.negY x y := fun hy =>
    hfree 2 one_le_two (by omega) (by rw [two_nsmul]; exact Point.add_self_of_Y_eq hy)
  have hQne : (W.Ψ₂Sq).eval x ≠ 0 := Ψ₂Sq_eval_ne_zero' h.left hy2

  obtain ⟨xa, ya, ha, haeq⟩ : ∃ (xa ya : F) (ha : W.toAffine.Nonsingular xa ya),
      ((n + 1) • (Point.some x y h : W.toAffine.Point)) = Point.some xa ya ha := by
    cases hE : ((n + 1) • (Point.some x y h : W.toAffine.Point)) with
    | zero => exact absurd hE (hfree (n + 1) (by omega) (by omega))
    | @some xa ya ha => exact ⟨xa, ya, ha, rfl⟩
  obtain ⟨xb, yb, hb, hbeq⟩ : ∃ (xb yb : F) (hb : W.toAffine.Nonsingular xb yb),
      ((n + 2) • (Point.some x y h : W.toAffine.Point)) = Point.some xb yb hb := by
    cases hE : ((n + 2) • (Point.some x y h : W.toAffine.Point)) with
    | zero => exact absurd hE (hfree (n + 2) (by omega) (by omega))
    | @some xb yb hb => exact ⟨xb, yb, hb, rfl⟩
  obtain ⟨xg, yg, hgc, hgeq⟩ : ∃ (xg yg : F) (hgc : W.toAffine.Nonsingular xg yg),
      (n • (Point.some x y h : W.toAffine.Point)) = Point.some xg yg hgc := by
    cases hE : (n • (Point.some x y h : W.toAffine.Point)) with
    | zero => exact absurd hE (hfree n hn (by omega))
    | @some xg yg hgc => exact ⟨xg, yg, hgc, rfl⟩
  obtain ⟨x2, y2, h2c, h2eq⟩ : ∃ (x2 y2 : F) (h2c : W.toAffine.Nonsingular x2 y2),
      ((2 : ℕ) • (Point.some x y h : W.toAffine.Point)) = Point.some x2 y2 h2c := by
    cases hE : ((2 : ℕ) • (Point.some x y h : W.toAffine.Point)) with
    | zero => exact absurd hE (hfree 2 one_le_two (by omega))
    | @some x2 y2 h2c => exact ⟨x2, y2, h2c, rfl⟩

  have hax : xa ≠ x := by
    refine x_ne_of_ne_of_ne_neg ha h ?_ ?_
    · intro hE
      refine hfree n hn (by omega) (add_right_cancel (b := (Point.some x y h)) ?_)
      rw [← succ_nsmul, haeq, hE, zero_add]
    · intro hE
      refine hfree (n + 2) (by omega) (by omega) ?_
      rw [show n + 2 = (n + 1) + 1 by ring, succ_nsmul, haeq, hE, neg_add_cancel]
  have hbg : xb ≠ xg := by
    refine x_ne_of_ne_of_ne_neg hb hgc ?_ ?_
    · intro hE
      refine hfree 2 one_le_two (by omega) (add_right_cancel
        (b := (n • (Point.some x y h : W.toAffine.Point))) ?_)
      rw [← add_nsmul, show 2 + n = n + 2 by ring, hbeq, hE, zero_add, ← hgeq]
    · intro hE
      refine hfree (2 * n + 2) (by omega) le_rfl ?_
      rw [show 2 * n + 2 = (n + 2) + n by ring, add_nsmul, hbeq, hgeq, hE, neg_add_cancel]

  have hM0 : xa * (W.ΨSq ((n : ℤ) + 1)).eval x = (W.Φ ((n : ℤ) + 1)).eval x := by
    have h1 := ih1.2
    rwa [haeq, Point.xOrZero_some, hc1] at h1
  have hM1 : xb * (W.ΨSq ((n : ℤ) + 2)).eval x = (W.Φ ((n : ℤ) + 2)).eval x := by
    have h1 := ih2.2
    rwa [hbeq, Point.xOrZero_some, hc2] at h1
  have hMm : xg * (W.ΨSq (n : ℤ)).eval x = (W.Φ (n : ℤ)).eval x := by
    have h1 := ih0.2
    rwa [hgeq, Point.xOrZero_some] at h1

  have hbdec : ((n + 2) • (Point.some x y h : W.toAffine.Point)) =
      Point.some xa ya ha + Point.some x y h := by
    rw [show n + 2 = (n + 1) + 1 by ring, succ_nsmul, haeq]
  have hbid : W.toAffine.addX xa x (W.toAffine.slope xa x ya y) = xb := by
    rw [Point.add_of_X_ne hax] at hbdec
    simpa using congrArg Point.xOrZero (hbdec.symm.trans hbeq)
  have hgdec : (n • (Point.some x y h : W.toAffine.Point)) =
      Point.some xa ya ha + -(Point.some x y h) := by
    rw [← haeq, succ_nsmul, add_neg_cancel_right]
  have hgid : W.toAffine.addX xa x (W.toAffine.slope xa x ya (W.toAffine.negY x y)) = xg := by
    rw [Point.neg_some, Point.add_of_X_ne hax] at hgdec
    simpa using congrArg Point.xOrZero (hgdec.symm.trans hgeq)
  have h2dec_pair : ((2 : ℕ) • (Point.some x y h : W.toAffine.Point)) =
      Point.some xb yb hb + -(Point.some xg yg hgc) := by
    have h0 : ((2 : ℕ) • (Point.some x y h : W.toAffine.Point)) =
        ((n + 2) • (Point.some x y h : W.toAffine.Point)) -
          (n • (Point.some x y h : W.toAffine.Point)) := by
      rw [show n + 2 = 2 + n by ring, add_nsmul]
      abel
    rw [h0, hbeq, hgeq, sub_eq_add_neg]
  have hx2id_pair : W.toAffine.addX xb xg (W.toAffine.slope xb xg yb (W.toAffine.negY xg yg)) =
      x2 := by
    rw [Point.neg_some, Point.add_of_X_ne hbg] at h2dec_pair
    simpa using congrArg Point.xOrZero (h2dec_pair.symm.trans h2eq)
  have h2dec_dup : ((2 : ℕ) • (Point.some x y h : W.toAffine.Point)) =
      Point.some x y h + Point.some x y h := two_nsmul _
  have hx2id_dup : W.toAffine.addX x x (W.toAffine.slope x x y y) = x2 := by
    rw [Point.add_self_of_Y_ne hy2] at h2dec_dup
    simpa using congrArg Point.xOrZero (h2dec_dup.symm.trans h2eq)

  have hg3 := addX_add_addX_negY_mul_sq' (W := W) ha.left h.left hax
  rw [hbid, hgid] at hg3
  have hg3p := addX_mul_addX_negY_mul_sq' (W := W) ha.left h.left hax
  rw [hbid, hgid] at hg3p
  have hg4 := addX_add_addX_negY_mul_sq' (W := W) hb.left hgc.left hbg
  rw [hx2id_pair] at hg4
  have hdup := addX_self_mul_Ψ₂Sq' (W := W) h.left hy2
  rw [hx2id_dup] at hdup

  have hD1 : (W.Φ ((n : ℤ) + 2)).eval x * (W.ΨSq ((n : ℤ) + 1)).eval x -
      (W.Φ ((n : ℤ) + 1)).eval x * (W.ΨSq ((n : ℤ) + 2)).eval x =
      -(W.preΨ (2 * (n : ℤ) + 3)).eval x := by
    have hpoly := W.Φ_succ_mul_ΨSq_sub_Φ_mul_ΨSq_succ ((n : ℤ) + 1)
    rw [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring,
      show 2 * ((n : ℤ) + 1) + 1 = 2 * (n : ℤ) + 3 by ring] at hpoly
    have hev := congrArg (Polynomial.eval x) hpoly
    simpa only [eval_sub, eval_mul, eval_neg] using hev
  have hD1m : (W.Φ ((n : ℤ) + 1)).eval x * (W.ΨSq (n : ℤ)).eval x -
      (W.Φ (n : ℤ)).eval x * (W.ΨSq ((n : ℤ) + 1)).eval x =
      -(W.preΨ (2 * (n : ℤ) + 1)).eval x := by
    have hpoly := W.Φ_succ_mul_ΨSq_sub_Φ_mul_ΨSq_succ ((n : ℤ))
    have hev := congrArg (Polynomial.eval x) hpoly
    simpa only [eval_sub, eval_mul, eval_neg] using hev
  have hD2a : (W.Φ ((n : ℤ) + 2)).eval x * (W.ΨSq (n : ℤ)).eval x -
      (W.Φ (n : ℤ)).eval x * (W.ΨSq ((n : ℤ) + 2)).eval x =
      -((W.preΨ (2 * (n : ℤ) + 2)).eval x * (W.Ψ₂Sq).eval x) := by
    have hpoly := W.Φ_succ_mul_ΨSq_pred_sub_Φ_pred_mul_ΨSq_succ ((n : ℤ) + 1)
    rw [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring, show (n : ℤ) + 1 - 1 = (n : ℤ) by ring,
      show 2 * ((n : ℤ) + 1) = 2 * (n : ℤ) + 2 by ring] at hpoly
    have hev := congrArg (Polynomial.eval x) hpoly
    simpa only [eval_sub, eval_mul, eval_neg] using hev
  have hD3a : (x * (W.ΨSq ((n : ℤ) + 1)).eval x - (W.Φ ((n : ℤ) + 1)).eval x) ^ 2 =
      (W.ΨSq ((n : ℤ) + 2)).eval x * (W.ΨSq (n : ℤ)).eval x := by
    have hpoly := W.X_mul_ΨSq_sub_Φ_sq ((n : ℤ) + 1)
    rw [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring,
      show (n : ℤ) + 1 - 1 = (n : ℤ) by ring] at hpoly
    have hev := congrArg (Polynomial.eval x) hpoly
    simpa only [eval_pow, eval_sub, eval_mul, eval_X] using hev
  have hPsi : (W.ΨSq (2 * (n : ℤ) + 2)).eval x =
      ((W.preΨ (2 * (n : ℤ) + 2)).eval x) ^ 2 * (W.Ψ₂Sq).eval x := by
    have heven : Even (2 * (n : ℤ) + 2) := ⟨(n : ℤ) + 1, by ring⟩
    have hev := congrArg (Polynomial.eval x) (W.ΨSq_of_even heven)
    simpa only [eval_mul, eval_pow] using hev
  have hPhi : (W.Φ (2 * (n : ℤ) + 2)).eval x =
      x * (W.ΨSq (2 * (n : ℤ) + 2)).eval x -
        (W.preΨ (2 * (n : ℤ) + 3)).eval x * (W.preΨ (2 * (n : ℤ) + 1)).eval x := by
    have hpoly := W.Φ_two_mul ((n : ℤ) + 1)
    rw [show 2 * ((n : ℤ) + 1) = 2 * (n : ℤ) + 2 by ring,
      show 2 * (n : ℤ) + 2 + 1 = 2 * (n : ℤ) + 3 by ring,
      show 2 * (n : ℤ) + 2 - 1 = 2 * (n : ℤ) + 1 by ring] at hpoly
    have hev := congrArg (Polynomial.eval x) hpoly
    simpa only [eval_sub, eval_mul, eval_X] using hev

  have hSk1ne : (W.ΨSq ((n : ℤ) + 2)).eval x ≠ 0 := by have h1 := ih2.1; rwa [hc2] at h1
  have hSkmne : (W.ΨSq (n : ℤ)).eval x ≠ 0 := ih0.1

  obtain ⟨hS2ne, hmain⟩ := even_step_core hM0 hMm hM1 hD1 hD1m hD2a hD3a hPsi hPhi
    hg4 hdup hg3 hg3p W.b_relation (eval_Ψ₂Sq' x) (eval_Φ_two' x) hQne hSk1ne hSkmne
    hax hbg
  have hrearrS : ((2 * n + 2) • (Point.some x y h : W.toAffine.Point)) =
      ((n + 2) • (Point.some x y h : W.toAffine.Point)) +
        (n • (Point.some x y h : W.toAffine.Point)) := by
    rw [show 2 * n + 2 = (n + 2) + n by ring, add_nsmul]
  constructor
  · rwa [hc22]
  · rw [hc22, hrearrS, hbeq, hgeq, Point.add_of_X_ne hbg, Point.xOrZero_some]
    exact mul_right_cancel₀ hQne hmain

theorem mfred_all {x y : F} (h : W.toAffine.Nonsingular x y) (m : ℕ) (hm : 1 ≤ m)
    (hfree : LowTorsionFree m h) : MFred m h := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases h5 : m ≤ 5
    · exact mfred_of_le_five h5 h hfree m hm le_rfl
    · rcases Nat.even_or_odd m with hev | hodd
      · obtain ⟨q, rfl⟩ : ∃ q, m = 2 * q + 2 := by
          obtain ⟨r, hr⟩ := hev
          exact ⟨r - 1, by omega⟩
        exact mfred_double (by omega) h hfree
          (ih q (by omega) (by omega) (hfree.mono (by omega)))
          (ih (q + 1) (by omega) (by omega) (hfree.mono (by omega)))
          (ih (q + 2) (by omega) (by omega) (hfree.mono (by omega)))
      · obtain ⟨q, rfl⟩ : ∃ q, m = 2 * q + 3 := by
          obtain ⟨r, hr⟩ := hodd
          exact ⟨r - 1, by omega⟩
        exact mfred_double_succ (by omega) h hfree
          (ih q (by omega) (by omega) (hfree.mono (by omega)))
          (ih (q + 1) (by omega) (by omega) (hfree.mono (by omega)))
          (ih (q + 2) (by omega) (by omega) (hfree.mono (by omega)))
          (ih (q + 3) (by omega) (by omega) (hfree.mono (by omega)))
end WeierstrassCurve.Affine

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

section RootToTorsion

theorem nsmul_succ_eq_zero_of_ΨSq_eval_eq_zero {m : ℕ} (hm : 2 ≤ m) {x y : F}
    (h : W.toAffine.Nonsingular x y) (hfree : LowTorsionFree m h) (hmf : MFred m h)
    (hroot : (W.ΨSq ((m : ℤ) + 1)).eval x = 0) :
    (m + 1) • (Point.some x y h : W.toAffine.Point) = 0 := by

  have hpoly := W.X_mul_ΨSq_sub_Φ_sq (m : ℤ)
  have hev := congrArg (Polynomial.eval x) hpoly
  simp only [eval_pow, eval_sub, eval_mul, eval_X] at hev

  have hsq : (x * (W.ΨSq (m : ℤ)).eval x - (W.Φ (m : ℤ)).eval x) ^ 2 = 0 := by
    rw [hev, hroot, zero_mul]
  have hxΦ : x * (W.ΨSq (m : ℤ)).eval x = (W.Φ (m : ℤ)).eval x :=
    sub_eq_zero.mp (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hsq)

  have hmPne : (m • (Point.some x y h : W.toAffine.Point)) ≠ 0 :=
    hfree m (by omega) le_rfl
  obtain ⟨xm, ym, hm', hmPeq⟩ : ∃ (xm ym : F) (hm' : W.toAffine.Nonsingular xm ym),
      (m • (Point.some x y h : W.toAffine.Point)) = Point.some xm ym hm' := by
    cases hmP : (m • (Point.some x y h : W.toAffine.Point)) with
    | zero => exact absurd hmP hmPne
    | @some xm ym hm' => exact ⟨xm, ym, hm', rfl⟩

  have hxm : xm = x := by
    have h2 := hmf.2
    rw [hmPeq, Point.xOrZero_some] at h2
    exact mul_right_cancel₀ hmf.1 (h2.trans hxΦ.symm)

  rcases Y_eq_of_X_eq hm'.left h.left hxm with hyy | hyy
  ·
    exfalso
    have hmP_P : (m • (Point.some x y h : W.toAffine.Point)) = Point.some x y h := by
      rw [hmPeq]
      subst hxm; subst hyy
      exact congrArg _ (Subsingleton.elim _ _)
    have hsucc : ((m - 1) + 1) • (Point.some x y h : W.toAffine.Point) =
        (m - 1) • (Point.some x y h : W.toAffine.Point) + Point.some x y h :=
      succ_nsmul _ _
    rw [show m - 1 + 1 = m by omega] at hsucc
    have hcontra : (m - 1) • (Point.some x y h : W.toAffine.Point) + Point.some x y h =
        0 + Point.some x y h := by
      rw [zero_add, ← hsucc, hmP_P]
    exact hfree (m - 1) (by omega) (by omega) (add_right_cancel hcontra)
  ·
    have hmPneg : (m • (Point.some x y h : W.toAffine.Point)) =
        -(Point.some x y h : W.toAffine.Point) := by
      rw [hmPeq, Point.neg_some]
      subst hxm; subst hyy
      exact congrArg _ (Subsingleton.elim _ _)
    calc (m + 1) • (Point.some x y h : W.toAffine.Point)
        = m • (Point.some x y h : W.toAffine.Point) + Point.some x y h := succ_nsmul _ _
      _ = -(Point.some x y h : W.toAffine.Point) + Point.some x y h := by rw [hmPneg]
      _ = 0 := neg_add_cancel _

end RootToTorsion

section TorsionToRoot

theorem ΨSq_eval_eq_zero_or_of_succ_nsmul_eq_zero {m : ℕ} {x y : F}
    (h : W.toAffine.Nonsingular x y) (hmf : MFred m h)
    (hkill : (m + 1) • (Point.some x y h : W.toAffine.Point) = 0) :
    (W.ΨSq ((m : ℤ) + 1)).eval x = 0 ∨ (W.ΨSq ((m : ℤ) - 1)).eval x = 0 := by

  have hmPneg : (m • (Point.some x y h : W.toAffine.Point)) =
      -(Point.some x y h : W.toAffine.Point) := by
    have hsucc : (m + 1) • (Point.some x y h : W.toAffine.Point) =
        m • (Point.some x y h : W.toAffine.Point) + Point.some x y h := succ_nsmul _ _
    rw [hsucc] at hkill
    exact eq_neg_of_add_eq_zero_left hkill

  have hxΦ : x * (W.ΨSq (m : ℤ)).eval x = (W.Φ (m : ℤ)).eval x := by
    have h2 := hmf.2
    rw [hmPneg, Point.neg_some, Point.xOrZero_some] at h2
    exact h2

  have hpoly := W.X_mul_ΨSq_sub_Φ_sq (m : ℤ)
  have hev := congrArg (Polynomial.eval x) hpoly
  simp only [eval_pow, eval_sub, eval_mul, eval_X] at hev
  have hprod : (W.ΨSq ((m : ℤ) + 1)).eval x * (W.ΨSq ((m : ℤ) - 1)).eval x = 0 := by
    rw [← hev, sub_eq_zero_of_eq hxΦ]
    ring
  exact mul_eq_zero.mp hprod

theorem ΨSq_eval_eq_zero_of_succ_nsmul_eq_zero {m : ℕ} (hm : 4 ≤ m) {x y : F}
    (h : W.toAffine.Nonsingular x y) (hfree : LowTorsionFree m h)
    (hmf : MFred m h) (hmf' : MFred (m - 2) h)
    (hkill : (m + 1) • (Point.some x y h : W.toAffine.Point) = 0) :
    (W.ΨSq ((m : ℤ) + 1)).eval x = 0 := by
  rcases ΨSq_eval_eq_zero_or_of_succ_nsmul_eq_zero h hmf hkill with hgood | hbad
  · exact hgood
  ·
    exfalso
    have hbad' : (W.ΨSq (((m - 2 : ℕ) : ℤ) + 1)).eval x = 0 := by
      rw [show (((m - 2 : ℕ) : ℤ) + 1) = (m : ℤ) - 1 by omega]
      exact hbad
    have hzero := nsmul_succ_eq_zero_of_ΨSq_eval_eq_zero (m := m - 2) (by omega) h
      (hfree.mono (by omega)) hmf' hbad'
    rw [show m - 2 + 1 = m - 1 by omega] at hzero
    exact hfree (m - 1) (by omega) (by omega) hzero

theorem succ_nsmul_eq_zero_iff_ΨSq_eval_eq_zero {m : ℕ} (hm : 4 ≤ m) {x y : F}
    (h : W.toAffine.Nonsingular x y) (hfree : LowTorsionFree m h)
    (hmf : MFred m h) (hmf' : MFred (m - 2) h) :
    (m + 1) • (Point.some x y h : W.toAffine.Point) = 0 ↔
      (W.ΨSq ((m : ℤ) + 1)).eval x = 0 :=
  ⟨ΨSq_eval_eq_zero_of_succ_nsmul_eq_zero hm h hfree hmf hmf',
    nsmul_succ_eq_zero_of_ΨSq_eval_eq_zero (by omega) h hfree hmf⟩

end TorsionToRoot

section StarForm

theorem nsmul_eq_zero_of_ΨSq_eval_eq_zero_of_starIdentity {n : ℕ} (hn : 3 ≤ n) {x y : F}
    (h : W.toAffine.Nonsingular x y) (hfree : LowTorsionFree (n - 1) h)
    (hstar : ∀ j : ℤ, 2 ≤ j → j + 2 ≤ (n : ℤ) → W.StarIdentity j)
    (hroot : (W.ΨSq (n : ℤ)).eval x = 0) :
    n • (Point.some x y h : W.toAffine.Point) = 0 := by

  have hmf : MFred (n - 1) h := by
    refine mfred_of_forall_starIdentity (n - 1) h hfree
      (fun j hj2 hjM => hstar j hj2 (by omega)) (n - 1) (by omega) le_rfl

  have hroot' : (W.ΨSq (((n - 1 : ℕ) : ℤ) + 1)).eval x = 0 := by
    rw [show (((n - 1 : ℕ) : ℤ) + 1) = (n : ℤ) by omega]
    exact hroot
  have hzero := nsmul_succ_eq_zero_of_ΨSq_eval_eq_zero (m := n - 1) (by omega) h hfree hmf hroot'
  rwa [show n - 1 + 1 = n by omega] at hzero

theorem nsmul_six_eq_zero_of_ΨSq_eval_eq_zero {x y : F}
    (h : W.toAffine.Nonsingular x y) (hfree : LowTorsionFree 5 h)
    (hroot : (W.ΨSq (6 : ℤ)).eval x = 0) :
    6 • (Point.some x y h : W.toAffine.Point) = 0 := by
  have h6 := nsmul_eq_zero_of_ΨSq_eval_eq_zero_of_starIdentity (n := 6) (by norm_num) h
    (by simpa using hfree)
    (fun j hj2 hj6 => W.starIdentity_of_le_four j (by omega) (by omega))
    (by exact_mod_cast hroot)
  simpa using h6

end StarForm

end WeierstrassCurve.Affine


