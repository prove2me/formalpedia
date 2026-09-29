-- Prove2me | Definitions.Def_NumberField_NormPowChar
-- name    : NumberField_NormPowChar
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/e4f6bd78-bb7a-5af6-a27c-3ca55a167d57
-- title:
--   Unitary norm-power characters of the idele group
-- statement:
--   Throughout, $F$ is a number field. The module's main definition is [`NumberField.TateGlobal.normPowChar`](../def/NumberField_NormPowChar.html#L22): for a real number $t$ it is the monoid homomorphism from the unit group of the adele ring $\mathbb{A}_F$ of $F$ (Lean: `(AdeleRing (𝓞 F) F)ˣ`) to $\mathbb{C}^\times$ sending an idele $x$ to the principal complex power $(\|x\|)^{i t}$, where $\|x\|$ is $\mathrm{ideleNorm}\ F\ x$ — by definition the real number underlying the value at $x$ of Mathlib's `distribHaarChar` for the scaling action on $\mathbb{A}_F$, that is, the modulus by which multiplication by $x$ scales an additive Haar measure on the adele ring. The value is packaged as a unit of $\mathbb{C}$, which requires the non-vanishing lemma `ofReal_ideleNorm_cpow_ne_zero`: since $\|x\|>0$, the power $(\|x\|)^{s}$ is non-zero for every $s \in \mathbb{C}$. That the assignment is multiplicative rests on multiplicativity of `ideleNorm` together with positivity of the two factors, and that it sends $1$ to $1$ on `ideleNorm_one`, the statement $\|1\|=1$, obtained here from multiplicativity and positivity of the modulus.
--
--   The remaining declarations record the elementary properties of this character: the underlying complex number of `normPowChar F t x` is exactly $(\|x\|)^{i t}$; its absolute value is $1$, so the character is unitary; for $t=0$ it is the trivial homomorphism; and it takes the value $1$ at every idele of norm one, hence is trivial on the subgroup `normOneIdeles F`, the kernel of the modulus character. Continuity is not asserted, and only the purely imaginary exponents $s=it$ are treated, not general complex powers $\|\cdot\|^{s}$.
--
--   **Relation to Mathlib.** The modulus itself is Mathlib's `distribHaarChar` for the multiplicative action on the adele ring; `ideleNorm` is the project's real-valued repackaging of it, and the norm-power character assembled from it is the project's own.
--
--   **Where it is used.** The norm-power characters are the unitary twists $\|\cdot\|^{it}$ available to insert as the character argument of the project's Tate global zeta integral `zetaIntegral`, and they are the archimedean part of the description of characters of the idele class group; they feed the adelic and automorphic side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_NormPowChar.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open Complex

namespace NumberField.TateGlobal

variable (F : Type) [Field F] [NumberField F]

theorem ideleNorm_one : ideleNorm F 1 = 1 := by
  have h := ideleNorm_mul (1 : (AdeleRing (𝓞 F) F)ˣ) 1
  rw [mul_one] at h
  exact (mul_eq_left₀ (ideleNorm_pos (1 : (AdeleRing (𝓞 F) F)ˣ)).ne').mp h.symm

theorem ofReal_ideleNorm_cpow_ne_zero (x : (AdeleRing (𝓞 F) F)ˣ) (s : ℂ) :
    ((ideleNorm F x : ℝ) : ℂ) ^ s ≠ 0 := fun h =>
  (ideleNorm_pos x).ne' (ofReal_eq_zero.mp ((cpow_eq_zero_iff _ _).mp h).1)

def normPowChar (t : ℝ) : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ where
  toFun x := Units.mk0 (((ideleNorm F x : ℝ) : ℂ) ^ (I * t)) (ofReal_ideleNorm_cpow_ne_zero F x _)
  map_one' := Units.ext (by rw [Units.val_mk0, ideleNorm_one, ofReal_one, one_cpow, Units.val_one])
  map_mul' x y := Units.ext (by
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, ideleNorm_mul, ofReal_mul,
      mul_cpow_ofReal_nonneg (ideleNorm_pos x).le (ideleNorm_pos y).le])

variable {F}

theorem coe_normPowChar_apply (t : ℝ) (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((normPowChar F t x : ℂˣ) : ℂ) = ((ideleNorm F x : ℝ) : ℂ) ^ (I * t) := rfl

theorem norm_coe_normPowChar_apply (t : ℝ) (x : (AdeleRing (𝓞 F) F)ˣ) : ‖((normPowChar F t x : ℂˣ) : ℂ)‖ = 1 := by
  rw [coe_normPowChar_apply, norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos x), mul_re, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, one_mul, sub_zero, Real.rpow_zero]

theorem normPowChar_zero : normPowChar F 0 = 1 := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [coe_normPowChar_apply, ofReal_zero, mul_zero, cpow_zero, MonoidHom.one_apply, Units.val_one]

theorem normPowChar_eq_one_of_ideleNorm_eq_one (t : ℝ) {x : (AdeleRing (𝓞 F) F)ˣ} (hx : ideleNorm F x = 1) :
    normPowChar F t x = 1 :=
  Units.ext (by rw [coe_normPowChar_apply, hx, ofReal_one, one_cpow, Units.val_one])

end NumberField.TateGlobal

end


