-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexReciprocalCalculus
-- name    : liuyao_ca_fd889115_k1_Analysis_ComplexReciprocalCalculus
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:59:18.421429+00:00
-- url     : https://prove2.me/theorems/d43b27ad-d80d-4919-9b8d-bc22214a6cdf
-- title:
--   Computable analysis · ComplexReciprocalCalculus · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ComplexReciprocalCalculus.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexPowerCalculus

set_option autoImplicit true

/-!
# Quantitative rational-complex reciprocal calculus

All estimates are finite rational identities.  A positive lower bound on
`normSq` supplies both the inverse norm bound and a Lipschitz modulus for the
complex reciprocal map.
-/

namespace ComputableAnalysis

namespace Rat

theorem inv_antitone_of_pos {a b : Rat} (ha : 0 < a) (hab : a <= b) :
    b⁻¹ <= a⁻¹ := by
  have hb : 0 < b := by grind
  have habpos : 0 < a * b := Rat.mul_pos ha hb
  apply Rat.le_of_mul_le_mul_left (c := a * b) ?_ habpos
  have ha0 : a ≠ 0 := Rat.ne_of_gt ha
  have hb0 : b ≠ 0 := Rat.ne_of_gt hb
  calc
    a * b * b⁻¹ = a := by
      rw [Rat.mul_assoc, Rat.mul_inv_cancel b hb0, Rat.mul_one]
    _ <= b := hab
    _ = a * b * a⁻¹ := by
      rw [Rat.mul_comm a b, Rat.mul_assoc,
        Rat.mul_inv_cancel a ha0, Rat.mul_one]

end Rat

namespace QComplex

theorem normBound_inverse_eq (z : QComplex)
    (hnorm : 0 < normSq z) :
    normBound (inverse z) = normBound z * (normSq z)⁻¹ := by
  have hinv : 0 <= (normSq z)⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hnorm)
  unfold inverse normBound
  simp only [Rat.div_def, qabs_mul, qabs_neg,
    qabs_eq_self_of_nonneg hinv]
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem inverse_normBound_le
    {z : QComplex} {C margin : Rat}
    (hC : 0 <= C) (hmargin : 0 < margin)
    (hz : normBound z <= C) (hsep : margin <= normSq z) :
    normBound (inverse z) <= C * margin⁻¹ := by
  have hnorm : 0 < normSq z := by grind
  have hinv0 : 0 <= (normSq z)⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hnorm)
  have hantitone := Rat.inv_antitone_of_pos hmargin hsep
  rw [normBound_inverse_eq z hnorm]
  exact Rat.le_trans
    (Rat.mul_le_mul_of_nonneg_right hz hinv0)
    (Rat.mul_le_mul_of_nonneg_left hantitone hC)

/-- Exact reciprocal-difference identity
`z⁻¹ - w⁻¹ = z⁻¹ (w-z) w⁻¹`. -/
theorem inverse_sub_inverse
    (z w : QComplex) (hz : normSq z ≠ 0) (hw : normSq w ≠ 0) :
    sub (inverse z) (inverse w) =
      mul (mul (inverse z) (sub w z)) (inverse w) := by
  have hzinv := mul_inverse_of_normSq_ne_zero z hz
  have hwinv := mul_inverse_of_normSq_ne_zero w hw
  have hiz : mul (inverse z) z = one := by
    rw [mul_comm_cert]
    exact hzinv
  unfold sub
  rw [mul_add_cert, add_mul_cert, mul_neg_cert, neg_mul_cert]
  have hfirst :
      mul (mul (inverse z) w) (inverse w) = inverse z := by
    rw [mul_assoc_cert, hwinv, mul_one_cert]
  have hsecond :
      neg (mul (mul (inverse z) z) (inverse w)) =
        neg (inverse w) := by
    rw [hiz, one_mul_cert]
  rw [hfirst, hsecond]

theorem inverse_difference_normBound_le
    {z w : QComplex} {C margin : Rat}
    (hC : 0 <= C) (hmargin : 0 < margin)
    (hzC : normBound z <= C) (hwC : normBound w <= C)
    (hzsep : margin <= normSq z) (hwsep : margin <= normSq w) :
    normBound (sub (inverse z) (inverse w)) <=
      (C * margin⁻¹) ^ 2 * normBound (sub z w) := by
  have hznorm : 0 < normSq z := by grind
  have hwnorm : 0 < normSq w := by grind
  have hzinv := inverse_normBound_le hC hmargin hzC hzsep
  have hwinv := inverse_normBound_le hC hmargin hwC hwsep
  have hbound0 : 0 <= C * margin⁻¹ :=
    Rat.mul_nonneg hC (Rat.le_of_lt ((Rat.inv_pos).2 hmargin))
  rw [inverse_sub_inverse z w (Rat.ne_of_gt hznorm) (Rat.ne_of_gt hwnorm)]
  have hsub : sub w z = neg (sub z w) := by
    cases z
    cases w
    simp [sub, add, neg]
    congr 1 <;> grind [Rat.sub_eq_add_neg]
  have hdist : normBound (sub w z) = normBound (sub z w) := by
    rw [hsub, normBound_neg]
  calc
    normBound (mul (mul (inverse z) (sub w z)) (inverse w)) <=
        normBound (mul (inverse z) (sub w z)) *
          normBound (inverse w) := normBound_mul_le _ _
    _ <= (normBound (inverse z) * normBound (sub w z)) *
          normBound (inverse w) :=
      Rat.mul_le_mul_of_nonneg_right (normBound_mul_le _ _)
        (normBound_nonneg _)
    _ <= ((C * margin⁻¹) * normBound (sub w z)) *
          normBound (inverse w) :=
      Rat.mul_le_mul_of_nonneg_right
        (Rat.mul_le_mul_of_nonneg_right hzinv (normBound_nonneg _))
        (normBound_nonneg _)
    _ <= ((C * margin⁻¹) * normBound (sub w z)) *
          (C * margin⁻¹) :=
      Rat.mul_le_mul_of_nonneg_left hwinv
        (Rat.mul_nonneg hbound0 (normBound_nonneg _))
    _ = (C * margin⁻¹) ^ 2 * normBound (sub z w) := by
      rw [hdist]
      simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
      grind [Rat.mul_assoc, Rat.mul_comm]

end QComplex
end ComputableAnalysis


