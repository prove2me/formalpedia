-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RationalCircleDifferences
-- name    : liuyao_ca_fd889115_k1_Analysis_RationalCircleDifferences
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:02:16.538333+00:00
-- url     : https://prove2.me/theorems/14a4a6b3-7eeb-4b4f-8573-8233f7dbd77d
-- title:
--   Computable analysis · RationalCircleDifferences · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/RationalCircleDifferences.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RationalCircle

set_option autoImplicit true

/-! Rational circle differences, isolated from complex rotation theory.
These finite algebraic estimates are extracted from GeometricRotationODE;
no complex number or exponential theorem occurs in their proofs. -/
namespace ComputableAnalysis.RationalCircleDifferences
set_option maxHeartbeats 2000000

def pointRe (t : Rat) : Rat := (RationalCircle.Stage.point t).x
def pointIm (t : Rat) : Rat := (RationalCircle.Stage.point t).y
def pointReDerivative (t : Rat) : Rat := (RationalCircle.Stage.pointDerivative t).x
def pointImDerivative (t : Rat) : Rat := (RationalCircle.Stage.pointDerivative t).y

private theorem rat_eq_of_right_mul_eq_mul_ne {a b c : Rat}
    (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  calc
    a = (a * c) * c⁻¹ := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (b * c) * c⁻¹ := by rw [h]
    _ = b := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem pointRe_differenceQuotient (t h : Rat) (hh : h ≠ 0) :
    (pointRe (t + h) - pointRe t) / h =
      (-2 * (2 * t + h)) /
        ((1 + t * t) * (1 + (t + h) * (t + h))) := by
  let d := 1 + t * t
  let e := 1 + (t + h) * (t + h)
  have hdpos : 0 < d := by
    dsimp [d]
    exact RationalCircle.Stage.one_add_square_pos t
  have hepos : 0 < e := by
    dsimp [e]
    exact RationalCircle.Stage.one_add_square_pos (t + h)
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  have hene : e ≠ 0 := Rat.ne_of_gt hepos
  have hprod : h * d * e ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hh hzero
      · exact hdne hzero
    · exact hene hzero
  apply rat_eq_of_right_mul_eq_mul_ne hprod
  unfold pointRe RationalCircle.Stage.point
  change (((1 - (t + h) * (t + h)) / e - (1 - t * t) / d) / h) *
      (h * d * e) = ((-2 * (2 * t + h)) / (d * e)) * (h * d * e)
  rw [Rat.div_def]
  have hcancelH : h⁻¹ * h = 1 := Rat.inv_mul_cancel h hh
  have hcancelD : d⁻¹ * d = 1 := Rat.inv_mul_cancel d hdne
  have hcancelE : e⁻¹ * e = 1 := Rat.inv_mul_cancel e hene
  have hcancelDE : (d * e)⁻¹ * (d * e) = 1 :=
    Rat.inv_mul_cancel (d * e) (by
      intro hzero
      rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdne hzero
      · exact hene hzero)
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- Exact finite quotient for the chart's imaginary coordinate. -/
theorem pointIm_differenceQuotient (t h : Rat) (hh : h ≠ 0) :
    (pointIm (t + h) - pointIm t) / h =
      (2 * (1 - t * t - t * h)) /
        ((1 + t * t) * (1 + (t + h) * (t + h))) := by
  let d := 1 + t * t
  let e := 1 + (t + h) * (t + h)
  have hdpos : 0 < d := by
    dsimp [d]
    exact RationalCircle.Stage.one_add_square_pos t
  have hepos : 0 < e := by
    dsimp [e]
    exact RationalCircle.Stage.one_add_square_pos (t + h)
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  have hene : e ≠ 0 := Rat.ne_of_gt hepos
  have hprod : h * d * e ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hh hzero
      · exact hdne hzero
    · exact hene hzero
  apply rat_eq_of_right_mul_eq_mul_ne hprod
  unfold pointIm RationalCircle.Stage.point
  change (((2 * (t + h)) / e - (2 * t) / d) / h) * (h * d * e) =
      ((2 * (1 - t * t - t * h)) / (d * e)) * (h * d * e)
  rw [Rat.div_def]
  have hcancelH : h⁻¹ * h = 1 := Rat.inv_mul_cancel h hh
  have hcancelD : d⁻¹ * d = 1 := Rat.inv_mul_cancel d hdne
  have hcancelE : e⁻¹ * e = 1 := Rat.inv_mul_cancel e hene
  have hcancelDE : (d * e)⁻¹ * (d * e) = 1 :=
    Rat.inv_mul_cancel (d * e) (by
      intro hzero
      rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdne hzero
      · exact hene hzero)
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- Exact real-coordinate secant error relative to the named rational
velocity.  Its explicit factor of `h` is the starting point for a quantitative
derivative modulus. -/
theorem pointRe_differenceQuotient_sub_derivative (t h : Rat) (hh : h ≠ 0) :
    (pointRe (t + h) - pointRe t) / h - pointReDerivative t =
      (2 * h * (-1 + 3 * t * t + 2 * t * h)) /
        ((1 + t * t) * (1 + t * t) * (1 + (t + h) * (t + h))) := by
  rw [pointRe_differenceQuotient t h hh]
  let d := 1 + t * t
  let e := 1 + (t + h) * (t + h)
  have hdpos : 0 < d := by
    dsimp [d]
    exact RationalCircle.Stage.one_add_square_pos t
  have hepos : 0 < e := by
    dsimp [e]
    exact RationalCircle.Stage.one_add_square_pos (t + h)
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  have hene : e ≠ 0 := Rat.ne_of_gt hepos
  have hprod : d * d * e ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdne hzero
      · exact hdne hzero
    · exact hene hzero
  apply rat_eq_of_right_mul_eq_mul_ne hprod
  unfold pointReDerivative RationalCircle.Stage.pointDerivative
  dsimp
  change (((-2 * (2 * t + h)) / (d * e) - (-4 * t) / (d * d))) *
      (d * d * e) =
    ((2 * h * (-1 + 3 * t * t + 2 * t * h)) / (d * d * e)) *
      (d * d * e)
  rw [Rat.div_def]
  simp only [Rat.inv_mul_rev]
  have hcancelD : d⁻¹ * d = 1 := Rat.inv_mul_cancel d hdne
  have hcancelE : e⁻¹ * e = 1 := Rat.inv_mul_cancel e hene
  have hcancelDD : (d * d)⁻¹ * (d * d) = 1 :=
    Rat.inv_mul_cancel (d * d) (by
      intro hzero
      rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdne hzero
      · exact hdne hzero)
  have hcancelDDE : (d * d * e)⁻¹ * (d * d * e) = 1 :=
    Rat.inv_mul_cancel (d * d * e) hprod
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.neg_mul, Rat.mul_neg]

/-- Exact imaginary-coordinate secant error relative to the named rational
velocity. -/
theorem pointIm_differenceQuotient_sub_derivative (t h : Rat) (hh : h ≠ 0) :
    (pointIm (t + h) - pointIm t) / h - pointImDerivative t =
      (-2 * h * (t * (3 - t * t) + h * (1 - t * t))) /
        ((1 + t * t) * (1 + t * t) * (1 + (t + h) * (t + h))) := by
  rw [pointIm_differenceQuotient t h hh]
  let d := 1 + t * t
  let e := 1 + (t + h) * (t + h)
  have hdpos : 0 < d := by
    dsimp [d]
    exact RationalCircle.Stage.one_add_square_pos t
  have hepos : 0 < e := by
    dsimp [e]
    exact RationalCircle.Stage.one_add_square_pos (t + h)
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  have hene : e ≠ 0 := Rat.ne_of_gt hepos
  have hprod : d * d * e ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdne hzero
      · exact hdne hzero
    · exact hene hzero
  apply rat_eq_of_right_mul_eq_mul_ne hprod
  unfold pointImDerivative RationalCircle.Stage.pointDerivative
  dsimp
  change (((2 * (1 - t * t - t * h)) / (d * e) -
      (2 * (1 - t * t)) / (d * d))) * (d * d * e) =
    ((-2 * h * (t * (3 - t * t) + h * (1 - t * t))) /
      (d * d * e)) * (d * d * e)
  rw [Rat.div_def]
  simp only [Rat.inv_mul_rev]
  have hcancelD : d⁻¹ * d = 1 := Rat.inv_mul_cancel d hdne
  have hcancelE : e⁻¹ * e = 1 := Rat.inv_mul_cancel e hene
  have hcancelDD : (d * d)⁻¹ * (d * d) = 1 :=
    Rat.inv_mul_cancel (d * d) (by
      intro hzero
      rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdne hzero
      · exact hdne hzero)
  have hcancelDDE : (d * d * e)⁻¹ * (d * d * e) = 1 :=
    Rat.inv_mul_cancel (d * d * e) hprod
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.neg_mul, Rat.mul_neg]

private theorem qabs_factors_le_one {u v : Rat}
    (hu : qabs u <= 1) (hv : qabs v <= 1) :
    qabs u * qabs v <= 1 := by
  calc
    qabs u * qabs v <= 1 * qabs v :=
      Rat.mul_le_mul_of_nonneg_right hu (qabs_nonneg v)
    _ <= 1 * 1 := Rat.mul_le_mul_of_nonneg_left hv (by decide +kernel)
    _ = 1 := by decide +kernel

private theorem qabs_step_le_one {t h : Rat}
    (ht0 : 0 <= t) (ht1 : t <= 1)
    (hth0 : 0 <= t + h) (hth1 : t + h <= 1) :
    qabs h <= 1 := by
  apply qabs_le_of_neg_le_le
  · have : 0 <= t + h := hth0
    grind [Rat.sub_eq_add_neg]
  · have : t + h <= 1 := hth1
    grind [Rat.sub_eq_add_neg]

private theorem qabs_unit_le_one {t : Rat} (ht0 : 0 <= t) (ht1 : t <= 1) :
    qabs t <= 1 := by
  rw [qabs_eq_self_of_nonneg ht0]
  exact ht1

private theorem one_le_one_add_square (u : Rat) : 1 <= 1 + u * u := by
  have hsquare : 0 <= u * u := RationalCircle.Stage.ratSquare_nonneg u
  grind

private theorem one_le_mul_of_one_le {a b : Rat}
    (ha : 1 <= a) (hb : 1 <= b) : 1 <= a * b := by
  calc
    1 = 1 * 1 := by decide +kernel
    _ <= a * 1 := Rat.mul_le_mul_of_nonneg_right ha (by decide +kernel)
    _ <= a * b := Rat.mul_le_mul_of_nonneg_left hb (by grind)

private theorem one_div_le_one_of_one_le {d : Rat} (hd : 1 <= d) :
    1 / d <= 1 := by
  have hdpos : 0 < d := by grind
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  apply Rat.le_of_mul_le_mul_right (c := d)
  · calc
      (1 / d) * d = 1 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= d := hd
      _ = 1 * d := by grind
  · exact hdpos

private theorem chart_denominator_inv_abs_le_one (t h : Rat) :
    qabs
      (((1 + t * t) * (1 + t * t) *
        (1 + (t + h) * (t + h)))⁻¹) <= 1 := by
  let d := 1 + t * t
  let e := 1 + (t + h) * (t + h)
  have hd : 1 <= d := by
    dsimp [d]
    exact one_le_one_add_square t
  have he : 1 <= e := by
    dsimp [e]
    exact one_le_one_add_square (t + h)
  have hde : 1 <= d * d * e :=
    one_le_mul_of_one_le (one_le_mul_of_one_le hd hd) he
  have hpos : 0 < d * d * e := by grind
  rw [qabs_eq_self_of_nonneg (Rat.le_of_lt ((Rat.inv_pos).2 hpos))]
  have hinv : 1 / (d * d * e) <= 1 := one_div_le_one_of_one_le hde
  simpa [d, e, Rat.div_def] using hinv

private theorem qabs_re_secant_coefficient_le_six {t h : Rat}
    (ht : qabs t <= 1) (hh : qabs h <= 1) :
    qabs (-1 + 3 * t * t + 2 * t * h) <= 6 := by
  have htt : qabs t * qabs t <= 1 := qabs_factors_le_one ht ht
  have hth : qabs t * qabs h <= 1 := qabs_factors_le_one ht hh
  have hthree : qabs (3 : Rat) = 3 := by decide +kernel
  have htwo : qabs (2 : Rat) = 2 := by decide +kernel
  have hnegone : qabs (-1 : Rat) = 1 := by decide +kernel
  have h3tt : qabs (3 * t * t) <= 3 := by
    rw [qabs_mul, qabs_mul, hthree]
    calc
      3 * qabs t * qabs t = 3 * (qabs t * qabs t) := by
        grind [Rat.mul_assoc]
      _ <= 3 * 1 := Rat.mul_le_mul_of_nonneg_left htt (by decide +kernel)
      _ = 3 := by decide +kernel
  have h2th : qabs (2 * t * h) <= 2 := by
    rw [qabs_mul, qabs_mul, htwo]
    calc
      2 * qabs t * qabs h = 2 * (qabs t * qabs h) := by
        grind [Rat.mul_assoc]
      _ <= 2 * 1 := Rat.mul_le_mul_of_nonneg_left hth (by decide +kernel)
      _ = 2 := by decide +kernel
  calc
    qabs (-1 + 3 * t * t + 2 * t * h) =
        qabs ((-1) + (3 * t * t + 2 * t * h)) := by
          congr 1
          grind [Rat.add_assoc]
    _ <= qabs (-1) + qabs (3 * t * t + 2 * t * h) := qabs_add_le _ _
    _ <= 1 + (qabs (3 * t * t) + qabs (2 * t * h)) := by
      rw [hnegone]
      exact (Rat.add_le_add_left).2 (qabs_add_le _ _)
    _ <= 1 + (3 + 2) := (Rat.add_le_add_left).2
      (rat_add_le_add h3tt h2th)
    _ = 6 := by decide +kernel

private theorem qabs_im_secant_coefficient_le_six {t h : Rat}
    (ht : qabs t <= 1) (hh : qabs h <= 1) :
    qabs (t * (3 - t * t) + h * (1 - t * t)) <= 6 := by
  have htt : qabs t * qabs t <= 1 := qabs_factors_le_one ht ht
  have hthree : qabs (3 : Rat) = 3 := by decide +kernel
  have hone : qabs (1 : Rat) = 1 := by decide +kernel
  have h3sub : qabs (3 - t * t) <= 4 := by
    calc
      qabs (3 - t * t) <= qabs 3 + qabs (t * t) := qabs_sub_le _ _
      _ = 3 + (qabs t * qabs t) := by rw [qabs_mul, hthree]
      _ <= 3 + 1 := (Rat.add_le_add_left).2 htt
      _ = 4 := by decide +kernel
  have h1sub : qabs (1 - t * t) <= 2 := by
    calc
      qabs (1 - t * t) <= qabs 1 + qabs (t * t) := qabs_sub_le _ _
      _ = 1 + (qabs t * qabs t) := by rw [qabs_mul, hone]
      _ <= 1 + 1 := (Rat.add_le_add_left).2 htt
      _ = 2 := by decide +kernel
  have hleft : qabs (t * (3 - t * t)) <= 4 := by
    rw [qabs_mul]
    calc
      qabs t * qabs (3 - t * t) <= 1 * qabs (3 - t * t) :=
        Rat.mul_le_mul_of_nonneg_right ht (qabs_nonneg _)
      _ <= 1 * 4 := Rat.mul_le_mul_of_nonneg_left h3sub (by decide +kernel)
      _ = 4 := by decide +kernel
  have hright : qabs (h * (1 - t * t)) <= 2 := by
    rw [qabs_mul]
    calc
      qabs h * qabs (1 - t * t) <= 1 * qabs (1 - t * t) :=
        Rat.mul_le_mul_of_nonneg_right hh (qabs_nonneg _)
      _ <= 1 * 2 := Rat.mul_le_mul_of_nonneg_left h1sub (by decide +kernel)
      _ = 2 := by decide +kernel
  calc
    qabs (t * (3 - t * t) + h * (1 - t * t)) <=
        qabs (t * (3 - t * t)) + qabs (h * (1 - t * t)) := qabs_add_le _ _
    _ <= 4 + 2 := rat_add_le_add hleft hright
    _ = 6 := by decide +kernel

/-- Uniform finite real-coordinate secant estimate on the unit chart. -/
theorem pointRe_secant_error_le_twelve {t h : Rat}
    (ht0 : 0 <= t) (ht1 : t <= 1)
    (hth0 : 0 <= t + h) (hth1 : t + h <= 1) (hh : h ≠ 0) :
    qabs ((pointRe (t + h) - pointRe t) / h - pointReDerivative t) <=
      12 * qabs h := by
  rw [pointRe_differenceQuotient_sub_derivative t h hh, Rat.div_def, qabs_mul]
  have ht : qabs t <= 1 := qabs_unit_le_one ht0 ht1
  have hstep : qabs h <= 1 := qabs_step_le_one ht0 ht1 hth0 hth1
  have hcoefficient : qabs (-1 + 3 * t * t + 2 * t * h) <= 6 :=
    qabs_re_secant_coefficient_le_six ht hstep
  have htwo : qabs (2 : Rat) = 2 := by decide +kernel
  have hnumerator :
      qabs (2 * h * (-1 + 3 * t * t + 2 * t * h)) <= 12 * qabs h := by
    rw [qabs_mul, qabs_mul, htwo]
    calc
      2 * qabs h * qabs (-1 + 3 * t * t + 2 * t * h) =
          (2 * qabs h) * qabs (-1 + 3 * t * t + 2 * t * h) := by
            grind [Rat.mul_assoc]
      _ <= (2 * qabs h) * 6 :=
        Rat.mul_le_mul_of_nonneg_left hcoefficient
          (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg h))
      _ = 12 * qabs h := by grind [Rat.mul_assoc, Rat.mul_comm]
  have hden := chart_denominator_inv_abs_le_one t h
  calc
    qabs (2 * h * (-1 + 3 * t * t + 2 * t * h)) *
        qabs (((1 + t * t) * (1 + t * t) *
          (1 + (t + h) * (t + h)))⁻¹) <=
        (12 * qabs h) * qabs (((1 + t * t) * (1 + t * t) *
          (1 + (t + h) * (t + h)))⁻¹) :=
      Rat.mul_le_mul_of_nonneg_right hnumerator (qabs_nonneg _)
    _ <= (12 * qabs h) * 1 :=
      Rat.mul_le_mul_of_nonneg_left hden
        (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg h))
    _ = 12 * qabs h := by rw [Rat.mul_one]

/-- Uniform finite imaginary-coordinate secant estimate on the unit chart. -/
theorem pointIm_secant_error_le_twelve {t h : Rat}
    (ht0 : 0 <= t) (ht1 : t <= 1)
    (hth0 : 0 <= t + h) (hth1 : t + h <= 1) (hh : h ≠ 0) :
    qabs ((pointIm (t + h) - pointIm t) / h - pointImDerivative t) <=
      12 * qabs h := by
  rw [pointIm_differenceQuotient_sub_derivative t h hh, Rat.div_def, qabs_mul]
  have ht : qabs t <= 1 := qabs_unit_le_one ht0 ht1
  have hstep : qabs h <= 1 := qabs_step_le_one ht0 ht1 hth0 hth1
  have hcoefficient : qabs (t * (3 - t * t) + h * (1 - t * t)) <= 6 :=
    qabs_im_secant_coefficient_le_six ht hstep
  have htwo : qabs (-2 : Rat) = 2 := by decide +kernel
  have hnumerator :
      qabs (-2 * h * (t * (3 - t * t) + h * (1 - t * t))) <= 12 * qabs h := by
    rw [qabs_mul, qabs_mul, htwo]
    calc
      2 * qabs h * qabs (t * (3 - t * t) + h * (1 - t * t)) =
          (2 * qabs h) * qabs (t * (3 - t * t) + h * (1 - t * t)) := by
            grind [Rat.mul_assoc]
      _ <= (2 * qabs h) * 6 :=
        Rat.mul_le_mul_of_nonneg_left hcoefficient
          (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg h))
      _ = 12 * qabs h := by grind [Rat.mul_assoc, Rat.mul_comm]
  have hden := chart_denominator_inv_abs_le_one t h
  calc
    qabs (-2 * h * (t * (3 - t * t) + h * (1 - t * t))) *
        qabs (((1 + t * t) * (1 + t * t) *
          (1 + (t + h) * (t + h)))⁻¹) <=
        (12 * qabs h) * qabs (((1 + t * t) * (1 + t * t) *
          (1 + (t + h) * (t + h)))⁻¹) :=
      Rat.mul_le_mul_of_nonneg_right hnumerator (qabs_nonneg _)
    _ <= (12 * qabs h) * 1 :=
      Rat.mul_le_mul_of_nonneg_left hden
        (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg h))
    _ = 12 * qabs h := by rw [Rat.mul_one]


end ComputableAnalysis.RationalCircleDifferences


