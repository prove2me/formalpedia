-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteDerivativeLimit
-- name    : liuyao_ca_fd889115_k1_Analysis_FiniteDerivativeLimit
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:54:52.291706+00:00
-- url     : https://prove2.me/theorems/448ce048-3ff9-427d-b8d1-b635462a94f5
-- title:
--   Computable analysis · FiniteDerivativeLimit · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FiniteDerivativeLimit.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Differential

set_option autoImplicit true

/-!
# Finite-model passage to a represented derivative

This module supplies the completeness-free limit bridge needed by power
series and Gaussian derivatives.  At each requested precision and rational
step, a caller may choose three exact rational witnesses: approximations to
the two endpoint values and to the derivative value.  If those witnesses lie
inside the represented boxes, their exact secant error is small, and the two
runtime boxes are narrow, then the represented difference quotient is near
the represented derivative.

There is no quantification over arbitrary real test functions, no completed
function space, and no topological limit.  The schedules and all witnesses
are executable natural/rational data.
-/

namespace ComputableAnalysis

namespace QInterval

/-- Sign-complete width law for the interval scaling used by finite
difference quotients. -/
theorem scaleRat_width (r : Rat) (I : QInterval) :
    (scaleRat r I).width = qabs r * I.width := by
  by_cases hr : 0 <= r
  · unfold scaleRat QInterval.width
    rw [if_pos hr, qabs_eq_self_of_nonneg hr]
    grind [Rat.sub_eq_add_neg, Rat.mul_add]
  · have hrneg : r < 0 := Rat.not_le.mp hr
    unfold scaleRat QInterval.width
    rw [if_neg hr, qabs_eq_neg_of_nonpos (Rat.le_of_lt hrneg)]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]

/-- Rational interval scaling contains the correspondingly scaled value,
with the negative-sign endpoint reversal handled explicitly. -/
theorem scaleRat_mem {I : QInterval} {x r : Rat}
    (hx : I.lo <= x /\ x <= I.hi) :
    (scaleRat r I).lo <= r * x /\ r * x <= (scaleRat r I).hi := by
  by_cases hr : 0 <= r
  · unfold scaleRat
    rw [if_pos hr]
    exact
      ⟨Rat.mul_le_mul_of_nonneg_left hx.1 hr,
        Rat.mul_le_mul_of_nonneg_left hx.2 hr⟩
  · have hrnonpos : r <= 0 := Rat.le_of_lt (Rat.not_le.mp hr)
    unfold scaleRat
    rw [if_neg hr]
    exact
      ⟨rat_mul_le_mul_of_nonpos_left hx.2 hrnonpos,
        rat_mul_le_mul_of_nonpos_left hx.1 hrnonpos⟩

/-- Interval negation contains the negation of every contained value. -/
theorem neg_mem {I : QInterval} {x : Rat}
    (hx : I.lo <= x /\ x <= I.hi) :
    (neg I).lo <= -x /\ -x <= (neg I).hi := by
  unfold neg
  exact ⟨Rat.neg_le_neg hx.2, Rat.neg_le_neg hx.1⟩

/-- Interval negation preserves width exactly. -/
theorem neg_width (I : QInterval) : (neg I).width = I.width := by
  unfold neg QInterval.width
  grind [Rat.sub_eq_add_neg]

/-- The uncertainty of a represented difference quotient is the sum of the
two endpoint uncertainties, magnified by the absolute reciprocal step. -/
theorem differenceQuotient_width (A B : QInterval) (h : Rat) :
    (differenceQuotient B A h).width =
      qabs (1 / h) * (B.width + A.width) := by
  unfold differenceQuotient divRat
  rw [scaleRat_width, sub_width]

/-- Two rational witnesses inside two narrow boxes certify quantitative
nearness of the boxes when the witnesses themselves are close. -/
theorem nearAt_of_mem_mem_qabs_sub_le
    {I J : QInterval} {x y : Rat} {eps : QPos}
    (hx : I.lo <= x /\ x <= I.hi)
    (hy : J.lo <= y /\ y <= J.hi)
    (hxy : qabs (x - y) <= eps.val)
    (hIwidth : I.width <= eps.val)
    (hJwidth : J.width <= eps.val) :
    I.NearAt J eps := by
  have hforward : x - y <= eps.val :=
    Rat.le_trans (self_le_qabs (x - y)) hxy
  have hbackward : y - x <= eps.val := by
    have h := Rat.le_trans (self_le_qabs (y - x))
      (show qabs (y - x) <= eps.val by
        rw [show y - x = -(x - y) by grind [Rat.sub_eq_add_neg], qabs_neg]
        exact hxy)
    exact h
  unfold NearAt
  constructor
  · grind [Rat.sub_eq_add_neg]
  constructor
  · grind [Rat.sub_eq_add_neg]
  exact ⟨hIwidth, hJwidth⟩

/-- If exact rational endpoint witnesses lie inside two boxes, then their
exact rational secant lies inside the interval difference quotient. -/
theorem differenceQuotient_mem_of_mem
    {A B : QInterval} {a b h : Rat}
    (ha : A.lo <= a /\ a <= A.hi)
    (hb : B.lo <= b /\ b <= B.hi)
    (_hh : h ≠ 0) :
    (differenceQuotient B A h).lo <= (b - a) / h /\
      (b - a) / h <= (differenceQuotient B A h).hi := by
  have hsub :
      (sub B A).lo <= b - a /\ b - a <= (sub B A).hi := by
    unfold sub
    constructor <;> grind [Rat.sub_eq_add_neg]
  by_cases hinv : 0 <= 1 / h
  · unfold differenceQuotient divRat scaleRat
    rw [if_pos hinv]
    constructor
    · have := Rat.mul_le_mul_of_nonneg_left hsub.1 hinv
      simpa [Rat.div_def, Rat.mul_comm] using this
    · have := Rat.mul_le_mul_of_nonneg_left hsub.2 hinv
      simpa [Rat.div_def, Rat.mul_comm] using this
  · have hinvNonpos : 1 / h <= 0 := Rat.le_of_lt (Rat.not_le.mp hinv)
    unfold differenceQuotient divRat scaleRat
    rw [if_neg hinv]
    constructor
    · have := rat_mul_le_mul_of_nonpos_left hsub.2 hinvNonpos
      simpa [Rat.div_def, Rat.mul_comm] using this
    · have := rat_mul_le_mul_of_nonpos_left hsub.1 hinvNonpos
      simpa [Rat.div_def, Rat.mul_comm] using this

end QInterval

/-- Executable finite-model data sufficient to identify a represented
derivative on a rational interval.

The model may depend on the base point, step, and requested precision.  This
is essential for Taylor-prefix arguments: a smaller step can request a finer
prefix so endpoint representation errors remain small after division by the
step. -/
structure FiniteModelDerivativeOnInterval
    (f df : FunctionOnInterval) where
  same_lower : df.lower = f.lower
  same_upper : df.upper = f.upper
  stepPrecision : Nat -> Nat
  evalPrecision : Rat -> Rat -> Nat -> Nat
  baseValue : Rat -> Rat -> Nat -> Rat
  stepValue : Rat -> Rat -> Nat -> Rat
  derivativeValue : Rat -> Rat -> Nat -> Rat
  base_mem :
    forall x h n
      (hx : inDomainInterval f.lower f.upper x)
      (_hxh : inDomainInterval f.lower f.upper (x + h)),
      let I := f.compute x hx (evalPrecision x h n)
      I.lo <= baseValue x h n /\ baseValue x h n <= I.hi
  step_mem :
    forall x h n
      (_hx : inDomainInterval f.lower f.upper x)
      (hxh : inDomainInterval f.lower f.upper (x + h)),
      let I := f.compute (x + h) hxh (evalPrecision x h n)
      I.lo <= stepValue x h n /\ stepValue x h n <= I.hi
  derivative_mem :
    forall x h n
      (hdx : inDomainInterval df.lower df.upper x),
      let I := df.compute x hdx (evalPrecision x h n)
      I.lo <= derivativeValue x h n /\ derivativeValue x h n <= I.hi
  secant_error :
    forall x h n,
      inDomainInterval f.lower f.upper x ->
      inDomainInterval f.lower f.upper (x + h) ->
      h ≠ 0 ->
      qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
      qabs (((stepValue x h n - baseValue x h n) / h) -
        derivativeValue x h n) <= (precisionAtStage n).val
  quotient_width :
    forall x h n
      (hx : inDomainInterval f.lower f.upper x)
      (hxh : inDomainInterval f.lower f.upper (x + h)),
      h ≠ 0 ->
      qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
      (QInterval.differenceQuotient
        (f.compute (x + h) hxh (evalPrecision x h n))
        (f.compute x hx (evalPrecision x h n)) h).width <=
          (precisionAtStage n).val
  derivative_width :
    forall x h n
      (hdx : inDomainInterval df.lower df.upper x),
      (df.compute x hdx (evalPrecision x h n)).width <=
        (precisionAtStage n).val

namespace FiniteModelDerivativeOnInterval

/-- Convert finite rational model witnesses into the repository's full
two-sided represented derivative certificate. -/
def toHasDerivativeOnInterval
    {f df : FunctionOnInterval}
    (M : FiniteModelDerivativeOnInterval f df) :
    HasDerivativeOnInterval f df where
  same_lower := M.same_lower
  same_upper := M.same_upper
  stepPrecision := M.stepPrecision
  evalPrecision := M.evalPrecision
  close := by
    intro x h n hx hxh hdx hh hsmall
    let A := f.compute x hx (M.evalPrecision x h n)
    let B := f.compute (x + h) hxh (M.evalPrecision x h n)
    let D := df.compute x hdx (M.evalPrecision x h n)
    let q := (M.stepValue x h n - M.baseValue x h n) / h
    let d := M.derivativeValue x h n
    have hq :
        (QInterval.differenceQuotient B A h).lo <= q /\
          q <= (QInterval.differenceQuotient B A h).hi := by
      exact QInterval.differenceQuotient_mem_of_mem
        (M.base_mem x h n hx hxh) (M.step_mem x h n hx hxh) hh
    have hd : D.lo <= d /\ d <= D.hi := M.derivative_mem x h n hdx
    have herror : qabs (q - d) <= (precisionAtStage n).val :=
      M.secant_error x h n hx hxh hh hsmall
    exact QInterval.nearAt_of_mem_mem_qabs_sub_le hq hd herror
      (M.quotient_width x h n hx hxh hh hsmall)
      (M.derivative_width x h n hdx)

end FiniteModelDerivativeOnInterval

end ComputableAnalysis


