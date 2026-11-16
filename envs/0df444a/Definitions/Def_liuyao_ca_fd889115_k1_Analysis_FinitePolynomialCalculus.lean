-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FinitePolynomialCalculus
-- name    : liuyao_ca_fd889115_k1_Analysis_FinitePolynomialCalculus
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:55:18.03794+00:00
-- url     : https://prove2.me/theorems/dccc5952-8730-4408-89d0-c7aff90184b5
-- title:
--   Computable analysis · FinitePolynomialCalculus · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FinitePolynomialCalculus.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Differential
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Exp
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PowerSeries

set_option autoImplicit true

/-!
# Quantitative derivatives of finite rational polynomials

This module packages the finite secant estimate from `PowerSeries.lean` into
the project’s two-sided interval derivative interface.  The input is a
rational interval together with a rational bounding box; the proof selects a
dyadic step schedule from the explicitly computed monomial error coefficient.
No mean-value theorem, topology API, or completed-real argument is used.
-/

namespace ComputableAnalysis

namespace FinitePolynomial

/-- The normalized monomial `x^(n+1)/(n+1)` as an exact rational interval
function. -/
def normalizedMonomialOnInterval (a b : Rat) (n : Nat) : FunctionOnInterval :=
  FunctionOnInterval.exactRat
    (fun x => x ^ (n + 1) / ((n + 1 : Nat) : Rat)) a b

/-- The derivative monomial `x^n` on the same interval. -/
def monomialOnInterval (a b : Rat) (n : Nat) : FunctionOnInterval :=
  FunctionOnInterval.exactRat (fun x => x ^ n) a b

/-- The executable dyadic step schedule for the normalized-monomial
derivative.  It converts the explicit finite secant coefficient into the
requested interval precision by the rational half-decay modulus. -/
def normalizedMonomialStepPrecision (C : Rat) (n stage : Nat) : Nat :=
  2 ^ RationalMajorant.halfDecayShift
    (powerSecantErrorBound C (n + 1)) (precisionAtStage stage)

private theorem qabs_le_of_neg_le_le {x C : Rat}
    (hleft : -C <= x) (hright : x <= C) :
    qabs x <= C := by
  unfold qabs
  by_cases hx : x < 0
  · rw [if_pos hx]
    grind [Rat.sub_eq_add_neg]
  · rw [if_neg hx]
    exact hright

/-- A quantitative rational finite-difference certificate on the symmetric
box `[-C,C]`.

Unlike a bare derivative assertion, this records the explicit coefficient of
`|h|` in the secant error.  That is precisely the datum that survives finite
addition and rational scaling, and that later gives an executable dyadic
step schedule. -/
structure SecantDerivativeBound (C : Rat) (f df : Rat -> Rat) where
  errorCoefficient : Rat
  errorCoefficient_nonneg : 0 <= errorCoefficient
  error_bound : forall x h : Rat, h ≠ 0 ->
    qabs x <= C -> qabs (x + h) <= C ->
    qabs (((f (x + h) - f x) / h) - df x) <=
      qabs h * errorCoefficient

/-- A quantitative secant bound on a box centered at a rational expansion
point.  This is the translated form of `SecantDerivativeBound`; its local
coordinate is `x - basepoint`. -/
structure CenteredSecantDerivativeBound (basepoint C : Rat)
    (f df : Rat -> Rat) where
  errorCoefficient : Rat
  errorCoefficient_nonneg : 0 <= errorCoefficient
  error_bound : forall x h : Rat, h ≠ 0 ->
    qabs (x - basepoint) <= C -> qabs (x + h - basepoint) <= C ->
    qabs (((f (x + h) - f x) / h) - df x) <=
      qabs h * errorCoefficient

namespace SecantDerivativeBound

/-- Constants have zero finite-difference error. -/
def constant (C c : Rat) : SecantDerivativeBound C (fun _x => c) (fun _x => 0) where
  errorCoefficient := 0
  errorCoefficient_nonneg := by decide +kernel
  error_bound := by
    intro x h _hh _hx _hxh
    have hzero : (((c - c) / h) - 0 : Rat) = 0 := by
      rw [Rat.sub_self, Rat.div_def, Rat.zero_mul]
      grind [Rat.sub_eq_add_neg]
    rw [hzero, qabs_eq_self_of_nonneg (by decide +kernel), Rat.mul_zero]
    exact Rat.le_refl

/-- Quantitative secant bounds are closed under finite addition. -/
def add {C : Rat} {f df g dg : Rat -> Rat}
    (F : SecantDerivativeBound C f df)
    (G : SecantDerivativeBound C g dg) :
    SecantDerivativeBound C
      (fun x => f x + g x)
      (fun x => df x + dg x) where
  errorCoefficient := F.errorCoefficient + G.errorCoefficient
  errorCoefficient_nonneg := Rat.add_nonneg F.errorCoefficient_nonneg
    G.errorCoefficient_nonneg
  error_bound := by
    intro x h hh hx hxh
    have hF := F.error_bound x h hh hx hxh
    have hG := G.error_bound x h hh hx hxh
    have hsplit :
        (((f (x + h) + g (x + h) - (f x + g x)) / h) -
            (df x + dg x)) =
          (((f (x + h) - f x) / h) - df x) +
            (((g (x + h) - g x) / h) - dg x) := by
      rw [Rat.div_def, Rat.div_def, Rat.div_def]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
        Rat.add_assoc, Rat.add_comm, Rat.mul_comm]
    rw [hsplit]
    calc
      qabs
          ((((f (x + h) - f x) / h) - df x) +
            (((g (x + h) - g x) / h) - dg x)) <=
          qabs (((f (x + h) - f x) / h) - df x) +
            qabs (((g (x + h) - g x) / h) - dg x) :=
        qabs_add_le _ _
      _ <= qabs h * F.errorCoefficient + qabs h * G.errorCoefficient :=
        rat_add_le_add hF hG
      _ = qabs h * (F.errorCoefficient + G.errorCoefficient) := by
        grind [Rat.mul_add]

/-- Quantitative secant bounds are closed under rational scaling. -/
def scaleRat (r : Rat) {C : Rat} {f df : Rat -> Rat}
    (F : SecantDerivativeBound C f df) :
    SecantDerivativeBound C
      (fun x => r * f x)
      (fun x => r * df x) where
  errorCoefficient := qabs r * F.errorCoefficient
  errorCoefficient_nonneg := Rat.mul_nonneg (qabs_nonneg _)
    F.errorCoefficient_nonneg
  error_bound := by
    intro x h hh hx hxh
    have hF := F.error_bound x h hh hx hxh
    have hsplit :
        (((r * f (x + h) - r * f x) / h) - r * df x) =
          r * (((f (x + h) - f x) / h) - df x) := by
      rw [Rat.div_def, Rat.div_def]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
        Rat.add_assoc, Rat.add_comm, Rat.mul_comm]
    rw [hsplit, qabs_mul]
    calc
      qabs r * qabs (((f (x + h) - f x) / h) - df x) <=
          qabs r * (qabs h * F.errorCoefficient) :=
        Rat.mul_le_mul_of_nonneg_left hF (qabs_nonneg _)
      _ = qabs h * (qabs r * F.errorCoefficient) := by
        grind [Rat.mul_assoc, Rat.mul_comm]

/-- Quantitative secant bounds are closed under products when rational local
majorants for each factor and its proposed derivative are supplied.

The final term of the coefficient is the finite ``corner rectangle'': the
two secant quotients are bounded using `|h| <= 2C` on the symmetric box. -/
def mul {C : Rat} {f df g dg : Rat -> Rat}
    (F : SecantDerivativeBound C f df)
    (G : SecantDerivativeBound C g dg)
    (fMajorant dfMajorant gMajorant dgMajorant : Rat)
    (hfMajorant : forall x, qabs x <= C -> qabs (f x) <= fMajorant)
    (hdfMajorant : forall x, qabs x <= C -> qabs (df x) <= dfMajorant)
    (hgMajorant : forall x, qabs x <= C -> qabs (g x) <= gMajorant)
    (hdgMajorant : forall x, qabs x <= C -> qabs (dg x) <= dgMajorant)
    (hC0 : 0 <= C) (hf0 : 0 <= fMajorant) (hdf0 : 0 <= dfMajorant)
    (hg0 : 0 <= gMajorant) (hdg0 : 0 <= dgMajorant) :
    SecantDerivativeBound C
      (fun x => f x * g x)
      (fun x => f x * dg x + g x * df x) where
  errorCoefficient :=
    fMajorant * G.errorCoefficient + gMajorant * F.errorCoefficient +
      (dfMajorant + 2 * C * F.errorCoefficient) *
        (dgMajorant + 2 * C * G.errorCoefficient)
  errorCoefficient_nonneg := by
    apply Rat.add_nonneg
    · apply Rat.add_nonneg
      · exact Rat.mul_nonneg hf0 G.errorCoefficient_nonneg
      · exact Rat.mul_nonneg hg0 F.errorCoefficient_nonneg
    · apply Rat.mul_nonneg
      · exact Rat.add_nonneg hdf0
          (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC0)
            F.errorCoefficient_nonneg)
      · exact Rat.add_nonneg hdg0
          (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC0)
            G.errorCoefficient_nonneg)
  error_bound := by
    intro x h hh hx hxh
    let qf : Rat := (f (x + h) - f x) / h
    let qg : Rat := (g (x + h) - g x) / h
    have hstep : qabs h <= 2 * C := by
      have hrewrite : h = (x + h) - x := by
        grind [Rat.sub_eq_add_neg]
      rw [hrewrite]
      calc
        qabs ((x + h) - x) <= qabs (x + h) + qabs x := qabs_sub_le _ _
        _ <= C + C := rat_add_le_add hxh hx
        _ = 2 * C := by grind
    have hF := F.error_bound x h hh hx hxh
    have hG := G.error_bound x h hh hx hxh
    have hqf : qabs qf <= dfMajorant + 2 * C * F.errorCoefficient := by
      have hq : qabs qf <= qabs (qf - df x) + qabs (df x) := by
        calc
          qabs qf = qabs ((qf - df x) + df x) := by
            congr 1
            grind [Rat.sub_eq_add_neg]
          _ <= qabs (qf - df x) + qabs (df x) := qabs_add_le _ _
      have hF' : qabs (qf - df x) <= qabs h * F.errorCoefficient := by
        simpa [qf] using hF
      have hstepF : qabs h * F.errorCoefficient <=
          2 * C * F.errorCoefficient :=
        Rat.mul_le_mul_of_nonneg_right hstep F.errorCoefficient_nonneg
      calc
        qabs qf <= qabs (qf - df x) + qabs (df x) := hq
        _ <= qabs h * F.errorCoefficient + dfMajorant :=
          rat_add_le_add hF' (hdfMajorant x hx)
        _ <= 2 * C * F.errorCoefficient + dfMajorant :=
          rat_add_le_add hstepF Rat.le_refl
        _ = dfMajorant + 2 * C * F.errorCoefficient := by
          grind [Rat.add_comm]
    have hqg : qabs qg <= dgMajorant + 2 * C * G.errorCoefficient := by
      have hq : qabs qg <= qabs (qg - dg x) + qabs (dg x) := by
        calc
          qabs qg = qabs ((qg - dg x) + dg x) := by
            congr 1
            grind [Rat.sub_eq_add_neg]
          _ <= qabs (qg - dg x) + qabs (dg x) := qabs_add_le _ _
      have hG' : qabs (qg - dg x) <= qabs h * G.errorCoefficient := by
        simpa [qg] using hG
      have hstepG : qabs h * G.errorCoefficient <=
          2 * C * G.errorCoefficient :=
        Rat.mul_le_mul_of_nonneg_right hstep G.errorCoefficient_nonneg
      calc
        qabs qg <= qabs (qg - dg x) + qabs (dg x) := hq
        _ <= qabs h * G.errorCoefficient + dgMajorant :=
          rat_add_le_add hG' (hdgMajorant x hx)
        _ <= 2 * C * G.errorCoefficient + dgMajorant :=
          rat_add_le_add hstepG Rat.le_refl
        _ = dgMajorant + 2 * C * G.errorCoefficient := by
          grind [Rat.add_comm]
    have htermF :
        qabs (f x) * qabs (qg - dg x) <=
          qabs h * (fMajorant * G.errorCoefficient) := by
      calc
        qabs (f x) * qabs (qg - dg x) <=
            fMajorant * qabs (qg - dg x) :=
          Rat.mul_le_mul_of_nonneg_right (hfMajorant x hx) (qabs_nonneg _)
        _ <= fMajorant * (qabs h * G.errorCoefficient) :=
          Rat.mul_le_mul_of_nonneg_left (by simpa [qg] using hG) hf0
        _ = qabs h * (fMajorant * G.errorCoefficient) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    have htermG :
        qabs (g x) * qabs (qf - df x) <=
          qabs h * (gMajorant * F.errorCoefficient) := by
      calc
        qabs (g x) * qabs (qf - df x) <=
            gMajorant * qabs (qf - df x) :=
          Rat.mul_le_mul_of_nonneg_right (hgMajorant x hx) (qabs_nonneg _)
        _ <= gMajorant * (qabs h * F.errorCoefficient) :=
          Rat.mul_le_mul_of_nonneg_left (by simpa [qf] using hF) hg0
        _ = qabs h * (gMajorant * F.errorCoefficient) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    have htermQ :
        qabs h * qabs qf * qabs qg <=
          qabs h * ((dfMajorant + 2 * C * F.errorCoefficient) *
            (dgMajorant + 2 * C * G.errorCoefficient)) := by
      have hproduct : qabs qf * qabs qg <=
          (dfMajorant + 2 * C * F.errorCoefficient) *
            (dgMajorant + 2 * C * G.errorCoefficient) := by
        calc
          qabs qf * qabs qg <=
              (dfMajorant + 2 * C * F.errorCoefficient) * qabs qg :=
            Rat.mul_le_mul_of_nonneg_right hqf (qabs_nonneg _)
          _ <= (dfMajorant + 2 * C * F.errorCoefficient) *
              (dgMajorant + 2 * C * G.errorCoefficient) :=
            Rat.mul_le_mul_of_nonneg_left hqg
              (Rat.add_nonneg hdf0
                (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC0)
                  F.errorCoefficient_nonneg))
      calc
        qabs h * qabs qf * qabs qg = qabs h * (qabs qf * qabs qg) := by
          rw [Rat.mul_assoc]
        _ <= qabs h * ((dfMajorant + 2 * C * F.errorCoefficient) *
            (dgMajorant + 2 * C * G.errorCoefficient)) :=
          Rat.mul_le_mul_of_nonneg_left hproduct (qabs_nonneg _)
    have hproduct := ExactFunction.product_differenceQuotient_error_le_qabs
      f df g dg x h hh
    calc
      qabs (((f (x + h) * g (x + h) - f x * g x) / h) -
          (f x * dg x + g x * df x)) <=
          qabs (f x) * qabs (qg - dg x) +
            qabs (g x) * qabs (qf - df x) +
              qabs h * qabs qf * qabs qg := by
            simpa [qf, qg, ExactFunction.differenceQuotient] using hproduct
      _ <= qabs h * (fMajorant * G.errorCoefficient) +
            qabs h * (gMajorant * F.errorCoefficient) +
              qabs h * ((dfMajorant + 2 * C * F.errorCoefficient) *
                (dgMajorant + 2 * C * G.errorCoefficient)) := by
            exact rat_add_le_add (rat_add_le_add htermF htermG) htermQ
      _ = qabs h *
          (fMajorant * G.errorCoefficient + gMajorant * F.errorCoefficient +
            (dfMajorant + 2 * C * F.errorCoefficient) *
              (dgMajorant + 2 * C * G.errorCoefficient)) := by
            grind [Rat.mul_add, Rat.mul_assoc, Rat.add_assoc]

/-- Quantitative secant bounds are closed under reciprocals on a box where
the denominator is uniformly at least one.

The coefficient is completely explicit.  The first term transports the
original secant error through division; the second pays for changing the two
denominator factors between the base point and the step endpoint. -/
def reciprocalOfOneLe {C : Rat} {f df : Rat -> Rat}
    (F : SecantDerivativeBound C f df)
    (derivativeMajorant : Rat)
    (hderivativeMajorant : forall x, qabs x <= C ->
      qabs (df x) <= derivativeMajorant)
    (hderivativeNonneg : 0 <= derivativeMajorant)
    (hC0 : 0 <= C)
    (hone : forall x, qabs x <= C -> 1 <= f x) :
    SecantDerivativeBound C
      (fun x => 1 / f x)
      (fun x => -(df x / (f x * f x))) where
  errorCoefficient :=
    F.errorCoefficient + derivativeMajorant *
      (derivativeMajorant + 2 * C * F.errorCoefficient)
  errorCoefficient_nonneg := by
    exact Rat.add_nonneg F.errorCoefficient_nonneg
      (Rat.mul_nonneg hderivativeNonneg
        (Rat.add_nonneg hderivativeNonneg
          (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC0)
            F.errorCoefficient_nonneg)))
  error_bound := by
    intro x h hh hx hxh
    let a := f x
    let b := f (x + h)
    let d := df x
    let q := (b - a) / h
    let Q := derivativeMajorant + 2 * C * F.errorCoefficient
    have haOne : 1 <= a := hone x hx
    have hbOne : 1 <= b := hone (x + h) hxh
    have haPos : 0 < a := by grind
    have hbPos : 0 < b := by grind
    have haNe : a ≠ 0 := Rat.ne_of_gt haPos
    have hbNe : b ≠ 0 := Rat.ne_of_gt hbPos
    have hF : qabs (q - d) <= qabs h * F.errorCoefficient := by
      simpa [a, b, d, q] using F.error_bound x h hh hx hxh
    have hstep : qabs h <= 2 * C := by
      have hrewrite : h = (x + h) - x := by
        grind [Rat.sub_eq_add_neg]
      rw [hrewrite]
      calc
        qabs ((x + h) - x) <= qabs (x + h) + qabs x := qabs_sub_le _ _
        _ <= C + C := rat_add_le_add hxh hx
        _ = 2 * C := by grind
    have hq : qabs q <= Q := by
      have htriangle : qabs q <= qabs (q - d) + qabs d := by
        calc
          qabs q = qabs ((q - d) + d) := by
            congr 1
            grind [Rat.sub_eq_add_neg]
          _ <= qabs (q - d) + qabs d := qabs_add_le _ _
      have hstepError : qabs h * F.errorCoefficient <=
          2 * C * F.errorCoefficient :=
        Rat.mul_le_mul_of_nonneg_right hstep F.errorCoefficient_nonneg
      calc
        qabs q <= qabs (q - d) + qabs d := htriangle
        _ <= qabs h * F.errorCoefficient + derivativeMajorant :=
          rat_add_le_add hF (hderivativeMajorant x hx)
        _ <= 2 * C * F.errorCoefficient + derivativeMajorant :=
          rat_add_le_add hstepError Rat.le_refl
        _ = Q := by
          dsimp [Q]
          grind [Rat.add_comm]
    have hQ0 : 0 <= Q := by
      dsimp [Q]
      exact Rat.add_nonneg hderivativeNonneg
        (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hC0)
          F.errorCoefficient_nonneg)
    have habOne : 1 <= a * b := by
      calc
        (1 : Rat) = 1 * 1 := by decide +kernel
        _ <= a * b := rat_mul_le_mul_of_nonneg
          (by decide +kernel) haOne (by decide +kernel) hbOne
    have haabOne : 1 <= a * a * b := by
      have haaOne : 1 <= a * a := by
        calc
          (1 : Rat) = 1 * 1 := by decide +kernel
          _ <= a * a := rat_mul_le_mul_of_nonneg
            (by decide +kernel) haOne (by decide +kernel) haOne
      calc
        (1 : Rat) = 1 * 1 := by decide +kernel
        _ <= (a * a) * b := rat_mul_le_mul_of_nonneg
          (by decide +kernel) haaOne (by decide +kernel) hbOne
    have habPos : 0 < a * b := Rat.mul_pos haPos hbPos
    have haabPos : 0 < a * a * b :=
      Rat.mul_pos (Rat.mul_pos haPos haPos) hbPos
    have hinvAB0 : 0 <= 1 / (a * b) := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (by decide +kernel)
        (Rat.le_of_lt ((Rat.inv_pos).2 habPos))
    have hinvAAB0 : 0 <= 1 / (a * a * b) := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (by decide +kernel)
        (Rat.le_of_lt ((Rat.inv_pos).2 haabPos))
    have one_div_le_one_of_one_le {z : Rat}
        (hzOne : 1 <= z) (hzPos : 0 < z) : 1 / z <= 1 := by
      have hzNe : z ≠ 0 := Rat.ne_of_gt hzPos
      apply Rat.le_of_mul_le_mul_right (c := z)
      · calc
          (1 / z) * z = 1 := by
            rw [Rat.div_def]
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_cancel]
          _ <= z := hzOne
          _ = 1 * z := by rw [Rat.one_mul]
      · exact hzPos
    have hinvABle : 1 / (a * b) <= 1 := by
      exact one_div_le_one_of_one_le habOne habPos
    have hinvAABle : 1 / (a * a * b) <= 1 := by
      exact one_div_le_one_of_one_le haabOne haabPos
    have hqabsInvAB : qabs ((a * b)⁻¹) = 1 / (a * b) := by
      rw [qabs_eq_self_of_nonneg
        (Rat.le_of_lt ((Rat.inv_pos).2 habPos))]
      simp [Rat.div_def]
    have hqabsInvAAB : qabs ((a * a * b)⁻¹) = 1 / (a * a * b) := by
      rw [qabs_eq_self_of_nonneg
        (Rat.le_of_lt ((Rat.inv_pos).2 haabPos))]
      simp [Rat.div_def]
    have hqmul : q * h = b - a := by
      dsimp [q]
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_cancel]
    have hidentity :
        (((1 / b - 1 / a) / h) - (-(d / (a * a)))) =
          (-(q - d)) / (a * b) + (d * h * q) / (a * a * b) := by
      rw [Rat.div_def]
      have habNe : a * b ≠ 0 := Rat.ne_of_gt habPos
      have haaNe : a * a ≠ 0 :=
        Rat.ne_of_gt (Rat.mul_pos haPos haPos)
      have haabNe : a * a * b ≠ 0 := Rat.ne_of_gt haabPos
      dsimp [q]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
        Rat.mul_comm, Rat.inv_mul_cancel, Rat.mul_inv_cancel]
    have hfirst :
        qabs ((-(q - d)) / (a * b)) <= qabs h * F.errorCoefficient := by
      rw [Rat.div_def, qabs_mul, qabs_neg, hqabsInvAB]
      calc
        qabs (q - d) * (1 / (a * b)) <=
            (qabs h * F.errorCoefficient) * (1 / (a * b)) :=
          Rat.mul_le_mul_of_nonneg_right hF hinvAB0
        _ <= (qabs h * F.errorCoefficient) * 1 :=
          Rat.mul_le_mul_of_nonneg_left hinvABle
            (Rat.mul_nonneg (qabs_nonneg _) F.errorCoefficient_nonneg)
        _ = qabs h * F.errorCoefficient := by rw [Rat.mul_one]
    have hsecond :
        qabs ((d * h * q) / (a * a * b)) <=
          qabs h * (derivativeMajorant * Q) := by
      rw [Rat.div_def, qabs_mul, qabs_mul, qabs_mul, hqabsInvAAB]
      have hdq : qabs d * qabs q <= derivativeMajorant * Q :=
        calc
          qabs d * qabs q <= derivativeMajorant * qabs q :=
            Rat.mul_le_mul_of_nonneg_right
              (hderivativeMajorant x hx) (qabs_nonneg _)
          _ <= derivativeMajorant * Q :=
            Rat.mul_le_mul_of_nonneg_left hq hderivativeNonneg
      calc
        qabs d * qabs h * qabs q * (1 / (a * a * b)) =
            qabs h * (qabs d * qabs q) * (1 / (a * a * b)) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= qabs h * (derivativeMajorant * Q) *
              (1 / (a * a * b)) :=
          Rat.mul_le_mul_of_nonneg_right
            (Rat.mul_le_mul_of_nonneg_left hdq (qabs_nonneg _)) hinvAAB0
        _ <= qabs h * (derivativeMajorant * Q) * 1 :=
          Rat.mul_le_mul_of_nonneg_left hinvAABle
            (Rat.mul_nonneg (qabs_nonneg _)
              (Rat.mul_nonneg hderivativeNonneg hQ0))
        _ = qabs h * (derivativeMajorant * Q) := by rw [Rat.mul_one]
    rw [show f x = a by rfl, show f (x + h) = b by rfl,
      show df x = d by rfl, hidentity]
    calc
      qabs ((-(q - d)) / (a * b) + (d * h * q) / (a * a * b)) <=
          qabs ((-(q - d)) / (a * b)) +
            qabs ((d * h * q) / (a * a * b)) := qabs_add_le _ _
      _ <= qabs h * F.errorCoefficient +
          qabs h * (derivativeMajorant * Q) :=
        rat_add_le_add hfirst hsecond
      _ = qabs h *
          (F.errorCoefficient + derivativeMajorant * Q) := by
        grind [Rat.mul_add]

/-- Translation of the input leaves a quantitative secant bound unchanged.
This is the finite algebra needed to use a Taylor polynomial at its declared
rational expansion point instead of only at zero. -/
def translate (a : Rat) {C : Rat} {f df : Rat -> Rat}
    (F : SecantDerivativeBound C f df) :
    CenteredSecantDerivativeBound a C
      (fun x => f (x - a))
      (fun x => df (x - a)) where
  errorCoefficient := F.errorCoefficient
  errorCoefficient_nonneg := F.errorCoefficient_nonneg
  error_bound := by
    intro x h hh hx hxh
    have hshift : (x - a) + h = (x + h) - a := by
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    have hF := F.error_bound (x - a) h hh hx (by
      rw [hshift]
      exact hxh)
    simpa [hshift] using hF

/-- The dyadic schedule selected by a quantitative secant coefficient. -/
def stepPrecision {C : Rat} {f df : Rat -> Rat}
    (F : SecantDerivativeBound C f df) (stage : Nat) : Nat :=
  2 ^ RationalMajorant.halfDecayShift F.errorCoefficient
    (precisionAtStage stage)

private theorem step_error_le_precision
    {C : Rat} {f df : Rat -> Rat}
    (F : SecantDerivativeBound C f df) {h : Rat} (stage : Nat)
    (hsmall : qabs h <= 1 / ((F.stepPrecision stage : Nat) : Rat)) :
    qabs h * F.errorCoefficient <= (precisionAtStage stage).val := by
  let shift : Nat := RationalMajorant.halfDecayShift F.errorCoefficient
    (precisionAtStage stage)
  have hsmall' : qabs h <= 1 / (((2 ^ shift : Nat) : Rat)) := by
    simpa [stepPrecision, shift] using hsmall
  have hscaled : qabs h * F.errorCoefficient <=
      1 / (((2 ^ shift : Nat) : Rat)) * F.errorCoefficient :=
    Rat.mul_le_mul_of_nonneg_right hsmall' F.errorCoefficient_nonneg
  have hgeometric : F.errorCoefficient * ((1 : Rat) / 2) ^ shift <=
      (precisionAtStage stage).val := by
    simpa [shift] using RationalMajorant.halfDecayShift_spec
      F.errorCoefficient_nonneg (precisionAtStage stage)
  calc
    qabs h * F.errorCoefficient <=
        1 / (((2 ^ shift : Nat) : Rat)) * F.errorCoefficient := hscaled
    _ = F.errorCoefficient * ((1 : Rat) / 2) ^ shift := by
      rw [RationalMajorant.half_pow_eq_one_div_nat_two_pow]
      grind [Rat.mul_comm]
    _ <= (precisionAtStage stage).val := hgeometric

/-- Package a quantitative rational secant bound as the project's two-sided
interval derivative certificate on any subinterval of its symmetric box. -/
def toHasDerivativeOnInterval {C : Rat} {f df : Rat -> Rat}
    (F : SecantDerivativeBound C f df)
    (a b : Rat) (hleft : -C <= a) (hright : b <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat f a b)
      (FunctionOnInterval.exactRat df a b) where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := F.stepPrecision
  evalPrecision := fun _x _h _stage => 0
  close := by
    intro x h stage hx hxh _hdx hh hsmall
    have hxleft : -C <= x := Rat.le_trans hleft hx.1
    have hxright : x <= C := Rat.le_trans hx.2 hright
    have hxhleft : -C <= x + h := Rat.le_trans hleft hxh.1
    have hxhright : x + h <= C := Rat.le_trans hxh.2 hright
    have hxbound : qabs x <= C := qabs_le_of_neg_le_le hxleft hxright
    have hxhbound : qabs (x + h) <= C :=
      qabs_le_of_neg_le_le hxhleft hxhright
    have hfinite := F.error_bound x h hh hxbound hxhbound
    have hstep := F.step_error_le_precision stage hsmall
    have herror : qabs (((f (x + h) - f x) / h) - df x) <=
        (precisionAtStage stage).val :=
      Rat.le_trans hfinite hstep
    let q : Rat := (f (x + h) - f x) / h
    have hupper : q - df x <= (precisionAtStage stage).val := by
      calc
        q - df x <= qabs (q - df x) := self_le_qabs _
        _ <= (precisionAtStage stage).val := by simpa [q] using herror
    have hlower : -(q - df x) <= (precisionAtStage stage).val := by
      calc
        -(q - df x) <= qabs (-(q - df x)) := self_le_qabs _
        _ = qabs (q - df x) := qabs_neg _
        _ <= (precisionAtStage stage).val := by simpa [q] using herror
    change intervalNearAtPrecision
      (QInterval.differenceQuotient
        { lo := f (x + h), hi := f (x + h) }
        { lo := f x, hi := f x } h)
      { lo := df x, hi := df x } stage
    rw [QInterval.differenceQuotient_singleton]
    unfold intervalNearAtPrecision QInterval.NearAt QInterval.width
    constructor
    · change q <= df x + (precisionAtStage stage).val
      grind [Rat.sub_eq_add_neg]
    constructor
    · change df x <= q + (precisionAtStage stage).val
      grind [Rat.sub_eq_add_neg]
    constructor <;> grind [Rat.sub_eq_add_neg]

/- A product certificate can be handed directly to the interval derivative
interface.  The hypotheses are deliberately explicit: the finite product
estimate needs rational majorants for both factors and both proposed
derivatives, and the resulting interval chart is the exact rational product
chart rather than an unproved real-valued multiplication. -/
def SecantDerivativeBound.mulToHasDerivativeOnInterval
    {C : Rat} {f df g dg : Rat -> Rat}
    (F : SecantDerivativeBound C f df)
    (G : SecantDerivativeBound C g dg)
    (fMajorant dfMajorant gMajorant dgMajorant : Rat)
    (hfMajorant : forall x, qabs x <= C -> qabs (f x) <= fMajorant)
    (hdfMajorant : forall x, qabs x <= C -> qabs (df x) <= dfMajorant)
    (hgMajorant : forall x, qabs x <= C -> qabs (g x) <= gMajorant)
    (hdgMajorant : forall x, qabs x <= C -> qabs (dg x) <= dgMajorant)
    (hC0 : 0 <= C) (hf0 : 0 <= fMajorant) (hdf0 : 0 <= dfMajorant)
    (hg0 : 0 <= gMajorant) (hdg0 : 0 <= dgMajorant)
    (a b : Rat) (hleft : -C <= a) (hright : b <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (fun x => f x * g x) a b)
      (FunctionOnInterval.exactRat
        (fun x => f x * dg x + g x * df x) a b) :=
  SecantDerivativeBound.toHasDerivativeOnInterval
    (SecantDerivativeBound.mul F G fMajorant dfMajorant gMajorant dgMajorant
      hfMajorant hdfMajorant hgMajorant hdgMajorant hC0 hf0 hdf0 hg0 hdg0)
    a b hleft hright

end SecantDerivativeBound

namespace CenteredSecantDerivativeBound

/-- The same explicit dyadic schedule works on a translated box, because a
translation changes neither the step nor the quantitative error coefficient. -/
def stepPrecision {basepoint C : Rat} {f df : Rat -> Rat}
    (F : CenteredSecantDerivativeBound basepoint C f df) (stage : Nat) : Nat :=
  2 ^ RationalMajorant.halfDecayShift F.errorCoefficient
    (precisionAtStage stage)

private theorem step_error_le_precision
    {basepoint C : Rat} {f df : Rat -> Rat}
    (F : CenteredSecantDerivativeBound basepoint C f df) {h : Rat} (stage : Nat)
    (hsmall : qabs h <= 1 / ((F.stepPrecision stage : Nat) : Rat)) :
    qabs h * F.errorCoefficient <= (precisionAtStage stage).val := by
  let shift : Nat := RationalMajorant.halfDecayShift F.errorCoefficient
    (precisionAtStage stage)
  have hsmall' : qabs h <= 1 / (((2 ^ shift : Nat) : Rat)) := by
    simpa [stepPrecision, shift] using hsmall
  have hscaled : qabs h * F.errorCoefficient <=
      1 / (((2 ^ shift : Nat) : Rat)) * F.errorCoefficient :=
    Rat.mul_le_mul_of_nonneg_right hsmall' F.errorCoefficient_nonneg
  have hgeometric : F.errorCoefficient * ((1 : Rat) / 2) ^ shift <=
      (precisionAtStage stage).val := by
    simpa [shift] using RationalMajorant.halfDecayShift_spec
      F.errorCoefficient_nonneg (precisionAtStage stage)
  calc
    qabs h * F.errorCoefficient <=
        1 / (((2 ^ shift : Nat) : Rat)) * F.errorCoefficient := hscaled
    _ = F.errorCoefficient * ((1 : Rat) / 2) ^ shift := by
      rw [RationalMajorant.half_pow_eq_one_div_nat_two_pow]
      grind [Rat.mul_comm]
    _ <= (precisionAtStage stage).val := hgeometric

/-- A translated quantitative secant bound gives a two-sided interval
derivative certificate on any rational interval lying in its local box. -/
def toHasDerivativeOnInterval {basepoint C : Rat} {f df : Rat -> Rat}
    (F : CenteredSecantDerivativeBound basepoint C f df)
    (a b : Rat) (hleft : -C <= a - basepoint)
    (hright : b - basepoint <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat f a b)
      (FunctionOnInterval.exactRat df a b) where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := F.stepPrecision
  evalPrecision := fun _x _h _stage => 0
  close := by
    intro x h stage hx hxh _hdx hh hsmall
    change a <= x /\ x <= b at hx
    change a <= x + h /\ x + h <= b at hxh
    have hxleft : -C <= x - basepoint := by
      calc
        -C <= a - basepoint := hleft
        _ <= x - basepoint := by grind [Rat.sub_eq_add_neg]
    have hxright : x - basepoint <= C := by
      calc
        x - basepoint <= b - basepoint := by grind [Rat.sub_eq_add_neg]
        _ <= C := hright
    have hxhleft : -C <= x + h - basepoint := by
      calc
        -C <= a - basepoint := hleft
        _ <= x + h - basepoint := by grind [Rat.sub_eq_add_neg]
    have hxhright : x + h - basepoint <= C := by
      calc
        x + h - basepoint <= b - basepoint := by grind [Rat.sub_eq_add_neg]
        _ <= C := hright
    have hxbound : qabs (x - basepoint) <= C :=
      qabs_le_of_neg_le_le hxleft hxright
    have hxhbound : qabs (x + h - basepoint) <= C :=
      qabs_le_of_neg_le_le hxhleft hxhright
    have hfinite := F.error_bound x h hh hxbound hxhbound
    have hstep := F.step_error_le_precision stage hsmall
    have herror : qabs (((f (x + h) - f x) / h) - df x) <=
        (precisionAtStage stage).val :=
      Rat.le_trans hfinite hstep
    let q : Rat := (f (x + h) - f x) / h
    have hupper : q - df x <= (precisionAtStage stage).val := by
      calc
        q - df x <= qabs (q - df x) := self_le_qabs _
        _ <= (precisionAtStage stage).val := by simpa [q] using herror
    have hlower : -(q - df x) <= (precisionAtStage stage).val := by
      calc
        -(q - df x) <= qabs (-(q - df x)) := self_le_qabs _
        _ = qabs (q - df x) := qabs_neg _
        _ <= (precisionAtStage stage).val := by simpa [q] using herror
    change intervalNearAtPrecision
      (QInterval.differenceQuotient
        { lo := f (x + h), hi := f (x + h) }
        { lo := f x, hi := f x } h)
      { lo := df x, hi := df x } stage
    rw [QInterval.differenceQuotient_singleton]
    unfold intervalNearAtPrecision QInterval.NearAt QInterval.width
    constructor
    · change q <= df x + (precisionAtStage stage).val
      grind [Rat.sub_eq_add_neg]
    constructor
    · change df x <= q + (precisionAtStage stage).val
      grind [Rat.sub_eq_add_neg]
    constructor <;> grind [Rat.sub_eq_add_neg]

/-! The reciprocal kernel is the first non-polynomial derivative certificate
needed by the logarithm chapter.  It is centered at `3/2` with radius `1/2`,
so every admissible rational point and step endpoint lies in `[1,2]`. -/
def reciprocalCenteredSecantBound :
    CenteredSecantDerivativeBound (3 / 2) (1 / 2)
      (fun x => 1 / x) (fun x => -(1 / x ^ 2)) := by
  refine {
    errorCoefficient := 1
    errorCoefficient_nonneg := by decide +kernel
    error_bound := ?_ }
  intro x h hh hx hxh
  have hxlo : (1 : Rat) <= x := by
    have hq := neg_qabs_le_self (x - 3 / 2)
    exact (by grind : (1 : Rat) <= x)
  have hxhi : x <= 2 := by
    have hq := self_le_qabs (x - 3 / 2)
    exact (by grind : x <= (2 : Rat))
  have hxhlo : (1 : Rat) <= x + h := by
    have hq := neg_qabs_le_self (x + h - 3 / 2)
    exact (by grind : (1 : Rat) <= x + h)
  have hxhhi : x + h <= 2 := by
    have hq := self_le_qabs (x + h - 3 / 2)
    exact (by grind : x + h <= (2 : Rat))
  have hxpos : 0 < x := by grind
  have hxhpos : 0 < x + h := by grind
  have hxne : x ≠ 0 := Rat.ne_of_gt hxpos
  have hxhne : x + h ≠ 0 := Rat.ne_of_gt hxhpos
  have hdenpos : 0 < x ^ 2 * (x + h) := by
    exact Rat.mul_pos (Rat.pow_pos hxpos) hxhpos
  have hdenone : (1 : Rat) <= x ^ 2 * (x + h) := by
    have hxsq : (1 : Rat) <= x ^ 2 := by
      rw [show x ^ 2 = x * x by simp [Rat.pow_succ]]
      calc
        (1 : Rat) = 1 * 1 := by decide +kernel
        _ <= x * 1 := Rat.mul_le_mul_of_nonneg_right hxlo (by decide +kernel)
        _ <= x * x := Rat.mul_le_mul_of_nonneg_left hxlo (by grind)
    calc
      (1 : Rat) = 1 * 1 := by decide +kernel
      _ <= 1 * (x + h) := by
        exact Rat.mul_le_mul_of_nonneg_left hxhlo (by decide +kernel)
      _ <= x ^ 2 * (x + h) := by
        exact Rat.mul_le_mul_of_nonneg_right hxsq (Rat.le_of_lt hxhpos)
  have hinv_nonneg : 0 <= (x ^ 2 * (x + h))⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hdenpos)
  have hinv_le_one : (x ^ 2 * (x + h))⁻¹ <= 1 := by
    apply Rat.le_of_mul_le_mul_right (c := x ^ 2 * (x + h))
    · calc
        (x ^ 2 * (x + h))⁻¹ * (x ^ 2 * (x + h)) = 1 :=
          Rat.inv_mul_cancel _ (Rat.ne_of_gt hdenpos)
        _ <= 1 * (x ^ 2 * (x + h)) := by
          simpa using hdenone
    · exact hdenpos
  have hrewrite :
      ((1 / (x + h) - 1 / x) / h - -(1 / x ^ 2)) =
        h * (x ^ 2 * (x + h))⁻¹ := by
    rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def,
      Rat.inv_mul_rev]
    have hxinv : x * x⁻¹ = 1 := Rat.mul_inv_cancel x hxne
    have hxinv' : x⁻¹ * x = 1 := Rat.inv_mul_cancel x hxne
    have hxh_inv : (x + h) * (x + h)⁻¹ = 1 :=
      Rat.mul_inv_cancel (x + h) hxhne
    have hxh_inv' : (x + h)⁻¹ * (x + h) = 1 :=
      Rat.inv_mul_cancel (x + h) hxhne
    have h_inv : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
    have h_inv' : h⁻¹ * h = 1 := Rat.inv_mul_cancel h hh
    have hx2rewrite : (x ^ 2)⁻¹ = x⁻¹ * x⁻¹ := by
      simp [Rat.pow_succ, Rat.inv_mul_rev]
    rw [hx2rewrite]
    simp only [Rat.one_mul]
    grind [Rat.mul_inv_cancel, Rat.inv_mul_cancel,
      Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.sub_eq_add_neg]
  rw [hrewrite, qabs_mul, qabs_eq_self_of_nonneg hinv_nonneg]
  have hmul : qabs h * (x ^ 2 * (x + h))⁻¹ <= qabs h * 1 :=
    Rat.mul_le_mul_of_nonneg_left hinv_le_one (qabs_nonneg h)
  simpa only [Rat.mul_one] using hmul

/-- The reciprocal kernel has a two-sided finite-difference derivative
certificate on the logarithm chart `[1,2]`. -/
def reciprocalOnOneTwo_hasDerivativeOnInterval :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (fun x => 1 / x) 1 2)
      (FunctionOnInterval.exactRat (fun x => -(1 / x ^ 2)) 1 2) :=
  CenteredSecantDerivativeBound.toHasDerivativeOnInterval
    reciprocalCenteredSecantBound 1 2 (by decide +kernel) (by decide +kernel)

/-! Transport the same certificate through the rational translation
`x ↦ x + 1`.  This is the coordinate used by the logarithm integral on
`[0,1]`. -/
def logTwoKernelCenteredSecantBound :
    CenteredSecantDerivativeBound (1 / 2) (1 / 2)
      (fun x => 1 / (1 + x)) (fun x => -(1 / (1 + x) ^ 2)) := by
  refine {
    errorCoefficient := reciprocalCenteredSecantBound.errorCoefficient
    errorCoefficient_nonneg := reciprocalCenteredSecantBound.errorCoefficient_nonneg
    error_bound := ?_ }
  intro x h hh hx hxh
  have hx' : qabs ((x + 1) - 3 / 2) <= (1 / 2 : Rat) := by
    have heq : (x + 1) - 3 / 2 = x - 1 / 2 := by
      grind [Rat.sub_eq_add_neg]
    rw [heq]
    exact hx
  have hxh' : qabs ((x + h + 1) - 3 / 2) <= (1 / 2 : Rat) := by
    have heq : (x + h + 1) - 3 / 2 = x + h - 1 / 2 := by
      grind [Rat.sub_eq_add_neg]
    rw [heq]
    exact hxh
  have hbound := reciprocalCenteredSecantBound.error_bound
    (x + 1) h hh hx' (by
      have heq : (x + 1 + h) - 3 / 2 = (x + h + 1) - 3 / 2 := by
        grind [Rat.sub_eq_add_neg]
      rw [heq]
      exact hxh')
  simpa [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
    Rat.pow_succ, reciprocalCenteredSecantBound] using hbound

/-- The translated reciprocal kernel has a two-sided finite-difference
derivative certificate on the unit interval. -/
def logTwoKernel_hasDerivativeOnInterval :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (fun x => 1 / (1 + x)) 0 1)
      (FunctionOnInterval.exactRat (fun x => -(1 / (1 + x) ^ 2)) 0 1) :=
  CenteredSecantDerivativeBound.toHasDerivativeOnInterval
    logTwoKernelCenteredSecantBound 0 1 (by decide +kernel) (by decide +kernel)

end CenteredSecantDerivativeBound

/-- The monomial secant estimate as reusable quantitative data. -/
def normalizedMonomialSecantBound (C : Rat) (n : Nat) (hC1 : 1 <= C) :
    SecantDerivativeBound C
      (fun x => x ^ (n + 1) / ((n + 1 : Nat) : Rat))
      (fun x => x ^ n) where
  errorCoefficient := powerSecantErrorBound C (n + 1)
  errorCoefficient_nonneg :=
    powerSecantErrorBound_nonneg
      (Rat.le_trans (by decide +kernel) hC1) _
  error_bound := by
    intro x h hh hx hxh
    exact qabs_normalized_power_differenceQuotient_sub_monomial_le
      (x := x) (h := h) (C := C) hh
      (Rat.le_trans (by decide +kernel) hC1) hC1 hx hxh n

/-- Every normalized monomial has a two-sided rational interval derivative on
any interval contained in `[-C,C]`, provided `C >= 1`.  The proof is the
literal finite quotient estimate with a dyadic schedule chosen from its
explicit error coefficient. -/
def normalizedMonomial_hasDerivativeOnInterval
    (a b C : Rat) (n : Nat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (normalizedMonomialOnInterval a b n)
      (monomialOnInterval a b n) := by
  simpa [normalizedMonomialOnInterval, monomialOnInterval,
    normalizedMonomialStepPrecision, SecantDerivativeBound.stepPrecision]
    using (normalizedMonomialSecantBound C n hC1).toHasDerivativeOnInterval
      a b hleft hright

/-! The local FTC consequence of the normalized power rule.  This is the
application-facing form: on one positive rational cell, the derivative box
scaled by the cell width contains the finite endpoint increment.  It is the
piece that a partition-level effective FTC assembles across cells. -/
theorem normalizedMonomial_endpointDifference_contains_of_pos
    (a b C : Rat) (n : Nat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C)
    {x h : Rat} {stage : Nat}
    (hx : inDomainInterval a b x)
    (hxh : inDomainInterval a b (x + h))
    (hpos : 0 < h)
    (hsmall : qabs h <=
      (1 / ((
        (normalizedMonomial_hasDerivativeOnInterval a b C n hleft hright hC1).stepPrecision
          stage : Nat) : Rat))) :
    (QInterval.scaleByRat h
      (QInterval.expand
        ((monomialOnInterval a b n).compute x hx
          ((normalizedMonomial_hasDerivativeOnInterval a b C n hleft hright hC1).evalPrecision
            x h stage))
        (2 * (precisionAtStage stage).val))).ContainsInterval
      (QInterval.subInterval
        ((normalizedMonomialOnInterval a b n).compute (x + h) hxh
          ((normalizedMonomial_hasDerivativeOnInterval a b C n hleft hright hC1).evalPrecision
            x h stage))
        ((normalizedMonomialOnInterval a b n).compute x hx
          ((normalizedMonomial_hasDerivativeOnInterval a b C n hleft hright hC1).evalPrecision
            x h stage))) := by
  exact HasDerivativeOnInterval.endpointDifference_contains_of_pos
    (normalizedMonomial_hasDerivativeOnInterval a b C n hleft hright hC1)
    hx hxh hx hpos hsmall

/-! Scaling the normalized monomial by its denominator exposes the general
power rule.  The only new algebra is cancellation of the positive rational
`n + 1`; all error control remains the normalized finite secant certificate. -/
def monomialSecantDerivativeBound (C : Rat) (n : Nat) (hC1 : 1 <= C) :
    SecantDerivativeBound C
      (fun x => x ^ (n + 1))
      (fun x => ((n + 1 : Nat) : Rat) * x ^ n) := by
  let k : Rat := ((n + 1 : Nat) : Rat)
  let H := SecantDerivativeBound.scaleRat k
    (normalizedMonomialSecantBound C n hC1)
  have hk : k ≠ 0 := by
    dsimp [k]
    exact Rat.ne_of_gt (by
      exact (Rat.natCast_pos).2 (Nat.succ_pos n))
  refine {
    errorCoefficient := H.errorCoefficient
    errorCoefficient_nonneg := H.errorCoefficient_nonneg
    error_bound := ?_ }
  intro x h hh hx hxh
  have hbound := H.error_bound x h hh hx hxh
  change qabs
      ((k * ((x + h) ^ (n + 1) / k) -
        k * (x ^ (n + 1) / k)) / h - k * x ^ n) <=
      qabs h * H.errorCoefficient at hbound
  have hcancel (z : Rat) : k * (z / k) = z := by
    rw [Rat.div_def]
    calc
      k * (z * k⁻¹) = k * (k⁻¹ * z) := by rw [Rat.mul_comm z]
      _ = (k * k⁻¹) * z := by rw [Rat.mul_assoc]
      _ = z := by rw [Rat.mul_inv_cancel k hk, Rat.one_mul]
  have hrewrite :
      (k * ((x + h) ^ (n + 1) / k) -
        k * (x ^ (n + 1) / k)) / h - k * x ^ n =
      ((x + h) ^ (n + 1) - x ^ (n + 1)) / h - k * x ^ n := by
    rw [hcancel ((x + h) ^ (n + 1)), hcancel (x ^ (n + 1))]
  rw [hrewrite] at hbound
  exact hbound

def monomial_hasDerivativeOnInterval
    (a b C : Rat) (n : Nat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (fun x => x ^ (n + 1)) a b)
      (FunctionOnInterval.exactRat
        (fun x => ((n + 1 : Nat) : Rat) * x ^ n) a b) :=
  (monomialSecantDerivativeBound C n hC1).toHasDerivativeOnInterval
    a b hleft hright

/-! The cubic is obtained from the normalized degree-two monomial by a
rational scalar.  This keeps its finite secant error and dyadic schedule in
the reusable monomial certificate instead of introducing a second hand-made
limit argument. -/
def cubeSecantDerivativeBound (C : Rat) (hC1 : 1 <= C) :
    SecantDerivativeBound C
      (fun x => x ^ 3)
      (fun x => 3 * x ^ 2) := by
  let H := SecantDerivativeBound.scaleRat 3
    (normalizedMonomialSecantBound C 2 hC1)
  refine {
    errorCoefficient := H.errorCoefficient
    errorCoefficient_nonneg := H.errorCoefficient_nonneg
    error_bound := ?_ }
  intro x h hh hx hxh
  have hbound := H.error_bound x h hh hx hxh
  have hthree : (3 : Rat) * (3 : Rat)⁻¹ = 1 := by decide +kernel
  simp only [Nat.reduceAdd] at hbound
  change qabs
      ((3 * ((x + h) ^ 3 / (3 : Rat)) -
        3 * (x ^ 3 / (3 : Rat))) / h - 3 * x ^ 2) <=
      qabs h * H.errorCoefficient at hbound
  have hrewrite :
      ((3 * ((x + h) ^ 3 / (3 : Rat)) -
          3 * (x ^ 3 / (3 : Rat))) / h - 3 * x ^ 2) =
        (((x + h) ^ 3 - x ^ 3) / h - 3 * x ^ 2) := by
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
      Rat.add_mul, Rat.sub_eq_add_neg]
  rw [hrewrite] at hbound
  exact hbound

def cube_hasDerivativeOnInterval
    (a b C : Rat) (hleft : -C <= a) (hright : b <= C)
    (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (fun x => x ^ 3) a b)
      (FunctionOnInterval.exactRat (fun x => 3 * x ^ 2) a b) :=
  (cubeSecantDerivativeBound C hC1).toHasDerivativeOnInterval
    a b hleft hright

/-- The degree-two Taylor prefix of exponential has the expected derivative
on every rational interval inside a bounded symmetric box.  This is the first
nontrivial finite Taylor polynomial assembled through the quantitative linear
interface, rather than by a separate hand-written quotient calculation. -/
def expTaylorQuadraticSecantBound (C : Rat) (hC1 : 1 <= C) :
    SecantDerivativeBound C expTaylorQuadratic (fun x => 1 + x) := by
  change SecantDerivativeBound C (fun x => 1 + x + x * x / 2) (fun x => 1 + x)
  have hinvone : ((1 : Rat)⁻¹) = 1 := by decide +kernel
  simpa [Rat.pow_succ, Rat.div_def, Rat.zero_add, Rat.mul_assoc, hinvone] using
    SecantDerivativeBound.add
      (SecantDerivativeBound.add
        (SecantDerivativeBound.constant C 1)
        (normalizedMonomialSecantBound C 0 hC1))
      (normalizedMonomialSecantBound C 1 hC1)

/-- The literal quadratic exponential prefix satisfies
`d/dx (1 + x + x^2/2) = 1 + x` in the project’s two-sided interval
finite-difference sense. -/
def expTaylorQuadratic_hasDerivativeOnInterval
    (a b C : Rat) (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat expTaylorQuadratic a b)
      (FunctionOnInterval.exactRat (fun x => 1 + x) a b) :=
  (expTaylorQuadraticSecantBound C hC1).toHasDerivativeOnInterval
    a b hleft hright

/-- The finite primitive prefix generated by rational derivative coefficients.
The `k`th coefficient contributes `c_k x^(k+1)/(k+1)`. -/
def integratedTaylorPrefix (coeffs : Nat -> Rat) : Nat -> Rat -> Rat
  | 0 => fun _x => 0
  | n + 1 => fun x =>
      integratedTaylorPrefix coeffs n x +
        coeffs n * (x ^ (n + 1) / ((n + 1 : Nat) : Rat))

/-! Finite order facts for positive Taylor coefficients.  These are purely
rational statements; they provide the range monotonicity needed to turn a
finite factorial prefix into a derivative box on a rational cell. -/

theorem integratedTaylorPrefix_mono_on_unit
    (coeffs : Nat -> Rat) (hcoeff : forall n, 0 <= coeffs n)
    (n : Nat) {x y : Rat}
    (hx : 0 <= x) (hy : y <= 1) (hxy : x <= y) :
    integratedTaylorPrefix coeffs n x <=
      integratedTaylorPrefix coeffs n y := by
  induction n with
  | zero => simp [integratedTaylorPrefix]
  | succ n ih =>
      simp only [integratedTaylorPrefix]
      have hpow : x ^ (n + 1) <= y ^ (n + 1) := by
        have hpow_all : ∀ m : Nat, x ^ m <= y ^ m := by
          intro m
          induction m with
          | zero => simp
          | succ m ihm =>
              have hleft : x ^ m * x <= y ^ m * x :=
                Rat.mul_le_mul_of_nonneg_right ihm hx
              have hright : y ^ m * x <= y ^ m * y :=
                Rat.mul_le_mul_of_nonneg_left hxy (Rat.pow_nonneg (by
                  exact Rat.le_trans hx hxy))
              calc
                x ^ (m + 1) = x ^ m * x := by rw [Rat.pow_succ]
                _ <= y ^ m * x := hleft
                _ <= y ^ m * y := hright
                _ = y ^ (m + 1) := by rw [Rat.pow_succ]
        exact hpow_all (n + 1)
      have hterm :
          coeffs n * (x ^ (n + 1) / ((n + 1 : Nat) : Rat)) <=
            coeffs n * (y ^ (n + 1) / ((n + 1 : Nat) : Rat)) := by
        have hden : 0 <= 1 / ((n + 1 : Nat) : Rat) := by
          exact Rat.le_of_lt (one_div_nat_pos (Nat.succ_pos n))
        rw [Rat.div_def, Rat.div_def]
        have hmul := Rat.mul_le_mul_of_nonneg_left hpow (hcoeff n)
        have hscaled := Rat.mul_le_mul_of_nonneg_right hmul hden
        simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm] using hscaled
      exact rat_add_le_add ih hterm

/-! A positive finite Taylor primitive contains its linear term.  This is a
finite substitute for the usual statement that a function with derivative at
least one is strictly increasing. -/
theorem integratedTaylorPrefix_succ_difference_ge
    (coeffs : Nat -> Rat) (hcoeff : forall n, 0 <= coeffs n)
    (hzero : 1 <= coeffs 0) (n : Nat) {x y : Rat}
    (hx : 0 <= x) (hy : y <= 1) (hxy : x <= y) :
    y - x <=
      integratedTaylorPrefix coeffs (n + 1) y -
        integratedTaylorPrefix coeffs (n + 1) x := by
  induction n with
  | zero =>
      have hdiff :
          integratedTaylorPrefix coeffs (0 + 1) y -
              integratedTaylorPrefix coeffs (0 + 1) x =
            coeffs 0 * (y - x) := by
        simp [integratedTaylorPrefix, Rat.pow_succ, Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
      rw [hdiff]
      have hnonneg : 0 <= y - x := by grind
      have hmul := Rat.mul_le_mul_of_nonneg_right hzero hnonneg
      grind
  | succ n ih =>
      have hpow : x ^ (n + 2) <= y ^ (n + 2) := by
        have hpow_all : ∀ m : Nat, x ^ m <= y ^ m := by
          intro m
          induction m with
          | zero => simp
          | succ m ihm =>
              have hleft : x ^ m * x <= y ^ m * x :=
                Rat.mul_le_mul_of_nonneg_right ihm hx
              have hright : y ^ m * x <= y ^ m * y :=
                Rat.mul_le_mul_of_nonneg_left hxy (Rat.pow_nonneg (by
                  exact Rat.le_trans hx hxy))
              calc
                x ^ (m + 1) = x ^ m * x := by rw [Rat.pow_succ]
                _ <= y ^ m * x := hleft
                _ <= y ^ m * y := hright
                _ = y ^ (m + 1) := by rw [Rat.pow_succ]
        exact hpow_all (n + 2)
      have hden : 0 <= 1 / ((n + 2 : Nat) : Rat) := by
        exact Rat.le_of_lt (one_div_nat_pos (by omega))
      have hpowdiv :
          x ^ (n + 2) / ((n + 2 : Nat) : Rat) <=
            y ^ (n + 2) / ((n + 2 : Nat) : Rat) := by
        rw [Rat.div_def, Rat.div_def]
        have hmul := Rat.mul_le_mul_of_nonneg_right hpow hden
        simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm] using hmul
      have hterm :
          coeffs (n + 1) *
              (y ^ (n + 2) / ((n + 2 : Nat) : Rat) -
                x ^ (n + 2) / ((n + 2 : Nat) : Rat)) >= 0 := by
        have hdiff : 0 <=
            y ^ (n + 2) / ((n + 2 : Nat) : Rat) -
              x ^ (n + 2) / ((n + 2 : Nat) : Rat) := by grind
        exact Rat.mul_nonneg (hcoeff (n + 1)) hdiff
      have hdecomp :
          integratedTaylorPrefix coeffs (n + 2) y -
              integratedTaylorPrefix coeffs (n + 2) x =
            (integratedTaylorPrefix coeffs (n + 1) y -
              integratedTaylorPrefix coeffs (n + 1) x) +
              coeffs (n + 1) *
                (y ^ (n + 2) / ((n + 2 : Nat) : Rat) -
                  x ^ (n + 2) / ((n + 2 : Nat) : Rat)) := by
        simp only [integratedTaylorPrefix]
        grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]
      rw [hdecomp]
      simpa [Nat.add_assoc] using (Rat.le_trans ih (by grind :
        integratedTaylorPrefix coeffs (n + 1) y -
            integratedTaylorPrefix coeffs (n + 1) x <=
          integratedTaylorPrefix coeffs (n + 1) y -
            integratedTaylorPrefix coeffs (n + 1) x +
              coeffs (n + 1) *
                (y ^ (n + 2) / ((n + 2 : Nat) : Rat) -
                  x ^ (n + 2) / ((n + 2 : Nat) : Rat))))

/-- The finite endpoint contribution of the next integrated Taylor monomial.

This is the exact rational FTC recurrence for a finite polynomial primitive:
the endpoint difference of the extended prefix is the previous endpoint
difference plus the new monomial's endpoint difference.  No limiting integral
or completed real is involved. -/
theorem integratedTaylorPrefix_endpointDifference_succ
    (coeffs : Nat -> Rat) (n : Nat) (a b : Rat) :
    integratedTaylorPrefix coeffs (n + 1) b -
        integratedTaylorPrefix coeffs (n + 1) a =
      (integratedTaylorPrefix coeffs n b -
        integratedTaylorPrefix coeffs n a) +
        coeffs n *
          (b ^ (n + 1) / ((n + 1 : Nat) : Rat) -
            a ^ (n + 1) / ((n + 1 : Nat) : Rat)) := by
  simp only [integratedTaylorPrefix]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

/-! The folded form is the public finite termwise-integration theorem.  The
recurrence above is convenient for induction; this sum is the form consumed
by power-series and quadrature code. -/

def finiteMonomialIntegralSum (coeffs : Nat -> Rat) (terms : Nat)
    (a b : Rat) : Rat :=
  match terms with
  | 0 => 0
  | n + 1 =>
      finiteMonomialIntegralSum coeffs n a b +
        coeffs n *
          (b ^ (n + 1) / ((n + 1 : Nat) : Rat) -
            a ^ (n + 1) / ((n + 1 : Nat) : Rat))

theorem integratedTaylorPrefix_endpointDifference_eq_finiteMonomialIntegralSum
    (coeffs : Nat -> Rat) (terms : Nat) (a b : Rat) :
    integratedTaylorPrefix coeffs terms b -
        integratedTaylorPrefix coeffs terms a =
      finiteMonomialIntegralSum coeffs terms a b := by
  induction terms with
  | zero =>
      simp [integratedTaylorPrefix, finiteMonomialIntegralSum]
      grind [Rat.sub_eq_add_neg]
  | succ n ih =>
      rw [integratedTaylorPrefix_endpointDifference_succ,
        finiteMonomialIntegralSum, ih]

theorem finiteMonomialIntegralSum_succ
    (coeffs : Nat -> Rat) (terms : Nat) (a b : Rat) :
    finiteMonomialIntegralSum coeffs (terms + 1) a b =
      finiteMonomialIntegralSum coeffs terms a b +
        coeffs terms *
          (b ^ (terms + 1) / ((terms + 1 : Nat) : Rat) -
            a ^ (terms + 1) / ((terms + 1 : Nat) : Rat)) := by
  rfl

/-- The corresponding finite derivative prefix `sum_{k<n} c_k x^k`. -/
def taylorDerivativePrefix (coeffs : Nat -> Rat) : Nat -> Rat -> Rat
  | 0 => fun _x => 0
  | n + 1 => fun x =>
      taylorDerivativePrefix coeffs n x + coeffs n * x ^ n

/-- The finite polynomial formed from the first `terms` coefficients of a
formal Taylor stream.

The constant coefficient is retained explicitly; all higher terms are the
finite primitive of the stream's algebraic coefficient shift.  Thus this is
only rational polynomial evaluation, even when `coeffs` later belongs to an
infinite series. -/
def taylorPrefix (coeffs : FormalPowerSeries.Coeffs) : Nat -> Rat -> Rat
  | 0 => fun _x => 0
  | terms + 1 => fun x =>
      coeffs 0 +
        integratedTaylorPrefix
          (FormalPowerSeries.coefficientShift coeffs) terms x

/-- Adding one coefficient to a finite Taylor prefix adds precisely the
corresponding rational monomial.  This is the finite cancellation which
connects the integrated coefficient-shift presentation with the familiar
polynomial `sum_{k < terms} c_k x^k`; no infinite series is involved. -/
theorem taylorPrefix_succ (coeffs : FormalPowerSeries.Coeffs)
    (terms : Nat) (x : Rat) :
    taylorPrefix coeffs (terms + 1) x =
      taylorPrefix coeffs terms x + coeffs terms * x ^ terms := by
  cases terms with
  | zero =>
      simp [taylorPrefix, integratedTaylorPrefix, Rat.add_comm]
  | succ terms =>
      have hpos : 0 < (((terms + 1 : Nat) : Rat)) :=
        (Rat.natCast_pos).2 (Nat.succ_pos terms)
      have hne : ((terms + 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hpos
      simp only [taylorPrefix, integratedTaylorPrefix,
        FormalPowerSeries.coefficientShift]
      rw [Rat.div_def]
      have hcancel : ((terms + 1 : Nat) : Rat) *
          ((terms + 1 : Nat) : Rat)⁻¹ = 1 :=
        Rat.mul_inv_cancel _ hne
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-- The finite coefficient-shift polynomial paired with `taylorPrefix`.
For `terms + 1`, it is the literal derivative polynomial of the displayed
finite prefix; no statement about an infinite tail is made here. -/
def taylorPrefixShift (coeffs : FormalPowerSeries.Coeffs) : Nat -> Rat -> Rat
  | 0 => fun _x => 0
  | terms + 1 =>
      taylorDerivativePrefix (FormalPowerSeries.coefficientShift coeffs) terms

/-- The recursively presented finite Taylor prefix is the literal finite
coefficient sum.  This lets a coefficient-shift identity identify a finite
Taylor--Lagrange derivative with the next finite prefix without making any
claim about the omitted tail. -/
theorem taylorPrefix_eq_taylorDerivativePrefix
    (coeffs : FormalPowerSeries.Coeffs) :
    forall terms x,
      taylorPrefix coeffs terms x = taylorDerivativePrefix coeffs terms x
  | 0, _x => rfl
  | terms + 1, x => by
      rw [taylorPrefix_succ, taylorDerivativePrefix]
      rw [taylorPrefix_eq_taylorDerivativePrefix coeffs terms x]

/-- A checked coefficient-shift relation identifies the derivative of a
finite prefix with the equally truncated target coefficient stream.  The
extra source coefficient is necessary: differentiating a degree-`terms`
prefix leaves `terms` target coefficients. -/
theorem taylorPrefixShift_succ_eq_of_coefficientShift
    {source target : FormalPowerSeries.Coeffs}
    (hshift : FormalPowerSeries.HasCoefficientShift source target)
    (terms : Nat) (x : Rat) :
    taylorPrefixShift source (terms + 1) x = taylorPrefix target terms x := by
  unfold FormalPowerSeries.HasCoefficientShift at hshift
  rw [taylorPrefixShift, hshift]
  exact (taylorPrefix_eq_taylorDerivativePrefix target terms x).symm

/-- A finite Taylor polynomial centered at the rational point `a`.

The coefficient stream remains the usual stream in powers of `(x - a)`, so
the linear coefficient has the same local meaning at every rational center. -/
def taylorPrefixAt (a : Rat) (coeffs : FormalPowerSeries.Coeffs)
    (terms : Nat) (x : Rat) : Rat :=
  taylorPrefix coeffs terms (x - a)

/-- The coefficient-shift polynomial paired with `taylorPrefixAt`. -/
def taylorPrefixShiftAt (a : Rat) (coeffs : FormalPowerSeries.Coeffs)
    (terms : Nat) (x : Rat) : Rat :=
  taylorPrefixShift coeffs terms (x - a)

/-- At the basepoint, every nonconstant finite derivative prefix is its
constant coefficient.  This elementary identity is the exact algebraic core
of reading the linear Taylor coefficient as the slope at zero. -/
theorem taylorDerivativePrefix_at_zero (coeffs : Nat -> Rat) (terms : Nat) :
    taylorDerivativePrefix coeffs (terms + 1) 0 = coeffs 0 := by
  induction terms with
  | zero =>
      change 0 + coeffs 0 * 0 ^ 0 = coeffs 0
      rw [Rat.pow_zero, Rat.mul_one]
      exact Rat.zero_add _
  | succ terms ih =>
      rw [taylorDerivativePrefix]
      change taylorDerivativePrefix coeffs (terms + 1) 0 +
          coeffs (terms + 1) * 0 ^ (terms + 1) = coeffs 0
      rw [ih, Rat.pow_succ, Rat.mul_zero, Rat.mul_zero]
      exact Rat.add_zero _

/-- For a finite Taylor prefix with at least a linear term, the certified
coefficient-shift derivative has value `c₁` at the basepoint.  The analytic
certificate itself is supplied below by `taylorPrefix_hasDerivativeOnInterval`;
this theorem records the value selected by the finite Lagrange remainder. -/
theorem taylorPrefixShift_at_zero (coeffs : FormalPowerSeries.Coeffs)
    (terms : Nat) :
    taylorPrefixShift coeffs (terms + 2) 0 = coeffs 1 := by
  rw [show terms + 2 = (terms + 1) + 1 by omega]
  rw [taylorPrefixShift, taylorDerivativePrefix_at_zero]
  simp [FormalPowerSeries.coefficientShift]

/-- The coefficient-shift polynomial of a finite Taylor expansion takes the
value `c₁` at its declared rational basepoint. -/
theorem taylorPrefixShiftAt_at_basepoint (a : Rat)
    (coeffs : FormalPowerSeries.Coeffs) (terms : Nat) :
    taylorPrefixShiftAt a coeffs (terms + 2) a = coeffs 1 := by
  unfold taylorPrefixShiftAt
  rw [Rat.sub_self]
  exact taylorPrefixShift_at_zero coeffs terms

/-- Every finite rational Taylor primitive carries an explicit secant bound.
The proof is structural: add the next normalized monomial, then scale it by
its rational coefficient. -/
def integratedTaylorPrefixSecantBound (C : Rat) (coeffs : Nat -> Rat)
    (hC1 : 1 <= C) : (n : Nat) ->
    SecantDerivativeBound C
      (integratedTaylorPrefix coeffs n)
      (taylorDerivativePrefix coeffs n)
  | 0 => SecantDerivativeBound.constant C 0
  | n + 1 => by
      let F := integratedTaylorPrefixSecantBound C coeffs hC1 n
      let G := SecantDerivativeBound.scaleRat (coeffs n)
        (normalizedMonomialSecantBound C n hC1)
      refine {
        errorCoefficient := F.errorCoefficient + G.errorCoefficient
        errorCoefficient_nonneg := Rat.add_nonneg
          F.errorCoefficient_nonneg G.errorCoefficient_nonneg
        error_bound := ?_ }
      intro x h hh hx hxh
      have hsum := (SecantDerivativeBound.add F G).error_bound
        x h hh hx hxh
      simpa [F, G, integratedTaylorPrefix, taylorDerivativePrefix,
        SecantDerivativeBound.add] using hsum

/-- The literal accumulated coefficient carried by
`integratedTaylorPrefixSecantBound`.  Publishing this finite recurrence lets
function-specific factorial streams prove one uniform majorant without
unfolding dependent structure transports. -/
def integratedTaylorPrefixSecantCoefficient (C : Rat)
    (coeffs : Nat -> Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 =>
      integratedTaylorPrefixSecantCoefficient C coeffs n +
        qabs (coeffs n) * powerSecantErrorBound C (n + 1)

theorem integratedTaylorPrefixSecantBound_errorCoefficient
    (C : Rat) (coeffs : Nat -> Rat) (hC1 : 1 <= C) :
    forall n : Nat,
      (integratedTaylorPrefixSecantBound C coeffs hC1 n).errorCoefficient =
        integratedTaylorPrefixSecantCoefficient C coeffs n
  | 0 => rfl
  | n + 1 => by
      rw [integratedTaylorPrefixSecantBound,
        integratedTaylorPrefixSecantCoefficient]
      change
        (integratedTaylorPrefixSecantBound C coeffs hC1 n).errorCoefficient +
            qabs (coeffs n) * powerSecantErrorBound C (n + 1) =
          integratedTaylorPrefixSecantCoefficient C coeffs n +
            qabs (coeffs n) * powerSecantErrorBound C (n + 1)
      rw [integratedTaylorPrefixSecantBound_errorCoefficient C coeffs hC1 n]

/-- A finite rational Taylor primitive has its literal finite coefficient
prefix as a two-sided interval derivative on every subinterval of `[-C,C]`. -/
def integratedTaylorPrefix_hasDerivativeOnInterval
    (coeffs : Nat -> Rat) (n : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (integratedTaylorPrefix coeffs n) a b)
      (FunctionOnInterval.exactRat (taylorDerivativePrefix coeffs n) a b) :=
  (integratedTaylorPrefixSecantBound C coeffs hC1 n).toHasDerivativeOnInterval
    a b hleft hright

/-! The finite Taylor primitive now exposes the same cell-level FTC contract
as the normalized monomial.  This is the direct termwise-integration API:
the derivative-prefix box, scaled by a positive cell width, contains the
primitive's finite endpoint increment. -/
theorem integratedTaylorPrefix_endpointDifference_contains_of_pos
    (coeffs : Nat -> Rat) (n : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C)
    {x h : Rat} {stage : Nat}
    (hx : inDomainInterval a b x)
    (hxh : inDomainInterval a b (x + h))
    (hpos : 0 < h)
    (hsmall : qabs h <=
      (1 / ((
        (integratedTaylorPrefix_hasDerivativeOnInterval
          coeffs n a b C hleft hright hC1).stepPrecision stage : Nat) : Rat))) :
    let D := integratedTaylorPrefix_hasDerivativeOnInterval
      coeffs n a b C hleft hright hC1
    (QInterval.scaleByRat h
      (QInterval.expand
        ((FunctionOnInterval.exactRat (taylorDerivativePrefix coeffs n) a b).compute
          x hx (D.evalPrecision x h stage))
        (2 * (precisionAtStage stage).val))).ContainsInterval
      (QInterval.subInterval
        ((FunctionOnInterval.exactRat (integratedTaylorPrefix coeffs n) a b).compute
          (x + h) hxh (D.evalPrecision x h stage))
        ((FunctionOnInterval.exactRat (integratedTaylorPrefix coeffs n) a b).compute
          x hx (D.evalPrecision x h stage))) := by
  let D := integratedTaylorPrefix_hasDerivativeOnInterval
    coeffs n a b C hleft hright hC1
  dsimp only
  exact HasDerivativeOnInterval.endpointDifference_contains_of_pos
    D hx hxh hx hpos hsmall

/-- Every finite Taylor prefix carries the explicit secant bound supplied by
its coefficient shift.  This is the reusable Taylor--Lagrange bridge for a
finite polynomial: the analytic-looking derivative claim is justified by a
rational `|h|` remainder coefficient. -/
def taylorPrefixSecantBound (C : Rat) (coeffs : FormalPowerSeries.Coeffs)
    (hC1 : 1 <= C) : (terms : Nat) ->
    SecantDerivativeBound C
      (taylorPrefix coeffs terms)
      (taylorPrefixShift coeffs terms)
  | 0 => SecantDerivativeBound.constant C 0
  | terms + 1 => by
      simpa [taylorPrefix, taylorPrefixShift, Rat.zero_add] using
        SecantDerivativeBound.add
          (SecantDerivativeBound.constant C (coeffs 0))
          (integratedTaylorPrefixSecantBound C
            (FormalPowerSeries.coefficientShift coeffs) hC1 terms)

/-- A finite Taylor coefficient prefix has its coefficient-shift polynomial
as a two-sided interval derivative on every rational subinterval of a
bounded symmetric box. -/
def taylorPrefix_hasDerivativeOnInterval
    (coeffs : FormalPowerSeries.Coeffs) (terms : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (taylorPrefix coeffs terms) a b)
      (FunctionOnInterval.exactRat (taylorPrefixShift coeffs terms) a b) :=
  (taylorPrefixSecantBound C coeffs hC1 terms).toHasDerivativeOnInterval
    a b hleft hright

/-- Finite sine coefficient prefixes satisfy the full interval derivative
interface with the equally truncated cosine coefficient prefix.  This is a
Taylor--Lagrange theorem for rational polynomials, not yet a derivative claim
for the tail-enclosed sine evaluator. -/
def sineTaylorPrefix_hasDerivativeOnInterval
    (terms : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat
        (taylorPrefix FormalPowerSeries.sinCoeff (terms + 1)) a b)
      (FunctionOnInterval.exactRat
        (taylorPrefix FormalPowerSeries.cosCoeff terms) a b) := by
  have h := taylorPrefix_hasDerivativeOnInterval
    FormalPowerSeries.sinCoeff (terms + 1) a b C hleft hright hC1
  have hrewrite : taylorPrefixShift FormalPowerSeries.sinCoeff (terms + 1) =
      taylorPrefix FormalPowerSeries.cosCoeff terms := by
    funext x
    exact taylorPrefixShift_succ_eq_of_coefficientShift
      FormalPowerSeries.sinCoeff_hasCoefficientShift terms x
  rw [hrewrite] at h
  exact h

/-- Finite cosine coefficient prefixes satisfy the corresponding negative
sine Taylor--Lagrange derivative certificate.  Keeping the target stream as
`-sin` makes the statement exact at every truncation order. -/
def cosineTaylorPrefix_hasDerivativeOnInterval
    (terms : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat
        (taylorPrefix FormalPowerSeries.cosCoeff (terms + 1)) a b)
      (FunctionOnInterval.exactRat
        (taylorPrefix (FormalPowerSeries.neg FormalPowerSeries.sinCoeff) terms) a b) := by
  have hshift : FormalPowerSeries.HasCoefficientShift
      FormalPowerSeries.cosCoeff
      (FormalPowerSeries.neg FormalPowerSeries.sinCoeff) := by
    unfold FormalPowerSeries.HasCoefficientShift
    simpa [FormalPowerSeries.derivative] using
      FormalPowerSeries.cosCoeff_derivative
  have h := taylorPrefix_hasDerivativeOnInterval
    FormalPowerSeries.cosCoeff (terms + 1) a b C hleft hright hC1
  have hrewrite : taylorPrefixShift FormalPowerSeries.cosCoeff (terms + 1) =
      taylorPrefix (FormalPowerSeries.neg FormalPowerSeries.sinCoeff) terms := by
    funext x
    exact taylorPrefixShift_succ_eq_of_coefficientShift hshift terms x
  rw [hrewrite] at h
  exact h

/-- The finite Taylor--Lagrange secant bound transports to any rational
expansion point.  The symmetric box is expressed in the local coordinate
`x - basepoint`. -/
def taylorPrefixAtSecantBound (C basepoint : Rat)
    (coeffs : FormalPowerSeries.Coeffs) (hC1 : 1 <= C) (terms : Nat) :
    CenteredSecantDerivativeBound basepoint C
      (taylorPrefixAt basepoint coeffs terms)
      (taylorPrefixShiftAt basepoint coeffs terms) := by
  change CenteredSecantDerivativeBound basepoint C
    (fun x => taylorPrefix coeffs terms (x - basepoint))
    (fun x => taylorPrefixShift coeffs terms (x - basepoint))
  exact SecantDerivativeBound.translate basepoint
    (taylorPrefixSecantBound C coeffs hC1 terms)

/-- A finite Taylor polynomial centered at any rational basepoint has the
coefficient-shift polynomial as its interval derivative.  Together with
`taylorPrefixShiftAt_at_basepoint`, this makes `c₁` an actual certified slope
at the point where the expansion is centered. -/
def taylorPrefixAt_hasDerivativeOnInterval
    (basepoint : Rat) (coeffs : FormalPowerSeries.Coeffs)
    (terms : Nat) (a b C : Rat)
    (hleft : -C <= a - basepoint) (hright : b - basepoint <= C)
    (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (taylorPrefixAt basepoint coeffs terms) a b)
      (FunctionOnInterval.exactRat (taylorPrefixShiftAt basepoint coeffs terms) a b) :=
  CenteredSecantDerivativeBound.toHasDerivativeOnInterval
    (taylorPrefixAtSecantBound C basepoint coeffs hC1 terms)
    a b hleft hright

/-- The ordinary finite factorial-series prefix for exponential. -/
def expTaylorPrefix (n : Nat) (x : Rat) : Rat :=
  1 + integratedTaylorPrefix FormalPowerSeries.expCoeff n x

theorem expTaylorPrefix_mono_on_unit
    (n : Nat) {x y : Rat}
    (hx : 0 <= x) (hy : y <= 1) (hxy : x <= y) :
    expTaylorPrefix n x <= expTaylorPrefix n y := by
  have hcoeff : forall k, 0 <= FormalPowerSeries.expCoeff k := by
    intro k
    unfold FormalPowerSeries.expCoeff
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2
      (RationalMajorant.factorialRat_pos k))
  unfold expTaylorPrefix
  exact rat_add_le_add (by rfl) (integratedTaylorPrefix_mono_on_unit
    FormalPowerSeries.expCoeff hcoeff n hx hy hxy)

/-- The factorial-series prefix one degree lower, the derivative of
`expTaylorPrefix n`. -/
def expTaylorDerivativePrefix (n : Nat) (x : Rat) : Rat :=
  taylorDerivativePrefix FormalPowerSeries.expCoeff n x

/-- Advancing the finite exponential prefix appends exactly its next
factorial monomial.  This finite recurrence is the shared algebra behind
uniform series boxes and their tail certificates. -/
theorem expTaylorPrefix_succ (n : Nat) (x : Rat) :
    expTaylorPrefix (n + 1) x = expTaylorPrefix n x +
      FormalPowerSeries.expCoeff n *
        (x ^ (n + 1) / ((n + 1 : Nat) : Rat)) := by
  unfold expTaylorPrefix
  rw [integratedTaylorPrefix]
  change 1 +
      (integratedTaylorPrefix FormalPowerSeries.expCoeff n x +
        FormalPowerSeries.expCoeff n * (x ^ (n + 1) / ((n + 1 : Nat) : Rat))) = _
  rw [Rat.add_assoc]

/-! The endpoint form of the finite exponential Taylor remainder recurrence.

When one factorial term is appended, its contribution to the endpoint
difference is exactly the corresponding rational monomial difference.  This
is the finite endpoint identity used before any tail or integral estimate is
introduced. -/
theorem expTaylorPrefix_endpointDifference_succ
    (n : Nat) (a b : Rat) :
    expTaylorPrefix (n + 1) b - expTaylorPrefix (n + 1) a =
      (expTaylorPrefix n b - expTaylorPrefix n a) +
        FormalPowerSeries.expCoeff n *
          (b ^ (n + 1) / ((n + 1 : Nat) : Rat) -
            a ^ (n + 1) / ((n + 1 : Nat) : Rat)) := by
  rw [expTaylorPrefix_succ, expTaylorPrefix_succ]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

/-- On a rational box, every factorial-series monomial is bounded by the
corresponding uniform factorial tail term.  This is the finite majorization
needed before attaching a common tail certificate to Taylor prefixes at
nearby inputs. -/
theorem qabs_expCoeff_monomial_le_factorialTailTerm
    {C x : Rat} (hC : 0 <= C) (hx : qabs x <= C) (n : Nat) :
    qabs (FormalPowerSeries.expCoeff n * x ^ n) <=
      RationalMajorant.factorialTailTerm C n := by
  have hcoeff : 0 <= FormalPowerSeries.expCoeff n := by
    unfold FormalPowerSeries.expCoeff
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 (RationalMajorant.factorialRat_pos n))
  have hpow : qabs (x ^ n) <= C ^ n :=
    RationalMajorant.qabs_pow_le_pow hC hx n
  calc
    qabs (FormalPowerSeries.expCoeff n * x ^ n) =
        FormalPowerSeries.expCoeff n * qabs (x ^ n) := by
          rw [qabs_mul, qabs_eq_self_of_nonneg hcoeff]
    _ <= FormalPowerSeries.expCoeff n * C ^ n :=
      Rat.mul_le_mul_of_nonneg_left hpow hcoeff
    _ = C ^ n / factorialRat n := by
      unfold FormalPowerSeries.expCoeff
      rw [Rat.div_def, Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = RationalMajorant.factorialTailTerm C n := rfl

/-! A finite absolute-value bound for the exponential primitive prefix.  This
is intentionally stated for an arbitrary nonnegative rational majorant: it
is useful on symmetric input boxes, where monotonicity of the prefix is not
available. -/

theorem qabs_integratedExpTaylorPrefix_le
    {C x : Rat} (hC : 0 <= C) (hx : qabs x <= C) :
    forall n,
      qabs (integratedTaylorPrefix FormalPowerSeries.expCoeff n x) <=
        RationalMajorant.factorialTailPartial C 1 n
  | 0 => by
      simp [integratedTaylorPrefix, RationalMajorant.factorialTailPartial,
        qabs_eq_self_of_nonneg]
  | n + 1 => by
      change qabs
        (integratedTaylorPrefix FormalPowerSeries.expCoeff n x +
          FormalPowerSeries.expCoeff n *
            (x ^ (n + 1) / ((n + 1 : Nat) : Rat))) <=
        RationalMajorant.factorialTailPartial C 1 n +
          RationalMajorant.factorialTailTerm C (1 + n)
      have hrewrite :
          FormalPowerSeries.expCoeff n *
              (x ^ (n + 1) / ((n + 1 : Nat) : Rat)) =
            FormalPowerSeries.expCoeff (n + 1) * x ^ (n + 1) := by
        unfold FormalPowerSeries.expCoeff
        rw [Rat.div_def]
        rw [FormalPowerSeries.factorialRat_succ]
        grind [Rat.mul_assoc, Rat.mul_comm]
      have hterm :
          qabs (FormalPowerSeries.expCoeff n *
            (x ^ (n + 1) / ((n + 1 : Nat) : Rat))) <=
            RationalMajorant.factorialTailTerm C (n + 1) := by
        rw [hrewrite]
        have hmon := qabs_expCoeff_monomial_le_factorialTailTerm
          (C := C) (x := x) hC hx (n + 1)
        simpa [RationalMajorant.factorialTailTerm] using hmon
      change qabs
        (integratedTaylorPrefix FormalPowerSeries.expCoeff n x +
          FormalPowerSeries.expCoeff n *
            (x ^ (n + 1) / ((n + 1 : Nat) : Rat))) <= _
      calc
        qabs
            (integratedTaylorPrefix FormalPowerSeries.expCoeff n x +
              FormalPowerSeries.expCoeff n *
                (x ^ (n + 1) / ((n + 1 : Nat) : Rat))) <=
            qabs (integratedTaylorPrefix FormalPowerSeries.expCoeff n x) +
              qabs (FormalPowerSeries.expCoeff n *
                (x ^ (n + 1) / ((n + 1 : Nat) : Rat))) :=
          qabs_add_le _ _
        _ <= RationalMajorant.factorialTailPartial C 1 n +
              RationalMajorant.factorialTailTerm C (1 + n) :=
          rat_add_le_add (qabs_integratedExpTaylorPrefix_le hC hx n)
            (by simpa [Nat.add_comm] using hterm)
        _ = RationalMajorant.factorialTailPartial C 1 (n + 1) := by
          simp [RationalMajorant.factorialTailPartial]

/-- The accumulated finite secant coefficient for an exponential Taylor
prefix on `[-2,2]`.  This is a finite rational recurrence: its `n`th step is
the normalized-monomial secant coefficient weighted by `1/n!`. -/
def expTaylorPrefixSecantCoefficient : Nat -> Rat
  | 0 => 0
  | n + 1 =>
      expTaylorPrefixSecantCoefficient n +
        qabs (FormalPowerSeries.expCoeff n) * powerSecantErrorBound 2 (n + 1)

private theorem powerSecantErrorBound_two_closed (n : Nat) :
    powerSecantErrorBound 2 (n + 2) =
      ((n + 2 : Nat) : Rat) * ((n + 1 : Nat) : Rat) * (2 : Rat) ^ n := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, powerSecantErrorBound, ih,
        Rat.pow_succ]
      have hn2 : (((n + 2 : Nat) : Rat)) = (n : Rat) + 2 := by
        exact_mod_cast (by omega : n + 2 = n + 2)
      have hn3 : (((n + 3 : Nat) : Rat)) = (n : Rat) + 3 := by
        exact_mod_cast (by omega : n + 3 = n + 3)
      have hn1 : (((n + 1 : Nat) : Rat)) = (n : Rat) + 1 := by
        exact_mod_cast (by omega : n + 1 = n + 1)
      rw [hn1, hn2, hn3]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

private theorem expTaylorPrefixSecantCoefficient_summand (n : Nat) :
    qabs (FormalPowerSeries.expCoeff (n + 2)) *
        powerSecantErrorBound 2 (n + 3) =
      2 * RationalMajorant.factorialTailTerm 2 n +
        2 * RationalMajorant.factorialTailTerm 2 (n + 1) := by
  rw [powerSecantErrorBound_two_closed (n + 1)]
  have hnonneg : (0 : Rat) <= FormalPowerSeries.expCoeff (n + 2) := by
    unfold FormalPowerSeries.expCoeff
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2
      (RationalMajorant.factorialRat_pos _))
  rw [qabs_eq_self_of_nonneg hnonneg]
  unfold FormalPowerSeries.expCoeff RationalMajorant.factorialTailTerm
  rw [FormalPowerSeries.factorialRat_succ,
    FormalPowerSeries.factorialRat_succ, Rat.pow_succ]
  have hcast2 : (((n + 1 + 1 : Nat) : Rat)) = ((n + 2 : Nat) : Rat) := by
    exact_mod_cast (by omega : n + 1 + 1 = n + 2)
  have hcast3 : (((n + 1 + 2 : Nat) : Rat)) = ((n + 3 : Nat) : Rat) := by
    exact_mod_cast (by omega : n + 1 + 2 = n + 3)
  rw [hcast2, hcast3, Rat.div_def, Rat.div_def, Rat.div_def,
    Rat.inv_mul_rev, Rat.inv_mul_rev]
  have hp1 : ((n + 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt
    ((Rat.natCast_pos).2 (Nat.succ_pos n))
  have hp2 : ((n + 2 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt
    ((Rat.natCast_pos).2 (by omega))
  have hcancel1 : ((n + 1 : Nat) : Rat) * ((n + 1 : Nat) : Rat)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hp1
  have hcancel2 : ((n + 2 : Nat) : Rat) * ((n + 2 : Nat) : Rat)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hp2
  grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

private theorem expTaylorPrefixSecantCoefficient_eq_factorialTailPartials
    (n : Nat) :
    expTaylorPrefixSecantCoefficient (n + 2) =
      2 + 2 * RationalMajorant.factorialTailPartial 2 0 n +
        2 * RationalMajorant.factorialTailPartial 2 1 n := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega,
        expTaylorPrefixSecantCoefficient, ih,
        expTaylorPrefixSecantCoefficient_summand]
      rw [RationalMajorant.factorialTailPartial,
        RationalMajorant.factorialTailPartial]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

private theorem factorialTailPartial_two_one_le_eight (n : Nat) :
    RationalMajorant.factorialTailPartial 2 1 n <= 8 := by
  have hsplit := RationalMajorant.factorialTailPartial_add 2 0 1 n
  have hsplit' : RationalMajorant.factorialTailPartial 2 0 (n + 1) =
      RationalMajorant.factorialTailPartial 2 0 1 +
        RationalMajorant.factorialTailPartial 2 1 n := by
    simpa [Nat.add_comm] using hsplit
  have hone : RationalMajorant.factorialTailPartial 2 0 1 = 1 := by
    decide +kernel
  calc
    RationalMajorant.factorialTailPartial 2 1 n =
        0 + RationalMajorant.factorialTailPartial 2 1 n := by
          rw [Rat.zero_add]
    _ <= 1 + RationalMajorant.factorialTailPartial 2 1 n :=
      rat_add_le_add (by decide +kernel) (Rat.le_refl)
    _ = RationalMajorant.factorialTailPartial 2 0 (n + 1) := by
      rw [hsplit', hone]
    _ <= 8 := RationalMajorant.factorialTailPartial_two_le_eight (n + 1)

/-- The finite secant coefficient of every factorial exponential prefix is
bounded by the same rational constant on `[-2,2]`.  The proof is a finite
factorial-series computation, not an appeal to a completed exponential. -/
theorem expTaylorPrefixSecantCoefficient_le_thirty_four (terms : Nat) :
    expTaylorPrefixSecantCoefficient terms <= 34 := by
  cases terms with
  | zero => decide +kernel
  | succ terms =>
      cases terms with
      | zero => decide +kernel
      | succ n =>
          rw [show n + 1 + 1 = n + 2 by omega,
            expTaylorPrefixSecantCoefficient_eq_factorialTailPartials]
          calc
            2 + 2 * RationalMajorant.factorialTailPartial 2 0 n +
                2 * RationalMajorant.factorialTailPartial 2 1 n <=
                2 + 2 * 8 + 2 * 8 := by
              apply rat_add_le_add
              · apply rat_add_le_add
                · exact Rat.le_refl
                · exact Rat.mul_le_mul_of_nonneg_left
                    (RationalMajorant.factorialTailPartial_two_le_eight n)
                    (by decide +kernel)
              · exact Rat.mul_le_mul_of_nonneg_left
                  (factorialTailPartial_two_one_le_eight n) (by decide +kernel)
            _ = 34 := by decide +kernel

/-- Every finite exponential Taylor prefix has a uniform, rational secant
remainder on `[-2,2]`.  This is the finite bridge needed to pass from the
common factorial schedule to an analytic derivative certificate. -/
theorem expTaylorPrefix_secant_error_le_coefficient
    {x h : Rat} (hh : h ≠ 0) (hx : qabs x <= 2)
    (hxh : qabs (x + h) <= 2) : forall terms : Nat,
    qabs
      ((expTaylorPrefix terms (x + h) - expTaylorPrefix terms x) / h -
        expTaylorDerivativePrefix terms x) <=
      qabs h * expTaylorPrefixSecantCoefficient terms := by
  intro terms
  induction terms with
  | zero =>
      simp only [expTaylorPrefix, integratedTaylorPrefix,
        expTaylorDerivativePrefix, taylorDerivativePrefix,
        expTaylorPrefixSecantCoefficient]
      rw [Rat.add_zero, Rat.sub_self, Rat.div_def, Rat.zero_mul,
        show (0 : Rat) - 0 = 0 by decide +kernel,
        qabs_eq_self_of_nonneg (by decide +kernel), Rat.mul_zero]
      exact Rat.le_refl
  | succ terms ih =>
      have hmono := qabs_normalized_power_differenceQuotient_sub_monomial_le
        (x := x) (h := h) (C := (2 : Rat)) hh (by decide +kernel)
          (by decide +kernel) hx hxh terms
      have hdecomp :
          ((expTaylorPrefix (terms + 1) (x + h) -
              expTaylorPrefix (terms + 1) x) / h -
            expTaylorDerivativePrefix (terms + 1) x) =
            (((expTaylorPrefix terms (x + h) - expTaylorPrefix terms x) / h -
                expTaylorDerivativePrefix terms x) +
              FormalPowerSeries.expCoeff terms *
                ((((x + h) ^ (terms + 1) / ((terms + 1 : Nat) : Rat) -
                    x ^ (terms + 1) / ((terms + 1 : Nat) : Rat)) / h) -
                  x ^ terms)) := by
        rw [expTaylorPrefix_succ, expTaylorPrefix_succ]
        change ((expTaylorPrefix terms (x + h) +
            FormalPowerSeries.expCoeff terms *
              ((x + h) ^ (terms + 1) / ((terms + 1 : Nat) : Rat)) -
            (expTaylorPrefix terms x +
              FormalPowerSeries.expCoeff terms *
                (x ^ (terms + 1) / ((terms + 1 : Nat) : Rat))) ) / h -
            (expTaylorDerivativePrefix terms x +
              FormalPowerSeries.expCoeff terms * x ^ terms)) = _
        rw [Rat.div_def]
        have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm]
      rw [hdecomp]
      let A : Rat := (expTaylorPrefix terms (x + h) -
        expTaylorPrefix terms x) / h - expTaylorDerivativePrefix terms x
      let B : Rat := (((x + h) ^ (terms + 1) / ((terms + 1 : Nat) : Rat) -
        x ^ (terms + 1) / ((terms + 1 : Nat) : Rat)) / h) - x ^ terms
      change qabs (A + FormalPowerSeries.expCoeff terms * B) <= _
      have htriangle : qabs (A + FormalPowerSeries.expCoeff terms * B) <=
          qabs A + qabs (FormalPowerSeries.expCoeff terms * B) :=
        qabs_add_le _ _
      rw [qabs_mul] at htriangle
      have hsum : qabs A + qabs (FormalPowerSeries.expCoeff terms) * qabs B <=
          qabs h * expTaylorPrefixSecantCoefficient terms +
            qabs (FormalPowerSeries.expCoeff terms) *
              (qabs h * powerSecantErrorBound 2 (terms + 1)) := by
        dsimp [A, B]
        exact rat_add_le_add ih
          (Rat.mul_le_mul_of_nonneg_left hmono (qabs_nonneg _))
      apply Rat.le_trans htriangle
      apply Rat.le_trans hsum
      simp only [expTaylorPrefixSecantCoefficient]
      grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]

/-- The preceding finite secant remainder with its coefficient replaced by
the uniform rational bound `34`. -/
theorem expTaylorPrefix_secant_error_le_thirty_four
    {x h : Rat} (hh : h ≠ 0) (hx : qabs x <= 2)
    (hxh : qabs (x + h) <= 2) (terms : Nat) :
    qabs
      ((expTaylorPrefix terms (x + h) - expTaylorPrefix terms x) / h -
        expTaylorDerivativePrefix terms x) <=
      qabs h * 34 := by
  have hfinite := expTaylorPrefix_secant_error_le_coefficient
    (x := x) (h := h) hh hx hxh terms
  calc
    qabs
        ((expTaylorPrefix terms (x + h) - expTaylorPrefix terms x) / h -
          expTaylorDerivativePrefix terms x) <=
        qabs h * expTaylorPrefixSecantCoefficient terms := hfinite
    _ <= qabs h * 34 := Rat.mul_le_mul_of_nonneg_left
      (expTaylorPrefixSecantCoefficient_le_thirty_four terms) (qabs_nonneg _)

/-- A finite factorial Taylor prefix for exponential has the expected
one-degree-lower prefix as its derivative. -/
def expTaylorPrefixSecantBound (C : Rat) (n : Nat) (hC1 : 1 <= C) :
    SecantDerivativeBound C (expTaylorPrefix n) (expTaylorDerivativePrefix n) := by
  change SecantDerivativeBound C
    (fun x => 1 + integratedTaylorPrefix FormalPowerSeries.expCoeff n x)
    (fun x => taylorDerivativePrefix FormalPowerSeries.expCoeff n x)
  simpa only [Rat.zero_add] using
    (SecantDerivativeBound.add
      (SecantDerivativeBound.constant C 1)
      (integratedTaylorPrefixSecantBound C FormalPowerSeries.expCoeff hC1 n))

/-- The finite factorial Taylor prefixes used by exponential satisfy the
two-sided interval derivative interface before the separately certified
factorial tail is attached. -/
def expTaylorPrefix_hasDerivativeOnInterval
    (n : Nat) (a b C : Rat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (expTaylorPrefix n) a b)
      (FunctionOnInterval.exactRat (expTaylorDerivativePrefix n) a b) :=
  (expTaylorPrefixSecantBound C n hC1).toHasDerivativeOnInterval
    a b hleft hright

end FinitePolynomial

end ComputableAnalysis


