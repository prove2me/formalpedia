-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteQuadratureComparison
-- name    : liuyao_ca_fd889115_k1_Analysis_FiniteQuadratureComparison
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:55:58.717826+00:00
-- url     : https://prove2.me/theorems/79916162-32e1-4367-a5c7-a050798d70f8
-- title:
--   Computable analysis · FiniteQuadratureComparison · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FiniteQuadratureComparison.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Calculus
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FinitePolynomialCalculus

set_option autoImplicit true

/-!
# Finite sampled Darboux comparison

This module isolates the finite algebra needed to compare a sampled rational
quadrature sum with a separately certified candidate value.  A cell records a
rational sample and a rational range box for one particular rational function.
No integral functional, measurable function, or limiting argument is used.

The main comparison says that two points enclosed by the same finite Darboux
sum differ by at most its width.  That width is exactly the sum of
`cell width * range-box width`, so later function-specific integral
certificates can use the result without changing the computational foundation.

The final section keeps the same finite algebra for interval-valued special
functions: a common evaluator stage and full raw point-box containment replace
the assumption that the function itself is rational-valued.
-/

namespace ComputableAnalysis

/-! ## Midpoint rectangles from a quantitative finite secant certificate

The following construction is independent of Darboux range selection.  A
`SecantDerivativeBound` for a rational primitive controls the two half-cell
secants based at the midpoint.  Their finite sum controls the difference
between the exact primitive increment and the midpoint rectangle. -/

namespace FinitePolynomial.SecantDerivativeBound

theorem qabs_endpointDifference_sub_midpointRectangle_le
    {C : Rat} {primitive derivative : Rat -> Rat}
    (D : FinitePolynomial.SecantDerivativeBound C primitive derivative)
    {lower upper : Rat}
    (hlower : qabs lower <= C) (hupper : qabs upper <= C)
    (hordered : lower <= upper) :
    let I : QInterval := { lo := lower, hi := upper }
    qabs ((primitive upper - primitive lower) -
      I.width * derivative I.midpoint) <=
      I.width ^ 2 * D.errorCoefficient := by
  let I : QInterval := { lo := lower, hi := upper }
  let w : Rat := I.width
  let midpoint : Rat := I.midpoint
  change qabs ((primitive upper - primitive lower) -
      w * derivative midpoint) <= w ^ 2 * D.errorCoefficient
  have hw0 : 0 <= w := by
    dsimp [w, I, QInterval.width]
    grind [Rat.sub_eq_add_neg]
  by_cases hw : w = 0
  · have hlu : lower = upper := by
      dsimp [w, I, QInterval.width] at hw
      grind [Rat.sub_eq_add_neg]
    subst upper
    rw [hw]
    rw [Rat.zero_mul]
    change qabs (primitive lower - primitive lower - 0) <=
      0 ^ 2 * D.errorCoefficient
    have hz : primitive lower - primitive lower - 0 = 0 := by grind
    rw [hz, qabs_eq_self_of_nonneg (by decide +kernel)]
    have hpow : (0 : Rat) ^ 2 = 0 := by decide +kernel
    rw [hpow, Rat.zero_mul]
    exact Rat.le_refl
  · have hwne' : 0 ≠ w := by
      intro hzero
      exact hw hzero.symm
    have hwpos : 0 < w := (Rat.lt_iff_le_and_ne).2 ⟨hw0, hwne'⟩
    let half : Rat := w / 2
    have hhalfpos : 0 < half := by
      dsimp [half]
      rw [Rat.div_def]
      exact Rat.mul_pos hwpos ((Rat.inv_pos).2 (by decide +kernel))
    have hhalfne : half ≠ 0 := Rat.ne_of_gt hhalfpos
    have hmidplus : midpoint + half = upper := by
      dsimp [midpoint, half, w, I, QInterval.midpoint, QInterval.width]
      grind [Rat.div_def]
    have hmidminus : midpoint + (-half) = lower := by
      dsimp [midpoint, half, w, I, QInterval.midpoint, QInterval.width]
      grind [Rat.div_def]
    have hmidbound : qabs midpoint <= C := by
      have hm := QInterval.midpoint_mem
        (I := ({ lo := lower, hi := upper } : QInterval)) hordered
      have hlowerNeg : -C <= lower := Rat.le_trans
        (Rat.neg_le_neg hlower) (neg_qabs_le_self lower)
      have hupperPos : upper <= C := Rat.le_trans
        (self_le_qabs upper) hupper
      exact qabs_le_of_neg_le_le
        (Rat.le_trans hlowerNeg hm.1)
        (Rat.le_trans hm.2 hupperPos)
    have hplus := D.error_bound midpoint half hhalfne hmidbound (by
      rw [hmidplus]
      exact hupper)
    have hminus := D.error_bound midpoint (-half) (by
      intro hzero
      apply hhalfne
      grind) hmidbound (by
      rw [hmidminus]
      exact hlower)
    have hhalfabs : qabs half = half :=
      qabs_eq_self_of_nonneg (Rat.le_of_lt hhalfpos)
    have hnegHalfAbs : qabs (-half) = half := by
      rw [qabs_neg, hhalfabs]
    rw [hmidplus, hhalfabs] at hplus
    rw [hmidminus, hnegHalfAbs] at hminus
    let eplus : Rat :=
      (primitive upper - primitive midpoint) / half - derivative midpoint
    let eminus : Rat :=
      (primitive lower - primitive midpoint) / (-half) - derivative midpoint
    have hplus' : qabs eplus <= half * D.errorCoefficient := by
      simpa [eplus] using hplus
    have hminus' : qabs eminus <= half * D.errorCoefficient := by
      simpa [eminus] using hminus
    have hhalfCancel : half * half⁻¹ = 1 :=
      Rat.mul_inv_cancel half hhalfne
    have hnegHalfNe : -half ≠ 0 := by
      intro hzero
      apply hhalfne
      grind
    have hnegHalfCancel : (-half) * (-half)⁻¹ = 1 :=
      Rat.mul_inv_cancel (-half) hnegHalfNe
    have hwTwo : w = half + half := by
      dsimp [half]
      grind [Rat.div_def]
    have hdecomp :
        (primitive upper - primitive lower) - w * derivative midpoint =
          half * eplus + half * eminus := by
      dsimp [eplus, eminus]
      rw [Rat.div_def, Rat.div_def]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm]
    rw [hdecomp]
    have hscaledPlus :
        qabs (half * eplus) <= half * (half * D.errorCoefficient) := by
      rw [qabs_mul, hhalfabs]
      exact Rat.mul_le_mul_of_nonneg_left hplus' (Rat.le_of_lt hhalfpos)
    have hscaledMinus :
        qabs (half * eminus) <= half * (half * D.errorCoefficient) := by
      rw [qabs_mul, hhalfabs]
      exact Rat.mul_le_mul_of_nonneg_left hminus' (Rat.le_of_lt hhalfpos)
    calc
      qabs (half * eplus + half * eminus) <=
          qabs (half * eplus) + qabs (half * eminus) :=
        qabs_add_le _ _
      _ <= half * (half * D.errorCoefficient) +
          half * (half * D.errorCoefficient) :=
        rat_add_le_add hscaledPlus hscaledMinus
      _ <= w ^ 2 * D.errorCoefficient := by
        have hhalf0 : 0 <= half := Rat.le_of_lt hhalfpos
        have hhalf_le_w : half <= w := by
          rw [hwTwo]
          grind
        have hscaled : half * D.errorCoefficient <=
            w * D.errorCoefficient :=
          Rat.mul_le_mul_of_nonneg_right hhalf_le_w
            D.errorCoefficient_nonneg
        calc
          half * (half * D.errorCoefficient) +
              half * (half * D.errorCoefficient) =
              w * (half * D.errorCoefficient) := by
            rw [hwTwo]
            grind [Rat.mul_add, Rat.mul_assoc]
          _ <= w * (w * D.errorCoefficient) :=
            Rat.mul_le_mul_of_nonneg_left hscaled hw0
          _ = w ^ 2 * D.errorCoefficient := by
            rw [show (2 : Nat) = 1 + 1 by omega,
              Rat.pow_succ, Rat.pow_succ]
            grind [Rat.mul_assoc]

/-- A right-endpoint rectangle has the same quadratic one-cell error budget.
This is the form needed after reversing a positive reciprocal partition: the
left endpoint in the reciprocal coordinate becomes the right endpoint in the
original coordinate. -/
theorem qabs_endpointDifference_sub_rightRectangle_le
    {C : Rat} {primitive derivative : Rat -> Rat}
    (D : FinitePolynomial.SecantDerivativeBound C primitive derivative)
    {lower upper : Rat}
    (hlower : qabs lower <= C) (hupper : qabs upper <= C)
    (hordered : lower <= upper) :
    let I : QInterval := { lo := lower, hi := upper }
    qabs ((primitive upper - primitive lower) -
      I.width * derivative upper) <=
      I.width ^ 2 * D.errorCoefficient := by
  let I : QInterval := { lo := lower, hi := upper }
  let w : Rat := I.width
  change qabs ((primitive upper - primitive lower) -
      w * derivative upper) <= w ^ 2 * D.errorCoefficient
  have hw0 : 0 <= w := by
    dsimp [w, I, QInterval.width]
    grind [Rat.sub_eq_add_neg]
  by_cases hw : w = 0
  · have hlu : lower = upper := by
      dsimp [w, I, QInterval.width] at hw
      grind [Rat.sub_eq_add_neg]
    subst upper
    rw [hw, Rat.zero_mul]
    have hz : primitive lower - primitive lower - 0 = 0 := by grind
    rw [hz, qabs_eq_self_of_nonneg (by decide +kernel)]
    have hpow : (0 : Rat) ^ 2 = 0 := by decide +kernel
    rw [hpow, Rat.zero_mul]
    exact Rat.le_refl
  · have hwne : w ≠ 0 := hw
    have hwne' : 0 ≠ w := by exact Ne.symm hwne
    have hwpos : 0 < w := (Rat.lt_iff_le_and_ne).2 ⟨hw0, hwne'⟩
    have hnegw : -w ≠ 0 := by
      intro hzero
      apply hwne
      grind
    have hstep : upper + (-w) = lower := by
      dsimp [w, I, QInterval.width]
      grind [Rat.sub_eq_add_neg]
    have hsecant := D.error_bound upper (-w) hnegw hupper (by
      rw [hstep]
      exact hlower)
    rw [hstep, qabs_neg, qabs_eq_self_of_nonneg hw0] at hsecant
    let e : Rat :=
      (primitive lower - primitive upper) / (-w) - derivative upper
    have he : qabs e <= w * D.errorCoefficient := by
      simpa [e] using hsecant
    have hcancel : w * (-w)⁻¹ = -1 := by
      have h := Rat.mul_inv_cancel (-w) hnegw
      grind [Rat.mul_assoc, Rat.mul_comm]
    have hdecomp :
        (primitive upper - primitive lower) - w * derivative upper =
          w * e := by
      dsimp [e]
      rw [Rat.div_def]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm]
    rw [hdecomp, qabs_mul, qabs_eq_self_of_nonneg hw0]
    calc
      w * qabs e <= w * (w * D.errorCoefficient) :=
        Rat.mul_le_mul_of_nonneg_left he hw0
      _ = w ^ 2 * D.errorCoefficient := by
        rw [show (2 : Nat) = 1 + 1 by omega,
          Rat.pow_succ, Rat.pow_succ]
        grind [Rat.mul_assoc]

end FinitePolynomial.SecantDerivativeBound

namespace RationalPartition

/-- The total rational midpoint-rectangle term at one partition index. -/
def midpointRectangleTerm {a b : Rat} (P : RationalPartition a b)
    (f : Rat -> Rat) (k : Nat) : Rat :=
  if hk : k < P.pieces then
    (P.cell k hk).width *
      f (((P.cell k hk).lower + (P.cell k hk).upper) / 2)
  else 0

/-- The finite midpoint action on a rational partition. -/
def midpointRectangleAction {a b : Rat} (P : RationalPartition a b)
    (f : Rat -> Rat) : Rat :=
  (List.range P.pieces).foldl
    (fun total k => total + P.midpointRectangleTerm f k) 0

/-- The total rational right-endpoint rectangle term at one partition index. -/
def rightRectangleTerm {a b : Rat} (P : RationalPartition a b)
    (f : Rat -> Rat) (k : Nat) : Rat :=
  if hk : k < P.pieces then
    (P.cell k hk).width * f (P.cell k hk).upper
  else 0

/-- The finite right-endpoint rectangle action on a rational partition. -/
def rightRectangleAction {a b : Rat} (P : RationalPartition a b)
    (f : Rat -> Rat) : Rat :=
  (List.range P.pieces).foldl
    (fun total k => total + P.rightRectangleTerm f k) 0

/-- The midpoint action restricted to the first `n` cells.  Keeping the
partial fold explicit makes the global error estimate a finite induction. -/
def midpointRectanglePrefix {a b : Rat} (P : RationalPartition a b)
    (f : Rat -> Rat) (n : Nat) : Rat :=
  (List.range n).foldl
    (fun total k => total + P.midpointRectangleTerm f k) 0

theorem midpointRectanglePrefix_zero {a b : Rat}
    (P : RationalPartition a b) (f : Rat -> Rat) :
    P.midpointRectanglePrefix f 0 = 0 := by
  rfl

theorem midpointRectanglePrefix_succ {a b : Rat}
    (P : RationalPartition a b) (f : Rat -> Rat) (n : Nat) :
    P.midpointRectanglePrefix f (n + 1) =
      P.midpointRectanglePrefix f n + P.midpointRectangleTerm f n := by
  simp [midpointRectanglePrefix, List.range_succ]

theorem midpointRectanglePrefix_last {a b : Rat}
    (P : RationalPartition a b) (f : Rat -> Rat) :
    P.midpointRectanglePrefix f P.pieces = P.midpointRectangleAction f := by
  rfl

/-- The right-endpoint action restricted to the first `n` cells. -/
def rightRectanglePrefix {a b : Rat} (P : RationalPartition a b)
    (f : Rat -> Rat) (n : Nat) : Rat :=
  (List.range n).foldl
    (fun total k => total + P.rightRectangleTerm f k) 0

theorem rightRectanglePrefix_zero {a b : Rat}
    (P : RationalPartition a b) (f : Rat -> Rat) :
    P.rightRectanglePrefix f 0 = 0 := by
  rfl

theorem rightRectanglePrefix_succ {a b : Rat}
    (P : RationalPartition a b) (f : Rat -> Rat) (n : Nat) :
    P.rightRectanglePrefix f (n + 1) =
      P.rightRectanglePrefix f n + P.rightRectangleTerm f n := by
  simp [rightRectanglePrefix, List.range_succ]

theorem rightRectanglePrefix_last {a b : Rat}
    (P : RationalPartition a b) (f : Rat -> Rat) :
    P.rightRectanglePrefix f P.pieces = P.rightRectangleAction f := by
  rfl

end RationalPartition

namespace FinitePolynomial.SecantDerivativeBound

/-- Summing the one-cell midpoint estimates gives an entirely finite
partition estimate.  Its error is the quadratic variation of the rational
breakpoint path times the secant certificate's coefficient. -/
theorem qabs_endpointDifference_sub_midpointRectanglePrefix_le
    {C a b : Rat} {primitive derivative : Rat -> Rat}
    (D : FinitePolynomial.SecantDerivativeBound C primitive derivative)
    (P : RationalPartition a b)
    (ha : qabs a <= C) (hb : qabs b <= C)
    (n : Nat) (hn : n <= P.pieces) :
    qabs ((primitive (P.point n) - primitive (P.point 0)) -
        P.midpointRectanglePrefix derivative n) <=
      quadraticVariationSum P.clampedPath P.clampedPath n *
        D.errorCoefficient := by
  have hpoint : forall i, i <= P.pieces -> qabs (P.point i) <= C := by
    intro i hi
    have hai : a <= P.point i := by
      have h := P.monotone 0 i (Nat.zero_le i) hi
      simpa [P.left_endpoint] using h
    have hib : P.point i <= b := by
      have h := P.monotone i P.pieces hi (Nat.le_refl P.pieces)
      simpa [P.right_endpoint] using h
    apply qabs_le_of_neg_le_le
    · exact Rat.le_trans
        (Rat.le_trans (Rat.neg_le_neg ha) (neg_qabs_le_self a)) hai
    · exact Rat.le_trans hib (Rat.le_trans (self_le_qabs b) hb)
  induction n with
  | zero =>
      simp [RationalPartition.midpointRectanglePrefix,
        quadraticVariationSum, Rat.sub_self,
        qabs_eq_self_of_nonneg (show (0 : Rat) <= 0 by decide +kernel)]
  | succ n ih =>
      have hnlt : n < P.pieces := Nat.lt_of_succ_le hn
      have hnle : n <= P.pieces := Nat.le_trans (Nat.le_succ n) hn
      have hlocal := D.qabs_endpointDifference_sub_midpointRectangle_le
        (hpoint n hnle) (hpoint (n + 1) hn)
        (P.monotone n (n + 1) (Nat.le_succ n) hn)
      have hterm :
          P.midpointRectangleTerm derivative n =
            (P.point (n + 1) - P.point n) *
              derivative ((P.point n + P.point (n + 1)) / 2) := by
        simp [RationalPartition.midpointRectangleTerm, hnlt,
          RationalPartition.cell, RationalSubinterval.width]
      have hlocal' :
          qabs ((primitive (P.point (n + 1)) - primitive (P.point n)) -
              P.midpointRectangleTerm derivative n) <=
            (P.point (n + 1) - P.point n) ^ 2 *
              D.errorCoefficient := by
        simpa [RationalPartition.cell, RationalSubinterval.width, hterm,
          QInterval.width, QInterval.midpoint] using hlocal
      have hclampn : P.clampedPath n = P.point n :=
        P.clampedPath_eq_point hnle
      have hclampsucc : P.clampedPath (n + 1) = P.point (n + 1) :=
        P.clampedPath_eq_point hn
      rw [RationalPartition.midpointRectanglePrefix_succ,
        quadraticVariationSum, hclampn, hclampsucc]
      have hdecomp :
          (primitive (P.point (n + 1)) - primitive (P.point 0)) -
              (P.midpointRectanglePrefix derivative n +
                P.midpointRectangleTerm derivative n) =
            ((primitive (P.point n) - primitive (P.point 0)) -
                P.midpointRectanglePrefix derivative n) +
              ((primitive (P.point (n + 1)) - primitive (P.point n)) -
                P.midpointRectangleTerm derivative n) := by
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      rw [hdecomp]
      calc
        qabs
            (((primitive (P.point n) - primitive (P.point 0)) -
                P.midpointRectanglePrefix derivative n) +
              ((primitive (P.point (n + 1)) - primitive (P.point n)) -
                P.midpointRectangleTerm derivative n)) <=
            qabs ((primitive (P.point n) - primitive (P.point 0)) -
                P.midpointRectanglePrefix derivative n) +
              qabs ((primitive (P.point (n + 1)) - primitive (P.point n)) -
                P.midpointRectangleTerm derivative n) := qabs_add_le _ _
        _ <= quadraticVariationSum P.clampedPath P.clampedPath n *
                D.errorCoefficient +
              (P.point (n + 1) - P.point n) ^ 2 *
                D.errorCoefficient :=
          rat_add_le_add (ih hnle) hlocal'
        _ = (quadraticVariationSum P.clampedPath P.clampedPath n +
              (P.point (n + 1) - P.point n) *
                (P.point (n + 1) - P.point n)) *
              D.errorCoefficient := by
          rw [show (2 : Nat) = 1 + 1 by omega, Rat.pow_succ, Rat.pow_succ]
          grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-- The full finite midpoint action compares with the primitive's endpoint
difference by the same rational quadratic-variation budget. -/
theorem qabs_endpointDifference_sub_midpointRectangleAction_le
    {C a b : Rat} {primitive derivative : Rat -> Rat}
    (D : FinitePolynomial.SecantDerivativeBound C primitive derivative)
    (P : RationalPartition a b)
    (ha : qabs a <= C) (hb : qabs b <= C) :
    qabs ((primitive b - primitive a) -
        P.midpointRectangleAction derivative) <=
      quadraticVariationSum P.clampedPath P.clampedPath P.pieces *
        D.errorCoefficient := by
  simpa [P.left_endpoint, P.right_endpoint,
    RationalPartition.midpointRectanglePrefix_last] using
    D.qabs_endpointDifference_sub_midpointRectanglePrefix_le P ha hb
      P.pieces (Nat.le_refl P.pieces)

/-- Summing the one-cell right-endpoint estimates gives an arbitrary-partition
error bound in terms of the rational breakpoint path's quadratic variation. -/
theorem qabs_endpointDifference_sub_rightRectanglePrefix_le
    {C a b : Rat} {primitive derivative : Rat -> Rat}
    (D : FinitePolynomial.SecantDerivativeBound C primitive derivative)
    (P : RationalPartition a b)
    (ha : qabs a <= C) (hb : qabs b <= C)
    (n : Nat) (hn : n <= P.pieces) :
    qabs ((primitive (P.point n) - primitive (P.point 0)) -
        P.rightRectanglePrefix derivative n) <=
      quadraticVariationSum P.clampedPath P.clampedPath n *
        D.errorCoefficient := by
  have hpoint : forall i, i <= P.pieces -> qabs (P.point i) <= C := by
    intro i hi
    have hai : a <= P.point i := by
      have h := P.monotone 0 i (Nat.zero_le i) hi
      simpa [P.left_endpoint] using h
    have hib : P.point i <= b := by
      have h := P.monotone i P.pieces hi (Nat.le_refl P.pieces)
      simpa [P.right_endpoint] using h
    apply qabs_le_of_neg_le_le
    · exact Rat.le_trans
        (Rat.le_trans (Rat.neg_le_neg ha) (neg_qabs_le_self a)) hai
    · exact Rat.le_trans hib (Rat.le_trans (self_le_qabs b) hb)
  induction n with
  | zero =>
      simp [RationalPartition.rightRectanglePrefix,
        quadraticVariationSum, Rat.sub_self,
        qabs_eq_self_of_nonneg (show (0 : Rat) <= 0 by decide +kernel)]
  | succ n ih =>
      have hnlt : n < P.pieces := Nat.lt_of_succ_le hn
      have hnle : n <= P.pieces := Nat.le_trans (Nat.le_succ n) hn
      have hlocal := D.qabs_endpointDifference_sub_rightRectangle_le
        (hpoint n hnle) (hpoint (n + 1) hn)
        (P.monotone n (n + 1) (Nat.le_succ n) hn)
      have hterm :
          P.rightRectangleTerm derivative n =
            (P.point (n + 1) - P.point n) * derivative (P.point (n + 1)) := by
        simp [RationalPartition.rightRectangleTerm, hnlt,
          RationalPartition.cell, RationalSubinterval.width]
      have hlocal' :
          qabs ((primitive (P.point (n + 1)) - primitive (P.point n)) -
              P.rightRectangleTerm derivative n) <=
            (P.point (n + 1) - P.point n) ^ 2 *
              D.errorCoefficient := by
        simpa [RationalPartition.cell, RationalSubinterval.width, hterm,
          QInterval.width] using hlocal
      have hclampn : P.clampedPath n = P.point n :=
        P.clampedPath_eq_point hnle
      have hclampsucc : P.clampedPath (n + 1) = P.point (n + 1) :=
        P.clampedPath_eq_point hn
      rw [RationalPartition.rightRectanglePrefix_succ,
        quadraticVariationSum, hclampn, hclampsucc]
      have hdecomp :
          (primitive (P.point (n + 1)) - primitive (P.point 0)) -
              (P.rightRectanglePrefix derivative n +
                P.rightRectangleTerm derivative n) =
            ((primitive (P.point n) - primitive (P.point 0)) -
                P.rightRectanglePrefix derivative n) +
              ((primitive (P.point (n + 1)) - primitive (P.point n)) -
                P.rightRectangleTerm derivative n) := by
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      rw [hdecomp]
      calc
        qabs
            (((primitive (P.point n) - primitive (P.point 0)) -
                P.rightRectanglePrefix derivative n) +
              ((primitive (P.point (n + 1)) - primitive (P.point n)) -
                P.rightRectangleTerm derivative n)) <=
            qabs ((primitive (P.point n) - primitive (P.point 0)) -
                P.rightRectanglePrefix derivative n) +
              qabs ((primitive (P.point (n + 1)) - primitive (P.point n)) -
                P.rightRectangleTerm derivative n) := qabs_add_le _ _
        _ <= quadraticVariationSum P.clampedPath P.clampedPath n *
                D.errorCoefficient +
              (P.point (n + 1) - P.point n) ^ 2 *
                D.errorCoefficient :=
          rat_add_le_add (ih hnle) hlocal'
        _ = (quadraticVariationSum P.clampedPath P.clampedPath n +
              (P.point (n + 1) - P.point n) *
                (P.point (n + 1) - P.point n)) *
              D.errorCoefficient := by
          rw [show (2 : Nat) = 1 + 1 by omega, Rat.pow_succ, Rat.pow_succ]
          grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-- The full finite right-endpoint action compares with the primitive's
endpoint difference by the same rational quadratic-variation budget. -/
theorem qabs_endpointDifference_sub_rightRectangleAction_le
    {C a b : Rat} {primitive derivative : Rat -> Rat}
    (D : FinitePolynomial.SecantDerivativeBound C primitive derivative)
    (P : RationalPartition a b)
    (ha : qabs a <= C) (hb : qabs b <= C) :
    qabs ((primitive b - primitive a) -
        P.rightRectangleAction derivative) <=
      quadraticVariationSum P.clampedPath P.clampedPath P.pieces *
        D.errorCoefficient := by
  simpa [P.left_endpoint, P.right_endpoint,
    RationalPartition.rightRectanglePrefix_last] using
    D.qabs_endpointDifference_sub_rightRectanglePrefix_le P ha hb
      P.pieces (Nat.le_refl P.pieces)

/-- On an equally spaced rational grid, quadratic variation is at most mesh
times interval length.  Hence a finite polynomial secant certificate supplies
an explicit, computable midpoint-rule error with no appeal to an integral. -/
theorem qabs_uniform_midpointRectangleAction_error_le
    {C a b : Rat} {primitive derivative : Rat -> Rat}
    (D : FinitePolynomial.SecantDerivativeBound C primitive derivative)
    (pieces : Nat) (hpieces : 0 < pieces) (hab : a <= b)
    (ha : qabs a <= C) (hb : qabs b <= C) :
    let P := RationalPartition.uniform a b pieces hpieces hab
    qabs ((primitive b - primitive a) -
        P.midpointRectangleAction derivative) <=
      (mesh a b pieces * (b - a)) * D.errorCoefficient := by
  let P := RationalPartition.uniform a b pieces hpieces hab
  have hfinite := D.qabs_endpointDifference_sub_midpointRectangleAction_le
    P ha hb
  have hvariation :
      quadraticVariationSum P.clampedPath P.clampedPath pieces <=
        mesh a b pieces * (b - a) := by
    have h := RationalPartition.uniform_clampedPath_quadraticVariation_le_mesh_mul_endpointDifference
        a b pieces hpieces hab P.clampedPath
        (RationalPartition.clampedPath_step_nonnegative P)
    change quadraticVariationSum P.clampedPath P.clampedPath pieces <=
      mesh a b pieces * (P.clampedPath pieces - P.clampedPath 0) at h
    rw [P.clampedPath_eq_point (Nat.le_refl pieces),
      P.clampedPath_eq_point (Nat.zero_le pieces)] at h
    have hpRight : P.point pieces = b := by
      have hpiecesEq : P.pieces = pieces := rfl
      rw [← hpiecesEq]
      exact P.right_endpoint
    rw [hpRight, P.left_endpoint] at h
    exact h
  exact Rat.le_trans hfinite
    (Rat.mul_le_mul_of_nonneg_right hvariation
      D.errorCoefficient_nonneg)

end FinitePolynomial.SecantDerivativeBound

/-- A rational point regarded as a degenerate interval. -/
def QInterval.pointInterval (x : Rat) : QInterval := { lo := x, hi := x }

namespace QInterval

theorem pointInterval_width (x : Rat) : (pointInterval x).width = 0 := by
  unfold pointInterval width
  grind

theorem addInterval_pointInterval (x y : Rat) :
    addInterval (pointInterval x) (pointInterval y) = pointInterval (x + y) := by
  rfl

theorem addInterval_fold_pointInterval (xs : List Nat) (term : Nat -> Rat)
    (initial : Rat) :
    xs.foldl (fun acc k => addInterval acc (pointInterval (term k)))
        (pointInterval initial) =
      pointInterval (xs.foldl (fun acc k => acc + term k) initial) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons k xs ih =>
      simp only [List.foldl, addInterval_pointInterval]
      exact ih (initial + term k)

/-- Any two rational points enclosed by one interval differ by at most that
interval's width. -/
theorem qabs_sub_le_width_of_contains_points {I : QInterval} {x y : Rat}
    (hx : I.ContainsInterval (pointInterval x))
    (hy : I.ContainsInterval (pointInterval y)) :
    qabs (x - y) <= I.width := by
  exact qabs_sub_le_of_common_bounds hx.1 hx.2 hy.1 hy.2

end QInterval

/-- A cellwise, function-specific finite range certificate.  The function is
only evaluated on rationals, and every datum in the certificate is finite. -/
structure SampledDarbouxCell (f : Rat -> Rat) (a b : Rat) where
  cell : RationalSubinterval a b
  sample : Rat
  sample_mem : cell.contains sample
  range : QInterval
  range_contains : forall x, cell.contains x ->
    range.lo <= f x /\ f x <= range.hi

namespace SampledDarbouxCell

variable {f : Rat -> Rat} {a b : Rat}

def width (C : SampledDarbouxCell f a b) : Rat := C.cell.width

def sampleTerm (C : SampledDarbouxCell f a b) : Rat := C.width * f C.sample

def darbouxBox (C : SampledDarbouxCell f a b) : QInterval :=
  C.cell.scaleBound C.range

theorem width_nonnegative (C : SampledDarbouxCell f a b) : 0 <= C.width := by
  unfold width RationalSubinterval.width
  have hordered := C.cell.ordered
  grind [Rat.sub_eq_add_neg]

theorem sample_mem_range (C : SampledDarbouxCell f a b) :
    C.range.lo <= f C.sample /\ f C.sample <= C.range.hi :=
  C.range_contains C.sample C.sample_mem

theorem range_width_nonnegative (C : SampledDarbouxCell f a b) :
    0 <= C.range.width := by
  have h := C.sample_mem_range
  unfold QInterval.width
  grind [Rat.sub_eq_add_neg]

/-- The Darboux box on one cell encloses its sampled rectangle. -/
theorem darbouxBox_contains_sampleTerm (C : SampledDarbouxCell f a b) :
    C.darbouxBox.ContainsInterval (QInterval.pointInterval C.sampleTerm) := by
  have hpoint : C.range.ContainsInterval
      (QInterval.pointInterval (f C.sample)) := C.sample_mem_range
  have hscaled := QInterval.scaleByRat_contains_of_nonneg C.width_nonnegative hpoint
  change (QInterval.scaleByRat C.width C.range).ContainsInterval
    (QInterval.pointInterval C.sampleTerm)
  simpa [sampleTerm, QInterval.scaleByRat, C.width_nonnegative,
    QInterval.pointInterval] using hscaled

theorem darbouxBox_width (C : SampledDarbouxCell f a b) :
    C.darbouxBox.width = C.width * C.range.width := by
  unfold darbouxBox RationalSubinterval.scaleBound
  exact QInterval.scaleByRat_width_of_nonneg C.width_nonnegative C.range

/-- The rational interval underlying a rational subinterval. -/
def cellInterval (C : RationalSubinterval a b) : QInterval :=
  { lo := C.lower, hi := C.upper }

theorem cellInterval_width (C : RationalSubinterval a b) :
    (cellInterval C).width = C.width := by
  rfl

/-- Turn a natural-valued Lipschitz certificate into a sampled midpoint cell.
The range is centered at the midpoint value and widened by `L * cell.width`.
The use of the full width, rather than half the width, keeps the proof free of
division-sensitive estimates while still giving a shrinking mesh rate. -/
def midpointOfLipschitzOnIntervalNat
    (C : RationalSubinterval a b) (L : Nat)
    (hlip : Integral.LipschitzOnIntervalNat f a b L) :
    SampledDarbouxCell f a b where
  cell := C
  sample := (cellInterval C).midpoint
  sample_mem := by
    exact QInterval.midpoint_mem C.ordered
  range :=
    { lo := f (cellInterval C).midpoint - (L : Rat) * C.width
      hi := f (cellInterval C).midpoint + (L : Rat) * C.width }
  range_contains := by
    intro x hx
    have hxDomain := C.contains_inDomain hx
    have hmidMem := QInterval.midpoint_mem (I := cellInterval C) C.ordered
    have hmidDomain := C.contains_inDomain hmidMem
    have hlipBound := hlip.2 x (cellInterval C).midpoint
      hxDomain.1 hxDomain.2 hmidDomain.1 hmidDomain.2
    have hdistance :
        qabs ((cellInterval C).midpoint - x) <= C.width := by
      rw [show (cellInterval C).midpoint - x =
        -(x - (cellInterval C).midpoint) by grind [Rat.sub_eq_add_neg],
        qabs_neg]
      have hdist := QInterval.qabs_sub_midpoint_le_width
        (I := cellInterval C) C.ordered hx.1 hx.2
      rw [cellInterval_width] at hdist
      exact hdist
    have hLnonnegative : 0 <= (L : Rat) := Rat.natCast_nonneg
    have herror : qabs (f x - f (cellInterval C).midpoint) <=
        (L : Rat) * C.width :=
      Rat.le_trans hlipBound
        (Rat.mul_le_mul_of_nonneg_left hdistance hLnonnegative)
    have hupper := Rat.le_trans (self_le_qabs
      (f x - f (cellInterval C).midpoint)) herror
    have hlower : f (cellInterval C).midpoint - f x <=
        (L : Rat) * C.width := by
      calc
        f (cellInterval C).midpoint - f x =
            -(f x - f (cellInterval C).midpoint) := by
          grind [Rat.sub_eq_add_neg]
        _ <= qabs (-(f x - f (cellInterval C).midpoint)) := self_le_qabs _
        _ = qabs (f x - f (cellInterval C).midpoint) := qabs_neg _
        _ <= (L : Rat) * C.width := herror
    constructor <;> grind [Rat.sub_eq_add_neg]

theorem midpointOfLipschitzOnIntervalNat_range_width
    (C : RationalSubinterval a b) (L : Nat)
    (hlip : Integral.LipschitzOnIntervalNat f a b L) :
    ((midpointOfLipschitzOnIntervalNat C L hlip).range).width =
      2 * (L : Rat) * C.width := by
  unfold midpointOfLipschitzOnIntervalNat QInterval.width
  grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]

end SampledDarbouxCell

namespace SampledDarbouxCells

variable {f : Rat -> Rat} {a b : Rat}

/-- The explicit rational sampled quadrature sum. -/
def sampledAction : List (SampledDarbouxCell f a b) -> Rat
  | [] => 0
  | C :: cells => C.sampleTerm + sampledAction cells

/-- The finite sum of the scaled cell range boxes. -/
def darbouxSum : List (SampledDarbouxCell f a b) -> QInterval
  | [] => QInterval.pointInterval 0
  | C :: cells => QInterval.addInterval C.darbouxBox (darbouxSum cells)

/-- Total width of the supplied finite cell list.  No disjointness or covering
claim is implicit in this definition. -/
def totalWidth : List (SampledDarbouxCell f a b) -> Rat
  | [] => 0
  | C :: cells => C.width + totalWidth cells

/-- Exact accumulated range uncertainty of the finite cell list. -/
def oscillationBudget : List (SampledDarbouxCell f a b) -> Rat
  | [] => 0
  | C :: cells => C.width * C.range.width + oscillationBudget cells

theorem darbouxSum_contains_sampledAction
    (cells : List (SampledDarbouxCell f a b)) :
    (darbouxSum cells).ContainsInterval
      (QInterval.pointInterval (sampledAction cells)) := by
  induction cells with
  | nil => exact QInterval.containsInterval_refl _
  | cons C cells ih =>
      simpa [darbouxSum, sampledAction, QInterval.addInterval_pointInterval] using
        QInterval.addInterval_contains C.darbouxBox_contains_sampleTerm ih

theorem darbouxSum_width
    (cells : List (SampledDarbouxCell f a b)) :
    (darbouxSum cells).width = oscillationBudget cells := by
  induction cells with
  | nil => simp [darbouxSum, oscillationBudget, QInterval.pointInterval_width]
  | cons C cells ih =>
      simp only [darbouxSum, oscillationBudget, QInterval.addInterval_width,
        C.darbouxBox_width, ih]

theorem totalWidth_nonnegative
    (cells : List (SampledDarbouxCell f a b)) : 0 <= totalWidth cells := by
  induction cells with
  | nil => simp [totalWidth]
  | cons C cells ih =>
      simp only [totalWidth]
      have hC := C.width_nonnegative
      grind

/-- A common cell-range oscillation bound gives the expected total-width
error estimate. -/
theorem oscillationBudget_le_totalWidth_mul
    (cells : List (SampledDarbouxCell f a b)) (oscillation : Rat)
    (hoscillation : forall C, C ∈ cells -> C.range.width <= oscillation) :
    oscillationBudget cells <= totalWidth cells * oscillation := by
  induction cells with
  | nil => simp [oscillationBudget, totalWidth]
  | cons C cells ih =>
      have hC : C.range.width <= oscillation := hoscillation C (by simp)
      have htail : forall D, D ∈ cells -> D.range.width <= oscillation := by
        intro D hD
        exact hoscillation D (List.mem_cons_of_mem C hD)
      have hmul := Rat.mul_le_mul_of_nonneg_left hC C.width_nonnegative
      have hrest := ih htail
      simp only [oscillationBudget, totalWidth]
      calc
        C.width * C.range.width + oscillationBudget cells <=
            C.width * oscillation + totalWidth cells * oscillation :=
          rat_add_le_add hmul hrest
        _ = (C.width + totalWidth cells) * oscillation := by
          grind [Rat.add_mul]

/-- If a candidate rational value is independently certified to lie in the
same finite Darboux sum as the sampled action, their difference is bounded by
the exact cellwise oscillation budget. -/
theorem qabs_candidate_sub_sampledAction_le
    (cells : List (SampledDarbouxCell f a b)) (candidate : Rat)
    (hcandidate : (darbouxSum cells).ContainsInterval
      (QInterval.pointInterval candidate)) :
    qabs (candidate - sampledAction cells) <= oscillationBudget cells := by
  rw [←darbouxSum_width cells]
  exact QInterval.qabs_sub_le_width_of_contains_points
    hcandidate (darbouxSum_contains_sampledAction cells)

theorem qabs_candidate_sub_sampledAction_le_totalWidth_mul
    (cells : List (SampledDarbouxCell f a b)) (candidate oscillation : Rat)
    (hcandidate : (darbouxSum cells).ContainsInterval
      (QInterval.pointInterval candidate))
    (hoscillation : forall C, C ∈ cells -> C.range.width <= oscillation) :
    qabs (candidate - sampledAction cells) <= totalWidth cells * oscillation :=
  Rat.le_trans (qabs_candidate_sub_sampledAction_le cells candidate hcandidate)
    (oscillationBudget_le_totalWidth_mul cells oscillation hoscillation)

end SampledDarbouxCells

/-! ## Rules carried by an actual rational partition -/

/-- A sampled Darboux rule whose cells are exactly the cells of one supplied
rational partition.  Unlike a bare list of cells, this records the covering
and adjacency data needed by later bounded-integral comparisons. -/
structure SampledDarbouxPartition (f : Rat -> Rat) {a b : Rat}
    (P : RationalPartition a b) where
  sample : (k : Nat) -> k < P.pieces -> Rat
  sample_mem : forall k (hk : k < P.pieces),
    (P.cell k hk).contains (sample k hk)
  range : (k : Nat) -> k < P.pieces -> QInterval
  range_contains : forall k (hk : k < P.pieces) x,
    (P.cell k hk).contains x ->
      (range k hk).lo <= f x /\ f x <= (range k hk).hi

namespace SampledDarbouxPartition

variable {f : Rat -> Rat} {a b : Rat} {P : RationalPartition a b}

/-- The sampled rectangle term, totalized by zero outside the finite cell
range so it can be folded over `List.range`. -/
def sampleTerm (R : SampledDarbouxPartition f P) (k : Nat) : Rat :=
  if hk : k < P.pieces then
    (P.cell k hk).width * f (R.sample k hk)
  else 0

def sampledAction (R : SampledDarbouxPartition f P) : Rat :=
  (List.range P.pieces).foldl (fun total k => total + R.sampleTerm k) 0

def darbouxSum (R : SampledDarbouxPartition f P) : QInterval :=
  P.boundIntegralSum R.range

theorem boundIntegralTerm_contains_sampleTerm
    (R : SampledDarbouxPartition f P) (k : Nat) :
    (P.boundIntegralTerm R.range k).ContainsInterval
      (QInterval.pointInterval (R.sampleTerm k)) := by
  by_cases hk : k < P.pieces
  · have hwidth : 0 <= (P.cell k hk).width := by
      unfold RationalSubinterval.width
      have hordered := (P.cell k hk).ordered
      grind [Rat.sub_eq_add_neg]
    have hsample := R.range_contains k hk (R.sample k hk) (R.sample_mem k hk)
    have hpoint : (R.range k hk).ContainsInterval
        (QInterval.pointInterval (f (R.sample k hk))) := hsample
    have hscaled := QInterval.scaleByRat_contains_of_nonneg hwidth hpoint
    simpa [RationalPartition.boundIntegralTerm, sampleTerm, hk,
      RationalSubinterval.scaleBound, QInterval.scaleByRat, hwidth,
      QInterval.pointInterval] using hscaled
  · simp [RationalPartition.boundIntegralTerm, sampleTerm, hk,
      QInterval.pointInterval, QInterval.ContainsInterval]

theorem darbouxSum_contains_sampledAction
    (R : SampledDarbouxPartition f P) :
    R.darbouxSum.ContainsInterval
      (QInterval.pointInterval R.sampledAction) := by
  have hfold := RationalPartition.addInterval_fold_contains
    (List.range P.pieces)
    (fun k => P.boundIntegralTerm R.range k)
    (fun k => QInterval.pointInterval (R.sampleTerm k))
    (outerInit := QInterval.pointInterval 0)
    (innerInit := QInterval.pointInterval 0)
    (QInterval.containsInterval_refl _)
    (R.boundIntegralTerm_contains_sampleTerm)
  unfold darbouxSum RationalPartition.boundIntegralSum sampledAction
  rw [QInterval.addInterval_fold_pointInterval] at hfold
  exact hfold

theorem qabs_candidate_sub_sampledAction_le_width
    (R : SampledDarbouxPartition f P) (candidate : Rat)
    (hcandidate : R.darbouxSum.ContainsInterval
      (QInterval.pointInterval candidate)) :
    qabs (candidate - R.sampledAction) <= R.darbouxSum.width :=
  QInterval.qabs_sub_le_width_of_contains_points
    hcandidate R.darbouxSum_contains_sampledAction

/-- The midpoint sampled rule on an explicit uniform rational partition,
constructed solely from a natural-valued Lipschitz certificate. -/
def uniformMidpoint (f : Rat -> Rat) (a b : Rat) (L pieces : Nat)
    (hpieces : 0 < pieces)
    (hlip : Integral.LipschitzOnIntervalNat f a b L) :
    SampledDarbouxPartition f
      (RationalPartition.uniform a b pieces hpieces hlip.1) where
  sample := fun k hk =>
    (SampledDarbouxCell.midpointOfLipschitzOnIntervalNat
      ((RationalPartition.uniform a b pieces hpieces hlip.1).cell k hk)
      L hlip).sample
  sample_mem := by
    intro k hk
    exact (SampledDarbouxCell.midpointOfLipschitzOnIntervalNat
      ((RationalPartition.uniform a b pieces hpieces hlip.1).cell k hk)
      L hlip).sample_mem
  range := fun k hk =>
    (SampledDarbouxCell.midpointOfLipschitzOnIntervalNat
      ((RationalPartition.uniform a b pieces hpieces hlip.1).cell k hk)
      L hlip).range
  range_contains := by
    intro k hk x hx
    exact (SampledDarbouxCell.midpointOfLipschitzOnIntervalNat
      ((RationalPartition.uniform a b pieces hpieces hlip.1).cell k hk)
      L hlip).range_contains x hx

theorem uniformMidpoint_range_width
    (f : Rat -> Rat) (a b : Rat) (L pieces : Nat)
    (hpieces : 0 < pieces)
    (hlip : Integral.LipschitzOnIntervalNat f a b L)
    (k : Nat) (hk : k < pieces) :
    ((uniformMidpoint f a b L pieces hpieces hlip).range k hk).width =
      2 * (L : Rat) * mesh a b pieces := by
  change
    ((SampledDarbouxCell.midpointOfLipschitzOnIntervalNat
      ((RationalPartition.uniform a b pieces hpieces hlip.1).cell k hk)
      L hlip).range).width = _
  rw [SampledDarbouxCell.midpointOfLipschitzOnIntervalNat_range_width,
    RationalPartition.uniform_cell_width a b pieces hpieces hlip.1 k hk]

/-- The uniform midpoint Darboux enclosure has an explicit first-order mesh
rate.  This is finite partition algebra; it does not assert a universal
integral for every Lipschitz function. -/
theorem uniformMidpoint_darbouxSum_width_le
    (f : Rat -> Rat) (a b : Rat) (L pieces : Nat)
    (hpieces : 0 < pieces)
    (hlip : Integral.LipschitzOnIntervalNat f a b L) :
    (uniformMidpoint f a b L pieces hpieces hlip).darbouxSum.width <=
      (b - a) * (2 * (L : Rat) * mesh a b pieces) := by
  unfold darbouxSum
  apply RationalPartition.uniform_boundIntegralSum_width_le
    pieces hpieces hlip.1 _ (2 * (L : Rat) * mesh a b pieces)
  intro k hk
  rw [uniformMidpoint_range_width f a b L pieces hpieces hlip k hk]
  exact Rat.le_refl

theorem uniformMidpoint_qabs_candidate_sub_sampledAction_le
    (f : Rat -> Rat) (a b : Rat) (L pieces : Nat)
    (hpieces : 0 < pieces)
    (hlip : Integral.LipschitzOnIntervalNat f a b L)
    (candidate : Rat)
    (hcandidate :
      (uniformMidpoint f a b L pieces hpieces hlip).darbouxSum.ContainsInterval
        (QInterval.pointInterval candidate)) :
    qabs (candidate -
      (uniformMidpoint f a b L pieces hpieces hlip).sampledAction) <=
        (b - a) * (2 * (L : Rat) * mesh a b pieces) :=
  Rat.le_trans
    ((uniformMidpoint f a b L pieces hpieces hlip
      ).qabs_candidate_sub_sampledAction_le_width candidate hcandidate)
    (uniformMidpoint_darbouxSum_width_le f a b L pieces hpieces hlip)

end SampledDarbouxPartition

/-! ## Common-stage rules for interval-valued functions -/

/-- A sampled Darboux rule for a rationally indexed family of raw real
computations.  Every cell range encloses the full point box at one explicit
common evaluator stage.  `sampleValue` is a rational point certified inside
the raw box at the chosen sample; consequently the finite sampled sum is still
an executable rational number.

This is the seam needed for special functions such as exponential: it does not
select a completed real value and it does not assert a universal integral. -/
structure SampledRawDarbouxPartition (f : Rat -> RealCompute) {a b : Rat}
    (P : RationalPartition a b) where
  evalStage : Nat
  sample : (k : Nat) -> k < P.pieces -> Rat
  sample_mem : forall k (hk : k < P.pieces),
    (P.cell k hk).contains (sample k hk)
  sampleValue : (k : Nat) -> k < P.pieces -> Rat
  sampleValue_mem : forall k (hk : k < P.pieces),
    ((f (sample k hk)).compute evalStage).ContainsInterval
      (QInterval.pointInterval (sampleValue k hk))
  range : (k : Nat) -> k < P.pieces -> QInterval
  range_contains : forall k (hk : k < P.pieces) x,
    (P.cell k hk).contains x ->
      (range k hk).ContainsInterval ((f x).compute evalStage)

namespace SampledRawDarbouxPartition

variable {f : Rat -> RealCompute} {a b : Rat} {P : RationalPartition a b}

/-- The rational sampled rectangle at the common raw-evaluator stage. -/
def sampleTerm (R : SampledRawDarbouxPartition f P) (k : Nat) : Rat :=
  if hk : k < P.pieces then
    (P.cell k hk).width * R.sampleValue k hk
  else 0

def sampledAction (R : SampledRawDarbouxPartition f P) : Rat :=
  (List.range P.pieces).foldl (fun total k => total + R.sampleTerm k) 0

def darbouxSum (R : SampledRawDarbouxPartition f P) : QInterval :=
  P.boundIntegralSum R.range

theorem range_contains_sampleValue
    (R : SampledRawDarbouxPartition f P) (k : Nat)
    (hk : k < P.pieces) :
    (R.range k hk).ContainsInterval
      (QInterval.pointInterval (R.sampleValue k hk)) := by
  have hrange := R.range_contains k hk (R.sample k hk) (R.sample_mem k hk)
  have hsample := R.sampleValue_mem k hk
  exact ⟨Rat.le_trans hrange.1 hsample.1,
    Rat.le_trans hsample.2 hrange.2⟩

theorem boundIntegralTerm_contains_sampleTerm
    (R : SampledRawDarbouxPartition f P) (k : Nat) :
    (P.boundIntegralTerm R.range k).ContainsInterval
      (QInterval.pointInterval (R.sampleTerm k)) := by
  by_cases hk : k < P.pieces
  · have hwidth : 0 <= (P.cell k hk).width := by
      unfold RationalSubinterval.width
      have hordered := (P.cell k hk).ordered
      grind [Rat.sub_eq_add_neg]
    have hscaled := QInterval.scaleByRat_contains_of_nonneg hwidth
      (R.range_contains_sampleValue k hk)
    simpa [RationalPartition.boundIntegralTerm, sampleTerm, hk,
      RationalSubinterval.scaleBound, QInterval.scaleByRat, hwidth,
      QInterval.pointInterval] using hscaled
  · simp [RationalPartition.boundIntegralTerm, sampleTerm, hk,
      QInterval.pointInterval, QInterval.ContainsInterval]

theorem darbouxSum_contains_sampledAction
    (R : SampledRawDarbouxPartition f P) :
    R.darbouxSum.ContainsInterval
      (QInterval.pointInterval R.sampledAction) := by
  have hfold := RationalPartition.addInterval_fold_contains
    (List.range P.pieces)
    (fun k => P.boundIntegralTerm R.range k)
    (fun k => QInterval.pointInterval (R.sampleTerm k))
    (outerInit := QInterval.pointInterval 0)
    (innerInit := QInterval.pointInterval 0)
    (QInterval.containsInterval_refl _)
    (R.boundIntegralTerm_contains_sampleTerm)
  unfold darbouxSum RationalPartition.boundIntegralSum sampledAction
  rw [QInterval.addInterval_fold_pointInterval] at hfold
  exact hfold

theorem qabs_candidate_sub_sampledAction_le_width
    (R : SampledRawDarbouxPartition f P) (candidate : Rat)
    (hcandidate : R.darbouxSum.ContainsInterval
      (QInterval.pointInterval candidate)) :
    qabs (candidate - R.sampledAction) <= R.darbouxSum.width :=
  QInterval.qabs_sub_le_width_of_contains_points
    hcandidate R.darbouxSum_contains_sampledAction

end SampledRawDarbouxPartition

end ComputableAnalysis


