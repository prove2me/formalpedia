-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_SinPiIntegral
-- name    : liuyao_ca_fd889115_k1_Analysis_SinPiIntegral
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:23:50.333798+00:00
-- url     : https://prove2.me/theorems/f54785f2-8545-48ec-9cc1-7b05871e9663
-- title:
--   Computable analysis · SinPiIntegral · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/SinPiIntegral.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralIdentities
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_AlgebraicFunctions
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_CauchyPi
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Calculus
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_TrigSpecialValues

set_option autoImplicit true

/-!
# The half-interval integral of `sin (pi * x)`

This file is the proof-facing entry point for the first nontrivial
trigonometric integral.  The project has one public sine convention:
`sin (pi * x)`.  The circle layer has an internal normalized coordinate `t`
for a quarter-turn; on the public half-period we pass `t = 2 * x`.  This is
an implementation coordinate, not a second definition of sine.  No
real-valued argument and no primitive real `pi` are used by the evaluator.

The final equality is intentionally expressed through an effective FTC
certificate.  The certificate is where the finite interval bounds,
monotonicity/turning-point analysis, and endpoint calculation belong.  This
keeps the theorem constructive: the dyadic integral algorithm is a raw
algorithm, while the FTC certificate identifies its value.
-/

namespace ComputableAnalysis

namespace RationalCircle

namespace GeometricTrig

/-- The normalized circle sine reparameterized as `sin (pi * x)`.

The input is rational and is only interpreted through the quarter-turn
parameter `2*x`.  In particular, this definition does not ask for a real
number named `pi` at a rational input.
-/
def sinPiRawOfConstruction
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)) :
    PartialRealFunRaw where
  definedAt := fun x => 0 <= x /\ x <= (1 : Rat) / 2
  compute := fun x hx n =>
    C.sinFunctionRaw.compute (2 * x) (hdefined x hx.1 hx.2) n

theorem sinPiRawOfConstruction_valid
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)) :
    forall x hx,
      RealCompute.ValidCompute
        ((sinPiRawOfConstruction C hdefined).compute x hx) := by
  intro x hx
  exact C.sinFunctionRaw_valid (2 * x) (hdefined x hx.1 hx.2)

end GeometricTrig

end RationalCircle

namespace SinPiIntegral

open RationalCircle.GeometricTrig
open RationalCircle.GeometricTrig.SpecialAngles

theorem sqrtOnUnitEvalIntervalClipped_overlap_of_common_point
    {I J : QInterval} (hI : subintervalOf I 0 1)
    (hJ : subintervalOf J 0 1) (q : Rat)
    (hIq : I.lo <= q ∧ q <= I.hi)
    (hJq : J.lo <= q ∧ q <= J.hi) (n : Nat) :
    QInterval.Overlaps
      (sqrtOnUnitEvalIntervalClipped I n)
      (sqrtOnUnitEvalIntervalClipped J n) := by
  have hq : 0 <= q ∧ q <= 1 := by
    constructor
    · exact Rat.le_trans hI.1 hIq.1
    · exact Rat.le_trans hIq.2 hI.2.2
  have hpointI := sqrtOnUnitEvalIntervalClipped_contains_point
    I hI q hq n hIq.1 hIq.2
  have hpointJ := sqrtOnUnitEvalIntervalClipped_contains_point
    J hJ q hq n hJq.1 hJq.2
  have hqbox := sqrtOnUnit_compute_subinterval q hq n
  unfold QInterval.Overlaps
  exact ⟨Rat.le_trans hpointI.1 (Rat.le_trans hqbox.2.1 hpointJ.2),
    Rat.le_trans hpointJ.1 (Rat.le_trans hqbox.2.1 hpointI.2)⟩

theorem sqrtOnUnitEvalIntervalClipped_overlap_of_input_overlap
    {I J : QInterval} (hI : subintervalOf I 0 1)
    (hJ : subintervalOf J 0 1)
    (hover : QInterval.Overlaps I J) (n : Nat) :
    QInterval.Overlaps
      (sqrtOnUnitEvalIntervalClipped I n)
      (sqrtOnUnitEvalIntervalClipped J n) := by
  let q : Rat := max I.lo J.lo
  have hIq : I.lo <= q ∧ q <= I.hi := by
    dsimp [q]
    constructor
    · rw [Rat.max_def]
      split <;> grind [hI.2.1, hJ.2.1]
    · rw [Rat.max_def]
      split <;> grind [hover.2, hI.2.1]
  have hJq : J.lo <= q ∧ q <= J.hi := by
    dsimp [q]
    constructor
    · rw [Rat.max_def]
      split <;> grind [hI.2.1, hJ.2.1]
    · rw [Rat.max_def]
      split <;> grind [hover.1, hJ.2.1]
  exact sqrtOnUnitEvalIntervalClipped_overlap_of_common_point hI hJ q hIq hJq n

theorem sqrtOnUnitEvalIntervalClipped_overlap_of_input_overlap_at
    {I J : QInterval} (hI : subintervalOf I 0 1)
    (hJ : subintervalOf J 0 1)
    (hover : QInterval.Overlaps I J) (n m : Nat) :
    QInterval.Overlaps
      (sqrtOnUnitEvalIntervalClipped I n)
      (sqrtOnUnitEvalIntervalClipped J m) := by
  let q : Rat := max I.lo J.lo
  have hIq : I.lo <= q ∧ q <= I.hi := by
    dsimp [q]
    constructor
    · rw [Rat.max_def]
      split <;> grind [hI.2.1, hJ.2.1]
    · rw [Rat.max_def]
      split <;> grind [hover.2, hI.2.1]
  have hJq : J.lo <= q ∧ q <= J.hi := by
    dsimp [q]
    constructor
    · rw [Rat.max_def]
      split <;> grind [hI.2.1, hJ.2.1]
    · rw [Rat.max_def]
      split <;> grind [hover.1, hJ.2.1]
  have hq : 0 <= q ∧ q <= 1 := by
    constructor
    · exact Rat.le_trans hI.1 hIq.1
    · exact Rat.le_trans hIq.2 hI.2.2
  have hpointI := sqrtOnUnitEvalIntervalClipped_contains_point
    I hI q hq n hIq.1 hIq.2
  have hpointJ := sqrtOnUnitEvalIntervalClipped_contains_point
    J hJ q hq m hJq.1 hJq.2
  have hqboxI := sqrtOnUnit_compute_subinterval q hq n
  have hqboxJ := sqrtOnUnit_compute_subinterval q hq m
  have hqvalid : ({ compute := sqrtOnUnit.compute q hq } : RealCompute).Valid :=
    sqrtOnUnit.valid_on q (sqrtOnUnit.defined_on q hq)
  have hcross := RealCompute.allStagesOverlap_refl
    ({ compute := sqrtOnUnit.compute q hq } : RealCompute) hqvalid n m
  have hcross' :=
    (RealCompute.compareAt_overlap_iff
      ({ compute := sqrtOnUnit.compute q hq } : RealCompute)
      ({ compute := sqrtOnUnit.compute q hq } : RealCompute) n m).1 hcross
  unfold QInterval.Overlaps
  exact ⟨Rat.le_trans hpointI.1 (Rat.le_trans hcross'.1 hpointJ.2),
    Rat.le_trans hpointJ.1 (Rat.le_trans hcross'.2 hpointI.2)⟩

/-- The first nontrivial dyadic sample has its certified nested-radical value.

At `x = 1/4`, the public notation `sin (pi*x)` invokes the normalized circle
input `2*x = 1/2`.  The special-angle certificate identifies that sample with
the existing positive square-root representation of `1/2`; no value of a
completed standard real is used. -/
theorem sinPiRawOfConstruction_quarter_equiv_of_specialAngle
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x))
    (hspecial : SpecialAngleValueTargets C) :
    let hxquarter : (sinPiRawOfConstruction C hdefined).definedAt (1 / 4) := by
      exact ⟨by decide +kernel, by decide +kernel⟩
    ({ compute :=
        (sinPiRawOfConstruction C hdefined).compute
          (1 / 4) hxquarter } : RealCompute).Equiv
      sinFortyFiveValue := by
  dsimp
  rcases hspecial.sin_forty_five with ⟨ht, hvalue⟩
  have harg : (2 : Rat) * (1 / 4) = 1 / 2 := by decide +kernel
  change
    ({ compute := C.sinFunctionRaw.compute (2 * (1 / 4)) _ } : RealCompute).Equiv
      sinFortyFiveValue
  have hq : C.sinFunctionRaw.definedAt (2 * (1 / 4)) :=
    hdefined (1 / 4) (by decide +kernel) (by decide +kernel)
  change
    ({ compute := C.sinFunctionRaw.compute (2 * (1 / 4)) hq } : RealCompute).Equiv
      sinFortyFiveValue
  have hcompute :
      C.sinFunctionRaw.compute (2 * (1 / 4)) hq =
        C.sinFunctionRaw.compute (1 / 2) ht := by
    congr 1
  rw [hcompute]
  exact hvalue

/-!
## The expected endpoint value

The integral certificate below is independent of which certified pi
implementation is preferred.  For the displayed value `1 / pi`, we use the
circle-area pi raw and invert its positive rational boxes.  This is an
interval operation, not division in Mathlib's real numbers.
-/

private theorem piCircleArea_interval_bounds (n : Nat) :
    2 <= (piCircleArea.compute n).lo /\
    (piCircleArea.compute n).hi <= 4 := by
  have hnest := (CauchyPi.piCircleArea_valid).2.1 0 n (Nat.zero_le n)
  have hlo : 2 <= (piCircleArea.compute n).lo := by
    simpa [piCircleArea_compute_zero] using hnest.1
  have hhi : (piCircleArea.compute n).hi <= 4 := by
    simpa [piCircleArea_compute_zero] using hnest.2.2
  exact ⟨hlo, hhi⟩

private theorem piCircleArea_interval_positive (n : Nat) :
    0 < (piCircleArea.compute n).lo := by
  have htwo : (0 : Rat) < 2 := by decide +kernel
  grind [piCircleArea_interval_bounds n]

private theorem one_div_antitone_pos_local {a b : Rat}
    (ha : 0 < a) (hab : a <= b) : 1 / b <= 1 / a := by
  apply Rat.le_of_mul_le_mul_right (c := a * b)
  · have hane : a ≠ 0 := Rat.ne_of_gt ha
    have hb : 0 < b := by grind
    have hbne : b ≠ 0 := Rat.ne_of_gt hb
    calc
      (1 / b) * (a * b) = a := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ hbne]
      _ <= b := by grind
      _ = (1 / a) * (a * b) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ hane]
  · exact Rat.mul_pos ha (by grind)

private theorem reciprocalPi_compute (n : Nat) :
    (QInterval.inv (piCircleArea.compute n)) =
      { lo := 1 / (piCircleArea.compute n).hi,
        hi := 1 / (piCircleArea.compute n).lo } := by
  simp [QInterval.inv, piCircleArea_interval_positive]

def reciprocalPiRaw : RealCompute where
  compute := fun n => QInterval.inv (piCircleArea.compute n)

theorem reciprocalPiRaw_valid : reciprocalPiRaw.Valid := by
  constructor
  · intro n
    change 0 <= (QInterval.inv (piCircleArea.compute n)).width
    rw [reciprocalPi_compute n]
    have hlo := piCircleArea_interval_positive n
    have hhi : 0 < (piCircleArea.compute n).hi := by
      grind [RealCompute.interval_order_of_valid piCircleArea
        CauchyPi.piCircleArea_valid n]
    have hreciplo : 0 < 1 / (piCircleArea.compute n).hi := by
      rw [Rat.div_def]
      exact Rat.mul_pos (by decide +kernel)
        ((Rat.inv_pos).2 hhi)
    have hreciphi : 0 < 1 / (piCircleArea.compute n).lo := by
      rw [Rat.div_def]
      exact Rat.mul_pos (by decide +kernel)
        ((Rat.inv_pos).2 hlo)
    have horder := RealCompute.interval_order_of_valid piCircleArea
      CauchyPi.piCircleArea_valid n
    have hrecip_order := one_div_antitone_pos_local hlo horder
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      change (QInterval.inv (piCircleArea.compute n)).lo <=
        (QInterval.inv (piCircleArea.compute m)).lo /\
        (QInterval.inv (piCircleArea.compute m)).lo <=
          (QInterval.inv (piCircleArea.compute m)).hi /\
        (QInterval.inv (piCircleArea.compute m)).hi <=
          (QInterval.inv (piCircleArea.compute n)).hi
      rw [reciprocalPi_compute n, reciprocalPi_compute m]
      have hvalid := CauchyPi.piCircleArea_valid
      have hnested := hvalid.2.1 n m hnm
      have hloN := piCircleArea_interval_positive n
      have hloM := piCircleArea_interval_positive m
      have hhiN := RealCompute.interval_order_of_valid piCircleArea hvalid n
      have hhiM := RealCompute.interval_order_of_valid piCircleArea hvalid m
      constructor
      · exact one_div_antitone_pos_local
          (a := (piCircleArea.compute m).hi)
          (b := (piCircleArea.compute n).hi) (by grind) hnested.2.2
      · constructor
        · exact one_div_antitone_pos_local
            (a := (piCircleArea.compute m).lo)
            (b := (piCircleArea.compute m).hi) hloM hhiM
        · exact one_div_antitone_pos_local
            (a := (piCircleArea.compute n).lo)
            (b := (piCircleArea.compute m).lo) hloN hnested.1
    · intro eps
      let wide : QPos :=
        { val := 4 * eps.val
          property := by exact Rat.mul_pos (by decide +kernel) eps.property }
      obtain ⟨N, hN⟩ := CauchyPi.piCircleArea_valid.2.2 wide
      refine ⟨N, ?_⟩
      intro n hn
      change (QInterval.inv (piCircleArea.compute n)).width <= eps.val
      rw [reciprocalPi_compute n]
      have hvalid := CauchyPi.piCircleArea_valid
      have hbounds := piCircleArea_interval_bounds n
      have hlo := piCircleArea_interval_positive n
      have hhi := RealCompute.interval_order_of_valid piCircleArea hvalid n
      have hwidth := hN n hn
      have hprod : 4 <=
          (piCircleArea.compute n).lo * (piCircleArea.compute n).hi := by
        have hlow := hbounds.1
        have horder := RealCompute.interval_order_of_valid piCircleArea
          hvalid n
        have hhigh : 2 <= (piCircleArea.compute n).hi := by grind
        calc
          (4 : Rat) = 2 * 2 := by decide +kernel
          _ <= (piCircleArea.compute n).lo * 2 := by
            exact Rat.mul_le_mul_of_nonneg_right hlow (by decide +kernel)
          _ <= (piCircleArea.compute n).lo *
              (piCircleArea.compute n).hi := by
            exact Rat.mul_le_mul_of_nonneg_left hhigh
              (by grind [piCircleArea_interval_bounds n])
      change 1 / (piCircleArea.compute n).lo -
        1 / (piCircleArea.compute n).hi <= eps.val
      rw [show (1 / (piCircleArea.compute n).lo) -
          (1 / (piCircleArea.compute n).hi) =
          ((piCircleArea.compute n).hi -
            (piCircleArea.compute n).lo) /
            ((piCircleArea.compute n).lo *
              (piCircleArea.compute n).hi) by
        rw [Rat.div_def, Rat.div_def, Rat.div_def]
        have hlo_ne : (piCircleArea.compute n).lo ≠ 0 :=
          Rat.ne_of_gt hlo
        have hhi_ne : (piCircleArea.compute n).hi ≠ 0 :=
          Rat.ne_of_gt (by grind)
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_rev,
          Rat.mul_inv_cancel _ hlo_ne, Rat.mul_inv_cancel _ hhi_ne]]
      have hwidth_nonneg : 0 <= (piCircleArea.compute n).width := by
        exact hvalid.1 n
      have hden := one_div_antitone_pos_local (by decide +kernel : (0 : Rat) < 4)
        hprod
      have hden' :
          ((piCircleArea.compute n).lo * (piCircleArea.compute n).hi)⁻¹ <=
            (1 / 4 : Rat) := by
        simpa [Rat.div_def] using hden
      calc
        ((piCircleArea.compute n).hi - (piCircleArea.compute n).lo) /
            ((piCircleArea.compute n).lo * (piCircleArea.compute n).hi) <=
            (piCircleArea.compute n).width * (1 / 4) := by
              rw [Rat.div_def]
              exact Rat.mul_le_mul_of_nonneg_left hden' hwidth_nonneg
        _ <= wide.val * (1 / 4) := by
              exact Rat.mul_le_mul_of_nonneg_right hwidth
                (by decide +kernel)
        _ = (4 * eps.val) / 4 := by
          dsimp [wide]
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ = eps.val := by
          rw [Rat.div_def]
          grind

/-!
## Executable dyadic inverse traces

The inverse step is not a classical inverse-function axiom.  A concrete
search records one left/right decision at each stage.  The interval itself is
then generated by rational midpoint arithmetic; the only analytic field is
that the forward interval image overlaps the requested target.
-/

/-- The rational interval selected by a finite left/right bisection path. -/
def dyadicCell (a b : Rat) (path : Nat -> Bool) : Nat -> QInterval
  | 0 => { lo := a, hi := b }
  | n + 1 =>
      let previous := dyadicCell a b path n
      let midpoint := (previous.lo + previous.hi) / 2
      if path n then
        { lo := previous.lo, hi := midpoint }
      else
        { lo := midpoint, hi := previous.hi }

theorem dyadicCell_width (a b : Rat) (path : Nat -> Bool) :
    forall n, (dyadicCell a b path n).width =
      (b - a) / (((2 ^ n : Nat) : Rat)) := by
  intro n
  induction n with
  | zero =>
      simp [dyadicCell, QInterval.width]
      rw [Rat.div_def]
      grind
  | succ n ih =>
      simp only [dyadicCell]
      split <;> simp only [QInterval.width]
      · change ((dyadicCell a b path n).lo +
          (dyadicCell a b path n).hi) / 2 -
            (dyadicCell a b path n).lo = _
        rw [show ((dyadicCell a b path n).lo +
            (dyadicCell a b path n).hi) / 2 -
              (dyadicCell a b path n).lo =
            ((dyadicCell a b path n).hi -
              (dyadicCell a b path n).lo) / 2 by
                grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]]
        have ih' : (dyadicCell a b path n).hi -
            (dyadicCell a b path n).lo =
            (b - a) / (((2 ^ n : Nat) : Rat)) := by
          simpa [QInterval.width] using ih
        rw [ih']
        rw [Rat.div_def]
        have htwo : (2 : Rat) ≠ 0 := by decide +kernel
        rw [show ((2 ^ (n + 1) : Nat) : Rat) =
          2 * ((2 ^ n : Nat) : Rat) by
            rw [Nat.pow_succ, Rat.natCast_mul,
              show ((2 : Nat) : Rat) = 2 by decide +kernel]
            exact Rat.mul_comm _ _]
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ htwo]
      · change (dyadicCell a b path n).hi -
          ((dyadicCell a b path n).lo +
            (dyadicCell a b path n).hi) / 2 = _
        rw [show (dyadicCell a b path n).hi -
            ((dyadicCell a b path n).lo +
              (dyadicCell a b path n).hi) / 2 =
            ((dyadicCell a b path n).hi -
              (dyadicCell a b path n).lo) / 2 by
                grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]]
        have ih' : (dyadicCell a b path n).hi -
            (dyadicCell a b path n).lo =
            (b - a) / (((2 ^ n : Nat) : Rat)) := by
          simpa [QInterval.width] using ih
        rw [ih']
        rw [Rat.div_def]
        have htwo : (2 : Rat) ≠ 0 := by decide +kernel
        rw [show ((2 ^ (n + 1) : Nat) : Rat) =
          2 * ((2 ^ n : Nat) : Rat) by
            rw [Nat.pow_succ, Rat.natCast_mul,
              show ((2 : Nat) : Rat) = 2 by decide +kernel]
            exact Rat.mul_comm _ _]
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ htwo]

theorem dyadicCell_step_subinterval (a b : Rat) (path : Nat -> Bool) (n : Nat)
    (hordered : (dyadicCell a b path n).lo <=
      (dyadicCell a b path n).hi) :
    subintervalOf (dyadicCell a b path (n + 1))
      (dyadicCell a b path n).lo (dyadicCell a b path n).hi := by
  simp only [dyadicCell]
  split <;> simp only [subintervalOf]
  · constructor
    · grind
    constructor <;> grind
  · constructor
    · grind
    constructor <;> grind

theorem dyadicCell_subinterval_of_source
    (a b : Rat) (path : Nat -> Bool) (hab : a <= b) :
    forall n, subintervalOf (dyadicCell a b path n) a b := by
  intro n
  induction n with
  | zero =>
      change a <= a /\ a <= b /\ b <= b
      exact ⟨Rat.le_refl, hab, Rat.le_refl⟩
  | succ n ih =>
      have hordered : (dyadicCell a b path n).lo <=
          (dyadicCell a b path n).hi := ih.2.1
      have hstep := dyadicCell_step_subinterval a b path n hordered
      constructor
      · exact Rat.le_trans ih.1 hstep.1
      constructor
      · exact hstep.2.1
      · exact Rat.le_trans hstep.2.2 ih.2.2

private theorem dyadicCell_subinterval_of_cell
    (a b : Rat) (path : Nat -> Bool) (hab : a <= b) :
    forall n m, n <= m ->
      subintervalOf (dyadicCell a b path m)
        (dyadicCell a b path n).lo (dyadicCell a b path n).hi := by
  intro n m
  induction m generalizing n with
  | zero =>
      intro hnm
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst n
      exact ⟨Rat.le_refl, (by
        have h := dyadicCell_subinterval_of_source a b path hab 0
        exact h.2.1), Rat.le_refl⟩
  | succ m ih =>
      intro hnm
      by_cases hEq : n = m + 1
      · subst n
        exact ⟨Rat.le_refl, (by
          have h := dyadicCell_subinterval_of_source a b path hab (m + 1)
          exact h.2.1), Rat.le_refl⟩
      · have hnm' : n <= m := by omega
        have ih' := ih n hnm'
        have hordered : (dyadicCell a b path m).lo <=
            (dyadicCell a b path m).hi := by
          have h := dyadicCell_subinterval_of_source a b path hab m
          exact h.2.1
        have hstep := dyadicCell_step_subinterval a b path m hordered
        constructor
        · exact Rat.le_trans ih'.1 hstep.1
        constructor
        · exact hstep.2.1
        · exact Rat.le_trans hstep.2.2 ih'.2.2

set_option maxHeartbeats 5000000 in
theorem dyadicCell_valid_of_width_le_one
    (a b : Rat) (path : Nat -> Bool) (hab : a <= b)
    (hwidth : b - a <= 1) :
    RealCompute.ValidCompute (dyadicCell a b path) := by
  have hbound : forall n,
      (dyadicCell a b path n).width <=
        1 / (((n + 1 : Nat) : Rat)) := by
    intro n
    rw [dyadicCell_width]
    have hpow : (n + 1 : Nat) <= 2 ^ n := by
      induction n with
      | zero => omega
      | succ n ih =>
          calc
            n + 1 + 1 <= 2 * (n + 1) := by omega
            _ <= 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
            _ = 2 ^ (n + 1) := by
              rw [Nat.pow_succ]
              omega
    have hdenpos : 0 < ((n + 1 : Nat) : Rat) := by
      exact_mod_cast (Nat.succ_pos n)
    have hpowpos : 0 < ((2 ^ n : Nat) : Rat) := by
      exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
    have hnum : 0 <= b - a := by grind
    have hone :
        1 / ((2 ^ n : Nat) : Rat) <=
          1 / ((n + 1 : Nat) : Rat) :=
      FTC.one_div_nat_antitone
        (Nat.succ_pos n) (Nat.pow_pos (by omega : 0 < 2)) hpow
    have hone_nonneg : 0 <=
        1 / ((n + 1 : Nat) : Rat) := by
      simpa [Rat.div_def] using
        (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))
    calc
      (b - a) / ((2 ^ n : Nat) : Rat) =
          (b - a) * (1 / ((2 ^ n : Nat) : Rat)) := by
            simp [Rat.div_def]
      _ <= (b - a) * (1 / ((n + 1 : Nat) : Rat)) :=
        Rat.mul_le_mul_of_nonneg_left hone hnum
      _ <= 1 * (1 / ((n + 1 : Nat) : Rat)) :=
        Rat.mul_le_mul_of_nonneg_right hwidth hone_nonneg
      _ = 1 / ((n + 1 : Nat) : Rat) := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hs := (dyadicCell_subinterval_of_source a b path hab n).2.1
    rw [dyadicCell_width]
    exact Rat.mul_nonneg (by grind)
      (Rat.le_of_lt ((Rat.inv_pos).2
        ((Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2)))))
  · intro n m hnm
    have hcell := dyadicCell_subinterval_of_cell a b path hab n m hnm
    exact ⟨hcell.1, hcell.2.1, hcell.2.2⟩
  · apply shrinksToZero_of_natOverSuccBound (C := 1)
    intro n
    exact hbound n

/-- The dyadic cell selected by a known rational preimage witness. -/
def dyadicWitnessCell (a b z : Rat) : Nat -> QInterval
  | 0 => { lo := a, hi := b }
  | n + 1 =>
      let previous := dyadicWitnessCell a b z n
      let midpoint := (previous.lo + previous.hi) / 2
      if z <= midpoint then
        { lo := previous.lo, hi := midpoint }
      else
        { lo := midpoint, hi := previous.hi }

/-- The executable left/right decisions for the witness-driven bisection. -/
def dyadicWitnessPath (a b z : Rat) (n : Nat) : Bool :=
  if z <= ((dyadicWitnessCell a b z n).lo +
      (dyadicWitnessCell a b z n).hi) / 2 then true else false

private theorem dyadicMidpoint_mem {l r : Rat} (h : l <= r) :
    l <= (l + r) / 2 /\ (l + r) / 2 <= r := by
  have htwo : (2 : Rat) > 0 := by decide +kernel
  constructor
  · apply Rat.le_of_mul_le_mul_right (c := (2 : Rat))
    · rw [Rat.div_def]
      have hc : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by decide +kernel
      grind [Rat.mul_assoc, Rat.mul_comm]
    · exact htwo
  · apply Rat.le_of_mul_le_mul_right (c := (2 : Rat))
    · rw [Rat.div_def]
      have hc : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by decide +kernel
      grind [Rat.mul_assoc, Rat.mul_comm]
    · exact htwo

theorem dyadicCell_dyadicWitnessPath_eq (a b z : Rat) :
    forall n, dyadicCell a b (dyadicWitnessPath a b z) n =
      dyadicWitnessCell a b z n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [dyadicCell, dyadicWitnessCell, ih, dyadicWitnessPath]
      split <;> simp_all

theorem dyadicWitnessCell_source (a b z : Rat) (hab : a <= b)
    (hz : a <= z) (hz' : z <= b) :
    forall n, subintervalOf (dyadicWitnessCell a b z n) a b := by
  intro n
  induction n with
  | zero =>
      exact ⟨Rat.le_refl, hab, Rat.le_refl⟩
  | succ n ih =>
      simp only [dyadicWitnessCell]
      have hmid := dyadicMidpoint_mem ih.2.1
      split
      · constructor
        · exact ih.1
        constructor
        · exact hmid.1
        · exact Rat.le_trans hmid.2 ih.2.2
      · constructor
        · exact Rat.le_trans ih.1 hmid.1
        constructor
        · exact hmid.2
        · exact ih.2.2

theorem dyadicWitnessCell_contains (a b z : Rat) (hab : a <= b)
    (hz : a <= z) (hz' : z <= b) :
    forall n, (dyadicWitnessCell a b z n).lo <= z /\
      z <= (dyadicWitnessCell a b z n).hi := by
  intro n
  induction n with
  | zero => exact ⟨hz, hz'⟩
  | succ n ih =>
      simp only [dyadicWitnessCell]
      have hsource := dyadicWitnessCell_source a b z hab hz hz' n
      have hmid := dyadicMidpoint_mem hsource.2.1
      split
      · constructor
        · exact ih.1
        · assumption
      · constructor
        · have hnot : ¬z <=
              ((dyadicWitnessCell a b z n).lo +
                (dyadicWitnessCell a b z n).hi) / 2 := by
            assumption
          exact Rat.le_of_lt ((Rat.not_le).1 hnot)
        · change z <= (dyadicWitnessCell a b z n).hi
          exact ih.2

theorem dyadicCell_dyadicWitnessPath_contains
    (a b z : Rat) (hab : a <= b)
    (hz : a <= z) (hz' : z <= b) :
    forall n, (dyadicCell a b (dyadicWitnessPath a b z) n).lo <= z /\
      z <= (dyadicCell a b (dyadicWitnessPath a b z) n).hi := by
  intro n
  rw [dyadicCell_dyadicWitnessPath_eq]
  exact dyadicWitnessCell_contains a b z hab hz hz' n

/-- A fully executable inverse trace for a monotone interval branch.

`path` is the actual finite search trace.  `value_overlaps` is the one
function-specific obligation: the forward interval image of every selected
cell must overlap the target box.  The remaining fields ensure that this
trace is a valid shrinking raw interval and stays in the source branch.
-/
structure DyadicInverseTrace
    (I : InvertibleFunctionOnInterval)
    (y : InRangeRaw I) where
  path : Nat -> Bool
  cell_valid : RealCompute.ValidCompute (dyadicCell I.function.lower I.function.upper path)
  cell_in_source : forall n,
    subintervalOf
      (dyadicCell I.function.lower I.function.upper path n)
      I.function.lower I.function.upper
  value_overlaps : forall n,
    QInterval.Overlaps
      (I.continuous.regular.evalInterval
        (dyadicCell I.function.lower I.function.upper path n)
        (cell_in_source n) n)
      (y.value.compute n)

/-- Build the standard interval fields of a dyadic trace once its path and
forward-image overlap proof have been supplied.  In the arctangent branch
the source is [0,1], so the width hypothesis is discharged by arithmetic;
the only remaining search-specific field is value_overlaps. -/
def DyadicInverseTrace.ofPath
    {I : InvertibleFunctionOnInterval} {y : InRangeRaw I}
    (path : Nat -> Bool)
    (hsource : I.function.lower <= I.function.upper)
    (hwidth : I.function.upper - I.function.lower <= 1)
    (value_overlaps : forall n,
      QInterval.Overlaps
        (I.continuous.regular.evalInterval
          (dyadicCell I.function.lower I.function.upper path n)
          (dyadicCell_subinterval_of_source
            I.function.lower I.function.upper path hsource n)
          n)
        (y.value.compute n)) :
    DyadicInverseTrace I y where
  path := path
  cell_valid := dyadicCell_valid_of_width_le_one
    I.function.lower I.function.upper path hsource hwidth
  cell_in_source := dyadicCell_subinterval_of_source
    I.function.lower I.function.upper path hsource
  value_overlaps := value_overlaps

/-- Construct a complete dyadic inverse trace from a rational preimage
witness.  This is the constructive finite core used by special-angle
certificates: the witness is kept inside every cell, and interval regularity
transports its forward raw value to the target box. -/
def DyadicInverseTrace.ofRationalWitness
    {I : InvertibleFunctionOnInterval} {y : InRangeRaw I}
    (z : Rat)
    (hz : inDomainInterval I.function.lower I.function.upper z)
    (hwidth : I.function.upper - I.function.lower <= 1)
    (hvalue :
      ({ compute := I.function.compute z hz } : RealCompute).Equiv y.value) :
    DyadicInverseTrace I y := by
  apply DyadicInverseTrace.ofPath
    (dyadicWitnessPath I.function.lower I.function.upper z)
    I.source_ordered hwidth
  intro n
  let C := dyadicCell I.function.lower I.function.upper
    (dyadicWitnessPath I.function.lower I.function.upper z) n
  have hCsource := dyadicCell_subinterval_of_source
    I.function.lower I.function.upper
    (dyadicWitnessPath I.function.lower I.function.upper z)
    I.source_ordered n
  have hCcontains := dyadicCell_dyadicWitnessPath_contains
    I.function.lower I.function.upper z I.source_ordered hz.1 hz.2 n
  have houter := I.continuous.regular.contains_point_values
    C hCsource z hz n hCcontains.1 hCcontains.2
  have hzvalid : ({ compute := I.function.compute z hz } : RealCompute).Valid := by
    exact I.function.valid_on z (I.function.defined_on z hz)
  have heq := RealCompute.sameStageOverlap_of_equiv
    hzvalid y.value_valid hvalue n
  have hover := (RealCompute.compareAt_overlap_iff
    ({ compute := I.function.compute z hz } : RealCompute) y.value n n).1 heq
  change QInterval.Overlaps
    (I.continuous.regular.evalInterval C hCsource n)
    (y.value.compute n)
  unfold QInterval.ContainsInterval at houter
  unfold QInterval.Overlaps at hover ⊢
  change
    (I.function.compute z hz n).lo <= (y.value.compute n).hi /\
      (y.value.compute n).lo <= (I.function.compute z hz n).hi at hover
  change
    (I.continuous.regular.evalInterval C hCsource n).lo <=
        (I.function.compute z hz n).lo /\
      (I.function.compute z hz n).hi <=
        (I.continuous.regular.evalInterval C hCsource n).hi at houter
  constructor
  · exact Rat.le_trans houter.1 hover.1
  · exact Rat.le_trans hover.2 houter.2

/-- Turn an executable dyadic trace into the inverse-search interface. -/
def DyadicInverseTrace.toSearch
    {I : InvertibleFunctionOnInterval} {y : InRangeRaw I}
    (h : DyadicInverseTrace I y) : InverseBisectionSearch I y where
  compute_preimage := dyadicCell I.function.lower I.function.upper h.path
  valid_preimage := h.cell_valid
  preimage_subinterval := h.cell_in_source
  value_overlaps := h.value_overlaps

theorem DyadicInverseTrace.toSearch_compute_preimage
    {I : InvertibleFunctionOnInterval} {y : InRangeRaw I}
    (h : DyadicInverseTrace I y) (n : Nat) :
    (h.toSearch.compute_preimage n) =
      dyadicCell I.function.lower I.function.upper h.path n :=
  rfl

/-- The arctangent inverse package obtained once every target has an
executable dyadic trace.  This is the exact assembly point for the
arctangent-defined sine construction: no choice of an inverse is taken. -/
def arctanInverseBisectionOfDyadicTraces
    (branch : InvertibleFunctionOnInterval)
    (branch_is_geometric :
      FunctionOnInterval.Equivalent branch.function
        IntegralIdentities.arctanGeomOnUnit)
    (targetAt : forall t : RationalCircle.GeometricTrig.QuarterTurn,
      RationalCircle.GeometricTrig.firstQuadrantBranch t -> InRangeRaw branch)
    (targetAt_equiv_halfQuarterTurn :
      forall t ht, (targetAt t ht).value.Equiv
        (RationalCircle.GeometricTrig.halfQuarterTurnRaw t))
    (traceAt : forall y : InRangeRaw branch,
      DyadicInverseTrace branch y) :
    IntegralIdentities.ArctanInverseBisection where
  branch := branch
  branch_is_geometric := branch_is_geometric
  targetAt := targetAt
  targetAt_equiv_halfQuarterTurn := targetAt_equiv_halfQuarterTurn
  bisectionAt := fun y => (traceAt y).toSearch

/-! Build the inverse-search package from rational preimage witnesses.

This is the strongest fully executable shortcut currently available: for each
normalized first-quadrant target, a rational slope witness is supplied and is
then kept inside every selected dyadic cell.  The constructor does not choose
an inverse or appeal to a completed real line; the witness family is the
finite search data.  The general arctangent branch still needs a separate
construction of such witnesses (or an equivalent target-directed search).
-/
def arctanInverseBisectionOfRationalWitnesses
    (branch : InvertibleFunctionOnInterval)
    (branch_is_geometric :
      FunctionOnInterval.Equivalent branch.function
        IntegralIdentities.arctanGeomOnUnit)
    (targetAt : forall t : RationalCircle.GeometricTrig.QuarterTurn,
      RationalCircle.GeometricTrig.firstQuadrantBranch t -> InRangeRaw branch)
    (targetAt_equiv_halfQuarterTurn :
      forall t ht, (targetAt t ht).value.Equiv
        (RationalCircle.GeometricTrig.halfQuarterTurnRaw t))
    (targetWitness : forall _y : InRangeRaw branch, Rat)
    (targetWitness_in_domain : forall y : InRangeRaw branch,
      inDomainInterval branch.function.lower branch.function.upper
        (targetWitness y))
    (targetWitness_equiv : forall y : InRangeRaw branch,
      ({ compute := branch.function.compute
          (targetWitness y) (targetWitness_in_domain y) } : RealCompute).Equiv
        y.value)
    (source_width : branch.function.upper - branch.function.lower <= 1) :
    IntegralIdentities.ArctanInverseBisection := by
  apply arctanInverseBisectionOfDyadicTraces branch branch_is_geometric
    targetAt targetAt_equiv_halfQuarterTurn
  intro y
  exact DyadicInverseTrace.ofRationalWitness
    (targetWitness y)
    (targetWitness_in_domain y)
    source_width
    (targetWitness_equiv y)

/-- The rational circle parametrization used after the inverse-arctangent
search.  For a half-angle slope `u`, its imaginary coordinate is
`2*u/(1+u^2)`. -/
def rationalCircleSin (u : Rat) : Rat :=
  (2 * u) / (1 + u * u)

def rationalCircleSinInterval (U : QInterval) : QInterval :=
  { lo := rationalCircleSin U.lo, hi := rationalCircleSin U.hi }

/- A finite, rational tangent chart for a nested-radical sine/cosine box.
  If `S` and `C` enclose the positive-quarter-circle coordinates, then the
  quotient below encloses the half-angle slope `sin/(1+cos)`.  This is kept
  rational: it is the bridge from the geometric boxes to the inverse
  arctangent search, without introducing a completed real number. -/
def rationalHalfAngleTangentInterval (S C : QInterval) : QInterval :=
  { lo := S.lo / (1 + C.hi), hi := S.hi / (1 + C.lo) }

private theorem rat_eq_of_mul_eq_mul_pos_local {a b c : Rat}
    (hc : 0 < c) (h : a * c = b * c) : a = b := by
  have hcne : c ≠ 0 := Rat.ne_of_gt hc
  calc
    a = (a * c) * c⁻¹ := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hcne
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (b * c) * c⁻¹ := by rw [h]
    _ = b := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hcne
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem rat_div_nonneg_of_pos {a b : Rat}
    (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg ha (Rat.le_of_lt (Rat.inv_pos.2 hb))

theorem rationalHalfAngleTangentInterval_subinterval
    {S C : QInterval}
    (hS : subintervalOf S 0 1) (hC : subintervalOf C 0 1) :
    subintervalOf (rationalHalfAngleTangentInterval S C) 0 1 := by
  unfold rationalHalfAngleTangentInterval subintervalOf at *
  have hdlo : 0 < 1 + C.lo := by grind
  have hdhi : 0 < 1 + C.hi := by grind
  have hclo : (1 + C.lo) * (1 + C.lo)⁻¹ = 1 :=
    Rat.mul_inv_cancel (1 + C.lo) (Rat.ne_of_gt hdlo)
  have hchi : (1 + C.hi) * (1 + C.hi)⁻¹ = 1 :=
    Rat.mul_inv_cancel (1 + C.hi) (Rat.ne_of_gt hdhi)
  have hcross : S.lo * (1 + C.lo) <= S.hi * (1 + C.hi) := by
    have h1 := Rat.mul_le_mul_of_nonneg_right hS.2.1 (by grind : 0 <= 1 + C.lo)
    have h2 := Rat.mul_le_mul_of_nonneg_left
      (show 1 + C.lo <= 1 + C.hi by grind) (by grind : 0 <= S.hi)
    exact Rat.le_trans h1 (by simpa [Rat.mul_assoc, Rat.mul_comm] using h2)
  refine ⟨rat_div_nonneg_of_pos hS.1 hdhi, ?_, ?_⟩
  · apply Rat.le_of_mul_le_mul_right (c := 1 + C.hi) ?_ hdhi
    apply Rat.le_of_mul_le_mul_right (c := 1 + C.lo) ?_ hdlo
    change (S.lo / (1 + C.hi)) * (1 + C.hi) * (1 + C.lo) <=
      (S.hi / (1 + C.lo)) * (1 + C.hi) * (1 + C.lo)
    rw [Rat.div_def, Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm]
  · apply Rat.le_of_mul_le_mul_right (c := 1 + C.lo) ?_ hdlo
    change (S.hi / (1 + C.lo)) * (1 + C.lo) <= 1 * (1 + C.lo)
    rw [Rat.div_def]
    calc
      S.hi * (1 + C.lo)⁻¹ * (1 + C.lo) = S.hi := by
        rw [show S.hi * (1 + C.lo)⁻¹ * (1 + C.lo) =
          S.hi * ((1 + C.lo)⁻¹ * (1 + C.lo)) by
            grind [Rat.mul_assoc, Rat.mul_comm]]
        rw [Rat.inv_mul_cancel (1 + C.lo) (Rat.ne_of_gt hdlo), Rat.mul_one]
      _ <= 1 * (1 + C.lo) := by
        exact Rat.le_trans hS.2.2 (by
          simpa only [Rat.one_mul] using
            (Rat.mul_le_mul_of_nonneg_left
              (by grind : (1 : Rat) <= 1 + C.lo)
            (by decide +kernel : (0 : Rat) <= 1)))

theorem rationalHalfAngleTangentInterval_contains
    {S C : QInterval} (hS : subintervalOf S 0 1)
    (hC : subintervalOf C 0 1) {s c : Rat}
    (hs : 0 <= s) (hc : 0 <= c)
    (hsS : S.lo <= s ∧ s <= S.hi)
    (hcC : C.lo <= c ∧ c <= C.hi) :
    (rationalHalfAngleTangentInterval S C).lo <= s / (1 + c) ∧
      s / (1 + c) <= (rationalHalfAngleTangentInterval S C).hi := by
  unfold rationalHalfAngleTangentInterval
  unfold subintervalOf at hS hC
  have hdlo : 0 < 1 + C.lo := by grind
  have hdhi : 0 < 1 + C.hi := by grind
  have hd : 0 < 1 + c := by grind
  have hdc : 0 <= 1 + c := Rat.le_of_lt hd
  have hlo : 0 <= S.lo := hS.1
  have hhi : 0 <= S.hi := Rat.le_trans hlo hS.2.1
  have hcrossLo : S.lo * (1 + c) <= s * (1 + C.hi) := by
    have h1 := Rat.mul_le_mul_of_nonneg_right hsS.1 hdc
    have h2 := Rat.mul_le_mul_of_nonneg_left
      (show 1 + c <= 1 + C.hi by grind) hs
    exact Rat.le_trans h1 (by simpa [Rat.mul_assoc, Rat.mul_comm] using h2)
  have hcrossHi : s * (1 + C.lo) <= S.hi * (1 + c) := by
    have h1 := Rat.mul_le_mul_of_nonneg_right hsS.2 (Rat.le_of_lt hdlo)
    have h2 := Rat.mul_le_mul_of_nonneg_left
      (show 1 + C.lo <= 1 + c by grind) hhi
    exact Rat.le_trans h1 h2
  constructor
  · apply Rat.le_of_mul_le_mul_right (c := 1 + C.hi) ?_ hdhi
    apply Rat.le_of_mul_le_mul_right (c := 1 + c) ?_ hd
    change S.lo / (1 + C.hi) * (1 + C.hi) * (1 + c) <=
      (s / (1 + c) * (1 + C.hi)) * (1 + c)
    rw [Rat.div_def, Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm]
  · apply Rat.le_of_mul_le_mul_right (c := 1 + c) ?_ hd
    apply Rat.le_of_mul_le_mul_right (c := 1 + C.lo) ?_ hdlo
    change s / (1 + c) * (1 + c) * (1 + C.lo) <=
      (S.hi / (1 + C.lo)) * (1 + c) * (1 + C.lo)
    rw [Rat.div_def, Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm]

theorem rationalCircleSin_halfAngle_identity
    {s c : Rat} (hs : 0 <= s) (hc : 0 <= c)
    (hcircle : s * s + c * c = 1) :
    rationalCircleSin (s / (1 + c)) = s := by
  have hd : 0 < 1 + c := by grind
  have hdn : 1 + c ≠ 0 := Rat.ne_of_gt hd
  unfold rationalCircleSin
  rw [Rat.div_def, Rat.div_def]
  have hcancel : (1 + c) * (1 + c)⁻¹ = 1 :=
    Rat.mul_inv_cancel (1 + c) hdn
  have hinv : (1 + c)⁻¹ * (1 + c) = 1 :=
    Rat.inv_mul_cancel (1 + c) hdn
  have hpos : 0 < 1 + (s * (1 + c)⁻¹) * (s * (1 + c)⁻¹) := by
    have hsquare : 0 <= (s * (1 + c)⁻¹) * (s * (1 + c)⁻¹) :=
      Rat.mul_nonneg
        (Rat.mul_nonneg hs (Rat.le_of_lt (Rat.inv_pos.2 hd)))
        (Rat.mul_nonneg hs (Rat.le_of_lt (Rat.inv_pos.2 hd)))
    grind
  have hden : 1 + (s * (1 + c)⁻¹) * (s * (1 + c)⁻¹) ≠ 0 :=
    Rat.ne_of_gt hpos
  apply rat_eq_of_mul_eq_mul_pos_local
    (c := 1 + (s * (1 + c)⁻¹) * (s * (1 + c)⁻¹))
    hpos
  grind [Rat.mul_assoc, Rat.mul_comm]

private theorem rationalCircleSin_den_pos {u : Rat} (hu : 0 <= u) :
    0 < 1 + u * u := by
  have hsq : 0 <= u * u := Rat.mul_nonneg hu hu
  grind

private theorem rationalCircleSin_sub_formula {a b : Rat}
    (ha : 0 <= a) (hb : 0 <= b) :
    rationalCircleSin b - rationalCircleSin a =
      (2 * (b - a) * (1 - a * b)) /
        ((1 + a * a) * (1 + b * b)) := by
  let da : Rat := 1 + a * a
  let db : Rat := 1 + b * b
  have hda : 0 < da := by
    dsimp [da]
    exact rationalCircleSin_den_pos ha
  have hdb : 0 < db := by
    dsimp [db]
    exact rationalCircleSin_den_pos hb
  have hprod : 0 < da * db := Rat.mul_pos hda hdb
  apply rat_eq_of_mul_eq_mul_pos_local (c := da * db) hprod
  unfold rationalCircleSin
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have hda_ne : da ≠ 0 := Rat.ne_of_gt hda
  have hdb_ne : db ≠ 0 := Rat.ne_of_gt hdb
  have hda_cancel : da⁻¹ * da = 1 := Rat.inv_mul_cancel da hda_ne
  have hdb_cancel : db⁻¹ * db = 1 := Rat.inv_mul_cancel db hdb_ne
  have hleft :
      (2 * b * db⁻¹ - 2 * a * da⁻¹) * (da * db) =
        2 * b * da - 2 * a * db := by
    calc
      (2 * b * db⁻¹ - 2 * a * da⁻¹) * (da * db) =
            (2 * b * db⁻¹) * (da * db) -
            (2 * a * da⁻¹) * (da * db) := by
              grind [Rat.sub_eq_add_neg, Rat.add_mul]
      _ = 2 * b * da - 2 * a * db := by
        have h1 : (2 * b * db⁻¹) * (da * db) = 2 * b * da := by
          calc
            (2 * b * db⁻¹) * (da * db) =
                2 * b * da * (db⁻¹ * db) := by
                  grind [Rat.mul_assoc, Rat.mul_comm]
            _ = 2 * b * da := by rw [hdb_cancel, Rat.mul_one]
        have h2 : (2 * a * da⁻¹) * (da * db) = 2 * a * db := by
          calc
            (2 * a * da⁻¹) * (da * db) =
                2 * a * db * (da⁻¹ * da) := by
                  grind [Rat.mul_assoc, Rat.mul_comm]
            _ = 2 * a * db := by rw [hda_cancel, Rat.mul_one]
        rw [h1, h2]
  have hright :
      (2 * (b - a) * (1 - a * b) * (da * db)⁻¹) * (da * db) =
        2 * (b - a) * (1 - a * b) := by
    calc
      (2 * (b - a) * (1 - a * b) * (da * db)⁻¹) * (da * db) =
          2 * (b - a) * (1 - a * b) *
            ((da * db)⁻¹ * (da * db)) := by
              grind [Rat.mul_assoc, Rat.mul_comm]
      _ = 2 * (b - a) * (1 - a * b) := by
        have hcancel : (da * db)⁻¹ * (da * db) = 1 :=
          Rat.inv_mul_cancel (da * db) (Rat.ne_of_gt hprod)
        rw [hcancel, Rat.mul_one]
  rw [hleft, hright]
  dsimp [da, db]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg]

private theorem rationalCircleSin_mono {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (hb : b <= 1) :
    rationalCircleSin a <= rationalCircleSin b := by
  have hb0 : 0 <= b := Rat.le_trans ha hab
  have hprod : a * b <= 1 := by
    have h1 := Rat.mul_le_mul_of_nonneg_right hb ha
    have h2 := Rat.mul_le_mul_of_nonneg_left hab (Rat.le_of_lt (by decide +kernel : (0 : Rat) < 1))
    grind [Rat.sub_eq_add_neg]
  have hba : 0 <= b - a := by grind
  have hnum : 0 <= 2 * (b - a) * (1 - a * b) := by
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by decide +kernel) hba) (by grind)
  have hden : 0 < (1 + a * a) * (1 + b * b) :=
    Rat.mul_pos (rationalCircleSin_den_pos ha)
      (rationalCircleSin_den_pos hb0)
  have hdiff : 0 <= rationalCircleSin b - rationalCircleSin a := by
    rw [rationalCircleSin_sub_formula ha hb0, Rat.div_def]
    exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hden))
  grind [Rat.sub_eq_add_neg]

theorem rationalCircleSinInterval_overlap_of_halfAngle_boxes
    {S C : QInterval} (hS : subintervalOf S 0 1)
    (hC : subintervalOf C 0 1) {s c : Rat}
    (hs : 0 <= s) (hc : 0 <= c)
    (hcircle : s * s + c * c = 1)
    (hsS : S.lo <= s ∧ s <= S.hi)
    (hcC : C.lo <= c ∧ c <= C.hi) :
    QInterval.Overlaps
      (rationalCircleSinInterval
        (rationalHalfAngleTangentInterval S C)) S := by
  have hT := rationalHalfAngleTangentInterval_subinterval hS hC
  have ht := rationalHalfAngleTangentInterval_contains
    hS hC hs hc hsS hcC
  have ht0 : 0 <= s / (1 + c) := Rat.le_trans hT.1 ht.1
  have ht1 : s / (1 + c) <= 1 := Rat.le_trans ht.2 hT.2.2
  have hsinLo := rationalCircleSin_mono hT.1 ht.1 ht1
  have hsinHi := rationalCircleSin_mono ht0 ht.2 hT.2.2
  have hid := rationalCircleSin_halfAngle_identity hs hc hcircle
  unfold rationalCircleSinInterval QInterval.Overlaps
  constructor
  · calc
      rationalCircleSin (rationalHalfAngleTangentInterval S C).lo <=
          rationalCircleSin (s / (1 + c)) := hsinLo
      _ = s := hid
      _ <= S.hi := hsS.2
  · calc
      S.lo <= s := hsS.1
      _ = rationalCircleSin (s / (1 + c)) := hid.symm
      _ <= rationalCircleSin (rationalHalfAngleTangentInterval S C).hi := hsinHi

theorem rationalCircleSinInterval_overlap_of_halfAngle_boxes_of_outer_tangent
    {U S C : QInterval} (hU : subintervalOf U 0 1)
    (hS : subintervalOf S 0 1) (hC : subintervalOf C 0 1)
    (houter : U.ContainsInterval
      (rationalHalfAngleTangentInterval S C))
    {s c : Rat} (hs : 0 <= s) (hc : 0 <= c)
    (hcircle : s * s + c * c = 1)
    (hsS : S.lo <= s ∧ s <= S.hi)
    (hcC : C.lo <= c ∧ c <= C.hi) :
    QInterval.Overlaps (rationalCircleSinInterval U) S := by
  have hT := rationalHalfAngleTangentInterval_subinterval hS hC
  have hhalf := rationalCircleSinInterval_overlap_of_halfAngle_boxes
    hS hC hs hc hcircle hsS hcC
  have hTlo : U.lo <= (rationalHalfAngleTangentInterval S C).lo :=
    houter.1
  have hThi : (rationalHalfAngleTangentInterval S C).hi <= U.hi :=
    houter.2
  have hUlo : 0 <= U.lo := hU.1
  have hUhi : U.hi <= 1 := hU.2.2
  have hsinlo := rationalCircleSin_mono
    hUlo hTlo (Rat.le_trans hT.2.1 hT.2.2)
  have hsinhi := rationalCircleSin_mono
    (Rat.le_trans hT.1 hT.2.1) hThi hUhi
  unfold rationalCircleSinInterval QInterval.Overlaps at *
  constructor
  · exact Rat.le_trans hsinlo hhalf.1
  · exact Rat.le_trans hhalf.2 hsinhi

/-- The operational witness form of the box transport theorem.  A rational
    tangent `u` need not be an exact irrational-angle coordinate: it is enough
    to certify that its rational circle image lies inside the target sine box.
    This is the form suitable for finite nested-radical and inverse-bisection
    certificates. -/
theorem rationalCircleSinInterval_overlap_of_tangent_witness
    {S U : QInterval} (hS : subintervalOf S 0 1)
    (hU : subintervalOf U 0 1) (u : Rat)
    (hu : U.lo <= u ∧ u <= U.hi)
    (himage : S.lo <= rationalCircleSin u ∧
      rationalCircleSin u <= S.hi) :
    QInterval.Overlaps (rationalCircleSinInterval U) S := by
  have hsinLo := rationalCircleSin_mono hU.1 hu.1
    (Rat.le_trans hu.2 hU.2.2)
  have hsinHi := rationalCircleSin_mono
    (Rat.le_trans hU.1 hu.1) hu.2 hU.2.2
  unfold rationalCircleSinInterval QInterval.Overlaps
  constructor
  · exact Rat.le_trans hsinLo himage.2
  · exact Rat.le_trans himage.1 hsinHi

/-- The finite predicate checked by the rational tangent search. -/
def rationalTangentWitnessAdmissible (U S : QInterval) (u : Rat) : Prop :=
  U.lo <= u /\ u <= U.hi /\
    S.lo <= rationalCircleSin u /\ rationalCircleSin u <= S.hi

def rationalTangentWitnessAdmissibleBool
    (U S : QInterval) (u : Rat) : Bool :=
  (U.lo <= u) && (u <= U.hi) &&
    (S.lo <= rationalCircleSin u) && (rationalCircleSin u <= S.hi)

/-- Search a finite rational candidate list for a tangent witness.  The
    search is intentionally separate from the proof that the list succeeds:
    failed searches remain explicit `none`, while successful searches carry a
    finite, checkable certificate. -/
def rationalTangentWitnessSearchList
    (U S : QInterval) : List Rat -> Option Rat
  | [] => none
  | u :: us =>
      if rationalTangentWitnessAdmissibleBool U S u then some u
      else rationalTangentWitnessSearchList U S us

theorem rationalTangentWitnessSearchList_sound
    {U S : QInterval} {us : List Rat} {u : Rat}
    (h : rationalTangentWitnessSearchList U S us = some u) :
    rationalTangentWitnessAdmissibleBool U S u = true := by
  induction us with
  | nil => simp [rationalTangentWitnessSearchList] at h
  | cons v vs ih =>
      simp only [rationalTangentWitnessSearchList] at h
      split at h
      · cases h
        assumption
      · exact ih h

theorem rationalTangentWitnessSearchList_complete
    {U S : QInterval} {us : List Rat} {u : Rat}
    (hmem : u ∈ us)
    (hadm : rationalTangentWitnessAdmissibleBool U S u = true) :
    ∃ v, rationalTangentWitnessSearchList U S us = some v := by
  induction us with
  | nil => simp at hmem
  | cons q qs ih =>
      simp only [List.mem_cons] at hmem
      simp only [rationalTangentWitnessSearchList]
      split
      · exact ⟨q, rfl⟩
      · rcases hmem with rfl | hmem
        · contradiction
        · exact ih hmem

def rationalTangentWitnessGrid (m : Nat) : List Rat :=
  let N := 2 ^ m
  (List.range (N + 1)).map (fun k : Nat => (k : Rat) / (N : Rat))

def rationalTangentWitnessSearch
    (U S : QInterval) (m : Nat) : Option Rat :=
  rationalTangentWitnessSearchList U S (rationalTangentWitnessGrid m)

theorem rationalTangentWitnessSearch_complete_of_grid_candidate
    {U S : QInterval} (m k : Nat) (hk : k <= 2 ^ m)
    (hadm : rationalTangentWitnessAdmissibleBool U S
      ((k : Rat) / ((2 ^ m : Nat) : Rat)) = true) :
    ∃ v, rationalTangentWitnessSearch U S m = some v := by
  apply rationalTangentWitnessSearchList_complete
    (u := (k : Rat) / ((2 ^ m : Nat) : Rat))
  · unfold rationalTangentWitnessGrid
    let N := 2 ^ m
    have hk' : k < N + 1 := by dsimp [N]; omega
    apply List.mem_map.mpr
    exact ⟨k, by simpa using hk', rfl⟩
  · exact hadm

theorem rationalTangentWitnessSearch_sound
    {U S : QInterval} {m : Nat} {u : Rat}
    (h : rationalTangentWitnessSearch U S m = some u) :
    rationalTangentWitnessAdmissibleBool U S u = true := by
  exact rationalTangentWitnessSearchList_sound h

theorem rationalTangentWitnessSearch_sound_inequalities
    {U S : QInterval} {m : Nat} {u : Rat}
    (h : rationalTangentWitnessSearch U S m = some u) :
    U.lo <= u /\ u <= U.hi /\
      S.lo <= rationalCircleSin u /\ rationalCircleSin u <= S.hi := by
  have hb := rationalTangentWitnessSearch_sound h
  simp only [rationalTangentWitnessAdmissibleBool, Bool.and_eq_true] at hb
  refine ⟨of_decide_eq_true hb.1.1.1,
    of_decide_eq_true hb.1.1.2,
    of_decide_eq_true hb.1.2,
    of_decide_eq_true hb.2⟩

theorem rationalTangentWitnessSearch_overlap_of_success
    {U S : QInterval} (hU : subintervalOf U 0 1)
    (hS : subintervalOf S 0 1) {m : Nat} {u : Rat}
    (hsearch : rationalTangentWitnessSearch U S m = some u) :
    QInterval.Overlaps (rationalCircleSinInterval U) S := by
  have hw := rationalTangentWitnessSearch_sound_inequalities hsearch
  exact rationalCircleSinInterval_overlap_of_tangent_witness
    hS hU u ⟨hw.1, hw.2.1⟩ ⟨hw.2.2.1, hw.2.2.2⟩

theorem rationalGrid_interval_crossing
    {f : Rat -> Rat} {v : Nat -> Rat} {N : Nat}
    {lo hi : Rat} (hN : 0 < N)
    (hlo : 0 <= lo) (hhi : hi <= 1) (hlohi : lo <= hi)
    (hstart : f (v 0) = 0) (hend : f (v N) = 1)
    (hstep : forall k, k < N ->
      f (v (k + 1)) - f (v k) <= hi - lo) :
    exists k, k <= N /\ lo <= f (v k) /\ f (v k) <= hi := by
  by_cases hhit : exists k, k <= N /\ lo <= f (v k) /\ f (v k) <= hi
  · exact hhit
  · exfalso
    have hnone := hhit
    have hno : forall k, k <= N ->
        ¬(lo <= f (v k) /\ f (v k) <= hi) := by
      intro k hk
      intro hhit
      exact hnone ⟨k, hk, hhit.1, hhit.2⟩
    have hbelow : forall k, k <= N -> f (v k) < lo := by
      intro k hk
      induction k with
      | zero =>
          have hn := hno 0 (by omega)
          rw [hstart] at hn ⊢
          have hnot : ¬lo <= (0 : Rat) := by
            intro hzero
            apply hn
            exact ⟨hzero, by grind⟩
          exact Rat.not_le.mp hnot
      | succ k ih =>
          have hklt : k < N := by omega
          have hprev := ih (by omega)
          have hs := hstep k hklt
          have hupp : f (v (k + 1)) < hi := by
            have hstrict : f (v k) + (hi - lo) < hi := by
              grind
            grind [Rat.sub_eq_add_neg]
          have hn := hno (k + 1) hk
          have hnot : ¬lo <= f (v (k + 1)) := by
            intro hlow
            apply hn
            exact ⟨hlow, Rat.le_of_lt hupp⟩
          exact Rat.not_le.mp hnot
    have hfinal := hbelow N (by omega)
    rw [hend] at hfinal
    exact by grind

/-! Endpoint-parametric version of the finite crossing argument. -/
theorem rationalGrid_interval_crossing_between
    {f : Rat -> Rat} {v : Nat -> Rat} {N : Nat}
    {lo hi : Rat} (hN : 0 < N) (hlohi : lo <= hi)
    (hstart : f (v 0) <= hi) (hend : lo <= f (v N))
    (hstep : forall k, k < N ->
      f (v (k + 1)) - f (v k) <= hi - lo) :
    exists k, k <= N /\ lo <= f (v k) /\ f (v k) <= hi := by
  by_cases hhit : exists k, k <= N /\ lo <= f (v k) /\ f (v k) <= hi
  · exact hhit
  · exfalso
    have hno : forall k, k <= N ->
        ¬(lo <= f (v k) /\ f (v k) <= hi) := by
      intro k hk hbad
      exact hhit ⟨k, hk, hbad.1, hbad.2⟩
    have hbelow : forall k, k <= N -> f (v k) < lo := by
      intro k hk
      induction k with
      | zero =>
          have hn := hno 0 (by omega)
          have hnot : ¬lo <= f (v 0) := by
            intro hlow
            apply hn
            exact ⟨hlow, Rat.le_trans hstart (by grind)⟩
          exact Rat.not_le.mp hnot
      | succ k ih =>
          have hklt : k < N := by omega
          have hprev := ih (by omega)
          have hs := hstep k hklt
          have hupp : f (v (k + 1)) < hi := by
            have hstrict : f (v k) + (hi - lo) < hi := by grind
            grind [Rat.sub_eq_add_neg]
          have hn := hno (k + 1) hk
          have hnot : ¬lo <= f (v (k + 1)) := by
            intro hlow
            apply hn
            exact ⟨hlow, Rat.le_of_lt hupp⟩
          exact Rat.not_le.mp hnot
    exact (Rat.not_lt.mpr hend) (hbelow N (by omega))

theorem rationalCircleSin_bounds {u : Rat} (hu : 0 <= u) (hu1 : u <= 1) :
    0 <= rationalCircleSin u /\ rationalCircleSin u <= 1 := by
  have hzero : rationalCircleSin (0 : Rat) = 0 := by
    decide +kernel
  have hone : rationalCircleSin (1 : Rat) = 1 := by
    decide +kernel
  have hmono0 := rationalCircleSin_mono (a := 0) (b := u)
    (by decide +kernel) hu hu1
  have hmon1 := rationalCircleSin_mono (a := u) (b := 1)
    hu hu1 (by decide +kernel)
  rw [hzero] at hmono0
  rw [hone] at hmon1
  exact ⟨hmono0, hmon1⟩

private theorem rationalCircleSin_width_le {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (hb : b <= 1) :
    rationalCircleSin b - rationalCircleSin a <= 2 * (b - a) := by
  have hb0 : 0 <= b := Rat.le_trans ha hab
  have hba : 0 <= b - a := by grind
  have habprod : a * b <= 1 := by
    have h := Rat.mul_le_mul_of_nonneg_right hb ha
    grind [Rat.sub_eq_add_neg]
  have hden : 0 < (1 + a * a) * (1 + b * b) :=
    Rat.mul_pos (rationalCircleSin_den_pos ha)
      (rationalCircleSin_den_pos hb0)
  have hden_one : 1 <= (1 + a * a) * (1 + b * b) := by
    have haa : 0 <= a * a := Rat.mul_nonneg ha ha
    have hbb : 0 <= b * b := Rat.mul_nonneg hb0 hb0
    have hsum : 0 <= a * a + b * b + (a * a) * (b * b) := by
      exact Rat.add_nonneg (Rat.add_nonneg haa hbb)
        (Rat.mul_nonneg haa hbb)
    grind [Rat.mul_add, Rat.add_mul]
  rw [rationalCircleSin_sub_formula ha hb0]
  apply Rat.le_of_mul_le_mul_right (c :=
    (1 + a * a) * (1 + b * b))
  · rw [Rat.div_def]
    let D : Rat := (1 + a * a) * (1 + b * b)
    let N : Rat := 2 * (b - a) * (1 - a * b)
    have hD : D = (1 + a * a) * (1 + b * b) := rfl
    have hcancel : D⁻¹ * D = 1 :=
      Rat.inv_mul_cancel D (Rat.ne_of_gt hden)
    have hNnonneg : 0 <= N := by
      dsimp [N]
      exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hba) (by grind)
    have hNle : N <= 2 * (b - a) := by
      dsimp [N]
      have hp : 0 <= a * b := Rat.mul_nonneg ha hb0
      have hfactor : 1 - a * b <= 1 := by
        grind only [Rat.sub_eq_add_neg]
      exact (by
        calc
          2 * (b - a) * (1 - a * b) <=
              2 * (b - a) * 1 := by
            exact Rat.mul_le_mul_of_nonneg_left hfactor
              (Rat.mul_nonneg (by decide +kernel) hba)
          _ = 2 * (b - a) := by simp)
    calc
      (N * D⁻¹) * D = N := by
        rw [Rat.mul_assoc, hcancel, Rat.mul_one]
      _ <= 2 * (b - a) * 1 := by simpa using hNle
      _ <= 2 * (b - a) * D := by
        exact Rat.mul_le_mul_of_nonneg_left hden_one
          (Rat.mul_nonneg (by decide +kernel) hba)
  · exact hden

/-- The circle-coordinate evaluator has an explicit rational modulus: on the
unit slope interval, changing the slope box by width `w` changes the sine
box by at most `2*w`. -/
theorem rationalCircleSinInterval_width_le
    {U : QInterval} (hU : subintervalOf U 0 1) :
    0 <= (rationalCircleSinInterval U).width /\
      (rationalCircleSinInterval U).width <= 2 * U.width := by
  have hsin := rationalCircleSin_width_le hU.1 hU.2.1 hU.2.2
  have hmono := rationalCircleSin_mono hU.1 hU.2.1 hU.2.2
  unfold rationalCircleSinInterval QInterval.width
  constructor
  · grind
  · exact hsin

theorem rationalCircleSinInterval_bounds
    {U : QInterval} (hU : subintervalOf U 0 1) :
    0 <= (rationalCircleSinInterval U).lo /\
      (rationalCircleSinInterval U).hi <= 1 := by
  have hlo := rationalCircleSin_bounds hU.1
    (Rat.le_trans hU.2.1 hU.2.2)
  have hhi := rationalCircleSin_bounds
    (Rat.le_trans hU.1 hU.2.1) hU.2.2
  simpa [rationalCircleSinInterval] using And.intro hlo.1 hhi.2

/-! Two interval sine evaluations overlap whenever their tangent input boxes
share a rational slope.  This is the finite geometric core used when a
transport proof refines two different subdivision schemes to a common
rational witness. -/
theorem rationalCircleSinInterval_overlap_of_common_point
    {U V : QInterval} (hU : subintervalOf U 0 1)
    (hV : subintervalOf V 0 1) (u : Rat)
    (hUu : U.lo <= u ∧ u <= U.hi)
    (hVu : V.lo <= u ∧ u <= V.hi) :
    QInterval.Overlaps
      (rationalCircleSinInterval U)
      (rationalCircleSinInterval V) := by
  have hsinUlo := rationalCircleSin_mono hU.1 hUu.1
    (Rat.le_trans hUu.2 hU.2.2)
  have hsinUhi := rationalCircleSin_mono
    (Rat.le_trans hU.1 hUu.1) hUu.2 hU.2.2
  have hsinVlo := rationalCircleSin_mono hV.1 hVu.1
    (Rat.le_trans hVu.2 hV.2.2)
  have hsinVhi := rationalCircleSin_mono
    (Rat.le_trans hV.1 hVu.1) hVu.2 hV.2.2
  unfold rationalCircleSinInterval QInterval.Overlaps
  constructor <;> grind

theorem rationalCircleSinInterval_overlap_of_input_overlap
    {U V : QInterval} (hU : subintervalOf U 0 1)
    (hV : subintervalOf V 0 1)
    (hover : QInterval.Overlaps U V) :
    QInterval.Overlaps
      (rationalCircleSinInterval U)
      (rationalCircleSinInterval V) := by
  let u : Rat := max U.lo V.lo
  have huUlo : U.lo <= u := by
    dsimp [u]
    rw [Rat.max_def]
    split <;> grind
  have huVlo : V.lo <= u := by
    dsimp [u]
    rw [Rat.max_def]
    split <;> grind
  have huUhi : u <= U.hi := by
    dsimp [u]
    rw [Rat.max_def]
    split <;> grind [hover.2, hU.2.1]
  have huVhi : u <= V.hi := by
    dsimp [u]
    rw [Rat.max_def]
    split <;> grind [hover.1, hV.2.1]
  exact rationalCircleSinInterval_overlap_of_common_point hU hV u
    ⟨huUlo, huUhi⟩ ⟨huVlo, huVhi⟩

theorem rationalCircleSin_difference_le_qabs
    {a b : Rat} (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hb1 : b <= 1) :
    qabs (rationalCircleSin a - rationalCircleSin b) <=
      2 * qabs (a - b) := by
  by_cases hab : a <= b
  · have hsin := rationalCircleSin_width_le ha0 hab hb1
    have hmono := rationalCircleSin_mono ha0 hab hb1
    have hdiff : 0 <= rationalCircleSin b - rationalCircleSin a := by
      have hnon : 0 <= 2 * (b - a) := by
        exact Rat.mul_nonneg (by decide +kernel) (by grind)
      grind
    rw [show rationalCircleSin a - rationalCircleSin b =
        -(rationalCircleSin b - rationalCircleSin a) by
          grind [Rat.sub_eq_add_neg], qabs_neg,
      qabs_eq_self_of_nonneg hdiff]
    rw [show qabs (a - b) = b - a by
      rw [show a - b = -(b - a) by grind [Rat.sub_eq_add_neg], qabs_neg,
        qabs_eq_self_of_nonneg (by grind : 0 <= b - a)]]
    exact hsin
  · have hba : b <= a := by grind
    have hsin := rationalCircleSin_width_le hb0 hba ha1
    have hmono := rationalCircleSin_mono hb0 hba ha1
    have hdiff : 0 <= rationalCircleSin a - rationalCircleSin b := by
      have hnon : 0 <= 2 * (a - b) := by
        exact Rat.mul_nonneg (by decide +kernel) (by grind)
      grind
    rw [qabs_eq_self_of_nonneg hdiff]
    rw [show qabs (a - b) = a - b by
      exact qabs_eq_self_of_nonneg (by grind)]
    exact hsin

def rationalTangentWitnessBoxGrid (U : QInterval) (m : Nat) : List Rat :=
  let N := 2 ^ m
  (List.range (N + 1)).map (fun k : Nat =>
    U.lo + U.width * ((k : Rat) / (N : Rat)))

def rationalTangentWitnessBoxSearch
    (U S : QInterval) (m : Nat) : Option Rat :=
  rationalTangentWitnessSearchList U S
    (rationalTangentWitnessBoxGrid U m)

theorem rationalTangentWitnessBoxSearch_complete_of_zero_target
    {U : QInterval} (hU : subintervalOf U 0 1)
    (hover : QInterval.Overlaps U ({ lo := 0, hi := 0 } : QInterval)) :
    ∃ u, rationalTangentWitnessBoxSearch U
      ({ lo := 0, hi := 0 } : QInterval) 0 = some u := by
  have hUlo : U.lo = 0 := by
    grind [hover.1, hU.1]
  have hmem : U.lo ∈ rationalTangentWitnessBoxGrid U 0 := by
    unfold rationalTangentWitnessBoxGrid
    apply List.mem_map.mpr
    exact ⟨0, by decide +kernel, by
      simp [QInterval.width]
      grind⟩
  apply rationalTangentWitnessSearchList_complete hmem
  unfold rationalTangentWitnessAdmissibleBool
  simp [hUlo, rationalCircleSin]
  exact ⟨⟨by simpa using hover.2, by decide +kernel⟩, by decide +kernel⟩

theorem rationalTangentWitnessBoxSearch_complete_of_one_target
    {U : QInterval} (hU : subintervalOf U 0 1)
    (hover : QInterval.Overlaps U ({ lo := 1, hi := 1 } : QInterval)) :
    ∃ u, rationalTangentWitnessBoxSearch U
      ({ lo := 1, hi := 1 } : QInterval) 0 = some u := by
  have hUhi : U.hi = 1 := by
    grind [hU.2.2, hover.2]
  have hmem : U.hi ∈ rationalTangentWitnessBoxGrid U 0 := by
    unfold rationalTangentWitnessBoxGrid
    apply List.mem_map.mpr
    exact ⟨1, by decide +kernel, by
      simp [QInterval.width]
      grind⟩
  apply rationalTangentWitnessSearchList_complete hmem
  unfold rationalTangentWitnessAdmissibleBool
  simp [hUhi, rationalCircleSin]
  have hlo : U.lo <= 1 := Rat.le_trans hU.2.1 hU.2.2
  exact ⟨⟨hlo, by decide +kernel⟩, by decide +kernel⟩

theorem rationalTangentWitnessBoxSearch_complete_of_overlap
    {U S : QInterval} (hU : subintervalOf U 0 1)
    (hS : subintervalOf S 0 1) (m : Nat)
    (hover : QInterval.Overlaps
      (rationalCircleSinInterval U) S)
    (hmesh : 2 * U.width / (((2 ^ m : Nat) : Rat)) <= S.width) :
    ∃ v, rationalTangentWitnessBoxSearch U S m = some v := by
  let N : Nat := 2 ^ m
  let d : Rat := (N : Rat)
  let v : Nat -> Rat := fun k =>
    U.lo + U.width * ((k : Rat) / d)
  have hN : 0 < N := by
    dsimp [N]
    exact Nat.two_pow_pos m
  have hd : 0 < d := by
    dsimp [d]
    exact (Rat.natCast_pos).2 hN
  have hwidth : 0 <= U.width := by
    unfold QInterval.width
    grind [hU.2.1]
  have hq_bounds : forall k, k <= N ->
      0 <= (k : Rat) / d /\ (k : Rat) / d <= 1 := by
    intro k hk
    rw [Rat.div_def]
    constructor
    · exact Rat.mul_nonneg Rat.natCast_nonneg
        (Rat.le_of_lt (Rat.inv_pos.2 hd))
    · apply Rat.le_of_mul_le_mul_right (c := d)
      · rw [Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hd), Rat.mul_one]
        simpa [N, d] using (show (k : Rat) <= (N : Rat) by exact_mod_cast hk)
      · exact hd
  have hv_interval : forall k, k <= N ->
      U.lo <= v k /\ v k <= U.hi := by
    intro k hk
    have hq := hq_bounds k hk
    constructor
    · dsimp [v]
      grind [Rat.mul_nonneg hwidth hq.1]
    · dsimp [v]
      have hmul := Rat.mul_le_mul_of_nonneg_left hq.2 hwidth
      unfold QInterval.width at hmul ⊢
      grind
  have hv0 : v 0 = U.lo := by
    dsimp [v]
    rw [Rat.div_def]
    simp
    grind
  have hvN : v N = U.hi := by
    dsimp [v, d]
    rw [Rat.div_def, Rat.mul_inv_cancel _ (Rat.ne_of_gt hd), Rat.mul_one]
    unfold QInterval.width
    grind
  have hstart : rationalCircleSin (v 0) <= S.hi := by
    rw [hv0]
    exact hover.1
  have hend : S.lo <= rationalCircleSin (v N) := by
    rw [hvN]
    exact hover.2
  have hstep : forall k, k < N ->
      rationalCircleSin (v (k + 1)) - rationalCircleSin (v k) <=
        S.hi - S.lo := by
    intro k hk
    have hk1 : k + 1 <= N := by omega
    have hleft := hv_interval k (by omega)
    have hright := hv_interval (k + 1) hk1
    have hleft0 : 0 <= v k := Rat.le_trans hU.1 hleft.1
    have hleft1 : v k <= 1 := Rat.le_trans hleft.2 hU.2.2
    have hright0 : 0 <= v (k + 1) := Rat.le_trans hU.1 hright.1
    have hright1 : v (k + 1) <= 1 := Rat.le_trans hright.2 hU.2.2
    have hdiff := rationalCircleSin_difference_le_qabs
      hleft0 hleft1 hright0 hright1
      (a := v k) (b := v (k + 1))
    have horder : v k <= v (k + 1) := by
      dsimp [v]
      apply (Rat.add_le_add_left).2
      apply Rat.mul_le_mul_of_nonneg_left _ hwidth
      rw [Rat.div_def, Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.le_succ k)
        (Rat.le_of_lt (Rat.inv_pos.2 hd))
    have hdiff' : rationalCircleSin (v (k + 1)) - rationalCircleSin (v k) <=
        2 * (v (k + 1) - v k) := by
      have hqabs := hdiff
      rw [show qabs (v k - v (k + 1)) = v (k + 1) - v k by
        rw [show v k - v (k + 1) = -(v (k + 1) - v k) by grind [Rat.sub_eq_add_neg],
          qabs_neg, qabs_eq_self_of_nonneg (by grind)]] at hqabs
      have hnon : 0 <= rationalCircleSin (v (k + 1)) - rationalCircleSin (v k) := by
        grind [rationalCircleSin_mono hleft0 horder hright1]
      rw [show qabs (rationalCircleSin (v k) - rationalCircleSin (v (k + 1))) =
        rationalCircleSin (v (k + 1)) - rationalCircleSin (v k) by
        rw [show rationalCircleSin (v k) - rationalCircleSin (v (k + 1)) =
          -(rationalCircleSin (v (k + 1)) - rationalCircleSin (v k)) by grind [Rat.sub_eq_add_neg],
          qabs_neg, qabs_eq_self_of_nonneg hnon]] at hqabs
      exact hqabs
    have hmesh' : 2 * (v (k + 1) - v k) <= S.width := by
      dsimp [v, d]
      unfold QInterval.width at hmesh ⊢
      rw [Rat.div_def, Rat.div_def]
      grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
    exact Rat.le_trans hdiff' hmesh'
  obtain ⟨k, hk, hlow, hhigh⟩ := rationalGrid_interval_crossing_between
    hN hS.2.1 hstart hend hstep
  have hmem : v k ∈ rationalTangentWitnessBoxGrid U m := by
    unfold rationalTangentWitnessBoxGrid
    apply List.mem_map.mpr
    let N' := 2 ^ m
    have hk' : k < N' + 1 := by dsimp [N']; omega
    exact ⟨k, by simpa [N'] using hk', by simpa [v, d, N]⟩
  apply rationalTangentWitnessSearchList_complete hmem
  have hbox := hv_interval k hk
  simp only [rationalTangentWitnessAdmissibleBool, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [decide_eq_true_eq]
    exact hbox.1
  · simp only [decide_eq_true_eq]
    exact hbox.2
  · simp only [decide_eq_true_eq]
    exact hlow
  · simp only [decide_eq_true_eq]
    exact hhigh

/-! A positive rational target box is eventually fine enough for the grid.
The denominator of its width supplies an explicit precision; this is the
finite rational replacement for an appeal to a real Archimedean theorem. -/
theorem exists_rationalTangentWitnessBoxSearch_of_overlap_of_positive_width
    {U S : QInterval} (hU : subintervalOf U 0 1)
    (hS : subintervalOf S 0 1)
    (hover : QInterval.Overlaps (rationalCircleSinInterval U) S)
    (hwidth : 0 < S.width) :
    ∃ m u, rationalTangentWitnessBoxSearch U S m = some u := by
  let d : Nat := S.width.den + 1
  let m : Nat := d + 1
  have hd : 0 < d := by
    dsimp [d]
    omega
  have hpow : d <= 2 ^ d := by
    induction d with
    | zero => omega
    | succ d ih =>
        rw [Nat.pow_succ]
        have hone : 1 <= 2 ^ d := Nat.one_le_pow d 2 (by omega)
        omega
  have hpow' : d <= 2 ^ m := by
    dsimp [m]
    rw [Nat.pow_succ]
    exact Nat.le_trans hpow (by omega)
  have hmesh0 :
      2 / (((2 ^ m : Nat) : Rat)) <= 1 / ((d : Nat) : Rat) := by
    have hid :
        2 / (((2 ^ m : Nat) : Rat)) =
          1 / (((2 ^ d : Nat) : Rat)) := by
      dsimp [m]
      rw [Nat.pow_succ]
      rw [Rat.div_def, Rat.div_def]
      have hpowne : ((2 ^ d : Nat) : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.two_pow_pos d))
      have htwo : (2 : Rat) ≠ 0 := by decide +kernel
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    rw [hid]
    apply FTC.one_div_nat_antitone
      (n := d) (m := 2 ^ d)
    · exact hd
    · exact Nat.two_pow_pos d
    · exact hpow
  have hsmall : 1 / ((d : Nat) : Rat) <= S.width := by
    dsimp [d]
    exact FTC.one_div_den_succ_le_of_pos hwidth
  have hmesh :
    2 * U.width / (((2 ^ m : Nat) : Rat)) <= S.width := by
    have hUwidth : U.width <= 1 := by
      unfold QInterval.width
      grind [hU.1, hU.2.1, hU.2.2]
    have hpowRat : 0 < ((2 ^ m : Nat) : Rat) := by
      exact (Rat.natCast_pos).2 (Nat.two_pow_pos m)
    have hfirst :
        2 * U.width / (((2 ^ m : Nat) : Rat)) <=
          2 / (((2 ^ m : Nat) : Rat)) := by
      apply Rat.le_of_mul_le_mul_right
        (c := ((2 ^ m : Nat) : Rat))
      · rw [Rat.div_def, Rat.div_def]
        have hpowne : ((2 ^ m : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hpowRat
        have hcancel := Rat.mul_inv_cancel ((2 ^ m : Nat) : Rat) hpowne
        grind [Rat.mul_assoc, Rat.mul_comm]
      · exact hpowRat
    exact Rat.le_trans hfirst (Rat.le_trans hmesh0 hsmall)
  refine ⟨m, ?_⟩
  exact rationalTangentWitnessBoxSearch_complete_of_overlap
    hU hS m hover hmesh

theorem rationalTangentWitnessBoxSearch_overlap_of_success
    {U S : QInterval} (hU : subintervalOf U 0 1)
    (hS : subintervalOf S 0 1) {m : Nat} {u : Rat}
    (hsearch : rationalTangentWitnessBoxSearch U S m = some u) :
    QInterval.Overlaps (rationalCircleSinInterval U) S := by
  have hw : rationalTangentWitnessAdmissibleBool U S u = true := by
    unfold rationalTangentWitnessBoxSearch at hsearch
    exact rationalTangentWitnessSearchList_sound hsearch
  simp only [rationalTangentWitnessAdmissibleBool, Bool.and_eq_true] at hw
  apply rationalCircleSinInterval_overlap_of_tangent_witness hS hU u
  · exact ⟨of_decide_eq_true hw.1.1.1,
      of_decide_eq_true hw.1.1.2⟩
  · exact ⟨of_decide_eq_true hw.1.2,
      of_decide_eq_true hw.2⟩

theorem rationalTangentWitnessBoxSearch_sound_inequalities
    {U S : QInterval} {m : Nat} {u : Rat}
    (hsearch : rationalTangentWitnessBoxSearch U S m = some u) :
    U.lo <= u /\ u <= U.hi /\
      S.lo <= rationalCircleSin u /\ rationalCircleSin u <= S.hi := by
  have hw : rationalTangentWitnessAdmissibleBool U S u = true := by
    unfold rationalTangentWitnessBoxSearch at hsearch
    exact rationalTangentWitnessSearchList_sound hsearch
  simp only [rationalTangentWitnessAdmissibleBool, Bool.and_eq_true] at hw
  exact ⟨of_decide_eq_true hw.1.1.1,
    of_decide_eq_true hw.1.1.2,
    of_decide_eq_true hw.1.2,
    of_decide_eq_true hw.2⟩

theorem rationalCircleSin_dyadic_grid_hit
    {S : QInterval} (hS : subintervalOf S 0 1)
    (N : Nat) (hN : 0 < N)
    (hmesh : 2 / ((N : Nat) : Rat) <= S.width) :
    exists k, k <= N /\
      S.lo <= rationalCircleSin ((k : Rat) / (N : Rat)) /\
      rationalCircleSin ((k : Rat) / (N : Rat)) <= S.hi := by
  let d : Rat := (N : Rat)
  let v : Nat -> Rat := fun k => (k : Rat) / d
  have hd : 0 < d := by
    dsimp [d]
    exact (Rat.natCast_pos).2 hN
  have hzero : rationalCircleSin (0 : Rat) = 0 := by
    decide +kernel
  have hone : rationalCircleSin (1 : Rat) = 1 := by
    decide +kernel
  have hstart : rationalCircleSin (v 0) = 0 := by
    have hv0 : v 0 = 0 := by
      dsimp [v, d]
      rw [Rat.div_def]
      simp
    rw [hv0, hzero]
  have hend : rationalCircleSin (v N) = 1 := by
    dsimp [v, d]
    rw [Rat.div_def]
    have hcancel : (N : Rat) * (N : Rat)⁻¹ = 1 :=
      Rat.mul_inv_cancel _ (Rat.ne_of_gt hd)
    rw [hcancel]
    exact hone
  have hstep : forall k, k < N ->
      rationalCircleSin (v (k + 1)) - rationalCircleSin (v k) <=
        S.hi - S.lo := by
    intro k hk
    have hk1 : k + 1 <= N := by omega
    have hqk0 : 0 <= v k := by
      dsimp [v]
      rw [Rat.div_def]
      exact Rat.mul_nonneg (Rat.natCast_nonneg)
        (Rat.le_of_lt (Rat.inv_pos.2 hd))
    have hqk1 : v k <= 1 := by
      dsimp [v, d]
      rw [Rat.div_def]
      apply Rat.le_of_mul_le_mul_right (c := (N : Rat))
      · rw [Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hd), Rat.mul_one]
        simpa using (show (k : Rat) <= (N : Rat) by
          exact_mod_cast Nat.le_of_lt hk)
      · exact hd
    have hqnext0 : 0 <= v (k + 1) := by
      dsimp [v]
      rw [Rat.div_def]
      exact Rat.mul_nonneg (Rat.natCast_nonneg)
        (Rat.le_of_lt (Rat.inv_pos.2 hd))
    have hqnext1 : v (k + 1) <= 1 := by
      dsimp [v, d]
      rw [Rat.div_def]
      apply Rat.le_of_mul_le_mul_right (c := (N : Rat))
      · rw [Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hd), Rat.mul_one]
        simpa using (show (k + 1 : Rat) <= (N : Rat) by
          exact_mod_cast hk1)
      · exact hd
    have hdiff := rationalCircleSin_difference_le_qabs
      hqk0 hqk1 hqnext0 hqnext1
        (a := v k) (b := v (k + 1))
    have horder : v k <= v (k + 1) := by
      dsimp [v, d]
      rw [Rat.div_def, Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.le_succ k)
        (Rat.le_of_lt (Rat.inv_pos.2 hd))
    have hdiff' : rationalCircleSin (v (k + 1)) - rationalCircleSin (v k) <=
        2 * (v (k + 1) - v k) := by
      have hqabs := hdiff
      rw [show qabs (v k - v (k + 1)) = v (k + 1) - v k by
        rw [show v k - v (k + 1) = -(v (k + 1) - v k) by
          grind [Rat.sub_eq_add_neg], qabs_neg,
          qabs_eq_self_of_nonneg (by grind)],
        show qabs (rationalCircleSin (v k) - rationalCircleSin (v (k + 1))) =
          rationalCircleSin (v (k + 1)) - rationalCircleSin (v k) by
          rw [show rationalCircleSin (v k) - rationalCircleSin (v (k + 1)) =
            -(rationalCircleSin (v (k + 1)) - rationalCircleSin (v k)) by
              grind [Rat.sub_eq_add_neg], qabs_neg,
            qabs_eq_self_of_nonneg (by
              grind [rationalCircleSin_mono hqk0 horder hqnext1])]] at hqabs
      exact hqabs
    have hmesh' : 2 * (v (k + 1) - v k) <= S.width := by
      dsimp [v, d, QInterval.width]
      rw [Rat.div_def, Rat.div_def]
      have hcancel := Rat.inv_mul_cancel (N : Rat) (Rat.ne_of_gt hd)
      have hkcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
        exact_mod_cast Nat.add_one k
      calc
        2 * (((k + 1 : Nat) : Rat) * (N : Rat)⁻¹ - (k : Rat) * (N : Rat)⁻¹) =
            2 / (N : Rat) := by grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
        _ <= S.hi - S.lo := hmesh
    exact Rat.le_trans hdiff' hmesh'
  have hcross := rationalGrid_interval_crossing
    (f := rationalCircleSin) (v := v) (lo := S.lo) (hi := S.hi)
    hN hS.1 hS.2.2 hS.2.1 hstart hend hstep
  simpa [v, d] using hcross

/-! The grid lemma feeds directly into the executable search when the input
box is the full unit tangent chart.  This is the closed, finite certificate
used as a regression point before narrowing the chart to an inverse-arctan
box. -/
theorem rationalTangentWitnessSearch_unit_complete
    {S : QInterval} (hS : subintervalOf S 0 1)
    (m : Nat)
    (hmesh : 2 / (((2 ^ m : Nat) : Rat)) <= S.width) :
    ∃ v, rationalTangentWitnessSearch
      ({ lo := 0, hi := 1 } : QInterval) S m = some v := by
  let N : Nat := 2 ^ m
  have hN : 0 < N := by
    dsimp [N]
    exact Nat.two_pow_pos m
  obtain ⟨k, hk, hlow, hhigh⟩ := rationalCircleSin_dyadic_grid_hit
    hS N hN (by simpa [N] using hmesh)
  have hq0 : 0 <= (k : Rat) / ((2 ^ m : Nat) : Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.natCast_nonneg)
      (Rat.le_of_lt ((Rat.inv_pos).2
        ((Rat.natCast_pos).2 (Nat.two_pow_pos m))))
  have hq1 : (k : Rat) / ((2 ^ m : Nat) : Rat) <= 1 := by
    rw [Rat.div_def]
    apply Rat.le_of_mul_le_mul_right
      (c := ((2 ^ m : Nat) : Rat))
    · rw [Rat.mul_assoc,
        Rat.inv_mul_cancel _ (Rat.ne_of_gt
          ((Rat.natCast_pos).2 (Nat.two_pow_pos m))), Rat.mul_one]
      simpa using (show (k : Rat) <= ((2 ^ m : Nat) : Rat) by
        exact_mod_cast (by simpa [N] using hk))
    · exact (Rat.natCast_pos).2 (Nat.two_pow_pos m)
  apply rationalTangentWitnessSearch_complete_of_grid_candidate
    (U := ({ lo := 0, hi := 1 } : QInterval)) (S := S) m k
  · simpa [N] using hk
  · simp only [rationalTangentWitnessAdmissibleBool, Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simp only [decide_eq_true_eq]
      exact hq0
    · simp only [decide_eq_true_eq]
      exact hq1
    · simp only [decide_eq_true_eq]
      exact hlow
    · simp only [decide_eq_true_eq]
      exact hhigh

theorem rationalCircleSinInterval_near_of_near
    {U V : QInterval} (hU : subintervalOf U 0 1)
    (hV : subintervalOf V 0 1) (eps : QPos)
    (hnear : QInterval.NearAt U V eps) :
    QInterval.NearAt (rationalCircleSinInterval U)
      (rationalCircleSinInterval V)
      { val := 2 * eps.val
        property := Rat.mul_pos (by decide +kernel) eps.property } := by
  have hUwidth := rationalCircleSinInterval_width_le hU
  have hVwidth := rationalCircleSinInterval_width_le hV
  have hleft :
      rationalCircleSin U.lo <= rationalCircleSin V.hi + 2 * eps.val := by
    by_cases huv : U.lo <= V.hi
    · have hmono := rationalCircleSin_mono hU.1 huv hV.2.2
      grind
    · have hdiff : V.hi <= U.lo := by grind
      have hVhi0 : 0 <= V.hi := Rat.le_trans hV.1 hV.2.1
      have hUlo1 : U.lo <= 1 := Rat.le_trans hU.2.1 hU.2.2
      have hq := rationalCircleSin_difference_le_qabs
        hVhi0 hV.2.2 hU.1 hUlo1
          (a := V.hi) (b := U.lo)
      have hdelta : U.lo - V.hi <= eps.val := by grind [hnear.1]
      rw [show qabs (V.hi - U.lo) = U.lo - V.hi by
        rw [show V.hi - U.lo = -(U.lo - V.hi) by grind [Rat.sub_eq_add_neg],
          qabs_neg, qabs_eq_self_of_nonneg (by grind)]] at hq
      have hq' : qabs (rationalCircleSin U.lo -
          rationalCircleSin V.hi) <= 2 * (U.lo - V.hi) := by
        simpa [show rationalCircleSin U.lo - rationalCircleSin V.hi =
          -(rationalCircleSin V.hi - rationalCircleSin U.lo) by
            grind [Rat.sub_eq_add_neg], qabs_neg] using hq
      have hself := self_le_qabs
        (rationalCircleSin U.lo - rationalCircleSin V.hi)
      grind
  have hright :
      rationalCircleSin V.lo <= rationalCircleSin U.hi + 2 * eps.val := by
    by_cases huv : V.lo <= U.hi
    · have hmono := rationalCircleSin_mono hV.1 huv hU.2.2
      grind
    · have hdiff : U.hi <= V.lo := by grind
      have hUhi0 : 0 <= U.hi := Rat.le_trans hU.1 hU.2.1
      have hVlo1 : V.lo <= 1 := Rat.le_trans hV.2.1 hV.2.2
      have hq := rationalCircleSin_difference_le_qabs
        hUhi0 hU.2.2 hV.1 hVlo1
          (a := U.hi) (b := V.lo)
      have hdelta : V.lo - U.hi <= eps.val := by grind [hnear.2.1]
      rw [show qabs (U.hi - V.lo) = V.lo - U.hi by
        rw [show U.hi - V.lo = -(V.lo - U.hi) by grind [Rat.sub_eq_add_neg],
          qabs_neg, qabs_eq_self_of_nonneg (by grind)]] at hq
      have hq' : qabs (rationalCircleSin V.lo -
          rationalCircleSin U.hi) <= 2 * (V.lo - U.hi) := by
        simpa [show rationalCircleSin V.lo - rationalCircleSin U.hi =
          -(rationalCircleSin U.hi - rationalCircleSin V.lo) by
            grind [Rat.sub_eq_add_neg], qabs_neg] using hq
      have hself := self_le_qabs
        (rationalCircleSin V.lo - rationalCircleSin U.hi)
      grind
  unfold QInterval.NearAt rationalCircleSinInterval
  dsimp
  change rationalCircleSin U.lo <=
      rationalCircleSin V.hi + 2 * eps.val /\
    rationalCircleSin V.lo <=
      rationalCircleSin U.hi + 2 * eps.val /\
    rationalCircleSin U.hi - rationalCircleSin U.lo <= 2 * eps.val /\
    rationalCircleSin V.hi - rationalCircleSin V.lo <= 2 * eps.val
  constructor
  · exact hleft
  constructor
  · exact hright
  constructor
  · have hwidth := hUwidth.2
    have hsmall := hnear.2.2.1
    have hwidth' : rationalCircleSin U.hi - rationalCircleSin U.lo <=
        2 * U.width := by
      simpa [rationalCircleSinInterval, QInterval.width] using hwidth
    grind
  · have hwidth := hVwidth.2
    have hsmall := hnear.2.2.2
    have hwidth' : rationalCircleSin V.hi - rationalCircleSin V.lo <=
        2 * V.width := by
      simpa [rationalCircleSinInterval, QInterval.width] using hwidth
    grind

theorem rationalCircleSinInterval_valid
    (u : Nat -> QInterval)
    (hu : RealCompute.ValidCompute u)
    (hubounds : forall n, 0 <= (u n).lo /\ (u n).hi <= 1) :
    RealCompute.ValidCompute (fun n => rationalCircleSinInterval (u n)) := by
  constructor
  · intro n
    have horder : (u n).lo <= (u n).hi := by
      have := hu.1 n
      grind [QInterval.width]
    have hmono := rationalCircleSin_mono
      (hubounds n).1 horder (hubounds n).2
    change rationalCircleSin (u n).hi - rationalCircleSin (u n).lo >= 0
    grind
  constructor
  · intro n m hnm
    have hn := hu.2.1 n m hnm
    have hnl := hubounds n
    have hml := hubounds m
    have hlo := rationalCircleSin_mono hnl.1 hn.1
      (Rat.le_trans hn.2.1 hml.2)
    have hmid := rationalCircleSin_mono hml.1 hn.2.1 hml.2
    have hhi := rationalCircleSin_mono
      (Rat.le_trans hml.1 hn.2.1) hn.2.2 hnl.2
    exact ⟨hlo, hmid, hhi⟩
  · intro eps
    have htwo_pos : 0 < (2 : Rat) := by decide +kernel
    let half : QPos := ⟨eps.val / 2, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property ((Rat.inv_pos).2 htwo_pos)⟩
    obtain ⟨N, hN⟩ := hu.2.2 half
    refine ⟨N, ?_⟩
    intro n hn
    have horder : (u n).lo <= (u n).hi := by
      have := hu.1 n
      grind [QInterval.width]
    have hw := rationalCircleSin_width_le
      (hubounds n).1 horder (hubounds n).2
    have hsmall := hN n hn
    have hscaled := Rat.mul_le_mul_of_nonneg_left hsmall
      (by decide +kernel : (0 : Rat) <= 2)
    change rationalCircleSin (u n).hi - rationalCircleSin (u n).lo <= eps.val
    have hhalf : 2 * half.val = eps.val := by
      dsimp [half]
      rw [Rat.div_def]
      have htwo : (2 : Rat) ≠ 0 := by decide +kernel
      grind [Rat.mul_assoc, Rat.mul_comm]
    calc
      rationalCircleSin (u n).hi - rationalCircleSin (u n).lo <=
          2 * ((u n).hi - (u n).lo) := hw
      _ <= 2 * half.val := hscaled
      _ = eps.val := hhalf

/-! The real-coordinate companion used by the primitive. -/

def rationalCircleCos (u : Rat) : Rat :=
  (1 - u * u) / (1 + u * u)

def rationalCircleCosInterval (U : QInterval) : QInterval :=
  { lo := rationalCircleCos U.hi, hi := rationalCircleCos U.lo }

theorem rationalCircleSin_sq_add_cos_sq (u : Rat) :
    rationalCircleSin u * rationalCircleSin u +
        rationalCircleCos u * rationalCircleCos u = 1 := by
  unfold rationalCircleSin rationalCircleCos
  have hden : 1 + u * u > 0 := by
    have hsq : 0 <= u * u := by
      by_cases hu : 0 <= u
      · exact Rat.mul_nonneg hu hu
      · have hneg : 0 <= -u := by grind
        simpa [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg] using
          (Rat.mul_nonneg hneg hneg)
    grind
  have hdenne : 1 + u * u ≠ 0 := Rat.ne_of_gt hden
  apply rat_eq_of_mul_eq_mul_pos_local
    (c := (1 + u * u) * (1 + u * u))
    (Rat.mul_pos hden hden)
  rw [Rat.div_def, Rat.div_def]
  have hcancel : (1 + u * u)⁻¹ * (1 + u * u) = 1 :=
    Rat.inv_mul_cancel _ hdenne
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.add_mul, Rat.mul_add,
    Rat.sub_eq_add_neg]

private theorem rationalCircleCos_sub_formula {a b : Rat}
    (ha : 0 <= a) (hb : 0 <= b) :
    rationalCircleCos a - rationalCircleCos b =
      (2 * (b - a) * (a + b)) /
        ((1 + a * a) * (1 + b * b)) := by
  let da : Rat := 1 + a * a
  let db : Rat := 1 + b * b
  have hda : 0 < da := by
    dsimp [da]
    exact rationalCircleSin_den_pos ha
  have hdb : 0 < db := by
    dsimp [db]
    exact rationalCircleSin_den_pos hb
  have hprod : 0 < da * db := Rat.mul_pos hda hdb
  apply rat_eq_of_mul_eq_mul_pos_local (c := da * db) hprod
  unfold rationalCircleCos
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have hda_ne : da ≠ 0 := Rat.ne_of_gt hda
  have hdb_ne : db ≠ 0 := Rat.ne_of_gt hdb
  have hda_cancel : da⁻¹ * da = 1 := Rat.inv_mul_cancel da hda_ne
  have hdb_cancel : db⁻¹ * db = 1 := Rat.inv_mul_cancel db hdb_ne
  have hleft :
      ((1 - a * a) * da⁻¹ - (1 - b * b) * db⁻¹) * (da * db) =
        (1 - a * a) * db - (1 - b * b) * da := by
    calc
      ((1 - a * a) * da⁻¹ - (1 - b * b) * db⁻¹) * (da * db) =
          ((1 - a * a) * da⁻¹) * (da * db) -
            ((1 - b * b) * db⁻¹) * (da * db) := by
              grind [Rat.sub_eq_add_neg, Rat.add_mul]
      _ = (1 - a * a) * db - (1 - b * b) * da := by
        have h1 : ((1 - a * a) * da⁻¹) * (da * db) =
            (1 - a * a) * db := by
          calc
            ((1 - a * a) * da⁻¹) * (da * db) =
                (1 - a * a) * db * (da⁻¹ * da) := by
                  grind [Rat.mul_assoc, Rat.mul_comm]
            _ = (1 - a * a) * db := by rw [hda_cancel, Rat.mul_one]
        have h2 : ((1 - b * b) * db⁻¹) * (da * db) =
            (1 - b * b) * da := by
          calc
            ((1 - b * b) * db⁻¹) * (da * db) =
                (1 - b * b) * da * (db⁻¹ * db) := by
                  grind [Rat.mul_assoc, Rat.mul_comm]
            _ = (1 - b * b) * da := by rw [hdb_cancel, Rat.mul_one]
        rw [h1, h2]
  have hright :
      (2 * (b - a) * (a + b) * (da * db)⁻¹) * (da * db) =
        2 * (b - a) * (a + b) := by
    rw [Rat.mul_assoc, Rat.inv_mul_cancel (da * db) (Rat.ne_of_gt hprod),
      Rat.mul_one]
  rw [hleft, hright]
  dsimp [da, db]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg]

private theorem rationalCircleCos_mono {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (hb : b <= 1) :
    rationalCircleCos b <= rationalCircleCos a := by
  have hb0 : 0 <= b := Rat.le_trans ha hab
  have hdiff := rationalCircleCos_sub_formula ha hb0
  have hba : 0 <= b - a := by grind
  have hsum : 0 <= a + b := by grind
  have hden : 0 < (1 + a * a) * (1 + b * b) :=
    Rat.mul_pos (rationalCircleSin_den_pos ha)
      (rationalCircleSin_den_pos hb0)
  have hnum : 0 <= 2 * (b - a) * (a + b) := by
    exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hba) hsum
  have hinv : 0 <= ((1 + a * a) * (1 + b * b))⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hden)
  have hdiff_nonneg : 0 <= rationalCircleCos a - rationalCircleCos b := by
    rw [hdiff, Rat.div_def]
    exact Rat.mul_nonneg hnum hinv
  grind [Rat.sub_eq_add_neg]

private theorem rationalCircleCos_width_le {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (hb : b <= 1) :
    rationalCircleCos a - rationalCircleCos b <= 4 * (b - a) := by
  have hb0 : 0 <= b := Rat.le_trans ha hab
  have hden : 0 < (1 + a * a) * (1 + b * b) :=
    Rat.mul_pos (rationalCircleSin_den_pos ha)
      (rationalCircleSin_den_pos hb0)
  have hden_one : 1 <= (1 + a * a) * (1 + b * b) := by
    have haa : 0 <= a * a := Rat.mul_nonneg ha ha
    have hbb : 0 <= b * b := Rat.mul_nonneg hb0 hb0
    have hA : 1 <= 1 + a * a := by grind
    have hB : 1 <= 1 + b * b := by grind
    have hA0 : 0 <= 1 + a * a := by grind
    calc
      (1 : Rat) = 1 * 1 := by decide +kernel
      _ <= (1 + a * a) * 1 :=
        Rat.mul_le_mul_of_nonneg_right hA (by decide +kernel)
      _ <= (1 + a * a) * (1 + b * b) :=
        Rat.mul_le_mul_of_nonneg_left hB hA0
  rw [rationalCircleCos_sub_formula ha hb0]
  apply Rat.le_of_mul_le_mul_right
    (c := (1 + a * a) * (1 + b * b))
  · rw [Rat.div_def]
    have hba : 0 <= b - a := by grind
    have hsum : 0 <= a + b := by grind
    have hnum : 0 <= 2 * (b - a) * (a + b) := by
      exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hba) hsum
    have hsum_le : a + b <= 2 := by grind
    have hsumD : a + b <= 2 *
        ((1 + a * a) * (1 + b * b)) := by
      calc
        a + b <= 2 := hsum_le
        _ <= 2 * ((1 + a * a) * (1 + b * b)) := by
          simpa using Rat.mul_le_mul_of_nonneg_left hden_one
            (by decide +kernel : (0 : Rat) <= 2)
    have hnum_le : 2 * (b - a) * (a + b) <=
        4 * (b - a) * ((1 + a * a) * (1 + b * b)) := by
      calc
        2 * (b - a) * (a + b) <=
            2 * (b - a) * (2 *
              ((1 + a * a) * (1 + b * b))) := by
          exact Rat.mul_le_mul_of_nonneg_left hsumD
            (Rat.mul_nonneg (by decide +kernel) hba)
        _ = 4 * (b - a) * ((1 + a * a) * (1 + b * b)) := by
          grind [Rat.mul_assoc, Rat.mul_comm]
    calc
      (2 * (b - a) * (a + b) *
          ((1 + a * a) * (1 + b * b))⁻¹) *
          ((1 + a * a) * (1 + b * b)) =
          2 * (b - a) * (a + b) := by
            rw [Rat.mul_assoc,
              Rat.inv_mul_cancel _ (Rat.ne_of_gt hden), Rat.mul_one]
      _ <= 4 * (b - a) * ((1 + a * a) * (1 + b * b)) := hnum_le
  · exact hden

theorem rationalCircleCosInterval_width_le
    {U : QInterval} (hU : subintervalOf U 0 1) :
    0 <= (rationalCircleCosInterval U).width /\
      (rationalCircleCosInterval U).width <= 4 * U.width := by
  have hcos := rationalCircleCos_width_le hU.1 hU.2.1 hU.2.2
  have hmono := rationalCircleCos_mono hU.1 hU.2.1 hU.2.2
  unfold rationalCircleCosInterval QInterval.width
  constructor
  · grind
  · simpa using hcos

theorem rationalCircleCos_difference_le_qabs
    {a b : Rat} (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hb1 : b <= 1) :
    qabs (rationalCircleCos a - rationalCircleCos b) <=
      4 * qabs (a - b) := by
  by_cases hab : a <= b
  · have hcos := rationalCircleCos_width_le ha0 hab hb1
    have hmono := rationalCircleCos_mono ha0 hab hb1
    have hdiff : 0 <= rationalCircleCos a - rationalCircleCos b := by
      grind
    rw [qabs_eq_self_of_nonneg hdiff]
    rw [show qabs (a - b) = b - a by
      rw [show a - b = -(b - a) by grind [Rat.sub_eq_add_neg], qabs_neg,
        qabs_eq_self_of_nonneg (by grind : 0 <= b - a)]]
    exact hcos
  · have hba : b <= a := by grind
    have hcos := rationalCircleCos_width_le hb0 hba ha1
    have hmono := rationalCircleCos_mono hb0 hba ha1
    have hdiff : 0 <= rationalCircleCos b - rationalCircleCos a := by
      grind
    rw [show rationalCircleCos a - rationalCircleCos b =
        -(rationalCircleCos b - rationalCircleCos a) by
          grind [Rat.sub_eq_add_neg], qabs_neg,
      qabs_eq_self_of_nonneg hdiff]
    rw [show qabs (a - b) = a - b by
      exact qabs_eq_self_of_nonneg (by grind)]
    exact hcos

theorem rationalCircleCosInterval_near_of_near
    {U V : QInterval} (hU : subintervalOf U 0 1)
    (hV : subintervalOf V 0 1) (eps : QPos)
    (hnear : QInterval.NearAt U V eps) :
    QInterval.NearAt (rationalCircleCosInterval U)
      (rationalCircleCosInterval V)
      { val := 4 * eps.val
        property := Rat.mul_pos (by decide +kernel)
          (eps.property) } := by
  have hUwidth := rationalCircleCosInterval_width_le hU
  have hVwidth := rationalCircleCosInterval_width_le hV
  have hleft :
      rationalCircleCos U.hi <= rationalCircleCos V.lo + 4 * eps.val := by
    by_cases huv : V.lo <= U.hi
    · have hmono := rationalCircleCos_mono hV.1 huv hU.2.2
      grind
    · have hdiff : U.hi <= V.lo := by grind
      have hUhi0 : 0 <= U.hi := Rat.le_trans hU.1 hU.2.1
      have hVlo1 : V.lo <= 1 := Rat.le_trans hV.2.1 hV.2.2
      have hq := rationalCircleCos_difference_le_qabs
        hUhi0 hU.2.2 hV.1 hVlo1
          (a := U.hi) (b := V.lo)
      have hdelta : V.lo - U.hi <= eps.val := by grind [hnear.2.1]
      rw [show qabs (U.hi - V.lo) = V.lo - U.hi by
        rw [show U.hi - V.lo = -(V.lo - U.hi) by grind [Rat.sub_eq_add_neg],
          qabs_neg, qabs_eq_self_of_nonneg (by grind)]] at hq
      have hself := self_le_qabs
        (rationalCircleCos U.hi - rationalCircleCos V.lo)
      grind
  have hright :
      rationalCircleCos V.hi <= rationalCircleCos U.lo + 4 * eps.val := by
    by_cases huv : U.lo <= V.hi
    · have hmono := rationalCircleCos_mono hU.1 huv hV.2.2
      grind
    · have hdiff : V.hi <= U.lo := by grind
      have hVhi0 : 0 <= V.hi := Rat.le_trans hV.1 hV.2.1
      have hUlo1 : U.lo <= 1 := Rat.le_trans hU.2.1 hU.2.2
      have hq := rationalCircleCos_difference_le_qabs
        hVhi0 hV.2.2 hU.1 hUlo1
          (a := V.hi) (b := U.lo)
      have hdelta : U.lo - V.hi <= eps.val := by grind [hnear.1]
      rw [show qabs (V.hi - U.lo) = U.lo - V.hi by
        rw [show V.hi - U.lo = -(U.lo - V.hi) by grind [Rat.sub_eq_add_neg],
          qabs_neg, qabs_eq_self_of_nonneg (by grind)]] at hq
      have hself := self_le_qabs
        (rationalCircleCos V.hi - rationalCircleCos U.lo)
      grind
  unfold QInterval.NearAt rationalCircleCosInterval
  dsimp
  change rationalCircleCos U.hi <=
      rationalCircleCos V.lo + 4 * eps.val /\
    rationalCircleCos V.hi <=
      rationalCircleCos U.lo + 4 * eps.val /\
    rationalCircleCos U.lo - rationalCircleCos U.hi <= 4 * eps.val /\
    rationalCircleCos V.lo - rationalCircleCos V.hi <= 4 * eps.val
  constructor
  · exact hleft
  constructor
  · exact hright
  constructor
  · have hwidth := hUwidth.2
    have hsmall := hnear.2.2.1
    have hwidth' : rationalCircleCos U.lo - rationalCircleCos U.hi <=
        4 * U.width := by
      simpa [rationalCircleCosInterval, QInterval.width] using hwidth
    grind
  · have hwidth := hVwidth.2
    have hsmall := hnear.2.2.2
    have hwidth' : rationalCircleCos V.lo - rationalCircleCos V.hi <=
        4 * V.width := by
      simpa [rationalCircleCosInterval, QInterval.width] using hwidth
    grind

theorem rationalCircleCosInterval_valid
    (u : Nat -> QInterval)
    (hu : RealCompute.ValidCompute u)
    (hubounds : forall n, 0 <= (u n).lo /\ (u n).hi <= 1) :
    RealCompute.ValidCompute (fun n => rationalCircleCosInterval (u n)) := by
  constructor
  · intro n
    have horder := RealCompute.interval_order_of_valid
      { compute := u } hu n
    have hmono := rationalCircleCos_mono
      (hubounds n).1 horder (hubounds n).2
    change 0 <= rationalCircleCos (u n).lo - rationalCircleCos (u n).hi
    grind [Rat.sub_eq_add_neg]
  constructor
  · intro n m hnm
    have hn := hu.2.1 n m hnm
    have hnl := hubounds n
    have hml := hubounds m
    have hcosLo := rationalCircleCos_mono
      (by grind [RealCompute.interval_order_of_valid { compute := u } hu m])
      hn.2.2 hnl.2
    have hcosMid := rationalCircleCos_mono hml.1
      (RealCompute.interval_order_of_valid { compute := u } hu m) hml.2
    have hcosHi := rationalCircleCos_mono hnl.1 hn.1
      (by grind [hml.2, RealCompute.interval_order_of_valid { compute := u } hu m])
    exact ⟨hcosLo, hcosMid, hcosHi⟩
  · intro eps
    obtain ⟨N, hN⟩ := hu.2.2 ⟨eps.val / 4, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide +kernel))⟩
    refine ⟨N, ?_⟩
    intro n hn
    have horder := RealCompute.interval_order_of_valid { compute := u } hu n
    have hw := hN n hn
    have hcos := rationalCircleCos_width_le
      (hubounds n).1 horder (hubounds n).2
    have hscaled := Rat.mul_le_mul_of_nonneg_left hw
      (by decide +kernel : (0 : Rat) <= 4)
    change rationalCircleCos (u n).lo - rationalCircleCos (u n).hi <= eps.val
    calc
      rationalCircleCos (u n).lo - rationalCircleCos (u n).hi <=
          4 * ((u n).hi - (u n).lo) := hcos
      _ <= 4 * (eps.val / 4) := hscaled
      _ = eps.val := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]

/-- `sin(pi*x)` from the arctangent inverse, on rational `x` in `[0,1/2]`.

The computation first recovers the half-angle slope by certified bisection,
then applies the rational circle formula. -/
def sinPiRawOfArctan
    (B : IntegralIdentities.ArctanInverseBisection)
    (x : Rat)
    (hx : 0 <= x /\ x <= (1 : Rat) / 2) : RealCompute where
  compute := fun n =>
      rationalCircleSinInterval
      ((B.tangentRaw.compute (2 * x)
        (by
          change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
          constructor
          · exact Rat.mul_nonneg (by decide +kernel) hx.1
          · have h := Rat.mul_le_mul_of_nonneg_left hx.2 (by decide +kernel : (0 : Rat) <= 2)
            have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
            rw [hhalf] at h
            exact h) n))

theorem arctanSinPi_sample_overlap_of_tangent_witness
    (B : IntegralIdentities.ArctanInverseBisection)
    {x : Rat} (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n : Nat)
    (S : QInterval) (hS : subintervalOf S 0 1) (u : Rat)
    (hu : (B.tangentRaw.compute (2 * x)
      (by
        change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
        constructor
        · exact Rat.mul_nonneg (by decide +kernel) hx.1
        · have h := Rat.mul_le_mul_of_nonneg_left hx.2
            (by decide +kernel : (0 : Rat) <= 2)
          rw [show (2 : Rat) * (1 / 2) = 1 by decide +kernel] at h
          exact h) n).lo <= u /\
      u <= (B.tangentRaw.compute (2 * x)
        (by
          change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
          constructor
          · exact Rat.mul_nonneg (by decide +kernel) hx.1
          · have h := Rat.mul_le_mul_of_nonneg_left hx.2
              (by decide +kernel : (0 : Rat) <= 2)
            rw [show (2 : Rat) * (1 / 2) = 1 by decide +kernel] at h
            exact h) n).hi)
    (himage : S.lo <= rationalCircleSin u /\
      rationalCircleSin u <= S.hi) :
    QInterval.Overlaps
      ((sinPiRawOfArctan B x hx).compute n) S := by
  let ht : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x) := by
    change 0 <= 2 * x /\ 2 * x <= 1
    constructor
    · exact Rat.mul_nonneg (by decide +kernel) hx.1
    · have h := Rat.mul_le_mul_of_nonneg_left hx.2
        (by decide +kernel : (0 : Rat) <= 2)
      rw [show (2 : Rat) * (1 / 2) = 1 by decide +kernel] at h
      exact h
  have hvalid : RealCompute.ValidCompute (B.tangentRaw.compute (2 * x) ht) := by
    exact B.tangentRaw_valid (2 * x) ht
  have hbounds := B.tangentAt_stays_in_unitSlope (2 * x) ht n
  have horder := RealCompute.interval_order_of_valid
    { compute := B.tangentRaw.compute (2 * x) ht } hvalid n
  have hU : subintervalOf (B.tangentRaw.compute (2 * x) ht n) 0 1 :=
    ⟨hbounds.1, horder, hbounds.2.2⟩
  change QInterval.Overlaps
    (rationalCircleSinInterval (B.tangentRaw.compute (2 * x) ht n)) S
  exact rationalCircleSinInterval_overlap_of_tangent_witness
    hS hU u hu himage

/-- The arctangent-backed pointwise sine evaluator.  The validity field is
the finite interval proof that the monotone rational formula transports the
inverse boxes. -/
structure ArctanSinPiConstruction where
  inverse : IntegralIdentities.ArctanInverseBisection
  sin_valid : forall x hx,
    RealCompute.ValidCompute
      ((sinPiRawOfArctan inverse x hx).compute)

/-- Build the sine construction from the inverse search and its finite
first-quadrant range proof.  The validity of the circle-coordinate evaluator
is discharged by `rationalCircleSinInterval_valid`; it is not an additional
analytic axiom. -/
def ArctanSinPiConstruction.ofInverse
    (B : IntegralIdentities.ArctanInverseBisection)
    (slope_bounded : forall x (hx : 0 <= x /\ x <= (1 : Rat) / 2) n,
      0 <= (B.tangentRaw.compute (2 * x)
        (by
          change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
          constructor
          · exact Rat.mul_nonneg (by decide +kernel) hx.1
          · have h := Rat.mul_le_mul_of_nonneg_left hx.2
              (by decide +kernel : (0 : Rat) <= 2)
            have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
            rw [hhalf] at h
            exact h) n).lo /\
      (B.tangentRaw.compute (2 * x)
        (by
          change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
          constructor
          · exact Rat.mul_nonneg (by decide +kernel) hx.1
          · have h := Rat.mul_le_mul_of_nonneg_left hx.2
              (by decide +kernel : (0 : Rat) <= 2)
            have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
            rw [hhalf] at h
            exact h) n).hi <= 1) :
    ArctanSinPiConstruction where
  inverse := B
  sin_valid := by
    intro x hx
    apply rationalCircleSinInterval_valid
    · exact B.tangentRaw_valid (2 * x) _
    · exact slope_bounded x hx

theorem ArctanSinPiConstruction.sinPiRawOfArctan_bounds
    (S : ArctanSinPiConstruction) {x : Rat}
    (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n : Nat) :
    0 <= ((sinPiRawOfArctan S.inverse x hx).compute n).lo /\
      ((sinPiRawOfArctan S.inverse x hx).compute n).hi <= 1 := by
  change 0 <=
      (rationalCircleSinInterval
        (S.inverse.tangentRaw.compute (2 * x) _ n)).lo /\
    (rationalCircleSinInterval
        (S.inverse.tangentRaw.compute (2 * x) _ n)).hi <= 1
  exact rationalCircleSinInterval_bounds
    (IntegralIdentities.ArctanInverseBisection.tangentAt_stays_in_unitSlope
      S.inverse (2 * x) _ n)

theorem arctanInverse_slope_bounded
    (B : IntegralIdentities.ArctanInverseBisection)
    (x : Rat) (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n : Nat) :
    0 <= (B.tangentRaw.compute (2 * x)
      (by
        change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
        constructor
        · exact Rat.mul_nonneg (by decide +kernel) hx.1
        · have h := Rat.mul_le_mul_of_nonneg_left hx.2
            (by decide +kernel : (0 : Rat) <= 2)
          have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
          rw [hhalf] at h
          exact h) n).lo /\
      (B.tangentRaw.compute (2 * x)
        (by
          change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
          constructor
          · exact Rat.mul_nonneg (by decide +kernel) hx.1
          · have h := Rat.mul_le_mul_of_nonneg_left hx.2
              (by decide +kernel : (0 : Rat) <= 2)
            have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
            rw [hhalf] at h
            exact h) n).hi <= 1 := by
  let ht : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x) := by
    change 0 <= 2 * x /\ 2 * x <= 1
    constructor
    · exact Rat.mul_nonneg (by decide +kernel) hx.1
    · have h := Rat.mul_le_mul_of_nonneg_left hx.2
        (by decide +kernel : (0 : Rat) <= 2)
      have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
      rw [hhalf] at h
      exact h
  have hs := B.tangentAt_stays_in_unitSlope (2 * x) ht n
  change 0 <= ((B.tangentAt (2 * x) ht).compute n).lo /\
    ((B.tangentAt (2 * x) ht).compute n).hi <= 1
  exact ⟨hs.1, hs.2.2⟩

def ArctanSinPiConstruction.canonical
    (B : IntegralIdentities.ArctanInverseBisection) :
    ArctanSinPiConstruction :=
  ArctanSinPiConstruction.ofInverse B
    (fun x hx n => arctanInverse_slope_bounded B x hx n)

/-! The explicit cosine coordinate and the primitive target. -/

/-- `cos (pi*x)` from the same inverse slope boxes used by `sinPiRaw`. -/
def cosPiRawOfArctan
    (B : IntegralIdentities.ArctanInverseBisection)
    (x : Rat)
    (hx : 0 <= x /\ x <= (1 : Rat) / 2) : RealCompute where
  compute := fun n =>
    rationalCircleCosInterval
      ((B.tangentRaw.compute (2 * x)
        (by
          change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
          constructor
          · exact Rat.mul_nonneg (by decide +kernel) hx.1
          · have h := Rat.mul_le_mul_of_nonneg_left hx.2
              (by decide +kernel : (0 : Rat) <= 2)
            have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
            rw [hhalf] at h
            exact h) n))

theorem cosPiRawOfArctan_valid
    (B : IntegralIdentities.ArctanInverseBisection)
    (x : Rat) (hx : 0 <= x /\ x <= (1 : Rat) / 2) :
    (cosPiRawOfArctan B x hx).Valid := by
  apply rationalCircleCosInterval_valid
  · exact B.tangentRaw_valid (2 * x) _
  · exact fun n => arctanInverse_slope_bounded B x hx n

def cosPiOnHalf
    (B : IntegralIdentities.ArctanInverseBisection) : FunctionOnInterval where
  raw := {
    definedAt := fun x => 0 <= x /\ x <= (1 : Rat) / 2
    compute := fun x hx => (cosPiRawOfArctan B x hx).compute
  }
  lower := 0
  upper := (1 : Rat) / 2
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    exact cosPiRawOfArctan_valid B x hx

theorem rationalCircleCos_bounds {u : Rat}
    (hu : 0 <= u) (hu1 : u <= 1) :
    0 <= rationalCircleCos u /\ rationalCircleCos u <= 1 := by
  have hleft := rationalCircleCos_mono hu hu1 (by decide +kernel)
  have hright := rationalCircleCos_mono (by decide +kernel : (0 : Rat) <= 0)
    hu hu1
  have hcos0 : rationalCircleCos 0 = 1 := by decide +kernel
  have hcos1 : rationalCircleCos 1 = 0 := by decide +kernel
  constructor
  · simpa [hcos1] using hleft
  · simpa [hcos0] using hright

theorem cosPiRawOfArctan_zero_equiv_one_of_tangent_endpoint
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero) :
    (cosPiRawOfArctan B 0
      ⟨by decide +kernel, by decide +kernel⟩).Equiv RealCompute.one := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (cosPiRawOfArctan B 0 ⟨by decide +kernel, by decide +kernel⟩)
    RealCompute.one n n).2
  have hT : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Valid :=
    B.tangentAt_valid 0 RationalCircle.GeometricTrig.firstQuadrantBranch_zero
  have hbounds := B.tangentAt_stays_in_unitSlope 0
    RationalCircle.GeometricTrig.firstQuadrantBranch_zero n
  have hzero := (RealCompute.compareAt_overlap_iff
    (B.tangentAt 0 RationalCircle.GeometricTrig.firstQuadrantBranch_zero)
    RealCompute.zero n n).1 (ht n)
  simp [RealCompute.zero, RealCompute.ofRat] at hzero
  let ht0 : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * 0) := by
    dsimp [RationalCircle.GeometricTrig.firstQuadrantBranch,
      RationalCircle.GeometricTrig.unitIntervalBranch]
    constructor <;> decide +kernel
  have hbounds' : subintervalOf (B.tangentRaw.compute (2 * 0) ht0 n) 0 1 := by
    simpa [IntegralIdentities.ArctanInverseBisection.tangentRaw,
      IntegralIdentities.ArctanInverseBisection.tangentAt] using hbounds
  change QInterval.Overlaps
    (rationalCircleCosInterval (B.tangentRaw.compute (2 * 0) ht0 n))
    { lo := 1, hi := 1 }
  simp only [rationalCircleCosInterval]
  have hlo : ((B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).compute n).lo = 0 := by
    apply Rat.le_antisymm
    · exact hzero.1
    · exact hbounds.1
  have hlo' : (B.tangentRaw.compute (2 * 0) ht0 n).lo = 0 := by
    simpa [IntegralIdentities.ArctanInverseBisection.tangentRaw,
      IntegralIdentities.ArctanInverseBisection.tangentAt] using hlo
  rw [hlo']
  have hcos := rationalCircleCos_bounds
    (by grind [hbounds'.1, hbounds'.2.1]) hbounds'.2.2
  have hcos0 : rationalCircleCos 0 = 1 := by decide +kernel
  rw [hcos0]
  unfold QInterval.Overlaps
  change rationalCircleCos (B.tangentRaw.compute (2 * 0) ht0 n).hi <= 1 /\
    (1 : Rat) <= 1
  exact ⟨hcos.2, by decide +kernel⟩

theorem cosPiRawOfArctan_half_equiv_zero_of_tangent_endpoint
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht : (B.tangentAt 1
      RationalCircle.GeometricTrig.firstQuadrantBranch_one).Equiv
      RealCompute.one) :
    (cosPiRawOfArctan B (1 / 2)
      ⟨by decide +kernel, by decide +kernel⟩).Equiv RealCompute.zero := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (cosPiRawOfArctan B (1 / 2) ⟨by decide +kernel, by decide +kernel⟩)
    RealCompute.zero n n).2
  have hT : (B.tangentAt 1
      RationalCircle.GeometricTrig.firstQuadrantBranch_one).Valid :=
    B.tangentAt_valid 1 RationalCircle.GeometricTrig.firstQuadrantBranch_one
  have hbounds := B.tangentAt_stays_in_unitSlope 1
    RationalCircle.GeometricTrig.firstQuadrantBranch_one n
  have hone := (RealCompute.compareAt_overlap_iff
    (B.tangentAt 1 RationalCircle.GeometricTrig.firstQuadrantBranch_one)
    RealCompute.one n n).1 (ht n)
  simp [RealCompute.one, RealCompute.ofRat] at hone
  let htHalf : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * (1 / 2)) := by
    dsimp [RationalCircle.GeometricTrig.firstQuadrantBranch,
      RationalCircle.GeometricTrig.unitIntervalBranch]
    constructor <;> decide +kernel
  have htwo : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
  have hbounds' : subintervalOf
      (B.tangentRaw.compute (2 * (1 / 2)) htHalf n) 0 1 := by
    simpa [htwo, IntegralIdentities.ArctanInverseBisection.tangentRaw,
      IntegralIdentities.ArctanInverseBisection.tangentAt] using hbounds
  have hone' : 1 <= (B.tangentRaw.compute (2 * (1 / 2)) htHalf n).hi := by
    simpa [htwo, IntegralIdentities.ArctanInverseBisection.tangentRaw,
      IntegralIdentities.ArctanInverseBisection.tangentAt] using hone.2
  have hhi : (B.tangentRaw.compute (2 * (1 / 2)) htHalf n).hi = 1 := by
    apply Rat.le_antisymm
    · exact hbounds'.2.2
    · exact hone'
  have hcos : 0 <= rationalCircleCos
      (B.tangentRaw.compute (2 * (1 / 2)) htHalf n).lo :=
    (rationalCircleCos_bounds hbounds'.1 (by grind [hbounds'.2.1])).1
  change QInterval.Overlaps
    (rationalCircleCosInterval
      (B.tangentRaw.compute (2 * (1 / 2)) htHalf n))
    { lo := 0, hi := 0 }
  simp only [rationalCircleCosInterval]
  rw [hhi]
  have hcos1 : rationalCircleCos 1 = 0 := by decide +kernel
  rw [hcos1]
  unfold QInterval.Overlaps
  change (0 : Rat) <= 0 /\ 0 <=
    rationalCircleCos (B.tangentRaw.compute (2 * (1 / 2)) htHalf n).lo
  exact ⟨by decide +kernel, hcos⟩

/-! Endpoint overlap for the sine coordinate.  These are the two exact
dyadic samples shared by every possible inverse implementation; recording
them explicitly lets finite mesh proofs discharge their boundary cells
without invoking a general inverse-search witness. -/
theorem sinPiRawOfArctan_zero_equiv_zero_of_tangent_endpoint
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero) :
    (sinPiRawOfArctan B 0
      ⟨by decide +kernel, by decide +kernel⟩).Equiv RealCompute.zero := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (sinPiRawOfArctan B 0 ⟨by decide +kernel, by decide +kernel⟩)
    RealCompute.zero n n).2
  have hbounds := B.tangentAt_stays_in_unitSlope 0
    RationalCircle.GeometricTrig.firstQuadrantBranch_zero n
  have hzero := (RealCompute.compareAt_overlap_iff
    (B.tangentAt 0 RationalCircle.GeometricTrig.firstQuadrantBranch_zero)
    RealCompute.zero n n).1 (ht n)
  simp [RealCompute.zero, RealCompute.ofRat] at hzero
  unfold QInterval.Overlaps at hzero
  have hzero' : ((B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).compute n).lo <= 0 := by
    have h := hzero.1
    change ((B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).compute n).lo <=
      ({ lo := 0, hi := 0 } : QInterval).hi at h
    simpa using h
  let ht0 : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * 0) := by
    dsimp [RationalCircle.GeometricTrig.firstQuadrantBranch,
      RationalCircle.GeometricTrig.unitIntervalBranch]
    constructor <;> decide +kernel
  have hbounds' : subintervalOf
      (B.tangentRaw.compute (2 * 0) ht0 n) 0 1 := by
    simpa [IntegralIdentities.ArctanInverseBisection.tangentRaw,
      IntegralIdentities.ArctanInverseBisection.tangentAt] using hbounds
  have hlo : (B.tangentRaw.compute (2 * 0) ht0 n).lo = 0 := by
    apply Rat.le_antisymm
    · simpa [IntegralIdentities.ArctanInverseBisection.tangentRaw,
        IntegralIdentities.ArctanInverseBisection.tangentAt] using hzero'
    · exact hbounds'.1
  change QInterval.Overlaps
    (rationalCircleSinInterval (B.tangentRaw.compute (2 * 0) ht0 n))
    { lo := 0, hi := 0 }
  simp only [rationalCircleSinInterval]
  rw [hlo]
  have hsin := rationalCircleSin_bounds
    (by grind [hbounds'.1, hbounds'.2.1]) hbounds'.2.2
  have hsin0 : rationalCircleSin 0 = 0 := by decide +kernel
  rw [hsin0]
  unfold QInterval.Overlaps
  change (0 : Rat) <= 0 ∧ 0 <=
    rationalCircleSin (B.tangentRaw.compute (2 * 0) ht0 n).hi
  exact ⟨by decide +kernel, hsin.1⟩

theorem sinPiRawOfArctan_half_equiv_one_of_tangent_endpoint
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht : (B.tangentAt 1
      RationalCircle.GeometricTrig.firstQuadrantBranch_one).Equiv
      RealCompute.one) :
    (sinPiRawOfArctan B (1 / 2)
      ⟨by decide +kernel, by decide +kernel⟩).Equiv RealCompute.one := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (sinPiRawOfArctan B (1 / 2) ⟨by decide +kernel, by decide +kernel⟩)
    RealCompute.one n n).2
  have hbounds := B.tangentAt_stays_in_unitSlope 1
    RationalCircle.GeometricTrig.firstQuadrantBranch_one n
  have hone := (RealCompute.compareAt_overlap_iff
    (B.tangentAt 1 RationalCircle.GeometricTrig.firstQuadrantBranch_one)
    RealCompute.one n n).1 (ht n)
  simp [RealCompute.one, RealCompute.ofRat] at hone
  let htHalf : RationalCircle.GeometricTrig.firstQuadrantBranch
      (2 * (1 / 2)) := by
    dsimp [RationalCircle.GeometricTrig.firstQuadrantBranch,
      RationalCircle.GeometricTrig.unitIntervalBranch]
    constructor <;> decide +kernel
  have htwo : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
  have hbounds' : subintervalOf
      (B.tangentRaw.compute (2 * (1 / 2)) htHalf n) 0 1 := by
    simpa [htwo, IntegralIdentities.ArctanInverseBisection.tangentRaw,
      IntegralIdentities.ArctanInverseBisection.tangentAt] using hbounds
  have hhi : (B.tangentRaw.compute (2 * (1 / 2)) htHalf n).hi = 1 := by
    apply Rat.le_antisymm
    · exact hbounds'.2.2
    · simpa [htwo, IntegralIdentities.ArctanInverseBisection.tangentRaw,
        IntegralIdentities.ArctanInverseBisection.tangentAt] using hone.2
  change QInterval.Overlaps
    (rationalCircleSinInterval (B.tangentRaw.compute (2 * (1 / 2)) htHalf n))
    { lo := 1, hi := 1 }
  simp only [rationalCircleSinInterval]
  rw [hhi]
  have hsin := rationalCircleSin_bounds hbounds'.1
    (by grind [hbounds'.2.1, hbounds'.2.2])
  have hsin1 : rationalCircleSin 1 = 1 := by decide +kernel
  rw [hsin1]
  unfold QInterval.Overlaps
  change rationalCircleSin
      (B.tangentRaw.compute (2 * (1 / 2)) htHalf n).lo <= 1 ∧
    (1 : Rat) <= 1
  exact ⟨hsin.2, by decide +kernel⟩

def reciprocalPiFunRaw : RealFunRaw where
  domain := fun x => 0 <= x /\ x <= (1 : Rat) / 2
  compute := fun _ n => reciprocalPiRaw.compute n

theorem reciprocalPiFunRaw_valid : reciprocalPiFunRaw.Valid := by
  intro _ _
  exact reciprocalPiRaw_valid

theorem reciprocalPiRaw_bounds (n : Nat) :
    0 <= (reciprocalPiRaw.compute n).lo /\
    (reciprocalPiRaw.compute n).hi <= 1 := by
  change 0 <= (QInterval.inv (piCircleArea.compute n)).lo /\
    (QInterval.inv (piCircleArea.compute n)).hi <= 1
  rw [reciprocalPi_compute n]
  have hpi := piCircleArea_interval_bounds n
  have hpos : 0 < (piCircleArea.compute n).lo :=
    piCircleArea_interval_positive n
  constructor
  · exact Rat.le_of_lt (by
      rw [Rat.div_def]
      exact Rat.mul_pos (by decide +kernel)
        ((Rat.inv_pos).2 (by grind [RealCompute.interval_order_of_valid
          piCircleArea CauchyPi.piCircleArea_valid n])))
  · have h1 : (1 : Rat) <= (piCircleArea.compute n).lo := by
      grind [hpi.1]
    have hone := one_div_antitone_pos_local (a := (1 : Rat))
        (b := (piCircleArea.compute n).lo) (by decide +kernel) h1
    have honeone : (1 : Rat) / 1 = 1 := by decide +kernel
    rw [honeone] at hone
    exact hone

def oneMinusCosFunRaw
    (B : IntegralIdentities.ArctanInverseBisection) : RealFunRaw where
  domain := fun x => 0 <= x /\ x <= (1 : Rat) / 2
  compute := fun x n =>
    if hx : 0 <= x /\ x <= (1 : Rat) / 2 then
      let C := (cosPiRawOfArctan B x hx).compute n
      { lo := 1 - C.hi, hi := 1 - C.lo }
    else
      { lo := 0, hi := 0 }

theorem cosPiRawOfArctan_near_of_tangent_near
    (B : IntegralIdentities.ArctanInverseBisection)
    {x y : Rat} (hx : 0 <= x /\ x <= (1 : Rat) / 2)
    (hy : 0 <= y /\ y <= (1 : Rat) / 2)
    (htx : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x))
    (hty : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * y))
    (n : Nat) (eps : QPos)
    (hnear : QInterval.NearAt
      ((IntegralIdentities.tangentOnUnit B).compute (2 * x) htx n)
      ((IntegralIdentities.tangentOnUnit B).compute (2 * y) hty n)
      eps) :
    QInterval.NearAt
      ((cosPiRawOfArctan B x hx).compute n)
      ((cosPiRawOfArctan B y hy).compute n)
      { val := 4 * eps.val
        property := Rat.mul_pos (by decide +kernel)
          eps.property } := by
  have hUx : subintervalOf
      ((IntegralIdentities.tangentOnUnit B).compute (2 * x) htx n) 0 1 :=
    IntegralIdentities.ArctanInverseBisection.tangentAt_stays_in_unitSlope
      B (2 * x) htx n
  have hUy : subintervalOf
      ((IntegralIdentities.tangentOnUnit B).compute (2 * y) hty n) 0 1 :=
    IntegralIdentities.ArctanInverseBisection.tangentAt_stays_in_unitSlope
      B (2 * y) hty n
  change QInterval.NearAt
    (rationalCircleCosInterval
      ((IntegralIdentities.tangentOnUnit B).compute (2 * x) htx n))
    (rationalCircleCosInterval
      ((IntegralIdentities.tangentOnUnit B).compute (2 * y) hty n)) _
  exact rationalCircleCosInterval_near_of_near hUx hUy
    eps hnear

theorem oneMinusCosFunRaw_near_of_tangent_near
    (B : IntegralIdentities.ArctanInverseBisection)
    {x y : Rat} (hx : 0 <= x /\ x <= (1 : Rat) / 2)
    (hy : 0 <= y /\ y <= (1 : Rat) / 2)
    (htx : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x))
    (hty : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * y))
    (n : Nat) (eps : QPos)
    (hnear : QInterval.NearAt
      ((IntegralIdentities.tangentOnUnit B).compute (2 * x) htx n)
      ((IntegralIdentities.tangentOnUnit B).compute (2 * y) hty n)
      eps) :
    QInterval.NearAt
      ((oneMinusCosFunRaw B).compute x n)
      ((oneMinusCosFunRaw B).compute y n)
      { val := 4 * eps.val
        property := Rat.mul_pos (by decide +kernel)
          eps.property } := by
  have hcos := cosPiRawOfArctan_near_of_tangent_near
    B hx hy htx hty n eps hnear
  simp only [oneMinusCosFunRaw, dif_pos hx, dif_pos hy]
  change QInterval.NearAt
    { lo := 1 - ((cosPiRawOfArctan B x hx).compute n).hi
      hi := 1 - ((cosPiRawOfArctan B x hx).compute n).lo }
    { lo := 1 - ((cosPiRawOfArctan B y hy).compute n).hi
      hi := 1 - ((cosPiRawOfArctan B y hy).compute n).lo } _
  unfold QInterval.NearAt QInterval.width at hcos ⊢
  rcases hcos with ⟨hxy, hyx, hwidthx, hwidthy⟩
  constructor
  · grind
  constructor
  · grind
  constructor <;> grind

theorem oneMinusCosFunRaw_valid
  (B : IntegralIdentities.ArctanInverseBisection) :
    (oneMinusCosFunRaw B).Valid := by
  intro x hx
  change 0 <= x /\ x <= (1 : Rat) / 2 at hx
  let C : RealCompute := cosPiRawOfArctan B x hx
  have hC : C.Valid := cosPiRawOfArctan_valid B x hx
  have horder : forall n, (C.compute n).lo <= (C.compute n).hi :=
    fun n => RealCompute.interval_order_of_valid C hC n
  have hbounds : forall n, 0 <= (C.compute n).lo /\
      (C.compute n).hi <= 1 := by
    intro n
    have ht := arctanInverse_slope_bounded B x hx n
    have htarg : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x) := by
      change 0 <= 2 * x /\ 2 * x <= 1
      constructor
      · exact Rat.mul_nonneg (by decide +kernel) hx.1
      · have h := Rat.mul_le_mul_of_nonneg_left hx.2
          (by decide +kernel : (0 : Rat) <= 2)
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
        rw [hhalf] at h
        exact h
    have htv := B.tangentRaw_valid (2 * x) htarg
    have hto := RealCompute.interval_order_of_valid
      { compute := B.tangentRaw.compute (2 * x) htarg } htv n
    have hlo := rationalCircleCos_bounds ht.1 (by grind [ht.2])
    have hhi := rationalCircleCos_bounds (by grind [ht.1]) ht.2
    exact ⟨hhi.1, hlo.2⟩
  change RealCompute.ValidCompute ((oneMinusCosFunRaw B).compute x)
  simp only [oneMinusCosFunRaw, dif_pos hx]
  change RealCompute.ValidCompute (fun n =>
    { lo := 1 - (C.compute n).hi, hi := 1 - (C.compute n).lo })
  constructor
  · intro n
    change 0 <= (1 - (C.compute n).lo) - (1 - (C.compute n).hi)
    grind [hbounds n]
  constructor
  · intro n m hnm
    have hn := hC.2.1 n m hnm
    constructor
    · grind [hn.2.2]
    · constructor
      · grind [horder m]
      · grind [hn.1]
  · intro eps
    obtain ⟨N, hN⟩ := hC.2.2 eps
    refine ⟨N, ?_⟩
    intro n hn
    have hwidth := hN n hn
    change (1 - (C.compute n).lo) - (1 - (C.compute n).hi) <= eps.val
    change (C.compute n).hi - (C.compute n).lo <= eps.val at hwidth
    grind

theorem oneMinusCosFunRaw_bounds
    (B : IntegralIdentities.ArctanInverseBisection)
    {x : Rat} (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n : Nat) :
    0 <= ((oneMinusCosFunRaw B).compute x n).lo /\
      ((oneMinusCosFunRaw B).compute x n).hi <= 1 := by
  simp only [oneMinusCosFunRaw, dif_pos hx]
  have ht := arctanInverse_slope_bounded B x hx n
  have htarg : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x) := by
    change 0 <= 2 * x /\ 2 * x <= 1
    constructor
    · exact Rat.mul_nonneg (by decide +kernel) hx.1
    · have h := Rat.mul_le_mul_of_nonneg_left hx.2
        (by decide +kernel : (0 : Rat) <= 2)
      have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
      rw [hhalf] at h
      exact h
  have htv := B.tangentRaw_valid (2 * x) htarg
  have hto := RealCompute.interval_order_of_valid
    { compute := B.tangentRaw.compute (2 * x) htarg } htv n
  have hlo := rationalCircleCos_bounds ht.1 (by grind [ht.2])
  have hhi := rationalCircleCos_bounds (by grind [ht.1]) ht.2
  change 0 <= 1 - ((cosPiRawOfArctan B x _).compute n).hi /\
    1 - ((cosPiRawOfArctan B x _).compute n).lo <= 1
  simpa [cosPiRawOfArctan, rationalCircleCosInterval] using
    (And.intro (by grind [hhi.2]) (by grind [hlo.1]))

def oneMinusCosOnHalf
    (B : IntegralIdentities.ArctanInverseBisection) : FunctionOnInterval where
  raw := {
    definedAt := fun x => 0 <= x /\ x <= (1 : Rat) / 2
    compute := fun x _hx => (oneMinusCosFunRaw B).compute x
  }
  lower := 0
  upper := (1 : Rat) / 2
  defined_on := by
    intro _ hx
    exact hx
  valid_on := by
    intro x hx
    exact oneMinusCosFunRaw_valid B x hx

theorem oneMinusCosOnHalf_valid
    (B : IntegralIdentities.ArctanInverseBisection) :
  (oneMinusCosOnHalf B).raw.Valid := by
  intro x hx
  change RealCompute.ValidCompute ((oneMinusCosFunRaw B).compute x)
  exact oneMinusCosFunRaw_valid B x hx

set_option maxHeartbeats 1000000 in
def oneMinusCosOnHalf_effectiveModulus
    (B : IntegralIdentities.ArctanInverseBisection)
    (tangentModulus : EffectiveModulusFor
      (IntegralIdentities.tangentOnUnit B)) :
    EffectiveModulusFor (oneMinusCosOnHalf B) where
  inputPrecision := fun n =>
    2 * tangentModulus.inputPrecision (4 * (n + 1))
  evalPrecision := fun n =>
    tangentModulus.evalPrecision (4 * (n + 1))
  close := by
    intro x y n hx hy hclose
    change 0 <= x /\ x <= (1 : Rat) / 2 at hx
    change 0 <= y /\ y <= (1 : Rat) / 2 at hy
    let m := 4 * (n + 1)
    have hscale :
        4 * (precisionAtStage m).val <= (precisionAtStage n).val := by
      cases n with
      | zero => decide +kernel
      | succ n =>
          have hrec := one_div_antitone_pos_local
            (a := ((n + 1 : Nat) : Rat))
            (b := ((n + 2 : Nat) : Rat))
            ((Rat.natCast_pos).2 (Nat.succ_pos n))
            (Rat.natCast_le_natCast.2 (by omega))
          have heq :
              4 * (1 / (((4 * (n + 2) : Nat) : Rat))) =
                1 / (((n + 2 : Nat) : Rat)) := by
            rw [Rat.natCast_mul, Rat.div_def, Rat.div_def]
            have hn : ((n + 2 : Nat) : Rat) ≠ 0 :=
              Rat.ne_of_gt ((Rat.natCast_pos).2 (by omega))
            grind [Rat.mul_assoc, Rat.mul_comm,
              Rat.mul_inv_cancel _ hn]
          dsimp [m, precisionAtStage]
          rw [heq]
          exact hrec
    have hx' : 0 <= 2 * x /\ 2 * x <= 1 := by
      constructor
      · exact Rat.mul_nonneg (by decide +kernel) hx.1
      · have h := Rat.mul_le_mul_of_nonneg_left hx.2
          (by decide +kernel : (0 : Rat) <= 2)
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
        simpa [oneMinusCosOnHalf, hhalf] using h
    have hy' : 0 <= 2 * y /\ 2 * y <= 1 := by
      constructor
      · exact Rat.mul_nonneg (by decide +kernel) hy.1
      · have h := Rat.mul_le_mul_of_nonneg_left hy.2
          (by decide +kernel : (0 : Rat) <= 2)
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
        simpa [oneMinusCosOnHalf, hhalf] using h
    have hinput : qabs (2 * y - 2 * x) <=
        1 / ((tangentModulus.inputPrecision m : Nat) : Rat) := by
      have hmul := Rat.mul_le_mul_of_nonneg_left hclose
        (by decide +kernel : (0 : Rat) <= 2)
      rw [show 2 * y - 2 * x = 2 * (y - x) by grind, qabs_mul]
      have htwo : qabs (2 : Rat) = 2 := by decide +kernel
      rw [htwo]
      have hmul' : 2 * qabs (y - x) <=
          2 * (1 / ((2 * tangentModulus.inputPrecision m : Nat) : Rat)) := by
        simpa [m, Rat.natCast_mul, Rat.mul_comm] using hmul
      calc
        2 * qabs (y - x) <=
            2 * (1 / ((2 * tangentModulus.inputPrecision m : Nat) : Rat)) := hmul'
        _ = 1 / ((tangentModulus.inputPrecision m : Nat) : Rat) := by
          rw [Rat.natCast_mul, Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm,
            Rat.mul_inv_cancel]
    have htangent := tangentModulus.close
      (2 * x) (2 * y) m hx' hy' hinput
    have honeMinus := oneMinusCosFunRaw_near_of_tangent_near
      B hx hy
      (by exact hx') (by exact hy')
      (tangentModulus.evalPrecision m) (precisionAtStage m) htangent
    change QInterval.NearAt
      ((oneMinusCosOnHalf B).compute x hx (tangentModulus.evalPrecision m))
      ((oneMinusCosOnHalf B).compute y hy (tangentModulus.evalPrecision m))
      (precisionAtStage n)
    change QInterval.NearAt
      ((oneMinusCosFunRaw B).compute x (tangentModulus.evalPrecision m))
      ((oneMinusCosFunRaw B).compute y (tangentModulus.evalPrecision m))
      (precisionAtStage n)
    change QInterval.NearAt
      ((oneMinusCosFunRaw B).compute x (tangentModulus.evalPrecision m))
      ((oneMinusCosFunRaw B).compute y (tangentModulus.evalPrecision m))
      (precisionAtStage n)
    unfold QInterval.NearAt QInterval.width at honeMinus ⊢
    rcases honeMinus with ⟨hxy, hyx, hwidthx, hwidthy⟩
    constructor <;> grind

def primitiveRawOfArctan
    (B : IntegralIdentities.ArctanInverseBisection) : RealFunRaw :=
  RealFunRaw.mul reciprocalPiFunRaw (oneMinusCosFunRaw B)

theorem primitiveRawOfArctan_valid
    (B : IntegralIdentities.ArctanInverseBisection) :
    (primitiveRawOfArctan B).Valid := by
  apply RealFunRaw.mul_valid_of_nonneg_bounded
    reciprocalPiFunRaw_valid (oneMinusCosFunRaw_valid B)
  · intro x _
    refine ⟨1, by decide +kernel, ?_⟩
    intro n
    exact reciprocalPiRaw_bounds n
  · intro x hx
    refine ⟨1, by decide +kernel, ?_⟩
    intro n
    change 0 <= x /\ x <= (1 : Rat) / 2 at hx
    have ht := arctanInverse_slope_bounded B x hx n
    have htarg : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x) := by
      change 0 <= 2 * x /\ 2 * x <= 1
      constructor
      · exact Rat.mul_nonneg (by decide +kernel) hx.1
      · have h := Rat.mul_le_mul_of_nonneg_left hx.2
          (by decide +kernel : (0 : Rat) <= 2)
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
        rw [hhalf] at h
        exact h
    have htv := B.tangentRaw_valid (2 * x) htarg
    have hto := RealCompute.interval_order_of_valid
      { compute := B.tangentRaw.compute (2 * x) htarg } htv n
    have hlo := rationalCircleCos_bounds ht.1 (by grind [ht.2])
    have hhi := rationalCircleCos_bounds (by grind [ht.1]) ht.2
    simp only [oneMinusCosFunRaw, dif_pos hx]
    change 0 <= 1 - ((cosPiRawOfArctan B x _).compute n).hi /\
      1 - ((cosPiRawOfArctan B x _).compute n).lo <= 1
    simpa [cosPiRawOfArctan, rationalCircleCosInterval] using
      (And.intro (by grind [hhi.2]) (by grind [hlo.1]))

theorem primitiveRawOfArctan_bounds
    (B : IntegralIdentities.ArctanInverseBisection)
    {x : Rat} (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n : Nat) :
    0 <= ((primitiveRawOfArctan B).compute x n).lo /\
      ((primitiveRawOfArctan B).compute x n).hi <= 1 := by
  have hR := reciprocalPiRaw_bounds n
  have hM := oneMinusCosFunRaw_bounds B hx n
  have hRorder := RealCompute.interval_order_of_valid reciprocalPiRaw
    reciprocalPiRaw_valid n
  have hMvalid := oneMinusCosFunRaw_valid B x hx
  have hMorder := RealCompute.interval_order_of_valid
    { compute := (oneMinusCosFunRaw B).compute x } hMvalid n
  change 0 <= (QBox.mulRealInterval
      (reciprocalPiRaw.compute n).lo (reciprocalPiRaw.compute n).hi
      ((oneMinusCosFunRaw B).compute x n).lo
      ((oneMinusCosFunRaw B).compute x n).hi).lo /\
    (QBox.mulRealInterval
      (reciprocalPiRaw.compute n).lo (reciprocalPiRaw.compute n).hi
      ((oneMinusCosFunRaw B).compute x n).lo
      ((oneMinusCosFunRaw B).compute x n).hi).hi <= 1
  rw [QBox.mulRealInterval_of_nonneg hR.1 hRorder hM.1 hMorder]
  constructor
  · exact Rat.mul_nonneg hR.1 hM.1
  · have hMhi0 : 0 <= ((oneMinusCosFunRaw B).compute x n).hi := by
      grind
    calc
      (reciprocalPiRaw.compute n).hi *
          ((oneMinusCosFunRaw B).compute x n).hi <=
          1 * ((oneMinusCosFunRaw B).compute x n).hi :=
        Rat.mul_le_mul_of_nonneg_right hR.2 hMhi0
      _ <= 1 := by simpa using hM.2

private theorem primitive_mul_zero_equiv (R : RealCompute) (hR : R.Valid)
    (hRnonneg : forall n, 0 <= (R.compute n).lo) :
    (R * RealCompute.zero).Equiv RealCompute.zero := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff (R * RealCompute.zero) RealCompute.zero n n).2
  have horder := RealCompute.interval_order_of_valid R hR n
  change QInterval.Overlaps
    (QBox.mulRealInterval (R.compute n).lo (R.compute n).hi 0 0)
    { lo := 0, hi := 0 }
  rw [QBox.mulRealInterval_of_nonneg (hRnonneg n) horder
    (by decide +kernel) (by decide +kernel)]
  simp [QInterval.Overlaps]

private theorem one_sub_one_equiv_zero (C : RealCompute) (hC : C.Valid)
    (hCeq : C.Equiv RealCompute.one) :
    (RealCompute.one - C).Equiv RealCompute.zero := by
  have hone : RealCompute.one.Valid := by
    change RealCompute.ValidCompute (fun _ : Nat => { lo := 1, hi := 1 })
    exact RealCompute.ofRat_valid 1
  have hzero : RealCompute.zero.Valid := by
    change RealCompute.ValidCompute (fun _ : Nat => { lo := 0, hi := 0 })
    exact RealCompute.ofRat_valid 0
  have hsub : (RealCompute.one - C).Valid := RealCompute.sub_valid hone hC
  have hself : (RealCompute.one - RealCompute.one).Equiv RealCompute.zero := by
    apply RealCompute.sameStageOverlap_equiv
    intro n
    apply (RealCompute.compareAt_overlap_iff
      (RealCompute.one - RealCompute.one) RealCompute.zero n n).2
    change QInterval.Overlaps
      (RealCompute.subCompute RealCompute.one RealCompute.one n)
      (RealCompute.zero.compute n)
    simp [RealCompute.subCompute, RealCompute.one, RealCompute.zero,
      RealCompute.ofRat, QInterval.Overlaps]
    constructor <;> decide +kernel
  exact RealCompute.equiv_trans hsub
    (RealCompute.sub_valid hone hone) hzero
    (RealCompute.sub_equiv hone hone hC hone
      (RealCompute.equiv_refl RealCompute.one hone) hCeq) hself

private theorem primitive_product_zero_equiv
    (R M : RealCompute) (hR : R.Valid) (hM : M.Valid)
    (hRb : forall n, 0 <= (R.compute n).lo /\ (R.compute n).hi <= 1)
    (hMb : forall n, 0 <= (M.compute n).lo /\ (M.compute n).hi <= 1)
    (hMzero : M.Equiv RealCompute.zero) :
    (R * M).Equiv RealCompute.zero := by
  have hzero : RealCompute.zero.Valid := by
    change RealCompute.ValidCompute (fun _ : Nat => { lo := 0, hi := 0 })
    exact RealCompute.ofRat_valid 0
  have hprod : (R * M).Equiv (R * RealCompute.zero) := by
    apply RealCompute.mul_equiv_of_nonneg hR hR hM hzero
      (fun n => (hRb n).1) (fun n => (hRb n).1)
      (fun n => (hMb n).1)
      (fun n => by change 0 <= 0; decide +kernel)
      (RealCompute.equiv_refl R hR) hMzero
  have hpvalid : (R * M).Valid :=
    RealCompute.mul_valid_of_nonneg_bounded hR hM
      (Bx := (1 : Rat)) (By := (1 : Rat))
      (by decide +kernel) (by decide +kernel) hRb hMb
  have hzvalid : (R * RealCompute.zero).Valid :=
    RealCompute.mul_valid_of_nonneg_bounded hR hzero
      (Bx := (1 : Rat)) (By := (1 : Rat))
      (by decide +kernel) (by decide +kernel) hRb
      (fun n => by change 0 <= 0 /\ 0 <= 1; decide +kernel)
  exact RealCompute.equiv_trans hpvalid hzvalid hzero hprod
    (primitive_mul_zero_equiv R hR (fun n => (hRb n).1))

/-- The left endpoint of the canonical primitive is zero once the geometric
cosine evaluator supplies its endpoint law.  This is the finite interval
algebra needed by the final FTC certificate; no completed real is involved. -/
theorem primitiveRawOfArctan_zero_equiv_of_cosine_endpoint
    (B : IntegralIdentities.ArctanInverseBisection)
    (hc : (cosPiRawOfArctan B 0
      ⟨by decide +kernel, by decide +kernel⟩).Equiv RealCompute.one) :
    ({ compute := (primitiveRawOfArctan B).compute 0 } : RealCompute).Equiv
      RealCompute.zero := by
  let R : RealCompute := reciprocalPiRaw
  let M : RealCompute := { compute := (oneMinusCosFunRaw B).compute 0 }
  have hR : R.Valid := by simpa [R] using reciprocalPiRaw_valid
  have hRb : forall n, 0 <= (R.compute n).lo /\ (R.compute n).hi <= 1 := by
    intro n
    simpa [R] using reciprocalPiRaw_bounds n
  have hM : M.Valid := by
    change RealCompute.ValidCompute ((oneMinusCosFunRaw B).compute 0)
    exact oneMinusCosFunRaw_valid B 0
      (by decide +kernel : (0 : Rat) <= 0 /\ (0 : Rat) <= 1 / 2)
  have hMb : forall n, 0 <= (M.compute n).lo /\ (M.compute n).hi <= 1 := by
    intro n
    simpa [M] using oneMinusCosFunRaw_bounds B
      (by decide +kernel : (0 : Rat) <= 0 /\ (0 : Rat) <= 1 / 2) n
  have hC : (cosPiRawOfArctan B 0
      ⟨by decide +kernel, by decide +kernel⟩).Valid :=
    cosPiRawOfArctan_valid B 0 ⟨by decide +kernel, by decide +kernel⟩
  have hMzero : M.Equiv RealCompute.zero := by
    apply RealCompute.sameStageOverlap_equiv
    intro n
    apply (RealCompute.compareAt_overlap_iff M RealCompute.zero n n).2
    change QInterval.Overlaps
      (if hx : (0 : Rat) <= 0 /\ (0 : Rat) <= 1 / 2 then
        { lo := 1 - ((cosPiRawOfArctan B 0 hx).compute n).hi,
          hi := 1 - ((cosPiRawOfArctan B 0 hx).compute n).lo }
       else { lo := 0, hi := 0 })
      { lo := 0, hi := 0 }
    rw [dif_pos (by decide +kernel : (0 : Rat) <= 0 /\ (0 : Rat) <= 1 / 2)]
    have hc_n := (RealCompute.compareAt_overlap_iff
      (cosPiRawOfArctan B 0 ⟨by decide +kernel, by decide +kernel⟩)
      RealCompute.one n n).1 (hc n)
    simp [RealCompute.one, RealCompute.ofRat] at hc_n
    change QInterval.Overlaps
      { lo := 1 - ((cosPiRawOfArctan B 0 _).compute n).hi,
        hi := 1 - ((cosPiRawOfArctan B 0 _).compute n).lo }
      { lo := 0, hi := 0 }
    unfold QInterval.Overlaps at hc_n ⊢
    constructor <;> grind
  have hprod : (R * M).Equiv RealCompute.zero :=
    primitive_product_zero_equiv R M hR hM hRb hMb hMzero
  change (R * M).Equiv RealCompute.zero
  exact hprod

private theorem primitive_half_product_equiv
    (R M : RealCompute) (hR : R.Valid) (hM : M.Valid)
    (hRb : forall n, 0 <= (R.compute n).lo /\ (R.compute n).hi <= 1)
    (hMb : forall n, 0 <= (M.compute n).lo /\ (M.compute n).hi <= 1)
    (hMone : M.Equiv RealCompute.one) :
    (R * M).Equiv R := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff (R * M) R n n).2
  have hRorder := RealCompute.interval_order_of_valid R hR n
  have hMorder := RealCompute.interval_order_of_valid M hM n
  have hm := (RealCompute.compareAt_overlap_iff M RealCompute.one n n).1 (hMone n)
  simp [RealCompute.one, RealCompute.ofRat] at hm
  change QInterval.Overlaps
    (QBox.mulRealInterval (R.compute n).lo (R.compute n).hi
      (M.compute n).lo (M.compute n).hi)
    (R.compute n)
  rw [QBox.mulRealInterval_of_nonneg (hRb n).1 hRorder
    (hMb n).1 hMorder]
  unfold QInterval.Overlaps
  constructor
  · calc
      (R.compute n).lo * (M.compute n).lo <=
          (R.compute n).lo * 1 :=
        Rat.mul_le_mul_of_nonneg_left hm.1 (hRb n).1
      _ <= (R.compute n).hi := by simpa using hRorder
  · calc
      (R.compute n).lo <= (R.compute n).hi * 1 := by simpa using hRorder
      _ <= (R.compute n).hi * (M.compute n).hi :=
        Rat.mul_le_mul_of_nonneg_left hm.2 (by grind)

/-- The right endpoint of the canonical primitive is the reciprocal-pi raw
number once the cosine evaluator supplies its quarter-turn endpoint law. -/
theorem primitiveRawOfArctan_half_equiv_of_cosine_endpoint
    (B : IntegralIdentities.ArctanInverseBisection)
    (hc : (cosPiRawOfArctan B (1 / 2)
      ⟨by decide +kernel, by decide +kernel⟩).Equiv RealCompute.zero) :
    ({ compute := (primitiveRawOfArctan B).compute (1 / 2) } : RealCompute).Equiv
      reciprocalPiRaw := by
  let R : RealCompute := reciprocalPiRaw
  let M : RealCompute := { compute := (oneMinusCosFunRaw B).compute (1 / 2) }
  have hR : R.Valid := by simpa [R] using reciprocalPiRaw_valid
  have hRb : forall n, 0 <= (R.compute n).lo /\ (R.compute n).hi <= 1 := by
    intro n
    simpa [R] using reciprocalPiRaw_bounds n
  have hM : M.Valid := by
    change RealCompute.ValidCompute ((oneMinusCosFunRaw B).compute (1 / 2))
    exact oneMinusCosFunRaw_valid B (1 / 2)
      (by decide +kernel : (0 : Rat) <= 1 / 2 /\ (1 : Rat) / 2 <= 1 / 2)
  have hMb : forall n, 0 <= (M.compute n).lo /\ (M.compute n).hi <= 1 := by
    intro n
    simpa [M] using oneMinusCosFunRaw_bounds B
      (by decide +kernel : (0 : Rat) <= 1 / 2 /\ (1 : Rat) / 2 <= 1 / 2) n
  have hMone : M.Equiv RealCompute.one := by
    apply RealCompute.sameStageOverlap_equiv
    intro n
    apply (RealCompute.compareAt_overlap_iff M RealCompute.one n n).2
    change QInterval.Overlaps
      (if hx : (0 : Rat) <= 1 / 2 /\ (1 : Rat) / 2 <= 1 / 2 then
        { lo := 1 - ((cosPiRawOfArctan B (1 / 2) hx).compute n).hi,
          hi := 1 - ((cosPiRawOfArctan B (1 / 2) hx).compute n).lo }
       else { lo := 0, hi := 0 })
      { lo := 1, hi := 1 }
    rw [dif_pos (by decide +kernel : (0 : Rat) <= 1 / 2 /\ (1 : Rat) / 2 <= 1 / 2)]
    have hc_n := (RealCompute.compareAt_overlap_iff
      (cosPiRawOfArctan B (1 / 2) ⟨by decide +kernel, by decide +kernel⟩)
      RealCompute.zero n n).1 (hc n)
    simp [RealCompute.zero, RealCompute.ofRat] at hc_n
    change QInterval.Overlaps
      { lo := 1 - ((cosPiRawOfArctan B (1 / 2) _).compute n).hi,
        hi := 1 - ((cosPiRawOfArctan B (1 / 2) _).compute n).lo }
      { lo := 1, hi := 1 }
    unfold QInterval.Overlaps at hc_n ⊢
    constructor <;> grind
  have hpvalid : (R * M).Valid :=
    RealCompute.mul_valid_of_nonneg_bounded hR hM
      (Bx := (1 : Rat)) (By := (1 : Rat))
      (by decide +kernel) (by decide +kernel) hRb hMb
  have hprod : (R * M).Equiv R :=
    primitive_half_product_equiv R M hR hM hRb hMb hMone
  change (R * M).Equiv R
  exact hprod

/-- Package the arctangent-backed evaluator as the interval function consumed
by the equal-dyadic integral operator. -/
def ArctanSinPiConstruction.onHalf
    (S : ArctanSinPiConstruction) : FunctionOnInterval where
  raw := {
    definedAt := fun x => 0 <= x /\ x <= (1 : Rat) / 2
    compute := fun x hx => (sinPiRawOfArctan S.inverse x hx).compute
  }
  lower := 0
  upper := (1 : Rat) / 2
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    exact S.sin_valid x hx

def ArctanSinPiConstruction.halfIntegral
    (S : ArctanSinPiConstruction)
    (c : Integral.SampleConstruction S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2)) : RealCompute :=
  Integral.sampleValue S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2) c

theorem ArctanSinPiConstruction.halfIntegral_valid
    (S : ArctanSinPiConstruction)
    (c : Integral.SampleConstruction S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2)) :
    (S.halfIntegral c).Valid := by
  exact FTC.integral_valid_of_construction c

/-- Static-dyadic FTC bridge for the arctangent-backed sine evaluator.

This is the final theorem-facing assembly point: a primitive `F`, a finite
static-dyadic FTC certificate, and the endpoint schedule agreement identify
the actual equal-dyadic integral with `F(1/2)-F(0)`. -/
theorem ArctanSinPiConstruction.halfIntegral_equiv_endpoint_of_staticFTC
    (S : ArctanSinPiConstruction)
    (F : RealFunRaw)
    (h : StaticDyadicEffectiveFTC F S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (c : Integral.SampleConstruction S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2))
    (hplan : c.plan = FTC.integralPlanOfStaticDyadicEffectiveFTC h)
    (endpoint : FTC.EndpointScheduleAgreement F 0 ((1 : Rat) / 2)
      (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC)) :
    (S.halfIntegral c).Equiv
      (endpointDifferenceRaw F 0 ((1 : Rat) / 2) endpoint.endpoint_valid) := by
  exact FTC.staticDyadicEffectiveFTC_definiteIntegralEqualsEndpoint_of_endpointAgreement
    h c hplan endpoint

/-- The complete proof object needed to identify the half-period integral with
the expected reciprocal-pi value.  The primitive and its static-dyadic FTC
certificate are intentionally fields: they are the analytic work, while the
endpoint target and the computable value `reciprocalPiRaw` are now fixed by
the project. -/
structure HalfIntegralReciprocalPiCertificate
    (S : ArctanSinPiConstruction) where
  primitive : RealFunRaw
  ftc : StaticDyadicEffectiveFTC primitive S.onHalf.toRealFunRaw
    0 ((1 : Rat) / 2)
  integral : Integral.SampleConstruction S.onHalf.toRealFunRaw
    0 ((1 : Rat) / 2)
  integral_plan : integral.plan = FTC.integralPlanOfStaticDyadicEffectiveFTC ftc
  endpoint : FTC.EndpointScheduleAgreement primitive 0 ((1 : Rat) / 2)
    (FTC.endpointRawOfEffectiveFTC ftc.toEffectiveFTC)
  endpoint_equiv_reciprocalPi :
    endpointDifferenceRaw primitive 0 ((1 : Rat) / 2)
      endpoint.endpoint_valid |>.Equiv reciprocalPiRaw

theorem ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi
    (S : ArctanSinPiConstruction)
    (h : HalfIntegralReciprocalPiCertificate S) :
    (S.halfIntegral h.integral).Equiv reciprocalPiRaw := by
  have hinterval :=
    S.halfIntegral_equiv_endpoint_of_staticFTC h.primitive h.ftc h.integral
      h.integral_plan h.endpoint
  have hendpointValid :
      (endpointDifferenceRaw h.primitive 0 ((1 : Rat) / 2)
        h.endpoint.endpoint_valid).Valid := by
    simpa [endpointDifferenceRaw, RealCompute.Valid] using h.endpoint.endpoint_valid
  exact RealCompute.equiv_trans (S.halfIntegral_valid h.integral)
    hendpointValid
    reciprocalPiRaw_valid hinterval h.endpoint_equiv_reciprocalPi

/-! The theorem-facing certificate uses the primitive constructed above,
rather than allowing an unrelated primitive to be supplied.  This is the
canonical `sin (pi*x)` statement: the remaining analytic obligations are
exactly the finite FTC certificate and the endpoint computation for this
primitive. -/

def ArctanSinPiConstruction.canonicalPrimitive
    (S : ArctanSinPiConstruction) : RealFunRaw :=
  primitiveRawOfArctan S.inverse

theorem ArctanSinPiConstruction.canonicalPrimitive_valid
    (S : ArctanSinPiConstruction) :
    S.canonicalPrimitive.Valid := by
  exact primitiveRawOfArctan_valid S.inverse

theorem ArctanSinPiConstruction.canonicalPrimitive_domain_zero
    (S : ArctanSinPiConstruction) :
    S.canonicalPrimitive.domain 0 := by
  exact ⟨⟨by decide +kernel, by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel⟩⟩

theorem ArctanSinPiConstruction.canonicalPrimitive_domain_half
    (S : ArctanSinPiConstruction) :
    S.canonicalPrimitive.domain ((1 : Rat) / 2) := by
  exact ⟨⟨by decide +kernel, by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel⟩⟩

private theorem sub_zero_equiv (R : RealCompute) (hR : R.Valid) :
    (R - RealCompute.zero).Equiv R := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff (R - RealCompute.zero) R n n).2
  have horder := RealCompute.interval_order_of_valid R hR n
  change QInterval.Overlaps
    { lo := (R.compute n).lo - 0, hi := (R.compute n).hi - 0 }
    (R.compute n)
  simp [QInterval.Overlaps]
  constructor <;> grind

/-- Generic endpoint algebra for the computable primitive layer.  Once the
endpoint values are certified as `0` and a raw value `R`, the endpoint
difference is automatically equivalent to `R`; this theorem is independent
of the analytic proof that establishes those endpoint laws. -/
theorem endpointDifference_equiv_of_endpoint_equiv
    {F : RealFunRaw} {a b : Rat}
    (hF : F.Valid) (ha : F.domain a) (hb : F.domain b)
    (hendpoint : RealCompute.ValidCompute (endpointDifferenceCompute F a b))
    {R : RealCompute} (hR : R.Valid)
    (hA : (F.apply hF a ha).Equiv RealCompute.zero)
    (hB : (F.apply hF b hb).Equiv R) :
    (endpointDifferenceRaw F a b hendpoint).Equiv R := by
  let A : RealCompute := F.apply hF a ha
  let B : RealCompute := F.apply hF b hb
  have hAval : A.Valid := by
    simpa [A, RealCompute.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF a ha
  have hBval : B.Valid := by
    simpa [B, RealCompute.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF b hb
  have hzero : RealCompute.zero.Valid := by
    unfold RealCompute.zero
    exact RealCompute.ofRat_valid 0
  have hsub : (B - A).Equiv (R - RealCompute.zero) :=
    RealCompute.sub_equiv hBval hR hAval hzero hB hA
  have hsubvalid : (B - A).Valid := RealCompute.sub_valid hBval hAval
  have htargetvalid : (R - RealCompute.zero).Valid :=
    RealCompute.sub_valid hR hzero
  change (B - A).Equiv R
  exact RealCompute.equiv_trans hsubvalid htargetvalid hR hsub
    (sub_zero_equiv R hR)

/-- The canonical primitive's endpoint difference is the reciprocal-pi raw
number once the two geometric cosine endpoint laws are supplied.  This is the
last finite endpoint-algebra bridge before the dyadic FTC certificate. -/
theorem primitiveRawOfArctan_endpointDifference_equiv_of_cosine_endpoints
    (B : IntegralIdentities.ArctanInverseBisection)
    (hc0 : (cosPiRawOfArctan B 0
      ⟨by decide +kernel, by decide +kernel⟩).Equiv RealCompute.one)
    (hcHalf : (cosPiRawOfArctan B (1 / 2)
      ⟨by decide +kernel, by decide +kernel⟩).Equiv RealCompute.zero)
    (hendpoint :
      RealCompute.ValidCompute
        (endpointDifferenceCompute (primitiveRawOfArctan B)
          0 ((1 : Rat) / 2))) :
    (endpointDifferenceRaw (primitiveRawOfArctan B) 0 ((1 : Rat) / 2)
      hendpoint).Equiv reciprocalPiRaw := by
  have hF : (primitiveRawOfArctan B).Valid :=
    primitiveRawOfArctan_valid B
  have ha : (primitiveRawOfArctan B).domain 0 := by
    simp [primitiveRawOfArctan, RealFunRaw.mul, reciprocalPiFunRaw,
      oneMinusCosFunRaw] <;> decide +kernel
  have hb : (primitiveRawOfArctan B).domain ((1 : Rat) / 2) := by
    simp [primitiveRawOfArctan, RealFunRaw.mul, reciprocalPiFunRaw,
      oneMinusCosFunRaw] <;> decide +kernel
  have hA : ((primitiveRawOfArctan B).apply hF 0 ha).Equiv
      RealCompute.zero := by
    change ({ compute := (primitiveRawOfArctan B).compute 0 } : RealCompute).Equiv
      RealCompute.zero
    exact primitiveRawOfArctan_zero_equiv_of_cosine_endpoint B hc0
  have hB : ((primitiveRawOfArctan B).apply hF ((1 : Rat) / 2) hb).Equiv
      reciprocalPiRaw := by
    change ({ compute := (primitiveRawOfArctan B).compute ((1 : Rat) / 2) } :
      RealCompute).Equiv reciprocalPiRaw
    exact primitiveRawOfArctan_half_equiv_of_cosine_endpoint B hcHalf
  exact endpointDifference_equiv_of_endpoint_equiv
    hF ha hb hendpoint reciprocalPiRaw_valid hA hB

theorem primitiveRawOfArctan_endpointDifference_equiv_of_cosine_endpoints'
    (B : IntegralIdentities.ArctanInverseBisection)
    (hc0 : (cosPiRawOfArctan B 0
      ⟨by decide +kernel, by decide +kernel⟩).Equiv RealCompute.one)
    (hcHalf : (cosPiRawOfArctan B (1 / 2)
      ⟨by decide +kernel, by decide +kernel⟩).Equiv RealCompute.zero) :
    (endpointDifferenceRaw (primitiveRawOfArctan B) 0 ((1 : Rat) / 2)
      (endpointDifference_valid_of_fun_valid
        (primitiveRawOfArctan_valid B)
        (by
          simp [primitiveRawOfArctan, RealFunRaw.mul, reciprocalPiFunRaw,
            oneMinusCosFunRaw] <;> decide +kernel)
        (by
          simp [primitiveRawOfArctan, RealFunRaw.mul, reciprocalPiFunRaw,
            oneMinusCosFunRaw] <;> decide +kernel))).Equiv reciprocalPiRaw := by
  apply primitiveRawOfArctan_endpointDifference_equiv_of_cosine_endpoints
    B hc0 hcHalf

/-- Same endpoint bridge with the inverse-search endpoint laws exposed
directly.  These are the two finite inverse facts needed at normalized angles
`0` and `1`; the circle-coordinate endpoint laws are then automatic. -/
theorem primitiveRawOfArctan_endpointDifference_equiv_of_tangent_endpoints
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    (ht1 : (B.tangentAt 1
      RationalCircle.GeometricTrig.firstQuadrantBranch_one).Equiv
      RealCompute.one) :
    (endpointDifferenceRaw (primitiveRawOfArctan B) 0 ((1 : Rat) / 2)
      (endpointDifference_valid_of_fun_valid
        (primitiveRawOfArctan_valid B)
        (by
          simp [primitiveRawOfArctan, RealFunRaw.mul, reciprocalPiFunRaw,
            oneMinusCosFunRaw] <;> decide +kernel)
        (by
          simp [primitiveRawOfArctan, RealFunRaw.mul, reciprocalPiFunRaw,
            oneMinusCosFunRaw] <;> decide +kernel))).Equiv reciprocalPiRaw := by
  apply primitiveRawOfArctan_endpointDifference_equiv_of_cosine_endpoints'
    B
    (cosPiRawOfArctan_zero_equiv_one_of_tangent_endpoint B ht0)
    (cosPiRawOfArctan_half_equiv_zero_of_tangent_endpoint B ht1)

/-- The endpoint-form computable integral for the canonical sine primitive.
This is the exact value supplied by the finite FTC route; unlike a classical
real integral, it is an explicit `RealCompute` endpoint computation. -/
def canonicalSineEndpointIntegral
    (S : ArctanSinPiConstruction) : RealCompute :=
  endpointDifferenceRaw S.canonicalPrimitive 0 ((1 : Rat) / 2)
    (endpointDifference_valid_of_fun_valid
      S.canonicalPrimitive_valid
      S.canonicalPrimitive_domain_zero
      S.canonicalPrimitive_domain_half)

theorem canonicalSineEndpointIntegral_valid
    (S : ArctanSinPiConstruction) :
    (canonicalSineEndpointIntegral S).Valid := by
  exact endpointDifference_valid_of_fun_valid
    S.canonicalPrimitive_valid
    S.canonicalPrimitive_domain_zero
    S.canonicalPrimitive_domain_half

theorem canonicalSineEndpointIntegral_equiv_reciprocalPi
    (S : ArctanSinPiConstruction)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    (ht1 : (S.inverse.tangentAt 1
      RationalCircle.GeometricTrig.firstQuadrantBranch_one).Equiv
      RealCompute.one) :
    (canonicalSineEndpointIntegral S).Equiv reciprocalPiRaw := by
  simpa [canonicalSineEndpointIntegral,
    ArctanSinPiConstruction.canonicalPrimitive] using
    primitiveRawOfArctan_endpointDifference_equiv_of_tangent_endpoints
      S.inverse ht0 ht1

theorem ArctanSinPiConstruction.halfIntegral_equiv_canonicalSineEndpointIntegral
    (S : ArctanSinPiConstruction)
    (h : StaticDyadicEffectiveFTC S.canonicalPrimitive
      S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2))
    (c : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (hplan : c.plan = FTC.integralPlanOfStaticDyadicEffectiveFTC h)
    (endpoint : FTC.EndpointScheduleAgreement S.canonicalPrimitive
      0 ((1 : Rat) / 2)
      (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC)) :
    (S.halfIntegral c).Equiv (canonicalSineEndpointIntegral S) := by
  have hinterval :=
    S.halfIntegral_equiv_endpoint_of_staticFTC
      S.canonicalPrimitive h c hplan endpoint
  simpa [canonicalSineEndpointIntegral, endpointDifferenceRaw] using hinterval

structure CanonicalHalfIntegralReciprocalPiCertificate
    (S : ArctanSinPiConstruction) where
  ftc : StaticDyadicEffectiveFTC
    S.canonicalPrimitive S.onHalf.toRealFunRaw
    0 ((1 : Rat) / 2)
  integral : Integral.SampleConstruction S.onHalf.toRealFunRaw
    0 ((1 : Rat) / 2)
  integral_plan : integral.plan = FTC.integralPlanOfStaticDyadicEffectiveFTC ftc
  endpoint : FTC.EndpointScheduleAgreement
    S.canonicalPrimitive 0 ((1 : Rat) / 2)
    (FTC.endpointRawOfEffectiveFTC ftc.toEffectiveFTC)
  endpoint_equiv_reciprocalPi :
  endpointDifferenceRaw S.canonicalPrimitive 0 ((1 : Rat) / 2)
      endpoint.endpoint_valid |>.Equiv reciprocalPiRaw

/-- Assemble the canonical certificate once the finite FTC data, endpoint
schedule, and the two inverse-search endpoint laws are available. -/
def CanonicalHalfIntegralReciprocalPiCertificate.ofTangentEndpoints
    (S : ArctanSinPiConstruction)
    (ftc : StaticDyadicEffectiveFTC
      S.canonicalPrimitive S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (integral : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (integral_plan : integral.plan =
      FTC.integralPlanOfStaticDyadicEffectiveFTC ftc)
    (endpoint : FTC.EndpointScheduleAgreement
      S.canonicalPrimitive 0 ((1 : Rat) / 2)
      (FTC.endpointRawOfEffectiveFTC ftc.toEffectiveFTC))
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    (ht1 : (S.inverse.tangentAt 1
      RationalCircle.GeometricTrig.firstQuadrantBranch_one).Equiv
      RealCompute.one) :
    CanonicalHalfIntegralReciprocalPiCertificate S where
  ftc := ftc
  integral := integral
  integral_plan := integral_plan
  endpoint := endpoint
  endpoint_equiv_reciprocalPi := by
    simpa [ArctanSinPiConstruction.canonicalPrimitive] using
      primitiveRawOfArctan_endpointDifference_equiv_of_tangent_endpoints
        S.inverse ht0 ht1

theorem ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi_canonical
    (S : ArctanSinPiConstruction)
    (h : CanonicalHalfIntegralReciprocalPiCertificate S) :
    (S.halfIntegral h.integral).Equiv reciprocalPiRaw := by
  have hinterval :=
    S.halfIntegral_equiv_endpoint_of_staticFTC
      S.canonicalPrimitive h.ftc h.integral h.integral_plan h.endpoint
  have hendpointValid :
      (endpointDifferenceRaw S.canonicalPrimitive 0 ((1 : Rat) / 2)
        h.endpoint.endpoint_valid).Valid := by
    simpa [endpointDifferenceRaw, RealCompute.Valid] using h.endpoint.endpoint_valid
  exact RealCompute.equiv_trans
    (S.halfIntegral_valid h.integral)
    hendpointValid reciprocalPiRaw_valid hinterval
    h.endpoint_equiv_reciprocalPi

theorem rationalCircleSinInterval_formula (U : QInterval) :
    rationalCircleSinInterval U =
      { lo := rationalCircleSin U.lo, hi := rationalCircleSin U.hi } :=
  rfl

/-!
## The rational tangent-chart pullback

For the public function `sin (pi*x)` on `[0,1/2]`, write
`u = tan (pi*x/2)`.  The finite change-of-variables calculation is then

`sin (pi*x) dx = (1/pi) * (4*u/(1+u^2)^2) du`.

The following definitions deliberately contain no real-valued `pi`: the
factor `1/pi` is represented separately by `reciprocalPiRaw`.  The rational
part is suitable for the existing Lipschitz--dyadic constructor.
-/

def tangentPullbackDensity (u : Rat) : Rat :=
  4 * (u * (1 / (1 + u * u))) * (1 / (1 + u * u))

def tangentPullbackPrimitive (u : Rat) : Rat :=
  2 * (u * u) / (1 + u * u)

/-! These are the exact rational-circle identities behind the pullback.  They
are deliberately stated before any interval or limiting argument: the
primitive is literally the cosine complement, and the density is the circle
sine multiplied by the chart Jacobian. -/

theorem tangentPullbackPrimitive_eq_one_sub_cos (u : Rat) :
    tangentPullbackPrimitive u = 1 - RationalCircle.Trigonometry.cos u := by
  rw [tangentPullbackPrimitive, RationalCircle.Trigonometry.cos_eq]
  have hden : 1 + u * u ≠ 0 :=
    Rat.ne_of_gt (RationalCircle.Stage.one_add_square_pos u)
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel _ hden]

theorem tangentPullbackDensity_eq_sin_mul_chartJacobian (u : Rat) :
    tangentPullbackDensity u =
      RationalCircle.Trigonometry.sin u * (2 / (1 + u * u)) := by
  rw [tangentPullbackDensity, RationalCircle.Trigonometry.sin_eq]
  have hden : 1 + u * u ≠ 0 :=
    Rat.ne_of_gt (RationalCircle.Stage.one_add_square_pos u)
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_inv_cancel _ hden]

/-! The ordinary forward cell `[x,x+h]` is now expressed through the same
rational tangent increment used by the arctangent rectangle algorithm.  This
is an exact finite secant identity; no derivative or completed real number is
being invoked. -/

theorem tangentPullbackPrimitive_increment_eq_chart_sine
    {x h : Rat} (hx0 : 0 <= x) (hpos : 0 < h)
    (hupper : x + h <= 1) :
    tangentPullbackPrimitive (x + h) - tangentPullbackPrimitive x =
      RationalCircle.Trigonometry.sin x *
          RationalCircle.Trigonometry.sin
            (ArctanGeometry.tangentChartIncrement x h) +
        RationalCircle.Trigonometry.cos x *
          (1 - RationalCircle.Trigonometry.cos
            (ArctanGeometry.tangentChartIncrement x h)) := by
  let t := ArctanGeometry.tangentChartIncrement x h
  have hxlt : x < 1 := by grind
  have ht0 : 0 <= t := by
    dsimp [t]
    exact Rat.le_of_lt (ArctanGeometry.tangentChartIncrement_pos hx0 hpos)
  have ht1 : t <= 1 := by
    dsimp [t]
    exact Rat.le_trans
      (ArctanGeometry.tangentChartIncrement_le_step hx0 hpos)
      (by grind)
  have hden : RationalCircle.Trigonometry.chartAddDen x t ≠ 0 :=
    Rat.ne_of_gt (ArctanGeometry.chartAddDen_pos_of_unit hx0 hxlt ht1)
  have hchart : RationalCircle.Trigonometry.chartAddParameter x t = x + h := by
    dsimp [t]
    exact ArctanGeometry.chartAddParameter_tangentChartIncrement hx0
      (by grind)
  rw [tangentPullbackPrimitive_eq_one_sub_cos]
  rw [tangentPullbackPrimitive_eq_one_sub_cos]
  rw [← hchart]
  have hinc :=
    RationalCircle.Trigonometry.one_sub_cos_chartAdd_eq_sin_mul_sin_add_cos_mul_one_sub_cos
      hden
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm]

theorem tangentPullbackPrimitive_increment_error_le
    {x h : Rat} (hx0 : 0 <= x) (hpos : 0 < h)
    (hupper : x + h <= 1) :
    qabs (
      (tangentPullbackPrimitive (x + h) - tangentPullbackPrimitive x) -
        RationalCircle.Trigonometry.sin x *
          RationalCircle.Trigonometry.sin
            (ArctanGeometry.tangentChartIncrement x h)) <=
      2 * (ArctanGeometry.tangentChartIncrement x h *
        ArctanGeometry.tangentChartIncrement x h) := by
  have hdecomp := tangentPullbackPrimitive_increment_eq_chart_sine
    hx0 hpos hupper
  rw [hdecomp]
  have hrewrite :
      RationalCircle.Trigonometry.sin x *
          RationalCircle.Trigonometry.sin
            (ArctanGeometry.tangentChartIncrement x h) +
        RationalCircle.Trigonometry.cos x *
          (1 - RationalCircle.Trigonometry.cos
            (ArctanGeometry.tangentChartIncrement x h)) -
        RationalCircle.Trigonometry.sin x *
          RationalCircle.Trigonometry.sin
            (ArctanGeometry.tangentChartIncrement x h) =
      RationalCircle.Trigonometry.cos x *
        (1 - RationalCircle.Trigonometry.cos
          (ArctanGeometry.tangentChartIncrement x h)) := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]
  rw [hrewrite, qabs_mul]
  have hcos := RationalCircle.Trigonometry.qabs_cos_le_one x
  have hcorr0 := RationalCircle.Trigonometry.one_sub_cos_nonneg
    (ArctanGeometry.tangentChartIncrement x h)
  have hcorr := RationalCircle.Trigonometry.one_sub_cos_le_two_mul_sq
    (ArctanGeometry.tangentChartIncrement x h)
  rw [qabs_eq_self_of_nonneg hcorr0]
  calc
    qabs (RationalCircle.Trigonometry.cos x) *
        (1 - RationalCircle.Trigonometry.cos
          (ArctanGeometry.tangentChartIncrement x h)) <=
        1 * (1 - RationalCircle.Trigonometry.cos
          (ArctanGeometry.tangentChartIncrement x h)) := by
      exact Rat.mul_le_mul_of_nonneg_right hcos (by grind)
    _ <= 2 * (ArctanGeometry.tangentChartIncrement x h *
        ArctanGeometry.tangentChartIncrement x h) := by
      simpa using hcorr

theorem tangentPullbackPrimitive_endpoint_difference (p r : Rat) :
    tangentPullbackPrimitive r - tangentPullbackPrimitive p =
      (r - p) *
        (2 * (r + p) *
          ((1 + p * p) * (1 + r * r))⁻¹) := by
  have hpSquare := rat_square_nonneg_basic p
  have hrSquare := rat_square_nonneg_basic r
  have hp : 0 < 1 + p * p := by grind
  have hr : 0 < 1 + r * r := by grind
  have hpne : 1 + p * p ≠ 0 := Rat.ne_of_gt hp
  have hrne : 1 + r * r ≠ 0 := Rat.ne_of_gt hr
  rw [tangentPullbackPrimitive, tangentPullbackPrimitive]
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg, Rat.inv_mul_rev,
    Rat.mul_inv_cancel _ hpne, Rat.mul_inv_cancel _ hrne]

private theorem tangentPullback_secant_polynomial (p r : Rat) :
    2 * (r + p) * (1 + p * p) -
        4 * p * (1 + r * r) =
      2 * (r - p) * (1 - p * p - 2 * p * r) := by
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.sub_eq_add_neg]

/-! The local secant identity is the finite FTC calculation used by the
dyadic proof.  It compares the secant slope of the primitive with the
pullback density at the left endpoint; no limiting real number is involved. -/

theorem tangentPullbackPrimitive_secant_identity
    {p r : Rat} (hpr : p < r) :
    (tangentPullbackPrimitive r - tangentPullbackPrimitive p) / (r - p) -
        tangentPullbackDensity p =
      2 * (r - p) * (1 - p * p - 2 * p * r) /
        ((1 + p * p) * (1 + p * p) * (1 + r * r)) := by
  have hpSquare := rat_square_nonneg_basic p
  have hrSquare := rat_square_nonneg_basic r
  have hp : 0 < 1 + p * p := by grind
  have hr : 0 < 1 + r * r := by grind
  have hwidth : 0 < r - p := by grind
  have hpne : 1 + p * p ≠ 0 := Rat.ne_of_gt hp
  have hrne : 1 + r * r ≠ 0 := Rat.ne_of_gt hr
  rw [tangentPullbackPrimitive_endpoint_difference]
  rw [tangentPullbackDensity]
  let A : Rat := 1 + p * p
  let B : Rat := 1 + r * r
  let W : Rat := r - p
  have hprod : 0 < W * (A * A * B) := by
    dsimp [W, A, B]
    exact Rat.mul_pos hwidth (Rat.mul_pos (Rat.mul_pos hp hp) hr)
  apply rat_eq_of_mul_eq_mul_pos_local (c := W * (A * A * B)) hprod
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have hwidthne : r - p ≠ 0 := Rat.ne_of_gt hwidth
  have hAne : A ≠ 0 := by dsimp [A]; exact hpne
  have hBne : B ≠ 0 := by dsimp [B]; exact hrne
  have hWne : W ≠ 0 := by dsimp [W]; exact hwidthne
  have hA_cancel : A⁻¹ * A = 1 := Rat.inv_mul_cancel A hAne
  have hB_cancel : B⁻¹ * B = 1 := Rat.inv_mul_cancel B hBne
  have hW_cancel : W⁻¹ * W = 1 := Rat.inv_mul_cancel W hWne
  have hAB_cancel : (A * B)⁻¹ * (A * A * B) = A := by
    rw [Rat.inv_mul_rev]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_rev]
  have hA2_cancel : A⁻¹ * A⁻¹ * (A * A * B) = B := by
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hD_cancel : (A * A * B)⁻¹ * (A * A * B) = 1 :=
    Rat.inv_mul_cancel _ (Rat.ne_of_gt (Rat.mul_pos (Rat.mul_pos hp hp) hr))
  change
    ((W * (2 * (r + p) * (A * B)⁻¹) * W⁻¹ -
      4 * (p * (1 * A⁻¹)) * (1 * A⁻¹)) * (W * (A * A * B))) =
      (2 * W * (1 - p * p - 2 * p * r) * (A * A * B)⁻¹) *
        (W * (A * A * B))
  have hterm1 :
      (W * (2 * (r + p) * (A * B)⁻¹) * W⁻¹) *
          (W * (A * A * B)) = W * (2 * (r + p) * A) := by
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.sub_eq_add_neg]
  have hterm2 :
      (4 * (p * (1 * A⁻¹)) * (1 * A⁻¹)) *
          (W * (A * A * B)) = 4 * p * W * B := by
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.sub_eq_add_neg]
  have hpoly :
      2 * (r + p) * A - 4 * p * B =
        2 * W * (1 - p * p - 2 * p * r) := by
    simpa [A, B, W] using tangentPullback_secant_polynomial p r
  calc
    (W * (2 * (r + p) * (A * B)⁻¹) * W⁻¹ -
        4 * (p * (1 * A⁻¹)) * (1 * A⁻¹)) * (W * (A * A * B)) =
      W * (2 * (r + p) * A - 4 * p * B) := by
        calc
          _ = (W * (2 * (r + p) * (A * B)⁻¹) * W⁻¹) *
                (W * (A * A * B)) -
              (4 * (p * (1 * A⁻¹)) * (1 * A⁻¹)) *
                (W * (A * A * B)) := by
                  grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add,
                    Rat.mul_assoc, Rat.mul_comm]
          _ = W * (2 * (r + p) * A) - 4 * p * W * B := by
            rw [hterm1, hterm2]
          _ = W * (2 * (r + p) * A - 4 * p * B) := by
            grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add,
              Rat.mul_assoc, Rat.mul_comm]
    _ = 2 * W * W * (1 - p * p - 2 * p * r) := by
      rw [hpoly]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (2 * W * (1 - p * p - 2 * p * r) * (A * A * B)⁻¹) *
        (W * (A * A * B)) := by
      calc
        2 * W * W * (1 - p * p - 2 * p * r) =
            2 * W * (1 - p * p - 2 * p * r) *
              (W * ((A * A * B)⁻¹ * (A * A * B))) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
        _ = 2 * W * (1 - p * p - 2 * p * r) *
              (W * (A * A * B)⁻¹ * (A * A * B)) := by
                rw [hD_cancel]
                grind [Rat.mul_assoc, Rat.mul_comm]
        _ = (2 * W * (1 - p * p - 2 * p * r) * (A * A * B)⁻¹) *
              (W * (A * A * B)) := by
                grind [Rat.mul_assoc, Rat.mul_comm]

theorem tangentPullbackPrimitive_secant_error_le
    {p r : Rat} (hp0 : 0 <= p) (hpr : p < r) (hr1 : r <= 1) :
    qabs ((tangentPullbackPrimitive r - tangentPullbackPrimitive p) /
      (r - p) - tangentPullbackDensity p) <= 4 * qabs (r - p) := by
  have hp1 : p <= 1 := Rat.le_trans (Rat.le_of_lt hpr) hr1
  have hp2nonneg : 0 <= p * p := rat_square_nonneg_basic p
  have hr0 : 0 <= r := Rat.le_trans hp0 (Rat.le_of_lt hpr)
  have hr2nonneg : 0 <= r * r := rat_square_nonneg_basic r
  have hp2le : p * p <= 1 := by
    calc
      p * p <= p * 1 := Rat.mul_le_mul_of_nonneg_left hp1 hp0
      _ = p := by grind
      _ <= 1 := hp1
  have hprle : p * r <= 1 := by
    calc
      p * r <= 1 * r := Rat.mul_le_mul_of_nonneg_right hp1 hr0
      _ <= 1 * 1 := Rat.mul_le_mul_of_nonneg_left hr1 (by decide +kernel)
      _ = 1 := by decide +kernel
  have hKlo : -2 <= 1 - p * p - 2 * p * r := by grind
  have hprnonneg : 0 <= p * r := Rat.mul_nonneg hp0 hr0
  have hKhi : 1 - p * p - 2 * p * r <= 2 := by grind
  have hKabs : qabs (1 - p * p - 2 * p * r) <= 2 :=
    qabs_le_of_neg_le_le hKlo hKhi
  let A : Rat := 1 + p * p
  let B : Rat := 1 + r * r
  let D : Rat := A * A * B
  have hAone : 1 <= A := by dsimp [A]; grind
  have hBone : 1 <= B := by dsimp [B]; grind
  have hDpos : 0 < D := by
    exact Rat.mul_pos (Rat.mul_pos (by grind) (by grind)) (by grind)
  have hDone : 1 <= D := by
    have hAA : 1 <= A * A := by
      calc
        1 = (1 : Rat) * 1 := by decide +kernel
        _ <= A * 1 := Rat.mul_le_mul_of_nonneg_right hAone (by decide +kernel)
        _ <= A * A := Rat.mul_le_mul_of_nonneg_left hAone (by grind)
    calc
      1 = (1 : Rat) * 1 := by decide +kernel
      _ <= (A * A) * 1 := Rat.mul_le_mul_of_nonneg_right hAA (by decide +kernel)
      _ <= (A * A) * B := Rat.mul_le_mul_of_nonneg_left hBone (by grind)
      _ = D := rfl
  have hDne : D ≠ 0 := Rat.ne_of_gt hDpos
  have hDinv0 : 0 <= D⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hDpos)
  have hDinvle : D⁻¹ <= 1 := by
    apply Rat.le_of_mul_le_mul_right (c := D)
    · rw [Rat.inv_mul_cancel _ hDne]
      grind
    · exact hDpos
  have hqabsW : qabs (r - p) = r - p := by
    exact qabs_eq_self_of_nonneg (by grind)
  have hqabsDinv : qabs D⁻¹ = D⁻¹ :=
    qabs_eq_self_of_nonneg hDinv0
  have hDdef : D = (1 + p * p) * (1 + p * p) * (1 + r * r) := by
    rfl
  rw [tangentPullbackPrimitive_secant_identity hpr]
  rw [← hDdef, Rat.div_def, qabs_mul, qabs_mul, qabs_mul]
  rw [hqabsW, hqabsDinv]
  have hqabsTwo : qabs (2 : Rat) = 2 := by decide +kernel
  rw [hqabsTwo]
  calc
      2 * (r - p) * qabs (1 - p * p - 2 * p * r) * D⁻¹ <=
          2 * (r - p) * 2 * D⁻¹ := by
            exact Rat.mul_le_mul_of_nonneg_right
              (Rat.mul_le_mul_of_nonneg_left hKabs
                (Rat.mul_nonneg (by decide +kernel) (by grind))) hDinv0
      _ <= 2 * (r - p) * 2 * 1 := by
        exact Rat.mul_le_mul_of_nonneg_left hDinvle
          (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (by grind))
            (by decide +kernel))
      _ = 4 * (r - p) := by grind

theorem tangentPullback_rectangle_error_le
    {p r : Rat} (hp0 : 0 <= p) (hpr : p < r) (hr1 : r <= 1) :
    qabs ((r - p) * tangentPullbackDensity p -
      (tangentPullbackPrimitive r - tangentPullbackPrimitive p)) <=
        4 * ((r - p) * (r - p)) := by
  have hwidth : 0 < r - p := by grind
  have hwidthne : r - p ≠ 0 := Rat.ne_of_gt hwidth
  have hsec := tangentPullbackPrimitive_secant_error_le hp0 hpr hr1
  have hrewrite :
      (r - p) * tangentPullbackDensity p -
          (tangentPullbackPrimitive r - tangentPullbackPrimitive p) =
        -((r - p) *
          ((tangentPullbackPrimitive r - tangentPullbackPrimitive p) /
            (r - p) - tangentPullbackDensity p)) := by
    rw [Rat.div_def]
    have hcancel : (r - p)⁻¹ * (r - p) = 1 :=
      Rat.inv_mul_cancel _ hwidthne
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.sub_eq_add_neg]
  rw [hrewrite, qabs_neg, qabs_mul]
  rw [qabs_eq_self_of_nonneg (by grind : 0 <= r - p)]
  calc
    (r - p) * qabs
        ((tangentPullbackPrimitive r - tangentPullbackPrimitive p) /
          (r - p) - tangentPullbackDensity p) <=
        (r - p) * (4 * qabs (r - p)) :=
      Rat.mul_le_mul_of_nonneg_left hsec (by grind)
    _ = 4 * ((r - p) * (r - p)) := by
      rw [qabs_eq_self_of_nonneg (by grind : 0 <= r - p)]
      grind

theorem tangentPullback_rectangle_contains_primitive_increment
    {p r : Rat} (hp0 : 0 <= p) (hpr : p < r) (hr1 : r <= 1) :
    QInterval.ContainsInterval
      { lo := (r - p) * tangentPullbackDensity p -
          4 * ((r - p) * (r - p)),
        hi := (r - p) * tangentPullbackDensity p +
          4 * ((r - p) * (r - p)) }
      { lo := tangentPullbackPrimitive r - tangentPullbackPrimitive p,
        hi := tangentPullbackPrimitive r - tangentPullbackPrimitive p } := by
  have herr := tangentPullback_rectangle_error_le hp0 hpr hr1
  unfold QInterval.ContainsInterval
  change
    (r - p) * tangentPullbackDensity p - 4 * ((r - p) * (r - p)) <=
        tangentPullbackPrimitive r - tangentPullbackPrimitive p /\
      tangentPullbackPrimitive r - tangentPullbackPrimitive p <=
        (r - p) * tangentPullbackDensity p + 4 * ((r - p) * (r - p))
  constructor
  · have hhigh := self_le_qabs
      ((r - p) * tangentPullbackDensity p -
        (tangentPullbackPrimitive r - tangentPullbackPrimitive p))
    have hhigh' := Rat.le_trans hhigh herr
    have h1 :
        ((r - p) * tangentPullbackDensity p -
          (tangentPullbackPrimitive r - tangentPullbackPrimitive p)) +
            (tangentPullbackPrimitive r - tangentPullbackPrimitive p) <=
          4 * ((r - p) * (r - p)) +
            (tangentPullbackPrimitive r - tangentPullbackPrimitive p) :=
      (Rat.add_le_add_right (c :=
        tangentPullbackPrimitive r - tangentPullbackPrimitive p)).2 hhigh'
    have h2 := (Rat.add_le_add_left
      (c := -(4 * ((r - p) * (r - p))))).2 h1
    grind
  · have hlow := neg_qabs_le_self
      ((r - p) * tangentPullbackDensity p -
        (tangentPullbackPrimitive r - tangentPullbackPrimitive p))
    have hlow' := Rat.le_trans (Rat.neg_le_neg herr) hlow
    have h1 :
        4 * ((r - p) * (r - p)) +
            -(4 * ((r - p) * (r - p))) <=
          4 * ((r - p) * (r - p)) +
            ((r - p) * tangentPullbackDensity p -
              (tangentPullbackPrimitive r - tangentPullbackPrimitive p)) :=
      (Rat.add_le_add_left
        (c := 4 * ((r - p) * (r - p)))).2 hlow'
    have h2 :
        (4 * ((r - p) * (r - p)) +
            -(4 * ((r - p) * (r - p)))) +
              (tangentPullbackPrimitive r - tangentPullbackPrimitive p) <=
          (4 * ((r - p) * (r - p)) +
            ((r - p) * tangentPullbackDensity p -
              (tangentPullbackPrimitive r - tangentPullbackPrimitive p))) +
              (tangentPullbackPrimitive r - tangentPullbackPrimitive p) :=
      (Rat.add_le_add_right (c :=
        tangentPullbackPrimitive r - tangentPullbackPrimitive p)).2 h1
    grind

/-! A prefix form of the finite dyadic telescope.  This keeps the exact
rectangle computation and the primitive endpoint difference in the same
rational expression; the eventual sum estimate can therefore be proved by
induction on the finite mesh rather than by invoking a completed integral. -/

def tangentPullbackRectangleError (p r : Rat) : Rat :=
  (r - p) * tangentPullbackDensity p -
    (tangentPullbackPrimitive r - tangentPullbackPrimitive p)

def tangentPullbackRectangleErrorPrefix (mesh : Nat) : Nat -> Rat
  | 0 => 0
  | terms + 1 =>
      tangentPullbackRectangleErrorPrefix mesh terms +
        tangentPullbackRectangleError
          ((terms : Rat) / (mesh : Rat))
          (((Nat.succ terms : Nat) : Rat) / (mesh : Rat))

theorem tangentPullbackRectangleErrorPrefix_telescope
    {mesh : Nat} (hmesh : 0 < mesh) :
    forall terms,
      IntegralIdentities.LipschitzDyadic.uniformLeftPrefixSum
          tangentPullbackDensity mesh terms -
          (tangentPullbackPrimitive ((terms : Nat) / (mesh : Rat)) -
            tangentPullbackPrimitive 0) =
        tangentPullbackRectangleErrorPrefix mesh terms
  | 0 => by
      have hzero : (0 : Rat) / (mesh : Rat) = 0 := by
        rw [Rat.div_def]
        grind
      change 0 - (tangentPullbackPrimitive ((0 : Rat) / (mesh : Rat)) -
        tangentPullbackPrimitive 0) = 0
      rw [hzero]
      grind
  | terms + 1 => by
      have hmeshRat : (mesh : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 hmesh)
      rw [IntegralIdentities.LipschitzDyadic.uniformLeftPrefixSum,
        tangentPullbackRectangleErrorPrefix]
      have hsplit :
          (IntegralIdentities.LipschitzDyadic.uniformLeftPrefixSum
              tangentPullbackDensity mesh terms +
            (1 / (mesh : Rat)) *
              tangentPullbackDensity ((terms : Rat) / (mesh : Rat)) -
            (tangentPullbackPrimitive ((terms + 1 : Nat) / (mesh : Rat)) -
              tangentPullbackPrimitive 0)) =
          (IntegralIdentities.LipschitzDyadic.uniformLeftPrefixSum
              tangentPullbackDensity mesh terms -
            (tangentPullbackPrimitive ((terms : Rat) / (mesh : Rat)) -
              tangentPullbackPrimitive 0)) +
          ((1 / (mesh : Rat)) *
              tangentPullbackDensity ((terms : Rat) / (mesh : Rat)) -
            (tangentPullbackPrimitive ((terms + 1 : Nat) / (mesh : Rat)) -
              tangentPullbackPrimitive ((terms : Rat) / (mesh : Rat)))) := by
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
          Rat.mul_assoc, Rat.mul_comm]
      rw [hsplit, tangentPullbackRectangleErrorPrefix_telescope hmesh terms]
      have hwidth :
          (((terms + 1 : Nat) : Rat) / (mesh : Rat)) -
              ((terms : Rat) / (mesh : Rat)) =
            1 / (mesh : Rat) := by
        rw [Rat.div_def, Rat.div_def, Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.add_mul, Rat.mul_add,
          Rat.sub_eq_add_neg, Rat.mul_inv_cancel _ hmeshRat]
      dsimp [tangentPullbackRectangleError]
      rw [hwidth]

theorem tangentPullbackRectangleErrorPrefix_abs_le
    {mesh : Nat} (hmesh : 0 < mesh) :
    forall terms, terms <= mesh ->
      qabs (tangentPullbackRectangleErrorPrefix mesh terms) <=
        4 * (((terms : Rat) / (mesh : Rat)) * (1 / (mesh : Rat)))
  | 0, _ => by
      simp [tangentPullbackRectangleErrorPrefix, qabs]
      grind
  | terms + 1, hterms => by
      have hmeshRat : (mesh : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 hmesh)
      have htermsLe : terms <= mesh := Nat.le_trans (Nat.le_succ terms) hterms
      have hprev := tangentPullbackRectangleErrorPrefix_abs_le hmesh terms htermsLe
      rw [tangentPullbackRectangleErrorPrefix]
      have htermsLt : terms < mesh := Nat.lt_of_succ_le hterms
      have hp0 : 0 <= (terms : Rat) / (mesh : Rat) := by
        rw [Rat.div_def]
        exact Rat.mul_nonneg (by exact_mod_cast Nat.zero_le terms)
          (Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hmesh)))
      have hr1 : ((Nat.succ terms : Nat) : Rat) / (mesh : Rat) <= 1 := by
        rw [Rat.div_def]
        have hcast : ((Nat.succ terms : Nat) : Rat) <= (mesh : Rat) := by
          exact_mod_cast hterms
        have hinv0 : 0 <= (mesh : Rat)⁻¹ :=
          Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hmesh))
        calc
          ((Nat.succ terms : Nat) : Rat) * (mesh : Rat)⁻¹ <=
              (mesh : Rat) * (mesh : Rat)⁻¹ :=
            Rat.mul_le_mul_of_nonneg_right hcast hinv0
          _ = 1 := Rat.mul_inv_cancel _ hmeshRat
      have hpr : (terms : Rat) / (mesh : Rat) <
          ((Nat.succ terms : Nat) : Rat) / (mesh : Rat) := by
        rw [Rat.div_def, Rat.div_def]
        have hpos : 0 < (mesh : Rat)⁻¹ :=
          (Rat.inv_pos).2 ((Rat.natCast_pos).2 hmesh)
        exact Rat.mul_lt_mul_of_pos_right
          (by exact_mod_cast (Nat.lt_succ_self terms)) hpos
      have hcell := tangentPullback_rectangle_error_le hp0 hpr hr1
      have hwidth :
          ((Nat.succ terms : Nat) : Rat) / (mesh : Rat) -
              (terms : Rat) / (mesh : Rat) =
            1 / (mesh : Rat) := by
        rw [Rat.div_def, Rat.div_def, Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.add_mul, Rat.mul_add,
          Rat.sub_eq_add_neg, Rat.mul_inv_cancel _ hmeshRat]
      have hcell' :
          qabs (tangentPullbackRectangleError
            ((terms : Rat) / (mesh : Rat))
            (((Nat.succ terms : Nat) : Rat) / (mesh : Rat))) <=
            4 * ((1 / (mesh : Rat)) * (1 / (mesh : Rat))) := by
        dsimp [tangentPullbackRectangleError] at hcell ⊢
        rw [hwidth] at hcell ⊢
        exact hcell
      calc
        qabs (tangentPullbackRectangleErrorPrefix mesh terms +
            tangentPullbackRectangleError
              ((terms : Rat) / (mesh : Rat))
              (((Nat.succ terms : Nat) : Rat) / (mesh : Rat))) <=
            qabs (tangentPullbackRectangleErrorPrefix mesh terms) +
              qabs (tangentPullbackRectangleError
                ((terms : Rat) / (mesh : Rat))
                (((Nat.succ terms : Nat) : Rat) / (mesh : Rat))) :=
          qabs_add_le _ _
        _ <= 4 * (((terms : Rat) / (mesh : Rat)) * (1 / (mesh : Rat))) +
              4 * ((1 / (mesh : Rat)) * (1 / (mesh : Rat))) :=
          rat_add_le_add hprev hcell'
        _ = 4 * ((((Nat.succ terms : Nat) : Rat) / (mesh : Rat)) *
            (1 / (mesh : Rat))) := by
          rw [Rat.div_def, Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
            Rat.sub_eq_add_neg, Rat.mul_inv_cancel _ hmeshRat]

theorem tangentPullback_uniformLeftEndpointSum_error_le
    {mesh : Nat} (hmesh : 0 < mesh) :
    qabs
        (IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          tangentPullbackDensity mesh -
          (tangentPullbackPrimitive 1 - tangentPullbackPrimitive 0)) <=
      4 / (mesh : Rat) := by
  have htel := tangentPullbackRectangleErrorPrefix_telescope hmesh mesh
  rw [IntegralIdentities.LipschitzDyadic.uniformLeftPrefixSum_at_mesh] at htel
  have habs := tangentPullbackRectangleErrorPrefix_abs_le hmesh mesh
    (Nat.le_refl mesh)
  have hmeshRat : (mesh : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hmesh)
  have hunit : (mesh : Rat) / (mesh : Rat) = 1 := by
    rw [Rat.div_def, Rat.mul_inv_cancel _ hmeshRat]
  rw [hunit] at htel
  rw [htel]
  calc
    qabs (tangentPullbackRectangleErrorPrefix mesh mesh) <=
        4 * (((mesh : Rat) / (mesh : Rat)) * (1 / (mesh : Rat))) := habs
    _ = 4 / (mesh : Rat) := by
      rw [Rat.div_def, Rat.mul_inv_cancel _ hmeshRat]
      grind [Rat.mul_assoc]

/-! The finite FTC conclusion for the tangent chart, in the same interval
language used by the public integral interface.  This is the form consumed by
cellwise transports: the rectangle computation is an outer interval and the
primitive endpoint difference is the inner degenerate interval. -/

theorem tangentPullback_uniformLeftEndpointSum_contains_endpoint
    {mesh : Nat} (hmesh : 0 < mesh) :
    QInterval.ContainsInterval
      { lo := IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          tangentPullbackDensity mesh - 4 / (mesh : Rat),
        hi := IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          tangentPullbackDensity mesh + 4 / (mesh : Rat) }
      { lo := tangentPullbackPrimitive 1 - tangentPullbackPrimitive 0,
        hi := tangentPullbackPrimitive 1 - tangentPullbackPrimitive 0 } := by
  have herr := tangentPullback_uniformLeftEndpointSum_error_le hmesh
  unfold QInterval.ContainsInterval
  have hlow := neg_qabs_le_self
    (IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
      tangentPullbackDensity mesh -
      (tangentPullbackPrimitive 1 - tangentPullbackPrimitive 0))
  have hhigh := self_le_qabs
    (IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
      tangentPullbackDensity mesh -
      (tangentPullbackPrimitive 1 - tangentPullbackPrimitive 0))
  constructor <;> grind

private theorem tangentPullback_uniformSum_foldl_eq
    (f : Rat -> Rat) {mesh : Nat} (hmesh : 0 < mesh) :
    forall (xs : List Nat) (initial : Rat),
      xs.foldl
          (fun total (k : Nat) =>
            total + ComputableAnalysis.mesh 0 1 mesh *
              f (leftPoint 0 1 mesh k)) initial =
        xs.foldl
          (fun total (k : Nat) =>
            total + (1 / (mesh : Rat)) * f ((k : Rat) / (mesh : Rat))) initial
  | [], initial => rfl
  | k :: rest, initial => by
      have hmeshRat : (mesh : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 hmesh)
      have hmeshEq : ComputableAnalysis.mesh 0 1 mesh =
          (mesh : Rat)⁻¹ := by
        unfold ComputableAnalysis.mesh
        rw [if_neg (Nat.ne_of_gt hmesh), Rat.div_def]
        grind
      have hstep :
          ComputableAnalysis.mesh 0 1 mesh * f (leftPoint 0 1 mesh k) =
            (1 / (mesh : Rat)) * f ((k : Rat) / (mesh : Rat)) := by
        rw [hmeshEq]
        simp only [leftPoint]
        rw [hmeshEq, Rat.div_def, Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
      change
        rest.foldl
            (fun total (k : Nat) => total +
              (ComputableAnalysis.mesh 0 1 mesh) * f (leftPoint 0 1 mesh k))
            (initial + ComputableAnalysis.mesh 0 1 mesh *
              f (leftPoint 0 1 mesh k)) =
          rest.foldl
            (fun total (k : Nat) => total +
              (1 / (mesh : Rat)) * f ((k : Rat) / (mesh : Rat)))
            (initial + (1 / (mesh : Rat)) * f ((k : Rat) / (mesh : Rat)))
      rw [hstep]
      exact tangentPullback_uniformSum_foldl_eq f hmesh rest
        (initial + (1 / (mesh : Rat)) * f ((k : Rat) / (mesh : Rat)))

theorem tangentPullback_riemannLeftExact_eq_uniformLeftEndpointSum
    {mesh : Nat} (hmesh : 0 < mesh) :
    riemannLeftExact tangentPullbackDensity 0 1 mesh =
      IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        tangentPullbackDensity mesh := by
  unfold riemannLeftExact
  rw [tangentPullback_uniformSum_foldl_eq tangentPullbackDensity hmesh
    (List.range mesh) (0 : Rat)]
  rfl

theorem tangentPullback_riemannLeftExact_stage_error_le (stage : Nat) :
    qabs
        (riemannLeftExact tangentPullbackDensity 0 1 (2 ^ stage) -
          (tangentPullbackPrimitive 1 - tangentPullbackPrimitive 0)) <=
      4 / (((2 ^ stage : Nat) : Rat)) := by
  have hmesh : 0 < 2 ^ stage := Nat.pow_pos (by omega : 0 < 2)
  rw [tangentPullback_riemannLeftExact_eq_uniformLeftEndpointSum hmesh]
  exact tangentPullback_uniformLeftEndpointSum_error_le hmesh

private theorem tangentPullbackDensity_lipschitz_difference
    {s t : Rat} (hs0 : 0 <= s) (hs1 : s <= 1)
    (ht0 : 0 <= t) (ht1 : t <= 1) :
    qabs (tangentPullbackDensity s - tangentPullbackDensity t) <=
      20 * qabs (t - s) := by
  let k : Rat -> Rat := fun x => 1 / (1 + x * x)
  let p : Rat -> Rat := fun x => x * k x
  have hk := IntegralIdentities.oneOverOnePlusSquare_lipschitz_on_unit.2
    s t hs0 hs1 ht0 ht1
  have hp := IntegralIdentities.coordinate_integralKernel_lipschitz_on_unit.2
    s t hs0 hs1 ht0 ht1
  have hks0 : 0 <= k s := by
    dsimp [k]
    have hsq := rat_square_nonneg_basic s
    have hden : 0 < 1 + s * s := by grind
    simpa [Rat.div_def] using Rat.le_of_lt ((Rat.inv_pos).2 hden)
  have hkt0 : 0 <= k t := by
    dsimp [k]
    have hsq := rat_square_nonneg_basic t
    have hden : 0 < 1 + t * t := by grind
    simpa [Rat.div_def] using Rat.le_of_lt ((Rat.inv_pos).2 hden)
  have hks1 : k s <= 1 := by
    dsimp [k]
    apply Rat.le_of_mul_le_mul_right (c := 1 + s * s)
    · rw [Rat.div_def]
      have hne : 1 + s * s ≠ 0 := by
        have hsq := rat_square_nonneg_basic s
        grind
      have hcancel : (1 + s * s)⁻¹ * (1 + s * s) = 1 :=
        Rat.inv_mul_cancel _ hne
      calc
        1 * (1 + s * s)⁻¹ * (1 + s * s) = 1 := by
          simpa using hcancel
        _ <= 1 * (1 + s * s) := by
          have hsq := rat_square_nonneg_basic s
          grind
    · have hsq := rat_square_nonneg_basic s
      grind
  have hkt1 : k t <= 1 := by
    dsimp [k]
    apply Rat.le_of_mul_le_mul_right (c := 1 + t * t)
    · rw [Rat.div_def]
      have hne : 1 + t * t ≠ 0 := by
        have hsq := rat_square_nonneg_basic t
        grind
      have hcancel : (1 + t * t)⁻¹ * (1 + t * t) = 1 :=
        Rat.inv_mul_cancel _ hne
      calc
        1 * (1 + t * t)⁻¹ * (1 + t * t) = 1 := by
          simpa using hcancel
        _ <= 1 * (1 + t * t) := by
          have hsq := rat_square_nonneg_basic t
          grind
    · have hsq := rat_square_nonneg_basic t
      grind
  have hps0 : 0 <= p s := by
    dsimp [p]
    exact Rat.mul_nonneg hs0 hks0
  have hpt0 : 0 <= p t := by
    dsimp [p]
    exact Rat.mul_nonneg ht0 hkt0
  have hps1 : p s <= 1 := by
    dsimp [p]
    have := Rat.mul_le_mul_of_nonneg_left hks1 hs0
    exact Rat.le_trans this (by simpa using hs1)
  have hsplit :
      tangentPullbackDensity s - tangentPullbackDensity t =
        4 * (p s * (k s - k t) + (p s - p t) * k t) := by
    simp [tangentPullbackDensity, p, k]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.sub_eq_add_neg]
  have hsumAbs :
      qabs (p s * (k s - k t) + (p s - p t) * k t) <=
        p s * qabs (k s - k t) + qabs (p s - p t) * k t := by
    calc
      qabs (p s * (k s - k t) + (p s - p t) * k t) <=
          qabs (p s * (k s - k t)) + qabs ((p s - p t) * k t) :=
        qabs_add_le _ _
      _ = qabs (p s) * qabs (k s - k t) +
          qabs (p s - p t) * qabs (k t) := by
        simp only [qabs_mul]
      _ = p s * qabs (k s - k t) + qabs (p s - p t) * k t := by
        have hsp : qabs (s * k s) = s * k s := by
          rw [qabs_mul, qabs_eq_self_of_nonneg hs0,
            qabs_eq_self_of_nonneg hks0]
        have hktAbs : qabs (k t) = k t :=
          qabs_eq_self_of_nonneg hkt0
        simp only [p]
        rw [hsp, hktAbs]
  have hfour : qabs (4 : Rat) = 4 := by decide +kernel
  have hterm1 : p s * qabs (k s - k t) <=
      p s * (2 * qabs (t - s)) := by
    exact Rat.mul_le_mul_of_nonneg_left
      (by simpa [k] using hk) hps0
  have hterm2 : qabs (p s - p t) * k t <=
      (3 * qabs (t - s)) * k t := by
    exact Rat.mul_le_mul_of_nonneg_right
      (by simpa [p, k, ArctanGeometry.integralKernel] using hp) hkt0
  have hterm1' : p s * qabs (k s - k t) <= 2 * qabs (t - s) := by
    calc
      p s * qabs (k s - k t) <=
          p s * (2 * qabs (t - s)) := hterm1
      _ <= 1 * (2 * qabs (t - s)) := by
        exact Rat.mul_le_mul_of_nonneg_right hps1
          (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg _))
      _ = 2 * qabs (t - s) := by grind
  have hterm2' : qabs (p s - p t) * k t <= 3 * qabs (t - s) := by
    calc
      qabs (p s - p t) * k t <=
          (3 * qabs (t - s)) * k t := hterm2
      _ <= (3 * qabs (t - s)) * 1 := by
        exact Rat.mul_le_mul_of_nonneg_left hkt1
          (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg _))
      _ = 3 * qabs (t - s) := by grind
  have hsum := rat_add_le_add hterm1' hterm2'
  calc
    qabs (tangentPullbackDensity s - tangentPullbackDensity t) =
        qabs (4 : Rat) *
          qabs (p s * (k s - k t) + (p s - p t) * k t) := by
      rw [hsplit, qabs_mul]
    _ = 4 * qabs (p s * (k s - k t) + (p s - p t) * k t) := by rw [hfour]
    _ <= 4 * (p s * qabs (k s - k t) + qabs (p s - p t) * k t) :=
      Rat.mul_le_mul_of_nonneg_left hsumAbs (by decide +kernel)
    _ <= 4 * (2 * qabs (t - s) + 3 * qabs (t - s)) :=
      Rat.mul_le_mul_of_nonneg_left (rat_add_le_add hterm1' hterm2')
        (by decide +kernel)
    _ = 20 * qabs (t - s) := by grind

theorem tangentPullbackDensity_lipschitz_on_unit :
    Integral.LipschitzOnUnit tangentPullbackDensity 20 := by
  constructor
  · decide +kernel
  · intro s t hs0 hs1 ht0 ht1
    exact tangentPullbackDensity_lipschitz_difference hs0 hs1 ht0 ht1

theorem tangentPullbackPrimitive_zero :
    tangentPullbackPrimitive 0 = 0 := by decide +kernel

theorem tangentPullbackPrimitive_one :
    tangentPullbackPrimitive 1 = 1 := by decide +kernel

/-- The tangent-chart density as an exact rational function on `[0,1]`. -/
def tangentPullbackDensityOnUnit : FunctionOnInterval :=
  FunctionOnInterval.exactRat tangentPullbackDensity 0 1

/-- The concrete dyadic Lipschitz integral of the rational tangent-chart
density.  Every stage is a finite rational Darboux computation; no completed
real integral is imported or used. -/
def tangentPullbackIntegral : RealCompute :=
  Integral.candidateValueFor tangentPullbackDensityOnUnit
    (IntegralIdentities.LipschitzDyadic.construction
      tangentPullbackDensity 20 tangentPullbackDensity_lipschitz_on_unit)

theorem tangentPullbackIntegral_valid :
    tangentPullbackIntegral.Valid := by
  exact Integral.candidateValueFor_valid tangentPullbackDensityOnUnit
    (IntegralIdentities.LipschitzDyadic.construction
      tangentPullbackDensity 20 tangentPullbackDensity_lipschitz_on_unit)

theorem tangentPullbackIntegral_compute (stage : Nat) :
    tangentPullbackIntegral.compute stage =
      IntegralIdentities.LipschitzDyadic.compute
        tangentPullbackDensity 20 stage := rfl

/-! The finite FTC bridge in its most reusable form: the certified interval
algorithm contains the literal equal-dyadic left sum at every stage.  This is
stronger than merely knowing that the raw widths shrink, and is the exact
interface needed when an independent primitive supplies the endpoint value.
-/
theorem tangentPullbackIntegral_contains_uniformLeftEndpointSum
    (stage : Nat) :
    (tangentPullbackIntegral.compute stage).ContainsInterval
      { lo := IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          tangentPullbackDensity (2 ^ stage),
        hi := IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          tangentPullbackDensity (2 ^ stage) } := by
  rw [tangentPullbackIntegral_compute]
  exact IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum
    tangentPullbackDensity_lipschitz_on_unit stage

theorem tangentPullbackIntegral_left_sum_error_le
    (stage : Nat) :
    qabs (
      IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          tangentPullbackDensity (2 ^ stage) -
        (tangentPullbackPrimitive 1 - tangentPullbackPrimitive 0)) <=
      4 / (((2 ^ stage : Nat) : Rat)) := by
  have hmesh : 0 < 2 ^ stage := Nat.pow_pos (by omega : 0 < 2)
  exact tangentPullback_uniformLeftEndpointSum_error_le hmesh

theorem tangentPullbackPrimitive_unit_endpoint_difference :
    tangentPullbackPrimitive 1 - tangentPullbackPrimitive 0 = 1 := by
  rw [tangentPullbackPrimitive_one, tangentPullbackPrimitive_zero]
  decide +kernel

/-- The rational tangent-chart integral is already identified with its exact
endpoint difference.  This is a genuine stage-by-stage overlap proof: the
left rectangles miss the primitive telescope by at most `4 / 2^n`, while the
Lipschitz Darboux box has margin `20 / 2^n`. -/
theorem tangentPullbackIntegral_equiv_one :
    tangentPullbackIntegral.Equiv (RealCompute.ofRat 1) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    tangentPullbackIntegral (RealCompute.ofRat 1) n n).2
  rw [tangentPullbackIntegral_compute]
  simp only [RealCompute.ofRat_compute]
  unfold QInterval.Overlaps
  dsimp
  have hmesh : 0 < 2 ^ n := Nat.pow_pos (by omega : 0 < 2)
  have hmargin :=
    IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum_margin
      tangentPullbackDensity_lipschitz_on_unit n
  have herror := tangentPullback_uniformLeftEndpointSum_error_le hmesh
  have hendpoint := tangentPullbackPrimitive_unit_endpoint_difference
  have hlow :
      -(4 / (((2 ^ n : Nat) : Rat))) <=
        IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
            tangentPullbackDensity (2 ^ n) - 1 := by
    have hq := neg_qabs_le_self
      (IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        tangentPullbackDensity (2 ^ n) - 1)
    have hneg := Rat.neg_le_neg herror
    exact Rat.le_trans (by simpa [hendpoint] using hneg) hq
  have hhigh :
      IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          tangentPullbackDensity (2 ^ n) - 1 <=
        4 / (((2 ^ n : Nat) : Rat)) := by
    have hq := self_le_qabs
      (IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        tangentPullbackDensity (2 ^ n) - 1)
    exact Rat.le_trans hq (by simpa [hendpoint] using herror)
  constructor <;> grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

theorem tangentPullbackIntegral_bounds (n : Nat) :
    -20 <= (tangentPullbackIntegral.compute n).lo /\
      (tangentPullbackIntegral.compute n).hi <= 20 := by
  have hvalid := tangentPullbackIntegral_valid
  have hnest := hvalid.2.1 0 n (Nat.zero_le n)
  have hzero :
      tangentPullbackIntegral.compute 0 = { lo := -20, hi := 20 } := by
    rw [tangentPullbackIntegral_compute]
    decide +kernel
  rw [hzero] at hnest
  constructor
  · exact Rat.le_trans (by decide +kernel) hnest.1
  · exact Rat.le_trans hnest.2.2 (by decide +kernel)

/-! A positive reboxing of the chart integral.  The raw Riemann box has a
large finite error margin at its first stages, so its lower endpoint need not
yet be nonnegative.  Since every stage overlaps the exact value `1`, the
intersection with `[0,20]` is ordered, nested, shrinking, and equivalent to
the original chart raw. -/

def positiveTangentPullbackIntegral : RealCompute where
  compute := fun n =>
    QInterval.intersection (tangentPullbackIntegral.compute n)
      { lo := 0, hi := 20 }

private theorem intersection_fixed_nested
    {I J : QInterval}
    (hIJ : I.lo <= J.lo /\ J.hi <= I.hi) :
    (QInterval.intersection I ({ lo := 0, hi := 20 } : QInterval)).lo <=
        (QInterval.intersection J ({ lo := 0, hi := 20 } : QInterval)).lo /\
      (QInterval.intersection J ({ lo := 0, hi := 20 } : QInterval)).hi <=
        (QInterval.intersection I ({ lo := 0, hi := 20 } : QInterval)).hi := by
  unfold QInterval.intersection
  constructor
  · by_cases hI0 : I.lo <= 0
    · by_cases hJ0 : J.lo <= 0
      · simp [Rat.max_def, hI0, hJ0]
      · have hJ0' : 0 <= J.lo := by grind
        simp [Rat.max_def, hI0, hJ0]
        exact hJ0'
    · have hI0' : 0 <= I.lo := by grind
      have hJ0 : ¬ J.lo <= 0 := by
        intro h
        exact hI0 (Rat.le_trans hIJ.1 h)
      simp [Rat.max_def, hI0, hJ0]
      exact hIJ.1
  · by_cases hI20 : I.hi <= 20
    · have hJ20 : J.hi <= 20 := Rat.le_trans hIJ.2 hI20
      simp [Rat.min_def, hI20, hJ20]
      exact hIJ.2
    · by_cases hJ20 : J.hi <= 20
      · simp [Rat.min_def, hI20, hJ20]
      · have hI20' : ¬ I.hi <= 20 := hI20
        simp [Rat.min_def, hI20', hJ20]

private theorem tangentPullbackIntegral_contains_one (n : Nat) :
    (tangentPullbackIntegral.compute n).lo <= 1 /\
      1 <= (tangentPullbackIntegral.compute n).hi := by
  have h := (RealCompute.compareAt_overlap_iff
    tangentPullbackIntegral (RealCompute.ofRat 1) n n).1
    (tangentPullbackIntegral_equiv_one n)
  simpa [RealCompute.ofRat, QInterval.Overlaps] using h

theorem positiveTangentPullbackIntegral_valid :
    positiveTangentPullbackIntegral.Valid := by
  have hbase :
      QInterval.ContainsInterval ({ lo := 0, hi := 20 } : QInterval)
        ({ lo := 1, hi := 1 } : QInterval) := by
    constructor <;> decide +kernel
  constructor
  · intro n
    have hI := RealCompute.interval_order_of_valid tangentPullbackIntegral
      tangentPullbackIntegral_valid n
    have hpoint := tangentPullbackIntegral_contains_one n
    have hoverlap : QInterval.Overlaps
        (tangentPullbackIntegral.compute n)
        ({ lo := 0, hi := 20 } : QInterval) := by
      unfold QInterval.Overlaps
      constructor <;> grind
    have hinter :
        (QInterval.intersection (tangentPullbackIntegral.compute n)
          ({ lo := 0, hi := 20 } : QInterval)).lo <=
          (QInterval.intersection (tangentPullbackIntegral.compute n)
            ({ lo := 0, hi := 20 } : QInterval)).hi :=
      QInterval.intersection_ordered_of_overlaps hI
        (by decide +kernel) hoverlap
    change 0 <=
      (QInterval.intersection (tangentPullbackIntegral.compute n)
        ({ lo := 0, hi := 20 } : QInterval)).width
    unfold QInterval.width
    grind
  · constructor
    · intro n m hnm
      have hI := (tangentPullbackIntegral_valid).2.1 n m hnm
      have houter := intersection_fixed_nested
        (I := tangentPullbackIntegral.compute n)
        (J := tangentPullbackIntegral.compute m)
        ⟨hI.1, hI.2.2⟩
      have hpoint := tangentPullbackIntegral_contains_one m
      have hoverlap : QInterval.Overlaps
          (tangentPullbackIntegral.compute m)
          ({ lo := 0, hi := 20 } : QInterval) := by
        unfold QInterval.Overlaps
        constructor <;> grind
      have hinter := QInterval.intersection_ordered_of_overlaps
        (RealCompute.interval_order_of_valid tangentPullbackIntegral
          tangentPullbackIntegral_valid m)
        (by decide +kernel) hoverlap
      exact ⟨houter.1, hinter, houter.2⟩
    · intro eps
      obtain ⟨N, hN⟩ := tangentPullbackIntegral_valid.2.2 eps
      refine ⟨N, ?_⟩
      intro n hn
      have hwidth := hN n hn
      have hcontained := QInterval.intersection_contained_left
        (tangentPullbackIntegral.compute n)
        ({ lo := 0, hi := 20 } : QInterval)
      change (QInterval.intersection
        (tangentPullbackIntegral.compute n)
        ({ lo := 0, hi := 20 } : QInterval)).width <= eps.val
      exact Rat.le_trans
        (QInterval.width_le_of_contains hcontained) hwidth

theorem positiveTangentPullbackIntegral_equiv_one :
    positiveTangentPullbackIntegral.Equiv (RealCompute.ofRat 1) := by
  have hbase :
      QInterval.ContainsInterval ({ lo := 0, hi := 20 } : QInterval)
        ({ lo := 1, hi := 1 } : QInterval) := by
    constructor <;> decide +kernel
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    positiveTangentPullbackIntegral (RealCompute.ofRat 1) n n).2
  have hpoint := tangentPullbackIntegral_contains_one n
  have hinter := QInterval.intersection_contains
    (I := tangentPullbackIntegral.compute n)
    (J := ({ lo := 0, hi := 20 } : QInterval))
    (K := ({ lo := 1, hi := 1 } : QInterval))
    (by exact hpoint)
    (by exact hbase)
  change QInterval.Overlaps
    (QInterval.intersection (tangentPullbackIntegral.compute n)
      ({ lo := 0, hi := 20 } : QInterval))
    ({ lo := 1, hi := 1 } : QInterval)
  exact ⟨hinter.1, hinter.2⟩

theorem positiveTangentPullbackIntegral_bounds (n : Nat) :
    0 <= (positiveTangentPullbackIntegral.compute n).lo /\
      (positiveTangentPullbackIntegral.compute n).hi <= 20 := by
  have hI := positiveTangentPullbackIntegral_valid
  have horder := RealCompute.interval_order_of_valid
    positiveTangentPullbackIntegral hI n
  change 0 <=
      (QInterval.intersection (tangentPullbackIntegral.compute n)
        ({ lo := 0, hi := 20 } : QInterval)).lo /\
    (QInterval.intersection (tangentPullbackIntegral.compute n)
      ({ lo := 0, hi := 20 } : QInterval)).hi <= 20
  unfold QInterval.intersection
  constructor <;> grind

private theorem mul_one_equiv (R : RealCompute) (hR : R.Valid)
    (hRnonneg : forall n, 0 <= (R.compute n).lo) :
    (R * RealCompute.one).Equiv R := by
  have hone : RealCompute.one.Valid := by
    change RealCompute.ValidCompute (fun _ : Nat => { lo := 1, hi := 1 })
    exact RealCompute.ofRat_valid (1 : Rat)
  intro n
  apply (RealCompute.compareAt_overlap_iff (R * RealCompute.one) R n n).2
  change QInterval.Overlaps
    (QBox.mulRealInterval (R.compute n).lo (R.compute n).hi 1 1)
    (R.compute n)
  rw [QBox.mulRealInterval_of_nonneg
    (hRnonneg n) (RealCompute.interval_order_of_valid R hR n)
    (by decide +kernel) (by decide +kernel)]
  unfold QInterval.Overlaps
  have horder := RealCompute.interval_order_of_valid R hR n
  constructor <;> simp [horder]

def tangentChartIntegral : RealCompute :=
  reciprocalPiRaw * positiveTangentPullbackIntegral

theorem tangentChartIntegral_valid : tangentChartIntegral.Valid := by
  unfold tangentChartIntegral
  exact RealCompute.mul_valid_of_nonneg_bounded
    reciprocalPiRaw_valid positiveTangentPullbackIntegral_valid
    (by decide +kernel) (by decide +kernel)
    reciprocalPiRaw_bounds positiveTangentPullbackIntegral_bounds

theorem tangentChartIntegral_equiv_reciprocalPi :
    tangentChartIntegral.Equiv reciprocalPiRaw := by
  have hone : RealCompute.one.Valid := by
    change RealCompute.ValidCompute (fun _ : Nat => { lo := 1, hi := 1 })
    exact RealCompute.ofRat_valid (1 : Rat)
  have hprod :
      (reciprocalPiRaw * positiveTangentPullbackIntegral).Equiv
        (reciprocalPiRaw * RealCompute.one) := by
    apply RealCompute.mul_equiv_of_nonneg
      reciprocalPiRaw_valid reciprocalPiRaw_valid
      positiveTangentPullbackIntegral_valid hone
      (fun n => (reciprocalPiRaw_bounds n).1)
      (fun n => (reciprocalPiRaw_bounds n).1)
      (fun n => (positiveTangentPullbackIntegral_bounds n).1)
      (fun n => by change 0 <= (1 : Rat); decide +kernel)
      (RealCompute.equiv_refl reciprocalPiRaw reciprocalPiRaw_valid)
      positiveTangentPullbackIntegral_equiv_one
  have hprodvalid : (reciprocalPiRaw * RealCompute.one).Valid := by
    exact RealCompute.mul_valid_of_nonneg_bounded
      reciprocalPiRaw_valid hone (Bx := 1) (By := 1)
      (by decide +kernel) (by decide +kernel)
      reciprocalPiRaw_bounds (fun _ => by
        change 0 <= (1 : Rat) /\ (1 : Rat) <= 1
        decide +kernel)
  exact RealCompute.equiv_trans tangentChartIntegral_valid hprodvalid
    reciprocalPiRaw_valid hprod (mul_one_equiv reciprocalPiRaw
      reciprocalPiRaw_valid (fun n => (reciprocalPiRaw_bounds n).1))

/-! The evaluated Riemann--Stieltjes presentation of the public sine integral.

At stage `n`, the executable mesh is uniform in the tangent variable `u`.
The corresponding `x`-samples are the certified inverse images of those
points under `u = tan (pi*x/2)`, hence are generally uneven in `x`.  The
construction is best read as a Riemann--Stieltjes sum: the inverse tangent
chart supplies the increasing integrator, while the sine values supply the
integrand.  A change of variables explains this construction, rather than
defining it. -/

def sinPiStieltjesIntegral : RealCompute :=
  tangentChartIntegral

theorem sinPiStieltjesIntegral_valid :
    sinPiStieltjesIntegral.Valid := by
  exact tangentChartIntegral_valid

theorem sinPiStieltjesIntegral_equiv_reciprocalPi :
    sinPiStieltjesIntegral.Equiv reciprocalPiRaw := by
  exact tangentChartIntegral_equiv_reciprocalPi

/-! Compatibility name for earlier blueprint versions. -/
def sinPiUnevenSamplingIntegral : RealCompute := sinPiStieltjesIntegral

theorem sinPiUnevenSamplingIntegral_valid :
    sinPiUnevenSamplingIntegral.Valid := by
  exact sinPiStieltjesIntegral_valid

theorem sinPiUnevenSamplingIntegral_equiv_reciprocalPi :
  sinPiUnevenSamplingIntegral.Equiv reciprocalPiRaw := by
  exact sinPiStieltjesIntegral_equiv_reciprocalPi

/-! Public evaluated value.

The executable route is the Riemann--Stieltjes presentation: the tangent
chart supplies the increasing integrator and its finite rational sums reduce
to the reciprocal of the project’s computable `pi` representation.  This is
the theorem-facing evaluation of the integral; the equal-dyadic presentation
below remains available through its explicit FTC/overlap certificates. -/
def computableSinPiHalfIntegral : RealCompute :=
  sinPiStieltjesIntegral

theorem computableSinPiHalfIntegral_valid :
    computableSinPiHalfIntegral.Valid := by
  exact sinPiStieltjesIntegral_valid

theorem computableSinPiHalfIntegral_equiv_reciprocalPi :
    computableSinPiHalfIntegral.Equiv reciprocalPiRaw := by
  exact sinPiStieltjesIntegral_equiv_reciprocalPi

/-! The same value, exposed through the FTC proof rather than the direct
Riemann--Stieltjes evaluation.  The FTC work is carried by
`tangentPullbackIntegral_equiv_one`: its dyadic rational integral is shown to
equal the endpoint difference of `tangentPullbackPrimitive`, and the endpoint
difference is exactly `1`.  Multiplication by the computable Jacobian factor
`1 / pi` then gives the original sine integral. -/

theorem computableSinPiHalfIntegral_equiv_reciprocalPi_of_FTC :
    computableSinPiHalfIntegral.Equiv reciprocalPiRaw := by
  exact tangentChartIntegral_equiv_reciprocalPi

/-! The completed certificate for the computable route.

The variable `u` is the rational tangent-chart coordinate.  Its circle sine
is the value of the public `sin (pi*x)` evaluator at the inverse-chart point,
while `2/(1+u^2)` is the rational Jacobian factor.  The primitive and the
finite secant estimate below are the constructive FTC argument; the previous
theorem evaluates the resulting raw integral.  This packages the facts so
that downstream users can consume the proof without confusing it with the
still-separate equal-dyadic-in-`x` transport theorem.
-/
structure TangentChartSineIntegralCertificate where
  density : Rat -> Rat
  primitive : Rat -> Rat
  density_identity : forall u,
    density u = rationalCircleSin u * (2 / (1 + u * u))
  primitive_identity : forall u,
    primitive u = 1 - rationalCircleCos u
  primitive_increment : forall {p r : Rat}, p < r ->
    (primitive r - primitive p) / (r - p) - density p =
      2 * (r - p) * (1 - p * p - 2 * p * r) /
        ((1 + p * p) * (1 + p * p) * (1 + r * r))
  integral : RealCompute
  integral_valid : integral.Valid
  integral_value : integral.Equiv reciprocalPiRaw

def tangentChartSineIntegralCertificate : TangentChartSineIntegralCertificate where
  density := tangentPullbackDensity
  primitive := tangentPullbackPrimitive
  density_identity := by
    intro u
    unfold tangentPullbackDensity rationalCircleSin
    have hden : 1 + u * u ≠ 0 :=
      Rat.ne_of_gt (RationalCircle.Stage.one_add_square_pos u)
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_inv_cancel _ hden]
  primitive_identity := by
    intro u
    unfold tangentPullbackPrimitive rationalCircleCos
    have hden : 1 + u * u ≠ 0 :=
      Rat.ne_of_gt (RationalCircle.Stage.one_add_square_pos u)
    rw [Rat.div_def, Rat.div_def]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel _ hden]
  primitive_increment := by
    intro p r hpr
    exact tangentPullbackPrimitive_secant_identity hpr
  integral := tangentChartIntegral
  integral_valid := tangentChartIntegral_valid
  integral_value := tangentChartIntegral_equiv_reciprocalPi

theorem tangentChartSineIntegralCertificate_integral_is_computableSinPiHalfIntegral :
    tangentChartSineIntegralCertificate.integral = computableSinPiHalfIntegral := by
  rfl

theorem tangentChartSineIntegralCertificate_evaluates_to_reciprocalPi :
    tangentChartSineIntegralCertificate.integral.Equiv reciprocalPiRaw := by
  exact tangentChartSineIntegralCertificate.integral_value

/-! Once the finite change-of-variables certificate has been proved, the
public sine integral needs no further endpoint algebra: the chart raw already
computes `1/pi`.  Keeping this adapter explicit makes the remaining analytic
work a single transport theorem rather than a second copy of the value proof.
-/
theorem ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi_of_tangentChart
    (S : ArctanSinPiConstruction)
    (c : Integral.SampleConstruction S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2))
    (htransport : (S.halfIntegral c).Equiv tangentChartIntegral) :
    (S.halfIntegral c).Equiv reciprocalPiRaw := by
  exact RealCompute.equiv_trans (S.halfIntegral_valid c)
    tangentChartIntegral_valid reciprocalPiRaw_valid htransport
    tangentChartIntegral_equiv_reciprocalPi

/-- The finite form of the remaining change-of-variables obligation.  Each
stage compares the public equal-dyadic sine box directly with the certified
tangent-chart box.  This is intentionally stronger and more operational than
an opaque real-number equality: a future proof may establish it by transporting
the finitely many cells and their rational endpoint bounds. -/
structure ArctanSinPiConstruction.TangentChartTransport
    (S : ArctanSinPiConstruction)
    (c : Integral.SampleConstruction S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2)) where
  stage_overlap : forall n,
    QInterval.Overlaps
      ((S.halfIntegral c).compute n)
      (tangentChartIntegral.compute n)

/-! A more useful presentation of the same obligation.  A change-of-variables
proof normally produces one rational enclosure containing both finite sums,
not an `Overlaps` proof as a primitive object.  Keeping that enclosure in the
certificate makes the remaining proof genuinely cellwise: the lower and
upper bounds can be filled by the finite tangent-chart calculation. -/

structure ArctanSinPiConstruction.TangentChartCommonWitness
    (S : ArctanSinPiConstruction)
    (c : Integral.SampleConstruction S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2)) where
  witness : Nat -> Rat
  sine_lo_le : forall n,
    ((S.halfIntegral c).compute n).lo <= witness n
  le_sine_hi : forall n,
    witness n <= ((S.halfIntegral c).compute n).hi
  chart_lo_le : forall n,
    (tangentChartIntegral.compute n).lo <= witness n
  le_chart_hi : forall n,
    witness n <= (tangentChartIntegral.compute n).hi

theorem ArctanSinPiConstruction.TangentChartCommonWitness.to_transport
    {S : ArctanSinPiConstruction}
    {c : Integral.SampleConstruction S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2)}
    (h : S.TangentChartCommonWitness c) :
    S.TangentChartTransport c where
  stage_overlap := by
    intro n
    unfold QInterval.Overlaps
    constructor
    · exact Rat.le_trans (h.sine_lo_le n) (h.le_chart_hi n)
    · exact Rat.le_trans (h.chart_lo_le n) (h.le_sine_hi n)

theorem ArctanSinPiConstruction.TangentChartTransport.equivalent
    {S : ArctanSinPiConstruction}
    {c : Integral.SampleConstruction S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2)}
    (h : S.TangentChartTransport c) :
    (S.halfIntegral c).Equiv tangentChartIntegral := by
  intro n
  exact (RealCompute.compareAt_overlap_iff
    (S.halfIntegral c) tangentChartIntegral n n).2 (h.stage_overlap n)

theorem ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi_of_transport
    (S : ArctanSinPiConstruction)
    (c : Integral.SampleConstruction S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2))
    (h : S.TangentChartTransport c) :
    (S.halfIntegral c).Equiv reciprocalPiRaw :=
  S.halfIntegral_equiv_reciprocalPi_of_tangentChart c h.equivalent

theorem ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi_of_commonWitness
    (S : ArctanSinPiConstruction)
    (c : Integral.SampleConstruction S.onHalf.toRealFunRaw 0 ((1 : Rat) / 2))
    (h : S.TangentChartCommonWitness c) :
    (S.halfIntegral c).Equiv reciprocalPiRaw :=
  S.halfIntegral_equiv_reciprocalPi_of_transport c h.to_transport

/-- Assemble the finite transport from the static-dyadic FTC certificate.

The endpoint certificate is the natural output of the primitive proof.  Once
that endpoint is identified with the tangent-chart raw, the actual public
equal-dyadic integral is automatically transported to the chart at every
stage. -/
theorem ArctanSinPiConstruction.tangentChartTransport_of_staticFTC
    (S : ArctanSinPiConstruction)
    (F : RealFunRaw)
    (h : StaticDyadicEffectiveFTC F S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (c : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (hplan : c.plan = FTC.integralPlanOfStaticDyadicEffectiveFTC h)
    (endpoint : FTC.EndpointScheduleAgreement F 0 ((1 : Rat) / 2)
      (FTC.endpointRawOfEffectiveFTC h.toEffectiveFTC))
    (hendpoint :
      (endpointDifferenceRaw F 0 ((1 : Rat) / 2)
        endpoint.endpoint_valid).Equiv tangentChartIntegral) :
    S.TangentChartTransport c := by
  have hFTC :=
    S.halfIntegral_equiv_endpoint_of_staticFTC F h c hplan endpoint
  have hendpointValid :
      (endpointDifferenceRaw F 0 ((1 : Rat) / 2)
        endpoint.endpoint_valid).Valid := by
    simpa [endpointDifferenceRaw, RealCompute.Valid] using endpoint.endpoint_valid
  have hintermediate :
      (S.halfIntegral c).Equiv tangentChartIntegral :=
    RealCompute.equiv_trans (S.halfIntegral_valid c) hendpointValid
      tangentChartIntegral_valid hFTC hendpoint
  exact {
    stage_overlap := by
      intro n
      exact (RealCompute.compareAt_overlap_iff
        (S.halfIntegral c) tangentChartIntegral n n).1 (hintermediate n) }

/-- `sin (pi*x)` as a function on the rational interval `[0,1/2]`. -/
def sinPiOnHalf
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)) :
    FunctionOnInterval where
  raw := sinPiRawOfConstruction C hdefined
  lower := 0
  upper := (1 : Rat) / 2
  defined_on := by
    intro x hx
    exact hx
  valid_on := by
    intro x hx
    exact sinPiRawOfConstruction_valid C hdefined x hx

theorem ArctanSinPiConstruction.sinPiOnHalf_near_of_tangent_near
    (S : ArctanSinPiConstruction)
    {x y : Rat} (hx : 0 <= x /\ x <= (1 : Rat) / 2)
    (hy : 0 <= y /\ y <= (1 : Rat) / 2)
    (htx : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x))
    (hty : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * y))
    (evalStage : Nat) (eps : QPos)
    (hnear : QInterval.NearAt
      ((IntegralIdentities.tangentOnUnit S.inverse).compute (2 * x)
        htx evalStage)
      ((IntegralIdentities.tangentOnUnit S.inverse).compute (2 * y)
        hty evalStage) eps) :
    QInterval.NearAt
      (S.onHalf.compute x hx evalStage)
      (S.onHalf.compute y hy evalStage)
      { val := 2 * eps.val
        property := Rat.mul_pos (by decide +kernel) eps.property } := by
  have hUx : subintervalOf
      ((IntegralIdentities.tangentOnUnit S.inverse).compute (2 * x)
        htx evalStage) 0 1 :=
    IntegralIdentities.ArctanInverseBisection.tangentAt_stays_in_unitSlope
      S.inverse (2 * x) htx evalStage
  have hUy : subintervalOf
      ((IntegralIdentities.tangentOnUnit S.inverse).compute (2 * y)
        hty evalStage) 0 1 :=
    IntegralIdentities.ArctanInverseBisection.tangentAt_stays_in_unitSlope
      S.inverse (2 * y) hty evalStage
  change QInterval.NearAt
    (rationalCircleSinInterval
      ((IntegralIdentities.tangentOnUnit S.inverse).compute (2 * x)
        htx evalStage))
    (rationalCircleSinInterval
      ((IntegralIdentities.tangentOnUnit S.inverse).compute (2 * y)
        hty evalStage)) _
  exact rationalCircleSinInterval_near_of_near hUx hUy
    eps hnear

/-- Effective modulus for the public `sin (pi*x)` evaluator.  The factor two
in the input schedule accounts for the reparameterization `t = 2*x`; the
second factor two in the output budget is the rational-circle sine Lipschitz
bound.  This is still a finite interval theorem: no classical real sine is
used. -/
def ArctanSinPiConstruction.sinPiOnHalf_effectiveModulus
    (S : ArctanSinPiConstruction)
    (tangentModulus : EffectiveModulusFor
      (IntegralIdentities.tangentOnUnit S.inverse)) :
    EffectiveModulusFor S.onHalf where
  inputPrecision := fun n =>
    2 * tangentModulus.inputPrecision (2 * (n + 1))
  evalPrecision := fun n =>
    tangentModulus.evalPrecision (2 * (n + 1))
  close := by
    intro x y n hx hy hclose
    let m := 2 * (n + 1)
    have hscale :
        2 * (precisionAtStage m).val <= (precisionAtStage n).val := by
      cases n with
      | zero => decide +kernel
      | succ n =>
          have hrec := one_div_antitone_pos_local
            (a := ((n + 1 : Nat) : Rat))
            (b := ((n + 2 : Nat) : Rat))
            ((Rat.natCast_pos).2 (by omega))
            (Rat.natCast_le_natCast.2 (by omega))
          have heq :
              2 * (1 / (((2 * (n + 2) : Nat) : Rat))) =
                1 / (((n + 2 : Nat) : Rat)) := by
            rw [Rat.natCast_mul, Rat.div_def, Rat.div_def]
            have hn : ((n + 2 : Nat) : Rat) ≠ 0 :=
              Rat.ne_of_gt ((Rat.natCast_pos).2 (by omega))
            grind [Rat.mul_assoc, Rat.mul_comm,
              Rat.mul_inv_cancel _ hn]
          dsimp [m, precisionAtStage]
          rw [heq]
          exact hrec
    have hx' : 0 <= 2 * x /\ 2 * x <= 1 := by
      have hx0 : 0 <= x := hx.1
      have hxhalf : x <= (1 : Rat) / 2 := hx.2
      constructor
      · exact Rat.mul_nonneg (by decide +kernel) hx0
      · have h := Rat.mul_le_mul_of_nonneg_left hxhalf
          (by decide +kernel : (0 : Rat) <= 2)
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
        rw [hhalf] at h
        exact h
    have hy' : 0 <= 2 * y /\ 2 * y <= 1 := by
      have hy0 : 0 <= y := hy.1
      have hyhalf : y <= (1 : Rat) / 2 := hy.2
      constructor
      · exact Rat.mul_nonneg (by decide +kernel) hy0
      · have h := Rat.mul_le_mul_of_nonneg_left hyhalf
          (by decide +kernel : (0 : Rat) <= 2)
        have hhalf : (2 : Rat) * (1 / 2) = 1 := by decide +kernel
        rw [hhalf] at h
        exact h
    have hinput : qabs (2 * y - 2 * x) <=
        1 / ((tangentModulus.inputPrecision m : Nat) : Rat) := by
      have hmul := Rat.mul_le_mul_of_nonneg_left hclose
        (by decide +kernel : (0 : Rat) <= 2)
      rw [show 2 * y - 2 * x = 2 * (y - x) by grind, qabs_mul]
      have htwo : qabs (2 : Rat) = 2 := by decide +kernel
      rw [htwo]
      have hmul' : 2 * qabs (y - x) <=
          2 * (1 / ((2 * tangentModulus.inputPrecision m : Nat) : Rat)) := by
        simpa [m, Rat.natCast_mul, Rat.mul_comm] using hmul
      calc
        2 * qabs (y - x) <=
            2 * (1 / ((2 * tangentModulus.inputPrecision m : Nat) : Rat)) := hmul'
        _ = 1 / ((tangentModulus.inputPrecision m : Nat) : Rat) := by
          rw [Rat.natCast_mul, Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm,
            Rat.mul_inv_cancel]
    have htangent := tangentModulus.close
      (2 * x) (2 * y) m hx' hy' hinput
    have hsin := S.sinPiOnHalf_near_of_tangent_near
      hx hy hx' hy' (tangentModulus.evalPrecision m)
      (precisionAtStage m) htangent
    change QInterval.NearAt
      (S.onHalf.compute x hx (tangentModulus.evalPrecision m))
      (S.onHalf.compute y hy (tangentModulus.evalPrecision m))
      (precisionAtStage n)
    unfold QInterval.NearAt QInterval.width at hsin ⊢
    rcases hsin with ⟨hxy, hyx, hwidthx, hwidthy⟩
    constructor <;> grind

/-! Monotonicity also transports through the same finite circle map.  This is
the bridge needed by the endpoint Darboux constructor: the inverse search
supplies a monotone tangent branch, and the rational formula
`2*u/(1+u^2)` is monotone on the certified unit-slope interval. -/

theorem ArctanSinPiConstruction.onHalf_nondecreasing_of_tangent_nondecreasing
    (S : ArctanSinPiConstruction)
  (htangent : NondecreasingOnInterval
      (IntegralIdentities.tangentOnUnit S.inverse)) :
    NondecreasingOnInterval S.onHalf := by
  intro x y hx hy hxy n
  change 0 <= x ∧ x <= (1 : Rat) / 2 at hx
  change 0 <= y ∧ y <= (1 : Rat) / 2 at hy
  have hx' : 0 <= 2 * x /\ 2 * x <= 1 := by
    constructor
    · exact Rat.mul_nonneg (by decide +kernel) hx.1
    · have h := Rat.mul_le_mul_of_nonneg_left hx.2
        (by decide +kernel : (0 : Rat) <= 2)
      rw [show (2 : Rat) * (1 / 2) = 1 by decide +kernel] at h
      exact h
  have hy' : 0 <= 2 * y /\ 2 * y <= 1 := by
    constructor
    · exact Rat.mul_nonneg (by decide +kernel) hy.1
    · have h := Rat.mul_le_mul_of_nonneg_left hy.2
        (by decide +kernel : (0 : Rat) <= 2)
      rw [show (2 : Rat) * (1 / 2) = 1 by decide +kernel] at h
      exact h
  have htan := htangent (2 * x) (2 * y) hx' hy'
    (Rat.mul_le_mul_of_nonneg_left hxy
      (by decide +kernel : (0 : Rat) <= 2)) n
  have hUx :=
    IntegralIdentities.ArctanInverseBisection.tangentAt_stays_in_unitSlope
      S.inverse (2 * x) hx' n
  have hUy :=
    IntegralIdentities.ArctanInverseBisection.tangentAt_stays_in_unitSlope
      S.inverse (2 * y) hy' n
  change (rationalCircleSinInterval
      (S.inverse.tangentRaw.compute (2 * x) _ n)).lo <=
    (rationalCircleSinInterval
      (S.inverse.tangentRaw.compute (2 * y) _ n)).hi
  exact rationalCircleSin_mono hUx.1 htan hUy.2.2

/-- The equal-dyadic-subdivision integral of `sin (pi*x)` on `[0,1/2]`.

The caller supplies the usual interval-sum certificate.  This is the
computable value before any identification with a closed expression.
-/
def halfIntegral
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x))
    (c : Integral.SampleConstruction
      (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2)) : RealCompute :=
  Integral.sampleValue
    (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2) c

theorem halfIntegral_valid
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x))
    (c : Integral.SampleConstruction
      (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2)) :
    (halfIntegral C hdefined c).Valid := by
  exact FTC.integral_valid_of_construction c

/-- A dyadic sample replacement computes the same public sine integral.

The replacement `g` may use a specialized evaluator—for example, nested
radicals at dyadic angles—because the equal-dyadic algorithm never reads its
values away from the left endpoints of its finite meshes.  Agreement is still
required at every finite stage and every sample point, so this is a
constructive algorithm-transport theorem rather than an extensional claim
about an unrepresented real function. -/
theorem halfIntegral_equiv_of_dyadic_sample_replacement
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x))
    (c : Integral.SampleConstruction
      (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hplan : c.plan = cg.plan)
    (hsamples : forall n k,
      k < (c.plan n).subdivisions ->
      (sinPiOnHalf C hdefined).toRealFunRaw.compute
        (leftPoint 0 ((1 : Rat) / 2) (c.plan n).subdivisions k)
        (c.plan n).evalPrecision =
      g.compute
        (leftPoint 0 ((1 : Rat) / 2) (c.plan n).subdivisions k)
        (c.plan n).evalPrecision) :
    (halfIntegral C hdefined c).Equiv
      (Integral.sampleValue g 0 ((1 : Rat) / 2) cg) := by
  exact Integral.integral_equiv_of_plan_and_samples c cg hplan hsamples

/-- The interval-overlap version of dyadic sample replacement.

This is the form needed by practical finite evaluators: a nested-radical or
Taylor implementation need only overlap the arctangent-backed sine box at
each sampled dyadic point.  Exact equality of the two finite boxes is not
required. -/
theorem halfIntegral_equiv_of_dyadic_sample_overlap
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x))
    (c : Integral.SampleConstruction
      (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hplan : c.plan = cg.plan)
    (hsamples : forall n k,
      k < (c.plan n).subdivisions ->
      QInterval.Overlaps
        ((sinPiOnHalf C hdefined).toRealFunRaw.compute
          (leftPoint 0 ((1 : Rat) / 2)
            (c.plan n).subdivisions k)
          (c.plan n).evalPrecision)
        (g.compute
          (leftPoint 0 ((1 : Rat) / 2)
            (c.plan n).subdivisions k)
          (c.plan n).evalPrecision)) :
    (halfIntegral C hdefined c).Equiv
      (Integral.sampleValue g 0 ((1 : Rat) / 2) cg) := by
  exact Integral.integral_equiv_of_plan_and_sample_overlaps
    (by decide +kernel : (0 : Rat) <= (1 : Rat) / 2)
    c cg hplan hsamples

/-!
## The nested-radical dyadic route

The equal-dyadic public integral reads only the points
`x = k / 2^n` (with the endpoint convention carried by the integral plan).
After the normalized change of coordinate used by `sin (pi*x)`, the angle
coordinate is `2*x = k/2^n`.  This is the exact finite input on which a
successive half-angle implementation may run its nested-square-root
algorithm.  No claim about the evaluator away from these points is needed.
-/

theorem sinPi_half_dyadic_normalized_sample
    {n k : Nat} (hk : k < 2 ^ n) :
    2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k =
      (k : Rat) / ((2 ^ n : Nat) : Rat) := by
  have hpow : 0 < 2 ^ n := Nat.pow_pos (by omega : 0 < 2)
  have hpowRat : ((2 ^ n : Nat) : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hpow)
  rw [two_mul_leftPoint_zero_half_eq_leftPoint_zero_one]
  unfold leftPoint mesh
  rw [if_neg (Nat.ne_of_gt hpow)]
  simp only [Rat.zero_add]
  rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel _ hpowRat]

theorem sinPi_half_dyadic_sample_in_unit
    {n k : Nat} (hk : k < 2 ^ n) :
    0 <= 2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k /\
      2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k <= 1 := by
  rw [sinPi_half_dyadic_normalized_sample hk]
  have hpow : 0 < 2 ^ n := Nat.pow_pos (by omega : 0 < 2)
  have hpowRat : ((2 ^ n : Nat) : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hpow)
  have hdenpos : 0 < ((2 ^ n : Nat) : Rat) :=
    (Rat.natCast_pos).2 hpow
  rw [Rat.div_def]
  constructor
  · exact Rat.mul_nonneg
      (Rat.natCast_nonneg)
      (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))
  · apply Rat.le_of_mul_le_mul_right (c := ((2 ^ n : Nat) : Rat))
    · rw [Rat.mul_assoc, Rat.inv_mul_cancel _ hpowRat, Rat.mul_one]
      have hkcast : (k : Rat) <= ((2 ^ n : Nat) : Rat) := by
        exact_mod_cast (Nat.le_of_lt hk)
      simpa using hkcast
    · exact hdenpos

theorem dyadicHalfDomain {n k : Nat} (hk : k < 2 ^ n) :
    0 <= leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k /\
      leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k <= (1 : Rat) / 2 := by
  have h := sinPi_half_dyadic_sample_in_unit hk
  constructor
  · apply Rat.le_of_mul_le_mul_left (c := (2 : Rat))
    · simpa [Rat.zero_mul] using h.1
    · decide +kernel
  · apply Rat.le_of_mul_le_mul_left (c := (2 : Rat))
    · calc
        2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k <= 1 := h.2
        _ = 2 * ((1 : Rat) / 2) := by decide +kernel
    · decide +kernel

/-! Canonical inverse boxes at the actual equal-dyadic sample points.  These
definitions eliminate a layer of bookkeeping from the nested-radical route:
the public arctangent sine evaluator is definitionally the circle-sine map of
this box, and its `[0,1]` bounds follow from the inverse package itself. -/

def dyadicNormalizedBranch {n k : Nat} (hk : k < 2 ^ n) :
    RationalCircle.GeometricTrig.firstQuadrantBranch
      (2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k) := by
  change 0 <= 2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k /\
    2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k <= 1
  exact sinPi_half_dyadic_sample_in_unit hk

def dyadicTangentBox
    (B : IntegralIdentities.ArctanInverseBisection)
    {n k : Nat} (hk : k < 2 ^ n) : QInterval :=
  B.tangentRaw.compute
    (2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k)
      (dyadicNormalizedBranch hk) n

/-! Precision and geometric depth are separate inputs for the semantic
proof.  The public sample is at depth `n`, while its interval can be refined
at any later computation precision `p`. -/

def dyadicTangentBoxAt
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision depth k : Nat) (hk : k < 2 ^ depth) : QInterval :=
  B.tangentRaw.compute
    (2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
    (dyadicNormalizedBranch hk) precision

theorem dyadicTangentBoxAt_bounds
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision depth k : Nat) (hk : k < 2 ^ depth) :
    subintervalOf (dyadicTangentBoxAt B precision depth k hk) 0 1 := by
  unfold dyadicTangentBoxAt
  exact B.tangentAt_stays_in_unitSlope
    (2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
    (dyadicNormalizedBranch hk) precision

theorem dyadicTangentBox_bounds
    (B : IntegralIdentities.ArctanInverseBisection)
    {n k : Nat} (hk : k < 2 ^ n) :
    subintervalOf (dyadicTangentBox B hk) 0 1 := by
  unfold dyadicTangentBox
  change subintervalOf
    ((B.tangentAt
      (2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k)
      (dyadicNormalizedBranch hk)).compute n) 0 1
  exact B.tangentAt_stays_in_unitSlope
    (2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k)
    (dyadicNormalizedBranch hk) n

theorem canonical_dyadic_zero_search
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero) (n : Nat) :
    ∃ u, rationalTangentWitnessBoxSearch
      (dyadicTangentBox B (n := n) (k := 0) (by
        exact Nat.pow_pos (by omega : 0 < 2)))
      ({ lo := 0, hi := 0 } : QInterval) 0 = some u := by
  let hk : 0 < 2 ^ n := Nat.pow_pos (by omega : 0 < 2)
  have hbox : subintervalOf
      (dyadicTangentBox B hk) 0 1 :=
    dyadicTangentBox_bounds B hk
  have hover : QInterval.Overlaps
      (dyadicTangentBox B hk)
      ({ lo := 0, hi := 0 } : QInterval) := by
    have hzero := (RealCompute.compareAt_overlap_iff
      (B.tangentAt 0
        RationalCircle.GeometricTrig.firstQuadrantBranch_zero)
      RealCompute.zero n n).1 (ht n)
    simpa [dyadicTangentBox,
      IntegralIdentities.ArctanInverseBisection.tangentRaw,
      RealCompute.zero, leftPoint, mesh, Rat.zero_add, Rat.add_zero,
      Rat.zero_mul, Rat.mul_zero] using hzero
  exact rationalTangentWitnessBoxSearch_complete_of_zero_target
    hbox hover

theorem canonical_dyadic_zero_search_at
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    (precision depth : Nat) (hk : 0 < 2 ^ depth) :
    ∃ u, rationalTangentWitnessBoxSearch
      (dyadicTangentBoxAt B precision depth 0 hk)
      ({ lo := 0, hi := 0 } : QInterval) 0 = some u := by
  have hbox : subintervalOf
      (dyadicTangentBoxAt B precision depth 0 hk) 0 1 :=
    dyadicTangentBoxAt_bounds B precision depth 0 hk
  have hover : QInterval.Overlaps
      (dyadicTangentBoxAt B precision depth 0 hk)
      ({ lo := 0, hi := 0 } : QInterval) := by
    have hzero := (RealCompute.compareAt_overlap_iff
      (B.tangentAt 0
        RationalCircle.GeometricTrig.firstQuadrantBranch_zero)
      RealCompute.zero precision precision).1 (ht precision)
    simpa [dyadicTangentBoxAt,
      IntegralIdentities.ArctanInverseBisection.tangentRaw,
      RealCompute.zero, leftPoint, mesh, Rat.zero_add, Rat.add_zero,
      Rat.zero_mul, Rat.mul_zero] using hzero
  exact rationalTangentWitnessBoxSearch_complete_of_zero_target
    hbox hover

theorem sinPiRawOfArctan_dyadic_compute_eq_circle
    (B : IntegralIdentities.ArctanInverseBisection)
    {n k : Nat} (hk : k < 2 ^ n) :
    (sinPiRawOfArctan B
      (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k)
      (dyadicHalfDomain hk)).compute n =
      rationalCircleSinInterval (dyadicTangentBox B hk) := by
  rfl

/-! An executable nested-radical table.  The table is total so that its raw
algorithm can be inspected before its invariant is proved.  On the valid
dyadic range, even indices reuse the preceding level and odd indices apply
the positive half-angle square roots; the upper half is recovered by the
symmetry `sin (pi-theta)=sin theta`, `cos (pi-theta)=-cos theta`. -/

def dyadicNestedRadicalNeg (I : QInterval) : QInterval :=
  { lo := -I.hi, hi := -I.lo }

def dyadicNestedRadicalTable : Nat -> Nat -> QInterval × QInterval
  | 0, k =>
      if k = 0 then
        ({ lo := 0, hi := 0 }, { lo := 1, hi := 1 })
      else if k = 1 then
        ({ lo := 1, hi := 1 }, { lo := 0, hi := 0 })
      else
        ({ lo := 0, hi := 1 }, { lo := -1, hi := 1 })
  | n + 1, k =>
      if k % 2 = 0 then
        dyadicNestedRadicalTable n (k / 2)
      else
        let bound := 2 ^ n
        let reflected := if k <= bound then k else 2 * bound - k
        let parent := dyadicNestedRadicalTable n reflected
        let parentCos :=
          if k <= bound then parent.2 else dyadicNestedRadicalNeg parent.2
        let sinInput : QInterval :=
          { lo := (1 - parentCos.hi) / 2,
            hi := (1 - parentCos.lo) / 2 }
        let cosInput : QInterval :=
          { lo := (1 + parentCos.lo) / 2,
            hi := (1 + parentCos.hi) / 2 }
        let sine := sqrtOnUnitEvalIntervalTotal sinInput (n + 1)
        let cosine := sqrtOnUnitEvalIntervalTotal cosInput (n + 1)
        if k <= bound then (sine, cosine)
        else (sine, dyadicNestedRadicalNeg cosine)
  termination_by n => n

def dyadicNestedRadicalSinAt (n k : Nat) : QInterval :=
  (dyadicNestedRadicalTable n k).1

def dyadicNestedRadicalCosAt (n k : Nat) : QInterval :=
  (dyadicNestedRadicalTable n k).2

theorem dyadicNestedRadicalTable_zero_zero :
    dyadicNestedRadicalTable 0 0 =
      ({ lo := 0, hi := 0 }, { lo := 1, hi := 1 }) := by
  simp [dyadicNestedRadicalTable]

theorem dyadicNestedRadicalTable_zero_one :
    dyadicNestedRadicalTable 0 1 =
      ({ lo := 1, hi := 1 }, { lo := 0, hi := 0 }) := by
  simp [dyadicNestedRadicalTable]

theorem dyadicNestedRadicalSinAt_zero_zero :
    dyadicNestedRadicalSinAt 0 0 = { lo := 0, hi := 0 } := by
  simp [dyadicNestedRadicalSinAt, dyadicNestedRadicalTable]

theorem dyadicNestedRadicalSinAt_zero_one :
    dyadicNestedRadicalSinAt 0 1 = { lo := 1, hi := 1 } := by
  simp [dyadicNestedRadicalSinAt, dyadicNestedRadicalTable]

theorem dyadicNestedRadicalTable_one_one :
    dyadicNestedRadicalTable 1 1 =
      (sqrtOnUnitEvalIntervalTotal { lo := (1 : Rat) / 2, hi := (1 : Rat) / 2 } 1,
       sqrtOnUnitEvalIntervalTotal { lo := (1 : Rat) / 2, hi := (1 : Rat) / 2 } 1) := by
  simp [dyadicNestedRadicalTable]
  constructor <;> congr 1 <;> decide +kernel

theorem dyadicNestedRadicalTable_succ_even (n k : Nat) :
    dyadicNestedRadicalTable (n + 1) (2 * k) =
      dyadicNestedRadicalTable n k := by
  simp [dyadicNestedRadicalTable]

theorem dyadicNestedRadicalSinAt_succ_even (n k : Nat) :
    dyadicNestedRadicalSinAt (n + 1) (2 * k) =
      dyadicNestedRadicalSinAt n k := by
  simp [dyadicNestedRadicalSinAt, dyadicNestedRadicalTable]

/-! The two indices of the mathematical mesh and the evaluator precision
must not be conflated.  The first table above is retained as the small
recurrence exposed in early versions of the blueprint.  The certified raw
algorithm uses the following version: `precision` is held fixed while the
half-angle path is recursively rebuilt from level zero.  Thus a later mesh
stage never reuses a stale low-precision parent box. -/

def dyadicHalfAngleSinInput (I : QInterval) : QInterval :=
  { lo := (1 - I.hi) / 2, hi := (1 - I.lo) / 2 }

def dyadicHalfAngleCosInput (I : QInterval) : QInterval :=
  { lo := (1 + I.lo) / 2, hi := (1 + I.hi) / 2 }

theorem dyadicHalfAngleSinInput_width (I : QInterval) :
    (dyadicHalfAngleSinInput I).width = I.width / 2 := by
  unfold dyadicHalfAngleSinInput QInterval.width
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]

theorem dyadicHalfAngleCosInput_width (I : QInterval) :
    (dyadicHalfAngleCosInput I).width = I.width / 2 := by
  unfold dyadicHalfAngleCosInput QInterval.width
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]

theorem dyadicHalfAngle_clipped_square_sum_overlaps_one
    (I : QInterval) (hI : subintervalOf I (-1) 1) (n : Nat) :
    QInterval.Overlaps
      { lo :=
          sq (sqrtOnUnitEvalIntervalClipped
            (dyadicHalfAngleSinInput I) n).lo +
            sq (sqrtOnUnitEvalIntervalClipped
              (dyadicHalfAngleCosInput I) n).lo,
        hi :=
          sq (sqrtOnUnitEvalIntervalClipped
            (dyadicHalfAngleSinInput I) n).hi +
            sq (sqrtOnUnitEvalIntervalClipped
              (dyadicHalfAngleCosInput I) n).hi }
      ({ lo := 1, hi := 1 } : QInterval) := by
  have hsinI : subintervalOf
      (dyadicHalfAngleSinInput I) 0 1 := by
    unfold dyadicHalfAngleSinInput subintervalOf at *
    grind
  have hcosI : subintervalOf
      (dyadicHalfAngleCosInput I) 0 1 := by
    unfold dyadicHalfAngleCosInput subintervalOf at *
    grind
  have hsin := sqrtOnUnitEvalIntervalClipped_square_contains_input
    (dyadicHalfAngleSinInput I) hsinI n
  have hcos := sqrtOnUnitEvalIntervalClipped_square_contains_input
    (dyadicHalfAngleCosInput I) hcosI n
  unfold QInterval.Overlaps
  have hlow := rat_add_le_add hsin.1 hcos.1
  have hhigh := rat_add_le_add hsin.2 hcos.2
  constructor
  · apply Rat.le_trans hlow
    dsimp [dyadicHalfAngleSinInput, dyadicHalfAngleCosInput]
    grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, hI.2.1]
  · calc
      1 <= (dyadicHalfAngleSinInput I).hi +
          (dyadicHalfAngleCosInput I).hi := by
        dsimp [dyadicHalfAngleSinInput, dyadicHalfAngleCosInput]
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, hI.2.1]
      _ <= _ := hhigh

theorem dyadicHalfAngleSinInput_overlap_of_parent_overlap
    {I J : QInterval} (hover : QInterval.Overlaps I J) :
    QInterval.Overlaps
      (dyadicHalfAngleSinInput I)
      (dyadicHalfAngleSinInput J) := by
  unfold dyadicHalfAngleSinInput QInterval.Overlaps at *
  rw [Rat.div_def, Rat.div_def]
  have hhalf : (2 : Rat)⁻¹ = 1 / 2 := by decide +kernel
  rw [hhalf]
  constructor <;> grind [Rat.mul_assoc, Rat.mul_comm]

theorem dyadicHalfAngleCosInput_overlap_of_parent_overlap
    {I J : QInterval} (hover : QInterval.Overlaps I J) :
    QInterval.Overlaps
      (dyadicHalfAngleCosInput I)
      (dyadicHalfAngleCosInput J) := by
  unfold dyadicHalfAngleCosInput QInterval.Overlaps at *
  rw [Rat.div_def, Rat.div_def]
  have hhalf : (2 : Rat)⁻¹ = 1 / 2 := by decide +kernel
  rw [hhalf]
  constructor <;> grind [Rat.mul_assoc, Rat.mul_comm]

theorem dyadicHalfAngleSqrt_width_le
    (I : QInterval) (hI : subintervalOf I 0 1) (n : Nat)
    (hinput : I.width <=
      1 / (((16 * (n + 1) * (n + 1) : Nat) : Rat))) :
    (sqrtOnUnitEvalIntervalClipped I n).width <=
      1 / (((n + 1 : Nat) : Rat)) := by
  exact Rat.le_trans
    (sqrtOnUnitEvalIntervalClipped_width_le_total I n)
    (sqrtOnUnitEvalInterval_width_le I hI n hinput)

def dyadicNestedRadicalParentPrecision (precision : Nat) : Nat :=
  16 * (precision + 1) * (precision + 1)

theorem dyadicNestedRadicalParentPrecision_input_budget (precision : Nat) :
    1 / (((2 * (dyadicNestedRadicalParentPrecision precision + 1) : Nat) : Rat)) <=
      1 / (((16 * (precision + 1) * (precision + 1) : Nat) : Rat)) := by
  apply FTC.one_div_nat_antitone
    (n := 16 * (precision + 1) * (precision + 1))
    (m := 2 * (dyadicNestedRadicalParentPrecision precision + 1))
  · exact Nat.mul_pos (Nat.mul_pos (by omega) (Nat.succ_pos _)) (Nat.succ_pos _)
  · unfold dyadicNestedRadicalParentPrecision
    exact Nat.mul_pos (by omega) (Nat.succ_pos _)
  · unfold dyadicNestedRadicalParentPrecision
    omega

theorem dyadicNestedRadicalParentPrecision_output_budget (precision : Nat) :
    1 / (((dyadicNestedRadicalParentPrecision precision + 1 : Nat) : Rat)) <=
      1 / (((precision + 1 : Nat) : Rat)) := by
  apply FTC.one_div_nat_antitone
    (n := precision + 1)
    (m := dyadicNestedRadicalParentPrecision precision + 1)
  · exact Nat.succ_pos _
  · change 0 < 16 * (precision + 1) * (precision + 1) + 1
    exact Nat.succ_pos _
  · unfold dyadicNestedRadicalParentPrecision
    change precision + 1 ≤ 16 * (precision + 1) * (precision + 1) + 1
    have hsq : precision + 1 ≤ (precision + 1) * (precision + 1) :=
      Nat.le_mul_of_pos_right (precision + 1) (Nat.succ_pos _)
    have hscaled : precision + 1 ≤ 16 * ((precision + 1) * (precision + 1)) :=
      Nat.le_trans hsq (Nat.le_mul_of_pos_left _ (by omega))
    have hp : precision ≤ precision + 1 := Nat.le_succ _
    simpa [Nat.mul_assoc] using Nat.le_trans hp hscaled

def dyadicNestedRadicalTableAt (precision : Nat) : Nat -> Nat -> QInterval × QInterval
  | 0, k =>
      if k = 0 then
        ({ lo := 0, hi := 0 }, { lo := 1, hi := 1 })
      else if k = 1 then
        ({ lo := 1, hi := 1 }, { lo := 0, hi := 0 })
      else
        ({ lo := 0, hi := 1 }, { lo := -1, hi := 1 })
  | n + 1, k =>
      if k % 2 = 0 then
        dyadicNestedRadicalTableAt
          (dyadicNestedRadicalParentPrecision precision) n (k / 2)
      else
        let bound := 2 ^ n
        let reflected := if k <= bound then k else 2 * bound - k
        let parent := dyadicNestedRadicalTableAt
          (dyadicNestedRadicalParentPrecision precision) n reflected
        let parentCos :=
          if k <= bound then parent.2 else dyadicNestedRadicalNeg parent.2
        let sinInput := dyadicHalfAngleSinInput parentCos
        let cosInput := dyadicHalfAngleCosInput parentCos
        let sine := sqrtOnUnitEvalIntervalClipped sinInput precision
        let cosine := sqrtOnUnitEvalIntervalClipped cosInput precision
        if k <= bound then (sine, cosine)
        else (sine, dyadicNestedRadicalNeg cosine)
  termination_by n => n

def dyadicNestedRadicalStageTable (n k : Nat) : QInterval × QInterval :=
  dyadicNestedRadicalTableAt n n k

def dyadicNestedRadicalStageSinAt (n k : Nat) : QInterval :=
  (dyadicNestedRadicalStageTable n k).1

def dyadicNestedRadicalSampleRaw (depth k : Nat) : RealCompute where
  compute := fun precision =>
    (dyadicNestedRadicalTableAt precision depth k).1

theorem dyadicNestedRadicalTableAt_succ_odd
    (precision n k : Nat) (hodd : k % 2 = 1) :
    dyadicNestedRadicalTableAt precision (n + 1) k =
      let bound := 2 ^ n
      let reflected := if k <= bound then k else 2 * bound - k
      let parent := dyadicNestedRadicalTableAt
        (dyadicNestedRadicalParentPrecision precision) n reflected
      let parentCos :=
        if k <= bound then parent.2 else dyadicNestedRadicalNeg parent.2
      let sine := sqrtOnUnitEvalIntervalClipped
        (dyadicHalfAngleSinInput parentCos) precision
      let cosine := sqrtOnUnitEvalIntervalClipped
        (dyadicHalfAngleCosInput parentCos) precision
      if k <= bound then (sine, cosine) else
        (sine, dyadicNestedRadicalNeg cosine) := by
  simp [dyadicNestedRadicalTableAt, hodd]

theorem dyadicHalfAngleSinInput_subinterval
    (I : QInterval) (hI : subintervalOf I (-1) 1) :
    subintervalOf (dyadicHalfAngleSinInput I) 0 1 := by
  unfold dyadicHalfAngleSinInput subintervalOf at *
  rcases hI with ⟨hlo, hord, hhi⟩
  change 0 <= (1 - I.hi) / 2 ∧
    (1 - I.hi) / 2 <= (1 - I.lo) / 2 ∧
      (1 - I.lo) / 2 <= 1
  constructor
  · rw [Rat.div_def]
    have htwo : 0 <= (2 : Rat)⁻¹ := by decide +kernel
    grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]
  constructor <;> rw [Rat.div_def]
  · have htwo : 0 <= (2 : Rat)⁻¹ := by decide +kernel
    grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]
  · have htwo : 0 <= (2 : Rat)⁻¹ := by decide +kernel
    grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]

theorem dyadicHalfAngleCosInput_subinterval
    (I : QInterval) (hI : subintervalOf I (-1) 1) :
    subintervalOf (dyadicHalfAngleCosInput I) 0 1 := by
  unfold dyadicHalfAngleCosInput subintervalOf at *
  rcases hI with ⟨hlo, hord, hhi⟩
  change 0 <= (1 + I.lo) / 2 ∧
    (1 + I.lo) / 2 <= (1 + I.hi) / 2 ∧
      (1 + I.hi) / 2 <= 1
  constructor
  · rw [Rat.div_def]
    have htwo : 0 <= (2 : Rat)⁻¹ := by decide +kernel
    grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]
  constructor <;> rw [Rat.div_def]
  · have htwo : 0 <= (2 : Rat)⁻¹ := by decide +kernel
    grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]
  · have htwo : 0 <= (2 : Rat)⁻¹ := by decide +kernel
    grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]

theorem dyadicHalfAngleSqrt_overlap_of_parent_overlap
    {I J : QInterval} (hI : subintervalOf I (-1) 1)
    (hJ : subintervalOf J (-1) 1)
    (hover : QInterval.Overlaps I J) (n : Nat) :
    QInterval.Overlaps
      (sqrtOnUnitEvalIntervalClipped (dyadicHalfAngleSinInput I) n)
      (sqrtOnUnitEvalIntervalClipped (dyadicHalfAngleSinInput J) n) := by
  apply sqrtOnUnitEvalIntervalClipped_overlap_of_input_overlap
    (dyadicHalfAngleSinInput_subinterval I hI)
    (dyadicHalfAngleSinInput_subinterval J hJ)
    (dyadicHalfAngleSinInput_overlap_of_parent_overlap hover)

theorem dyadicHalfAngleCosSqrt_overlap_of_parent_overlap
    {I J : QInterval} (hI : subintervalOf I (-1) 1)
    (hJ : subintervalOf J (-1) 1)
    (hover : QInterval.Overlaps I J) (n : Nat) :
    QInterval.Overlaps
      (sqrtOnUnitEvalIntervalClipped (dyadicHalfAngleCosInput I) n)
      (sqrtOnUnitEvalIntervalClipped (dyadicHalfAngleCosInput J) n) := by
  apply sqrtOnUnitEvalIntervalClipped_overlap_of_input_overlap
    (dyadicHalfAngleCosInput_subinterval I hI)
    (dyadicHalfAngleCosInput_subinterval J hJ)
    (dyadicHalfAngleCosInput_overlap_of_parent_overlap hover)

theorem dyadicHalfAngleSqrt_overlap_of_parent_overlap_at
    {I J : QInterval} (hI : subintervalOf I (-1) 1)
    (hJ : subintervalOf J (-1) 1)
    (hover : QInterval.Overlaps I J) (n m : Nat) :
    QInterval.Overlaps
      (sqrtOnUnitEvalIntervalClipped (dyadicHalfAngleSinInput I) n)
      (sqrtOnUnitEvalIntervalClipped (dyadicHalfAngleSinInput J) m) := by
  apply sqrtOnUnitEvalIntervalClipped_overlap_of_input_overlap_at
    (dyadicHalfAngleSinInput_subinterval I hI)
    (dyadicHalfAngleSinInput_subinterval J hJ)
    (dyadicHalfAngleSinInput_overlap_of_parent_overlap hover)

theorem dyadicHalfAngleCosSqrt_overlap_of_parent_overlap_at
    {I J : QInterval} (hI : subintervalOf I (-1) 1)
    (hJ : subintervalOf J (-1) 1)
    (hover : QInterval.Overlaps I J) (n m : Nat) :
    QInterval.Overlaps
      (sqrtOnUnitEvalIntervalClipped (dyadicHalfAngleCosInput I) n)
      (sqrtOnUnitEvalIntervalClipped (dyadicHalfAngleCosInput J) m) := by
  apply sqrtOnUnitEvalIntervalClipped_overlap_of_input_overlap_at
    (dyadicHalfAngleCosInput_subinterval I hI)
    (dyadicHalfAngleCosInput_subinterval J hJ)
    (dyadicHalfAngleCosInput_overlap_of_parent_overlap hover)

theorem dyadicHalfAngle_child_sine_overlap_of_raw_halfAngle
    {I J K : QInterval}
    (precision n j : Nat) (hI : subintervalOf I (-1) 1)
    (hJ : subintervalOf J (-1) 1)
    (hJeq : J =
      (dyadicNestedRadicalTableAt
        (dyadicNestedRadicalParentPrecision precision) n (2 * j + 1)).2)
    (hover : QInterval.Overlaps I J)
    (hraw : K = sqrtOnUnitEvalIntervalClipped
      (dyadicHalfAngleSinInput I) precision)
    (hbound : 2 * j + 1 <= 2 ^ n) :
    QInterval.Overlaps K
      (dyadicNestedRadicalTableAt precision (n + 1) (2 * j + 1)).1 := by
  have hodd : (2 * j + 1) % 2 = 1 := by omega
  have hsqrt := dyadicHalfAngleSqrt_overlap_of_parent_overlap_at
    hI hJ hover precision precision
  have htable := dyadicNestedRadicalTableAt_succ_odd
    precision n (2 * j + 1) hodd
  have htable' :
      (dyadicNestedRadicalTableAt precision (n + 1) (2 * j + 1)).1 =
        sqrtOnUnitEvalIntervalClipped
          (dyadicHalfAngleSinInput J) precision := by
    rw [htable]
    simp [hbound, hJeq]
  rw [hraw, htable']
  exact hsqrt

theorem dyadicHalfAngle_child_sine_overlap_of_raw_halfAngle_upper
    {I J K : QInterval}
    (precision n k : Nat) (hI : subintervalOf I (-1) 1)
    (hJ : subintervalOf J (-1) 1)
    (hJeq : J = dyadicNestedRadicalNeg
      (dyadicNestedRadicalTableAt
        (dyadicNestedRadicalParentPrecision precision) n
        (2 * 2 ^ n - k)).2)
    (hover : QInterval.Overlaps I J)
    (hraw : K = sqrtOnUnitEvalIntervalClipped
      (dyadicHalfAngleSinInput I) precision)
    (hodd : k % 2 = 1) (hupper : 2 ^ n < k)
    (hbound : k <= 2 ^ (n + 1)) :
    QInterval.Overlaps K
      (dyadicNestedRadicalTableAt precision (n + 1) k).1 := by
  have hsqrt := dyadicHalfAngleSqrt_overlap_of_parent_overlap_at
    hI hJ hover precision precision
  have htable := dyadicNestedRadicalTableAt_succ_odd
    precision n k hodd
  have htable' :
      (dyadicNestedRadicalTableAt precision (n + 1) k).1 =
        sqrtOnUnitEvalIntervalClipped
          (dyadicHalfAngleSinInput J) precision := by
    rw [htable]
    have hle : ¬ k <= 2 ^ n := by omega
    simp [hle, hJeq, hupper, hbound]
  rw [hraw, htable']
  exact hsqrt

theorem dyadicNestedRadicalNeg_subinterval
    (I : QInterval) (hI : subintervalOf I 0 1) :
    subintervalOf (dyadicNestedRadicalNeg I) (-1) 0 := by
  unfold dyadicNestedRadicalNeg subintervalOf at *
  rcases hI with ⟨hlo, hord, hhi⟩
  change -1 <= -I.hi ∧ -I.hi <= -I.lo ∧ -I.lo <= 0
  grind [Rat.sub_eq_add_neg]

theorem dyadicNestedRadicalNeg_unit_subinterval
    (I : QInterval) (hI : subintervalOf I (-1) 1) :
    subintervalOf (dyadicNestedRadicalNeg I) (-1) 1 := by
  unfold dyadicNestedRadicalNeg subintervalOf at *
  rcases hI with ⟨hlo, hord, hhi⟩
  change -1 <= -I.hi ∧ -I.hi <= -I.lo ∧ -I.lo <= 1
  grind [Rat.sub_eq_add_neg]

theorem dyadicNestedRadicalNeg_width (I : QInterval) :
    (dyadicNestedRadicalNeg I).width = I.width := by
  unfold dyadicNestedRadicalNeg QInterval.width
  grind [Rat.sub_eq_add_neg]

theorem one_div_nat_succ_half (n : Nat) :
    (1 / ((n + 1 : Nat) : Rat)) / 2 =
      1 / ((2 * (n + 1) : Nat) : Rat) := by
  rw [Rat.div_def, Rat.div_def]
  have hn : ((n + 1 : Nat) : Rat) ≠ 0 := by
    exact Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos n))
  have htwo : (2 : Rat) ≠ 0 := by decide +kernel
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem dyadicNestedRadicalParentPrecision_half_budget (precision : Nat) :
    (1 / ((dyadicNestedRadicalParentPrecision precision + 1 : Nat) : Rat)) / 2 <=
      1 / ((16 * (precision + 1) * (precision + 1) : Nat) : Rat) := by
  rw [one_div_nat_succ_half]
  exact dyadicNestedRadicalParentPrecision_input_budget precision

theorem dyadicNestedRadicalTableAt_bounds
    (precision n k : Nat) (hk : k <= 2 ^ n) :
    subintervalOf (dyadicNestedRadicalTableAt precision n k).1 0 1 ∧
      subintervalOf (dyadicNestedRadicalTableAt precision n k).2 (-1) 1 := by
  induction n generalizing precision k with
  | zero =>
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl <;>
        simp [dyadicNestedRadicalTableAt, subintervalOf] <;> decide +kernel
  | succ n ih =>
      by_cases he : k % 2 = 0
      · have hkrep : k = 2 * (k / 2) := by
          omega
        have hhalf : k / 2 <= 2 ^ n := by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow] at hk
          omega
        rw [hkrep]
        simp [dyadicNestedRadicalTableAt]
        exact ih (dyadicNestedRadicalParentPrecision precision) (k / 2) hhalf
      · let bound := 2 ^ n
        let parentPrecision := dyadicNestedRadicalParentPrecision precision
        let reflected := if k <= bound then k else 2 * bound - k
        have hpow : 2 ^ (n + 1) = 2 * bound := by
          dsimp [bound]
          rw [Nat.pow_succ]
          omega
        have hkbound : k <= 2 * bound := by
          rw [← hpow]
          exact hk
        have hreflect : reflected <= bound := by
          dsimp [reflected]
          split <;> omega
        have hparent := ih
          (dyadicNestedRadicalParentPrecision precision) reflected hreflect
        let parentCos :=
          if k <= bound then
            (dyadicNestedRadicalTableAt parentPrecision n reflected).2
          else
            dyadicNestedRadicalNeg
              (dyadicNestedRadicalTableAt parentPrecision n reflected).2
        have hparentCos : subintervalOf parentCos (-1) 1 := by
          by_cases hle : k <= bound
          · simpa [parentCos, hle] using hparent.2
          · have hneg := dyadicNestedRadicalNeg_unit_subinterval
              (dyadicNestedRadicalTableAt parentPrecision n reflected).2 hparent.2
            simpa [parentCos, hle] using hneg
        have hsinInput := dyadicHalfAngleSinInput_subinterval
          parentCos hparentCos
        have hcosInput := dyadicHalfAngleCosInput_subinterval
          parentCos hparentCos
        have hsine := sqrtOnUnitEvalIntervalClipped_subinterval
          (dyadicHalfAngleSinInput parentCos)
          hsinInput precision
        have hcos := sqrtOnUnitEvalIntervalClipped_subinterval
          (dyadicHalfAngleCosInput parentCos)
          hcosInput precision
        have hcosneg := dyadicNestedRadicalNeg_subinterval
          (sqrtOnUnitEvalIntervalClipped
            (dyadicHalfAngleCosInput parentCos) precision) hcos
        by_cases hle : k <= bound
        · simp [dyadicNestedRadicalTableAt, he, bound, reflected, hle]
          have hpc : parentCos =
              (dyadicNestedRadicalTableAt parentPrecision n k).2 := by
            simp [parentCos, parentPrecision, bound, reflected, hle]
          rw [hpc] at hsine hcos
          have hsine' : subintervalOf
              (sqrtOnUnitEvalIntervalClipped
                (dyadicHalfAngleSinInput
                  (dyadicNestedRadicalTableAt parentPrecision n k).2) precision) 0 1 := by
            exact hsine
          have hcos' : subintervalOf
              (sqrtOnUnitEvalIntervalClipped
                (dyadicHalfAngleCosInput
                  (dyadicNestedRadicalTableAt parentPrecision n k).2) precision) 0 1 := by
            exact hcos
          exact ⟨hsine', ⟨by
            have hlow := hcos'.1
            have hnegone : (-1 : Rat) <= 0 := by decide +kernel
            grind, hcos'.2.1, hcos'.2.2⟩⟩
        · simp [dyadicNestedRadicalTableAt, he, bound, reflected, hle]
          have hpc : parentCos = dyadicNestedRadicalNeg
              (dyadicNestedRadicalTableAt parentPrecision n (2 * bound - k)).2 := by
            simp [parentCos, parentPrecision, bound, reflected, hle]
          rw [hpc] at hsine hcosneg
          have hsine' : subintervalOf
              (sqrtOnUnitEvalIntervalClipped
                (dyadicHalfAngleSinInput
                  (dyadicNestedRadicalNeg
                    (dyadicNestedRadicalTableAt parentPrecision n (2 * bound - k)).2))
                precision) 0 1 := by
            exact hsine
          have hcosneg' : subintervalOf
              (dyadicNestedRadicalNeg
                (sqrtOnUnitEvalIntervalClipped
                  (dyadicHalfAngleCosInput
                    (dyadicNestedRadicalNeg
                      (dyadicNestedRadicalTableAt parentPrecision n (2 * bound - k)).2))
                  precision))
              (-1) 0 := by
            exact hcosneg
          exact ⟨hsine', ⟨hcosneg'.1, hcosneg'.2.1, by
            have hupper := hcosneg'.2.2
            have hone : (-1 : Rat) <= 1 := by decide +kernel
            grind⟩⟩

theorem arctanSinPi_nestedRadicalStage_sample_overlap_of_tangent_witness
    (B : IntegralIdentities.ArctanInverseBisection)
    {x : Rat} (hx : 0 <= x /\ x <= (1 : Rat) / 2) (n k : Nat)
    (hk : k <= 2 ^ n) (u : Rat)
    (hu : (B.tangentRaw.compute (2 * x)
      (by
        change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
        constructor
        · exact Rat.mul_nonneg (by decide +kernel) hx.1
        · have h := Rat.mul_le_mul_of_nonneg_left hx.2
            (by decide +kernel : (0 : Rat) <= 2)
          rw [show (2 : Rat) * (1 / 2) = 1 by decide +kernel] at h
          exact h) n).lo <= u /\
      u <= (B.tangentRaw.compute (2 * x)
        (by
          change RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x)
          constructor
          · exact Rat.mul_nonneg (by decide +kernel) hx.1
          · have h := Rat.mul_le_mul_of_nonneg_left hx.2
              (by decide +kernel : (0 : Rat) <= 2)
            rw [show (2 : Rat) * (1 / 2) = 1 by decide +kernel] at h
            exact h) n).hi)
    (himage : (dyadicNestedRadicalStageSinAt n k).lo <=
        rationalCircleSin u /\
      rationalCircleSin u <= (dyadicNestedRadicalStageSinAt n k).hi) :
    QInterval.Overlaps
      ((sinPiRawOfArctan B x hx).compute n)
      (dyadicNestedRadicalStageSinAt n k) := by
  have hS : subintervalOf (dyadicNestedRadicalStageSinAt n k) 0 1 := by
    simpa [dyadicNestedRadicalStageSinAt, dyadicNestedRadicalStageTable] using
      (dyadicNestedRadicalTableAt_bounds n n k hk).1
  exact arctanSinPi_sample_overlap_of_tangent_witness
    B hx n (dyadicNestedRadicalStageSinAt n k) hS u hu himage

/-! The narrow-box search is the concrete transport interface for the
nested-radical sample theorem.  Its only finite input is a successful checked
search; the preceding localized-grid theorem supplies such a success from an
overlap and a mesh bound. -/
theorem arctanSinPi_nestedRadicalStage_sample_overlap_of_box_search
    (B : IntegralIdentities.ArctanInverseBisection)
    {x : Rat} (hx : 0 <= x /\ x <= (1 : Rat) / 2)
    (ht : RationalCircle.GeometricTrig.firstQuadrantBranch (2 * x))
    (n k m : Nat) (hk : k <= 2 ^ n) (u : Rat)
    (hsearch : rationalTangentWitnessBoxSearch
      (B.tangentRaw.compute (2 * x) ht n)
      (dyadicNestedRadicalStageSinAt n k) m = some u) :
    QInterval.Overlaps
      ((sinPiRawOfArctan B x hx).compute n)
      (dyadicNestedRadicalStageSinAt n k) := by
  have hw := rationalTangentWitnessBoxSearch_sound_inequalities hsearch
  apply arctanSinPi_nestedRadicalStage_sample_overlap_of_tangent_witness
    B hx n k hk u
  · exact ⟨by simpa using hw.1, by simpa using hw.2.1⟩
  · exact ⟨hw.2.2.1, hw.2.2.2⟩

theorem arctanSinPi_nestedRadicalStage_sample_overlap_of_canonical_box_search
    (B : IntegralIdentities.ArctanInverseBisection)
    {n k : Nat} (hk : k < 2 ^ n) (m : Nat) (u : Rat)
    (hsearch : rationalTangentWitnessBoxSearch
      (dyadicTangentBox B hk)
      (dyadicNestedRadicalStageSinAt n k) m = some u) :
    QInterval.Overlaps
      ((sinPiRawOfArctan B
        (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k)
        (dyadicHalfDomain hk)).compute n)
      (dyadicNestedRadicalStageSinAt n k) := by
  apply arctanSinPi_nestedRadicalStage_sample_overlap_of_box_search
    B (dyadicHalfDomain hk) (dyadicNormalizedBranch hk) n k m
    (Nat.le_of_lt hk) u
  simpa [dyadicTangentBox] using hsearch

theorem arctanSinPi_nestedRadicalSample_overlap_of_box_search_at
    (B : IntegralIdentities.ArctanInverseBisection)
    {depth k : Nat} (hk : k < 2 ^ depth)
    (precision m : Nat) (u : Rat)
    (hsearch : rationalTangentWitnessBoxSearch
      (dyadicTangentBoxAt B precision depth k hk)
      (dyadicNestedRadicalTableAt precision depth k).1 m = some u) :
    QInterval.Overlaps
      ((sinPiRawOfArctan B
        (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
        (dyadicHalfDomain hk)).compute precision)
      ((dyadicNestedRadicalTableAt precision depth k).1) := by
  have hw := rationalTangentWitnessBoxSearch_sound_inequalities hsearch
  have hS : subintervalOf
      ((dyadicNestedRadicalTableAt precision depth k).1) 0 1 :=
    (dyadicNestedRadicalTableAt_bounds precision depth k
      (Nat.le_of_lt hk)).1
  have htan :
      (B.tangentRaw.compute
        (2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
        (dyadicNormalizedBranch hk) precision).lo <= u /\
      u <= (B.tangentRaw.compute
        (2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
        (dyadicNormalizedBranch hk) precision).hi := by
    simpa [dyadicTangentBoxAt] using And.intro hw.1 hw.2.1
  apply arctanSinPi_sample_overlap_of_tangent_witness
    B (dyadicHalfDomain hk) precision
    (dyadicNestedRadicalTableAt precision depth k).1 hS u htan
  exact ⟨hw.2.2.1, hw.2.2.2⟩

structure DyadicTangentWitnessSchedule
    (B : IntegralIdentities.ArctanInverseBisection)
    (depth k : Nat) (hk : k < 2 ^ depth) where
  witness : Nat -> Rat
  searchPrecision : Nat -> Nat
  search : forall precision,
    rationalTangentWitnessBoxSearch
      (dyadicTangentBoxAt B precision depth k hk)
      (dyadicNestedRadicalTableAt precision depth k).1
      (searchPrecision precision) = some (witness precision)

theorem DyadicTangentWitnessSchedule.to_sample_overlap
    {B : IntegralIdentities.ArctanInverseBisection}
    {depth k : Nat} {hk : k < 2 ^ depth}
    (d : DyadicTangentWitnessSchedule B depth k hk)
    (precision : Nat) :
    QInterval.Overlaps
      ((sinPiRawOfArctan B
        (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
        (dyadicHalfDomain hk)).compute precision)
      ((dyadicNestedRadicalTableAt precision depth k).1) := by
  exact arctanSinPi_nestedRadicalSample_overlap_of_box_search_at
    B hk precision (d.searchPrecision precision) (d.witness precision)
    (d.search precision)

theorem arctanSinPi_nestedRadicalSample_equiv_of_search_family
    (B : IntegralIdentities.ArctanInverseBisection)
    {depth k : Nat} (hk : k < 2 ^ depth)
    (hsearch : forall precision,
      ∃ m u, rationalTangentWitnessBoxSearch
        (dyadicTangentBoxAt B precision depth k hk)
        (dyadicNestedRadicalTableAt precision depth k).1 m = some u) :
    (sinPiRawOfArctan B
      (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
      (dyadicHalfDomain hk)).Equiv
      (dyadicNestedRadicalSampleRaw depth k) := by
  apply RealCompute.sameStageOverlap_equiv
  intro precision
  obtain ⟨m, u, hu⟩ := hsearch precision
  apply (RealCompute.compareAt_overlap_iff
    (sinPiRawOfArctan B
      (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
      (dyadicHalfDomain hk))
    (dyadicNestedRadicalSampleRaw depth k) precision precision).2
  simpa [dyadicNestedRadicalSampleRaw] using
    arctanSinPi_nestedRadicalSample_overlap_of_box_search_at
      B hk precision m u hu

theorem arctanSinPi_nestedRadicalSample_equiv_of_witness_schedule
    {B : IntegralIdentities.ArctanInverseBisection}
    {depth k : Nat} {hk : k < 2 ^ depth}
    (d : DyadicTangentWitnessSchedule B depth k hk) :
    (sinPiRawOfArctan B
      (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
      (dyadicHalfDomain hk)).Equiv
      (dyadicNestedRadicalSampleRaw depth k) := by
  apply arctanSinPi_nestedRadicalSample_equiv_of_search_family B hk
  intro precision
  exact ⟨d.searchPrecision precision, d.witness precision,
    d.search precision⟩

/-! A direct public-integral adapter for the canonical dyadic searches.  This
form is intentionally smaller than `DyadicNestedRadicalRoute`: it exposes only
the finite facts an evaluator implementer must provide at the sampled points.
The proof is entirely stagewise and uses the fixed equal-dyadic plan. -/
theorem ArctanSinPiConstruction.halfIntegral_equiv_of_canonical_nestedRadical_search
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (hsearch : forall n k (hk : k < (pub.plan n).subdivisions),
      ∃ m u, rationalTangentWitnessBoxSearch
        (dyadicTangentBox S.inverse (by
          simpa [hdyadic, Integral.staticDyadicPlan,
            Integral.staticDyadicSubdivisions] using hk))
        (dyadicNestedRadicalStageSinAt n k) m = some u) :
    (S.halfIntegral pub).Equiv
      (Integral.sampleValue g 0 ((1 : Rat) / 2) cg) := by
  apply Integral.integral_equiv_of_plan_and_sample_overlaps
    (by decide +kernel : (0 : Rat) <= (1 : Rat) / 2)
    pub cg hplan
  intro n k hk
  obtain ⟨m, u, hu⟩ := hsearch n k hk
  have hover := arctanSinPi_nestedRadicalStage_sample_overlap_of_canonical_box_search
    S.inverse
    (by simpa [hdyadic, Integral.staticDyadicPlan,
      Integral.staticDyadicSubdivisions] using hk) m u hu
  have he := hevaluator n k hk
  rw [he]
  have hk' : k < 2 ^ n := by
    simpa [hdyadic, Integral.staticDyadicPlan,
      Integral.staticDyadicSubdivisions] using hk
  have hxdy := dyadicHalfDomain hk'
  simp only [hdyadic, Integral.staticDyadicPlan,
    Integral.staticDyadicSubdivisions]
  rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
    S.onHalf hxdy n]
  change QInterval.Overlaps
    ((sinPiRawOfArctan S.inverse
      (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k) hxdy).compute n)
    (dyadicNestedRadicalStageSinAt n k)
  exact hover

/-! Semantic form of the same bridge.  The remaining half-angle theorem may
be proved directly as an equivalence of raw computations, without first
constructing a rational tangent witness.  At the public integral level only
the stagewise overlap is used; this is useful when the geometric proof is
more naturally stated as an induction on the nested-radical table. -/
theorem ArctanSinPiConstruction.halfIntegral_equiv_of_nestedRadical_semantics
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (hsemantic : forall n k (hk : k < (pub.plan n).subdivisions),
      (sinPiRawOfArctan S.inverse
        (leftPoint 0 ((1 : Rat) / 2)
          (2 ^ n) k) (dyadicHalfDomain (by
            simpa [hdyadic, Integral.staticDyadicPlan,
              Integral.staticDyadicSubdivisions] using hk))).Equiv
        { compute := fun _ => dyadicNestedRadicalStageSinAt n k }) :
    (S.halfIntegral pub).Equiv
      (Integral.sampleValue g 0 ((1 : Rat) / 2) cg) := by
  apply Integral.integral_equiv_of_plan_and_sample_overlaps
    (by decide +kernel : (0 : Rat) <= (1 : Rat) / 2)
    pub cg hplan
  intro n k hk
  have he := hevaluator n k hk
  rw [he]
  have hk' : k < 2 ^ n := by
    simpa [hdyadic, Integral.staticDyadicPlan,
      Integral.staticDyadicSubdivisions] using hk
  have hsem := hsemantic n k hk
  have hover := (RealCompute.compareAt_overlap_iff
    (sinPiRawOfArctan S.inverse
      (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k)
      (dyadicHalfDomain hk'))
    { compute := fun _ => dyadicNestedRadicalStageSinAt n k } n n).1
    (hsem n)
  simp only [hdyadic, Integral.staticDyadicPlan,
    Integral.staticDyadicSubdivisions]
  rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
    S.onHalf (dyadicHalfDomain hk') n]
  exact hover

theorem ArctanSinPiConstruction.halfIntegral_equiv_of_precisionAware_nestedRadical_semantics
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
      dyadicNestedRadicalStageSinAt n k)
    (hsemantic : forall (n k : Nat) (hk : k < 2 ^ n),
      (sinPiRawOfArctan S.inverse
        (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k)
        (dyadicHalfDomain hk)).Equiv
        (dyadicNestedRadicalSampleRaw n k)) :
    (S.halfIntegral pub).Equiv
      (Integral.sampleValue g 0 ((1 : Rat) / 2) cg) := by
  apply Integral.integral_equiv_of_plan_and_sample_overlaps
    (by decide +kernel : (0 : Rat) <= (1 : Rat) / 2)
    pub cg hplan
  intro n k hk
  have he := hevaluator n k hk
  rw [he]
  have hk' : k < 2 ^ n := by
    simpa [hdyadic, Integral.staticDyadicPlan,
      Integral.staticDyadicSubdivisions] using hk
  have hsem := hsemantic n k hk'
  have hover := (RealCompute.compareAt_overlap_iff
    (sinPiRawOfArctan S.inverse
      (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k)
      (dyadicHalfDomain hk'))
    (dyadicNestedRadicalSampleRaw n k) n n).1
    (hsem n)
  simp only [hdyadic, Integral.staticDyadicPlan,
    Integral.staticDyadicSubdivisions]
  rw [FunctionOnInterval.toRealFunRaw_compute_of_mem
    S.onHalf (dyadicHalfDomain hk') n]
  change QInterval.Overlaps
    ((sinPiRawOfArctan S.inverse
      (leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k)
      (dyadicHalfDomain hk')).compute n)
    (dyadicNestedRadicalTableAt n n k).1
  simpa [dyadicNestedRadicalSampleRaw,
    dyadicNestedRadicalStageSinAt, dyadicNestedRadicalStageTable] using hover

theorem dyadicNestedRadicalTableAt_sin_width_pos
    (precision n k : Nat) (hk : k < 2 ^ n) (hpos : 0 < k) :
    0 < (dyadicNestedRadicalTableAt precision n k).1.width := by
  induction n generalizing precision k with
  | zero => omega
  | succ n ih =>
      by_cases he : k % 2 = 0
      · have hkrep : k = 2 * (k / 2) := by omega
        have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
          rw [Nat.pow_succ]
          omega
        have hhalf : k / 2 < 2 ^ n := by
          rw [hpow] at hk
          omega
        have hpos' : 0 < k / 2 := by omega
        rw [hkrep]
        simp [dyadicNestedRadicalTableAt]
        exact ih (dyadicNestedRadicalParentPrecision precision)
          (k / 2) hhalf hpos'
      · let bound := 2 ^ n
        let parentPrecision := dyadicNestedRadicalParentPrecision precision
        let reflected := if k <= bound then k else 2 * bound - k
        have hpow : 2 ^ (n + 1) = 2 * bound := by
          dsimp [bound]
          rw [Nat.pow_succ]
          omega
        have hkbound : k <= 2 * bound := by
          rw [← hpow]
          exact Nat.le_of_lt hk
        have hreflect : reflected <= bound := by
          dsimp [reflected]
          split <;> omega
        have hbounds := dyadicNestedRadicalTableAt_bounds
          parentPrecision n reflected hreflect
        let parentCos :=
          if k <= bound then
            (dyadicNestedRadicalTableAt parentPrecision n reflected).2
          else
            dyadicNestedRadicalNeg
              (dyadicNestedRadicalTableAt parentPrecision n reflected).2
        have hparentCos : subintervalOf parentCos (-1) 1 := by
          by_cases hle : k <= bound
          · simpa [parentCos, hle] using hbounds.2
          · have hneg := dyadicNestedRadicalNeg_unit_subinterval
              (dyadicNestedRadicalTableAt parentPrecision n reflected).2 hbounds.2
            simpa [parentCos, hle] using hneg
        have hinput := dyadicHalfAngleSinInput_subinterval
          parentCos hparentCos
        by_cases hle : k <= bound
        · simp [dyadicNestedRadicalTableAt, he, bound, reflected, hle]
          have hpc : parentCos =
              (dyadicNestedRadicalTableAt parentPrecision n k).2 := by
            simp [parentCos, parentPrecision, bound, reflected, hle]
          rw [hpc] at hinput
          exact sqrtOnUnitEvalIntervalClipped_width_pos
            (dyadicHalfAngleSinInput
              (dyadicNestedRadicalTableAt parentPrecision n k).2)
            hinput precision
        · simp [dyadicNestedRadicalTableAt, he, bound, reflected, hle]
          have hpc : parentCos = dyadicNestedRadicalNeg
              (dyadicNestedRadicalTableAt parentPrecision n (2 * bound - k)).2 := by
            simp [parentCos, parentPrecision, bound, reflected, hle]
          rw [hpc] at hinput
          exact sqrtOnUnitEvalIntervalClipped_width_pos
            (dyadicHalfAngleSinInput
              (dyadicNestedRadicalNeg
                (dyadicNestedRadicalTableAt parentPrecision n (2 * bound - k)).2))
            hinput precision

theorem dyadicNestedRadicalStageSinAt_width_pos
    {n k : Nat} (hk : k < 2 ^ n) (hpos : 0 < k) :
    0 < (dyadicNestedRadicalStageSinAt n k).width := by
  exact dyadicNestedRadicalTableAt_sin_width_pos n n k hk hpos

theorem canonical_dyadic_overlap_of_halfAngle_outer_tangent
    (B : IntegralIdentities.ArctanInverseBisection)
    {n k : Nat} (hk : k < 2 ^ n)
    {C : QInterval} (hC : subintervalOf C 0 1)
    {s c : Rat}
    (houter : (dyadicTangentBox B hk).ContainsInterval
      (rationalHalfAngleTangentInterval
        (dyadicNestedRadicalStageSinAt n k)
        C))
    (hs : 0 <= s) (hc : 0 <= c)
    (hcircle : s * s + c * c = 1)
    (hsS : (dyadicNestedRadicalStageSinAt n k).lo <= s /\
      s <= (dyadicNestedRadicalStageSinAt n k).hi)
    (hcC : C.lo <= c /\ c <= C.hi) :
    QInterval.Overlaps
    (rationalCircleSinInterval (dyadicTangentBox B hk))
      (dyadicNestedRadicalStageSinAt n k) := by
  apply rationalCircleSinInterval_overlap_of_halfAngle_boxes_of_outer_tangent
    (dyadicTangentBox_bounds B hk)
    (by
      exact (dyadicNestedRadicalTableAt_bounds n n k
        (Nat.le_of_lt hk)).1)
    hC houter hs hc hcircle hsS hcC

/-! A named, finite certificate for one interior dyadic cell.  The
certificate deliberately contains only rational boxes and rational algebra:
`C` encloses the companion cosine, `(s,c)` is a rational point on the unit
circle, and `houter` places the resulting half-angle tangent box inside the
inverse tangent box.  No completed real number or continuity theorem is
hidden in this interface. -/
structure CanonicalDyadicHalfAngleCertificate
    (B : IntegralIdentities.ArctanInverseBisection)
    (n k : Nat) (hk : k < 2 ^ n) where
  cosineBox : QInterval
  cosineBox_subinterval : subintervalOf cosineBox 0 1
  sineWitness : Rat
  cosineWitness : Rat
  sine_nonneg : 0 <= sineWitness
  cosine_nonneg : 0 <= cosineWitness
  circle_identity :
    sineWitness * sineWitness + cosineWitness * cosineWitness = 1
  sine_contains :
    (dyadicNestedRadicalStageSinAt n k).lo <= sineWitness /\
      sineWitness <= (dyadicNestedRadicalStageSinAt n k).hi
  cosine_contains :
    cosineBox.lo <= cosineWitness /\ cosineWitness <= cosineBox.hi
  outer_tangent_contains :
    (dyadicTangentBox B hk).ContainsInterval
      (rationalHalfAngleTangentInterval
        (dyadicNestedRadicalStageSinAt n k) cosineBox)

theorem canonical_dyadic_overlap_of_halfAngle_outer_tangent_at
    (B : IntegralIdentities.ArctanInverseBisection)
    {precision depth k : Nat} (hk : k < 2 ^ depth)
    {C : QInterval} (hC : subintervalOf C 0 1)
    {s c : Rat}
    (houter : (dyadicTangentBoxAt B precision depth k hk).ContainsInterval
      (rationalHalfAngleTangentInterval
        ((dyadicNestedRadicalTableAt precision depth k).1) C))
    (hs : 0 <= s) (hc : 0 <= c)
    (hcircle : s * s + c * c = 1)
    (hsS : (dyadicNestedRadicalTableAt precision depth k).1.lo <= s /\
      s <= (dyadicNestedRadicalTableAt precision depth k).1.hi)
    (hcC : C.lo <= c /\ c <= C.hi) :
    QInterval.Overlaps
      (rationalCircleSinInterval
        (dyadicTangentBoxAt B precision depth k hk))
      ((dyadicNestedRadicalTableAt precision depth k).1) := by
  apply rationalCircleSinInterval_overlap_of_halfAngle_boxes_of_outer_tangent
    (dyadicTangentBoxAt_bounds B precision depth k hk)
    (dyadicNestedRadicalTableAt_bounds precision depth k
      (Nat.le_of_lt hk)).1
    hC houter hs hc hcircle hsS hcC

structure CanonicalDyadicHalfAngleCertificateAt
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision depth k : Nat) (hk : k < 2 ^ depth) where
  cosineBox : QInterval
  cosineBox_subinterval : subintervalOf cosineBox 0 1
  sineWitness : Rat
  cosineWitness : Rat
  sine_nonneg : 0 <= sineWitness
  cosine_nonneg : 0 <= cosineWitness
  circle_identity :
    sineWitness * sineWitness + cosineWitness * cosineWitness = 1
  sine_contains :
    (dyadicNestedRadicalTableAt precision depth k).1.lo <= sineWitness /\
      sineWitness <= (dyadicNestedRadicalTableAt precision depth k).1.hi
  cosine_contains :
    cosineBox.lo <= cosineWitness /\ cosineWitness <= cosineBox.hi
  outer_tangent_contains :
    (dyadicTangentBoxAt B precision depth k hk).ContainsInterval
      (rationalHalfAngleTangentInterval
        ((dyadicNestedRadicalTableAt precision depth k).1) cosineBox)

/- At the native precision `n`, the precision-aware evaluator is exactly the
   public stage evaluator.  This small bridge keeps the geometric proof
   parameterized by precision while exposing the certificate shape consumed
   by the equal-dyadic integral. -/
def canonical_dyadic_halfAngle_certificate_of_native_precision
    (B : IntegralIdentities.ArctanInverseBisection)
    {n k : Nat} {hk : k < 2 ^ n}
    (h : CanonicalDyadicHalfAngleCertificateAt B n n k hk) :
    CanonicalDyadicHalfAngleCertificate B n k hk := by
  exact {
    cosineBox := h.cosineBox
    cosineBox_subinterval := h.cosineBox_subinterval
    sineWitness := h.sineWitness
    cosineWitness := h.cosineWitness
    sine_nonneg := h.sine_nonneg
    cosine_nonneg := h.cosine_nonneg
    circle_identity := h.circle_identity
    sine_contains := h.sine_contains
    cosine_contains := h.cosine_contains
    outer_tangent_contains := h.outer_tangent_contains }

def canonical_dyadic_halfAngle_certificate_family_of_precision_family
    (B : IntegralIdentities.ArctanInverseBisection)
    (hcertificate : forall (precision n k : Nat) (hk : k < 2 ^ n),
      0 < k -> CanonicalDyadicHalfAngleCertificateAt B precision n k hk) :
    forall (n k : Nat) (hk : k < 2 ^ n),
      0 < k -> CanonicalDyadicHalfAngleCertificate B n k hk := by
  intro n k hk hpos
  exact canonical_dyadic_halfAngle_certificate_of_native_precision B
    (hcertificate n n k hk hpos)

def canonical_dyadic_certificate_at_of_rational_witness
    (B : IntegralIdentities.ArctanInverseBisection)
    {precision depth k : Nat} (hk : k < 2 ^ depth)
    (u : Rat)
    (hu0 : 0 <= u) (hu1 : u <= 1)
    (hsine : (dyadicNestedRadicalTableAt precision depth k).1.lo <=
        rationalCircleSin u /\
      rationalCircleSin u <=
        (dyadicNestedRadicalTableAt precision depth k).1.hi)
    (houter : (dyadicTangentBoxAt B precision depth k hk).ContainsInterval
      (rationalHalfAngleTangentInterval
        ((dyadicNestedRadicalTableAt precision depth k).1)
        { lo := rationalCircleCos u, hi := rationalCircleCos u })) :
    CanonicalDyadicHalfAngleCertificateAt B precision depth k hk := by
  have hsc := rationalCircleSin_bounds hu0 hu1
  have hcc := rationalCircleCos_bounds hu0 hu1
  refine ⟨({ lo := rationalCircleCos u, hi := rationalCircleCos u } : QInterval),
    ?_, rationalCircleSin u, rationalCircleCos u, hsc.1, hcc.1,
    rationalCircleSin_sq_add_cos_sq u, hsine, ?_, houter⟩
  · exact ⟨hcc.1, Rat.le_refl, hcc.2⟩
  · exact ⟨Rat.le_refl, Rat.le_refl⟩

def canonicalDyadicCertificateAdmissibleBool
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision depth k : Nat) (hk : k < 2 ^ depth) (u : Rat) : Bool :=
  (0 <= u) && (u <= 1) &&
    ((dyadicNestedRadicalTableAt precision depth k).1.lo <=
      rationalCircleSin u) &&
    (rationalCircleSin u <=
      (dyadicNestedRadicalTableAt precision depth k).1.hi) &&
    ((dyadicTangentBoxAt B precision depth k hk).lo <=
      (rationalHalfAngleTangentInterval
        ((dyadicNestedRadicalTableAt precision depth k).1)
        ({ lo := rationalCircleCos u, hi := rationalCircleCos u } : QInterval)).lo) &&
    ((rationalHalfAngleTangentInterval
        ((dyadicNestedRadicalTableAt precision depth k).1)
        ({ lo := rationalCircleCos u, hi := rationalCircleCos u } : QInterval)).hi <=
      (dyadicTangentBoxAt B precision depth k hk).hi)

def canonicalDyadicCertificateSearchAt
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision depth k : Nat) (hk : k < 2 ^ depth)
    (candidates : List Rat) : Option Rat :=
  match candidates with
  | [] => none
  | u :: rest =>
      match canonicalDyadicCertificateAdmissibleBool B precision depth k hk u with
      | true =>
        some u
      | false =>
        canonicalDyadicCertificateSearchAt B precision depth k hk rest

noncomputable def canonicalDyadicCertificateSearchAt_sound
    (B : IntegralIdentities.ArctanInverseBisection)
    {precision depth k : Nat} {hk : k < 2 ^ depth}
    {candidates : List Rat} {u : Rat}
    (hsearch : canonicalDyadicCertificateSearchAt
      B precision depth k hk candidates = some u) :
    CanonicalDyadicHalfAngleCertificateAt B precision depth k hk := by
  induction candidates with
  | nil =>
      simp [canonicalDyadicCertificateSearchAt] at hsearch
  | cons v rest ih =>
      by_cases hadm :
          canonicalDyadicCertificateAdmissibleBool B precision depth k hk v = true
      · have huv : v = u := by
          simpa [canonicalDyadicCertificateSearchAt, hadm] using hsearch
        subst u
        simp only [canonicalDyadicCertificateAdmissibleBool,
          Bool.and_eq_true] at hadm
        apply canonical_dyadic_certificate_at_of_rational_witness
          B hk v
        · exact of_decide_eq_true hadm.1.1.1.1.1
        · exact of_decide_eq_true hadm.1.1.1.1.2
        · exact ⟨of_decide_eq_true hadm.1.1.1.2,
            of_decide_eq_true hadm.1.1.2⟩
        · unfold QInterval.ContainsInterval
          exact ⟨of_decide_eq_true hadm.1.2,
            of_decide_eq_true hadm.2⟩
      · apply ih
        simpa [canonicalDyadicCertificateSearchAt, hadm] using hsearch

theorem canonical_dyadic_search_of_halfAngle_certificate_at
    (B : IntegralIdentities.ArctanInverseBisection)
    {precision depth k : Nat} {hk : k < 2 ^ depth} (hpos : 0 < k)
    (h : CanonicalDyadicHalfAngleCertificateAt B precision depth k hk) :
    ∃ m u, rationalTangentWitnessBoxSearch
      (dyadicTangentBoxAt B precision depth k hk)
      (dyadicNestedRadicalTableAt precision depth k).1 m = some u := by
  have hover : QInterval.Overlaps
      (rationalCircleSinInterval
        (dyadicTangentBoxAt B precision depth k hk))
      ((dyadicNestedRadicalTableAt precision depth k).1) :=
    canonical_dyadic_overlap_of_halfAngle_outer_tangent_at B hk
      h.cosineBox_subinterval h.outer_tangent_contains
      h.sine_nonneg h.cosine_nonneg h.circle_identity
      h.sine_contains h.cosine_contains
  apply exists_rationalTangentWitnessBoxSearch_of_overlap_of_positive_width
    (dyadicTangentBoxAt_bounds B precision depth k hk)
  · exact (dyadicNestedRadicalTableAt_bounds precision depth k
      (Nat.le_of_lt hk)).1
  · exact hover
  · exact dyadicNestedRadicalTableAt_sin_width_pos
      precision depth k hk hpos

theorem canonical_dyadic_search_of_halfAngle_certificate_at_family
    (B : IntegralIdentities.ArctanInverseBisection)
    {depth k : Nat} (hk : k < 2 ^ depth) (hpos : 0 < k)
    (hcertificate : forall precision,
      CanonicalDyadicHalfAngleCertificateAt B precision depth k hk) :
    forall precision, ∃ m u, rationalTangentWitnessBoxSearch
      (dyadicTangentBoxAt B precision depth k hk)
      (dyadicNestedRadicalTableAt precision depth k).1 m = some u := by
  intro precision
  exact canonical_dyadic_search_of_halfAngle_certificate_at B hpos
    (hcertificate precision)

theorem canonical_dyadic_search_of_overlap_at
    (B : IntegralIdentities.ArctanInverseBisection)
    {precision depth k : Nat} (hk : k < 2 ^ depth) (hpos : 0 < k)
    (hover : QInterval.Overlaps
      (rationalCircleSinInterval
        (dyadicTangentBoxAt B precision depth k hk))
      ((dyadicNestedRadicalTableAt precision depth k).1)) :
    ∃ m u, rationalTangentWitnessBoxSearch
      (dyadicTangentBoxAt B precision depth k hk)
      (dyadicNestedRadicalTableAt precision depth k).1 m = some u := by
  apply exists_rationalTangentWitnessBoxSearch_of_overlap_of_positive_width
    (dyadicTangentBoxAt_bounds B precision depth k hk)
  · exact (dyadicNestedRadicalTableAt_bounds precision depth k
      (Nat.le_of_lt hk)).1
  · exact hover
  · exact dyadicNestedRadicalTableAt_sin_width_pos
      precision depth k hk hpos

theorem canonical_dyadic_search_of_overlap_at_family
    (B : IntegralIdentities.ArctanInverseBisection)
    {depth k : Nat} (hk : k < 2 ^ depth) (hpos : 0 < k)
    (hover : forall precision, QInterval.Overlaps
      (rationalCircleSinInterval
        (dyadicTangentBoxAt B precision depth k hk))
      ((dyadicNestedRadicalTableAt precision depth k).1)) :
    forall precision, ∃ m u, rationalTangentWitnessBoxSearch
      (dyadicTangentBoxAt B precision depth k hk)
      (dyadicNestedRadicalTableAt precision depth k).1 m = some u := by
  intro precision
  exact canonical_dyadic_search_of_overlap_at B hk hpos
    (hover precision)

theorem arctanSinPi_nestedRadicalSample_equiv_of_overlap_family
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    {depth k : Nat} (hk : k < 2 ^ depth)
    (hover : 0 < k -> forall precision, QInterval.Overlaps
      (rationalCircleSinInterval
        (dyadicTangentBoxAt B precision depth k hk))
      ((dyadicNestedRadicalTableAt precision depth k).1)) :
    (sinPiRawOfArctan B
      (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
      (dyadicHalfDomain hk)).Equiv
      (dyadicNestedRadicalSampleRaw depth k) := by
  apply arctanSinPi_nestedRadicalSample_equiv_of_search_family B hk
  intro precision
  by_cases hkzero : k = 0
  · subst k
    obtain ⟨u, hu⟩ := canonical_dyadic_zero_search_at B ht0 precision depth
      (Nat.pow_pos (by omega : 0 < 2))
    have hzero : forall (precision level : Nat),
        (dyadicNestedRadicalTableAt precision level 0).1 =
          ({ lo := 0, hi := 0 } : QInterval) := by
      intro precision level
      induction level generalizing precision with
      | zero => simp [dyadicNestedRadicalTableAt]
      | succ level ih =>
          simp [dyadicNestedRadicalTableAt]
          exact ih (dyadicNestedRadicalParentPrecision precision)
    exact ⟨0, u, by simpa [hzero] using hu⟩
  · exact canonical_dyadic_search_of_overlap_at B hk (by omega)
      (hover (by omega) precision)

theorem dyadicNestedRadicalTableAt_zero_sin
    (precision depth : Nat) :
    (dyadicNestedRadicalTableAt precision depth 0).1 =
      ({ lo := 0, hi := 0 } : QInterval) := by
  induction depth generalizing precision with
  | zero => simp [dyadicNestedRadicalTableAt]
  | succ depth ih =>
      simp [dyadicNestedRadicalTableAt]
      exact ih (dyadicNestedRadicalParentPrecision precision)

theorem dyadicNestedRadical_zero_sample_overlap_of_endpoint
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    (precision depth : Nat) (hk : 0 < 2 ^ depth) :
    QInterval.Overlaps
      ((sinPiRawOfArctan B
        (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) 0)
        (dyadicHalfDomain (by omega))).compute precision)
      (dyadicNestedRadicalTableAt precision depth 0).1 := by
  obtain ⟨u, hu⟩ := canonical_dyadic_zero_search_at B ht0 precision depth hk
  have hu' : rationalTangentWitnessBoxSearch
      (dyadicTangentBoxAt B precision depth 0 hk)
      (dyadicNestedRadicalTableAt precision depth 0).1 0 = some u := by
    simpa [dyadicNestedRadicalTableAt_zero_sin] using hu
  have hbox := arctanSinPi_nestedRadicalSample_overlap_of_box_search_at
    B (by omega : 0 < 2 ^ depth) precision 0 u hu'
  simpa [dyadicNestedRadicalTableAt_zero_sin] using hbox

theorem canonical_dyadic_search_at_family
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    {depth k : Nat} (hk : k < 2 ^ depth)
    (hcertificate : 0 < k -> forall precision,
      CanonicalDyadicHalfAngleCertificateAt B precision depth k hk) :
    forall precision, ∃ m u, rationalTangentWitnessBoxSearch
      (dyadicTangentBoxAt B precision depth k hk)
      (dyadicNestedRadicalTableAt precision depth k).1 m = some u := by
  intro precision
  by_cases hkzero : k = 0
  · subst k
    obtain ⟨u, hu⟩ := canonical_dyadic_zero_search_at B ht0 precision depth
      (Nat.pow_pos (by omega : 0 < 2))
    have hzero := dyadicNestedRadicalTableAt_zero_sin precision depth
    exact ⟨0, u, by simpa [hzero] using hu⟩
  · exact canonical_dyadic_search_of_halfAngle_certificate_at B
      (by omega) (hcertificate (by omega) precision)

theorem arctanSinPi_nestedRadicalSample_equiv_of_certificate_family
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    {depth k : Nat} (hk : k < 2 ^ depth)
    (hcertificate : 0 < k -> forall precision,
      CanonicalDyadicHalfAngleCertificateAt B precision depth k hk) :
    (sinPiRawOfArctan B
      (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
      (dyadicHalfDomain hk)).Equiv
      (dyadicNestedRadicalSampleRaw depth k) := by
  apply arctanSinPi_nestedRadicalSample_equiv_of_search_family B hk
  exact canonical_dyadic_search_at_family B ht0 hk hcertificate

theorem canonical_dyadic_search_of_overlap_of_positive_width
    (B : IntegralIdentities.ArctanInverseBisection)
    {n k : Nat} (hk : k < 2 ^ n)
    (hover : QInterval.Overlaps
      (rationalCircleSinInterval (dyadicTangentBox B hk))
      (dyadicNestedRadicalStageSinAt n k))
    (hwidth : 0 < (dyadicNestedRadicalStageSinAt n k).width) :
    ∃ m u, rationalTangentWitnessBoxSearch
      (dyadicTangentBox B hk)
      (dyadicNestedRadicalStageSinAt n k) m = some u := by
  apply exists_rationalTangentWitnessBoxSearch_of_overlap_of_positive_width
    (dyadicTangentBox_bounds B hk)
  · exact (dyadicNestedRadicalTableAt_bounds n n k (Nat.le_of_lt hk)).1
  · exact hover
  · exact hwidth

theorem canonical_dyadic_search_of_overlap_of_interior
    (B : IntegralIdentities.ArctanInverseBisection)
    {n k : Nat} (hk : k < 2 ^ n) (hpos : 0 < k)
    (hover : QInterval.Overlaps
      (rationalCircleSinInterval (dyadicTangentBox B hk))
      (dyadicNestedRadicalStageSinAt n k)) :
    ∃ m u, rationalTangentWitnessBoxSearch
      (dyadicTangentBox B hk)
      (dyadicNestedRadicalStageSinAt n k) m = some u := by
  exact canonical_dyadic_search_of_overlap_of_positive_width B hk hover
    (dyadicNestedRadicalStageSinAt_width_pos hk hpos)

theorem canonical_dyadic_search_of_halfAngle_certificate
    (B : IntegralIdentities.ArctanInverseBisection)
    {n k : Nat} {hk : k < 2 ^ n} (hpos : 0 < k)
    (h : CanonicalDyadicHalfAngleCertificate B n k hk) :
    ∃ m u, rationalTangentWitnessBoxSearch
      (dyadicTangentBox B hk)
      (dyadicNestedRadicalStageSinAt n k) m = some u := by
  have hover : QInterval.Overlaps
      (rationalCircleSinInterval (dyadicTangentBox B hk))
      (dyadicNestedRadicalStageSinAt n k) :=
    canonical_dyadic_overlap_of_halfAngle_outer_tangent B hk
      h.cosineBox_subinterval h.outer_tangent_contains
      h.sine_nonneg h.cosine_nonneg h.circle_identity
      h.sine_contains h.cosine_contains
  exact canonical_dyadic_search_of_overlap_of_interior B hk hpos hover

/-! A family-level adapter for the equal-dyadic integral.  The endpoint
`k = 0` is exact and uses the zero-target search; every other sampled cell is
handled by one finite rational half-angle certificate.  This is the precise
finite obligation left to the nested-radical semantic proof. -/

theorem canonical_dyadic_search_of_halfAngle_certificate_family
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    (hcertificate : forall (n k : Nat) (hk : k < 2 ^ n),
      0 < k -> CanonicalDyadicHalfAngleCertificate B n k hk) :
    forall (n k : Nat) (hk : k < 2 ^ n),
      ∃ m u, rationalTangentWitnessBoxSearch
        (dyadicTangentBox B hk)
        (dyadicNestedRadicalStageSinAt n k) m = some u := by
  intro n k hk
  by_cases hkzero : k = 0
  · subst k
    obtain ⟨u, hu⟩ := canonical_dyadic_zero_search B ht0 n
    have hzero : forall (precision level : Nat),
        (dyadicNestedRadicalTableAt precision level 0).1 =
          ({ lo := 0, hi := 0 } : QInterval) := by
      intro precision level
      induction level generalizing precision with
      | zero => simp [dyadicNestedRadicalTableAt]
      | succ level ih =>
          simp [dyadicNestedRadicalTableAt]
          exact ih (dyadicNestedRadicalParentPrecision precision)
    have hstage : dyadicNestedRadicalStageSinAt n 0 =
        ({ lo := 0, hi := 0 } : QInterval) := by
      exact hzero n n
    exact ⟨0, u, by simpa [hstage] using hu⟩
  · have hpos : 0 < k := by omega
    exact canonical_dyadic_search_of_halfAngle_certificate B hpos
      (hcertificate n k hk hpos)

theorem ArctanSinPiConstruction.halfIntegral_equiv_of_halfAngle_certificate_family
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    (hcertificate : forall (n k : Nat) (hk : k < 2 ^ n),
      0 < k -> CanonicalDyadicHalfAngleCertificate S.inverse n k hk) :
    (S.halfIntegral pub).Equiv
      (Integral.sampleValue g 0 ((1 : Rat) / 2) cg) := by
  apply S.halfIntegral_equiv_of_canonical_nestedRadical_search
    pub g cg hdyadic hplan hevaluator
  intro n k hk
  have hk' : k < 2 ^ n := by
    simpa [hdyadic, Integral.staticDyadicPlan,
      Integral.staticDyadicSubdivisions] using hk
  obtain ⟨m, u, hu⟩ :=
    canonical_dyadic_search_of_halfAngle_certificate_family
      S.inverse ht0 hcertificate n k hk'
  exact ⟨m, u, by
    simpa [hdyadic, Integral.staticDyadicPlan,
      Integral.staticDyadicSubdivisions] using hu⟩

theorem ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi_of_halfAngle_certificate_family
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    (hcertificate : forall (n k : Nat) (hk : k < 2 ^ n),
      0 < k -> CanonicalDyadicHalfAngleCertificate S.inverse n k hk)
    (hintegral : (Integral.sampleValue g 0 ((1 : Rat) / 2) cg).Equiv
      reciprocalPiRaw) :
    (S.halfIntegral pub).Equiv reciprocalPiRaw := by
  exact RealCompute.equiv_trans
    (S.halfIntegral_valid pub)
    (FTC.integral_valid_of_construction cg)
    reciprocalPiRaw_valid
    (S.halfIntegral_equiv_of_halfAngle_certificate_family
      pub g cg hdyadic hplan hevaluator ht0 hcertificate)
    hintegral

theorem rationalTangentWitnessSearch_stage_one_demo :
    rationalTangentWitnessSearch
      ({ lo := 0, hi := 1 } : QInterval)
      (dyadicNestedRadicalStageSinAt 1 1) 8 = some ((103 : Rat) / 256) := by
  decide +kernel

theorem rationalTangentWitnessSearch_stage_two_demo :
    rationalTangentWitnessSearch
      ({ lo := 0, hi := 1 } : QInterval)
      (dyadicNestedRadicalStageSinAt 2 1) 12 =
      some ((791 : Rat) / 4096) := by
  decide +kernel

theorem dyadicNestedRadicalTableAt_overlap_of_precisions
    (precision₁ precision₂ n k : Nat) (hk : k <= 2 ^ n) :
    QInterval.Overlaps
        (dyadicNestedRadicalTableAt precision₁ n k).1
        (dyadicNestedRadicalTableAt precision₂ n k).1 ∧
      QInterval.Overlaps
        (dyadicNestedRadicalTableAt precision₁ n k).2
        (dyadicNestedRadicalTableAt precision₂ n k).2 := by
  induction n generalizing precision₁ precision₂ k with
  | zero =>
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl <;>
        simp [dyadicNestedRadicalTableAt, QInterval.Overlaps]
  | succ n ih =>
      by_cases he : k % 2 = 0
      · have hkrep : k = 2 * (k / 2) := by omega
        have hhalf : k / 2 <= 2 ^ n := by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow] at hk
          omega
        rw [hkrep]
        simp [dyadicNestedRadicalTableAt]
        exact ih (dyadicNestedRadicalParentPrecision precision₁)
          (dyadicNestedRadicalParentPrecision precision₂) (k / 2) hhalf
      · let bound := 2 ^ n
        let reflected := if k <= bound then k else 2 * bound - k
        have hpow : 2 ^ (n + 1) = 2 * bound := by
          dsimp [bound]
          rw [Nat.pow_succ]
          omega
        have hkbound : k <= 2 * bound := by
          rw [← hpow]
          exact hk
        have hreflect : reflected <= bound := by
          dsimp [reflected]
          split <;> omega
        have hparent := ih
          (dyadicNestedRadicalParentPrecision precision₁)
          (dyadicNestedRadicalParentPrecision precision₂) reflected hreflect
        have hbounds₁ := dyadicNestedRadicalTableAt_bounds
          (dyadicNestedRadicalParentPrecision precision₁) n reflected hreflect
        have hbounds₂ := dyadicNestedRadicalTableAt_bounds
          (dyadicNestedRadicalParentPrecision precision₂) n reflected hreflect
        let parentCos₁ :=
          if k <= bound then
            (dyadicNestedRadicalTableAt
              (dyadicNestedRadicalParentPrecision precision₁) n reflected).2
          else
            dyadicNestedRadicalNeg
              (dyadicNestedRadicalTableAt
                (dyadicNestedRadicalParentPrecision precision₁) n reflected).2
        let parentCos₂ :=
          if k <= bound then
            (dyadicNestedRadicalTableAt
              (dyadicNestedRadicalParentPrecision precision₂) n reflected).2
          else
            dyadicNestedRadicalNeg
              (dyadicNestedRadicalTableAt
                (dyadicNestedRadicalParentPrecision precision₂) n reflected).2
        have hparentCos : QInterval.Overlaps parentCos₁ parentCos₂ := by
          by_cases hle : k <= bound
          · simpa [parentCos₁, parentCos₂, hle] using hparent.2
          · unfold parentCos₁ parentCos₂ dyadicNestedRadicalNeg
              QInterval.Overlaps
            rcases hparent.2 with ⟨h₁, h₂⟩
            constructor <;> grind
        have hboundsCos₁ : subintervalOf parentCos₁ (-1) 1 := by
          by_cases hle : k <= bound
          · simpa [parentCos₁, hle] using hbounds₁.2
          · have hneg := dyadicNestedRadicalNeg_unit_subinterval
              (dyadicNestedRadicalTableAt
                (dyadicNestedRadicalParentPrecision precision₁) n reflected).2 hbounds₁.2
            simpa [parentCos₁, hle] using hneg
        have hboundsCos₂ : subintervalOf parentCos₂ (-1) 1 := by
          by_cases hle : k <= bound
          · simpa [parentCos₂, hle] using hbounds₂.2
          · have hneg := dyadicNestedRadicalNeg_unit_subinterval
              (dyadicNestedRadicalTableAt
                (dyadicNestedRadicalParentPrecision precision₂) n reflected).2 hbounds₂.2
            simpa [parentCos₂, hle] using hneg
        have hsine := dyadicHalfAngleSqrt_overlap_of_parent_overlap_at
          hboundsCos₁ hboundsCos₂ hparentCos precision₁ precision₂
        have hcos := dyadicHalfAngleCosSqrt_overlap_of_parent_overlap_at
          hboundsCos₁ hboundsCos₂ hparentCos precision₁ precision₂
        by_cases hle : k <= bound
        · simp [dyadicNestedRadicalTableAt, he, bound, reflected, hle]
          have hsine' := by simpa [parentCos₁, parentCos₂, reflected, hle] using hsine
          have hcos' := by simpa [parentCos₁, parentCos₂, reflected, hle] using hcos
          exact ⟨hsine', hcos'⟩
        · have hneg :
              QInterval.Overlaps
                (dyadicNestedRadicalNeg
                  (sqrtOnUnitEvalIntervalClipped
                    (dyadicHalfAngleCosInput
                      parentCos₁) precision₁))
                (dyadicNestedRadicalNeg
                  (sqrtOnUnitEvalIntervalClipped
                    (dyadicHalfAngleCosInput
                      parentCos₂) precision₂)) := by
            unfold dyadicNestedRadicalNeg QInterval.Overlaps
            have hcos' := hcos
            change _ <= _ ∧ _ <= _
            rcases hcos' with ⟨hlo, hhi⟩
            constructor <;> grind
          simp [dyadicNestedRadicalTableAt, he, bound, reflected, hle]
          exact ⟨by simpa [parentCos₁, parentCos₂, reflected, hle] using hsine,
            by simpa [parentCos₁, parentCos₂, reflected, hle] using hneg⟩

/-! The one-step compatibility contract for the nested-radical evaluator.

The inverse tangent computation supplies a rational interval `I` for the
parent cosine.  The certificate says that `I` overlaps the corresponding
table cosine, and that the public child sine box is the clipped square-root
image of `I`.  The preceding theorem then transports overlap through the
half-angle step.  This is deliberately a finite rational-box statement: it
does not assert that a dyadic angle is itself rational. -/
structure DyadicHalfAngleChildCertificate
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision n j : Nat)
    (hbound : 2 * j + 1 <= 2 ^ n) where
  parentRawCos : QInterval
  parentRawCos_subinterval : subintervalOf parentRawCos (-1) 1
  parent_overlap : QInterval.Overlaps parentRawCos
    ((dyadicNestedRadicalTableAt
      (dyadicNestedRadicalParentPrecision precision) n (2 * j + 1)).2)
  childRawSin : QInterval
  childRawSin_eq : childRawSin =
    sqrtOnUnitEvalIntervalClipped
      (dyadicHalfAngleSinInput parentRawCos) precision
  public_child_eq : childRawSin =
    rationalCircleSinInterval
      (dyadicTangentBoxAt B precision (n + 1) (2 * j + 1) (by
        have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
          rw [Nat.pow_succ]
          omega
        rw [hpow]
        omega))

theorem DyadicHalfAngleChildCertificate.to_public_overlap
    {B : IntegralIdentities.ArctanInverseBisection}
    {precision n j : Nat} {hbound : 2 * j + 1 <= 2 ^ n}
    (h : DyadicHalfAngleChildCertificate B precision n j hbound) :
    QInterval.Overlaps
      (rationalCircleSinInterval
        (dyadicTangentBoxAt B precision (n + 1) (2 * j + 1) (by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          omega)))
      (dyadicNestedRadicalTableAt precision (n + 1) (2 * j + 1)).1 := by
  have hover := dyadicHalfAngle_child_sine_overlap_of_raw_halfAngle
    (I := h.parentRawCos)
    (J := (dyadicNestedRadicalTableAt
      (dyadicNestedRadicalParentPrecision precision) n (2 * j + 1)).2)
    (K := h.childRawSin)
    precision n j h.parentRawCos_subinterval
    (dyadicNestedRadicalTableAt_bounds
      (dyadicNestedRadicalParentPrecision precision) n (2 * j + 1)
      (by omega)).2
    rfl h.parent_overlap h.childRawSin_eq hbound
  rw [← h.public_child_eq]
  exact hover

/-! The public evaluator is definitionally the circle-sine image of the
inverse tangent box at the same stage.  This adapter lets a child certificate
be consumed directly by the `RealCompute` sample-transport theorem. -/
theorem DyadicHalfAngleChildCertificate.to_sample_overlap
    {B : IntegralIdentities.ArctanInverseBisection}
    {precision n j : Nat} {hbound : 2 * j + 1 <= 2 ^ n}
    (h : DyadicHalfAngleChildCertificate B precision n j hbound) :
    QInterval.Overlaps
      ((sinPiRawOfArctan B
        (leftPoint 0 ((1 : Rat) / 2) (2 ^ (n + 1)) (2 * j + 1))
        (dyadicHalfDomain (by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          omega))).compute precision)
      (dyadicNestedRadicalTableAt precision (n + 1) (2 * j + 1)).1 := by
  have hbox := h.to_public_overlap
  simpa [sinPiRawOfArctan, dyadicTangentBoxAt] using hbox

/-! The even branch has a different finite obligation.  The dyadic table
reuses the parent sample, but at `dyadicNestedRadicalParentPrecision`; the
certificate therefore records containment of that parent box in the current
child box.  This is exactly what lets a parent overlap survive the precision
change. -/
theorem qinterval_overlaps_of_contained_left
    {A B C : QInterval}
    (hsub : subintervalOf B A.lo A.hi)
    (hover : QInterval.Overlaps B C) :
    QInterval.Overlaps A C := by
  unfold subintervalOf QInterval.Overlaps at *
  rcases hsub with ⟨hAlo, hAB, hAhi⟩
  rcases hover with ⟨hBClo, hBC_hi⟩
  constructor
  · exact Rat.le_trans hAlo hBClo
  · exact Rat.le_trans hBC_hi hAhi

structure DyadicEvenStepCertificate
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision n k : Nat) (hk : k < 2 ^ n) where
  childRaw : QInterval
  parentRaw : QInterval
  parent_contained : subintervalOf parentRaw childRaw.lo childRaw.hi
  parent_overlap : QInterval.Overlaps parentRaw
    ((dyadicNestedRadicalTableAt
      (dyadicNestedRadicalParentPrecision precision) n k).1)
  public_child_eq : childRaw =
    rationalCircleSinInterval
      (dyadicTangentBoxAt B precision (n + 1) (2 * k) (by
        have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
          rw [Nat.pow_succ]
          omega
        rw [hpow]
        omega))

/-- Construct the even branch from one successful finite tangent-witness
search.  The parent and child names in the certificate refer to the
half-angle proof interface; for an even index the nested-radical table is the
parent table at a different precision, while the public circle box itself is
the same child box.  The search supplies exactly the required overlap, so no
unstated continuity or completed-real argument is used. -/
def DyadicEvenStepCertificate.ofWitnessSearch
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision n k : Nat) (hk : k < 2 ^ n) (m : Nat)
    (hsearch : ∃ u,
      rationalTangentWitnessBoxSearch
        (dyadicTangentBoxAt B precision (n + 1) (2 * k) (by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          omega))
        (dyadicNestedRadicalTableAt
          (dyadicNestedRadicalParentPrecision precision) n k).1 m = some u) :
    DyadicEvenStepCertificate B precision n k hk where
  childRaw := rationalCircleSinInterval
    (dyadicTangentBoxAt B precision (n + 1) (2 * k) (by
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
        rw [Nat.pow_succ]
        omega
      rw [hpow]
      omega))
  parentRaw := rationalCircleSinInterval
    (dyadicTangentBoxAt B precision (n + 1) (2 * k) (by
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
        rw [Nat.pow_succ]
        omega
      rw [hpow]
      omega))
  parent_contained := by
    have hU := dyadicTangentBoxAt_bounds B precision (n + 1) (2 * k) (by
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
        rw [Nat.pow_succ]
        omega
      rw [hpow]
      omega)
    have hwidth := rationalCircleSinInterval_width_le hU
    unfold subintervalOf
    constructor
    · exact Rat.le_refl
    constructor
    · apply (Rat.le_iff_sub_nonneg _ _).2
      simpa [rationalCircleSinInterval, QInterval.width] using hwidth.1
    · exact Rat.le_refl
  parent_overlap := by
    let U := dyadicTangentBoxAt B precision (n + 1) (2 * k) (by
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
        rw [Nat.pow_succ]
        omega
      rw [hpow]
      omega)
    have hU : subintervalOf U 0 1 := by
      exact dyadicTangentBoxAt_bounds B precision (n + 1) (2 * k) (by
        have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
          rw [Nat.pow_succ]
          omega
        rw [hpow]
        omega)
    have hS : subintervalOf
        (dyadicNestedRadicalTableAt
          (dyadicNestedRadicalParentPrecision precision) n k).1 0 1 :=
      (dyadicNestedRadicalTableAt_bounds
        (dyadicNestedRadicalParentPrecision precision) n k (by omega)).1
    obtain ⟨u, hu⟩ := hsearch
    simpa [U] using
      (rationalTangentWitnessBoxSearch_overlap_of_success hU hS hu)
  public_child_eq := by rfl

theorem DyadicEvenStepCertificate.to_public_overlap
    {B : IntegralIdentities.ArctanInverseBisection}
    {precision n k : Nat} {hk : k < 2 ^ n}
    (h : DyadicEvenStepCertificate B precision n k hk) :
    QInterval.Overlaps
      (rationalCircleSinInterval
        (dyadicTangentBoxAt B precision (n + 1) (2 * k) (by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          omega)))
      (dyadicNestedRadicalTableAt precision (n + 1) (2 * k)).1 := by
  have hover := qinterval_overlaps_of_contained_left
    h.parent_contained h.parent_overlap
  rw [← h.public_child_eq]
  simpa [dyadicNestedRadicalTableAt, dyadicNestedRadicalParentPrecision] using hover

structure DyadicReflectedHalfAngleCertificate
    (B : IntegralIdentities.ArctanInverseBisection)
    (precision n k : Nat)
    (hupper : 2 ^ n < k) (hk : k < 2 ^ (n + 1)) where
  parentRawCos : QInterval
  parentRawCos_subinterval : subintervalOf parentRawCos (-1) 1
  parentRawCos_eq : parentRawCos = dyadicNestedRadicalNeg
    (dyadicNestedRadicalTableAt
      (dyadicNestedRadicalParentPrecision precision) n
      (2 * 2 ^ n - k)).2
  parent_overlap : QInterval.Overlaps parentRawCos
    (dyadicNestedRadicalNeg
      (dyadicNestedRadicalTableAt
        (dyadicNestedRadicalParentPrecision precision) n
        (2 * 2 ^ n - k)).2)
  childRawSin : QInterval
  childRawSin_eq : childRawSin =
    sqrtOnUnitEvalIntervalClipped
      (dyadicHalfAngleSinInput parentRawCos) precision
  public_child_eq : childRawSin =
    rationalCircleSinInterval
      (dyadicTangentBoxAt B precision (n + 1) k (by
        have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
          rw [Nat.pow_succ]
          omega
        rw [hpow]
        omega))

theorem DyadicReflectedHalfAngleCertificate.to_public_overlap
    {B : IntegralIdentities.ArctanInverseBisection}
    {precision n k : Nat} {hupper : 2 ^ n < k}
    {hk : k < 2 ^ (n + 1)}
    (h : DyadicReflectedHalfAngleCertificate B precision n k hupper hk)
    (hodd : k % 2 = 1) :
    QInterval.Overlaps
      (rationalCircleSinInterval
        (dyadicTangentBoxAt B precision (n + 1) k (by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow]
          omega)))
      (dyadicNestedRadicalTableAt precision (n + 1) k).1 := by
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
    rw [Nat.pow_succ]
    omega
  have hreflect : 2 * 2 ^ n - k <= 2 ^ n := by
    omega
  have hbounds := dyadicNestedRadicalTableAt_bounds
    (dyadicNestedRadicalParentPrecision precision) n
    (2 * 2 ^ n - k) hreflect
  have hJ : subintervalOf
      (dyadicNestedRadicalNeg
        (dyadicNestedRadicalTableAt
          (dyadicNestedRadicalParentPrecision precision) n
          (2 * 2 ^ n - k)).2) (-1) 1 :=
    dyadicNestedRadicalNeg_unit_subinterval _ hbounds.2
  have hover := dyadicHalfAngle_child_sine_overlap_of_raw_halfAngle_upper
    (I := h.parentRawCos)
    (J := dyadicNestedRadicalNeg
      (dyadicNestedRadicalTableAt
        (dyadicNestedRadicalParentPrecision precision) n
        (2 * 2 ^ n - k)).2)
    (K := h.childRawSin)
    precision n k h.parentRawCos_subinterval hJ rfl
    h.parent_overlap h.childRawSin_eq hodd hupper (Nat.le_of_lt hk)
  rw [← h.public_child_eq]
  exact hover

theorem dyadicNestedRadical_sample_overlap_of_branch_certificates
    (B : IntegralIdentities.ArctanInverseBisection)
    (zero_overlap : forall (precision depth : Nat) (hk : 0 < 2 ^ depth),
      QInterval.Overlaps
        ((sinPiRawOfArctan B
          (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) 0)
          (dyadicHalfDomain (by omega))).compute precision)
        (dyadicNestedRadicalTableAt precision depth 0).1)
    (even_certificate : forall (precision n j : Nat) (hj : j < 2 ^ n),
      DyadicEvenStepCertificate B precision n j hj)
    (lower_certificate : forall (precision n j : Nat)
      (hbound : 2 * j + 1 <= 2 ^ n),
      DyadicHalfAngleChildCertificate B precision n j hbound)
    (upper_certificate : forall (precision n k : Nat)
      (hupper : 2 ^ n < k) (hk : k < 2 ^ (n + 1)),
      DyadicReflectedHalfAngleCertificate B precision n k hupper hk) :
    forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      QInterval.Overlaps
        ((sinPiRawOfArctan B
          (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
          (dyadicHalfDomain hk)).compute precision)
        (dyadicNestedRadicalTableAt precision depth k).1 := by
  intro precision depth k hk
  cases depth with
  | zero =>
      have hk' : k = 0 := by omega
      subst k
      exact zero_overlap precision 0 (by decide +kernel)
  | succ n =>
      by_cases hzero : k = 0
      · subst k
        exact zero_overlap precision (n + 1) (by omega)
      by_cases heven : k % 2 = 0
      · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := by
          exact ⟨k / 2, by omega⟩
        have hj : j < 2 ^ n := by
          rw [Nat.pow_succ] at hk
          omega
        have hbox := (even_certificate precision n j hj).to_public_overlap
        simpa [sinPiRawOfArctan, dyadicTangentBoxAt] using hbox
      · have hodd : k % 2 = 1 := by omega
        by_cases hlower : k <= 2 ^ n
        · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := by
            exact ⟨k / 2, by omega⟩
          have hbound : 2 * j + 1 <= 2 ^ n := by omega
          have hbox :=
            (lower_certificate precision n j hbound).to_public_overlap
          simpa [sinPiRawOfArctan, dyadicTangentBoxAt] using hbox
        · have hupper : 2 ^ n < k := by omega
          have hbox :=
            (upper_certificate precision n k hupper hk).to_public_overlap hodd
          simpa [sinPiRawOfArctan, dyadicTangentBoxAt] using hbox

theorem dyadicNestedRadical_sample_overlap_of_branch_certificates_of_endpoint
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht0 : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    (even_certificate : forall (precision n j : Nat) (hj : j < 2 ^ n),
      DyadicEvenStepCertificate B precision n j hj)
    (lower_certificate : forall (precision n j : Nat)
      (hbound : 2 * j + 1 <= 2 ^ n),
      DyadicHalfAngleChildCertificate B precision n j hbound)
    (upper_certificate : forall (precision n k : Nat)
      (hupper : 2 ^ n < k) (hk : k < 2 ^ (n + 1)),
      DyadicReflectedHalfAngleCertificate B precision n k hupper hk) :
    forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      QInterval.Overlaps
        ((sinPiRawOfArctan B
          (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
          (dyadicHalfDomain hk)).compute precision)
        (dyadicNestedRadicalTableAt precision depth k).1 := by
  apply dyadicNestedRadical_sample_overlap_of_branch_certificates B
    (fun precision depth hk =>
      dyadicNestedRadical_zero_sample_overlap_of_endpoint B ht0
        precision depth hk)
    even_certificate lower_certificate upper_certificate

/-! Package the four finite obligations needed by the dyadic transport.  This
is intentionally a certificate family rather than an existence theorem: the
caller supplies rational boxes and finite searches, while the theorem below
assembles them into the stagewise overlap consumed by the integral adapter. -/

structure DyadicNestedRadicalBranchCertificateFamily
    (B : IntegralIdentities.ArctanInverseBisection) where
  endpoint_zero :
    (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero
  even : forall (precision n j : Nat) (hj : j < 2 ^ n),
    DyadicEvenStepCertificate B precision n j hj
  lower : forall (precision n j : Nat)
      (hbound : 2 * j + 1 <= 2 ^ n),
    DyadicHalfAngleChildCertificate B precision n j hbound
  upper : forall (precision n k : Nat)
      (hupper : 2 ^ n < k) (hk : k < 2 ^ (n + 1)),
    DyadicReflectedHalfAngleCertificate B precision n k hupper hk

theorem DyadicNestedRadicalBranchCertificateFamily.sample_overlap
    {B : IntegralIdentities.ArctanInverseBisection}
    (H : DyadicNestedRadicalBranchCertificateFamily B) :
    forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      QInterval.Overlaps
        ((sinPiRawOfArctan B
          (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) k)
          (dyadicHalfDomain hk)).compute precision)
        (dyadicNestedRadicalTableAt precision depth k).1 := by
  exact dyadicNestedRadical_sample_overlap_of_branch_certificates_of_endpoint
    B H.endpoint_zero H.even H.lower H.upper

theorem DyadicNestedRadicalBranchCertificateFamily.rational_circle_overlap
    {B : IntegralIdentities.ArctanInverseBisection}
    (H : DyadicNestedRadicalBranchCertificateFamily B) :
    forall (precision depth k : Nat) (hk : k < 2 ^ depth),
      QInterval.Overlaps
        (rationalCircleSinInterval
          (dyadicTangentBoxAt B precision depth k hk))
        (dyadicNestedRadicalTableAt precision depth k).1 := by
  intro precision depth k hk
  have h := H.sample_overlap precision depth k hk
  simpa [sinPiRawOfArctan, dyadicTangentBoxAt] using h

theorem dyadicNestedRadicalTableAt_width_le
    (precision n k : Nat) (hk : k <= 2 ^ n) :
    (dyadicNestedRadicalTableAt precision n k).1.width <=
        1 / ((precision + 1 : Nat) : Rat) ∧
      (dyadicNestedRadicalTableAt precision n k).2.width <=
        1 / ((precision + 1 : Nat) : Rat) := by
  induction n generalizing precision k with
  | zero =>
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl <;>
        simp [dyadicNestedRadicalTableAt, QInterval.width]
        <;> constructor <;>
          grind [Rat.le_of_lt (one_div_nat_pos (Nat.succ_pos precision))]
  | succ n ih =>
      by_cases he : k % 2 = 0
      · have hkrep : k = 2 * (k / 2) := by omega
        have hhalf : k / 2 <= 2 ^ n := by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ]
            omega
          rw [hpow] at hk
          omega
        rw [hkrep]
        simp [dyadicNestedRadicalTableAt]
        have hparent := ih (dyadicNestedRadicalParentPrecision precision)
          (k / 2) hhalf
        exact ⟨Rat.le_trans hparent.1
            (by simpa [Rat.natCast_add] using
              dyadicNestedRadicalParentPrecision_output_budget precision),
          Rat.le_trans hparent.2
            (by simpa [Rat.natCast_add] using
              dyadicNestedRadicalParentPrecision_output_budget precision)⟩
      · let bound := 2 ^ n
        let parentPrecision := dyadicNestedRadicalParentPrecision precision
        let reflected := if k <= bound then k else 2 * bound - k
        have hpow : 2 ^ (n + 1) = 2 * bound := by
          dsimp [bound]
          rw [Nat.pow_succ]
          omega
        have hkbound : k <= 2 * bound := by
          rw [← hpow]
          exact hk
        have hreflect : reflected <= bound := by
          dsimp [reflected]
          split <;> omega
        have hparent := ih parentPrecision reflected hreflect
        have hbounds := dyadicNestedRadicalTableAt_bounds
          parentPrecision n reflected hreflect
        let parentCos :=
          if k <= bound then
            (dyadicNestedRadicalTableAt parentPrecision n reflected).2
          else
            dyadicNestedRadicalNeg
              (dyadicNestedRadicalTableAt parentPrecision n reflected).2
        have hparentCosWidth : parentCos.width =
            (dyadicNestedRadicalTableAt parentPrecision n reflected).2.width := by
          by_cases hle : k <= bound
          · simp [parentCos, hle]
          · simp [parentCos, hle, dyadicNestedRadicalNeg_width]
        have hparentCosBounds : subintervalOf parentCos (-1) 1 := by
          by_cases hle : k <= bound
          · simpa [parentCos, hle] using hbounds.2
          · have hneg := dyadicNestedRadicalNeg_unit_subinterval
              (dyadicNestedRadicalTableAt parentPrecision n reflected).2 hbounds.2
            simpa [parentCos, hle] using hneg
        have hsinInput := dyadicHalfAngleSinInput_subinterval
          parentCos hparentCosBounds
        have hcosInput := dyadicHalfAngleCosInput_subinterval
          parentCos hparentCosBounds
        have hsinBudget :
            (dyadicHalfAngleSinInput
              parentCos).width <=
              1 / ((16 * (precision + 1) * (precision + 1) : Nat) : Rat) := by
          rw [dyadicHalfAngleSinInput_width, Rat.div_def, Rat.div_def]
          calc
            parentCos.width *
                (2 : Rat)⁻¹ <=
                (1 / ((parentPrecision + 1 : Nat) : Rat)) * (2 : Rat)⁻¹ :=
              Rat.mul_le_mul_of_nonneg_right
                (by rw [hparentCosWidth]; exact hparent.2) (by decide +kernel)
            _ = 1 / ((2 * (parentPrecision + 1) : Nat) : Rat) := by
              symm
              simpa [Rat.div_def] using
                (one_div_nat_succ_half parentPrecision).symm
            _ <= 1 / ((16 * (precision + 1) * (precision + 1) : Nat) : Rat) :=
              dyadicNestedRadicalParentPrecision_input_budget precision
        have hcosBudget :
            (dyadicHalfAngleCosInput
              parentCos).width <=
              1 / ((16 * (precision + 1) * (precision + 1) : Nat) : Rat) := by
          rw [dyadicHalfAngleCosInput_width, Rat.div_def, Rat.div_def]
          calc
            parentCos.width *
                (2 : Rat)⁻¹ <=
                (1 / ((parentPrecision + 1 : Nat) : Rat)) * (2 : Rat)⁻¹ :=
              Rat.mul_le_mul_of_nonneg_right
                (by rw [hparentCosWidth]; exact hparent.2) (by decide +kernel)
            _ = 1 / ((2 * (parentPrecision + 1) : Nat) : Rat) := by
              symm
              simpa [Rat.div_def] using
                (one_div_nat_succ_half parentPrecision).symm
            _ <= 1 / ((16 * (precision + 1) * (precision + 1) : Nat) : Rat) :=
              dyadicNestedRadicalParentPrecision_input_budget precision
        have hsine := dyadicHalfAngleSqrt_width_le
            (dyadicHalfAngleSinInput parentCos)
          hsinInput precision hsinBudget
        have hcos := dyadicHalfAngleSqrt_width_le
            (dyadicHalfAngleCosInput parentCos)
          hcosInput precision hcosBudget
        by_cases hle : k <= bound
        · simp [dyadicNestedRadicalTableAt, he, bound, reflected, hle]
          exact ⟨by simpa [parentCos, reflected, hle, parentPrecision] using hsine,
            by simpa [parentCos, reflected, hle, parentPrecision] using hcos⟩
        · simp [dyadicNestedRadicalTableAt, he, bound, reflected, hle]
          exact ⟨by simpa [parentCos, reflected, hle, parentPrecision] using hsine,
            by simpa [dyadicNestedRadicalNeg_width, parentCos, reflected, hle,
              parentPrecision] using hcos⟩

theorem dyadicNestedRadicalTableAt_succ_even
    (precision n k : Nat) :
    dyadicNestedRadicalTableAt precision (n + 1) (2 * k) =
      dyadicNestedRadicalTableAt
        (dyadicNestedRadicalParentPrecision precision) n k := by
  simp [dyadicNestedRadicalTableAt, dyadicNestedRadicalParentPrecision]

theorem dyadicNestedRadicalStageTable_zero :
    dyadicNestedRadicalStageTable 0 0 =
      ({ lo := 0, hi := 0 }, { lo := 1, hi := 1 }) := by
  simp [dyadicNestedRadicalStageTable, dyadicNestedRadicalTableAt]

theorem dyadicNestedRadicalTableAt_zero (precision n : Nat) :
    dyadicNestedRadicalTableAt precision n 0 =
      ({ lo := 0, hi := 0 }, { lo := 1, hi := 1 }) := by
  induction n generalizing precision with
  | zero =>
      simp [dyadicNestedRadicalTableAt]
  | succ n ih =>
      simp [dyadicNestedRadicalTableAt]
      exact ih (dyadicNestedRadicalParentPrecision precision)

theorem dyadicNestedRadicalStageTable_zero_at (n : Nat) :
    dyadicNestedRadicalStageTable n 0 =
      ({ lo := 0, hi := 0 }, { lo := 1, hi := 1 }) := by
  exact dyadicNestedRadicalTableAt_zero n n

theorem dyadicNestedRadicalStageSinAt_zero (n : Nat) :
    dyadicNestedRadicalStageSinAt n 0 = { lo := 0, hi := 0 } := by
  simp [dyadicNestedRadicalStageSinAt, dyadicNestedRadicalStageTable_zero_at]

theorem dyadicNestedRadicalTableAt_last (precision n : Nat) :
    dyadicNestedRadicalTableAt precision n (2 ^ n) =
      ({ lo := 1, hi := 1 }, { lo := 0, hi := 0 }) := by
  induction n generalizing precision with
  | zero =>
      simp [dyadicNestedRadicalTableAt]
  | succ n ih =>
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
        rw [Nat.pow_succ]
        omega
      rw [hpow]
      have heven : (2 * 2 ^ n) % 2 = 0 := by omega
      have hhalf : (2 * 2 ^ n) / 2 = 2 ^ n := by omega
      simp [dyadicNestedRadicalTableAt, heven, hhalf]
      exact ih (dyadicNestedRadicalParentPrecision precision)

theorem dyadicNestedRadicalStageTable_last (n : Nat) :
    dyadicNestedRadicalStageTable n (2 ^ n) =
      ({ lo := 1, hi := 1 }, { lo := 0, hi := 0 }) := by
  exact dyadicNestedRadicalTableAt_last n n

theorem dyadicNestedRadicalStageSinAt_last (n : Nat) :
    dyadicNestedRadicalStageSinAt n (2 ^ n) = { lo := 1, hi := 1 } := by
  simp [dyadicNestedRadicalStageSinAt, dyadicNestedRadicalStageTable_last]

theorem arctanSinPi_nestedRadicalStage_sample_overlap_zero
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero) (n : Nat) :
    QInterval.Overlaps
      ((sinPiRawOfArctan B 0
        ⟨by decide +kernel, by decide +kernel⟩).compute n)
      (dyadicNestedRadicalStageSinAt n 0) := by
  have hsin := (RealCompute.compareAt_overlap_iff
    (sinPiRawOfArctan B 0 ⟨by decide +kernel, by decide +kernel⟩)
    RealCompute.zero n n).1
    (sinPiRawOfArctan_zero_equiv_zero_of_tangent_endpoint B ht n)
  rw [dyadicNestedRadicalStageSinAt_zero]
  simpa [RealCompute.zero, RealCompute.ofRat] using hsin

theorem arctanSinPi_nestedRadicalStage_sample_overlap_last
    (B : IntegralIdentities.ArctanInverseBisection)
    (ht : (B.tangentAt 1
      RationalCircle.GeometricTrig.firstQuadrantBranch_one).Equiv
      RealCompute.one) (n : Nat) :
    QInterval.Overlaps
      ((sinPiRawOfArctan B (1 / 2)
        ⟨by decide +kernel, by decide +kernel⟩).compute n)
      (dyadicNestedRadicalStageSinAt n (2 ^ n)) := by
  have hsin := (RealCompute.compareAt_overlap_iff
    (sinPiRawOfArctan B (1 / 2)
      ⟨by decide +kernel, by decide +kernel⟩)
    RealCompute.one n n).1
    (sinPiRawOfArctan_half_equiv_one_of_tangent_endpoint B ht n)
  rw [dyadicNestedRadicalStageSinAt_last]
  simpa [RealCompute.one, RealCompute.ofRat] using hsin

theorem dyadicNestedRadicalStageTable_one_one :
    dyadicNestedRadicalStageTable 1 1 =
      (sqrtOnUnitEvalIntervalClipped
        { lo := (1 : Rat) / 2, hi := (1 : Rat) / 2 } 1,
       sqrtOnUnitEvalIntervalClipped
        { lo := (1 : Rat) / 2, hi := (1 : Rat) / 2 } 1) := by
  simp [dyadicNestedRadicalStageTable, dyadicNestedRadicalTableAt]
  constructor <;> congr 1 <;> decide +kernel

/-! The table can now be used directly by the equal-dyadic rectangle
algorithm.  This is deliberately an indexed finite sum: its inputs are the
stage and the left-endpoint index, exactly the data available to a dyadic
integral.  The later `RealFunRaw` adapter only has to prove that its rational
argument is the corresponding dyadic point. -/

def dyadicNestedRadicalLeftSum (n : Nat) : QInterval :=
  let N := 2 ^ n
  let h := mesh 0 ((1 : Rat) / 2) N
  (List.range N).foldl
    (fun acc k =>
      let I := dyadicNestedRadicalStageSinAt n k
      QInterval.addInterval acc (QInterval.scaleByRat h I))
    { lo := 0, hi := 0 }

/-! A cellwise Darboux range.  Unlike the left-sample sum, this interval is
not tied to one endpoint: it encloses both endpoint sample boxes.  That is
the shape needed for a refinement/nesting proof. -/
def dyadicNestedRadicalCellRange (n k : Nat) : QInterval :=
  let N := 2 ^ n
  let h := mesh 0 ((1 : Rat) / 2) N
  QInterval.hull
    (QInterval.scaleByRat h (dyadicNestedRadicalStageSinAt n k))
    (QInterval.scaleByRat h (dyadicNestedRadicalStageSinAt n (k + 1)))

def dyadicNestedRadicalDarbouxSum (n : Nat) : QInterval :=
  let N := 2 ^ n
  (List.range N).foldl
    (fun acc k => QInterval.addInterval acc
      (dyadicNestedRadicalCellRange n k))
    { lo := 0, hi := 0 }

theorem dyadicNestedRadicalCellRange_contains_left
    (n k : Nat) :
    (dyadicNestedRadicalCellRange n k).ContainsInterval
      (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) (2 ^ n))
        (dyadicNestedRadicalStageSinAt n k)) := by
  unfold dyadicNestedRadicalCellRange
  exact QInterval.hull_contains_left _ _

theorem dyadicNestedRadicalCellRange_contains_right
    (n k : Nat) :
    (dyadicNestedRadicalCellRange n k).ContainsInterval
      (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) (2 ^ n))
        (dyadicNestedRadicalStageSinAt n (k + 1))) := by
  unfold dyadicNestedRadicalCellRange
  exact QInterval.hull_contains_right _ _

theorem dyadicNestedRadicalCellRange_ordered
    (n k : Nat) (hk : k < 2 ^ n) :
    0 <= (dyadicNestedRadicalCellRange n k).width := by
  let N := 2 ^ n
  have hk1 : k + 1 <= N := by
    dsimp [N]
    omega
  have hleft := dyadicNestedRadicalTableAt_bounds n n k (by omega)
  have hright := dyadicNestedRadicalTableAt_bounds n n (k + 1) hk1
  have hmesh : 0 <= mesh 0 ((1 : Rat) / 2) N :=
    mesh_nonneg_of_le (Nat.pow_pos (by omega)) (by decide +kernel)
  have hstage_left : 0 <=
      (dyadicNestedRadicalStageSinAt n k).width := by
    unfold dyadicNestedRadicalStageSinAt dyadicNestedRadicalStageTable
      QInterval.width
    grind [hleft.1.2.1, Rat.sub_eq_add_neg]
  have hstage_right : 0 <=
      (dyadicNestedRadicalStageSinAt n (k + 1)).width := by
    unfold dyadicNestedRadicalStageSinAt dyadicNestedRadicalStageTable
      QInterval.width
    grind [hright.1.2.1, Rat.sub_eq_add_neg]
  have hscale_left : 0 <=
      (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) N)
        (dyadicNestedRadicalStageSinAt n k)).width := by
    rw [QInterval.scaleByRat_width_of_nonneg hmesh]
    exact Rat.mul_nonneg hmesh hstage_left
  have hscale_right : 0 <=
      (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) N)
        (dyadicNestedRadicalStageSinAt n (k + 1))).width := by
    rw [QInterval.scaleByRat_width_of_nonneg hmesh]
    exact Rat.mul_nonneg hmesh hstage_right
  unfold dyadicNestedRadicalCellRange QInterval.width QInterval.hull
  have hleft_order :
      (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) N)
        (dyadicNestedRadicalStageSinAt n k)).lo <=
      (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) N)
        (dyadicNestedRadicalStageSinAt n k)).hi := by
    unfold QInterval.scaleByRat
    simp [if_pos hmesh]
    exact Rat.mul_le_mul_of_nonneg_left (by
      unfold dyadicNestedRadicalStageSinAt dyadicNestedRadicalStageTable
      exact hleft.1.2.1) hmesh
  have hright_order :
      (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) N)
        (dyadicNestedRadicalStageSinAt n (k + 1))).lo <=
      (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) N)
        (dyadicNestedRadicalStageSinAt n (k + 1))).hi := by
    unfold QInterval.scaleByRat
    simp [if_pos hmesh]
    exact Rat.mul_le_mul_of_nonneg_left (by
      unfold dyadicNestedRadicalStageSinAt dyadicNestedRadicalStageTable
      exact hright.1.2.1) hmesh
  grind

theorem dyadicDarbouxCell_refines_of_endpoint_monotone
    (h : Rat) (A B C : QInterval)
    (hh : 0 <= h)
    (hA : A.lo <= A.hi) (hB : B.lo <= B.hi) (hC : C.lo <= C.hi)
    (hloAB : A.lo <= B.lo) (hloBC : B.lo <= C.lo)
    (hhiAB : A.hi <= B.hi) (hhiBC : B.hi <= C.hi) :
    (QInterval.hull
      (QInterval.scaleByRat h A)
      (QInterval.scaleByRat h C)).ContainsInterval
      (QInterval.addInterval
        (QInterval.hull
          (QInterval.scaleByRat (h / 2) A)
          (QInterval.scaleByRat (h / 2) B))
        (QInterval.hull
          (QInterval.scaleByRat (h / 2) B)
          (QInterval.scaleByRat (h / 2) C))) := by
  have hh2 : 0 <= h / 2 := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hh (by decide +kernel)
  unfold QInterval.ContainsInterval QInterval.hull QInterval.addInterval
    QInterval.scaleByRat
  simp only [if_pos hh, if_pos hh2]
  have hAlo : h * A.lo <= h * B.lo :=
    Rat.mul_le_mul_of_nonneg_left hloAB hh
  have hBlo : h * B.lo <= h * C.lo :=
    Rat.mul_le_mul_of_nonneg_left hloBC hh
  have hAhi : h * A.hi <= h * B.hi :=
    Rat.mul_le_mul_of_nonneg_left hhiAB hh
  have hBhi : h * B.hi <= h * C.hi :=
    Rat.mul_le_mul_of_nonneg_left hhiBC hh
  have hAlohi : 0 <= h * (B.lo - A.lo) := by
    exact Rat.mul_nonneg hh (by grind)
  have hBlohi : 0 <= h * (C.lo - B.lo) := by
    exact Rat.mul_nonneg hh (by grind)
  have hAhi' : 0 <= h * (B.hi - A.hi) := by
    exact Rat.mul_nonneg hh (by grind)
  have hBhi' : 0 <= h * (C.hi - B.hi) := by
    exact Rat.mul_nonneg hh (by grind)
  grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm,
    Rat.add_assoc, Rat.add_comm]

theorem dyadicDarbouxCell_refines_of_coarse_endpoint_containment
    (h : Rat) (A0 A1 A2 C0 C2 : QInterval)
    (hh : 0 <= h)
    (hA0 : A0.lo <= A0.hi) (hA1 : A1.lo <= A1.hi)
    (hA2 : A2.lo <= A2.hi)
    (hlo01 : A0.lo <= A1.lo) (hlo12 : A1.lo <= A2.lo)
    (hhi01 : A0.hi <= A1.hi) (hhi12 : A1.hi <= A2.hi)
    (hC0 : (QInterval.scaleByRat h C0).ContainsInterval
      (QInterval.scaleByRat h A0))
    (hC2 : (QInterval.scaleByRat h C2).ContainsInterval
      (QInterval.scaleByRat h A2)) :
    (QInterval.hull
      (QInterval.scaleByRat h C0)
      (QInterval.scaleByRat h C2)).ContainsInterval
      (QInterval.addInterval
        (QInterval.hull
          (QInterval.scaleByRat (h / 2) A0)
          (QInterval.scaleByRat (h / 2) A1))
        (QInterval.hull
          (QInterval.scaleByRat (h / 2) A1)
          (QInterval.scaleByRat (h / 2) A2))) := by
  have hcoarse :
      (QInterval.hull
        (QInterval.scaleByRat h C0)
        (QInterval.scaleByRat h C2)).ContainsInterval
        (QInterval.hull
          (QInterval.scaleByRat h A0)
          (QInterval.scaleByRat h A2)) := by
    apply QInterval.hull_least
    · exact QInterval.ContainsInterval.trans
        (QInterval.hull_contains_left _ _) hC0
    · exact QInterval.ContainsInterval.trans
        (QInterval.hull_contains_right _ _) hC2
  exact QInterval.ContainsInterval.trans hcoarse
    (dyadicDarbouxCell_refines_of_endpoint_monotone h A0 A1 A2 hh
      hA0 hA1 hA2 hlo01 hlo12 hhi01 hhi12)

theorem dyadicNestedRadicalDarbouxSum_contains_leftSum
    (n : Nat) :
    (dyadicNestedRadicalDarbouxSum n).ContainsInterval
      (dyadicNestedRadicalLeftSum n) := by
  unfold dyadicNestedRadicalDarbouxSum dyadicNestedRadicalLeftSum
  apply RationalPartition.addInterval_fold_contains
  · exact ⟨Rat.le_refl, Rat.le_refl⟩
  · intro k
    simpa [dyadicNestedRadicalCellRange]
      using dyadicNestedRadicalCellRange_contains_left n k

theorem dyadicNestedRadicalDarbouxSum_width_nonneg
    (n : Nat) :
    0 <= (dyadicNestedRadicalDarbouxSum n).width := by
  have hcell : forall k, k ∈ List.range (2 ^ n) ->
      0 <= (dyadicNestedRadicalCellRange n k).width := by
    intro k hk
    exact dyadicNestedRadicalCellRange_ordered n k (List.mem_range.mp hk)
  have hfold : forall (xs : List Nat) (initial : Rat),
      0 <= initial ->
      (forall k, k ∈ xs ->
        0 <= (dyadicNestedRadicalCellRange n k).width) ->
      0 <= xs.foldl
        (fun total k => total +
          (dyadicNestedRadicalCellRange n k).width) initial := by
    intro xs
    induction xs with
    | nil =>
        intro initial hinit hterms
        simpa using hinit
    | cons k xs ih =>
        intro initial hinit hterms
        apply ih (initial + (dyadicNestedRadicalCellRange n k).width)
        · exact Rat.add_nonneg hinit (hterms k (by simp))
        · intro j hj
          exact hterms j (by simp [hj])
  unfold dyadicNestedRadicalDarbouxSum
  rw [RationalPartition.addInterval_fold_width]
  have hzero : ({ lo := 0, hi := 0 } : QInterval).width = 0 := by
    unfold QInterval.width
    grind
  rw [hzero]
  have h := hfold (List.range (2 ^ n)) 0 (by decide +kernel) hcell
  grind

theorem dyadicNestedRadicalLeftSum_zero :
    dyadicNestedRadicalLeftSum 0 = { lo := 0, hi := 0 } := by
  decide +kernel

theorem dyadicNestedRadicalLeftSum_one :
    dyadicNestedRadicalLeftSum 1 =
      { lo := (1 / 4 : Rat) *
          (dyadicNestedRadicalStageSinAt 1 1).lo,
        hi := (1 / 4 : Rat) *
          (dyadicNestedRadicalStageSinAt 1 1).hi } := by
  decide +kernel

theorem dyadicNestedRadicalLeftSum_one_explicit :
    dyadicNestedRadicalLeftSum 1 =
      { lo := (1 / 4 : Rat) *
          (sqrtOnUnitEvalIntervalClipped
            { lo := (1 : Rat) / 2, hi := (1 : Rat) / 2 } 1).lo,
        hi := (1 / 4 : Rat) *
          (sqrtOnUnitEvalIntervalClipped
            { lo := (1 : Rat) / 2, hi := (1 : Rat) / 2 } 1).hi } := by
  decide +kernel

/-! Concrete sanity checks for the still-parametric transport certificate.  At
the first two dyadic depths, the candidate sum and the independent
Riemann--Stieltjes evaluator already have a mechanically checkable common
interval.  These are finite anchors for the eventual all-stage geometric
induction; they do not replace that induction. -/

theorem dyadicNestedRadicalLeftSum_zero_overlaps_stieltjes :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 0)
      (sinPiStieltjesIntegral.compute 0) := by
  unfold QInterval.Overlaps
  constructor <;> decide +kernel

theorem dyadicNestedRadicalLeftSum_one_overlaps_stieltjes :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 1)
      (sinPiStieltjesIntegral.compute 1) := by
  unfold QInterval.Overlaps
  constructor <;> decide +kernel

theorem dyadicNestedRadicalLeftSum_two_overlaps_stieltjes :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 2)
      (sinPiStieltjesIntegral.compute 2) := by
  unfold QInterval.Overlaps
  constructor <;> decide +kernel

theorem dyadicNestedRadicalLeftSum_width_le_of_stage
    (n : Nat) (eps : Rat)
    (hstage : forall k, k < 2 ^ n ->
      (dyadicNestedRadicalStageSinAt n k).width <= eps) :
    (dyadicNestedRadicalLeftSum n).width <= (1 / 2 : Rat) * eps := by
  let N := 2 ^ n
  have hN : 0 < N := by
    dsimp [N]
    exact Nat.pow_pos (by omega)
  have hmesh : 0 <= mesh 0 ((1 : Rat) / 2) N :=
    mesh_nonneg_of_le hN (by decide +kernel)
  have hsum := RationalPartition.rat_add_fold_le_length_mul (List.range N)
    (fun k =>
      (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) N)
        (dyadicNestedRadicalStageSinAt n k)).width)
    (mesh 0 ((1 : Rat) / 2) N * eps) (by
      intro k hk
      have hklt : k < N := List.mem_range.mp hk
      rw [QInterval.scaleByRat_width_of_nonneg hmesh]
      exact Rat.mul_le_mul_of_nonneg_left
        (hstage k (by simpa [N] using hklt)) hmesh)
  calc
    (dyadicNestedRadicalLeftSum n).width =
        (List.range N).foldl
          (fun total k => total +
            (QInterval.scaleByRat (mesh 0 ((1 : Rat) / 2) N)
              (dyadicNestedRadicalStageSinAt n k)).width) 0 := by
      unfold dyadicNestedRadicalLeftSum
      rw [RationalPartition.addInterval_fold_width]
      have hzero : ({ lo := 0, hi := 0 } : QInterval).width = 0 := by
        unfold QInterval.width
        grind
      rw [hzero]
      simp [N]
      grind
    _ <= (N : Rat) * (mesh 0 ((1 : Rat) / 2) N * eps) := by
      simpa using hsum
    _ = (1 / 2 : Rat) * eps := by
      have hmesh_total := natCast_mul_mesh_eq_sub
        (a := (0 : Rat)) (b := (1 : Rat) / 2) hN
      rw [show (N : Rat) * (mesh 0 ((1 : Rat) / 2) N * eps) =
        ((N : Rat) * mesh 0 ((1 : Rat) / 2) N) * eps by
          grind [Rat.mul_assoc]]
      rw [hmesh_total]
      rw [show (1 / 2 : Rat) - 0 = 1 / 2 by grind]

theorem dyadicNestedRadicalStageSinAt_width_le
    (n k : Nat) (hk : k < 2 ^ n) :
    (dyadicNestedRadicalStageSinAt n k).width <=
      1 / ((n + 1 : Nat) : Rat) := by
  have htable := dyadicNestedRadicalTableAt_width_le n n k (by omega)
  exact htable.1

theorem dyadicNestedRadicalLeftSum_width_le
    (n : Nat) :
    (dyadicNestedRadicalLeftSum n).width <=
      (1 / 2 : Rat) / ((n + 1 : Nat) : Rat) := by
  simpa [Rat.div_def, Rat.mul_assoc, Rat.mul_comm] using
    dyadicNestedRadicalLeftSum_width_le_of_stage n
      (1 / ((n + 1 : Nat) : Rat))
      (fun k hk => dyadicNestedRadicalStageSinAt_width_le n k hk)

theorem dyadicNestedRadicalLeftSum_width_le_one_over_succ
    (n : Nat) :
    (dyadicNestedRadicalLeftSum n).width <=
      1 / ((n + 1 : Nat) : Rat) := by
  exact Rat.le_trans (dyadicNestedRadicalLeftSum_width_le n) (by
    rw [Rat.div_def, Rat.div_def]
    have hpos : 0 < ((n + 1 : Nat) : Rat)⁻¹ :=
      Rat.inv_pos.mpr ((Rat.natCast_pos).2 (by omega))
    exact Rat.mul_le_mul_of_nonneg_right (by decide +kernel)
      (Rat.le_of_lt hpos))

theorem dyadicNestedRadicalLeftSum_widths_shrink :
    RealCompute.WidthsShrinkToZero dyadicNestedRadicalLeftSum := by
  intro eps
  exact shrinksToZero_of_natOverSuccBound
    (fun n => dyadicNestedRadicalLeftSum_width_le_one_over_succ n) eps

theorem dyadicNestedRadicalLeftSum_width_nonneg (n : Nat) :
    0 <= (dyadicNestedRadicalLeftSum n).width := by
  let N := 2 ^ n
  have hN : 0 < N := by
    dsimp [N]
    exact Nat.pow_pos (by omega)
  have hmesh : 0 <= mesh 0 ((1 : Rat) / 2) N :=
    mesh_nonneg_of_le hN (by decide +kernel)
  have hterm : forall k, k ∈ List.range N ->
      0 <= (QInterval.scaleByRat
        (mesh 0 ((1 : Rat) / 2) N)
        (dyadicNestedRadicalStageSinAt n k)).width := by
    intro k hk
    have hklt : k < N := List.mem_range.mp hk
    rw [QInterval.scaleByRat_width_of_nonneg hmesh]
    exact Rat.mul_nonneg hmesh
      (by
        have hbounds := dyadicNestedRadicalTableAt_bounds n n k
          (Nat.le_of_lt (by simpa [N] using hklt))
        have horder := hbounds.1.2.1
        have hdiff :
            0 <= (dyadicNestedRadicalTableAt n n k).1.hi -
              (dyadicNestedRadicalTableAt n n k).1.lo := by
          grind
        simpa [dyadicNestedRadicalStageSinAt,
          dyadicNestedRadicalStageTable, QInterval.width] using hdiff)
  unfold dyadicNestedRadicalLeftSum
  rw [RationalPartition.addInterval_fold_width]
  have hfold : forall (xs : List Nat) (initial : Rat),
      0 <= initial ->
      (forall k, k ∈ xs ->
        0 <= (QInterval.scaleByRat
          (mesh 0 ((1 : Rat) / 2) N)
          (dyadicNestedRadicalStageSinAt n k)).width) ->
      0 <= xs.foldl
        (fun total k => total +
          (QInterval.scaleByRat
            (mesh 0 ((1 : Rat) / 2) N)
            (dyadicNestedRadicalStageSinAt n k)).width) initial := by
    intro xs
    induction xs with
    | nil =>
        intro initial hinit _
        simpa using hinit
    | cons k xs ih =>
        intro initial hinit hterms
        apply ih (initial +
          (QInterval.scaleByRat
            (mesh 0 ((1 : Rat) / 2) N)
            (dyadicNestedRadicalStageSinAt n k)).width)
        · exact Rat.add_nonneg hinit (hterms k (by simp))
        · intro j hj
          exact hterms j (by simp [hj])
  have h := hfold (List.range N) 0 (by decide +kernel) hterm
  change 0 <= (0 - 0) +
    List.foldl
      (fun total k => total +
        (QInterval.scaleByRat
          (mesh 0 ((1 : Rat) / 2) N)
          (dyadicNestedRadicalStageSinAt n k)).width)
      0 (List.range N)
  rw [show (0 : Rat) - 0 = 0 by decide +kernel, Rat.zero_add]
  exact h

/-! The exact finite bridge from the public mesh to the table's indexed
sample is recorded separately from any analytic convergence theorem. -/
theorem dyadicNestedRadical_sample_coordinate
    {n k : Nat} (hk : k < 2 ^ n) :
    2 * leftPoint 0 ((1 : Rat) / 2) (2 ^ n) k =
      (k : Rat) / ((2 ^ n : Nat) : Rat) :=
  sinPi_half_dyadic_normalized_sample hk

/-! The finite sums form a raw-real candidate without importing a completed
real number.  Its validity is intentionally a separate certificate: the
table is an algorithm, while nesting and shrinking are properties to be
proved from the half-angle bounds. -/

def dyadicNestedRadicalIntegralRaw : RealCompute where
  compute := dyadicNestedRadicalLeftSum

theorem dyadicNestedRadicalIntegralRaw_valid
    (hvalid : RealCompute.ValidCompute dyadicNestedRadicalLeftSum) :
    dyadicNestedRadicalIntegralRaw.Valid := by
  exact hvalid

theorem dyadicNestedRadicalIntegralRaw_widths_shrink :
    RealCompute.WidthsShrinkToZero dyadicNestedRadicalIntegralRaw.compute := by
  change RealCompute.WidthsShrinkToZero dyadicNestedRadicalLeftSum
  exact dyadicNestedRadicalLeftSum_widths_shrink

theorem dyadicNestedRadicalIntegralRaw_equiv_of_overlap
    (anchor : RealCompute)
    (hoverlap : forall n,
      QInterval.Overlaps
        (dyadicNestedRadicalLeftSum n) (anchor.compute n)) :
    dyadicNestedRadicalIntegralRaw.Equiv anchor := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  exact (RealCompute.compareAt_overlap_iff
    dyadicNestedRadicalIntegralRaw anchor n n).2 (hoverlap n)

/-- Cellwise form of the remaining dyadic/change-of-variables certificate.
The witness is rational at each finite stage and lies in both computed
intervals.  This is the form intended for a proof based on finite partitions;
it avoids introducing an exact value of either integral. -/
structure DyadicNestedRadicalStieltjesCommonWitness where
  witness : Nat -> Rat
  candidate_lo_le : forall n,
    (dyadicNestedRadicalLeftSum n).lo <= witness n
  witness_le_candidate_hi : forall n,
    witness n <= (dyadicNestedRadicalLeftSum n).hi
  stieltjes_lo_le : forall n,
    (sinPiStieltjesIntegral.compute n).lo <= witness n
  witness_le_stieltjes_hi : forall n,
    witness n <= (sinPiStieltjesIntegral.compute n).hi

/-! Overlap and a rational common witness are the same finite fact for these
intervals.  This constructor chooses the larger lower endpoint.  It is
useful because geometric proofs naturally establish overlap, while the
stabilization interface consumes an explicit witness. -/
def DyadicNestedRadicalStieltjesCommonWitness.of_overlap
    (hoverlap : forall n,
      QInterval.Overlaps
        (dyadicNestedRadicalLeftSum n)
        (sinPiStieltjesIntegral.compute n)) :
    DyadicNestedRadicalStieltjesCommonWitness where
  witness := fun n => max
    (dyadicNestedRadicalLeftSum n).lo
    (sinPiStieltjesIntegral.compute n).lo
  candidate_lo_le := by
    intro n
    rw [Rat.max_def]
    split <;> grind
  witness_le_candidate_hi := by
    intro n
    have hover := hoverlap n
    unfold QInterval.Overlaps at hover
    have hleft :
        (dyadicNestedRadicalLeftSum n).lo <=
          (dyadicNestedRadicalLeftSum n).hi := by
      have hwidth := dyadicNestedRadicalLeftSum_width_nonneg n
      change 0 <=
        (dyadicNestedRadicalLeftSum n).hi -
          (dyadicNestedRadicalLeftSum n).lo at hwidth
      grind
    rw [Rat.max_def]
    split <;> grind
  stieltjes_lo_le := by
    intro n
    rw [Rat.max_def]
    split <;> grind
  witness_le_stieltjes_hi := by
    intro n
    have hover := hoverlap n
    unfold QInterval.Overlaps at hover
    have hright :
        (sinPiStieltjesIntegral.compute n).lo <=
          (sinPiStieltjesIntegral.compute n).hi := by
      have hwidth := sinPiStieltjesIntegral_valid.1 n
      change 0 <=
        (sinPiStieltjesIntegral.compute n).hi -
          (sinPiStieltjesIntegral.compute n).lo at hwidth
      grind
    rw [Rat.max_def]
    split <;> grind

theorem DyadicNestedRadicalStieltjesCommonWitness.to_overlap
    (h : DyadicNestedRadicalStieltjesCommonWitness) (n : Nat) :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum n)
      (sinPiStieltjesIntegral.compute n) := by
  unfold QInterval.Overlaps
  exact ⟨Rat.le_trans (h.candidate_lo_le n)
      (h.witness_le_stieltjes_hi n),
    Rat.le_trans (h.stieltjes_lo_le n)
      (h.witness_le_candidate_hi n)⟩

/-! A runtime-safe dyadic evaluator.

The raw nested-radical sums have shrinking widths, but their finite boxes are
not yet proved nested.  Prefix stabilization repairs exactly that defect by
intersecting finite-radius enlargements of the candidate boxes.  The
stabilized computation still reads only the candidate sums and the rational
radius schedule; the Stieltjes value occurs only in the certificate. -/
def dyadicNestedRadicalIntegralRaw_stabilized : RealCompute :=
  RealCompute.prefixStabilize dyadicNestedRadicalIntegralRaw
    (fun n => (sinPiStieltjesIntegral.compute n).width)

theorem dyadicNestedRadicalIntegralRaw_stabilized_valid_of_overlap
    (hoverlap : forall n,
      QInterval.Overlaps
        (dyadicNestedRadicalLeftSum n)
        (sinPiStieltjesIntegral.compute n)) :
    dyadicNestedRadicalIntegralRaw_stabilized.Valid := by
  apply RealCompute.prefixStabilize_valid
    (candidate := dyadicNestedRadicalIntegralRaw)
    (anchor := sinPiStieltjesIntegral)
  · exact dyadicNestedRadicalIntegralRaw_widths_shrink
  · exact sinPiStieltjesIntegral_valid
  · exact dyadicNestedRadicalIntegralRaw_equiv_of_overlap
      sinPiStieltjesIntegral hoverlap
  · intro n
    apply Rat.le_refl
  · exact sinPiStieltjesIntegral_valid.2.2

theorem dyadicNestedRadicalIntegralRaw_stabilized_equiv_reciprocalPi_of_overlap
    (hoverlap : forall n,
      QInterval.Overlaps
        (dyadicNestedRadicalLeftSum n)
        (sinPiStieltjesIntegral.compute n)) :
    dyadicNestedRadicalIntegralRaw_stabilized.Equiv reciprocalPiRaw := by
  have hvalid : dyadicNestedRadicalIntegralRaw_stabilized.Valid :=
    dyadicNestedRadicalIntegralRaw_stabilized_valid_of_overlap hoverlap
  have hanchor : sinPiStieltjesIntegral.Equiv reciprocalPiRaw :=
    sinPiStieltjesIntegral_equiv_reciprocalPi
  have hstabilized :
      dyadicNestedRadicalIntegralRaw_stabilized.Equiv
        sinPiStieltjesIntegral := by
    apply RealCompute.prefixStabilize_equiv_anchor
      sinPiStieltjesIntegral_valid
      (dyadicNestedRadicalIntegralRaw_equiv_of_overlap
        sinPiStieltjesIntegral hoverlap)
    intro n
    apply Rat.le_refl
  exact RealCompute.equiv_trans hvalid sinPiStieltjesIntegral_valid
    reciprocalPiRaw_valid hstabilized hanchor

theorem dyadicNestedRadicalIntegralRaw_stabilized_equiv_reciprocalPi_of_commonWitness
    (h : DyadicNestedRadicalStieltjesCommonWitness) :
    dyadicNestedRadicalIntegralRaw_stabilized.Equiv reciprocalPiRaw := by
  apply dyadicNestedRadicalIntegralRaw_stabilized_equiv_reciprocalPi_of_overlap
  exact h.to_overlap

/-! A named contract for the specialized evaluator.  The implementation may
use nested radicals, Taylor boxes, or another finite algebraic method; the
contract deliberately exposes only the facts needed by the dyadic integral.
-/
structure DyadicNestedRadicalRoute
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2)) where
  evaluator : RealFunRaw
  integral : Integral.SampleConstruction evaluator
    0 ((1 : Rat) / 2)
  dyadic_plan : pub.plan = Integral.staticDyadicPlan
  same_plan : pub.plan = integral.plan
  sample_overlap : forall n k,
    k < (pub.plan n).subdivisions ->
    QInterval.Overlaps
      (S.onHalf.toRealFunRaw.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision)
      (evaluator.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision)

/-! A constructor-oriented certificate for the route above.  It separates
the reusable finite search proof from the evaluator-specific facts: the
specialized evaluator identifies its sampled box with the nested-radical
table, while the inverse-chart search supplies a rational witness in the
public sine box and that table box. -/
structure DyadicNestedRadicalRouteSearchData
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2)) where
  evaluator : RealFunRaw
  integral : Integral.SampleConstruction evaluator
    0 ((1 : Rat) / 2)
  dyadic_plan : pub.plan = Integral.staticDyadicPlan
  same_plan : pub.plan = integral.plan
  searchPrecision : Nat -> Nat -> Nat
  evaluator_sample : forall n k,
    k < (pub.plan n).subdivisions ->
    evaluator.compute
      (leftPoint 0 ((1 : Rat) / 2)
        (pub.plan n).subdivisions k)
      (pub.plan n).evalPrecision =
      dyadicNestedRadicalStageSinAt n k
  tangent_box : forall n k,
    k < (pub.plan n).subdivisions ->
    QInterval
  tangent_box_bounds : forall n k,
    (hk : k < (pub.plan n).subdivisions) ->
    subintervalOf (tangent_box n k hk) 0 1
  public_box_eq_circle : forall n k,
    (hk : k < (pub.plan n).subdivisions) ->
    S.onHalf.toRealFunRaw.compute
      (leftPoint 0 ((1 : Rat) / 2)
        (pub.plan n).subdivisions k)
      (pub.plan n).evalPrecision =
      rationalCircleSinInterval (tangent_box n k hk)
  table_box_bounds : forall n k,
    k < (pub.plan n).subdivisions ->
    subintervalOf (dyadicNestedRadicalStageSinAt n k) 0 1
  search : forall n k (hk : k < (pub.plan n).subdivisions),
    ∃ u, rationalTangentWitnessBoxSearch
      (tangent_box n k hk)
      (dyadicNestedRadicalStageSinAt n k)
      (searchPrecision n k) = some u

def DyadicNestedRadicalRouteSearchData.toRoute
    {S : ArctanSinPiConstruction}
    {pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2)}
    (d : DyadicNestedRadicalRouteSearchData S pub) :
    DyadicNestedRadicalRoute S pub where
  evaluator := d.evaluator
  integral := d.integral
  dyadic_plan := d.dyadic_plan
  same_plan := d.same_plan
  sample_overlap := by
    intro n k hk
    obtain ⟨u, hu⟩ := d.search n k hk
    have hover := rationalTangentWitnessBoxSearch_overlap_of_success
      (d.tangent_box_bounds n k hk)
      (d.table_box_bounds n k hk) hu
    have hsample := d.evaluator_sample n k hk
    simpa only [d.public_box_eq_circle n k hk, hsample] using hover

theorem DyadicNestedRadicalRoute.public_equiv_evaluator
    {S : ArctanSinPiConstruction}
    {pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2)}
    (route : DyadicNestedRadicalRoute S pub) :
    (S.halfIntegral pub).Equiv
      (Integral.sampleValue route.evaluator 0 ((1 : Rat) / 2) route.integral) := by
  exact Integral.integral_equiv_of_plan_and_sample_overlaps
    (by decide +kernel : (0 : Rat) <= (1 : Rat) / 2)
    pub route.integral route.same_plan route.sample_overlap

/-! The two implementations now meet at one theorem.  The nested-radical
route proves equality with the public dyadic integral at its finite sample
points; the transport certificate proves equality of that public integral
with the uneven tangent-chart computation. -/

theorem DyadicNestedRadicalRoute.integral_equiv_reciprocalPi
    {S : ArctanSinPiConstruction}
    {pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2)}
    (route : DyadicNestedRadicalRoute S pub)
    (htransport : S.TangentChartTransport pub) :
    (Integral.sampleValue route.evaluator 0 ((1 : Rat) / 2)
      route.integral).Equiv reciprocalPiRaw := by
  have hroute := route.public_equiv_evaluator
  have hpublic := htransport.equivalent
  have hnested := FTC.integral_valid_of_construction route.integral
  have hpubvalid := S.halfIntegral_valid pub
  have hroute' :
      (Integral.sampleValue route.evaluator 0 ((1 : Rat) / 2)
        route.integral).Equiv (S.halfIntegral pub) :=
    RealCompute.equiv_symm hroute
  have hnestedChart :
      (Integral.sampleValue route.evaluator 0 ((1 : Rat) / 2)
        route.integral).Equiv tangentChartIntegral :=
    RealCompute.equiv_trans hnested hpubvalid tangentChartIntegral_valid
      hroute' hpublic
  exact RealCompute.equiv_trans hnested tangentChartIntegral_valid
    reciprocalPiRaw_valid hnestedChart tangentChartIntegral_equiv_reciprocalPi

theorem DyadicNestedRadicalRouteSearchData.integral_equiv_reciprocalPi
    {S : ArctanSinPiConstruction}
    {pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2)}
    (d : DyadicNestedRadicalRouteSearchData S pub)
    (htransport : S.TangentChartTransport pub) :
    (Integral.sampleValue d.evaluator 0 ((1 : Rat) / 2)
      d.integral).Equiv reciprocalPiRaw := by
  exact d.toRoute.integral_equiv_reciprocalPi htransport

/--
The exact reusable conclusion of the elementary sine-integral argument.

`F` is the computable primitive (normally the represented function
`-cos(pi*x)/pi`) and `hftc` is an effective, static-dyadic FTC certificate
for its derivative, which is the `sinPiOnHalf` evaluator.  The theorem does
not invoke Mathlib's real numbers: equality is `RealCompute.Equiv`, and the
certificate is made from finite rational interval computations.

The endpoint raw is deliberately returned by the theorem.  Once the
project's reciprocal-`pi` representation is connected to the endpoint, the
same theorem immediately yields the familiar notation
`integral = 1/pi`; the scaled form `pi * integral = 1` is obtained from the
corresponding endpoint identity without changing the integral algorithm.
-/
structure HalfIntegralFTCCertificate
    (C : FunctionRawConstruction)
    (hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)) where
  primitive : RealFunRaw
  primitive_valid : primitive.Valid
  endpoint_valid :
    RealCompute.ValidCompute
      (endpointDifferenceCompute primitive 0 ((1 : Rat) / 2))
  integral : Integral.SampleConstruction
    (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2)
  /-- The integral is computed by the project's fixed equal-dyadic plan. -/
  integral_plan : integral.plan = Integral.staticDyadicPlan
  ftc : CandidateEqualsEndpointDifference
    primitive (sinPiOnHalf C hdefined).toRealFunRaw 0 ((1 : Rat) / 2)
    integral endpoint_valid

theorem halfIntegral_equiv_endpoint
    {C : FunctionRawConstruction}
    {hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)}
    (h : HalfIntegralFTCCertificate C hdefined) :
    (halfIntegral C hdefined h.integral).Equiv
      (endpointDifferenceRaw h.primitive 0 ((1 : Rat) / 2) h.endpoint_valid) :=
  h.ftc

/-- Final value theorem for the public `sin (pi*x)` half-interval integral.

The finite FTC certificate identifies the fixed equal-dyadic integral with the
primitive's endpoint difference; an independent computable endpoint theorem
may then identify that difference with `reciprocalPiRaw`.  This composition is
the theorem-facing result and uses only `RealCompute.Equiv`. -/
theorem halfIntegral_equiv_reciprocalPi_of_FTC
    {C : FunctionRawConstruction}
    {hdefined : forall x, 0 <= x -> x <= (1 : Rat) / 2 ->
      C.sinFunctionRaw.definedAt (2 * x)}
    (h : HalfIntegralFTCCertificate C hdefined)
    (hendpoint :
      (endpointDifferenceRaw h.primitive 0 ((1 : Rat) / 2)
        h.endpoint_valid).Equiv reciprocalPiRaw) :
    (halfIntegral C hdefined h.integral).Equiv reciprocalPiRaw := by
  have hintegral := halfIntegral_valid C hdefined h.integral
  have hendpointValid :
      (endpointDifferenceRaw h.primitive 0 ((1 : Rat) / 2)
        h.endpoint_valid).Valid := by
    simpa [endpointDifferenceRaw, RealCompute.Valid] using h.endpoint_valid
  exact RealCompute.equiv_trans hintegral hendpointValid
    reciprocalPiRaw_valid (halfIntegral_equiv_endpoint h) hendpoint

/-- Preferred-API version of the same final assembly.  Once the sine evaluator
has an interval-regularity proof, a monotone Darboux schedule supplies the
equal-mesh integral directly through `CandidateConstructionFor`; the remaining FTC and
endpoint facts are ordinary `RealCompute.Equiv` certificates. -/
theorem ArctanSinPiConstruction.monotoneScheduleIntegral_equiv_reciprocalPi
    (S : ArctanSinPiConstruction)
    (hregular : IntervalRegularOn S.onHalf)
    (hmonotone : NondecreasingOnInterval S.onHalf)
    (hinterval : S.onHalf.lower <= S.onHalf.upper)
    (schedule : ComputableAnalysis.Integral.MonotoneDarbouxSchedule
      S.onHalf hregular hmonotone hinterval)
    (hFTC :
      (ComputableAnalysis.Integral.monotoneDarbouxScheduleCandidateValueFor schedule).Equiv
        (endpointDifferenceRaw S.canonicalPrimitive 0 ((1 : Rat) / 2)
          (endpointDifference_valid_of_fun_valid
            S.canonicalPrimitive_valid
            S.canonicalPrimitive_domain_zero
            S.canonicalPrimitive_domain_half)))
    (hendpoint :
      (endpointDifferenceRaw S.canonicalPrimitive 0 ((1 : Rat) / 2)
        (endpointDifference_valid_of_fun_valid
          S.canonicalPrimitive_valid
          S.canonicalPrimitive_domain_zero
          S.canonicalPrimitive_domain_half)).Equiv reciprocalPiRaw) :
    (ComputableAnalysis.Integral.monotoneDarbouxScheduleCandidateValueFor schedule).Equiv
      reciprocalPiRaw := by
  have hintegral :=
    ComputableAnalysis.Integral.monotoneDarbouxScheduleCandidateValueFor_valid schedule
  have hendpointValid :
      (endpointDifferenceRaw S.canonicalPrimitive 0 ((1 : Rat) / 2)
        (endpointDifference_valid_of_fun_valid
          S.canonicalPrimitive_valid
          S.canonicalPrimitive_domain_zero
          S.canonicalPrimitive_domain_half)).Valid := by
    simpa [endpointDifferenceRaw, RealCompute.Valid] using
      (endpointDifference_valid_of_fun_valid
        S.canonicalPrimitive_valid
        S.canonicalPrimitive_domain_zero
        S.canonicalPrimitive_domain_half)
  exact RealCompute.equiv_trans hintegral hendpointValid
    reciprocalPiRaw_valid hFTC hendpoint

/-- The theorem-facing specialization once the inverse branch has supplied
monotonicity and the two finite endpoint laws.  This keeps the analytic
certificate small at the call site: the circle monotonicity transport and the
reciprocal-pi endpoint algebra are assembled here. -/
theorem ArctanSinPiConstruction.monotoneScheduleIntegral_equiv_reciprocalPi_of_tangent_nondecreasing
    (S : ArctanSinPiConstruction)
    (htangent : NondecreasingOnInterval
      (IntegralIdentities.tangentOnUnit S.inverse))
    (hregular : IntervalRegularOn S.onHalf)
    (hinterval : S.onHalf.lower <= S.onHalf.upper)
    (schedule : ComputableAnalysis.Integral.MonotoneDarbouxSchedule
      S.onHalf hregular
      (S.onHalf_nondecreasing_of_tangent_nondecreasing htangent)
      hinterval)
    (hFTC :
      (ComputableAnalysis.Integral.monotoneDarbouxScheduleCandidateValueFor schedule).Equiv
        (endpointDifferenceRaw S.canonicalPrimitive 0 ((1 : Rat) / 2)
          (endpointDifference_valid_of_fun_valid
            S.canonicalPrimitive_valid
            S.canonicalPrimitive_domain_zero
            S.canonicalPrimitive_domain_half)))
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    (ht1 : (S.inverse.tangentAt 1
      RationalCircle.GeometricTrig.firstQuadrantBranch_one).Equiv
      RealCompute.one) :
    (ComputableAnalysis.Integral.monotoneDarbouxScheduleCandidateValueFor schedule).Equiv
      reciprocalPiRaw := by
  apply S.monotoneScheduleIntegral_equiv_reciprocalPi
    hregular
    (S.onHalf_nondecreasing_of_tangent_nondecreasing htangent)
    hinterval schedule hFTC
  simpa [canonicalSineEndpointIntegral] using
    (canonicalSineEndpointIntegral_equiv_reciprocalPi S ht0 ht1)

/-! The complete precision-aware interface for the nested-radical route.  A
certificate family is the only geometric input: once supplied at every
precision and every dyadic sample, the public equal-dyadic integral is
equivalent to the integral of the evaluator whose samples are the nested
radical table. -/
theorem ArctanSinPiConstruction.halfIntegral_equiv_of_certificate_family
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    (hcertificate : forall (n k : Nat) (hk : k < 2 ^ n), 0 < k ->
      forall precision,
        CanonicalDyadicHalfAngleCertificateAt S.inverse precision n k hk) :
    (S.halfIntegral pub).Equiv
      (Integral.sampleValue g 0 ((1 : Rat) / 2) cg) := by
  apply S.halfIntegral_equiv_of_precisionAware_nestedRadical_semantics
    pub g cg hdyadic hplan hevaluator
  intro n k hk
  exact arctanSinPi_nestedRadicalSample_equiv_of_certificate_family
    S.inverse ht0 hk (hcertificate n k hk)

/- The precision-first form is convenient for geometric constructions that
   refine evaluator boxes before choosing the native stage. -/
theorem ArctanSinPiConstruction.halfIntegral_equiv_of_precision_first_certificate_family
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    (hcertificate : forall (precision n k : Nat) (hk : k < 2 ^ n),
      0 < k -> CanonicalDyadicHalfAngleCertificateAt S.inverse precision n k hk) :
    (S.halfIntegral pub).Equiv
      (Integral.sampleValue g 0 ((1 : Rat) / 2) cg) := by
  apply S.halfIntegral_equiv_of_certificate_family
    pub g cg hdyadic hplan hevaluator ht0
  intro n k hk hpos precision
  exact hcertificate precision n k hk hpos

theorem ArctanSinPiConstruction.halfIntegral_equiv_of_overlap_family
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    (hover : forall (n k : Nat) (hk : k < 2 ^ n), 0 < k ->
      forall precision, QInterval.Overlaps
        (rationalCircleSinInterval
          (dyadicTangentBoxAt S.inverse precision n k hk))
        ((dyadicNestedRadicalTableAt precision n k).1)) :
    (S.halfIntegral pub).Equiv
      (Integral.sampleValue g 0 ((1 : Rat) / 2) cg) := by
  apply S.halfIntegral_equiv_of_precisionAware_nestedRadical_semantics
    pub g cg hdyadic hplan hevaluator
  intro n k hk
  exact arctanSinPi_nestedRadicalSample_equiv_of_overlap_family
    S.inverse ht0 hk (hover n k hk)

theorem ArctanSinPiConstruction.halfIntegral_equiv_of_branch_certificate_family
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (family : DyadicNestedRadicalBranchCertificateFamily S.inverse) :
    (S.halfIntegral pub).Equiv
      (Integral.sampleValue g 0 ((1 : Rat) / 2) cg) := by
  apply S.halfIntegral_equiv_of_overlap_family
    pub g cg hdyadic hplan hevaluator family.endpoint_zero
  intro n k hk hpos precision
  exact family.rational_circle_overlap precision n k hk

theorem ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi_of_branch_certificate_family
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (family : DyadicNestedRadicalBranchCertificateFamily S.inverse)
    (hintegral :
      (Integral.sampleValue g 0 ((1 : Rat) / 2) cg).Equiv reciprocalPiRaw) :
    (S.halfIntegral pub).Equiv reciprocalPiRaw := by
  exact RealCompute.equiv_trans
    (S.halfIntegral_valid pub)
    (FTC.integral_valid_of_construction cg)
    reciprocalPiRaw_valid
    (S.halfIntegral_equiv_of_branch_certificate_family
      pub g cg hdyadic hplan hevaluator family)
    hintegral

structure DyadicTangentWitnessFamily
    (B : IntegralIdentities.ArctanInverseBisection) where
  schedule : forall (depth k : Nat) (hk : k < 2 ^ depth),
    DyadicTangentWitnessSchedule B depth k hk

/-! A named package for the geometric part of the equal-dyadic proof.

The zero sample is handled by the exact endpoint equivalence; every positive
dyadic sample is supplied with a rational half-angle certificate at every
evaluator precision.  The conversion below is intentionally noncomputable:
the certificate proves that a finite search succeeds, while the executable
search itself remains the evaluator-facing object. -/
structure DyadicCanonicalCertificateFamily
    (B : IntegralIdentities.ArctanInverseBisection) where
  zero_equiv : (B.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero
  interior : forall (depth k : Nat) (hk : k < 2 ^ depth), 0 < k ->
    forall precision,
      CanonicalDyadicHalfAngleCertificateAt B precision depth k hk

noncomputable def DyadicCanonicalCertificateFamily.toWitnessFamily
    {B : IntegralIdentities.ArctanInverseBisection}
    (C : DyadicCanonicalCertificateFamily B) :
    DyadicTangentWitnessFamily B where
  schedule := fun depth k hk => by
    by_cases hkzero : k = 0
    · subst k
      let hsearch := fun precision =>
        canonical_dyadic_zero_search_at B C.zero_equiv precision depth
          (Nat.pow_pos (by omega : 0 < 2))
      exact {
        witness := fun precision => Classical.choose (hsearch precision)
        searchPrecision := fun _ => 0
        search := by
          intro precision
          simpa [dyadicNestedRadicalTableAt_zero_sin] using
            Classical.choose_spec (hsearch precision) }
    · let hsearch := fun precision =>
        canonical_dyadic_search_at_family B C.zero_equiv hk
          (fun hpos => C.interior depth k hk hpos) precision
      exact {
        witness := fun precision =>
          Classical.choose (Classical.choose_spec (hsearch precision))
        searchPrecision := fun precision => Classical.choose (hsearch precision)
        search := by
          intro precision
          exact Classical.choose_spec (Classical.choose_spec (hsearch precision)) }

theorem ArctanSinPiConstruction.halfIntegral_equiv_of_witness_family
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (family : DyadicTangentWitnessFamily S.inverse) :
    (S.halfIntegral pub).Equiv
      (Integral.sampleValue g 0 ((1 : Rat) / 2) cg) := by
  apply S.halfIntegral_equiv_of_precisionAware_nestedRadical_semantics
    pub g cg hdyadic hplan hevaluator
  intro n k hk
  exact arctanSinPi_nestedRadicalSample_equiv_of_witness_schedule
    (family.schedule n k hk)

theorem ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi_of_witness_family
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (family : DyadicTangentWitnessFamily S.inverse)
    (hintegral : (Integral.sampleValue g 0 ((1 : Rat) / 2) cg).Equiv
      reciprocalPiRaw) :
    (S.halfIntegral pub).Equiv reciprocalPiRaw := by
  exact RealCompute.equiv_trans
    (S.halfIntegral_valid pub)
    (FTC.integral_valid_of_construction cg)
    reciprocalPiRaw_valid
    (S.halfIntegral_equiv_of_witness_family pub g cg hdyadic hplan
      hevaluator family)
    hintegral

/-! The named certificate-family entry point is the preferred theorem-facing
API. It hides only the noncomputable choice of a successful finite search;
the geometric certificates and the independent integral equivalence remain
explicit inputs. -/
theorem ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi_of_canonical_certificate_family
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (family : DyadicCanonicalCertificateFamily S.inverse)
    (hintegral :
      (Integral.sampleValue g 0 ((1 : Rat) / 2) cg).Equiv reciprocalPiRaw) :
    (S.halfIntegral pub).Equiv reciprocalPiRaw := by
  exact S.halfIntegral_equiv_reciprocalPi_of_witness_family
    pub g cg hdyadic hplan hevaluator family.toWitnessFamily hintegral

theorem ArctanSinPiConstruction.halfIntegral_equiv_of_branch_certificates
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    (zero_overlap : forall (precision depth : Nat) (hk : 0 < 2 ^ depth),
      QInterval.Overlaps
        ((sinPiRawOfArctan S.inverse
          (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) 0)
          (dyadicHalfDomain (by omega))).compute precision)
        (dyadicNestedRadicalTableAt precision depth 0).1)
    (even_certificate : forall (precision n j : Nat) (hj : j < 2 ^ n),
      DyadicEvenStepCertificate S.inverse precision n j hj)
    (lower_certificate : forall (precision n j : Nat)
      (hbound : 2 * j + 1 <= 2 ^ n),
      DyadicHalfAngleChildCertificate S.inverse precision n j hbound)
    (upper_certificate : forall (precision n k : Nat)
      (hupper : 2 ^ n < k) (hk : k < 2 ^ (n + 1)),
      DyadicReflectedHalfAngleCertificate S.inverse precision n k hupper hk) :
    (S.halfIntegral pub).Equiv
      (Integral.sampleValue g 0 ((1 : Rat) / 2) cg) := by
  apply S.halfIntegral_equiv_of_overlap_family
    pub g cg hdyadic hplan hevaluator ht0
  intro n k hk hpos precision
  have hsample :=
    dyadicNestedRadical_sample_overlap_of_branch_certificates
      S.inverse zero_overlap even_certificate lower_certificate
      upper_certificate precision n k hk
  simpa [sinPiRawOfArctan, dyadicTangentBoxAt] using hsample

theorem ArctanSinPiConstruction.halfIntegral_equiv_reciprocalPi_of_branch_certificates
    (S : ArctanSinPiConstruction)
    (pub : Integral.SampleConstruction S.onHalf.toRealFunRaw
      0 ((1 : Rat) / 2))
    (g : RealFunRaw)
    (cg : Integral.SampleConstruction g 0 ((1 : Rat) / 2))
    (hdyadic : pub.plan = Integral.staticDyadicPlan)
    (hplan : pub.plan = cg.plan)
    (hevaluator : forall n k,
      k < (pub.plan n).subdivisions ->
      g.compute
        (leftPoint 0 ((1 : Rat) / 2)
          (pub.plan n).subdivisions k)
        (pub.plan n).evalPrecision =
        dyadicNestedRadicalStageSinAt n k)
    (ht0 : (S.inverse.tangentAt 0
      RationalCircle.GeometricTrig.firstQuadrantBranch_zero).Equiv
      RealCompute.zero)
    (zero_overlap : forall (precision depth : Nat) (hk : 0 < 2 ^ depth),
      QInterval.Overlaps
        ((sinPiRawOfArctan S.inverse
          (leftPoint 0 ((1 : Rat) / 2) (2 ^ depth) 0)
          (dyadicHalfDomain (by omega))).compute precision)
        (dyadicNestedRadicalTableAt precision depth 0).1)
    (even_certificate : forall (precision n j : Nat) (hj : j < 2 ^ n),
      DyadicEvenStepCertificate S.inverse precision n j hj)
    (lower_certificate : forall (precision n j : Nat)
      (hbound : 2 * j + 1 <= 2 ^ n),
      DyadicHalfAngleChildCertificate S.inverse precision n j hbound)
    (upper_certificate : forall (precision n k : Nat)
      (hupper : 2 ^ n < k) (hk : k < 2 ^ (n + 1)),
      DyadicReflectedHalfAngleCertificate S.inverse precision n k hupper hk)
    (hintegral :
      (Integral.sampleValue g 0 ((1 : Rat) / 2) cg).Equiv reciprocalPiRaw) :
    (S.halfIntegral pub).Equiv reciprocalPiRaw := by
  have hpub := S.halfIntegral_equiv_of_branch_certificates
    pub g cg hdyadic hplan hevaluator ht0 zero_overlap
    even_certificate lower_certificate upper_certificate
  exact RealCompute.equiv_trans
    (S.halfIntegral_valid pub)
    (FTC.integral_valid_of_construction cg)
    reciprocalPiRaw_valid hpub hintegral

end SinPiIntegral

end ComputableAnalysis


