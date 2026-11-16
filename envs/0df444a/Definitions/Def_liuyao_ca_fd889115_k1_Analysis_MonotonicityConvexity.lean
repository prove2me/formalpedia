-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_MonotonicityConvexity
-- name    : liuyao_ca_fd889115_k1_Analysis_MonotonicityConvexity
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:56:44.989567+00:00
-- url     : https://prove2.me/theorems/d112df8e-6258-4aca-8a0c-757bd83c489a
-- title:
--   Computable analysis · MonotonicityConvexity · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/MonotonicityConvexity.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_AlgebraicFunctions
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Calculus

set_option autoImplicit true

/-!
# Monotonicity and convexity for interval-valued computable functions

This file defines monotonicity and convexity directly for rational-input
interval algorithms of the form `n, t ↦ [a_n(t), b_n(t)]`.
-/

namespace ComputableAnalysis

/-- Raw-real secant of a rational-input raw function.  This is the exact
object used in the new convexity statement; finite interval slope enclosures
are its stages. -/
def secantRaw (F : RealFunRaw) (x y : Rat) : RealCompute where
  compute := fun n => secantSlopeIntervalOfRealFun F x y n

/-- A positive rationally separated secant of a valid raw function is itself
valid.  This is the representation-level fact used by both convexity and
derivative certificates; it does not depend on the convexity hypothesis. -/
theorem secantRaw_valid_of_valid
    {F : RealFunRaw} {x y : Rat}
    (hx : RealCompute.ValidCompute (F.applyCompute x))
    (hy : RealCompute.ValidCompute (F.applyCompute y)) (hxy : x < y) :
    (secantRaw F x y).Valid := by
  let X : RealCompute := { compute := F.compute x }
  let Y : RealCompute := { compute := F.compute y }
  have hX : X.Valid := by
    simpa [X, RealCompute.Valid, RealFunRaw.applyCompute] using hx
  have hY : Y.Valid := by
    simpa [Y, RealCompute.Valid, RealFunRaw.applyCompute] using hy
  have hden_pos : 0 < y - x := by
    rw [← Rat.lt_iff_sub_pos]
    exact hxy
  have hscale_nonneg : 0 <= 1 / (y - x) := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 hden_pos)
  have hscale :
      (RealCompute.scaleRat (1 / (y - x)) (Y - X)).Valid :=
    RealCompute.scaleRat_valid_of_nonneg hscale_nonneg
      (RealCompute.sub_valid hY hX)
  change RealCompute.ValidCompute
    (RealCompute.scaleRatCompute (1 / (y - x)) (Y - X))
  exact hscale

/-- Exact convexity on rational points of a rational interval.

Unlike `CurvatureOnSubinterval`, this is not an effective finite-stage
certificate.  It is the mathematical convexity property expressed with the
exact raw-real order `RealCompute.Le`: right secants are above left secants. -/
structure ExactConvexOn (F : RealFunRaw) (a b : Rat) where
  domain_on : forall x, inDomainInterval a b x -> F.domain x
  valid_on : forall x, inDomainInterval a b x ->
    RealCompute.ValidCompute (F.applyCompute x)
  secant_mono :
    forall w x y z,
      inDomainInterval a b w ->
      inDomainInterval a b x ->
      inDomainInterval a b y ->
      inDomainInterval a b z ->
      w < x ->
      x <= y ->
      y < z ->
        (secantRaw F w x).Le (secantRaw F y z)

namespace ExactConvexOn

theorem secant_le_secant
    {F : RealFunRaw} {a b w x y z : Rat}
    (hF : ExactConvexOn F a b)
    (hw : inDomainInterval a b w)
    (hx : inDomainInterval a b x)
    (hy : inDomainInterval a b y)
    (hz : inDomainInterval a b z)
    (hwx : w < x) (hxy : x <= y) (hyz : y < z) :
    (secantRaw F w x).Le (secantRaw F y z) :=
  hF.secant_mono w x y z hw hx hy hz hwx hxy hyz

theorem secantRaw_valid
    {F : RealFunRaw} {a b x y : Rat}
    (hF : ExactConvexOn F a b)
    (hx : inDomainInterval a b x)
    (hy : inDomainInterval a b y)
    (hxy : x < y) :
    (secantRaw F x y).Valid := by
  exact secantRaw_valid_of_valid
    (hF.valid_on x hx) (hF.valid_on y hy) hxy

end ExactConvexOn

/-- Right secant based at `q` with positive rational step `h`. -/
def rightSecantRaw (F : RealFunRaw) (q h : Rat) : RealCompute :=
  secantRaw F q (q + h)

/-- Left secant ending at `q` with positive rational step `h`. -/
def leftSecantRaw (F : RealFunRaw) (q h : Rat) : RealCompute :=
  secantRaw F (q - h) q

/-- Exact certificate that a supplied raw interval algorithm `D` is the right
derivative of a convex function at `q`: it is the greatest lower bound of the
right secants based at `q`.

This characterizes a concrete `D`; it does not obtain `D` from a completeness
principle.  A derivative construction must separately supply `D` and its
validity certificate through `RightDerivativeAt`. -/
structure IsRightDerivative
    {F : RealFunRaw} {a b q : Rat}
    (hF : ExactConvexOn F a b) (D : RealCompute) where
  q_mem : inDomainInterval a b q
  q_lt_upper : q < b
  lower_bound :
    forall h,
      0 < h ->
      q + h <= b ->
        D.Le (rightSecantRaw F q h)
  greatest_lower_bound :
    forall Y : RealCompute,
      (forall h, 0 < h -> q + h <= b ->
        Y.Le (rightSecantRaw F q h)) ->
          Y.Le D

/-- Exact certificate that a supplied raw interval algorithm `D` is the left
derivative of a convex function at `q`: it is the least upper bound of the
left secants ending at `q`.

This is a verification interface for an explicit `D`, not an appeal to a
completed real-number supremum construction. -/
structure IsLeftDerivative
    {F : RealFunRaw} {a b q : Rat}
    (hF : ExactConvexOn F a b) (D : RealCompute) where
  q_mem : inDomainInterval a b q
  lower_lt_q : a < q
  upper_bound :
    forall h,
      0 < h ->
      a <= q - h ->
        (leftSecantRaw F q h).Le D
  least_upper_bound :
    forall Y : RealCompute,
      (forall h, 0 < h -> a <= q - h ->
        (leftSecantRaw F q h).Le Y) ->
          D.Le Y

structure RightDerivativeAt
    {F : RealFunRaw} {a b : Rat}
    (hF : ExactConvexOn F a b) (q : Rat) where
  raw : RealCompute
  valid : raw.Valid
  isRightDerivative : IsRightDerivative (q := q) hF raw

structure LeftDerivativeAt
    {F : RealFunRaw} {a b : Rat}
    (hF : ExactConvexOn F a b) (q : Rat) where
  raw : RealCompute
  valid : raw.Valid
  isLeftDerivative : IsLeftDerivative (q := q) hF raw

theorem rightDerivativeAt_mono
    {F : RealFunRaw} {a b q1 q2 : Rat}
    {hF : ExactConvexOn F a b}
    (D1 : RightDerivativeAt hF q1)
    (D2 : RightDerivativeAt hF q2)
    (hq12 : q1 < q2) :
    D1.raw.Le D2.raw := by
  refine D2.isRightDerivative.greatest_lower_bound D1.raw ?_
  intro h2 hh2_pos hq2h2_le
  have hq1_mem := D1.isRightDerivative.q_mem
  have hq2_mem := D2.isRightDerivative.q_mem
  have hq2h2_mem : inDomainInterval a b (q2 + h2) := by
    unfold inDomainInterval at *
    constructor <;> grind
  have hq1_to_q2_le :
      D1.raw.Le (secantRaw F q1 q2) := by
    have hstep_pos : 0 < q2 - q1 := by
      rw [←Rat.lt_iff_sub_pos]
      exact hq12
    have hstep_upper : q1 + (q2 - q1) <= b := by
      unfold inDomainInterval at hq2_mem
      grind
    have hendpoint : q1 + (q2 - q1) = q2 := by
      grind
    simpa [rightSecantRaw, hendpoint] using
      D1.isRightDerivative.lower_bound (q2 - q1) hstep_pos hstep_upper
  have hsec_le :
      (secantRaw F q1 q2).Le (rightSecantRaw F q2 h2) := by
    have hq2_lt_q2h2 : q2 < q2 + h2 := by
      grind
    simpa [rightSecantRaw] using
      hF.secant_le_secant hq1_mem hq2_mem hq2_mem hq2h2_mem
        hq12 (Rat.le_refl : q2 <= q2) hq2_lt_q2h2
  have hsec_valid :
      (secantRaw F q1 q2).Valid :=
    hF.secantRaw_valid hq1_mem hq2_mem hq12
  exact RealCompute.le_trans hsec_valid hq1_to_q2_le hsec_le

/-- The supplied left derivatives of a convex function are monotone.  The
finite proof transports every left secant ending at `q₁` through the bridge
secant from `q₁` to `q₂`, then applies the least-upper-bound certificate at
`q₂`; no supremum or completed limit is constructed. -/
theorem leftDerivativeAt_mono
    {F : RealFunRaw} {a b q1 q2 : Rat}
    {hF : ExactConvexOn F a b}
    (D1 : LeftDerivativeAt hF q1)
    (D2 : LeftDerivativeAt hF q2)
    (hq12 : q1 < q2) :
    D1.raw.Le D2.raw := by
  refine D1.isLeftDerivative.least_upper_bound D2.raw ?_
  intro h1 hh1_pos hq1h1_le
  have hq1_mem := D1.isLeftDerivative.q_mem
  have hq2_mem := D2.isLeftDerivative.q_mem
  have hq1h1_mem : inDomainInterval a b (q1 - h1) := by
    unfold inDomainInterval at *
    constructor <;> grind
  have hleft_le_bridge :
      (leftSecantRaw F q1 h1).Le (secantRaw F q1 q2) := by
    have hq1h1_lt_q1 : q1 - h1 < q1 := by grind
    simpa [leftSecantRaw] using
      hF.secant_le_secant hq1h1_mem hq1_mem hq1_mem hq2_mem
        hq1h1_lt_q1 (Rat.le_refl : q1 <= q1) hq12
  have hbridge_valid :
      (secantRaw F q1 q2).Valid :=
    hF.secantRaw_valid hq1_mem hq2_mem hq12
  have hbridge_le_right :
      (secantRaw F q1 q2).Le D2.raw := by
    have hstep_pos : 0 < q2 - q1 := by
      rw [← Rat.lt_iff_sub_pos]
      exact hq12
    have hstep_lower : a <= q2 - (q2 - q1) := by
      unfold inDomainInterval at hq1_mem
      grind
    have hendpoint : q2 - (q2 - q1) = q1 := by grind
    simpa [leftSecantRaw, hendpoint] using
      D2.isLeftDerivative.upper_bound (q2 - q1) hstep_pos hstep_lower
  exact RealCompute.le_trans hbridge_valid hleft_le_bridge hbridge_le_right

/-! At a convex corner, the supplied left derivative cannot exceed the
supplied right derivative.  The proof uses one finite right secant as an
upper bound for every left secant; it does not identify either derivative
with an attained limiting value. -/
theorem leftDerivativeAt_le_rightDerivativeAt
    {F : RealFunRaw} {a b q : Rat}
    {hF : ExactConvexOn F a b}
    (Dleft : LeftDerivativeAt hF q)
    (Dright : RightDerivativeAt hF q) :
    Dleft.raw.Le Dright.raw := by
  refine Dleft.isLeftDerivative.least_upper_bound Dright.raw ?_
  intro hleft hleft_pos hleft_lower
  have hq_mem := Dleft.isLeftDerivative.q_mem
  have hq_left_mem : inDomainInterval a b (q - hleft) := by
    unfold inDomainInterval at *
    constructor <;> grind
  refine Dright.isRightDerivative.greatest_lower_bound
    (leftSecantRaw F q hleft) ?_
  intro hright hright_pos _hright_upper
  have hright_endpoint_mem : inDomainInterval a b (q + hright) := by
    unfold inDomainInterval at *
    constructor <;> grind
  have hleft_lt : q - hleft < q := by grind
  have hright_lt : q < q + hright := by grind
  simpa [leftSecantRaw, rightSecantRaw] using
    hF.secant_le_secant hq_left_mem hq_mem hq_mem hright_endpoint_mem
      hleft_lt (Rat.le_refl : q <= q) hright_lt

/-! The derivative enclosure at an interior point is bounded by the two
neighboring endpoint secants.  This is the direct convex-function form of the
mean-value mechanism: it uses only the supplied secant certificates and
rational subtraction, with no attained intermediate point and no completed
real supremum. -/
theorem derivative_between_neighboring_secants
    {F : RealFunRaw} {a b q : Rat}
    {hF : ExactConvexOn F a b}
    (Dleft : LeftDerivativeAt hF q)
    (Dright : RightDerivativeAt hF q)
    (haq : a < q) (hqb : q < b) :
    (secantRaw F a q).Le Dleft.raw /\
      Dright.raw.Le (secantRaw F q b) := by
  constructor
  · have hstep : 0 < q - a := by
      rw [← Rat.lt_iff_sub_pos]
      exact haq
    have hleft : a <= q - (q - a) := by grind
    have hbound := Dleft.isLeftDerivative.upper_bound
      (q - a) hstep hleft
    have hendpoint : q - (q - a) = a := by grind
    simpa [leftSecantRaw, hendpoint] using hbound
  · have hstep : 0 < b - q := by
      rw [← Rat.lt_iff_sub_pos]
      exact hqb
    have hright : q + (b - q) <= b := by grind
    have hbound := Dright.isRightDerivative.lower_bound
      (b - q) hstep hright
    have hendpoint : q + (b - q) = b := by grind
    simpa [rightSecantRaw, hendpoint] using hbound

/-- Exact concavity is convexity with the secant order reversed. -/
structure ExactConcaveOn (F : RealFunRaw) (a b : Rat) where
  domain_on : forall x, inDomainInterval a b x -> F.domain x
  valid_on : forall x, inDomainInterval a b x ->
    RealCompute.ValidCompute (F.applyCompute x)
  secant_antimono :
    forall w x y z,
      inDomainInterval a b w ->
      inDomainInterval a b x ->
      inDomainInterval a b y ->
      inDomainInterval a b z ->
      w < x ->
      x <= y ->
      y < z ->
        (secantRaw F y z).Le (secantRaw F w x)

namespace IntervalFunction

/-- A rational-input interval algorithm, written in the user-facing order
`stage, input ↦ interval`. -/
abbrev Raw := Nat -> Rat -> QInterval

def ofRealFunRaw (F : RealFunRaw) : Raw :=
  fun n t => F.compute t n

def neg (F : Raw) : Raw :=
  fun n t => QInterval.scaleByRat (-1) (F n t)

/-- Weak interval monotonicity from `x` to `y`.

For interval algorithms, this is the robust monotonicity assertion: the stage `n`
enclosure at `x` is compatible with being no larger than the stage `n`
enclosure at `y`.  Strong separated order can be added later, but this weak
form is the one that survives overlapping computable enclosures. -/
def IncreasingFrom (F : Raw) (x y : Rat) : Prop :=
  x <= y /\ forall n, QInterval.WeakLe (F n x) (F n y)

def IncreasingOn (F : Raw) (a b : Rat) : Prop :=
  forall x y, a <= x -> x <= y -> y <= b ->
    IncreasingFrom F x y

def secantSlope (F : Raw) (n : Nat) (x y : Rat) : QInterval :=
  QInterval.slopeBetween (F n y) (F n x) (y - x)

/-- Convexity as monotonicity of rational secant slopes. -/
def ConvexOn (F : Raw) (a b : Rat) : Prop :=
  forall x y z,
    a <= x -> x < y -> y < z -> z <= b ->
      forall n,
        QInterval.WeakLe
          (secantSlope F n x y)
          (secantSlope F n y z)

/-- Concavity is convexity with the secant-slope order reversed. -/
def ConcaveOn (F : Raw) (a b : Rat) : Prop :=
  forall x y z,
    a <= x -> x < y -> y < z -> z <= b ->
      forall n,
        QInterval.WeakLe
          (secantSlope F n y z)
          (secantSlope F n x y)

/-- A stagewise bracket for all secant slopes inside `[u,v]`.

For a convex function, a typical way to build this is to choose rational
sample points `l < u` and `v < r`, then use the left secant `[l,u]` as the
lower slope enclosure and the right secant `[v,r]` as the upper slope
enclosure.  If the function switches monotonicity inside `[u,v]`, the bracket
simply crosses `0`; no special case is needed for derivative bounds. -/
structure SecantSlopeBracketOn (F : Raw) (u v : Rat) where
  lower : Nat -> QInterval
  upper : Nat -> QInterval
  bounds :
    forall n x y,
      u <= x -> x < y -> y <= v ->
        QInterval.WeakLe (lower n) (secantSlope F n x y) /\
        QInterval.WeakLe (secantSlope F n x y) (upper n)

/-- A strict interior version of `SecantSlopeBracketOn`.

This is the natural output of outer secants for a convex function: if
`l < u < x < y < v < r`, then the outer secants `[l,u]` and `[v,r]` bracket
the interior secant `[x,y]`. -/
structure StrictSecantSlopeBracketOn (F : Raw) (u v : Rat) where
  lower : Nat -> QInterval
  upper : Nat -> QInterval
  bounds :
    forall n x y,
      u < x -> x < y -> y < v ->
        QInterval.WeakLe (lower n) (secantSlope F n x y) /\
        QInterval.WeakLe (secantSlope F n x y) (upper n)

end IntervalFunction

namespace ConvexDerivative

/-- The finite interval used to compute the pointwise derivative of a convex
function at a rational point: take the hull of the left and right secants with
the same rational radius. -/
def centeredInterval (F : RealFunRaw) (q h : Rat) (prec : Nat) : QInterval :=
  QInterval.hull
    (secantSlopeIntervalOfRealFun F (q - h) q prec)
    (secantSlopeIntervalOfRealFun F q (q + h) prec)

/-- Finite core of "the derivative of a convex function is increasing".

If `q₁ < q₂` and the right secant used at `q₁` lies to the left of the left
secant used at `q₂`, convexity puts the derivative interval at `q₁` weakly
below the derivative interval at `q₂`.

The full derivative theorem then adds the extra data that these centered
intervals shrink to actual raw-real derivative values. -/
theorem centeredInterval_weakLe_of_convex
    {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    (H : CurvatureOnSubinterval F C)
    (hconv : H.kind = CurvatureKind.convex)
    {q₁ q₂ h₁ h₂ : Rat}
    (_hq₁_left : C.contains (q₁ - h₁))
    (hq₁ : C.contains q₁)
    (hq₁_right : C.contains (q₁ + h₁))
    (hq₂_left : C.contains (q₂ - h₂))
    (hq₂ : C.contains q₂)
    (_hq₂_right : C.contains (q₂ + h₂))
    (hq₁_right_pos : q₁ < q₁ + h₁)
    (hgap : q₁ + h₁ <= q₂ - h₂)
    (hq₂_left_pos : q₂ - h₂ < q₂)
    (n : Nat) :
    QInterval.WeakLe
      (centeredInterval F q₁ h₁ (H.evalPrecision n))
      (centeredInterval F q₂ h₂ (H.evalPrecision n)) := by
  have hsec := H.secant_slope_order n
      q₁ (q₁ + h₁) (q₂ - h₂) q₂
      hq₁ hq₁_right hq₂_left hq₂
      hq₁_right_pos hgap hq₂_left_pos
  rw [hconv] at hsec
  unfold QInterval.WeakLe centeredInterval QInterval.hull at *
  grind

/-! The concave counterpart reverses the derivative order.  The proof is the
same finite four-secant calculation, with the concavity branch of the
curvature certificate supplying the reversed outer-secant inequality. -/
theorem centeredInterval_weakLe_of_concave
    {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    (H : CurvatureOnSubinterval F C)
    (hconc : H.kind = CurvatureKind.concave)
    {q₁ q₂ h₁ h₂ : Rat}
    (_hq₁_left : C.contains (q₁ - h₁))
    (hq₁ : C.contains q₁)
    (hq₁_right : C.contains (q₁ + h₁))
    (hq₂_left : C.contains (q₂ - h₂))
    (hq₂ : C.contains q₂)
    (_hq₂_right : C.contains (q₂ + h₂))
    (hq₁_right_pos : q₁ < q₁ + h₁)
    (hgap : q₁ + h₁ <= q₂ - h₂)
    (hq₂_left_pos : q₂ - h₂ < q₂)
    (n : Nat) :
    QInterval.WeakLe
      (centeredInterval F q₂ h₂ (H.evalPrecision n))
      (centeredInterval F q₁ h₁ (H.evalPrecision n)) := by
  have hsec := H.secant_slope_order n
      q₁ (q₁ + h₁) (q₂ - h₂) q₂
      hq₁ hq₁_right hq₂_left hq₂
      hq₁_right_pos hgap hq₂_left_pos
  rw [hconc] at hsec
  unfold QInterval.WeakLe centeredInterval QInterval.hull at *
  grind

/-- A rational point with a certified rational neighborhood contained in the
convexity cell.  This is the "interior point" condition needed for centered
left and right secants. -/
structure InteriorPoint {a b : Rat} (C : RationalSubinterval a b) (q : Rat) where
  radius : Rat
  radius_pos : 0 < radius
  left_mem : C.contains (q - radius)
  center_mem : C.contains q
  right_mem : C.contains (q + radius)

/-- A pointwise derivative certificate for a convex function.

At stage `n`, the derivative enclosure is the hull of the left secant
`[q - h_n, q]` and the right secant `[q, q + h_n]`.  Convexity gives the
correct finite bounds; the final field records the example-specific proof that
these centered secant hulls really form a valid raw real. -/
structure Pointwise {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} (H : CurvatureOnSubinterval F C) (q : Rat) where
  convex : H.kind = CurvatureKind.convex
  interior : InteriorPoint C q
  step : Nat -> Rat
  step_pos : forall n, 0 < step n
  step_le_radius : forall n, step n <= interior.radius
  valid :
    RealCompute.ValidCompute
      (fun n => centeredInterval F q (step n) (H.evalPrecision n))

namespace Pointwise

def compute {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    {H : CurvatureOnSubinterval F C} {q : Rat}
    (D : Pointwise H q) (n : Nat) : QInterval :=
  centeredInterval F q (D.step n) (H.evalPrecision n)

def raw {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    {H : CurvatureOnSubinterval F C} {q : Rat}
    (D : Pointwise H q) : RealCompute where
  compute := D.compute

theorem raw_valid {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    {H : CurvatureOnSubinterval F C} {q : Rat}
    (D : Pointwise H q) : D.raw.Valid := by
  change RealCompute.ValidCompute
    (fun n => centeredInterval F q (D.step n) (H.evalPrecision n))
  exact D.valid

theorem left_mem {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    {H : CurvatureOnSubinterval F C} {q : Rat}
    (D : Pointwise H q) (n : Nat) :
    C.contains (q - D.step n) := by
  have hpos := D.step_pos n
  have hle := D.step_le_radius n
  have hleft := D.interior.left_mem
  have hcenter := D.interior.center_mem
  unfold RationalSubinterval.contains at *
  constructor <;> grind

theorem center_mem {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    {H : CurvatureOnSubinterval F C} {q : Rat}
    (D : Pointwise H q) :
    C.contains q :=
  D.interior.center_mem

theorem right_mem {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    {H : CurvatureOnSubinterval F C} {q : Rat}
    (D : Pointwise H q) (n : Nat) :
    C.contains (q + D.step n) := by
  have hpos := D.step_pos n
  have hle := D.step_le_radius n
  have hright := D.interior.right_mem
  have hcenter := D.interior.center_mem
  unfold RationalSubinterval.contains at *
  constructor <;> grind

theorem left_lt_center {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} {H : CurvatureOnSubinterval F C}
    {q : Rat} (D : Pointwise H q) (n : Nat) :
    q - D.step n < q := by
  have hpos := D.step_pos n
  grind

theorem center_lt_right {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} {H : CurvatureOnSubinterval F C}
    {q : Rat} (D : Pointwise H q) (n : Nat) :
    q < q + D.step n := by
  have hpos := D.step_pos n
  grind

/-- The pointwise derivative enclosures are increasing once the two centered
secant neighborhoods are disjoint.  This is the finite statement used later to
derive monotonicity of the derivative function. -/
theorem compute_weakLe_of_gap
    {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    {H : CurvatureOnSubinterval F C} {q1 q2 : Rat}
    (D1 : Pointwise H q1) (D2 : Pointwise H q2)
    (n : Nat)
    (hgap : q1 + D1.step n <= q2 - D2.step n) :
    QInterval.WeakLe (D1.compute n) (D2.compute n) := by
  simpa [compute] using
    centeredInterval_weakLe_of_convex
      H D1.convex
      (D1.left_mem n) (D1.center_mem) (D1.right_mem n)
      (D2.left_mem n) (D2.center_mem) (D2.right_mem n)
      (D1.center_lt_right n) hgap (D2.left_lt_center n) n

end Pointwise

/-- A rational-input derivative function assembled from pointwise convex
derivative certificates.  The domain is exactly the rational points for which
the centered secant hulls have been proved to converge. -/
structure PointwiseFunction {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} (H : CurvatureOnSubinterval F C) where
  domain : Rat -> Prop
  derivAt : forall q, domain q -> Pointwise H q

namespace PointwiseFunction

def toPartialRealFunRaw {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} {H : CurvatureOnSubinterval F C}
    (D : PointwiseFunction H) : PartialRealFunRaw where
  definedAt := D.domain
  compute := fun q hq n => (D.derivAt q hq).compute n

theorem partial_valid {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} {H : CurvatureOnSubinterval F C}
    (D : PointwiseFunction H) :
    forall q hq,
      RealCompute.ValidCompute (D.toPartialRealFunRaw.compute q hq) := by
  intro q hq
  simpa [toPartialRealFunRaw, Pointwise.compute] using (D.derivAt q hq).valid

noncomputable def toRealFunRaw {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} {H : CurvatureOnSubinterval F C}
    (D : PointwiseFunction H) : RealFunRaw := by
  classical
  exact
    { domain := D.domain
      compute := fun q n =>
        if hq : D.domain q then
          (D.derivAt q hq).compute n
        else
          { lo := 0, hi := 0 } }

theorem valid {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} {H : CurvatureOnSubinterval F C}
    (D : PointwiseFunction H) :
    D.toRealFunRaw.Valid := by
  intro q hq
  classical
  have hqD : D.domain q := by
    simpa [toRealFunRaw] using hq
  have hcompute :
      RealFunRaw.applyCompute D.toRealFunRaw q = (D.derivAt q hqD).compute := by
    funext n
    simp [toRealFunRaw, RealFunRaw.applyCompute, hqD, Pointwise.compute]
  rw [hcompute]
  change RealCompute.ValidCompute
    (fun n => centeredInterval F q
      ((D.derivAt q hqD).step n) (H.evalPrecision n))
  exact (D.derivAt q hqD).valid

end PointwiseFunction

end ConvexDerivative

/-! The same centered-secant construction works for concave primitives.  The
only change is the order: as the center moves right, the certified derivative
boxes move weakly left.  Keeping this as a separate namespace makes the
orientation visible to clients and avoids encoding concavity by negating a
particular raw evaluator. -/
namespace ConcaveDerivative

abbrev centeredInterval (F : RealFunRaw) (q h : Rat) (prec : Nat) : QInterval :=
  ConvexDerivative.centeredInterval F q h prec
abbrev InteriorPoint {a b : Rat} (C : RationalSubinterval a b) (q : Rat) :=
  ConvexDerivative.InteriorPoint C q

structure Pointwise {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} (H : CurvatureOnSubinterval F C) (q : Rat) where
  concave : H.kind = CurvatureKind.concave
  interior : InteriorPoint C q
  step : Nat -> Rat
  step_pos : forall n, 0 < step n
  step_le_radius : forall n, step n <= interior.radius
  valid :
    RealCompute.ValidCompute
      (fun n => centeredInterval F q (step n) (H.evalPrecision n))

namespace Pointwise

def compute {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    {H : CurvatureOnSubinterval F C} {q : Rat}
    (D : Pointwise H q) (n : Nat) : QInterval :=
  centeredInterval F q (D.step n) (H.evalPrecision n)

def raw {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    {H : CurvatureOnSubinterval F C} {q : Rat}
    (D : Pointwise H q) : RealCompute where
  compute := D.compute

theorem raw_valid {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    {H : CurvatureOnSubinterval F C} {q : Rat}
    (D : Pointwise H q) : D.raw.Valid := by
  change RealCompute.ValidCompute
    (fun n => centeredInterval F q (D.step n) (H.evalPrecision n))
  exact D.valid

theorem left_mem {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    {H : CurvatureOnSubinterval F C} {q : Rat}
    (D : Pointwise H q) (n : Nat) :
    C.contains (q - D.step n) := by
  have hpos := D.step_pos n
  have hle := D.step_le_radius n
  have hleft := D.interior.left_mem
  have hcenter := D.interior.center_mem
  unfold RationalSubinterval.contains at *
  constructor <;> grind

theorem center_mem {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    {H : CurvatureOnSubinterval F C} {q : Rat}
    (D : Pointwise H q) : C.contains q :=
  D.interior.center_mem

theorem right_mem {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    {H : CurvatureOnSubinterval F C} {q : Rat}
    (D : Pointwise H q) (n : Nat) :
    C.contains (q + D.step n) := by
  have hpos := D.step_pos n
  have hle := D.step_le_radius n
  have hright := D.interior.right_mem
  have hcenter := D.interior.center_mem
  unfold RationalSubinterval.contains at *
  constructor <;> grind

theorem left_lt_center {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} {H : CurvatureOnSubinterval F C}
    {q : Rat} (D : Pointwise H q) (n : Nat) :
    q - D.step n < q := by
  have hpos := D.step_pos n
  grind

theorem center_lt_right {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} {H : CurvatureOnSubinterval F C}
    {q : Rat} (D : Pointwise H q) (n : Nat) :
    q < q + D.step n := by
  have hpos := D.step_pos n
  grind

/-- Concave derivative boxes are antitone once the two centered neighborhoods
are disjoint. -/
theorem compute_weakLe_of_gap
    {F : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    {H : CurvatureOnSubinterval F C} {q1 q2 : Rat}
    (D1 : Pointwise H q1) (D2 : Pointwise H q2)
    (n : Nat)
    (hgap : q1 + D1.step n <= q2 - D2.step n) :
    QInterval.WeakLe (D2.compute n) (D1.compute n) := by
  simpa [compute] using
    ConvexDerivative.centeredInterval_weakLe_of_concave
      H D1.concave
      (D1.left_mem n) (D1.center_mem) (D1.right_mem n)
      (D2.left_mem n) (D2.center_mem) (D2.right_mem n)
      (D1.center_lt_right n) hgap (D2.left_lt_center n) n

end Pointwise

/-! A family of concave pointwise derivative certificates can be exposed as a
partial function on the rational domain where the centered secant hulls have
been proved to converge. -/
structure PointwiseFunction {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} (H : CurvatureOnSubinterval F C) where
  domain : Rat -> Prop
  derivAt : forall q, domain q -> Pointwise H q

namespace PointwiseFunction

def toPartialRealFunRaw {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} {H : CurvatureOnSubinterval F C}
    (D : PointwiseFunction H) : PartialRealFunRaw where
  definedAt := D.domain
  compute := fun q hq n => (D.derivAt q hq).compute n

theorem partial_valid {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} {H : CurvatureOnSubinterval F C}
    (D : PointwiseFunction H) :
    forall q hq,
      RealCompute.ValidCompute (D.toPartialRealFunRaw.compute q hq) := by
  intro q hq
  simpa [toPartialRealFunRaw, Pointwise.compute] using (D.derivAt q hq).valid

noncomputable def toRealFunRaw {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} {H : CurvatureOnSubinterval F C}
    (D : PointwiseFunction H) : RealFunRaw := by
  classical
  exact
    { domain := D.domain
      compute := fun q n =>
        if hq : D.domain q then
          (D.derivAt q hq).compute n
        else
          { lo := 0, hi := 0 } }

theorem valid {F : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b} {H : CurvatureOnSubinterval F C}
    (D : PointwiseFunction H) : D.toRealFunRaw.Valid := by
  intro q hq
  classical
  have hqD : D.domain q := by
    simpa [toRealFunRaw] using hq
  have hcompute :
      RealFunRaw.applyCompute D.toRealFunRaw q = (D.derivAt q hqD).compute := by
    funext n
    simp [toRealFunRaw, RealFunRaw.applyCompute, hqD, Pointwise.compute]
  rw [hcompute]
  change RealCompute.ValidCompute
    (fun n => centeredInterval F q
      ((D.derivAt q hqD).step n) (H.evalPrecision n))
  exact (D.derivAt q hqD).valid

end PointwiseFunction

end ConcaveDerivative

namespace ExactFunction

def secantSlope (f : Rat -> Rat) (x y : Rat) : Rat :=
  (f y - f x) / (y - x)

def ConvexOn (f : Rat -> Rat) (a b : Rat) : Prop :=
  forall x y z,
    a <= x -> x < y -> y < z -> z <= b ->
      secantSlope f x y <= secantSlope f y z

def ConcaveOn (f : Rat -> Rat) (a b : Rat) : Prop :=
  forall x y z,
    a <= x -> x < y -> y < z -> z <= b ->
      secantSlope f y z <= secantSlope f x y

structure SecantSlopeBracketOn (f : Rat -> Rat) (u v : Rat) where
  lower : Rat
  upper : Rat
  bounds :
    forall x y,
      u <= x -> x < y -> y <= v ->
        lower <= secantSlope f x y /\
        secantSlope f x y <= upper

structure StrictSecantSlopeBracketOn (f : Rat -> Rat) (u v : Rat) where
  lower : Rat
  upper : Rat
  bounds :
    forall x y,
      u < x -> x < y -> y < v ->
        lower <= secantSlope f x y /\
        secantSlope f x y <= upper

def neg (f : Rat -> Rat) : Rat -> Rat :=
  fun x => -f x

theorem convex_secant_left_le_right
    {f : Rat -> Rat} {a b l u v : Rat}
    (hf : ConvexOn f a b)
    (hal : a <= l) (hlu : l < u) (huv : u < v) (hvb : v <= b) :
    secantSlope f l u <= secantSlope f u v :=
  hf l u v hal hlu huv hvb

theorem convex_left_outer_secant_le_inner
    {f : Rat -> Rat} {a b l u x y : Rat}
    (hf : ConvexOn f a b)
    (hal : a <= l) (hlu : l < u) (hux : u < x)
    (hxy : x < y) (hyb : y <= b) :
    secantSlope f l u <= secantSlope f x y := by
  have h1 : secantSlope f l u <= secantSlope f u x :=
    hf l u x hal hlu hux (Rat.le_trans (by grind : x <= y) hyb)
  have h2 : secantSlope f u x <= secantSlope f x y :=
    hf u x y (by grind) hux hxy hyb
  exact Rat.le_trans h1 h2

theorem convex_inner_secant_le_right_outer
    {f : Rat -> Rat} {a b x y v r : Rat}
    (hf : ConvexOn f a b)
    (hax : a <= x) (hxy : x < y) (hyv : y < v)
    (hvr : v < r) (hrb : r <= b) :
    secantSlope f x y <= secantSlope f v r := by
  have h1 : secantSlope f x y <= secantSlope f y v :=
    hf x y v hax hxy hyv (Rat.le_trans (by grind : v <= r) hrb)
  have h2 : secantSlope f y v <= secantSlope f v r :=
    hf y v r (by grind) hyv hvr hrb
  exact Rat.le_trans h1 h2

/-- Convexity bounds every strictly interior secant by outer secants.

This is the derivative-bounding pattern: if `[u,v]` is strictly inside a
larger convexity interval and `l < u < x < y < v < r`, then the left outer
secant `[l,u]` is a lower bound and the right outer secant `[v,r]` is an upper
bound for the interior secant `[x,y]`. -/
theorem convex_outer_secants_bound_inner_secants
    {f : Rat -> Rat} {a b l u x y v r : Rat}
    (hf : ConvexOn f a b)
    (hal : a <= l) (hlu : l < u) (hux : u < x)
    (hxy : x < y) (hyv : y < v) (hvr : v < r) (hrb : r <= b) :
    secantSlope f l u <= secantSlope f x y /\
      secantSlope f x y <= secantSlope f v r := by
  constructor
  · exact convex_left_outer_secant_le_inner hf hal hlu hux hxy
      (Rat.le_trans (by grind : y <= v) (Rat.le_trans (by grind : v <= r) hrb))
  · exact convex_inner_secant_le_right_outer hf
      (Rat.le_trans hal (by grind : l <= x)) hxy hyv hvr hrb

/-! The concave mirror of the neighboring-secant estimate.  It is kept as a
finite rational theorem rather than derived through a completed-real
derivative: for a concave function, the right outer secant is a lower bound
and the left outer secant is an upper bound for every strictly interior
secant. -/

theorem concave_outer_secants_bound_inner_secants
    {f : Rat -> Rat} {a b l u x y v r : Rat}
    (hf : ConcaveOn f a b)
    (hal : a <= l) (hlu : l < u) (hux : u < x)
    (hxy : x < y) (hyv : y < v) (hvr : v < r) (hrb : r <= b) :
    secantSlope f v r <= secantSlope f x y /\
      secantSlope f x y <= secantSlope f l u := by
  constructor
  · have h1 : secantSlope f y v <= secantSlope f x y :=
      hf x y v (Rat.le_trans hal (by grind : l <= x)) hxy hyv
        (Rat.le_trans (by grind : v <= r) hrb)
    have h2 : secantSlope f v r <= secantSlope f y v :=
      hf y v r (by grind) hyv hvr hrb
    exact Rat.le_trans h2 h1
  · have h1 : secantSlope f u x <= secantSlope f l u :=
      hf l u x hal hlu hux
        (Rat.le_trans (by grind : x <= y)
          (Rat.le_trans (by grind : y <= v) (Rat.le_trans (by grind : v <= r) hrb)))
    have h2 : secantSlope f x y <= secantSlope f u x :=
      hf u x y (by grind) hux hxy
        (Rat.le_trans (by grind : y <= v) (Rat.le_trans (by grind : v <= r) hrb))
    exact Rat.le_trans h2 h1

def concaveOuterSecantBracket
    {a b : Rat} (f : Rat -> Rat) (hf : ConcaveOn f a b)
    (l u v r : Rat)
    (hal : a <= l) (hlu : l < u) (_huv : u < v)
    (hvr : v < r) (hrb : r <= b) :
    StrictSecantSlopeBracketOn f u v where
  lower := secantSlope f v r
  upper := secantSlope f l u
  bounds := by
    intro x y hux hxy hyv
    exact concave_outer_secants_bound_inner_secants
      hf hal hlu hux hxy hyv hvr hrb

def convexOuterSecantBracket
    {a b : Rat} (f : Rat -> Rat) (hf : ConvexOn f a b)
    (l u v r : Rat)
    (hal : a <= l) (hlu : l < u) (_huv : u < v)
    (hvr : v < r) (hrb : r <= b) :
    StrictSecantSlopeBracketOn f u v where
  lower := secantSlope f l u
  upper := secantSlope f v r
  bounds := by
    intro x y hux hxy hyv
    exact convex_outer_secants_bound_inner_secants
      hf hal hlu hux hxy hyv hvr hrb

theorem neg_convex_of_concave
    {f : Rat -> Rat} {a b : Rat}
    (hf : ConcaveOn f a b) :
    ConvexOn (neg f) a b := by
  intro x y z hax hxy hyz hzb
  unfold secantSlope neg
  have h := hf x y z hax hxy hyz hzb
  unfold secantSlope at h
  have hneg :
      -((f y - f x) / (y - x)) <= -((f z - f y) / (z - y)) := by
    grind
  have hleft :
      ((-f y - -f x) / (y - x)) = -((f y - f x) / (y - x)) := by
    grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.neg_add]
  have hright :
      ((-f z - -f y) / (z - y)) = -((f z - f y) / (z - y)) := by
    grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.neg_add]
  rw [hleft, hright]
  exact hneg

theorem neg_concave_of_convex
    {f : Rat -> Rat} {a b : Rat}
    (hf : ConvexOn f a b) :
    ConcaveOn (neg f) a b := by
  intro x y z hax hxy hyz hzb
  unfold secantSlope neg
  have h := hf x y z hax hxy hyz hzb
  unfold secantSlope at h
  have hneg :
      -((f z - f y) / (z - y)) <= -((f y - f x) / (y - x)) := by
    grind
  have hleft :
      ((-f z - -f y) / (z - y)) = -((f z - f y) / (z - y)) := by
    grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.neg_add]
  have hright :
      ((-f y - -f x) / (y - x)) = -((f y - f x) / (y - x)) := by
    grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.neg_add]
  rw [hleft, hright]
  exact hneg

end ExactFunction

namespace SqrtConcavitySanity

def sqrtSquareSecant (u v : Rat) : Rat :=
  (v - u) / (sq v - sq u)

def negSqrtSquareSecant (u v : Rat) : Rat :=
  -sqrtSquareSecant u v

theorem sq_sub_sq_pos {u v : Rat} (h : u < v) (hu : 0 <= u) :
    0 < sq v - sq u := by
  have hv : 0 < v := by grind
  rw [sq_sub_factor]
  exact Rat.mul_pos (by grind) (by grind)

theorem sqrt_square_secant_eq_inv_sum
    {u v : Rat} (hu : 0 <= u) (huv : u < v) :
    sqrtSquareSecant u v = 1 / (u + v) := by
  unfold sqrtSquareSecant
  rw [sq_sub_factor]
  rw [Rat.div_def, Rat.div_def]
  have hdiff : v - u ≠ 0 := Rat.ne_of_gt (by grind : 0 < v - u)
  have hsum : v + u ≠ 0 := Rat.ne_of_gt (by grind : 0 < v + u)
  have hsum2 : u + v ≠ 0 := Rat.ne_of_gt (by grind : 0 < u + v)
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- On rational-square inputs, the square-root secant slopes decrease.

This is the rational algebra sanity check for the terminology: `sqrt` is
concave, and therefore `-sqrt` is convex, in the standard sense. -/
theorem sqrt_secant_slopes_antitone_on_squares
    {u v w : Rat} (hu : 0 <= u) (huv : u < v) (hvw : v < w) :
    sqrtSquareSecant v w <= sqrtSquareSecant u v := by
  have hv_nonneg : 0 <= v := by grind
  rw [sqrt_square_secant_eq_inv_sum hv_nonneg hvw]
  rw [sqrt_square_secant_eq_inv_sum hu huv]
  have huv_sum : u + v <= v + w := by grind
  have huv_pos : 0 < u + v := by grind
  have hvw_pos : 0 < v + w := by grind
  apply Rat.le_of_mul_le_mul_right (c := (u + v) * (v + w))
  · calc
      (1 / (v + w)) * ((u + v) * (v + w)) = u + v := by
        rw [Rat.div_def]
        have hne : v + w != 0 := by
          have hne' : v + w ≠ 0 := Rat.ne_of_gt hvw_pos
          simp [hne']
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= v + w := huv_sum
      _ = (1 / (u + v)) * ((u + v) * (v + w)) := by
        rw [Rat.div_def]
        have hne : u + v != 0 := by
          have hne' : u + v ≠ 0 := Rat.ne_of_gt huv_pos
          simp [hne']
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact Rat.mul_pos huv_pos hvw_pos

theorem neg_sqrt_secant_slopes_monotone_on_squares
    {u v w : Rat} (hu : 0 <= u) (huv : u < v) (hvw : v < w) :
    negSqrtSquareSecant u v <= negSqrtSquareSecant v w := by
  have hconc := sqrt_secant_slopes_antitone_on_squares hu huv hvw
  unfold negSqrtSquareSecant
  grind

end SqrtConcavitySanity

end ComputableAnalysis


