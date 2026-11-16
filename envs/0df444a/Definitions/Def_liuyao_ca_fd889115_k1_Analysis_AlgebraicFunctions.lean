-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_AlgebraicFunctions
-- name    : liuyao_ca_fd889115_k1_Analysis_AlgebraicFunctions
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:55:57.891061+00:00
-- url     : https://prove2.me/theorems/7c18dd60-46fe-4698-b114-2eaac805961f
-- title:
--   Computable analysis · AlgebraicFunctions · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/AlgebraicFunctions.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexInterval
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTC
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Polynomial

set_option autoImplicit true

namespace ComputableAnalysis

/-!
# Algebraic functions

This file collects algebraic-function algorithms.  In particular, square root
is treated here as the algebraic function cut out by `w^2 = z`; the rational
input algorithm below is the real branch on nonnegative rational inputs.
-/

namespace Polynomial

/-- One Newton step for a rational polynomial at a rational point.

The step is partial: if `p' x = 0`, Newton's method is not defined at `x`, so
the algorithm returns `none`. -/
def newtonStep? (coeffs : List Rat) (x : Rat) : Option Rat :=
  let slope := eval (derivative coeffs) x
  if slope = 0 then none else some (x - eval coeffs x / slope)

/-- The `n`th rational Newton iterate from `seed`, stopping if a derivative
vanishes along the way. -/
def newtonIterate? (coeffs : List Rat) : Nat -> Rat -> Option Rat
  | 0, seed => some seed
  | n + 1, seed =>
      match newtonIterate? coeffs n seed with
      | none => none
      | some x => newtonStep? coeffs x

/-- The `n`th Newton iterate, displayed as an exact point interval when the
iteration is defined.  This is deliberately not claimed to be a valid
`RealCompute`; convergence and certification require separate hypotheses. -/
def newtonPointInterval? (coeffs : List Rat) (seed : Rat) (n : Nat) :
    Option QInterval :=
  (newtonIterate? coeffs n seed).map fun x => { lo := x, hi := x }

end Polynomial

namespace CPoly

def derivative : Coeffs -> Coeffs
  | [] => []
  | _ :: cs =>
      cs.zipIdx.map fun (c, i) =>
        QComplex.scaleRat ((i + 1 : Nat) : Rat) c

def ofRatCoeffs (coeffs : List Rat) : Coeffs :=
  coeffs.map QComplex.ofRat

/-- One complex Newton step for a polynomial with rational-complex
coefficients at a rational-complex point. -/
def newtonStep? (coeffs : Coeffs) (z : QComplex) : Option QComplex :=
  let slope := eval (derivative coeffs) z
  match QComplex.div? (eval coeffs z) slope with
  | none => none
  | some correction => some (QComplex.sub z correction)

/-- The `n`th rational-complex Newton iterate from `seed`, stopping if the
derivative vanishes along the way. -/
def newtonIterate? (coeffs : Coeffs) : Nat -> QComplex -> Option QComplex
  | 0, seed => some seed
  | n + 1, seed =>
      match newtonIterate? coeffs n seed with
      | none => none
      | some z => newtonStep? coeffs z

def newtonIterateFromRatPoly? (coeffs : List Rat) (seed : QComplex)
    (n : Nat) : Option QComplex :=
  newtonIterate? (ofRatCoeffs coeffs) n seed

/-- The `n`th complex Newton iterate as an exact point box, when defined.
As with the rational version, this is a computational trace, not a validity
certificate. -/
def newtonPointBox? (coeffs : Coeffs) (seed : QComplex) (n : Nat) :
    Option QBox :=
  (newtonIterate? coeffs n seed).map QBox.point

end CPoly

namespace BiPoly

/-- Bivariate complex polynomials.  The outer list is in `z`; each inner
polynomial is in `w`. -/
abbrev Coeffs := List CPoly.Coeffs

def eval (P : Coeffs) (z w : QComplex) : QComplex :=
  P.foldr (fun row acc => QComplex.add (CPoly.eval row w) (QComplex.mul z acc)) QComplex.zero

def evalBox (P : Coeffs) (Z W : QBox) : QBox :=
  P.foldr (fun row acc => QBox.add (QBox.evalPoly row W) (QBox.mul Z acc)) QBox.zero

def onCurve (P : Coeffs) (z w : QComplex) : Prop :=
  eval P z w = QComplex.zero

/-- `w^2 - z`, viewed as an equation for square-root branches. -/
def sqrtEquation : Coeffs :=
  [[QComplex.zero, QComplex.zero, QComplex.one], [QComplex.ofRat (-1)]]

end BiPoly

namespace AlgebraicFunction

/-- A raw algebraic-function branch.  The branch is computational; the equation
records the algebraic relation it is intended to satisfy. -/
structure Raw where
  equation : BiPoly.Coeffs
  branch : FunctionRaw

namespace Raw

def domain (f : Raw) : QComplex -> Prop := f.branch.domain

def evalRaw (f : Raw) (z : QComplex) (hz : f.domain z) : ComplexCompute :=
  f.branch.evalRaw z hz

/-- Certification target: the computed boxes for the branch satisfy the
equation at every requested precision.  The input is exact rational-complex;
the output is a box. -/
def SatisfiesEquation (f : Raw) : Prop :=
  forall z (hz : f.domain z) n,
    let Z := QBox.point z
    let W := f.branch.compute z hz n
    let eps : QPos := if hn : n = 0 then
      { val := 1, property := by decide +kernel }
    else
      { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) }
    QBox.Overlaps (BiPoly.evalBox f.equation Z W) (QBox.zeroAround eps)

/-- Agreement of algebraic branches is still agreement of their underlying
raw functions on the common domain. -/
def AgreeOnCommonDomain (f g : Raw) : Prop :=
  FunctionRaw.AgreeOnCommonDomain f.branch g.branch

end Raw

/-- Target shape for a square-root branch: a domain, a raw algorithm, and the
equation `w^2 = z`. -/
def sqrtBranch (branch : FunctionRaw) : Raw where
  equation := BiPoly.sqrtEquation
  branch := branch

end AlgebraicFunction

def sq (x : Rat) : Rat := x * x
def maxRat (a b : Rat) : Rat := if a <= b then b else a
def sqrtUpperBound (q : Rat) : Rat := maxRat 1 q

theorem sqrtUpperBound_eq_one {q : Rat} (hq : q <= 1) :
    sqrtUpperBound q = 1 := by
  unfold sqrtUpperBound maxRat
  by_cases hle : (1 : Rat) <= q
  · have hqeq : q = 1 := Rat.le_antisymm hq hle
    simp [hqeq]
  · simp [hle]

def sqrtBisectStep (q : Rat) (I : QInterval) : QInterval :=
  let m := I.midpoint
  if sq m <= q then { lo := m, hi := I.hi } else { lo := I.lo, hi := m }

def sqrtBisect (q : Rat) : Nat -> QInterval -> QInterval
  | 0, I => I
  | n + 1, I => sqrtBisect q n (sqrtBisectStep q I)

def sqrtFuel (q : Rat) (eps : QPos) : Nat := eps.val.den + (sqrtUpperBound q).den + 8

def sqrtApprox? (q : Rat) (eps : QPos) : Option QInterval :=
  if q < 0 then none else some (sqrtBisect q (sqrtFuel q eps) { lo := 0, hi := sqrtUpperBound q })

def sqrtDomain (q : Rat) : Prop := ¬ q < 0

def sqrtStageEps (n : Nat) : QPos :=
  if hn : n = 0 then
    { val := 1, property := by decide +kernel }
  else
    { val := (1 / (n : Rat)), property := by
        rw [Rat.div_def, Rat.one_mul]
        exact (Rat.inv_pos).2
          ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn)) }

theorem one_div_natCast_den_eq (n : Nat) (hn : n ≠ 0) :
    (1 / (n : Rat)).den = n := by
  rw [Rat.div_def]
  rw [Rat.inv_def]
  change (1 * Rat.divInt 1 (n : Int)).den = n
  rw [Rat.one_mul]
  change (Rat.divInt 1 (Int.ofNat n)).den = n
  rw [Rat.divInt.eq_1]
  change (mkRat 1 n).den = n
  simp [mkRat, Rat.normalize_eq, hn]

theorem sqrtStageEps_den_eq (n : Nat) (hn : n ≠ 0) :
    (sqrtStageEps n).val.den = n := by
  simp [sqrtStageEps, hn]
  exact one_div_natCast_den_eq n hn

theorem sqrtFuel_sqrtStageEps_eq (q : Rat) (n : Nat) (hn : n ≠ 0) :
    sqrtFuel q (sqrtStageEps n) = n + (sqrtUpperBound q).den + 8 := by
  unfold sqrtFuel
  rw [sqrtStageEps_den_eq n hn]

def sqrtApproxOnDomain (q : Rat) (_h : sqrtDomain q) (n : Nat) : QInterval :=
  sqrtBisect q (sqrtFuel q (sqrtStageEps n)) { lo := 0, hi := sqrtUpperBound q }

def sqrtPartialRaw : PartialRealFunRaw where
  definedAt := sqrtDomain
  compute := sqrtApproxOnDomain

def sqrtCompute? (q : Rat) : Option (Nat -> QInterval) :=
  if hneg : q < 0 then
    none
  else
    some (sqrtPartialRaw.compute q hneg)

def sqrtCertified? (q : Rat) : Prop :=
  Exists fun compute : Nat -> QInterval =>
    sqrtCompute? q = some compute /\ RealCompute.ValidCompute compute

def sqrtRaw (q : Rat) (h : sqrtDomain q) : RealCompute where
  compute := fun n => sqrtApproxOnDomain q h n

def sqrtReal (q : Rat) (h : sqrtDomain q)
    (hvalid : (sqrtRaw q h).Valid) : RealCompute.Certified :=
  RealCompute.Certified.ofRaw (sqrtRaw q h) hvalid

namespace Rat

def sqrt (q : Rat) : Option (Nat -> QInterval) := sqrtCompute? q

end Rat

namespace RealCompute

def Nonnegative (x : RealCompute) : Prop :=
  forall eps, 0 <= (x.compute eps).hi

structure SqrtDomain (x : RealCompute) where
  valid : x.Valid
  nonnegative : x.Nonnegative

/-- Real square root as a partial operation target.

Unlike rational input, arbitrary computable-real nonnegativity is not generally
decidable, so the domain proof is an explicit argument.  The implementation of
the algorithm and the theorem that it computes a square root are later work.
-/
def sqrt (x : RealCompute) (_h : SqrtDomain x) : Prop :=
  Exists fun y : RealCompute => y.Valid

end RealCompute

def SqrtIntervalSpec (q : Rat) (I : QInterval) : Prop := 0 <= I.lo /\ I.lo <= I.hi /\ sq I.lo <= q /\ q <= sq I.hi

private theorem sqrtUpperBound_nonneg {q : Rat} (hq : 0 <= q) :
    0 <= sqrtUpperBound q := by
  unfold sqrtUpperBound maxRat
  by_cases hle : (1 : Rat) <= q
  case pos => simp [hle, hq]
  case neg => simpa [hle] using (by decide +kernel : (0 : Rat) <= 1)

private theorem sqrtUpperBound_sq_ge {q : Rat} (hq : 0 <= q) :
    q <= sq (sqrtUpperBound q) := by
  unfold sqrtUpperBound maxRat
  by_cases hle : (1 : Rat) <= q
  case pos =>
    simp [hle, sq]
    calc
      q = q * 1 := by grind
      _ <= q * q := Rat.mul_le_mul_of_nonneg_left hle hq
  case neg =>
    simp [hle, sq]
    have hqle : q <= 1 := by grind
    simpa using hqle

private theorem sqrtInitialSpec {q : Rat} (hq : 0 <= q) :
    SqrtIntervalSpec q { lo := 0, hi := sqrtUpperBound q } := by
  unfold SqrtIntervalSpec
  constructor
  case left => simp
  case right =>
    constructor
    case left => exact sqrtUpperBound_nonneg hq
    case right =>
      constructor
      case left => simpa [sq] using hq
      case right => exact sqrtUpperBound_sq_ge hq

private theorem midpoint_le_hi {I : QInterval} (h : I.lo <= I.hi) :
    I.midpoint <= I.hi := by
  unfold QInterval.midpoint
  have h2b : I.lo + I.hi <= 2 * I.hi := by grind
  calc
    (I.lo + I.hi) / 2 <= (2 * I.hi) / 2 := by
      rw [Rat.div_def, Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_right h2b
        (Rat.le_of_lt ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2)))
    _ = I.hi := by
      rw [Rat.div_def]
      have hne : (2 : Rat) != 0 := by decide +kernel
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem lo_le_midpoint {I : QInterval} (h : I.lo <= I.hi) :
    I.lo <= I.midpoint := by
  unfold QInterval.midpoint
  have h2a : 2 * I.lo <= I.lo + I.hi := by grind
  calc
    I.lo = (2 * I.lo) / 2 := by
      rw [Rat.div_def]
      have hne : (2 : Rat) != 0 := by decide +kernel
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    _ <= (I.lo + I.hi) / 2 := by
      rw [Rat.div_def, Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_right h2a
        (Rat.le_of_lt ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2)))

private theorem midpoint_nonneg {I : QInterval}
    (hlo : 0 <= I.lo) (hle : I.lo <= I.hi) :
    0 <= I.midpoint := by
  exact Rat.le_trans hlo (lo_le_midpoint hle)

theorem sqrtBisectStep_width_eq_half (q : Rat) (I : QInterval) :
    (sqrtBisectStep q I).width = I.width / 2 := by
  unfold sqrtBisectStep QInterval.width QInterval.midpoint
  by_cases h : sq ((I.lo + I.hi) / 2) <= q
  · simp [h]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]
  · simp [h]
    grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]

theorem sqrtBisect_width_eq (q : Rat) (fuel : Nat) (I : QInterval) :
    (sqrtBisect q fuel I).width =
      I.width / (((2 ^ fuel : Nat) : Rat)) := by
  induction fuel generalizing I with
  | zero =>
      simp [sqrtBisect]
      rw [Rat.div_def]
      grind [Rat.mul_inv_cancel]
  | succ fuel ih =>
      simp [sqrtBisect]
      rw [ih]
      rw [sqrtBisectStep_width_eq_half]
      rw [Rat.div_def, Rat.div_def, Rat.div_def]
      have hpow :
          (((2 ^ (fuel + 1) : Nat) : Rat)) =
            (((2 ^ fuel : Nat) : Rat)) * 2 := by
        exact_mod_cast (by simpa using (Nat.pow_succ 2 fuel))
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem sqrtApproxOnDomain_width_eq
    (q : Rat) (h : sqrtDomain q) (n : Nat) :
    (sqrtApproxOnDomain q h n).width =
      sqrtUpperBound q /
        (((2 ^ sqrtFuel q (sqrtStageEps n) : Nat) : Rat)) := by
  unfold sqrtApproxOnDomain
  rw [sqrtBisect_width_eq]
  simp [QInterval.width]
  rw [Rat.div_def]
  grind [Rat.mul_inv_cancel]

theorem sqrtApproxOnDomain_width_eq_positive_stage
    (q : Rat) (h : sqrtDomain q) (n : Nat) (hn : n ≠ 0) :
    (sqrtApproxOnDomain q h n).width =
      sqrtUpperBound q /
        (((2 ^ (n + (sqrtUpperBound q).den + 8) : Nat) : Rat)) := by
  rw [sqrtApproxOnDomain_width_eq]
  rw [sqrtFuel_sqrtStageEps_eq q n hn]

/-- On a rational input in the unit interval, the square-root bisection
box has an exact dyadic width.  The extra nine bisections are the fixed
initial safety margin of the public square-root algorithm.  This is useful
when a geometric construction chooses its evaluation precision from a mesh
size: it gives a literal error budget rather than only convergence. -/
theorem sqrtApproxOnDomain_width_eq_unit
    {q : Rat} (h : sqrtDomain q) (hq : q <= 1) (n : Nat) (hn : n ≠ 0) :
    (sqrtApproxOnDomain q h n).width =
      1 / (((2 ^ (n + 9) : Nat) : Rat)) := by
  rw [sqrtApproxOnDomain_width_eq_positive_stage q h n hn]
  rw [sqrtUpperBound_eq_one hq]
  change 1 / (((2 ^ (n + 1 + 8) : Nat) : Rat)) =
    1 / (((2 ^ (n + 9) : Nat) : Rat))
  congr 3 <;> omega

theorem sqrtStageEps_den_mono {n m : Nat} (hnm : n <= m) :
    (sqrtStageEps n).val.den <= (sqrtStageEps m).val.den := by
  by_cases hm0 : m = 0
  · have hn0 : n = 0 := by omega
    simp [sqrtStageEps, hn0, hm0]
  · by_cases hn0 : n = 0
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      rw [sqrtStageEps_den_eq m hm0]
      simp [sqrtStageEps, hn0]
      exact hmpos
    · rw [sqrtStageEps_den_eq n hn0, sqrtStageEps_den_eq m hm0]
      exact hnm

theorem sqrtFuel_sqrtStageEps_mono
    (q : Rat) {n m : Nat} (hnm : n <= m) :
    sqrtFuel q (sqrtStageEps n) <= sqrtFuel q (sqrtStageEps m) := by
  unfold sqrtFuel
  have hden := sqrtStageEps_den_mono hnm
  omega

theorem sqrtBisectStep_contains
    (q : Rat) {I : QInterval} (hI : I.lo <= I.hi) :
    I.ContainsInterval (sqrtBisectStep q I) := by
  unfold QInterval.ContainsInterval sqrtBisectStep QInterval.midpoint
  by_cases h : sq ((I.lo + I.hi) / 2) <= q
  · simp [h]
    exact lo_le_midpoint hI
  · simp [h]
    exact midpoint_le_hi hI

theorem sqrtBisectStep_spec {q : Rat} {I : QInterval}
    (hI : SqrtIntervalSpec q I) :
    SqrtIntervalSpec q (sqrtBisectStep q I) := by
  have hlo : 0 <= I.lo := hI.1
  have hlohi : I.lo <= I.hi := hI.2.1
  have hloSq : sq I.lo <= q := hI.2.2.1
  have hhiSq : q <= sq I.hi := hI.2.2.2
  have hlom : I.lo <= I.midpoint := lo_le_midpoint hlohi
  have hmhi : I.midpoint <= I.hi := midpoint_le_hi hlohi
  have hmnonneg : 0 <= I.midpoint := midpoint_nonneg hlo hlohi
  unfold sqrtBisectStep
  by_cases htest : sq I.midpoint <= q
  case pos =>
    simp [htest, SqrtIntervalSpec, hmnonneg, hmhi, hhiSq]
  case neg =>
    have hqle : q <= sq I.midpoint := by grind
    simp [htest, SqrtIntervalSpec, hlo, hlom, hloSq, hqle]

theorem sqrtBisect_spec (q : Rat) :
    forall fuel I, SqrtIntervalSpec q I ->
      SqrtIntervalSpec q (sqrtBisect q fuel I)
  | 0, _I, hI => hI
  | fuel + 1, I, hI =>
      sqrtBisect_spec q fuel (sqrtBisectStep q I) (sqrtBisectStep_spec hI)

private theorem qinterval_contains_refl (I : QInterval) :
    I.ContainsInterval I := by
  unfold QInterval.ContainsInterval
  exact ⟨Rat.le_refl, Rat.le_refl⟩

private theorem qinterval_contains_trans {I J K : QInterval}
    (hIJ : I.ContainsInterval J) (hJK : J.ContainsInterval K) :
    I.ContainsInterval K := by
  unfold QInterval.ContainsInterval at *
  exact ⟨Rat.le_trans hIJ.1 hJK.1, Rat.le_trans hJK.2 hIJ.2⟩

theorem sqrtBisect_succ_right (q : Rat) (fuel : Nat) (I : QInterval) :
    sqrtBisect q (fuel + 1) I = sqrtBisectStep q (sqrtBisect q fuel I) := by
  induction fuel generalizing I with
  | zero => rfl
  | succ fuel ih =>
      simpa [sqrtBisect] using ih (sqrtBisectStep q I)

theorem sqrtBisect_step_refines_of_spec
    {q : Rat} {I : QInterval} (hI : SqrtIntervalSpec q I) (fuel : Nat) :
    (sqrtBisect q fuel I).ContainsInterval
      (sqrtBisect q (fuel + 1) I) := by
  rw [sqrtBisect_succ_right]
  exact sqrtBisectStep_contains q (sqrtBisect_spec q fuel I hI).2.1

theorem sqrtBisect_contains_of_le_fuel
    {q : Rat} {I : QInterval} (hI : SqrtIntervalSpec q I)
    {fuel₁ fuel₂ : Nat} (hle : fuel₁ <= fuel₂) :
    (sqrtBisect q fuel₁ I).ContainsInterval
      (sqrtBisect q fuel₂ I) := by
  induction hle with
  | refl =>
      exact qinterval_contains_refl (sqrtBisect q fuel₁ I)
  | step hle ih =>
      rename_i k
      exact qinterval_contains_trans ih
        (sqrtBisect_step_refines_of_spec hI k)

theorem sqrtApproxOnDomain_spec (q : Rat) (h : sqrtDomain q) (n : Nat) :
    SqrtIntervalSpec q (sqrtApproxOnDomain q h n) := by
  have hq : 0 <= q := by
    unfold sqrtDomain at h
    grind
  unfold sqrtApproxOnDomain
  exact sqrtBisect_spec q _ _ (sqrtInitialSpec hq)

theorem le_of_sq_le_sq_of_nonneg_right {a b : Rat}
    (hb : 0 <= b) (h : sq a <= sq b) : a <= b := by
  by_cases hab : a <= b
  case pos => exact hab
  case neg =>
    have hba : b < a := by grind
    have hapos : 0 < a := by grind
    have hblea : b <= a := by grind
    have h1 : b * a < a * a := Rat.mul_lt_mul_of_pos_right hba hapos
    have h0 : b * b <= b * a := Rat.mul_le_mul_of_nonneg_left hblea hb
    unfold sq at h
    grind

theorem SqrtIntervalSpec.lo_le_of_sq_le
    {q r : Rat} {I : QInterval}
    (hI : SqrtIntervalSpec q I) (hr : 0 <= r) (hqr : q <= sq r) :
    I.lo <= r :=
  le_of_sq_le_sq_of_nonneg_right hr (Rat.le_trans hI.2.2.1 hqr)

theorem SqrtIntervalSpec.le_hi_of_sq_le
    {q r : Rat} {I : QInterval}
    (hI : SqrtIntervalSpec q I) (hrq : sq r <= q) :
    r <= I.hi := by
  have hhi_nonneg : 0 <= I.hi := Rat.le_trans hI.1 hI.2.1
  exact le_of_sq_le_sq_of_nonneg_right hhi_nonneg
    (Rat.le_trans hrq hI.2.2.2)

/-- A rational lower square certificate lies below the certified bisection
lower endpoint after paying exactly the enclosing interval's width.  This is
the finite replacement for appealing to an unrepresented exact square root:
it applies directly to rational geometric lower bounds such as chord cross
products. -/
theorem SqrtIntervalSpec.sub_width_le_lo_of_sq_le
    {q r : Rat} {I : QInterval}
    (hI : SqrtIntervalSpec q I) (hrq : sq r <= q) :
    r - I.width <= I.lo := by
  have hrhi : r <= I.hi := hI.le_hi_of_sq_le hrq
  unfold QInterval.width at hrhi ⊢
  grind [Rat.sub_eq_add_neg]

/-- A lower square certificate gives a quantitative lower bound for the
finite bisection result.  Unlike a statement about an exact square root, this
uses only the rational interval width produced by the algorithm. -/
theorem sqrtApproxOnDomain_sub_width_le_lo_of_sq_le
    (q : Rat) (h : sqrtDomain q) (n : Nat) {r : Rat}
    (hrq : sq r <= q) :
    r - (sqrtApproxOnDomain q h n).width <=
      (sqrtApproxOnDomain q h n).lo :=
  (sqrtApproxOnDomain_spec q h n).sub_width_le_lo_of_sq_le hrq

theorem sqrtPartialRaw_sub_width_le_lo_of_sq_le
    (q : Rat) (h : sqrtDomain q) (n : Nat) {r : Rat}
    (hrq : sq r <= q) :
    r - (sqrtPartialRaw.compute q h n).width <=
      (sqrtPartialRaw.compute q h n).lo := by
  simpa [sqrtPartialRaw] using
    (sqrtApproxOnDomain_sub_width_le_lo_of_sq_le q h n hrq)

def sqrtIntervalSpecBool (q : Rat) (I : QInterval) : Bool := decide (0 <= I.lo /\ I.lo <= I.hi /\ sq I.lo <= q /\ q <= sq I.hi)

def sqrtApproxOk? (q : Rat) (eps : QPos) : Option Bool :=
  match sqrtApprox? q eps with | none => none | some I => some (I.widthOk eps && sqrtIntervalSpecBool q I)

def SqrtRealComputeSpec (q : Rat) (x : RealCompute) : Prop := x.Valid /\ forall eps, SqrtIntervalSpec q (x.compute eps)

theorem sqrtRaw_stage_spec (q : Rat) (h : sqrtDomain q) (n : Nat) :
    SqrtIntervalSpec q ((sqrtRaw q h).compute n) := by
  simpa [sqrtRaw] using sqrtApproxOnDomain_spec q h n

def SqrtRawSpec (q : Rat) (h : sqrtDomain q) : Prop :=
  SqrtRealComputeSpec q (sqrtRaw q h)

theorem sqrt_spec_equiv_of_spec {q : Rat} {x y : RealCompute}
    (hx : SqrtRealComputeSpec q x) (hy : SqrtRealComputeSpec q y) :
    x.Equiv y := by
  intro n
  apply (RealCompute.compareAt_overlap_iff x y n n).2
  have hxs := hx.2 n
  have hys := hy.2 n
  unfold SqrtIntervalSpec at hxs hys
  have hxy : (x.compute n).lo <= (y.compute n).hi := by
    apply (Rat.not_lt).mp
    intro hnot
    have hlt : (y.compute n).hi < (x.compute n).lo := by grind
    have hdiff : 0 < (x.compute n).lo - (y.compute n).hi := by grind
    have hsum : 0 < (x.compute n).lo + (y.compute n).hi := by
      grind
    have hsq_lt : sq (y.compute n).hi < sq (x.compute n).lo := by
      unfold sq
      have hprod : 0 <
          ((x.compute n).lo - (y.compute n).hi) *
            ((x.compute n).lo + (y.compute n).hi) :=
        Rat.mul_pos hdiff hsum
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg]
    have hleft : sq (x.compute n).lo <= sq (y.compute n).hi :=
      Rat.le_trans hxs.2.2.1 hys.2.2.2
    grind
  have hyx : (y.compute n).lo <= (x.compute n).hi := by
    apply (Rat.not_lt).mp
    intro hnot
    have hlt : (x.compute n).hi < (y.compute n).lo := by grind
    have hdiff : 0 < (y.compute n).lo - (x.compute n).hi := by grind
    have hsum : 0 < (y.compute n).lo + (x.compute n).hi := by
      grind
    have hsq_lt : sq (x.compute n).hi < sq (y.compute n).lo := by
      unfold sq
      have hprod : 0 <
          ((y.compute n).lo - (x.compute n).hi) *
            ((y.compute n).lo + (x.compute n).hi) :=
        Rat.mul_pos hdiff hsum
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg]
    have hleft : sq (y.compute n).lo <= sq (x.compute n).hi :=
      Rat.le_trans hys.2.2.1 hxs.2.2.2
    grind
  change (x.compute n).lo <= (y.compute n).hi /\
    (y.compute n).lo <= (x.compute n).hi
  exact ⟨hxy, hyx⟩

def sqrtWidthConstant (q : Rat) : Nat :=
  (sqrtUpperBound q).num.natAbs + 1

private theorem rat_le_num_natAbs_succ (q : Rat) :
    q <= (((q.num.natAbs + 1 : Nat) : Rat)) := by
  by_cases hqpos : 0 < q
  · have hdenpos : 0 < ((q.den : Nat) : Rat) := by
      exact (Rat.natCast_pos).2 (Nat.pos_of_ne_zero q.den_nz)
    apply Rat.le_of_mul_le_mul_right (c := ((q.den : Nat) : Rat))
    · rw [Rat.mul_comm q ((q.den : Nat) : Rat), rat_den_mul_self]
      have hnumpos : 0 < q.num := rat_num_pos_of_pos hqpos
      have hnum_nonneg : 0 <= q.num := Int.le_of_lt hnumpos
      have hcast : (((q.num.natAbs : Nat) : Rat)) = (q.num : Rat) := by
        exact_mod_cast (Int.natAbs_of_nonneg hnum_nonneg)
      calc
        (q.num : Rat) = ((q.num.natAbs : Nat) : Rat) := by rw [hcast]
        _ <= (((q.num.natAbs + 1 : Nat) : Rat)) := by
          exact_mod_cast (Nat.le_succ q.num.natAbs)
        _ <= (((q.num.natAbs + 1 : Nat) : Rat)) *
            ((q.den : Nat) : Rat) := by
          exact_mod_cast (Nat.le_mul_of_pos_right (q.num.natAbs + 1)
            (Nat.pos_of_ne_zero q.den_nz))
    · exact hdenpos
  · have hqnonpos : q <= 0 := by grind
    have hzero : (0 : Rat) <= (((q.num.natAbs + 1 : Nat) : Rat)) :=
      Rat.natCast_nonneg
    exact Rat.le_trans hqnonpos hzero

private theorem succ_le_two_pow (n : Nat) : n + 1 <= 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 + 1 <= 2 * (n + 1) := by omega
        _ <= 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by
          rw [Nat.pow_succ]
          omega

theorem sqrtApproxOnDomain_width_le_nat_over_succ
    (q : Rat) (h : sqrtDomain q) (n : Nat) :
    (sqrtApproxOnDomain q h n).width <=
      (sqrtWidthConstant q : Rat) / (((n + 1 : Nat) : Rat)) := by
  let B : Rat := sqrtUpperBound q
  let C : Nat := sqrtWidthConstant q
  let fuel : Nat := sqrtFuel q (sqrtStageEps n)
  have hBC : B <= (C : Rat) := by
    dsimp [B, C, sqrtWidthConstant]
    exact rat_le_num_natAbs_succ (sqrtUpperBound q)
  have hfuel_ge : n <= fuel := by
    dsimp [fuel]
    by_cases hn : n = 0
    · omega
    · rw [sqrtFuel_sqrtStageEps_eq q n hn]
      omega
  have hsucc_pow : n + 1 <= 2 ^ fuel := by
    exact Nat.le_trans (succ_le_two_pow n)
      (Nat.pow_le_pow_right (by omega : 0 < 2) hfuel_ge)
  have hden_pos : 0 < (((2 ^ fuel : Nat) : Rat)) := by
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hone_den_nonneg : 0 <= 1 / (((2 ^ fuel : Nat) : Rat)) := by
    rw [Rat.div_def]
    exact Rat.le_of_lt (Rat.mul_pos (by decide +kernel : (0 : Rat) < 1)
      ((Rat.inv_pos).2 hden_pos))
  have hone :
      (1 / (((2 ^ fuel : Nat) : Rat))) <=
        1 / (((n + 1 : Nat) : Rat)) := by
    exact FTC.one_div_nat_antitone (Nat.succ_pos n)
      (Nat.pow_pos (by omega : 0 < 2)) hsucc_pow
  rw [sqrtApproxOnDomain_width_eq]
  dsimp [B, fuel] at *
  calc
    sqrtUpperBound q /
        (((2 ^ sqrtFuel q (sqrtStageEps n) : Nat) : Rat)) =
        B * (1 / (((2 ^ fuel : Nat) : Rat))) := by
      dsimp [B, fuel]
      rw [Rat.div_def, Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (C : Rat) * (1 / (((2 ^ fuel : Nat) : Rat))) := by
      exact Rat.mul_le_mul_of_nonneg_right hBC hone_den_nonneg
    _ <= (C : Rat) * (1 / (((n + 1 : Nat) : Rat))) := by
      exact Rat.mul_le_mul_of_nonneg_left hone Rat.natCast_nonneg
    _ = (sqrtWidthConstant q : Rat) / (((n + 1 : Nat) : Rat)) := by
      dsimp [C, sqrtWidthConstant]
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem widthsShrink_of_natOverSuccBound_local
    {compute : Nat -> QInterval} {C : Nat}
    (hbound : forall n,
      (compute n).width <= (C : Rat) / (((n + 1 : Nat) : Rat))) :
    RealCompute.WidthsShrinkToZero compute := by
  intro eps
  refine ⟨C * (eps.val.den + 1), ?_⟩
  intro n hn
  have hmain :
      (C : Rat) / (((n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    let K : Rat := (C : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 (Nat.succ_pos n)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hAne : A ≠ 0 := Rat.ne_of_gt hApos
    have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : K * B <= A := by
      dsimp [A, B, K]
      exact_mod_cast (by omega :
        C * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (K / A) * (A * B) = K * B := by
          rw [Rat.div_def]
          have hcancel : A * A⁻¹ = 1 := Rat.mul_inv_cancel A hAne
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          have hcancel : B * B⁻¹ = 1 := Rat.mul_inv_cancel B hBne
          grind [Rat.mul_assoc, Rat.mul_comm]
    · exact hABpos
  exact Rat.le_trans (hbound n)
    (Rat.le_trans hmain
      (FTC.one_div_den_succ_le_of_pos eps.property))

theorem sqrtApproxOnDomain_widthsShrink
    (q : Rat) (h : sqrtDomain q) :
    RealCompute.WidthsShrinkToZero (sqrtApproxOnDomain q h) :=
  widthsShrink_of_natOverSuccBound_local
    (sqrtApproxOnDomain_width_le_nat_over_succ q h)

theorem sqrtApproxOnDomain_ordered (q : Rat) (h : sqrtDomain q) (n : Nat) :
    0 <= (sqrtApproxOnDomain q h n).width := by
  have hspec := sqrtApproxOnDomain_spec q h n
  unfold SqrtIntervalSpec at hspec
  unfold QInterval.width
  grind

theorem sqrtApproxOnDomain_contains_of_le
    (q : Rat) (h : sqrtDomain q) {n m : Nat} (hnm : n <= m) :
    (sqrtApproxOnDomain q h n).ContainsInterval
      (sqrtApproxOnDomain q h m) := by
  have hq : 0 <= q := by
    unfold sqrtDomain at h
    grind
  unfold sqrtApproxOnDomain
  exact sqrtBisect_contains_of_le_fuel (sqrtInitialSpec hq)
    (sqrtFuel_sqrtStageEps_mono q hnm)

/-- Every finite square-root bisection box remains inside its explicit
initial interval.  This public endpoint bound is useful when a later
calculus certificate must control products of the finite endpoints. -/
theorem sqrtApproxOnDomain_hi_le_upperBound
    (q : Rat) (h : sqrtDomain q) (n : Nat) :
    (sqrtApproxOnDomain q h n).hi <= sqrtUpperBound q := by
  have hq0 : 0 <= q := by
    unfold sqrtDomain at h
    grind
  have hcontains :
      ({ lo := 0, hi := sqrtUpperBound q } : QInterval).ContainsInterval
        (sqrtApproxOnDomain q h n) := by
    unfold sqrtApproxOnDomain
    exact sqrtBisect_contains_of_le_fuel (sqrtInitialSpec hq0) (Nat.zero_le _)
  exact hcontains.2

theorem sqrtApproxOnDomain_nested
    (q : Rat) (h : sqrtDomain q) :
    forall n m, n <= m ->
      (sqrtApproxOnDomain q h n).lo <=
        (sqrtApproxOnDomain q h m).lo /\
      (sqrtApproxOnDomain q h m).lo <=
        (sqrtApproxOnDomain q h m).hi /\
      (sqrtApproxOnDomain q h m).hi <=
        (sqrtApproxOnDomain q h n).hi := by
  intro n m hnm
  have hcontains := sqrtApproxOnDomain_contains_of_le q h hnm
  have hspecm := sqrtApproxOnDomain_spec q h m
  unfold QInterval.ContainsInterval at hcontains
  exact ⟨hcontains.1, hspecm.2.1, hcontains.2⟩

theorem sqrtApproxOnDomain_valid (q : Rat) (h : sqrtDomain q) :
    RealCompute.ValidCompute (sqrtApproxOnDomain q h) := by
  exact ⟨sqrtApproxOnDomain_ordered q h,
    sqrtApproxOnDomain_nested q h,
    sqrtApproxOnDomain_widthsShrink q h⟩

theorem sqrtRaw_valid (q : Rat) (h : sqrtDomain q) :
    (sqrtRaw q h).Valid := by
  change RealCompute.ValidCompute (sqrtApproxOnDomain q h)
  exact sqrtApproxOnDomain_valid q h

theorem sqrtRaw_spec (q : Rat) (h : sqrtDomain q) :
    SqrtRawSpec q h :=
  ⟨sqrtRaw_valid q h, sqrtRaw_stage_spec q h⟩

/-! The square-root specification is strong enough to recover the defining
equation at the raw-real level.  This is the algebraic invariant used by the
constructive half-angle induction: it compares rational intervals directly,
without selecting an exact real square root. -/
theorem sqrtRaw_mul_self_equiv_of_domain (q : Rat) (h : sqrtDomain q) :
    (sqrtRaw q h * sqrtRaw q h).Equiv (RealCompute.ofRat q) := by
  intro n
  have hsvalid := sqrtRaw_valid q h
  have horder := RealCompute.interval_order_of_valid (sqrtRaw q h) hsvalid n
  have hspec := sqrtRaw_stage_spec q h n
  apply (RealCompute.compareAt_overlap_iff
    (sqrtRaw q h * sqrtRaw q h) (RealCompute.ofRat q) n n).2
  change QInterval.Overlaps
    (QBox.mulRealInterval
      ((sqrtRaw q h).compute n).lo
      ((sqrtRaw q h).compute n).hi
      ((sqrtRaw q h).compute n).lo
      ((sqrtRaw q h).compute n).hi)
    { lo := q, hi := q }
  rw [QBox.mulRealInterval_self_of_nonneg hspec.1 horder]
  unfold QInterval.Overlaps
  exact ⟨hspec.2.2.1, hspec.2.2.2⟩

theorem ofRat_add_equiv (a b : Rat) :
    (RealCompute.ofRat a + RealCompute.ofRat b).Equiv
      (RealCompute.ofRat (a + b)) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (RealCompute.ofRat a + RealCompute.ofRat b)
    (RealCompute.ofRat (a + b)) n n).2
  change QInterval.Overlaps
    { lo := a + b, hi := a + b }
    { lo := a + b, hi := a + b }
  exact ⟨by grind, by grind⟩

/-! Raw-real form of the elementary circle identity.  This separates the
algebraic part of the half-angle proof from the geometric theorem that
constructs the two square-root representatives. -/
theorem raw_square_sum_equiv_of_rational_square_sum
    {s c : RealCompute} {q r : Rat}
    (hss : (s * s).Valid) (hcc : (c * c).Valid)
    (hsq : (s * s).Equiv (RealCompute.ofRat q))
    (hcq : (c * c).Equiv (RealCompute.ofRat r))
    (hsum : q + r = 1) :
    (s * s + c * c).Equiv (RealCompute.ofRat 1) := by
  have hqvalid : (RealCompute.ofRat q).Valid := by
    unfold RealCompute.ofRat RealCompute.Valid
    exact RealCompute.ofRat_valid q
  have hrvalid : (RealCompute.ofRat r).Valid := by
    unfold RealCompute.ofRat RealCompute.Valid
    exact RealCompute.ofRat_valid r
  have honevalid : (RealCompute.ofRat (1 : Rat)).Valid := by
    unfold RealCompute.ofRat RealCompute.Valid
    exact RealCompute.ofRat_valid 1
  have hadd := RealCompute.add_equiv hss
    hqvalid hcc hrvalid hsq hcq
  have hrat := ofRat_add_equiv q r
  rw [hsum] at hrat
  have hmid : (RealCompute.ofRat q + RealCompute.ofRat r).Valid :=
    RealCompute.add_valid hqvalid hrvalid
  exact RealCompute.equiv_trans
    (RealCompute.add_valid hss hcc)
    hmid honevalid
    hadd hrat

theorem sqrtRaw_equiv_of_spec {q : Rat} (h : sqrtDomain q)
    {x : RealCompute} (hx : SqrtRealComputeSpec q x) :
    (sqrtRaw q h).Equiv x := by
  exact sqrt_spec_equiv_of_spec (sqrtRaw_spec q h) hx

theorem sqrtCertified_of_domain (q : Rat) (h : sqrtDomain q) :
    sqrtCertified? q := by
  unfold sqrtCertified? sqrtCompute?
  simp
  refine ⟨sqrtPartialRaw.compute q h, ?_, ?_⟩
  · exact ⟨h, rfl⟩
  · exact sqrtApproxOnDomain_valid q h

theorem sq_le_sq_of_nonneg_le {a b : Rat} (ha : 0 <= a) (hab : a <= b) :
    sq a <= sq b := by
  have hb : 0 <= b := Rat.le_trans ha hab
  unfold sq
  calc
    a * a <= b * a := Rat.mul_le_mul_of_nonneg_right hab ha
    _ <= b * b := Rat.mul_le_mul_of_nonneg_left hab hb

theorem sq_qabs (x : Rat) :
    sq (qabs x) = sq x := by
  unfold qabs sq
  by_cases hneg : x < 0
  case pos =>
    simp [hneg]
    grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
  case neg =>
    simp [hneg]

theorem sq_sub_factor (lo hi : Rat) :
    sq hi - sq lo = (hi - lo) * (hi + lo) := by
  unfold sq
  grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm,
    Rat.mul_assoc, Rat.mul_comm, Rat.sub_eq_add_neg]

theorem sq_lt_sq_of_nonneg_lt {a b : Rat} (ha : 0 <= a) (hab : a < b) :
    sq a < sq b := by
  have hdiff : 0 < sq b - sq a := by
    rw [sq_sub_factor]
    exact Rat.mul_pos (by grind) (by grind)
  grind

theorem sqrt_spec_sq_gap_le_stage_bound {q r : Rat} {x : RealCompute}
    (hx : SqrtRealComputeSpec q x)
    (hover : x.SameStageOverlap (RealCompute.ofRat r))
    (n : Nat) :
    qabs (sq r - q) <=
      (x.compute n).width * (2 * (x.compute 0).hi + 1) := by
  have hspec := hx.2 n
  have hr : (x.compute n).lo <= r /\ r <= (x.compute n).hi := by
    have h := (RealCompute.compareAt_overlap_iff x (RealCompute.ofRat r) n n).1
      (hover n)
    simpa [RealCompute.ofRat, QInterval.Overlaps] using h
  have hsq_lo_r : sq (x.compute n).lo <= sq r :=
    sq_le_sq_of_nonneg_le hspec.1 hr.1
  have hr_nonneg : 0 <= r := Rat.le_trans hspec.1 hr.1
  have hsq_r_hi : sq r <= sq (x.compute n).hi :=
    sq_le_sq_of_nonneg_le hr_nonneg hr.2
  have hgapStage :
      qabs (sq r - q) <= sq (x.compute n).hi - sq (x.compute n).lo :=
    qabs_sub_le_of_common_bounds
      hsq_lo_r hsq_r_hi hspec.2.2.1 hspec.2.2.2
  have hnest := hx.1.2.1 0 n (Nat.zero_le n)
  have hsum :
      (x.compute n).hi + (x.compute n).lo <=
        2 * (x.compute 0).hi + 1 := by
    have hlo_le_hi0 : (x.compute n).lo <= (x.compute 0).hi :=
      Rat.le_trans hspec.2.1 hnest.2.2
    have hhi_le_hi0 : (x.compute n).hi <= (x.compute 0).hi := hnest.2.2
    grind
  have hwidth_nonneg : 0 <= (x.compute n).hi - (x.compute n).lo := by
    simpa [QInterval.width] using hx.1.1 n
  have hprod :
      sq (x.compute n).hi - sq (x.compute n).lo <=
        (x.compute n).width * (2 * (x.compute 0).hi + 1) := by
    rw [sq_sub_factor, QInterval.width]
    exact Rat.mul_le_mul_of_nonneg_left hsum hwidth_nonneg
  exact Rat.le_trans hgapStage hprod

theorem eq_of_qabs_sub_le_width_mul_of_valid {a b C : Rat} {x : RealCompute}
    (hx : x.Valid) (hCpos : 0 < C)
    (hbound : forall n, qabs (a - b) <= (x.compute n).width * C) :
    a = b := by
  by_cases hEq : a = b
  case pos => exact hEq
  case neg =>
    exfalso
    let gap : Rat := qabs (a - b)
    have hdiff_ne : Not (a - b = 0) := by
      intro hzero
      apply hEq
      grind
    have hgap_pos : 0 < gap := by
      dsimp [gap]
      exact qabs_pos_of_ne hdiff_ne
    have htwoCpos : 0 < 2 * C := by grind
    have hepsPos : 0 < gap / (2 * C) := by
      rw [Rat.div_def]
      exact Rat.mul_pos hgap_pos ((Rat.inv_pos).2 htwoCpos)
    obtain ⟨N, hsmall⟩ := hx.2.2
      { val := gap / (2 * C), property := hepsPos }
    let n : Nat := N
    have hboundN : gap <= (x.compute n).width * C := by
      dsimp [gap]
      exact hbound n
    have hsmallN : (x.compute n).width <= gap / (2 * C) :=
      hsmall n (Nat.le_refl n)
    have hmul :
        (x.compute n).width * C <= (gap / (2 * C)) * C :=
      Rat.mul_le_mul_of_nonneg_right hsmallN (Rat.le_of_lt hCpos)
    have hgapLe : gap <= (gap / (2 * C)) * C :=
      Rat.le_trans hboundN hmul
    have hhalf : (gap / (2 * C)) * C = gap / 2 := by
      rw [Rat.div_def, Rat.div_def]
      have h2Cne : (2 * C : Rat) != 0 := by grind
      have h2ne : (2 : Rat) != 0 := by decide +kernel
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hgapLeHalf : gap <= gap / 2 := by
      rw [hhalf] at hgapLe
      exact hgapLe
    have hhalfLt : gap / 2 < gap := by
      have htwo : (0 : Rat) < 2 := by decide +kernel
      rw [Rat.div_lt_iff htwo]
      grind
    have hgapLtHalf : gap < gap / 2 :=
      Rat.lt_of_le_of_ne hgapLeHalf (Rat.ne_of_gt hhalfLt)
    grind

theorem sq_eq_of_sqrt_spec_equiv_rat {q r : Rat} {x : RealCompute}
    (hx : SqrtRealComputeSpec q x)
    (heq : x.Equiv (RealCompute.ofRat r)) :
    sq r = q := by
  let C : Rat := 2 * (x.compute 0).hi + 1
  have hspec0 := hx.2 0
  have hhi0_nonneg : 0 <= (x.compute 0).hi :=
    Rat.le_trans hspec0.1 hspec0.2.1
  have hCpos : 0 < C := by
    dsimp [C]
    grind
  have hratValid : (RealCompute.ofRat r).Valid := by
    change RealCompute.ValidCompute (RealCompute.ofRat r).compute
    exact RealCompute.ofRat_valid r
  have hover := RealCompute.sameStageOverlap_of_equiv hx.1 hratValid heq
  exact eq_of_qabs_sub_le_width_mul_of_valid hx.1 hCpos (by
    intro n
    dsimp [C]
    exact sqrt_spec_sq_gap_le_stage_bound hx hover n)

/-- Squaring as an exact rational interval function.  This is the forward map
for the first concrete inverse-function example: its inverse on the
nonnegative unit interval is the existing square-root bisection algorithm. -/
def squareRaw : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x _ _ => { lo := sq x, hi := sq x }

theorem squareRaw_valid (x : Rat) (hx : squareRaw.definedAt x) :
    RealCompute.ValidCompute (squareRaw.compute x hx) := by
  simpa [squareRaw] using RealCompute.ofRat_valid (sq x)

/-- The exact squaring function restricted to the nonnegative unit interval. -/
def squareOnUnit : FunctionOnInterval where
  raw := squareRaw
  lower := 0
  upper := 1
  defined_on := by
    intro _ _
    trivial
  valid_on := by
    intro x hx
    exact squareRaw_valid x hx

/-- Endpoint evaluation is an enclosure for squaring on a nonnegative input
interval. -/
def squareUnitEvalInterval (I : QInterval) : QInterval :=
  { lo := sq I.lo, hi := sq I.hi }

theorem squareUnitEvalInterval_width (I : QInterval) :
    (squareUnitEvalInterval I).width = I.width * (I.hi + I.lo) := by
  unfold squareUnitEvalInterval QInterval.width sq
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem squareUnit_interval_width_scale (w : Rat) (n : Nat)
    (hn : n ≠ 0)
    (hw : w <= 1 / ((2 * n : Nat) : Rat)) :
    2 * w <= 1 / (n : Rat) := by
  calc
    2 * w <= 2 * (1 / ((2 * n : Nat) : Rat)) :=
      Rat.mul_le_mul_of_nonneg_left hw (by decide)
    _ = 1 / (n : Rat) := by
      rw [Rat.div_def]
      rw [show ((2 * n : Nat) : Rat) = (2 : Rat) * (n : Rat) by
        exact Rat.natCast_mul 2 n]
      have htwo : (2 : Rat) ≠ 0 := by decide
      have hn' : (n : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn))
      rw [Rat.inv_mul_rev]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- Squaring is interval-regular on `[0,1]`, with a direct rational modulus.
The `n + 1` target convention lets stage zero retain a positive finite error
budget, as required for non-exact interval functions such as square root. -/
def squareOnUnit_intervalRegular : IntervalRegularOn squareOnUnit := by
  refine
    { evalInterval := fun I _ _ => squareUnitEvalInterval I
      inputPrecision := fun n => 2 * (n + 1)
      inputPrecision_pos := by
        intro n
        omega
      output_width := ?_
      contains_point_values := ?_ }
  · intro I hI n hwidth
    rcases hI with ⟨hlo, hord, hhi⟩
    have hwidth_nonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hsum_nonneg : 0 <= I.hi + I.lo := by
      have hhi_nonneg : 0 <= I.hi := Rat.le_trans hlo hord
      exact Rat.add_nonneg hhi_nonneg hlo
    have hsum_le_two : I.hi + I.lo <= 2 := by
      change (0 : Rat) <= I.lo at hlo
      change I.hi <= 1 at hhi
      grind
    constructor
    · rw [squareUnitEvalInterval_width]
      exact Rat.mul_nonneg hwidth_nonneg hsum_nonneg
    · rw [squareUnitEvalInterval_width]
      calc
        I.width * (I.hi + I.lo) <= I.width * 2 :=
          Rat.mul_le_mul_of_nonneg_left hsum_le_two hwidth_nonneg
        _ = 2 * I.width := by grind [Rat.mul_comm]
        _ <= 1 / (((n + 1 : Nat) : Rat)) :=
          squareUnit_interval_width_scale I.width (n + 1)
            (Nat.succ_ne_zero n) hwidth
  · intro I hI x hx n hxlo hxhi
    rcases hI with ⟨hIlo, hord, hIhi⟩
    change (0 : Rat) <= I.lo at hIlo
    have hlo_nonneg : 0 <= I.lo := hIlo
    have hx_nonneg : 0 <= x := Rat.le_trans hlo_nonneg hxlo
    have hlo_sq : sq I.lo <= sq x :=
      sq_le_sq_of_nonneg_le hlo_nonneg hxlo
    have hhi_sq : sq x <= sq I.hi :=
      sq_le_sq_of_nonneg_le hx_nonneg hxhi
    change squareUnitEvalInterval I |>.ContainsInterval
      (squareOnUnit.compute x hx n)
    change QInterval.ContainsInterval
      { lo := sq I.lo, hi := sq I.hi }
      { lo := sq x, hi := sq x }
    exact ⟨hlo_sq, hhi_sq⟩

/-- The concrete continuous squaring map used by the unit square-root
inverse example. -/
def squareOnUnit_continuous : ContinuousFunctionOnInterval where
  function := squareOnUnit
  regular := squareOnUnit_intervalRegular

/-- The square map on the unit interval satisfies the project's literal
rational epsilon--delta continuity predicate, without a topology import. -/
theorem squareOnUnit_epsilonDeltaContinuous :
    EpsilonDeltaContinuousOn squareOnUnit :=
  squareOnUnit_intervalRegular.epsilonDeltaContinuous

theorem squareOnUnit_nondecreasing : NondecreasingOnInterval squareOnUnit := by
  intro x y hx hy hxy _
  have hx_nonneg : 0 <= x := hx.1
  have hsq : sq x <= sq y := sq_le_sq_of_nonneg_le hx_nonneg hxy
  change sq x <= sq y
  exact hsq

/-- On `[0,1]`, a separation of `1/(n+1)` in the input strictly separates the
exact output boxes after squaring.  This is the nondecreasing effective
inverse-separation certificate. -/
def squareOnUnit_effectiveInverseSeparation :
    EffectiveInverseSeparation squareOnUnit where
  kind := .nondecreasing
  inputPrecision := fun n => n + 1
  inputPrecision_pos := fun n => Nat.succ_pos n
  outputPrecision := fun _ => 0
  separated := by
    intro x y hx hy n hsep
    have hx_nonneg : 0 <= x := hx.1
    have hstep_pos : 0 < (1 / (((n + 1 : Nat) : Rat))) :=
      one_div_nat_pos (Nat.succ_pos n)
    have hxy : x < y := by
      grind
    have hsq : sq x < sq y := sq_lt_sq_of_nonneg_lt hx_nonneg hxy
    change sq x < sq y
    exact hsq

/-- The unit-interval square map supplies the constructive data required by
the monotone inverse-function interface. -/
def squareOnUnit_invertible : InvertibleFunctionOnInterval where
  continuous := squareOnUnit_continuous
  source_ordered := by decide +kernel
  monotone := MonotoneOnInterval.ofNondecreasing squareOnUnit_nondecreasing
  separation := squareOnUnit_effectiveInverseSeparation
  orientation := trivial

/-- A rational target in the unit range of squaring, represented by its exact
rational point box and enclosed by the exact endpoint values of the square
branch. -/
def squareOnUnitRationalTarget (q : Rat) (hq : inDomainInterval 0 1 q) :
    InRangeRaw squareOnUnit_invertible where
  value := RealCompute.ofRat q
  value_valid := by
    change RealCompute.ValidCompute (RealCompute.ofRat q).compute
    exact RealCompute.ofRat_valid q
  rangePrecision := fun _ => 0
  in_range := by
    intro n
    change 0 <= q ∧ q <= 1 at hq
    simpa [InvertibleFunctionOnInterval.EndpointRangeContains,
      InvertibleFunctionOnInterval.function,
      InvertibleFunctionOnInterval.lowerValueBox,
      InvertibleFunctionOnInterval.upperValueBox,
      FunctionOnInterval.compute,
      squareOnUnit_invertible, squareOnUnit_continuous,
      squareOnUnit_effectiveInverseSeparation,
      squareOnUnit, squareRaw, sq, RealCompute.ofRat] using hq

private theorem sqrtDomain_of_unit {q : Rat} (hq : inDomainInterval 0 1 q) :
    sqrtDomain q := by
  unfold sqrtDomain
  change 0 <= q /\ q <= 1 at hq
  grind

/-- The rational square-root bisection never leaves `[0,1]` for a rational
target in `[0,1]`. -/
theorem sqrtApproxOnUnit_subinterval (q : Rat) (hq : inDomainInterval 0 1 q)
    (n : Nat) :
    subintervalOf (sqrtApproxOnDomain q (sqrtDomain_of_unit hq) n) 0 1 := by
  have hcontains :
      ({ lo := 0, hi := sqrtUpperBound q } : QInterval).ContainsInterval
        (sqrtApproxOnDomain q (sqrtDomain_of_unit hq) n) := by
    unfold sqrtApproxOnDomain
    exact sqrtBisect_contains_of_le_fuel (sqrtInitialSpec hq.1) (Nat.zero_le _)
  have hspec := sqrtApproxOnDomain_spec q (sqrtDomain_of_unit hq) n
  unfold QInterval.ContainsInterval at hcontains
  refine ⟨hcontains.1, hspec.2.1, ?_⟩
  simpa [sqrtUpperBound_eq_one hq.2] using hcontains.2

theorem sqrtRaw_halfAngle_square_sum_equiv_one
    {q r : Rat}
    (hq : inDomainInterval 0 1 q)
    (hr : inDomainInterval 0 1 r)
    (hsum : q + r = 1) :
    ((sqrtRaw q (sqrtDomain_of_unit hq) *
        sqrtRaw q (sqrtDomain_of_unit hq)) +
      (sqrtRaw r (sqrtDomain_of_unit hr) *
        sqrtRaw r (sqrtDomain_of_unit hr))).Equiv
      (RealCompute.ofRat 1) := by
  have hqvalid : (sqrtRaw q (sqrtDomain_of_unit hq) *
      sqrtRaw q (sqrtDomain_of_unit hq)).Valid := by
    apply RealCompute.mulSelf_valid_of_nonneg_bounded
      (B := (1 : Rat))
      (sqrtRaw_valid q (sqrtDomain_of_unit hq)) (by decide +kernel)
    intro n
    have hsub := sqrtApproxOnUnit_subinterval q hq n
    simpa [sqrtRaw] using (show
      0 <= (sqrtApproxOnDomain q (sqrtDomain_of_unit hq) n).lo /\
        (sqrtApproxOnDomain q (sqrtDomain_of_unit hq) n).hi <= 1 from
      ⟨hsub.1, hsub.2.2⟩)
  have hrvalid : (sqrtRaw r (sqrtDomain_of_unit hr) *
      sqrtRaw r (sqrtDomain_of_unit hr)).Valid := by
    apply RealCompute.mulSelf_valid_of_nonneg_bounded
      (B := (1 : Rat))
      (sqrtRaw_valid r (sqrtDomain_of_unit hr)) (by decide +kernel)
    intro n
    have hsub := sqrtApproxOnUnit_subinterval r hr n
    simpa [sqrtRaw] using (show
      0 <= (sqrtApproxOnDomain r (sqrtDomain_of_unit hr) n).lo /\
        (sqrtApproxOnDomain r (sqrtDomain_of_unit hr) n).hi <= 1 from
      ⟨hsub.1, hsub.2.2⟩)
  apply raw_square_sum_equiv_of_rational_square_sum hqvalid hrvalid
  · exact sqrtRaw_mul_self_equiv_of_domain q (sqrtDomain_of_unit hq)
  · exact sqrtRaw_mul_self_equiv_of_domain r (sqrtDomain_of_unit hr)
  · exact hsum

/-- The existing rational square-root bisection is a concrete inverse search
for each exact rational target in the unit range of squaring. -/
def sqrtOnUnitBisectionSearch (q : Rat) (hq : inDomainInterval 0 1 q) :
    InverseBisectionSearch squareOnUnit_invertible
      (squareOnUnitRationalTarget q hq) where
  compute_preimage := sqrtApproxOnDomain q (sqrtDomain_of_unit hq)
  valid_preimage := sqrtApproxOnDomain_valid q (sqrtDomain_of_unit hq)
  preimage_subinterval := sqrtApproxOnUnit_subinterval q hq
  value_overlaps := by
    intro n
    have hspec := sqrtApproxOnDomain_spec q (sqrtDomain_of_unit hq) n
    change sq (sqrtApproxOnDomain q (sqrtDomain_of_unit hq) n).lo <= q /\
      q <= sq (sqrtApproxOnDomain q (sqrtDomain_of_unit hq) n).hi
    exact ⟨hspec.2.2.1, hspec.2.2.2⟩

/-- A represented target with an explicit rational anchor can reuse the
existing square-root bisection trace.  The anchor is not a chosen exact real
root: it is finite input data together with an `Equiv` certificate saying
that the target representative and the rational point overlap at every
stage.  The value-overlap field is then transported through the common
rational point, so this remains a represented-target certificate rather than
an appeal to a completed-real inverse or an IVT. -/
def sqrtOnUnitRepresentedTargetSearch
    (y : InRangeRaw squareOnUnit_invertible)
    (q : Rat) (hq : inDomainInterval 0 1 q)
    (heq : y.value.Equiv (RealCompute.ofRat q)) :
    InverseBisectionSearch squareOnUnit_invertible y where
  compute_preimage := (sqrtOnUnitBisectionSearch q hq).compute_preimage
  valid_preimage := (sqrtOnUnitBisectionSearch q hq).valid_preimage
  preimage_subinterval := (sqrtOnUnitBisectionSearch q hq).preimage_subinterval
  value_overlaps := by
    intro n
    let E := squareOnUnit_invertible.continuous.regular.evalInterval
      ((sqrtOnUnitBisectionSearch q hq).compute_preimage n)
      ((sqrtOnUnitBisectionSearch q hq).preimage_subinterval n) n
    have hEq : QInterval.Overlaps E ((RealCompute.ofRat q).compute n) := by
      change QInterval.Overlaps E ((RealCompute.ofRat q).compute n)
      exact (sqrtOnUnitBisectionSearch q hq).value_overlaps n
    have hE : E.lo <= q /\ q <= E.hi := by
      simpa [RealCompute.ofRat, QInterval.Overlaps] using hEq
    have hTarget : QInterval.Overlaps
        (y.value.compute n) ((RealCompute.ofRat q).compute n) := by
      exact (RealCompute.compareAt_overlap_iff y.value (RealCompute.ofRat q) n n).1
        (heq n)
    have hY : (y.value.compute n).lo <= q /\ q <= (y.value.compute n).hi := by
      simpa [RealCompute.ofRat, QInterval.Overlaps] using hTarget
    change QInterval.Overlaps E (y.value.compute n)
    unfold QInterval.Overlaps
    exact ⟨Rat.le_trans hE.1 hY.2, Rat.le_trans hY.1 hE.2⟩

/- A represented-target stage certificate.  The rational anchor supplies the
endpoint-square bracket and width budget, while the transported target field
supplies the actual overlap with the represented value. -/
theorem sqrtOnUnitRepresentedTargetSearch_stage_certificate
    (y : InRangeRaw squareOnUnit_invertible)
    (q : Rat) (hq : inDomainInterval 0 1 q)
    (heq : y.value.Equiv (RealCompute.ofRat q))
    (n : Nat) (hn : n ≠ 0) (eps : Rat)
    (hbudget : 1 / (((2 ^ (n + 9) : Nat) : Rat)) <= eps) :
    let search := sqrtOnUnitRepresentedTargetSearch y q hq heq
    let I := search.compute_preimage n
    subintervalOf I 0 1 /\
      I.lo * I.lo <= q /\
      q <= I.hi * I.hi /\
      I.width <= eps /\
      QInterval.Overlaps
        (squareOnUnit_invertible.continuous.regular.evalInterval I
          (search.preimage_subinterval n) n)
        (y.value.compute n) := by
  have hdomain : sqrtDomain q := by
    exact sqrtDomain_of_unit hq
  have hsub := sqrtApproxOnUnit_subinterval q hq n
  have hspec := sqrtApproxOnDomain_spec q hdomain n
  have hwidth := sqrtApproxOnDomain_width_eq_unit hdomain hq.2 n hn
  have hover :=
    (sqrtOnUnitRepresentedTargetSearch y q hq heq).value_overlaps n
  dsimp [sqrtOnUnitRepresentedTargetSearch]
  refine ⟨hsub, hspec.2.2.1, hspec.2.2.2, ?_, hover⟩
  change (sqrtApproxOnDomain q hdomain n).width <= eps
  rw [hwidth]
  exact hbudget

/-- A logarithmic number of bisections suffices for the unit branch's
reciprocal-stage error budget. Keep the schedule opaque to interval elaboration. -/
@[irreducible] def sqrtOnUnitStage (n : Nat) : Nat := Nat.log2 (32*(n+1))+1

def sqrtOnUnitSchedule : RealCompute.StageSchedule where
  stage := sqrtOnUnitStage
  monotone := by
    intro i j hij
    unfold sqrtOnUnitStage
    have hi : 32*(i+1) ≠ 0 := by omega
    have hj : 32*(j+1) ≠ 0 := by omega
    have hm : 32*(i+1) ≤ 32*(j+1) := by omega
    have hl := (Nat.le_log2 hj).2 (Nat.le_trans (Nat.log2_self_le hi) hm)
    omega
  cofinal := by
    intro target
    refine ⟨2^target, ?_⟩
    unfold sqrtOnUnitStage
    have hn : (32*(2^target+1):Nat) ≠ 0 :=
      Nat.ne_of_gt (Nat.mul_pos (by decide +kernel) (Nat.succ_pos (2^target)))
    have hl := (Nat.le_log2 hn).2 (by omega : 2^target ≤ 32*(2^target+1))
    omega

/-- Square root as a represented rational-domain function on `[0,1]`.  At a
point it is the existing certified rational bisection algorithm, merely read
through `sqrtOnUnitSchedule`; hence it introduces neither an ambient real
number nor a completeness principle. -/
def sqrtOnUnit : FunctionOnInterval where
  raw :=
    { definedAt := sqrtDomain
      compute := fun q h n =>
        (sqrtApproxOnDomain q h (sqrtOnUnitSchedule.stage n)) }
  lower := 0
  upper := 1
  defined_on := by
    intro q hq
    exact sqrtDomain_of_unit hq
  valid_on := by
    intro q hq
    have hscheduled := RealCompute.schedule_valid
      (sqrtRaw q hq) (sqrtRaw_valid q hq) sqrtOnUnitSchedule
    change RealCompute.ValidCompute
      (fun n => sqrtApproxOnDomain q hq (sqrtOnUnitSchedule.stage n)) at hscheduled
    exact hscheduled

/-- Point evaluation of the unit square-root branch is exactly the scheduled
rational bisection box. -/
theorem sqrtOnUnit_compute (q : Rat) (hq : inDomainInterval 0 1 q) (n : Nat) :
    sqrtOnUnit.compute q hq n =
      sqrtApproxOnDomain q (sqrtDomain_of_unit hq) (sqrtOnUnitSchedule.stage n) :=
  rfl

/-- Rescheduling the unit branch preserves the value of the original
certified rational square-root computation. -/
theorem sqrtOnUnit_agrees_raw (q : Rat) (hq : inDomainInterval 0 1 q) :
    (sqrtOnUnit.raw.evalRaw q (sqrtDomain_of_unit hq)).Equiv
      (sqrtRaw q (sqrtDomain_of_unit hq)) := by
  intro n
  simpa only [sqrtOnUnit, PartialRealFunRaw.evalRaw, sqrtRaw,
    RealCompute.schedule, RealCompute.compareAt] using
    (RealCompute.equiv_symm (RealCompute.schedule_equiv
      (sqrtRaw q (sqrtDomain_of_unit hq))
      (sqrtRaw_valid q (sqrtDomain_of_unit hq)) sqrtOnUnitSchedule)) n

/-- On the unit input range the generic bisection width constant is the
literal finite constant two. -/
private theorem sqrtWidthConstant_eq_two_on_unit
    {q : Rat} (hq : inDomainInterval 0 1 q) :
    sqrtWidthConstant q = 2 := by
  simp [sqrtWidthConstant, sqrtUpperBound_eq_one hq.2]

/-- A unit-range bisection box at stage `m` has width at most `2/(m+1)`.
This is the uniform quantitative fact used by the interval evaluator below. -/
private theorem sqrtApproxOnUnit_width_le_two_over_succ
    (q : Rat) (hq : inDomainInterval 0 1 q) (m : Nat) :
    (sqrtApproxOnDomain q (sqrtDomain_of_unit hq) m).width <=
      2 / (((m + 1 : Nat) : Rat)) := by
  have h := sqrtApproxOnDomain_width_le_nat_over_succ q
    (sqrtDomain_of_unit hq) m
  rw [sqrtWidthConstant_eq_two_on_unit hq] at h
  exact h

/-- The scheduled unit square-root point boxes fit within the explicit
`1/(32(n+1))` local error budget. -/
private theorem sqrtOnUnit_width_le_errorBudget
    (q : Rat) (hq : inDomainInterval 0 1 q) (n : Nat) :
    (sqrtOnUnit.compute q hq n).width <=
      1 / ((32 * (n + 1 : Nat) : Nat) : Rat) := by
  rw [sqrtOnUnit_compute]
  have hn : sqrtOnUnitSchedule.stage n ≠ 0 := by
    change sqrtOnUnitStage n ≠ 0
    unfold sqrtOnUnitStage
    omega
  rw [sqrtApproxOnDomain_width_eq_unit (sqrtDomain_of_unit hq) hq.2 _ hn]
  have hstage : 32*(n+1) ≤ 2^(sqrtOnUnitSchedule.stage n) := by
    have ht := Nat.lt_log2_self (n := 32*(n+1))
    change 32*(n+1) ≤ 2^(sqrtOnUnitStage n)
    unfold sqrtOnUnitStage
    omega
  have hp : 2^(sqrtOnUnitSchedule.stage n) ≤ 2^(sqrtOnUnitSchedule.stage n+9) :=
    Nat.pow_le_pow_right (by decide +kernel : 1≤2) (by omega)
  exact FTC.one_div_nat_antitone
    (by omega : 0<32*(n+1))
    (Nat.pow_pos (by decide +kernel : 0<2)) (Nat.le_trans hstage hp)

/-- The explicit pointwise error budget for the scheduled unit square-root
branch. -/
private def sqrtUnitErrorBudget (n : Nat) : Rat :=
  1 / ((32 * (n + 1 : Nat) : Nat) : Rat)

/-- The input modulus used by the square-root interval evaluator.  The square
is essential near zero: square root is uniformly continuous on `[0,1]`, but
does not have a global linear modulus there. -/
private def sqrtUnitInputPrecision (n : Nat) : Nat :=
  16 * (n + 1) * (n + 1)

/-- An interval enclosure for all scheduled square-root point boxes over a
subinterval of `[0,1]`.  The endpoint bisections provide the main bracket;
the explicit pointwise budget makes it an enclosure for every rational point
between them. -/
private def sqrtUnitEvalInterval (I : QInterval)
    (hI : subintervalOf I 0 1) (n : Nat) : QInterval :=
  let hlo : inDomainInterval 0 1 I.lo := ⟨hI.1, Rat.le_trans hI.2.1 hI.2.2⟩
  let hhi : inDomainInterval 0 1 I.hi := ⟨Rat.le_trans hI.1 hI.2.1, hI.2.2⟩
  { lo := (sqrtOnUnit.compute I.lo hlo n).lo - sqrtUnitErrorBudget n
    hi := (sqrtOnUnit.compute I.hi hhi n).hi + sqrtUnitErrorBudget n }

/-- The endpoint-expanded square-root interval contains every scheduled
pointwise bisection box in its input interval. -/
private theorem sqrtUnitEvalInterval_contains_point
    (I : QInterval) (hI : subintervalOf I 0 1)
    (x : Rat) (hx : inDomainInterval 0 1 x)
    (n : Nat) (hxlo : I.lo <= x) (hxhi : x <= I.hi) :
    (sqrtUnitEvalInterval I hI n).ContainsInterval
      (sqrtOnUnit.compute x hx n) := by
  let hlo : inDomainInterval 0 1 I.lo :=
    ⟨hI.1, Rat.le_trans hI.2.1 hI.2.2⟩
  let hhi : inDomainInterval 0 1 I.hi :=
    ⟨Rat.le_trans hI.1 hI.2.1, hI.2.2⟩
  let A := sqrtOnUnit.compute I.lo hlo n
  let B := sqrtOnUnit.compute I.hi hhi n
  let Y := sqrtOnUnit.compute x hx n
  let D := sqrtUnitErrorBudget n
  have hA : SqrtIntervalSpec I.lo A := by
    dsimp [A]
    rw [sqrtOnUnit_compute]
    exact sqrtApproxOnDomain_spec I.lo (sqrtDomain_of_unit hlo)
      (sqrtOnUnitSchedule.stage n)
  have hB : SqrtIntervalSpec I.hi B := by
    dsimp [B]
    rw [sqrtOnUnit_compute]
    exact sqrtApproxOnDomain_spec I.hi (sqrtDomain_of_unit hhi)
      (sqrtOnUnitSchedule.stage n)
  have hY : SqrtIntervalSpec x Y := by
    dsimp [Y]
    rw [sqrtOnUnit_compute]
    exact sqrtApproxOnDomain_spec x (sqrtDomain_of_unit hx)
      (sqrtOnUnitSchedule.stage n)
  have hYwidth : Y.width <= D := by
    dsimp [Y, D, sqrtUnitErrorBudget]
    exact sqrtOnUnit_width_le_errorBudget x hx n
  have hAlo_le_Yhi : A.lo <= Y.hi := by
    have hYhi_nonneg : 0 <= Y.hi := Rat.le_trans hY.1 hY.2.1
    apply le_of_sq_le_sq_of_nonneg_right hYhi_nonneg
    exact Rat.le_trans hA.2.2.1
      (Rat.le_trans hxlo hY.2.2.2)
  have hYlo_le_Bhi : Y.lo <= B.hi := by
    have hBhi_nonneg : 0 <= B.hi := Rat.le_trans hB.1 hB.2.1
    apply le_of_sq_le_sq_of_nonneg_right hBhi_nonneg
    exact Rat.le_trans hY.2.2.1
      (Rat.le_trans hxhi hB.2.2.2)
  have hlo : A.lo - D <= Y.lo := by
    unfold QInterval.width at hYwidth
    grind [Rat.sub_eq_add_neg]
  have hhi : Y.hi <= B.hi + D := by
    unfold QInterval.width at hYwidth
    grind [Rat.sub_eq_add_neg]
  unfold QInterval.ContainsInterval
  simp [sqrtUnitEvalInterval, A, B, Y, D, hlo, hhi]

/-! Public interface for interval-valued nested-radical algorithms.  The
implementation above deliberately keeps its scheduling details local; this
wrapper exposes only the finite enclosure contract needed by other
constructive algorithms, such as the dyadic sine table. -/

def sqrtOnUnitEvalInterval (I : QInterval)
    (hI : subintervalOf I 0 1) (n : Nat) : QInterval :=
  sqrtUnitEvalInterval I hI n

theorem sqrtOnUnitEvalInterval_contains_point
    (I : QInterval) (hI : subintervalOf I 0 1)
    (x : Rat) (hx : inDomainInterval 0 1 x)
    (n : Nat) (hxlo : I.lo <= x) (hxhi : x <= I.hi) :
    (sqrtOnUnitEvalInterval I hI n).ContainsInterval
      (sqrtOnUnit.compute x hx n) := by
  exact sqrtUnitEvalInterval_contains_point I hI x hx n hxlo hxhi

/-- A total executable wrapper for callers that are constructing an
interval recursively.  The fallback is never used once the caller has proved
the input interval lies in `[0,1]`; keeping it explicit makes the raw
algorithm total before that proof is attached. -/
def sqrtOnUnitEvalIntervalTotal (I : QInterval) (n : Nat) : QInterval :=
  if hI : 0 <= I.lo ∧ I.lo <= I.hi ∧ I.hi <= 1 then
    sqrtOnUnitEvalInterval I hI n
  else
    { lo := 0, hi := 1 }

theorem sqrtOnUnitEvalIntervalTotal_eq
    (I : QInterval) (hI : subintervalOf I 0 1) (n : Nat) :
    sqrtOnUnitEvalIntervalTotal I n = sqrtOnUnitEvalInterval I hI n := by
  change 0 <= I.lo ∧ I.lo <= I.hi ∧ I.hi <= 1 at hI
  simp [sqrtOnUnitEvalIntervalTotal, hI]

theorem sqrtOnUnitEvalIntervalTotal_contains_point
    (I : QInterval) (hI : subintervalOf I 0 1)
    (x : Rat) (hx : inDomainInterval 0 1 x)
    (n : Nat) (hxlo : I.lo <= x) (hxhi : x <= I.hi) :
    (sqrtOnUnitEvalIntervalTotal I n).ContainsInterval
      (sqrtOnUnit.compute x hx n) := by
  rw [sqrtOnUnitEvalIntervalTotal_eq I hI n]
  exact sqrtOnUnitEvalInterval_contains_point I hI x hx n hxlo hxhi

/-! Clipping is harmless for the unit square-root branch: the exact point
box already lies in `[0,1]`, while clipping removes only error padding that
falls outside the geometric range. -/

theorem sqrtOnUnit_compute_subinterval
    (q : Rat) (hq : inDomainInterval 0 1 q) (n : Nat) :
    subintervalOf (sqrtOnUnit.compute q hq n) 0 1 := by
  rw [sqrtOnUnit_compute]
  exact sqrtApproxOnUnit_subinterval q hq
    (sqrtOnUnitSchedule.stage n)

def sqrtOnUnitEvalIntervalClipped (I : QInterval) (n : Nat) : QInterval :=
  QInterval.intersection
    (sqrtOnUnitEvalIntervalTotal I n) { lo := 0, hi := 1 }

theorem sqrtOnUnitEvalIntervalClipped_width_le_total
    (I : QInterval) (n : Nat) :
    (sqrtOnUnitEvalIntervalClipped I n).width <=
      (sqrtOnUnitEvalIntervalTotal I n).width := by
  apply QInterval.width_le_of_contains
  unfold sqrtOnUnitEvalIntervalClipped
  exact QInterval.intersection_contained_left
    (sqrtOnUnitEvalIntervalTotal I n) { lo := 0, hi := 1 }

theorem sqrtOnUnitEvalIntervalClipped_subinterval
    (I : QInterval) (hI : subintervalOf I 0 1) (n : Nat) :
    subintervalOf (sqrtOnUnitEvalIntervalClipped I n) 0 1 := by
  let hx : inDomainInterval 0 1 I.lo :=
    ⟨hI.1, Rat.le_trans hI.2.1 hI.2.2⟩
  have hpoint := sqrtOnUnit_compute_subinterval I.lo hx n
  have htotal := sqrtOnUnitEvalIntervalTotal_contains_point I hI I.lo hx n
    Rat.le_refl hI.2.1
  have hunit : QInterval.ContainsInterval
      { lo := 0, hi := 1 } (sqrtOnUnit.compute I.lo hx n) :=
    ⟨hpoint.1, hpoint.2.2⟩
  have hinter := QInterval.intersection_contains htotal hunit
  have hunitContained := QInterval.intersection_contained_right
    (sqrtOnUnitEvalIntervalTotal I n) { lo := 0, hi := 1 }
  unfold sqrtOnUnitEvalIntervalClipped subintervalOf
  exact ⟨hunitContained.1,
    Rat.le_trans hinter.1 (Rat.le_trans hpoint.2.1 hinter.2),
    hunitContained.2⟩

/-! The scheduled error padding cannot disappear under clipping.  This is
useful for recursive interval algorithms: every valid unit-branch square-root
box has a genuinely positive rational width, including at exact endpoint
inputs. -/
theorem sqrtOnUnitEvalIntervalClipped_width_pos
    (I : QInterval) (hI : subintervalOf I 0 1) (n : Nat) :
    0 < (sqrtOnUnitEvalIntervalClipped I n).width := by
  change 0 < (QInterval.intersection
    (sqrtOnUnitEvalIntervalTotal I n) { lo := 0, hi := 1 }).width
  rw [sqrtOnUnitEvalIntervalTotal_eq I hI n]
  let hlo : inDomainInterval 0 1 I.lo :=
    ⟨hI.1, Rat.le_trans hI.2.1 hI.2.2⟩
  let hhi : inDomainInterval 0 1 I.hi :=
    ⟨Rat.le_trans hI.1 hI.2.1, hI.2.2⟩
  let A := sqrtOnUnit.compute I.lo hlo n
  let B := sqrtOnUnit.compute I.hi hhi n
  let D := sqrtUnitErrorBudget n
  have hA := sqrtOnUnit_compute_subinterval I.lo hlo n
  have hB := sqrtOnUnit_compute_subinterval I.hi hhi n
  have hAs : SqrtIntervalSpec I.lo A := by
    dsimp [A]
    rw [sqrtOnUnit_compute]
    exact sqrtApproxOnDomain_spec I.lo (sqrtDomain_of_unit hlo)
      (sqrtOnUnitSchedule.stage n)
  have hBs : SqrtIntervalSpec I.hi B := by
    dsimp [B]
    rw [sqrtOnUnit_compute]
    exact sqrtApproxOnDomain_spec I.hi (sqrtDomain_of_unit hhi)
      (sqrtOnUnitSchedule.stage n)
  have hcross : A.lo <= B.hi := by
    have hsq : sq A.lo <= I.hi :=
      Rat.le_trans hAs.2.2.1 hI.2.1
    exact hBs.le_hi_of_sq_le hsq
  have hD : 0 < D := by
    dsimp [D, sqrtUnitErrorBudget]
    exact one_div_nat_pos (by omega)
  have hleft : A.lo - D < 1 := by
    have hAle : A.lo <= 1 := by
      dsimp [A]
      exact Rat.le_trans hA.2.1 hA.2.2
    grind
  have hright : 0 < B.hi + D := by
    have hBge : 0 <= B.hi := by
      dsimp [B]
      exact Rat.le_trans hB.1 hB.2.1
    grind
  unfold sqrtOnUnitEvalInterval sqrtUnitEvalInterval
  simp only [A, B, D]
  unfold QInterval.intersection QInterval.width
  by_cases hlo' : (sqrtOnUnit.compute I.lo hlo n).lo -
      sqrtUnitErrorBudget n <= 0
  · simp [Rat.max_def, hlo']
    by_cases hhi' : (sqrtOnUnit.compute I.hi hhi n).hi +
        sqrtUnitErrorBudget n <= 1
    · simp [Rat.min_def, hhi']
      grind
    · simp [Rat.min_def, hhi']
      grind
  · simp [Rat.max_def, hlo']
    by_cases hhi' : (sqrtOnUnit.compute I.hi hhi n).hi +
        sqrtUnitErrorBudget n <= 1
    · simp [Rat.min_def, hhi']
      grind
    · simp [Rat.min_def, hhi']
      grind

theorem sqrtOnUnitEvalIntervalClipped_contains_point
    (I : QInterval) (hI : subintervalOf I 0 1)
    (x : Rat) (hx : inDomainInterval 0 1 x)
    (n : Nat) (hxlo : I.lo <= x) (hxhi : x <= I.hi) :
    (sqrtOnUnitEvalIntervalClipped I n).ContainsInterval
      (sqrtOnUnit.compute x hx n) := by
  apply QInterval.intersection_contains
  · exact sqrtOnUnitEvalIntervalTotal_contains_point I hI x hx n hxlo hxhi
  · have h := sqrtOnUnit_compute_subinterval x hx n
    exact ⟨h.1, h.2.2⟩

theorem sqrtOnUnitEvalIntervalClipped_square_contains_input
    (I : QInterval) (hI : subintervalOf I 0 1) (n : Nat) :
    sq (sqrtOnUnitEvalIntervalClipped I n).lo <= I.lo /\
      I.hi <= sq (sqrtOnUnitEvalIntervalClipped I n).hi := by
  let J := sqrtOnUnitEvalIntervalClipped I n
  have hJ : subintervalOf J 0 1 := by
    exact sqrtOnUnitEvalIntervalClipped_subinterval I hI n
  have hlo : inDomainInterval 0 1 I.lo :=
    ⟨hI.1, Rat.le_trans hI.2.1 hI.2.2⟩
  have hhi : inDomainInterval 0 1 I.hi :=
    ⟨Rat.le_trans hI.1 hI.2.1, hI.2.2⟩
  have hloJ := sqrtOnUnitEvalIntervalClipped_contains_point
    I hI I.lo hlo n Rat.le_refl hI.2.1
  have hhiJ := sqrtOnUnitEvalIntervalClipped_contains_point
    I hI I.hi hhi n hI.2.1 Rat.le_refl
  have hslo := sqrtApproxOnDomain_spec I.lo
    (sqrtDomain_of_unit hlo) (sqrtOnUnitSchedule.stage n)
  have hshi := sqrtApproxOnDomain_spec I.hi
    (sqrtDomain_of_unit hhi) (sqrtOnUnitSchedule.stage n)
  have hlo_sq : sq J.lo <= sq
      (sqrtOnUnit.compute I.lo hlo n).lo := by
    apply sq_le_sq_of_nonneg_le hJ.1
    exact hloJ.1
  have hhi_sq : sq (sqrtOnUnit.compute I.hi hhi n).hi <= sq J.hi := by
    apply sq_le_sq_of_nonneg_le
      (by
        have hp := sqrtOnUnit_compute_subinterval I.hi hhi n
        have hp0 : 0 <= (sqrtOnUnit.compute I.hi hhi n).hi :=
          Rat.le_trans hp.1 hp.2.1
        simpa [sqrtOnUnit_compute] using hp0)
    exact hhiJ.2
  constructor
  · exact Rat.le_trans hlo_sq (by
      rw [sqrtOnUnit_compute]
      exact hslo.2.2.1)
  · exact Rat.le_trans hshi.2.2.2 (Rat.le_trans hhi_sq Rat.le_refl)

private theorem sqrtUnitErrorBudget_pos (n : Nat) :
    0 < sqrtUnitErrorBudget n := by
  unfold sqrtUnitErrorBudget
  exact one_div_nat_pos (by omega)

private theorem sqrtUnitInputPrecision_pos (n : Nat) :
    0 < sqrtUnitInputPrecision n := by
  unfold sqrtUnitInputPrecision
  exact Nat.mul_pos
    (Nat.mul_pos (by omega) (Nat.succ_pos n))
    (Nat.succ_pos n)

/-- The quadratic input modulus is exactly the square of the radius used in
the elementary square-root gap estimate. -/
private theorem sqrtUnitInputPrecision_inverse_eq_radius_sq (n : Nat) :
    1 / ((sqrtUnitInputPrecision n : Nat) : Rat) =
      sq (1 / ((4 * (n + 1 : Nat) : Nat) : Rat)) := by
  let T : Rat := ((n + 1 : Nat) : Rat)
  have hcast16 : ((16 * (n + 1) * (n + 1) : Nat) : Rat) =
      (16 : Rat) * T * T := by
    dsimp [T]
    repeat rw [Rat.natCast_mul]
    have h16 : ((16 : Nat) : Rat) = (16 : Rat) := by
      decide +kernel
    rw [h16]
  have hcast4 : ((4 * (n + 1) : Nat) : Rat) = (4 : Rat) * T := by
    dsimp [T]
    exact Rat.natCast_mul 4 (n + 1)
  have hnum : (16 : Rat)⁻¹ = (4 : Rat)⁻¹ * (4 : Rat)⁻¹ := by
    decide +kernel
  unfold sqrtUnitInputPrecision sq
  repeat rw [Rat.div_def]
  rw [hcast16, hcast4]
  repeat rw [Rat.inv_mul_rev]
  rw [hnum]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The radius `1/(4(n+1))` is eight of the scheduled pointwise error
budgets. -/
private theorem sqrtUnitRadius_eq_eight_errorBudget (n : Nat) :
    1 / ((4 * (n + 1 : Nat) : Nat) : Rat) =
      8 * sqrtUnitErrorBudget n := by
  let T : Rat := ((n + 1 : Nat) : Rat)
  have hcast4 : ((4 * (n + 1) : Nat) : Rat) = (4 : Rat) * T := by
    dsimp [T]
    exact Rat.natCast_mul 4 (n + 1)
  have hcast32 : ((32 * (n + 1) : Nat) : Rat) = (32 : Rat) * T := by
    dsimp [T]
    exact Rat.natCast_mul 32 (n + 1)
  have hnum : (4 : Rat)⁻¹ = 8 * (32 : Rat)⁻¹ := by
    decide +kernel
  unfold sqrtUnitErrorBudget
  repeat rw [Rat.div_def]
  rw [hcast4, hcast32]
  repeat rw [Rat.inv_mul_rev]
  rw [hnum]
  grind [Rat.mul_assoc, Rat.mul_comm]

private theorem sqrtUnit_thirteen_errorBudget_le_target (n : Nat) :
    13 * sqrtUnitErrorBudget n <=
      1 / ((n + 1 : Nat) : Rat) := by
  let T : Rat := ((n + 1 : Nat) : Rat)
  have hTpos : 0 < T := by
    dsimp [T]
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hTne : T ≠ 0 := Rat.ne_of_gt hTpos
  have hprodpos : 0 < (32 : Rat) * T :=
    Rat.mul_pos (by decide +kernel) hTpos
  have hcast32 : ((32 * (n + 1) : Nat) : Rat) = (32 : Rat) * T := by
    dsimp [T]
    exact Rat.natCast_mul 32 (n + 1)
  apply Rat.le_of_mul_le_mul_right (c := (32 : Rat) * T)
  · unfold sqrtUnitErrorBudget
    repeat rw [Rat.div_def]
    rw [hcast32]
    calc
      (13 * (1 * ((32 : Rat) * T)⁻¹)) * ((32 : Rat) * T) = 13 := by
        calc
          (13 * (1 * ((32 : Rat) * T)⁻¹)) * ((32 : Rat) * T) =
              13 * (((32 : Rat) * T)⁻¹ * ((32 : Rat) * T)) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
          _ = 13 := by
            rw [Rat.inv_mul_cancel _ (Rat.ne_of_gt hprodpos)]
            grind
      _ <= 32 := by decide +kernel
      _ = (1 * T⁻¹) * ((32 : Rat) * T) := by
        calc
          (32 : Rat) = 32 * (T⁻¹ * T) := by
            rw [Rat.inv_mul_cancel _ hTne]
            grind
          _ = (1 * T⁻¹) * ((32 : Rat) * T) := by
            grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hprodpos

/-- The square-root interval enclosure has the literal `1/(n+1)` output
width required by `IntervalRegularOn`, provided the input box has the
quadratic modulus `1/(16(n+1)^2)`. -/
private theorem sqrtUnitEvalInterval_width_le
    (I : QInterval) (hI : subintervalOf I 0 1) (n : Nat)
    (hinput : I.width <= 1 / ((sqrtUnitInputPrecision n : Nat) : Rat)) :
    (sqrtUnitEvalInterval I hI n).width <=
      1 / ((n + 1 : Nat) : Rat) := by
  have hIlo : 0 <= I.lo := hI.1
  have hIord : I.lo <= I.hi := hI.2.1
  have hIhi : I.hi <= 1 := hI.2.2
  let hlo : inDomainInterval 0 1 I.lo :=
    ⟨hIlo, Rat.le_trans hIord hIhi⟩
  let hhi : inDomainInterval 0 1 I.hi :=
    ⟨Rat.le_trans hIlo hIord, hIhi⟩
  let W : Rat := I.width
  let hW : inDomainInterval 0 1 W := by
    have hWnonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hWle : I.width <= 1 := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    exact ⟨hWnonneg, hWle⟩
  let A := sqrtOnUnit.compute I.lo hlo n
  let B := sqrtOnUnit.compute I.hi hhi n
  let S := sqrtOnUnit.compute W hW n
  let D := sqrtUnitErrorBudget n
  let R : Rat := 1 / ((4 * (n + 1 : Nat) : Nat) : Rat)
  have hA : SqrtIntervalSpec I.lo A := by
    dsimp [A]
    rw [sqrtOnUnit_compute]
    exact sqrtApproxOnDomain_spec I.lo (sqrtDomain_of_unit hlo)
      (sqrtOnUnitSchedule.stage n)
  have hB : SqrtIntervalSpec I.hi B := by
    dsimp [B]
    rw [sqrtOnUnit_compute]
    exact sqrtApproxOnDomain_spec I.hi (sqrtDomain_of_unit hhi)
      (sqrtOnUnitSchedule.stage n)
  have hS : SqrtIntervalSpec W S := by
    dsimp [S]
    rw [sqrtOnUnit_compute]
    exact sqrtApproxOnDomain_spec W (sqrtDomain_of_unit hW)
      (sqrtOnUnitSchedule.stage n)
  have hAwidth : A.width <= D := by
    dsimp [A, D, sqrtUnitErrorBudget]
    exact sqrtOnUnit_width_le_errorBudget I.lo hlo n
  have hBwidth : B.width <= D := by
    dsimp [B, D, sqrtUnitErrorBudget]
    exact sqrtOnUnit_width_le_errorBudget I.hi hhi n
  have hSwidth : S.width <= D := by
    dsimp [S, D, sqrtUnitErrorBudget]
    exact sqrtOnUnit_width_le_errorBudget W hW n
  have hWleRsq : W <= sq R := by
    dsimp [W, R]
    calc
      I.width <= 1 / ((sqrtUnitInputPrecision n : Nat) : Rat) := hinput
      _ = sq (1 / ((4 * (n + 1 : Nat) : Nat) : Rat)) :=
        sqrtUnitInputPrecision_inverse_eq_radius_sq n
  have hRnonneg : 0 <= R := by
    dsimp [R]
    exact Rat.le_of_lt (one_div_nat_pos (by omega))
  have hSlo_le_R : S.lo <= R :=
    SqrtIntervalSpec.lo_le_of_sq_le hS hRnonneg hWleRsq
  have hShi_le_R_add_D : S.hi <= R + D := by
    unfold QInterval.width at hSwidth
    grind [Rat.sub_eq_add_neg]
  let C : Rat := B.lo - A.hi
  have hC_le_Shi : C <= S.hi := by
    by_cases hCnonpos : C <= 0
    · exact Rat.le_trans hCnonpos (Rat.le_trans hS.1 hS.2.1)
    · have hCnonneg : 0 <= C := Rat.le_of_lt (by grind)
      have hC_le_sum : C <= B.lo + A.hi := by
        dsimp [C]
        have hAhi_nonneg : 0 <= A.hi := Rat.le_trans hA.1 hA.2.1
        grind [Rat.sub_eq_add_neg]
      have hdiffSq : sq B.lo - sq A.hi <= W := by
        have hBloSq : sq B.lo <= I.hi := hB.2.2.1
        have hAhiSq : I.lo <= sq A.hi := hA.2.2.2
        dsimp [W]
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg]
      have hCsq : sq C <= W := by
        calc
          sq C = C * C := rfl
          _ <= C * (B.lo + A.hi) :=
            Rat.mul_le_mul_of_nonneg_left hC_le_sum hCnonneg
          _ = sq B.lo - sq A.hi := by
            dsimp [C, sq]
            grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
              Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
          _ <= W := hdiffSq
      have hShi_nonneg : 0 <= S.hi := Rat.le_trans hS.1 hS.2.1
      apply le_of_sq_le_sq_of_nonneg_right hShi_nonneg
      exact Rat.le_trans hCsq hS.2.2.2
  have hC_le_R_add_D : C <= R + D :=
    Rat.le_trans hC_le_Shi hShi_le_R_add_D
  have htotal : B.hi + D - (A.lo - D) <= R + 5 * D := by
    unfold QInterval.width at hAwidth hBwidth
    dsimp [C] at hC_le_R_add_D
    grind [Rat.sub_eq_add_neg]
  have htarget : R + 5 * D <= 1 / ((n + 1 : Nat) : Rat) := by
    rw [show R = 8 * D by
      dsimp [R, D]
      exact sqrtUnitRadius_eq_eight_errorBudget n]
    calc
      8 * D + 5 * D = 13 * D := by
        grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
      _ <= 1 / ((n + 1 : Nat) : Rat) := by
        dsimp [D]
        exact sqrtUnit_thirteen_errorBudget_le_target n
  unfold QInterval.width
  simpa [sqrtUnitEvalInterval, A, B, D] using Rat.le_trans htotal htarget

/-- The quantitative width bound for the public interval wrapper.  The
    quadratic input budget is the computable modulus needed near zero; no
    ambient real-valued continuity theorem is involved. -/
theorem sqrtOnUnitEvalInterval_width_le
    (I : QInterval) (hI : subintervalOf I 0 1) (n : Nat)
    (hinput : I.width <=
      1 / (((16 * (n + 1) * (n + 1) : Nat) : Rat))) :
    (sqrtOnUnitEvalIntervalTotal I n).width <=
      1 / (((n + 1 : Nat) : Rat)) := by
  have hinput' : I.width <=
      1 / ((sqrtUnitInputPrecision n : Nat) : Rat) := by
    simpa [sqrtUnitInputPrecision] using hinput
  rw [sqrtOnUnitEvalIntervalTotal_eq I hI n]
  exact sqrtUnitEvalInterval_width_le I hI n hinput'

/-- Square root is interval-regular on the nonnegative unit interval.  Its
quadratic input modulus is an entirely finite rational estimate, so the
result supplies literal epsilon--delta continuity without topology or an
ambient completed real line. -/
def sqrtOnUnit_intervalRegular : IntervalRegularOn sqrtOnUnit where
  evalInterval := sqrtUnitEvalInterval
  inputPrecision := sqrtUnitInputPrecision
  inputPrecision_pos := sqrtUnitInputPrecision_pos
  output_width := by
    intro I hI n hinput
    constructor
    · let hx : inDomainInterval 0 1 I.lo :=
        ⟨hI.1, Rat.le_trans hI.2.1 hI.2.2⟩
      have hcontains := sqrtUnitEvalInterval_contains_point I hI I.lo hx n
        Rat.le_refl hI.2.1
      have hpoint := sqrtOnUnit.valid_on I.lo (sqrtOnUnit.defined_on I.lo hx)
      have hpointWidth : 0 <= (sqrtOnUnit.compute I.lo hx n).width := by
        simpa [FunctionOnInterval.compute] using hpoint.1 n
      unfold QInterval.ContainsInterval at hcontains
      unfold QInterval.width at hpointWidth ⊢
      grind [Rat.sub_eq_add_neg]
    · exact sqrtUnitEvalInterval_width_le I hI n hinput
  contains_point_values := sqrtUnitEvalInterval_contains_point

/-- The scheduled bisection square-root branch is a continuous function in
the project's rational epsilon--delta sense. -/
def sqrtOnUnit_continuous : ContinuousFunctionOnInterval where
  function := sqrtOnUnit
  regular := sqrtOnUnit_intervalRegular

theorem sqrtOnUnit_epsilonDeltaContinuous :
    EpsilonDeltaContinuousOn sqrtOnUnit :=
  sqrtOnUnit_intervalRegular.epsilonDeltaContinuous

namespace Rat

def IsNatSquare (n : Nat) : Prop :=
  Exists fun k : Nat => k * k = n

/-- An integer square, stated in a way that exposes the finite search:
negative integers are excluded, and otherwise one searches natural squares up to
`z.natAbs`. -/
def IsIntSquare (z : Int) : Prop :=
  0 <= z /\ IsNatSquare z.natAbs

/-- A rational square.  We do not require the witness to be nonnegative:
if `r^2 = q`, then the nonnegative square-root value is `|r|`. -/
def IsSquare (q : Rat) : Prop :=
  Exists fun r : Rat => sq r = q

def NotSquare (q : Rat) : Prop :=
  ¬ IsSquare q

/-- Finite normal-form criterion: a reduced rational is a square precisely when
its numerator and denominator are squares. -/
def IsSquareInLowestTerms (q : Rat) : Prop :=
  IsIntSquare q.num /\ IsNatSquare q.den

/-- Finite normal-form nonsquare criterion.

For a reduced rational, it is enough for either the numerator or the denominator
to fail the finite square test.  Requiring both to be nonsquares is a useful
sufficient special case, but not necessary: `2 / 9` and `4 / 3` are already
nonsquares. -/
def IsNonSquareInLowestTerms (q : Rat) : Prop :=
  ¬ IsIntSquare q.num ∨ ¬ IsNatSquare q.den

theorem sq_num (r : Rat) : (sq r).num = r.num * r.num := by
  unfold sq
  unfold HMul.hMul instHMul Mul.mul Rat.instMul Rat.mul
  simp [r.reduced]
  rfl

theorem sq_den (r : Rat) : (sq r).den = r.den * r.den := by
  unfold sq
  unfold HMul.hMul instHMul Mul.mul Rat.instMul Rat.mul
  simp [r.reduced]
  rfl

theorem sq_num_nonneg (r : Rat) : 0 <= (sq r).num := by
  rw [sq_num]
  rw [← Int.natAbs_mul_self]
  exact Int.natCast_nonneg _

theorem sq_num_isIntSquare (r : Rat) : IsIntSquare (sq r).num := by
  constructor
  · exact sq_num_nonneg r
  · refine ⟨r.num.natAbs, ?_⟩
    rw [sq_num]
    simp [Int.natAbs_mul]

theorem sq_den_isNatSquare (r : Rat) : IsNatSquare (sq r).den := by
  refine ⟨r.den, ?_⟩
  rw [sq_den]

/-- Euclid's normal-form observation: when a reduced rational is a square, its
normalized numerator and denominator are squares. -/
theorem isSquareInLowestTerms_of_isSquare {q : Rat} :
    IsSquare q -> IsSquareInLowestTerms q := by
  intro hq
  rcases hq with ⟨r, hr⟩
  rw [← hr]
  exact ⟨sq_num_isIntSquare r, sq_den_isNatSquare r⟩

theorem isSquare_of_isSquareInLowestTerms {q : Rat} :
    IsSquareInLowestTerms q -> IsSquare q := by
  intro hs
  rcases hs.1 with ⟨hnum_nonneg, hnum_square⟩
  rcases hnum_square with ⟨a, ha⟩
  rcases hs.2 with ⟨b, hb⟩
  have haRat : (a : Rat) * (a : Rat) = (q.num : Rat) := by
    have haInt : ((a * a : Nat) : Int) = q.num := by
      rw [ha]
      exact Int.natAbs_of_nonneg hnum_nonneg
    exact_mod_cast haInt
  have hbRat : (b : Rat) * (b : Rat) = (q.den : Rat) := by
    exact_mod_cast hb
  have hb_ne_zero : b ≠ 0 := by
    intro hb0
    apply q.den_nz
    rw [← hb]
    simp [hb0]
  have hbRat_ne_zero : (b : Rat) ≠ 0 := by
    exact_mod_cast hb_ne_zero
  refine Exists.intro ((a : Rat) / (b : Rat)) ?_
  apply rat_eq_of_den_mul_eq_num (q := q)
  rw [← hbRat, ← haRat]
  unfold sq
  rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel, Rat.inv_mul_cancel]

theorem square_iff_lowest_terms_square (q : Rat) :
    IsSquare q ↔ IsSquareInLowestTerms q :=
  ⟨isSquareInLowestTerms_of_isSquare, isSquare_of_isSquareInLowestTerms⟩

/-- Contrapositive form used for irrational square roots: if either normalized
part is not a square, then the rational is not a rational square. -/
theorem notSquare_of_nonSquareInLowestTerms {q : Rat} :
    IsNonSquareInLowestTerms q -> NotSquare q := by
  intro hns hsq
  have hs := isSquareInLowestTerms_of_isSquare hsq
  cases hns with
  | inl hnum => exact hnum hs.1
  | inr hden => exact hden hs.2

theorem notSquare_iff_lowest_terms_nonsquare (q : Rat) :
    NotSquare q ↔ IsNonSquareInLowestTerms q := by
  constructor
  · intro hn
    classical
    by_cases hnum : IsIntSquare q.num
    · right
      intro hden
      exact hn (isSquare_of_isSquareInLowestTerms ⟨hnum, hden⟩)
    · left
      exact hnum
  · exact notSquare_of_nonSquareInLowestTerms

theorem integer_square_criterion (z : Int) :
    IsSquare (z : Rat) ↔ IsIntSquare z := by
  exact Iff.trans (square_iff_lowest_terms_square (z : Rat)) (by
    unfold IsSquareInLowestTerms
    constructor
    · intro h
      simpa using h.1
    · intro hz
      constructor
      · simpa using hz
      · refine ⟨1, ?_⟩
        simp)

theorem square_root_denominator_bound (q r : Rat) (hr : sq r = q) :
    r.den <= q.den := by
  rw [← hr, sq_den]
  exact Nat.le_mul_of_pos_right r.den (Nat.pos_of_ne_zero r.den_nz)

end Rat

/-- General theorem target for rational square roots:
if `q` is a rational square, then the computable real produced by the rational
sqrt algorithm for `q` is rational.  The expected rational representative is
`|r|`, since the sqrt algorithm computes the nonnegative root. -/
theorem sqrt_rational_of_square
    (q r : Rat) (hq : sqrtDomain q) (h : SqrtRawSpec q hq)
    (hr : sq r = q) :
    (sqrtReal q hq h.1).Equiv (RealCompute.Certified.ofRat (qabs r)) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  have hI := h.2 n
  have habs_nonneg : 0 <= qabs r := qabs_nonneg r
  have hq_le_sq : q <= sq (qabs r) := by
    rw [sq_qabs, hr]
    exact Rat.le_refl
  have hsq_le_q : sq (qabs r) <= q := by
    rw [sq_qabs, hr]
    exact Rat.le_refl
  have hlo : ((sqrtRaw q hq).compute n).lo <= qabs r :=
    SqrtIntervalSpec.lo_le_of_sq_le hI habs_nonneg hq_le_sq
  have hhi : qabs r <= ((sqrtRaw q hq).compute n).hi :=
    SqrtIntervalSpec.le_hi_of_sq_le hI hsq_le_q
  exact (RealCompute.compareAt_overlap_iff (sqrtRaw q hq)
    (RealCompute.ofRat (qabs r)) n n).2
    (by simpa [RealCompute.ofRat, QInterval.Overlaps] using And.intro hlo hhi)

/-- Equivalently: for nonnegative rational input, the rational sqrt algorithm
produces a rational computable real exactly for rational-square inputs. -/
theorem sqrt_rational_iff_square
    (q : Rat) (hq : sqrtDomain q) (h : SqrtRawSpec q hq) :
    RealCompute.Certified.Rational (sqrtReal q hq h.1) ↔ Rat.IsSquare q := by
  constructor
  case mp =>
    intro hrational
    rcases hrational with ⟨r, heq⟩
    refine Exists.intro r ?_
    have heqRaw : (sqrtRaw q hq).Equiv (RealCompute.ofRat r) := by
      simpa [sqrtReal, RealCompute.Certified.ofRat, RealCompute.Certified.Equiv, RealCompute.Certified.ofRaw] using heq
    exact sq_eq_of_sqrt_spec_equiv_rat h heqRaw
  case mpr =>
    intro hsquare
    rcases hsquare with ⟨r, hr⟩
    refine Exists.intro (qabs r) ?_
    exact sqrt_rational_of_square q r hq h hr

/-- Lowest-terms version of the classification: the rationality of the
computable real `sqrt(q)` is determined by whether the normalized numerator and
denominator of `q` are both squares. -/
theorem sqrt_rational_iff_lowest_terms_square
    (q : Rat) (hq : sqrtDomain q) (h : SqrtRawSpec q hq) :
    RealCompute.Certified.Rational (sqrtReal q hq h.1) ↔
      Rat.IsSquareInLowestTerms q := by
  exact Iff.trans (sqrt_rational_iff_square q hq h)
    (Rat.square_iff_lowest_terms_square q)

end ComputableAnalysis


