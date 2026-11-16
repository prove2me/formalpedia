-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteFTCIntervalRegular
-- name    : liuyao_ca_fd889115_k1_Analysis_FiniteFTCIntervalRegular
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:18:05.917738+00:00
-- url     : https://prove2.me/theorems/bd4f4166-a309-47c1-9b9a-1bc04a905fe4
-- title:
--   Computable analysis · FiniteFTCIntervalRegular · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FiniteFTCIntervalRegular.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Calculus
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralIdentities
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Series

set_option autoImplicit true

/-!
# Interval-regular integral certificates

This module names the current boundary between interval regularity and
integrability.  `IntervalRegularOn` supplies the pointwise interval modulus;
the integral construction is still explicit certificate data.  The general
construction theorem is therefore not asserted, while exact constants give a
fully checked first instance.
-/

namespace ComputableAnalysis

namespace Integral

structure IntervalRegularCandidateCertificate (F : FunctionOnInterval) where
  regular : IntervalRegularOn F
  construction : CandidateConstructionFor F

def raw (F : FunctionOnInterval)
    (certificate : IntervalRegularCandidateCertificate F) : RealCompute :=
  candidateValueFor F certificate.construction

theorem raw_valid (F : FunctionOnInterval)
    (certificate : IntervalRegularCandidateCertificate F) :
    (raw F certificate).Valid := by
  exact candidateValueFor_valid F certificate.construction

def exactRat_constant (c a b : Rat) :
    IntervalRegularCandidateCertificate
      (FunctionOnInterval.exactRat (fun _ => c) a b) where
  regular := exactRat_constant_intervalRegularOn c a b
  construction := (constantMonotoneCandidateConstructionFor c a b).construction

theorem exactRat_constant_raw_eq_ofRat (c a b : Rat) :
    raw (FunctionOnInterval.exactRat (fun _ => c) a b)
      (exactRat_constant c a b) =
      RealCompute.ofRat ((b - a) * c) := by
  rfl

theorem exactRat_constant_raw_valid (c a b : Rat) :
    (raw (FunctionOnInterval.exactRat (fun _ => c) a b)
      (exactRat_constant c a b)).Valid := by
  exact raw_valid _ (exactRat_constant c a b)

/-- The interval image of a rational affine map with nonnegative slope. -/
def affineInterval (r c : Rat) (I : QInterval) : QInterval :=
  { lo := r * I.lo + c, hi := r * I.hi + c }

def stableAffine (r c : Rat) : StablePartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x _ => { lo := r * x + c, hi := r * x + c }
  rate := fun _ => .unknown

def stableAffineFunction (r c a b : Rat) : FunctionOnInterval :=
  FunctionOnInterval.ofStable (stableAffine r c) a b
    (fun _ _ => trivial)
    (fun x _ => RealCompute.ofRat_valid (r * x + c))

def stableAffine_intervalRegularOn_of_unit_slope
    (r c a b : Rat) (hr0 : 0 <= r) (hr1 : r <= 1) :
    IntervalRegularOn (stableAffineFunction r c a b) :=
  IntervalRegularOn.ofStable
    (stableAffine r c) a b
    (fun _ _ => trivial)
    (fun x _ => RealCompute.ofRat_valid (r * x + c))
    (fun I _hI _n => affineInterval r c I)
    (fun n => n + 1)
    (by intro n; omega)
    (by
      intro I hI n hsmall
      have hwidth_nonneg : 0 <= I.width := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg, hI.2.1]
      have hscaled_nonneg : 0 <= r * I.width :=
        Rat.mul_nonneg hr0 hwidth_nonneg
      have hscaled_le : r * I.width <= I.width := by
        have hmul := Rat.mul_le_mul_of_nonneg_right hr1 hwidth_nonneg
        simpa using hmul
      have hbound : r * I.width <= 1 / ((n + 1 : Nat) : Rat) :=
        Rat.le_trans hscaled_le hsmall
      have himage_width : (affineInterval r c I).width = r * I.width := by
        grind [affineInterval, QInterval.width, Rat.sub_eq_add_neg,
          Rat.mul_add, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
      rw [himage_width]
      constructor
      · exact hscaled_nonneg
      · exact hbound)
    (by
      intro I hI x hx n hIlo hIhi
      change QInterval.ContainsInterval (affineInterval r c I)
        { lo := r * x + c, hi := r * x + c }
      unfold affineInterval QInterval.ContainsInterval
      constructor
      · exact (Rat.add_le_add_right).2
          (Rat.mul_le_mul_of_nonneg_left hIlo hr0)
      · exact (Rat.add_le_add_right).2
          (Rat.mul_le_mul_of_nonneg_left hIhi hr0))

def stableSquare : StablePartialRealFunRaw where
  definedAt := fun x => 0 <= x ∧ x <= 1
  compute := fun x _ => { lo := x * x, hi := x * x }
  rate := fun _ => .unknown

def stableSquareFunction : FunctionOnInterval :=
  FunctionOnInterval.ofStable stableSquare 0 1
    (fun _ hx => hx)
    (fun x _ => RealCompute.ofRat_valid (x * x))

def stableSquareInterval (I : QInterval) : QInterval :=
  { lo := I.lo * I.lo, hi := I.hi * I.hi }

def stableSquare_intervalRegularOn_unit :
    IntervalRegularOn stableSquareFunction :=
  IntervalRegularOn.ofStable stableSquare 0 1
    (fun _ hx => hx)
    (fun x _ => RealCompute.ofRat_valid (x * x))
    (fun I _hI _n => stableSquareInterval I)
    (fun n => 2 * (n + 1))
    (by intro n; omega)
    (by
      intro I hI n hsmall
      have hwidth_nonneg : 0 <= I.width := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg, hI.2.1]
      have hlo_nonneg : 0 <= I.lo := hI.1
      have hhi_nonneg : 0 <= I.hi := Rat.le_trans hlo_nonneg hI.2.1
      have hsum_nonneg : 0 <= I.hi + I.lo :=
        Rat.add_nonneg hhi_nonneg hlo_nonneg
      have hsum_le_two : I.hi + I.lo <= 2 := by
        have hhi_le_one : I.hi <= 1 := hI.2.2
        have hlo_le_one : I.lo <= 1 := Rat.le_trans hI.2.1 hhi_le_one
        grind
      have hwidth : (stableSquareInterval I).width =
          I.width * (I.hi + I.lo) := by
        unfold stableSquareInterval QInterval.width
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
      rw [hwidth]
      constructor
      · exact Rat.mul_nonneg hwidth_nonneg hsum_nonneg
      · have hprod : I.width * (I.hi + I.lo) <= I.width * 2 :=
          Rat.mul_le_mul_of_nonneg_left hsum_le_two hwidth_nonneg
        have htwo : 2 * I.width <= 1 / ((n + 1 : Nat) : Rat) := by
          calc
            2 * I.width <= 2 * (1 / ((2 * (n + 1) : Nat) : Rat)) :=
              Rat.mul_le_mul_of_nonneg_left hsmall (by decide +kernel)
            _ = 1 / ((n + 1 : Nat) : Rat) := by
              rw [Rat.div_def]
              have hnrat : ((n + 1 : Nat) : Rat) ≠ 0 :=
                Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos n))
              rw [show ((2 * (n + 1) : Nat) : Rat) =
                (2 : Rat) * ((n + 1 : Nat) : Rat) by
                  exact_mod_cast (by omega : 2 * (n + 1) = 2 * (n + 1))]
              rw [Rat.inv_mul_rev]
              grind [Rat.mul_assoc, Rat.mul_comm,
                Rat.mul_inv_cancel _ hnrat]
        calc
          I.width * (I.hi + I.lo) <= I.width * 2 := hprod
          _ = 2 * I.width := by rw [Rat.mul_comm]
          _ <= 1 / ((n + 1 : Nat) : Rat) := htwo)
    (by
      intro I hI x hx n hIlo hIhi
      change QInterval.ContainsInterval (stableSquareInterval I)
        { lo := x * x, hi := x * x }
      unfold stableSquareInterval QInterval.ContainsInterval
      have hlo_nonneg : 0 <= I.lo := hI.1
      have hhi_nonneg : 0 <= I.hi := Rat.le_trans hlo_nonneg hI.2.1
      have hxl_nonneg : 0 <= x + I.lo := by grind
      have hxh_nonneg : 0 <= x + I.hi := by grind
      constructor
      · have hmul := Rat.mul_le_mul_of_nonneg_right hIlo hxl_nonneg
        grind [Rat.mul_add, Rat.add_mul]
      · have hmul := Rat.mul_le_mul_of_nonneg_right hIhi hxh_nonneg
        grind [Rat.mul_add, Rat.add_mul])

/-- A rational affine map with slope in `[0,1]` has a computable interval
modulus, witnessed by the finite schedule `n+1`. -/
def exactRat_affine_intervalRegularOn_of_unit_slope
    (r c a b : Rat) (hr0 : 0 <= r) (hr1 : r <= 1) :
    IntervalRegularOn
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b) where
  evalInterval := fun I _hI _n => affineInterval r c I
  inputPrecision := fun n => n + 1
  inputPrecision_pos := by
    intro n
    omega
  output_width := by
    intro I hI n hsmall
    unfold subintervalOf at hI
    have hwidth_nonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hscaled_nonneg : 0 <= r * I.width :=
      Rat.mul_nonneg hr0 hwidth_nonneg
    have hscaled_le : r * I.width <= I.width := by
      have hmul := Rat.mul_le_mul_of_nonneg_right hr1 hwidth_nonneg
      simpa using hmul
    have hwidth : (affineInterval r c I).width = r * I.width := by
      unfold affineInterval QInterval.width
      grind [Rat.sub_eq_add_neg, Rat.mul_add]
    rw [hwidth]
    constructor
    · exact hscaled_nonneg
    · have hbound : r * I.width <= 1 / ((n + 1 : Nat) : Rat) :=
        Rat.le_trans hscaled_le hsmall
      simpa [Rat.sub_eq_add_neg, Rat.mul_add] using hbound
  contains_point_values := by
    intro I hI x hx n hIlo hIhi
    unfold affineInterval QInterval.ContainsInterval
    change r * I.lo + c <= r * x + c ∧
      r * x + c <= r * I.hi + c
    constructor
    · grind [Rat.mul_le_mul_of_nonneg_left hIlo hr0]
    · grind [Rat.mul_le_mul_of_nonneg_left hIhi hr0]

def exactRat_affine_unitSlope (r c a b : Rat)
    (hr0 : 0 <= r) (hr1 : r <= 1) :
    IntervalRegularCandidateCertificate
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b) where
  regular := exactRat_affine_intervalRegularOn_of_unit_slope r c a b hr0 hr1
  construction := (affineMonotoneCandidateConstructionFor hr0).construction

theorem exactRat_affine_unitSlope_raw_eq_ofRat
    (r c a b : Rat) (hr0 : 0 <= r) (hr1 : r <= 1) :
    raw (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
      (exactRat_affine_unitSlope r c a b hr0 hr1) =
      RealCompute.ofRat ((b - a) * (r * (a + b) / 2 + c)) := by
  rfl

theorem exactRat_affine_unitSlope_raw_valid
    (r c a b : Rat) (hr0 : 0 <= r) (hr1 : r <= 1) :
    (raw (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
      (exactRat_affine_unitSlope r c a b hr0 hr1)).Valid := by
  exact raw_valid _ (exactRat_affine_unitSlope r c a b hr0 hr1)

/-- The interval image of an affine map, with endpoint order selected by the
sign of its slope. -/
def signedAffineInterval (r c : Rat) (I : QInterval) : QInterval :=
  if 0 <= r then
    affineInterval r c I
  else
    { lo := r * I.hi + c, hi := r * I.lo + c }

/-- Exact rational affine functions with slope in `[-1,1]` satisfy the same
computable interval-regularity contract in both monotonicity directions. -/
def exactRat_affine_intervalRegularOn_of_signed_unit_slope
    (r c a b : Rat) (hrneg : -1 <= r) (hrpos : r <= 1) :
    IntervalRegularOn
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b) where
  evalInterval := fun I _hI _n => signedAffineInterval r c I
  inputPrecision := fun n => n + 1
  inputPrecision_pos := by
    intro n
    omega
  output_width := by
    intro I hI n hsmall
    unfold subintervalOf at hI
    have hwidth_nonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    by_cases hr : 0 <= r
    · simp only [signedAffineInterval, if_pos hr]
      have hscaled_nonneg : 0 <= r * I.width :=
        Rat.mul_nonneg hr hwidth_nonneg
      have hscaled_le : r * I.width <= I.width := by
        have hmul := Rat.mul_le_mul_of_nonneg_right hrpos hwidth_nonneg
        simpa using hmul
      have hwidth : (affineInterval r c I).width = r * I.width := by
        unfold affineInterval QInterval.width
        grind [Rat.sub_eq_add_neg, Rat.mul_add]
      rw [hwidth]
      constructor
      · exact hscaled_nonneg
      · exact Rat.le_trans hscaled_le hsmall
    · simp only [signedAffineInterval, if_neg hr]
      have hminus_nonneg : 0 <= -r := by grind
      have hminus_le : -r <= 1 := by grind
      have hscaled_nonneg : 0 <= (-r) * I.width :=
        Rat.mul_nonneg hminus_nonneg hwidth_nonneg
      have hscaled_le : (-r) * I.width <= I.width := by
        have hmul := Rat.mul_le_mul_of_nonneg_right hminus_le hwidth_nonneg
        simpa using hmul
      have hwidth :
          (QInterval.mk (r * I.hi + c) (r * I.lo + c)).width =
            (-r) * I.width := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg, Rat.mul_add]
      rw [hwidth]
      constructor
      · exact hscaled_nonneg
      · exact Rat.le_trans hscaled_le hsmall
  contains_point_values := by
    intro I hI x hx n hIlo hIhi
    unfold signedAffineInterval
    by_cases hr : 0 <= r
    · simp only [if_pos hr]
      unfold affineInterval QInterval.ContainsInterval
      change r * I.lo + c <= r * x + c ∧
        r * x + c <= r * I.hi + c
      constructor <;> grind [Rat.mul_le_mul_of_nonneg_left hIlo hr,
        Rat.mul_le_mul_of_nonneg_left hIhi hr]
    · simp only [if_neg hr]
      unfold QInterval.ContainsInterval
      change r * I.hi + c <= r * x + c ∧
        r * x + c <= r * I.lo + c
      have hminus : 0 <= -r := by grind
      have hhi' := Rat.mul_le_mul_of_nonneg_left hIhi hminus
      have hlo' := Rat.mul_le_mul_of_nonneg_left hIlo hminus
      constructor <;> grind

def exactRat_affine_signed_unitSlope (r c a b : Rat)
    (hrneg : -1 <= r) (hrpos : r <= 1) :
    IntervalRegularCandidateCertificate
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b) where
  regular := exactRat_affine_intervalRegularOn_of_signed_unit_slope
    r c a b hrneg hrpos
  construction := by
    by_cases hr : 0 <= r
    · exact (affineMonotoneCandidateConstructionFor hr).construction
    · have hrle : r <= 0 := by grind
      exact (affineMonotoneCandidateConstructionFor_of_nonpos hrle).construction

theorem exactRat_affine_signed_unitSlope_raw_eq_ofRat
    (r c a b : Rat) (hrneg : -1 <= r) (hrpos : r <= 1) :
    raw (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
      (exactRat_affine_signed_unitSlope r c a b hrneg hrpos) =
      RealCompute.ofRat ((b - a) * (r * (a + b) / 2 + c)) := by
  by_cases hr : 0 <= r
  · unfold raw exactRat_affine_signed_unitSlope
    simp only [dif_pos hr]
    rfl
  · have hrle : r <= 0 := by grind
    unfold raw exactRat_affine_signed_unitSlope
    simp only [dif_neg hr]
    rfl

theorem exactRat_affine_signed_unitSlope_raw_valid
    (r c a b : Rat) (hrneg : -1 <= r) (hrpos : r <= 1) :
    (raw (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
      (exactRat_affine_signed_unitSlope r c a b hrneg hrpos)).Valid := by
  exact raw_valid _ (exactRat_affine_signed_unitSlope r c a b hrneg hrpos)

/-- The decreasing affine branch has the same endpoint-value interface as the
increasing branch.  The sign only changes the finite rectangle ordering; the
raw value remains the rational endpoint formula. -/
theorem exactRat_affine_signed_unitSlope_raw_equiv_ofRat
    (r c a b : Rat) (hrneg : -1 <= r) (hrpos : r <= 1) :
    (raw (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
      (exactRat_affine_signed_unitSlope r c a b hrneg hrpos)).Equiv
      (RealCompute.ofRat ((b - a) * (r * (a + b) / 2 + c))) := by
  rw [exactRat_affine_signed_unitSlope_raw_eq_ofRat r c a b hrneg hrpos]
  exact RealCompute.equiv_refl _ (RealCompute.ofRat_valid _)

def exactSquareInterval (I : QInterval) : QInterval :=
  { lo := I.lo * I.lo, hi := I.hi * I.hi }

private theorem two_width_le_one_div_succ_of_width_le
    {w : Rat} (n : Nat)
    (hw : w <= 1 / ((2 * (n + 1) : Nat) : Rat)) :
    2 * w <= 1 / ((n + 1 : Nat) : Rat) := by
  calc
    2 * w <= 2 * (1 / ((2 * (n + 1) : Nat) : Rat)) :=
      Rat.mul_le_mul_of_nonneg_left hw (by decide +kernel)
    _ = 1 / ((n + 1 : Nat) : Rat) := by
      rw [Rat.div_def]
      have hn : (n + 1 : Nat) ≠ 0 := by omega
      have hnrat : ((n + 1 : Nat) : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos n))
      have htwo : (2 : Rat) ≠ 0 := by decide +kernel
      rw [show ((2 * (n + 1) : Nat) : Rat) =
        (2 : Rat) * ((n + 1 : Nat) : Rat) by
          exact_mod_cast (by omega : 2 * (n + 1) = 2 * (n + 1))]
      rw [Rat.inv_mul_rev]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The exact rational square function on `[0,1]` has a finite interval
modulus.  This is the non-affine polynomial base case for the interval-regular
FTC bridge; its schedule is `2*(n+1)` because the square width is bounded by
`2*width(I)` on the unit interval. -/
def exactRat_square_intervalRegularOn_unit :
    IntervalRegularOn
      (FunctionOnInterval.exactRat (fun x => x * x) 0 1) where
  evalInterval := fun I _hI _n => exactSquareInterval I
  inputPrecision := fun n => 2 * (n + 1)
  inputPrecision_pos := by
    intro n
    omega
  output_width := by
    intro I hI n hsmall
    unfold subintervalOf at hI
    have hwidth_nonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hsum_nonneg : 0 <= I.hi + I.lo := by
      have hlo_nonneg : 0 <= I.lo := by
        have h := hI.1
        change (0 : Rat) <= I.lo at h
        exact h
      have hhi_nonneg : 0 <= I.hi := by grind
      exact Rat.add_nonneg hhi_nonneg hlo_nonneg
    have hsum_le_two : I.hi + I.lo <= 2 := by
      have hlo_nonneg : 0 <= I.lo := by
        have h := hI.1
        change (0 : Rat) <= I.lo at h
        exact h
      have hhi_le_one : I.hi <= 1 := by
        have h := hI.2.2
        change I.hi <= (1 : Rat) at h
        exact h
      grind
    have hwidth : (exactSquareInterval I).width =
        I.width * (I.hi + I.lo) := by
      unfold exactSquareInterval QInterval.width
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
    rw [hwidth]
    constructor
    · exact Rat.mul_nonneg hwidth_nonneg hsum_nonneg
    · have hprod : I.width * (I.hi + I.lo) <= I.width * 2 :=
        Rat.mul_le_mul_of_nonneg_left hsum_le_two hwidth_nonneg
      have htwo : 2 * I.width <= 1 / ((n + 1 : Nat) : Rat) :=
        two_width_le_one_div_succ_of_width_le n hsmall
      calc
        I.width * (I.hi + I.lo) <= I.width * 2 := hprod
        _ = 2 * I.width := by rw [Rat.mul_comm]
        _ <= 1 / ((n + 1 : Nat) : Rat) := htwo
  contains_point_values := by
    intro I hI x hx n hIlo hIhi
    unfold subintervalOf at hI
    unfold exactSquareInterval QInterval.ContainsInterval
    change I.lo * I.lo <= x * x ∧ x * x <= I.hi * I.hi
    have hlo_nonneg : 0 <= I.lo := by
      simpa [FunctionOnInterval.exactRat] using hI.1
    have hhi_nonneg : 0 <= I.hi := by
      have : 0 <= I.lo := hlo_nonneg
      grind
    have hxl_nonneg : 0 <= x + I.lo := by grind
    have hxh_nonneg : 0 <= x + I.hi := by grind
    constructor
    · have hmul := Rat.mul_le_mul_of_nonneg_right hIlo hxl_nonneg
      grind [Rat.mul_add, Rat.add_mul]
    · have hmul := Rat.mul_le_mul_of_nonneg_right hIhi hxh_nonneg
      grind [Rat.mul_add, Rat.add_mul]

def exactSquare_lipschitz_on_unit :
    Integral.LipschitzOnUnit (fun x : Rat => x * x) 2 := by
  constructor
  · decide +kernel
  · intro s t hs hs1 ht ht1
    have hsum_nonneg : 0 <= s + t := Rat.add_nonneg hs ht
    have hsum_le_two : s + t <= 2 := by grind
    have hfactor : s * s - t * t = (s - t) * (s + t) := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
    rw [hfactor, qabs_mul, qabs_eq_self_of_nonneg hsum_nonneg]
    have hst : qabs (s - t) = qabs (t - s) := by
      rw [show s - t = -(t - s) by grind [Rat.sub_eq_add_neg], qabs_neg]
    rw [hst]
    have hbound := Rat.mul_le_mul_of_nonneg_left hsum_le_two
      (qabs_nonneg (t - s))
    simpa [Rat.mul_comm] using hbound

def exactSquare_lipschitz_on_minusOne_one :
    Integral.LipschitzOnIntervalNat (fun x : Rat => x * x) (-1) 1 2 := by
  refine ⟨by decide +kernel, ?_⟩
  intro s t hs hsb ht htb
  have hsabs : qabs s <= 1 :=
    qabs_le_of_neg_le_le (by grind) (by grind)
  have htabs : qabs t <= 1 :=
    qabs_le_of_neg_le_le (by grind) (by grind)
  have hsum : qabs (s + t) <= 2 := by
    calc
      qabs (s + t) <= qabs s + qabs t := qabs_add_le s t
      _ <= 1 + 1 := rat_add_le_add hsabs htabs
      _ = 2 := by decide +kernel
  have hfactor : s * s - t * t = (s - t) * (s + t) := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
  rw [hfactor, qabs_mul]
  have hst : qabs (s - t) = qabs (t - s) := by
    rw [show s - t = -(t - s) by grind [Rat.sub_eq_add_neg], qabs_neg]
  rw [hst]
  have hbound := Rat.mul_le_mul_of_nonneg_left hsum
    (qabs_nonneg (t - s))
  simpa [Rat.mul_comm] using hbound

def exactRat_square_intervalRegularOn_minusOne_one :
    IntervalRegularOn
      (FunctionOnInterval.exactRat (fun x : Rat => x * x) (-1) 1) :=
  IntervalRegularOn.of_lipschitzOnIntervalNat (fun x : Rat => x * x)
    (-1) 1 2 exactSquare_lipschitz_on_minusOne_one

def exactRat_square_integral_certificate :
    Integral.IntervalRegularCandidateCertificate
      (FunctionOnInterval.exactRat (fun x : Rat => x * x) 0 1) where
  regular := exactRat_square_intervalRegularOn_unit
  construction :=
    IntegralIdentities.LipschitzDyadic.construction (fun x : Rat => x * x) 2
      exactSquare_lipschitz_on_unit

theorem exactRat_square_integral_raw_valid :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x * x) 0 1)
      exactRat_square_integral_certificate).Valid := by
  exact Integral.raw_valid _ exactRat_square_integral_certificate

def stableSquare_integral_certificate :
    Integral.IntervalRegularCandidateCertificate stableSquareFunction where
  regular := stableSquare_intervalRegularOn_unit
  construction :=
    { compute := IntegralIdentities.LipschitzDyadic.compute
        (fun x : Rat => x * x) 2
      certificate := IntegralIdentities.LipschitzDyadic.raw_valid
        exactSquare_lipschitz_on_unit }

theorem stableSquare_integral_raw_valid :
    (Integral.raw stableSquareFunction stableSquare_integral_certificate).Valid := by
  exact Integral.raw_valid _ stableSquare_integral_certificate

theorem exactSquare_uniformLeftSum_eq
    {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x * x) n =
      Series.squareSum n / (n : Rat) ^ 3 := by
  have hnrat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have haux : forall k : Nat,
      (List.range k).foldl
          (fun total (j : Nat) =>
            total + (1 / (n : Rat)) *
              (((j : Rat) / (n : Rat)) * ((j : Rat) / (n : Rat)))) 0 =
        Series.squareSum k / (n : Rat) ^ 3 := by
    intro k
    induction k with
    | zero =>
        simp [Series.squareSum, Rat.div_def]
    | succ k ih =>
        rw [List.range_succ, List.foldl_append]
        simp [List.foldl]
        rw [ih, Series.squareSum_succ]
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
          Rat.add_mul, Rat.pow_succ, Rat.mul_inv_cancel]
  unfold IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
  exact haux n

theorem exactSquare_uniformRightSum_eq
    {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x * x) n =
      Series.squareSum (n + 1) / (n : Rat) ^ 3 := by
  have hnrat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have hfrac (a b : Rat) :
      a / (n : Rat) ^ 3 + b / (n : Rat) ^ 3 =
        (a + b) / (n : Rat) ^ 3 := by
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm,
      Rat.pow_succ, Rat.mul_inv_cancel]
  have haux : forall k : Nat,
      (List.range k).foldl
          (fun total (j : Nat) =>
            total + (1 / (n : Rat)) *
              (((j + 1 : Nat) : Rat) / (n : Rat) *
                (((j + 1 : Nat) : Rat) / (n : Rat)))) 0 =
        Series.squareSum (k + 1) / (n : Rat) ^ 3 := by
    intro k
    induction k with
    | zero =>
        simp [Series.squareSum, Rat.div_def]
        grind
    | succ k ih =>
        simp at ih ⊢
        rw [List.range_succ, List.foldl_append]
        simp [List.foldl]
        rw [ih]
        have hterm :
            (1 / (n : Rat)) *
                (((k : Rat) + 1) / (n : Rat) *
                  (((k : Rat) + 1) / (n : Rat))) =
              ((k : Rat) + 1) ^ 2 / (n : Rat) ^ 3 := by
          rw [Rat.div_def, Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ,
            Rat.mul_inv_cancel]
        rw [hterm]
        have hs : Series.squareSum (k + 1 + 1) =
            Series.squareSum (k + 1) + ((k + 1 : Nat) : Rat) ^ 2 := by
          rw [show k + 1 + 1 = (k + 1) + 1 by omega,
            Series.squareSum_succ]
        rw [hs]
        simpa [Rat.natCast_add] using hfrac _ _
  unfold IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
  exact haux n

theorem exactSquare_uniformLeftSum_le_one_third
    {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x * x) n <= 1 / 3 := by
  rw [exactSquare_uniformLeftSum_eq hn, Series.squareSum_eq]
  have hnrat : 0 < (n : Rat) := (Rat.natCast_pos).2 hn
  have hden : 0 < (n : Rat) ^ 3 := Rat.pow_pos hnrat
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat) ^ 3)
  · rw [Rat.div_def, Rat.div_def]
    have hpoly : (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1)
        <= 2 * (n : Rat) ^ 3 := by
      have hn1 : 1 <= (n : Rat) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0))
      have hnonneg : 0 <= (n : Rat) * (3 * (n : Rat) - 1) := by
        exact Rat.mul_nonneg (Rat.le_of_lt hnrat) (by grind)
      have hid : 2 * (n : Rat) ^ 3 -
          (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) =
          (n : Rat) * (3 * (n : Rat) - 1) := by
            grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
              Rat.add_mul, Rat.sub_eq_add_neg]
      grind
    have hscaled := Rat.mul_le_mul_of_nonneg_right hpoly
      (Rat.le_of_lt ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 6)))
    have hcancel : ((n : Rat) ^ 3)⁻¹ * (n : Rat) ^ 3 = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt hden)
    calc
      (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) *
          6⁻¹ * ((n : Rat) ^ 3)⁻¹ * (n : Rat) ^ 3 =
          (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) * 6⁻¹ := by
            calc
              _ = ((n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) * 6⁻¹) *
                  (((n : Rat) ^ 3)⁻¹ * (n : Rat) ^ 3) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
              _ = _ := by rw [hcancel, Rat.mul_one]
      _ <= 2 * (n : Rat) ^ 3 * 6⁻¹ := hscaled
      _ = 1 / 3 * (n : Rat) ^ 3 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact hden

theorem exactSquare_uniformRightSum_ge_one_third
    {n : Nat} (hn : 0 < n) :
    1 / 3 <=
      IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x * x) n := by
  rw [exactSquare_uniformRightSum_eq hn, Series.squareSum_eq]
  have hnrat : 0 < (n : Rat) := (Rat.natCast_pos).2 hn
  have hden : 0 < (n : Rat) ^ 3 := Rat.pow_pos hnrat
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat) ^ 3)
  · rw [Rat.div_def, Rat.div_def]
    have hnp1 : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by
      simp [Rat.natCast_add]
    rw [hnp1]
    have hminus : (n : Rat) + 1 - 1 = (n : Rat) := by grind
    rw [hminus]
    have htwo : 2 * ((n : Rat) + 1) - 1 = 2 * (n : Rat) + 1 := by grind
    rw [htwo]
    rw [Rat.div_def]
    have hpoly : 2 * (n : Rat) ^ 3
        <= (n : Rat) * ((n : Rat) + 1) * (2 * (n : Rat) + 1) := by
      have hnonneg : 0 <= (n : Rat) * (3 * (n : Rat) + 1) := by
        exact Rat.mul_nonneg (Rat.le_of_lt hnrat) (by grind)
      have hid : (n : Rat) * ((n : Rat) + 1) * (2 * (n : Rat) + 1) -
          2 * (n : Rat) ^ 3 = (n : Rat) * (3 * (n : Rat) + 1) := by
            grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
              Rat.add_mul]
      grind
    have hscaled := Rat.mul_le_mul_of_nonneg_right hpoly
      (Rat.le_of_lt ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 6)))
    have hscaled' : 2 * (n : Rat) ^ 3 * 6⁻¹ <=
        ((n : Rat) + 1) * (n : Rat) * (2 * (n : Rat) + 1) * 6⁻¹ := by
      grind [Rat.mul_assoc, Rat.mul_comm]
    have hcancel : ((n : Rat) ^ 3)⁻¹ * (n : Rat) ^ 3 = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt hden)
    calc
      1 / 3 * (n : Rat) ^ 3 = 2 * (n : Rat) ^ 3 * 6⁻¹ := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= ((n : Rat) + 1) * (n : Rat) * (2 * (n : Rat) + 1) * 6⁻¹ := hscaled'
      _ = ((n : Rat) + 1) * (n : Rat) * (2 * (n : Rat) + 1) *
          6⁻¹ * ((n : Rat) ^ 3)⁻¹ * (n : Rat) ^ 3 := by
        calc
          _ = (((n : Rat) + 1) * (n : Rat) * (2 * (n : Rat) + 1) * 6⁻¹) *
              (((n : Rat) ^ 3)⁻¹ * (n : Rat) ^ 3) := by
            grind [Rat.mul_assoc, Rat.mul_comm]
          _ = _ := by
            symm
            calc
              _ = (((n : Rat) + 1) * (n : Rat) * (2 * (n : Rat) + 1) * 6⁻¹) *
                  (((n : Rat) ^ 3)⁻¹ * (n : Rat) ^ 3) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
              _ = _ := by rw [hcancel, Rat.mul_one]
  · exact hden

theorem exactSquare_compute_contains_one_third (stage : Nat) :
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x * x) 2 stage).ContainsInterval
      { lo := 1 / 3, hi := 1 / 3 } := by
  let n : Nat := 2 ^ stage
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.pow_pos (by omega : 0 < 2)
  have hl := IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum
    exactSquare_lipschitz_on_unit stage
  have hr := IntegralIdentities.LipschitzDyadic.compute_contains_uniformRightEndpointSum
    exactSquare_lipschitz_on_unit stage
  have hleft := exactSquare_uniformLeftSum_le_one_third hn
  have hright := exactSquare_uniformRightSum_ge_one_third hn
  unfold QInterval.ContainsInterval
  constructor
  · exact Rat.le_trans hl.1 hleft
  · exact Rat.le_trans hright hr.2

theorem exactRat_square_integral_raw_equiv_one_third :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x * x) 0 1)
      exactRat_square_integral_certificate).Equiv
      (RealCompute.ofRat (1 / 3)) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x * x) 2 n)
    { lo := 1 / 3, hi := 1 / 3 }
  unfold QInterval.Overlaps
  exact exactSquare_compute_contains_one_third n

theorem stableSquare_integral_raw_equiv_one_third :
    (Integral.raw stableSquareFunction stableSquare_integral_certificate).Equiv
      (RealCompute.ofRat (1 / 3)) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x * x) 2 n)
    { lo := 1 / 3, hi := 1 / 3 }
  unfold QInterval.Overlaps
  exact exactSquare_compute_contains_one_third n

def exactCubeInterval (I : QInterval) : QInterval :=
  { lo := I.lo ^ 3, hi := I.hi ^ 3 }

private theorem three_width_le_one_div_succ_of_width_le
    {w : Rat} (n : Nat)
    (hw : w <= 1 / ((3 * (n + 1) : Nat) : Rat)) :
    3 * w <= 1 / ((n + 1 : Nat) : Rat) := by
  calc
    3 * w <= 3 * (1 / ((3 * (n + 1) : Nat) : Rat)) :=
      Rat.mul_le_mul_of_nonneg_left hw (by decide +kernel)
    _ = 1 / ((n + 1 : Nat) : Rat) := by
      rw [Rat.div_def]
      have hnrat : ((n + 1 : Nat) : Rat) ≠ 0 :=
        Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos n))
      rw [show ((3 * (n + 1) : Nat) : Rat) =
        (3 : Rat) * ((n + 1 : Nat) : Rat) by
          exact_mod_cast (by omega : 3 * (n + 1) = 3 * (n + 1))]
      rw [Rat.inv_mul_rev]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

def exactRat_cube_intervalRegularOn_unit :
    IntervalRegularOn
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 3) 0 1) where
  evalInterval := fun I _hI _n => exactCubeInterval I
  inputPrecision := fun n => 3 * (n + 1)
  inputPrecision_pos := by
    intro n
    omega
  output_width := by
    intro I hI n hsmall
    unfold subintervalOf at hI
    have hwidth_nonneg : 0 <= I.width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hlo_nonneg : 0 <= I.lo := by
      have h := hI.1
      change (0 : Rat) <= I.lo at h
      exact h
    have hhi_le_one : I.hi <= 1 := by
      have h := hI.2.2
      change I.hi <= (1 : Rat) at h
      exact h
    have hwidth : (exactCubeInterval I).width =
        I.width * (I.hi ^ 2 + I.hi * I.lo + I.lo ^ 2) := by
      unfold exactCubeInterval QInterval.width
      grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul]
    rw [hwidth]
    constructor
    · have hsum_nonneg : 0 <= I.hi ^ 2 + I.hi * I.lo + I.lo ^ 2 := by
        exact Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg (by grind))
          (Rat.mul_nonneg (by grind) hlo_nonneg)) (Rat.pow_nonneg hlo_nonneg)
      exact Rat.mul_nonneg hwidth_nonneg hsum_nonneg
    · have hhi_nonneg : 0 <= I.hi := by grind
      have hterm1 : I.hi ^ 2 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left hhi_le_one (by grind : 0 <= I.hi)
        exact Rat.le_trans (by simpa [Rat.pow_succ] using h) hhi_le_one
      have hterm2 : I.hi * I.lo <= 1 := by
        exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hhi_le_one hlo_nonneg)
          (by grind)
      have hterm3 : I.lo ^ 2 <= 1 := by
        have hlo_le_one : I.lo <= 1 := by grind
        have h := Rat.mul_le_mul_of_nonneg_left hlo_le_one hlo_nonneg
        exact Rat.le_trans (by simpa [Rat.pow_succ] using h) hlo_le_one
      have hsum_le_three : I.hi ^ 2 + I.hi * I.lo + I.lo ^ 2 <= 3 := by grind
      have hprod := Rat.mul_le_mul_of_nonneg_left hsum_le_three hwidth_nonneg
      calc
        I.width * (I.hi ^ 2 + I.hi * I.lo + I.lo ^ 2) <= I.width * 3 := hprod
        _ = 3 * I.width := by rw [Rat.mul_comm]
        _ <= 1 / ((n + 1 : Nat) : Rat) :=
          three_width_le_one_div_succ_of_width_le n hsmall
  contains_point_values := by
    intro I hI x hx n hIlo hIhi
    unfold subintervalOf at hI
    unfold exactCubeInterval QInterval.ContainsInterval
    change I.lo ^ 3 <= x ^ 3 ∧ x ^ 3 <= I.hi ^ 3
    have hx' : 0 <= x ∧ x <= 1 := by
      simpa [FunctionOnInterval.exactRat, inDomainInterval] using hx
    have hx_nonneg : 0 <= x := hx'.1
    have hlo_nonneg : 0 <= I.lo := by
      have h := hI.1
      change (0 : Rat) <= I.lo at h
      exact h
    have hhi_nonneg : 0 <= I.hi := by grind
    have hsum_lo : 0 <= x ^ 2 + x * I.lo + I.lo ^ 2 := by
      exact Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg hx_nonneg)
        (Rat.mul_nonneg hx_nonneg hlo_nonneg)) (Rat.pow_nonneg hlo_nonneg)
    have hsum_hi : 0 <= I.hi ^ 2 + I.hi * x + x ^ 2 := by
      exact Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg hhi_nonneg)
        (Rat.mul_nonneg hhi_nonneg hx_nonneg)) (Rat.pow_nonneg hx_nonneg)
    have hlow : 0 <= (x - I.lo) *
        (x ^ 2 + x * I.lo + I.lo ^ 2) := by
      exact Rat.mul_nonneg (by grind) hsum_lo
    have hhigh : 0 <= (I.hi - x) *
        (I.hi ^ 2 + I.hi * x + x ^ 2) := by
      exact Rat.mul_nonneg (by grind) hsum_hi
    constructor <;> grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul,
      Rat.sub_eq_add_neg]

def stableCube : StablePartialRealFunRaw where
  definedAt := fun x => 0 <= x ∧ x <= 1
  compute := fun x _ => { lo := x ^ 3, hi := x ^ 3 }
  rate := fun _ => .unknown

def stableCubeFunction : FunctionOnInterval :=
  FunctionOnInterval.ofStable stableCube 0 1
    (fun _ hx => hx)
    (fun x _ => RealCompute.ofRat_valid (x ^ 3))

def stableCube_intervalRegularOn_unit :
    IntervalRegularOn stableCubeFunction :=
  IntervalRegularOn.ofStable stableCube 0 1
    (fun _ hx => hx)
    (fun x _ => RealCompute.ofRat_valid (x ^ 3))
    (fun I _hI _n => exactCubeInterval I)
    (fun n => 3 * (n + 1))
    (by intro n; omega)
    (by
      intro I hI n hsmall
      have hwidth_nonneg : 0 <= I.width := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg, hI.2.1]
      have hlo_nonneg : 0 <= I.lo := hI.1
      have hhi_nonneg : 0 <= I.hi := Rat.le_trans hlo_nonneg hI.2.1
      have hwidth : (exactCubeInterval I).width =
          I.width * (I.hi ^ 2 + I.hi * I.lo + I.lo ^ 2) := by
        unfold exactCubeInterval QInterval.width
        grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul]
      rw [hwidth]
      constructor
      · exact Rat.mul_nonneg hwidth_nonneg (by
          exact Rat.add_nonneg
            (Rat.add_nonneg (Rat.pow_nonneg hhi_nonneg)
              (Rat.mul_nonneg hhi_nonneg hlo_nonneg))
            (Rat.pow_nonneg hlo_nonneg))
      · have hhi_le_one : I.hi <= 1 := hI.2.2
        have hlo_le_one : I.lo <= 1 := Rat.le_trans hI.2.1 hhi_le_one
        have hhi_sq : I.hi ^ 2 <= 1 := by
          have h := Rat.mul_le_mul_of_nonneg_left hhi_le_one hhi_nonneg
          exact Rat.le_trans (by simpa [Rat.pow_succ] using h) hhi_le_one
        have hcross : I.hi * I.lo <= 1 := by
          exact Rat.le_trans
            (Rat.mul_le_mul_of_nonneg_right hhi_le_one hlo_nonneg)
            (by grind)
        have hlo_sq : I.lo ^ 2 <= 1 := by
          have h := Rat.mul_le_mul_of_nonneg_left hlo_le_one hlo_nonneg
          exact Rat.le_trans (by simpa [Rat.pow_succ] using h) hlo_le_one
        have hsum_le_three :
            I.hi ^ 2 + I.hi * I.lo + I.lo ^ 2 <= 3 := by grind
        have hprod := Rat.mul_le_mul_of_nonneg_left hsum_le_three hwidth_nonneg
        calc
          I.width * (I.hi ^ 2 + I.hi * I.lo + I.lo ^ 2) <= I.width * 3 := hprod
          _ = 3 * I.width := by rw [Rat.mul_comm]
          _ <= 1 / ((n + 1 : Nat) : Rat) :=
            three_width_le_one_div_succ_of_width_le n hsmall)
    (by
      intro I hI x hx n hIlo hIhi
      change QInterval.ContainsInterval (exactCubeInterval I)
        { lo := x ^ 3, hi := x ^ 3 }
      unfold exactCubeInterval QInterval.ContainsInterval
      have hlo_nonneg : 0 <= I.lo := hI.1
      have hhi_nonneg : 0 <= I.hi := Rat.le_trans hlo_nonneg hI.2.1
      have hx_nonneg : 0 <= x := hx.1
      have hsum_lo : 0 <= x ^ 2 + x * I.lo + I.lo ^ 2 := by
        exact Rat.add_nonneg
          (Rat.add_nonneg (Rat.pow_nonneg hx_nonneg)
            (Rat.mul_nonneg hx_nonneg hlo_nonneg))
          (Rat.pow_nonneg hlo_nonneg)
      have hsum_hi : 0 <= I.hi ^ 2 + I.hi * x + x ^ 2 := by
        exact Rat.add_nonneg
          (Rat.add_nonneg (Rat.pow_nonneg hhi_nonneg)
            (Rat.mul_nonneg hhi_nonneg hx_nonneg))
          (Rat.pow_nonneg hx_nonneg)
      have hlow : 0 <= (x - I.lo) *
          (x ^ 2 + x * I.lo + I.lo ^ 2) := by
        exact Rat.mul_nonneg (by grind) hsum_lo
      have hhigh : 0 <= (I.hi - x) *
          (I.hi ^ 2 + I.hi * x + x ^ 2) := by
        exact Rat.mul_nonneg (by grind) hsum_hi
      constructor <;> grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul,
        Rat.sub_eq_add_neg])

def exactCube_lipschitz_on_unit :
    Integral.LipschitzOnUnit (fun x : Rat => x ^ 3) 3 := by
  constructor
  · decide +kernel
  · intro s t hs hs1 ht ht1
    have hsum_nonneg : 0 <= s ^ 2 + s * t + t ^ 2 := by
      exact Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg (by grind))
        (Rat.mul_nonneg (by grind) (by grind))) (Rat.pow_nonneg (by grind))
    have hsum_le_three : s ^ 2 + s * t + t ^ 2 <= 3 := by
      have hs0 : 0 <= s := by grind
      have ht0 : 0 <= t := by grind
      have hs2 : s ^ 2 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left hs1 (by grind : 0 <= s)
        exact Rat.le_trans (by simpa [Rat.pow_succ] using h) hs1
      have ht2 : t ^ 2 <= 1 := by
        have h := Rat.mul_le_mul_of_nonneg_left ht1 (by grind : 0 <= t)
        exact Rat.le_trans (by simpa [Rat.pow_succ] using h) ht1
      have hst : s * t <= 1 := by
        exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hs1 ht0) (by grind)
      grind
    have hfactor : s ^ 3 - t ^ 3 = (s - t) * (s ^ 2 + s * t + t ^ 2) := by
      grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul]
    rw [hfactor, qabs_mul]
    have hbound := Rat.mul_le_mul_of_nonneg_left hsum_le_three
      (qabs_nonneg (s - t))
    calc
      qabs (s - t) * qabs (s ^ 2 + s * t + t ^ 2) <=
          qabs (s - t) * 3 :=
        Rat.mul_le_mul_of_nonneg_left
          (by simpa [qabs_eq_self_of_nonneg hsum_nonneg] using hsum_le_three)
          (qabs_nonneg _)
      _ = 3 * qabs (t - s) := by
        rw [show qabs (s - t) = qabs (t - s) by
          rw [show s - t = -(t - s) by grind [Rat.sub_eq_add_neg], qabs_neg]]
        grind [Rat.mul_comm]

def exactCube_lipschitz_on_minusOne_one :
    Integral.LipschitzOnIntervalNat (fun x : Rat => x ^ 3) (-1) 1 3 := by
  refine ⟨by decide +kernel, ?_⟩
  intro s t hs hsb ht htb
  have hsabs : qabs s <= 1 :=
    qabs_le_of_neg_le_le (by grind) (by grind)
  have htabs : qabs t <= 1 :=
    qabs_le_of_neg_le_le (by grind) (by grind)
  have hs2 : qabs (s ^ 2) <= 1 := by
    rw [RationalMajorant.qabs_pow_eq_pow_qabs]
    calc
      qabs s ^ 2 = qabs s * qabs s := by simpa [Rat.pow_succ]
      _ <= 1 * qabs s :=
        Rat.mul_le_mul_of_nonneg_right hsabs (qabs_nonneg s)
      _ <= 1 * 1 :=
        Rat.mul_le_mul_of_nonneg_left hsabs (by decide +kernel)
      _ = 1 := by decide +kernel
  have ht2 : qabs (t ^ 2) <= 1 := by
    rw [RationalMajorant.qabs_pow_eq_pow_qabs]
    calc
      qabs t ^ 2 = qabs t * qabs t := by simpa [Rat.pow_succ]
      _ <= 1 * qabs t :=
        Rat.mul_le_mul_of_nonneg_right htabs (qabs_nonneg t)
      _ <= 1 * 1 :=
        Rat.mul_le_mul_of_nonneg_left htabs (by decide +kernel)
      _ = 1 := by decide +kernel
  have hst : qabs (s * t) <= 1 := by
    rw [qabs_mul]
    calc
      qabs s * qabs t <= 1 * qabs t :=
        Rat.mul_le_mul_of_nonneg_right hsabs (qabs_nonneg t)
      _ <= 1 * 1 :=
        Rat.mul_le_mul_of_nonneg_left htabs (by decide +kernel)
      _ = 1 := by decide +kernel
  have hsum : qabs (s ^ 2 + s * t + t ^ 2) <= 3 := by
    calc
      qabs (s ^ 2 + s * t + t ^ 2) <=
          qabs (s ^ 2 + s * t) + qabs (t ^ 2) :=
        qabs_add_le (s ^ 2 + s * t) (t ^ 2)
      _ <= (qabs (s ^ 2) + qabs (s * t)) + qabs (t ^ 2) := by
        grind [qabs_add_le]
      _ <= (1 + 1) + 1 := by grind
      _ = 3 := by decide +kernel
  have hfactor : s ^ 3 - t ^ 3 =
      (s - t) * (s ^ 2 + s * t + t ^ 2) := by
    grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul]
  rw [hfactor, qabs_mul]
  calc
    qabs (s - t) * qabs (s ^ 2 + s * t + t ^ 2) <=
        qabs (s - t) * 3 :=
      Rat.mul_le_mul_of_nonneg_left hsum (qabs_nonneg _)
    _ = 3 * qabs (t - s) := by
      rw [show qabs (s - t) = qabs (t - s) by
        rw [show s - t = -(t - s) by grind [Rat.sub_eq_add_neg], qabs_neg]]
      grind [Rat.mul_comm]

def exactRat_cube_intervalRegularOn_minusOne_one :
    IntervalRegularOn
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 3) (-1) 1) :=
  IntervalRegularOn.of_lipschitzOnIntervalNat (fun x : Rat => x ^ 3)
    (-1) 1 3 exactCube_lipschitz_on_minusOne_one

/-! The cubic certificate is the first visible member of a uniform monomial
family.  On `[-1,1]`, the finite power-difference estimate gives the natural
Lipschitz constant `n` for `x^n`, including the constant case `n = 0`. -/

def exactPow_lipschitz_on_minusOne_one (n : Nat) :
    Integral.LipschitzOnIntervalNat (fun x : Rat => x ^ n) (-1) 1 n := by
  refine ⟨by decide +kernel, ?_⟩
  intro s t hs hsb ht htb
  have hsabs : qabs s <= 1 :=
    qabs_le_of_neg_le_le (by grind) (by grind)
  have htabs : qabs t <= 1 :=
    qabs_le_of_neg_le_le (by grind) (by grind)
  have hone : (1 : Rat) ^ n = 1 := by
    induction n with
    | zero => rw [Rat.pow_zero]
    | succ n ih => rw [Rat.pow_succ, ih]; decide +kernel
  have hpow := RationalMajorant.qabs_pow_sub_le_lipschitz
    (x := s) (y := t) (B := (1 : Rat))
    (by decide +kernel) (by decide +kernel) hsabs htabs n
  calc
    qabs (s ^ n - t ^ n) <=
        qabs (s - t) * (n : Rat) * (1 : Rat) ^ n := hpow
    _ = (n : Rat) * qabs (t - s) := by
      rw [show qabs (s - t) = qabs (t - s) by
        rw [show s - t = -(t - s) by grind [Rat.sub_eq_add_neg], qabs_neg]]
      rw [hone]
      grind [Rat.mul_comm, Rat.mul_assoc]

def exactRat_pow_intervalRegularOn_minusOne_one (n : Nat) :
    IntervalRegularOn
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ n) (-1) 1) :=
  IntervalRegularOn.of_lipschitzOnIntervalNat (fun x : Rat => x ^ n)
    (-1) 1 n (exactPow_lipschitz_on_minusOne_one n)

def exactPow_lipschitz_on_unit (n : Nat) :
    Integral.LipschitzOnUnit (fun x : Rat => x ^ n) (n : Rat) := by
  refine ⟨by exact_mod_cast Nat.zero_le n, ?_⟩
  intro s t hs hsb ht htb
  exact (exactPow_lipschitz_on_minusOne_one n).2 s t
    (by grind) (by grind) (by grind) (by grind)

def exactRat_pow_intervalRegularOn_unit (n : Nat) :
    IntervalRegularOn
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ n) 0 1) :=
  IntervalRegularOn.of_lipschitzOnIntervalNat (fun x : Rat => x ^ n)
    0 1 n
    (Integral.LipschitzOnIntervalNat.of_unit_subinterval
      (fun x : Rat => x ^ n) n (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (exactPow_lipschitz_on_unit n))

theorem exactRat_pow_nondecreasingDarbouxStage_stage_independent
    (power : Nat) (P : RationalPartition 0 1) (n m : Nat) :
    Integral.nondecreasingDarbouxStage
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ power) 0 1) P n =
      Integral.nondecreasingDarbouxStage
        (FunctionOnInterval.exactRat (fun x : Rat => x ^ power) 0 1) P m := by
  rfl

def exactRat_pow_integral_certificate (n : Nat) :
    Integral.IntervalRegularCandidateCertificate
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ n) 0 1) where
  regular := exactRat_pow_intervalRegularOn_unit n
  construction := IntegralIdentities.LipschitzDyadic.construction
    (fun x : Rat => x ^ n) n (exactPow_lipschitz_on_unit n)

private theorem uniformLeftEndpointSum_const_one_of_pos {n : Nat}
    (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun _ : Rat => 1) n = 1 := by
  have hnrat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have haux : forall k : Nat,
      (List.range k).foldl
          (fun total (j : Nat) =>
            total + (1 / (n : Rat)) * (1 : Rat)) 0 =
        (k : Rat) / (n : Rat) := by
    intro k
    induction k with
    | zero => simp [Rat.div_def]
    | succ k ih =>
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ih]
        simp [Rat.div_def, Rat.natCast_add]
        grind [Rat.add_mul, Rat.mul_comm]
  unfold IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
  rw [haux n]
  rw [Rat.div_def, Rat.mul_inv_cancel _ hnrat]

theorem exactRat_zero_integral_raw_equiv_one :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 0) 0 1)
      (exactRat_pow_integral_certificate 0)).Equiv
      (RealCompute.ofRat 1) := by
  apply RealCompute.sameStageOverlap_equiv
  intro stage
  apply (RealCompute.compareAt_overlap_iff _ _ stage stage).2
  have hconst : Integral.LipschitzOnUnit (fun _ : Rat => 1) 0 := by
    refine ⟨by decide +kernel, ?_⟩
    intro s t hs hsb ht htb
    simp <;> decide +kernel
  have hcontains :=
    IntegralIdentities.LipschitzDyadic.compute_contains_leftEndpointSum
      (f := fun _ : Rat => 1) (L := 0) hconst stage
  have huniform :=
    IntegralIdentities.LipschitzDyadic.dyadicLeftEndpointSum_eq_uniform
      (fun _ : Rat => 1) stage
  have hn : 0 < 2 ^ stage := Nat.pow_pos (by omega : 0 < 2)
  have hsum :
      IntegralIdentities.LipschitzDyadic.leftEndpointSum (fun _ : Rat => 1)
          (ArctanGeometry.arctanAreaLoopState 1 stage).intervals = 1 := by
    rw [huniform]
    exact uniformLeftEndpointSum_const_one_of_pos hn
  unfold Integral.raw Integral.candidateValueFor exactRat_pow_integral_certificate
  change QInterval.Overlaps
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x ^ 0) 0 stage)
    { lo := 1, hi := 1 }
  have hcompute :
      IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x ^ 0) 0 stage =
        IntegralIdentities.LipschitzDyadic.compute (fun _ : Rat => 1) 0 stage := by
    congr 1
    funext x
    simp
  rw [hcompute]
  unfold QInterval.Overlaps
  rw [hsum] at hcontains
  exact hcontains

theorem exactRat_one_integral_raw_equiv_half :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 1) 0 1)
      (exactRat_pow_integral_certificate 1)).Equiv
      (RealCompute.ofRat (1 / 2)) := by
  apply RealCompute.sameStageOverlap_equiv
  intro stage
  apply (RealCompute.compareAt_overlap_iff _ _ stage stage).2
  unfold Integral.raw Integral.candidateValueFor exactRat_pow_integral_certificate
  change QInterval.Overlaps
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x ^ 1) 1 stage)
    { lo := 1 / 2, hi := 1 / 2 }
  have hn : 0 < 2 ^ stage := Nat.pow_pos (by omega : 0 < 2)
  have hleft :=
    IntegralIdentities.LipschitzDyadic.compute_contains_leftEndpointSum
      (f := fun x : Rat => x) (L := 1)
      (IntegralIdentities.affineIdentity_lipschitz_on_unit) stage
  have hright :=
    IntegralIdentities.LipschitzDyadic.compute_contains_rightEndpointSum
      (f := fun x : Rat => x) (L := 1)
      (IntegralIdentities.affineIdentity_lipschitz_on_unit) stage
  have hleftTransport :=
    IntegralIdentities.LipschitzDyadic.dyadicLeftEndpointSum_eq_uniform
      (fun x : Rat => x) stage
  have hrightTransport :=
    IntegralIdentities.LipschitzDyadic.dyadicRightEndpointSum_eq_uniform
      (fun x : Rat => x) stage
  have hleftValue :=
    IntegralIdentities.affineIdentity_uniformLeftEndpointSum_eq hn
  have hrightValue :=
    IntegralIdentities.affineIdentity_uniformRightEndpointSum_eq hn
  have hleft_le :
      IntegralIdentities.LipschitzDyadic.leftEndpointSum (fun x : Rat => x)
          (ArctanGeometry.arctanAreaLoopState 1 stage).intervals <= 1 / 2 := by
    rw [hleftTransport, hleftValue]
    have hpow : (0 : Rat) < (2 ^ stage : Nat) := by
      exact_mod_cast hn
    have hden : (0 : Rat) < 2 * (2 ^ stage : Nat) := by
      grind
    have hden0 : (2 * (2 ^ stage : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hden
    have hinv : (0 : Rat) < ((2 * (2 ^ stage : Nat) : Rat))⁻¹ :=
      (Rat.inv_pos).2 hden
    rw [Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.mul_inv_cancel _ hden0]
  have hright_ge :
      1 / 2 <=
        IntegralIdentities.LipschitzDyadic.rightEndpointSum (fun x : Rat => x)
          (ArctanGeometry.arctanAreaLoopState 1 stage).intervals := by
    rw [hrightTransport, hrightValue]
    have hpow : (0 : Rat) < (2 ^ stage : Nat) := by
      exact_mod_cast hn
    have hden : (0 : Rat) < 2 * (2 ^ stage : Nat) := by
      grind
    have hden0 : (2 * (2 ^ stage : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hden
    have hinv : (0 : Rat) < ((2 * (2 ^ stage : Nat) : Rat))⁻¹ :=
      (Rat.inv_pos).2 hden
    rw [Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.mul_inv_cancel _ hden0]
  have hcompute :
      IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x ^ 1) 1 stage =
        IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x) 1 stage := by
    congr 1
    funext x
    rw [Rat.pow_one]
  rw [hcompute]
  unfold QInterval.Overlaps
  exact ⟨Rat.le_trans hleft.1 hleft_le, Rat.le_trans hright_ge hright.2⟩

theorem exactRat_pow_integral_raw_valid (n : Nat) :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ n) 0 1)
      (exactRat_pow_integral_certificate n)).Valid := by
  exact Integral.raw_valid _ (exactRat_pow_integral_certificate n)

theorem exactRat_pow_nondecreasing_on_unit (n : Nat) :
    NondecreasingOnInterval
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ n) 0 1) := by
  intro x y hx hy hxy _stage
  change 0 <= x ∧ x <= 1 at hx
  change 0 <= y ∧ y <= 1 at hy
  change x ^ n <= y ^ n
  have hpow : forall j : Nat, x ^ j <= y ^ j := by
    intro j
    induction j with
    | zero => rw [Rat.pow_zero, Rat.pow_zero]; decide +kernel
    | succ j ih =>
        rw [Rat.pow_succ, Rat.pow_succ]
        calc
          x ^ j * x <= y ^ j * x :=
            Rat.mul_le_mul_of_nonneg_right ih hx.1
          _ <= y ^ j * y :=
            Rat.mul_le_mul_of_nonneg_left hxy (Rat.pow_nonneg hy.1)
  exact hpow n

def exactRat_pow_monotoneCandidateConstructionFor (n : Nat) :
    MonotoneCandidateConstructionFor
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ n) 0 1) where
  monotone := MonotoneOnInterval.ofNondecreasing
    (exactRat_pow_nondecreasing_on_unit n)
  construction := (exactRat_pow_integral_certificate n).construction

theorem exactRat_pow_monotoneCandidateValueFor_valid (n : Nat) :
    (monotoneCandidateValueFor
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ n) 0 1)
      (exactRat_pow_monotoneCandidateConstructionFor n)).Valid := by
  exact monotoneCandidateValueFor_valid _ _

theorem exactRat_pow_monotoneCandidateValueFor_eq_dyadicRaw (n : Nat) :
    monotoneCandidateValueFor
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ n) 0 1)
      (exactRat_pow_monotoneCandidateConstructionFor n) =
    Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ n) 0 1)
      (exactRat_pow_integral_certificate n) := by
  rfl

/-! The normalized monomial primitive is also available as one generic
endpoint-difference object.  Its adjacent-interval law is purely finite
subtraction, so it does not depend on an integral construction or on a
completed real line. -/

def monomialPrimitiveRaw (n : Nat) : RealFunRaw :=
  RealFunRaw.exact
    (fun x : Rat => x ^ (n + 1) / ((n + 1 : Nat) : Rat))

noncomputable def monomialPrimitiveEndpointDifference
    (n : Nat) (a b : Rat) : RealCompute :=
  endpointDifferenceRaw (monomialPrimitiveRaw n) a b
    (endpointDifference_valid_of_fun_valid (RealFunRaw.exact_valid _) trivial trivial)

theorem monomialPrimitiveEndpointDifference_adjacent_additive
    (n : Nat) (a b c : Rat) :
    (monomialPrimitiveEndpointDifference n a b +
      monomialPrimitiveEndpointDifference n b c).Equiv
      (monomialPrimitiveEndpointDifference n a c) := by
  unfold monomialPrimitiveEndpointDifference
  apply endpointDifferenceRaw_adjacent_additive
    (RealFunRaw.exact_valid _) trivial trivial trivial

/-! A uniform left-rectangle sum for a monomial is exactly a scaled finite
power sum.  This is the finite computation underneath the eventual value
theorem; no convergence statement is used here. -/

private theorem foldl_scaled_power_range (h : Rat) (k n : Nat) :
    (List.range n : List Nat).foldl
      (fun acc (j : Nat) => acc + h * (((j : Rat) * h) ^ k)) 0 =
      h ^ (k + 1) * Series.powerSum k n := by
  have hpow : forall (m j : Nat), ((m : Rat) * h) ^ j =
      (m : Rat) ^ j * h ^ j := by
    intro m j
    induction j with
    | zero => rw [Rat.pow_zero, Rat.pow_zero, Rat.pow_zero]; decide +kernel
    | succ j ih =>
        rw [Rat.pow_succ, Rat.pow_succ, Rat.pow_succ, ih]
        grind [Rat.mul_assoc, Rat.mul_comm]
  induction n with
  | zero => simp [Series.powerSum_zero]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, Series.powerSum_succ]
      rw [hpow n k]
      grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm]

theorem uniformLeftEndpointSum_pow_eq_scaled_powerSum
    (k n : Nat) :
    _root_.ComputableAnalysis.IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x ^ k) n =
      (1 / (n : Rat)) ^ (k + 1) * Series.powerSum k n := by
  unfold _root_.ComputableAnalysis.IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
  have harg (j : Nat) :
      (j : Rat) / (n : Rat) = (j : Rat) * (1 / (n : Rat)) := by
    rw [Rat.div_def, Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hrewrite :
      (fun acc (j : Nat) =>
        acc + (1 / (n : Rat)) * (((j : Rat) / (n : Rat)) ^ k)) =
      (fun acc (j : Nat) =>
        acc + (1 / (n : Rat)) *
          (((j : Rat) * (1 / (n : Rat))) ^ k)) := by
    funext acc j
    rw [harg]
  rw [hrewrite]
  exact foldl_scaled_power_range (1 / (n : Rat)) k n

private theorem foldl_scaled_shifted_power_range (h : Rat) (k n : Nat) :
    (List.range n : List Nat).foldl
      (fun acc (j : Nat) =>
        acc + h * (((Nat.succ j : Nat) : Rat) * h) ^ k) 0 =
      h ^ (k + 1) * Series.powerSumBlock k 1 n := by
  have hpow : forall (m j : Nat), ((m : Rat) * h) ^ j =
      (m : Rat) ^ j * h ^ j := by
    intro m j
    induction j with
    | zero => rw [Rat.pow_zero, Rat.pow_zero, Rat.pow_zero]; decide +kernel
    | succ j ih =>
        rw [Rat.pow_succ, Rat.pow_succ, Rat.pow_succ, ih]
        grind [Rat.mul_assoc, Rat.mul_comm]
  induction n with
  | zero => simp [Series.powerSumBlock]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, Series.powerSumBlock_succ]
      rw [hpow (n + 1) k]
      simp only [Rat.natCast_add]
      grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm]

theorem uniformRightEndpointSum_pow_eq_scaled_powerSumBlock
    (k n : Nat) :
    _root_.ComputableAnalysis.IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x ^ k) n =
      (1 / (n : Rat)) ^ (k + 1) * Series.powerSumBlock k 1 n := by
  unfold _root_.ComputableAnalysis.IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
  have harg (j : Nat) :
      (Nat.succ j : Rat) / (n : Rat) =
        (Nat.succ j : Rat) * (1 / (n : Rat)) := by
    rw [Rat.div_def, Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hrewrite :
      (fun acc (j : Nat) =>
        acc + (1 / (n : Rat)) *
          (((Nat.succ j : Nat) : Rat) / (n : Rat)) ^ k) =
      (fun acc (j : Nat) =>
        acc + (1 / (n : Rat)) *
          ((((Nat.succ j : Nat) : Rat) * (1 / (n : Rat))) ^ k)) := by
    funext acc j
    rw [harg]
  rw [hrewrite]
  exact foldl_scaled_shifted_power_range (1 / (n : Rat)) k n

theorem uniformRightEndpointSum_pow_sub_left_eq_scaled_last_power
    {k n : Nat} (hk : 0 < k) :
    _root_.ComputableAnalysis.IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x ^ k) n -
      _root_.ComputableAnalysis.IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x ^ k) n =
      (1 / (n : Rat)) ^ (k + 1) * (n : Rat) ^ k := by
  rw [uniformRightEndpointSum_pow_eq_scaled_powerSumBlock,
    uniformLeftEndpointSum_pow_eq_scaled_powerSum]
  have hblock : Series.powerSumBlock k 1 n =
      Series.powerSum k n + (n : Rat) ^ k := by
    induction n with
    | zero =>
        have hzero : (0 : Rat) ^ k = 0 := by
          induction k with
          | zero => omega
          | succ k => rw [Rat.pow_succ]; simp
        simp [Series.powerSumBlock, Series.powerSum, hzero] <;> decide +kernel
    | succ n ih =>
        rw [Series.powerSumBlock_succ, Series.powerSum_succ, ih]
        simp only [Rat.natCast_add]
        grind [Rat.pow_succ, Rat.add_assoc, Rat.add_comm]
  rw [hblock]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.mul_add]

theorem uniformRightEndpointSum_pow_sub_left_eq_inv_of_pos
    {k n : Nat} (hk : 0 < k) (hn : 0 < n) :
    _root_.ComputableAnalysis.IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x ^ k) n -
      _root_.ComputableAnalysis.IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x ^ k) n =
      1 / (n : Rat) := by
  rw [uniformRightEndpointSum_pow_sub_left_eq_scaled_last_power hk]
  have hnrat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have hcancel : forall j : Nat,
      (1 / (n : Rat)) ^ j * (n : Rat) ^ j = 1 := by
    intro j
    induction j with
    | zero => rw [Rat.pow_zero, Rat.pow_zero]; decide +kernel
    | succ j ih =>
        rw [Rat.pow_succ, Rat.pow_succ]
        rw [Rat.div_def]
        have hmul : (n : Rat)⁻¹ * (n : Rat) = 1 :=
          Rat.inv_mul_cancel (n : Rat) hnrat
        grind [Rat.mul_assoc, Rat.mul_comm]
  rw [Rat.pow_succ]
  grind [Rat.mul_assoc, Rat.mul_comm, hcancel k]

def exactRat_cube_integral_certificate :
    Integral.IntervalRegularCandidateCertificate
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 3) 0 1) where
  regular := exactRat_cube_intervalRegularOn_unit
  construction :=
    IntegralIdentities.LipschitzDyadic.construction (fun x : Rat => x ^ 3) 3
      exactCube_lipschitz_on_unit

theorem exactRat_cube_integral_raw_valid :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 3) 0 1)
      exactRat_cube_integral_certificate).Valid := by
  exact Integral.raw_valid _ exactRat_cube_integral_certificate

def stableCube_integral_certificate :
    Integral.IntervalRegularCandidateCertificate stableCubeFunction where
  regular := stableCube_intervalRegularOn_unit
  construction :=
    { compute := IntegralIdentities.LipschitzDyadic.compute
        (fun x : Rat => x ^ 3) 3
      certificate := IntegralIdentities.LipschitzDyadic.raw_valid
        exactCube_lipschitz_on_unit }

theorem stableCube_integral_raw_valid :
    (Integral.raw stableCubeFunction stableCube_integral_certificate).Valid := by
  exact Integral.raw_valid _ stableCube_integral_certificate

theorem exactCube_uniformLeftSum_eq
    {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x ^ 3) n =
      Series.cubeSum n / (n : Rat) ^ 4 := by
  have hnrat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have haux : forall k : Nat,
      (List.range k).foldl
          (fun total (j : Nat) =>
            total + (1 / (n : Rat)) *
              (((j : Rat) / (n : Rat)) ^ 3)) 0 =
        Series.cubeSum k / (n : Rat) ^ 4 := by
    intro k
    induction k with
    | zero =>
        simp [Series.cubeSum, Rat.div_def]
    | succ k ih =>
        rw [List.range_succ, List.foldl_append]
        simp [List.foldl]
        rw [ih, Series.cubeSum_succ]
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
          Rat.add_mul, Rat.pow_succ, Rat.mul_inv_cancel]
  unfold IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
  exact haux n

theorem exactCube_uniformRightSum_eq
    {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x ^ 3) n =
      Series.cubeSum (n + 1) / (n : Rat) ^ 4 := by
  have hnrat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have hfrac (a b : Rat) :
      a / (n : Rat) ^ 4 + b / (n : Rat) ^ 4 =
        (a + b) / (n : Rat) ^ 4 := by
    rw [Rat.div_def, Rat.div_def, Rat.div_def]
    grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm,
      Rat.pow_succ, Rat.mul_inv_cancel]
  have haux : forall k : Nat,
      (List.range k).foldl
          (fun total (j : Nat) =>
            total + (1 / (n : Rat)) *
              ((((j + 1 : Nat) : Rat) / (n : Rat)) ^ 3)) 0 =
        Series.cubeSum (k + 1) / (n : Rat) ^ 4 := by
    intro k
    induction k with
    | zero =>
        simp [Series.cubeSum, Rat.div_def]
        grind
    | succ k ih =>
        simp at ih ⊢
        rw [List.range_succ, List.foldl_append]
        simp [List.foldl]
        rw [ih]
        have hterm :
            (1 / (n : Rat)) *
                ((((k : Rat) + 1) / (n : Rat)) ^ 3) =
              ((k : Rat) + 1) ^ 3 / (n : Rat) ^ 4 := by
          rw [Rat.div_def, Rat.div_def]
          grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm,
            Rat.mul_inv_cancel]
        change Series.cubeSum (k + 1) / (n : Rat) ^ 4 +
          (1 / (n : Rat)) * (((k : Rat) + 1) / (n : Rat)) ^ 3 =
          Series.cubeSum (k + 1 + 1) / (n : Rat) ^ 4
        rw [hterm]
        have hs : Series.cubeSum (k + 1 + 1) =
            Series.cubeSum (k + 1) + ((k + 1 : Nat) : Rat) ^ 3 := by
          rw [show k + 1 + 1 = (k + 1) + 1 by omega,
            Series.cubeSum_succ]
        rw [hs]
        simpa [Rat.natCast_add] using hfrac _ _
  unfold IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
  exact haux n

theorem exactCube_uniformLeftSum_le_one_fourth
    {n : Nat} (hn : 0 < n) :
    IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
        (fun x : Rat => x ^ 3) n <= 1 / 4 := by
  rw [exactCube_uniformLeftSum_eq hn, Series.cubeSum_eq]
  have hnrat : 0 < (n : Rat) := (Rat.natCast_pos).2 hn
  have hden : 0 < (n : Rat) ^ 4 := Rat.pow_pos hnrat
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat) ^ 4)
  · rw [Rat.div_def, Rat.div_def]
    have hn1 : 1 <= (n : Rat) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0))
    have hpoly : (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 <= (n : Rat) ^ 4 := by
      have hsq : ((n : Rat) - 1) ^ 2 <= (n : Rat) ^ 2 := by
        grind [Rat.pow_succ, Rat.sub_eq_add_neg]
      have h : (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 <=
          (n : Rat) ^ 2 * (n : Rat) ^ 2 :=
        Rat.mul_le_mul_of_nonneg_left hsq
          (Rat.pow_nonneg (Rat.le_of_lt hnrat) : 0 <= (n : Rat) ^ 2)
      simpa [Rat.pow_succ, Rat.mul_assoc] using h
    have hscaled := Rat.mul_le_mul_of_nonneg_right hpoly
      (Rat.le_of_lt ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 4)))
    have hcancel : ((n : Rat) ^ 4)⁻¹ * (n : Rat) ^ 4 = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt hden)
    calc
      (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 * 4⁻¹ *
          ((n : Rat) ^ 4)⁻¹ * (n : Rat) ^ 4 =
          (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 * 4⁻¹ := by
            calc
              _ = ((n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 * 4⁻¹) *
                  (((n : Rat) ^ 4)⁻¹ * (n : Rat) ^ 4) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
              _ = _ := by rw [hcancel, Rat.mul_one]
      _ <= (n : Rat) ^ 4 * 4⁻¹ := hscaled
      _ = 1 / 4 * (n : Rat) ^ 4 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hden

theorem exactCube_uniformRightSum_ge_one_fourth
    {n : Nat} (hn : 0 < n) :
    1 / 4 <=
      IntegralIdentities.LipschitzDyadic.uniformRightEndpointSum
        (fun x : Rat => x ^ 3) n := by
  rw [exactCube_uniformRightSum_eq hn, Series.cubeSum_eq]
  have hnrat : 0 < (n : Rat) := (Rat.natCast_pos).2 hn
  have hden : 0 < (n : Rat) ^ 4 := Rat.pow_pos hnrat
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat) ^ 4)
  · rw [Rat.div_def, Rat.div_def]
    have hnp1 : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by
      simp [Rat.natCast_add]
    rw [hnp1]
    have hminus : (n : Rat) + 1 - 1 = (n : Rat) := by grind
    rw [hminus]
    have hpoly : (n : Rat) ^ 4 <= ((n : Rat) + 1) ^ 2 * (n : Rat) ^ 2 := by
      have hnonneg : 0 <= (n : Rat) := Rat.le_of_lt hnrat
      have hsq : (n : Rat) ^ 2 <= ((n : Rat) + 1) ^ 2 := by
        grind [Rat.pow_succ]
      have h : (n : Rat) ^ 2 * (n : Rat) ^ 2 <=
          ((n : Rat) + 1) ^ 2 * (n : Rat) ^ 2 :=
        Rat.mul_le_mul_of_nonneg_right hsq
          (Rat.pow_nonneg hnonneg : 0 <= (n : Rat) ^ 2)
      simpa [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm] using h
    have hscaled := Rat.mul_le_mul_of_nonneg_right hpoly
      (Rat.le_of_lt ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 4)))
    have hcancel : ((n : Rat) ^ 4)⁻¹ * (n : Rat) ^ 4 = 1 :=
      Rat.inv_mul_cancel _ (Rat.ne_of_gt hden)
    have horder : ((n : Rat) + 1) ^ 2 * (n : Rat) ^ 2 =
        (n : Rat) ^ 2 * ((n : Rat) + 1) ^ 2 := by
      grind [Rat.mul_comm]
    calc
      1 / 4 * (n : Rat) ^ 4 = (n : Rat) ^ 4 * 4⁻¹ := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= ((n : Rat) + 1) ^ 2 * (n : Rat) ^ 2 * 4⁻¹ := by
        simpa [Rat.mul_assoc, Rat.mul_comm] using hscaled
      _ = ((n : Rat) + 1) ^ 2 * (n : Rat) ^ 2 * 4⁻¹ *
          ((n : Rat) ^ 4)⁻¹ * (n : Rat) ^ 4 := by
        calc
          _ = (((n : Rat) + 1) ^ 2 * (n : Rat) ^ 2 * 4⁻¹) *
              (((n : Rat) ^ 4)⁻¹ * (n : Rat) ^ 4) := by
            grind [Rat.mul_assoc, Rat.mul_comm]
          _ = _ := by
            symm
            calc
              _ = (((n : Rat) + 1) ^ 2 * (n : Rat) ^ 2 * 4⁻¹) *
                  (((n : Rat) ^ 4)⁻¹ * (n : Rat) ^ 4) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
              _ = _ := by rw [hcancel, Rat.mul_one]
  · exact hden

theorem exactCube_compute_contains_one_fourth (stage : Nat) :
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x ^ 3) 3 stage).ContainsInterval
      { lo := 1 / 4, hi := 1 / 4 } := by
  let n : Nat := 2 ^ stage
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.pow_pos (by omega : 0 < 2)
  have hl := IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum
    exactCube_lipschitz_on_unit stage
  have hr := IntegralIdentities.LipschitzDyadic.compute_contains_uniformRightEndpointSum
    exactCube_lipschitz_on_unit stage
  have hleft := exactCube_uniformLeftSum_le_one_fourth hn
  have hright := exactCube_uniformRightSum_ge_one_fourth hn
  unfold QInterval.ContainsInterval
  constructor
  · exact Rat.le_trans hl.1 hleft
  · exact Rat.le_trans hright hr.2

theorem exactRat_cube_integral_raw_equiv_one_fourth :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 3) 0 1)
      exactRat_cube_integral_certificate).Equiv
      (RealCompute.ofRat (1 / 4)) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x ^ 3) 3 n)
    { lo := 1 / 4, hi := 1 / 4 }
  unfold QInterval.Overlaps
  exact exactCube_compute_contains_one_fourth n

theorem stableCube_integral_raw_equiv_one_fourth :
    (Integral.raw stableCubeFunction stableCube_integral_certificate).Equiv
      (RealCompute.ofRat (1 / 4)) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    (IntegralIdentities.LipschitzDyadic.compute (fun x : Rat => x ^ 3) 3 n)
    { lo := 1 / 4, hi := 1 / 4 }
  unfold QInterval.Overlaps
  exact exactCube_compute_contains_one_fourth n

/-! ## First end-to-end effective FTC instance

The existing square integral is now also packaged through the generic
derivative-bound interface.  The derivative box on a cell `[a,b]` is the
endpoint range `[2*a,2*b]`; its scaled width sums to `2/N` on an `N`-cell
uniform partition. -/

def squarePrimitiveRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => x * x)

def squareDerivativeRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => 2 * x)

def squareEffectivePartition (eps : QPos) : Nat :=
  2 * (eps.val.den + 1)

theorem squareEffectivePartition_pos (eps : QPos) :
    0 < squareEffectivePartition eps := by
  unfold squareEffectivePartition
  omega

def squareEffectivePartitionOf (eps : QPos) : RationalPartition 0 1 :=
  RationalPartition.uniform 0 1 (squareEffectivePartition eps)
    (squareEffectivePartition_pos eps) (by decide +kernel)

def squareEffectiveBound
    {a b : Rat} (C : RationalSubinterval a b) (_n : Nat) : QInterval :=
  { lo := 2 * C.lower, hi := 2 * C.upper }

theorem squareEffectiveBound_width
    {a b : Rat} (C : RationalSubinterval a b) (n : Nat) :
    (squareEffectiveBound C n).width = 2 * C.width := by
  unfold squareEffectiveBound RationalSubinterval.width QInterval.width
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]

theorem squareEffectiveBound_contains_derivative
    {a b : Rat} (C : RationalSubinterval a b) (n : Nat)
    {x : Rat} (hx : C.contains x) :
    QInterval.ContainsInterval (squareEffectiveBound C n)
      ((squareDerivativeRaw.compute x n)) := by
  unfold squareEffectiveBound squareDerivativeRaw RealFunRaw.exact
    QInterval.ContainsInterval
  exact ⟨Rat.mul_le_mul_of_nonneg_left hx.1
      (by decide +kernel : (0 : Rat) ≤ 2),
    Rat.mul_le_mul_of_nonneg_left hx.2
      (by decide +kernel : (0 : Rat) ≤ 2)⟩

def squareEffectiveDerivativeBound (eps : QPos) (k : Nat)
    (hk : k < (squareEffectivePartitionOf eps).pieces) :
    DerivativeBoundOnSubinterval squareDerivativeRaw
      ((squareEffectivePartitionOf eps).cell k hk) := by
  let C := (squareEffectivePartitionOf eps).cell k hk
  exact {
    bound := fun n => squareEffectiveBound C n
    evalPrecision := fun n => n
    domain_on := fun x hx => trivial
    bound_ordered := fun n => by
      rw [squareEffectiveBound_width]
      unfold RationalSubinterval.width
      have hcell : 0 ≤ C.upper - C.lower := by
        have hordered := C.ordered
        grind
      exact Rat.mul_nonneg (by decide +kernel) hcell
    contains_values := fun n x hx => by
      exact squareEffectiveBound_contains_derivative C n hx }

def squareEffectiveFTCData :
    EffectiveDerivativeBoundFTC squarePrimitiveRaw squareDerivativeRaw 0 1 where
  primitive_valid := RealFunRaw.exact_valid _
  primitive_domain_lower := trivial
  primitive_domain_upper := trivial
  choosePartition := fun eps =>
    squareEffectivePartitionOf eps
  chooseEndpointPrecision := fun _ => 0
  chooseBoundStage := fun _ => 0
  derivativeBound := squareEffectiveDerivativeBound
  domain_at_partition := by
    intro eps i hi
    trivial
  localControl := by
    intro eps k hk
    let C := (squareEffectivePartitionOf eps).cell k hk
    let B := squareEffectiveDerivativeBound eps k hk
    exact {
      primitive_domain_lower := trivial
      primitive_domain_upper := trivial
      endpointPrecision := fun _ => 0
      endpoint_contained := by
        intro n
        dsimp [C, B, squareEffectiveDerivativeBound]
        unfold squareEffectiveBound RationalSubinterval.scaleBound
          endpointDifferenceInterval squarePrimitiveRaw RealFunRaw.exact
        have hwidth : 0 <= C.width := by
          unfold RationalSubinterval.width
          have hordered := C.ordered
          grind
        have hwidth' : 0 <=
            ((squareEffectivePartitionOf eps).cell k hk).width := by
          dsimp [C] at hwidth
          exact hwidth
        simp only [QInterval.scaleByRat, if_pos hwidth']
        have hordered : C.lower <= C.upper := C.ordered
        have hlower : 0 <= C.lower := C.lower_mem
        have hfactor :
            C.upper * C.upper - C.lower * C.lower =
              C.width * (C.upper + C.lower) := by
          unfold RationalSubinterval.width
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        have hlower0 : 0 <= C.lower := C.lower_mem
        have hupper0 : 0 <= C.upper := Rat.le_trans hlower0 C.ordered
        constructor
        · rw [hfactor]
          exact Rat.mul_le_mul_of_nonneg_left (by grind) hwidth
        · rw [hfactor]
          exact Rat.mul_le_mul_of_nonneg_left (by grind) hwidth }
  endpointPrecision_agreement := by
    intro eps k hk n
    rfl
  riemann_width := by
    intro eps
    let N := squareEffectivePartition eps
    have hN : 0 < N := by
      exact squareEffectivePartition_pos eps
    let P := squareEffectivePartitionOf eps
    have hbound : forall k (hk : k < N),
      (squareEffectiveBound
        ((RationalPartition.uniform 0 1 N hN (by decide +kernel)).cell k hk) 0).width <=
          2 * mesh 0 1 N := by
      intro k hk
      rw [squareEffectiveBound_width]
      have hw :
          ((RationalPartition.uniform 0 1 N hN (by decide +kernel)).cell k hk).width =
            mesh 0 1 N :=
        RationalPartition.uniform_cell_width 0 1 N hN (by decide +kernel) k hk
      rw [hw]
      exact Rat.le_refl
    have hsum := RationalPartition.uniform_boundIntegralSum_width_le
      N hN (by decide +kernel : (0 : Rat) <= 1)
      (fun k hk => (squareEffectiveDerivativeBound eps k hk).bound 0)
      (2 * mesh 0 1 N) hbound
    have hsum_bound :
        ((squareEffectivePartitionOf eps).boundIntegralSum
          (fun k hk => (squareEffectiveDerivativeBound eps k hk).bound 0)).width
          <= 2 * mesh 0 1 N := by
      change ((RationalPartition.uniform 0 1 N hN (by decide +kernel)).boundIntegralSum
          (fun k hk => (squareEffectiveDerivativeBound eps k hk).bound 0)).width
          <= 2 * mesh 0 1 N
      have hpart : squareEffectivePartitionOf eps =
          RationalPartition.uniform 0 1 N hN (by decide +kernel) := by
        unfold squareEffectivePartitionOf
        congr
      cases hpart
      exact Rat.le_trans hsum (by grind)
    have hmesh : mesh 0 1 N = 1 / (N : Rat) := by
      unfold mesh
      rw [if_neg (Nat.ne_of_gt hN)]
      rw [Rat.div_def]
      grind
    have hden := FTC.one_div_den_succ_le_of_pos eps.property
    have hfinal : 2 * mesh 0 1 N <= eps.val := by
      rw [hmesh]
      dsimp [N, squareEffectivePartition]
      have hcancel :
          (2 : Rat) * (1 / ((2 * (eps.val.den + 1) : Nat) : Rat)) =
            1 / ((eps.val.den + 1 : Nat) : Rat) := by
        rw [Rat.div_def, Rat.div_def]
        rw [Rat.natCast_mul]
        grind [Rat.mul_assoc, Rat.mul_comm,
          Rat.mul_inv_cancel]
      rw [hcancel]
      exact hden
    exact Rat.le_trans hsum_bound hfinal
  endpoint_width := by
    intro eps
    simpa [endpointDifferenceInterval, squarePrimitiveRaw, RealFunRaw.exact,
      QInterval.width, Rat.sub_self] using (Rat.le_of_lt eps.property)

theorem squareEffectiveFTC_equiv_endpoint :
    squareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      squareEffectiveFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact effectiveDerivativeBoundFTC squareEffectiveFTCData

/-! ## Cubic effective FTC instance

This is the first non-linear reuse of the adapter.  On `[a,b] ⊆ [0,1]`, the
derivative range is `[3*a^2, 3*b^2]`, while
`b^3-a^3 = (b-a)*(a^2+a*b+b^2)`.  The resulting global budget is `6/N`. -/

def cubePrimitiveRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => x * x * x)

def cubeDerivativeRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => 3 * x * x)

def cubeEffectivePartition (eps : QPos) : Nat :=
  6 * (eps.val.den + 1)

theorem cubeEffectivePartition_pos (eps : QPos) :
    0 < cubeEffectivePartition eps := by
  unfold cubeEffectivePartition
  omega

def cubeEffectivePartitionOf (eps : QPos) : RationalPartition 0 1 :=
  RationalPartition.uniform 0 1 (cubeEffectivePartition eps)
    (cubeEffectivePartition_pos eps) (by decide +kernel)

theorem cube_square_range {a b x : Rat}
    (ha : 0 <= a) (hab : a <= b) (hx : a <= x) (hxb : x <= b) :
    a * a <= x * x ∧ x * x <= b * b := by
  have hxa : 0 <= x + a := by grind
  have hxb' : 0 <= b + x := by grind
  have hleft : 0 <= (x - a) * (x + a) :=
    Rat.mul_nonneg (by grind) hxa
  have hright : 0 <= (b - x) * (b + x) :=
    Rat.mul_nonneg (by grind) hxb'
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

def cubeEffectiveBound
    {a b : Rat} (C : RationalSubinterval a b) (_n : Nat) : QInterval :=
  { lo := 3 * C.lower * C.lower, hi := 3 * C.upper * C.upper }

theorem cubeEffectiveBound_width
    {a b : Rat} (C : RationalSubinterval a b) (n : Nat) :
    (cubeEffectiveBound C n).width =
      3 * C.width * (C.upper + C.lower) := by
  unfold cubeEffectiveBound RationalSubinterval.width QInterval.width
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem cubeEffectiveBound_contains_derivative
    {a b : Rat} (C : RationalSubinterval a b) (n : Nat)
    (ha : 0 <= C.lower) {x : Rat} (hx : C.contains x) :
    QInterval.ContainsInterval (cubeEffectiveBound C n)
      (cubeDerivativeRaw.compute x n) := by
  unfold cubeEffectiveBound cubeDerivativeRaw RealFunRaw.exact
    QInterval.ContainsInterval
  have hrange := cube_square_range (a := C.lower) (b := C.upper) (x := x)
    ha C.ordered hx.1 hx.2
  constructor <;> grind

def cubeEffectiveDerivativeBound (eps : QPos) (k : Nat)
    (hk : k < (cubeEffectivePartitionOf eps).pieces) :
    DerivativeBoundOnSubinterval cubeDerivativeRaw
      ((cubeEffectivePartitionOf eps).cell k hk) := by
  let C := (cubeEffectivePartitionOf eps).cell k hk
  exact {
    bound := fun n => cubeEffectiveBound C n
    evalPrecision := fun n => n
    domain_on := fun x hx => trivial
    bound_ordered := fun n => by
      rw [cubeEffectiveBound_width]
      have hwidth : 0 <= C.width := by
        unfold RationalSubinterval.width
        have hordered := C.ordered
        grind
      have hsum : 0 <= C.upper + C.lower := by
        exact Rat.add_nonneg (Rat.le_trans C.lower_mem C.ordered) C.lower_mem
      exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hwidth) hsum
    contains_values := fun n x hx => by
      exact cubeEffectiveBound_contains_derivative C n C.lower_mem hx }

def cubeEffectiveFTCData :
    EffectiveDerivativeBoundFTC cubePrimitiveRaw cubeDerivativeRaw 0 1 where
  primitive_valid := RealFunRaw.exact_valid _
  primitive_domain_lower := trivial
  primitive_domain_upper := trivial
  choosePartition := fun eps => cubeEffectivePartitionOf eps
  chooseEndpointPrecision := fun _ => 0
  chooseBoundStage := fun _ => 0
  derivativeBound := cubeEffectiveDerivativeBound
  domain_at_partition := by
    intro eps i hi
    trivial
  localControl := by
    intro eps k hk
    let C := (cubeEffectivePartitionOf eps).cell k hk
    let B := cubeEffectiveDerivativeBound eps k hk
    exact {
      primitive_domain_lower := trivial
      primitive_domain_upper := trivial
      endpointPrecision := fun _ => 0
      endpoint_contained := by
        intro n
        dsimp [C, B, cubeEffectiveDerivativeBound]
        unfold cubeEffectiveBound RationalSubinterval.scaleBound
          endpointDifferenceInterval cubePrimitiveRaw RealFunRaw.exact
        have hwidth : 0 <= C.width := by
          unfold RationalSubinterval.width
          have hordered := C.ordered
          grind
        have hwidth' : 0 <=
            ((cubeEffectivePartitionOf eps).cell k hk).width := by
          dsimp [C] at hwidth
          exact hwidth
        simp only [QInterval.scaleByRat, if_pos hwidth']
        have hlower : 0 <= C.lower := C.lower_mem
        have hordered : C.lower <= C.upper := C.ordered
        have hfactor :
            C.upper * C.upper * C.upper - C.lower * C.lower * C.lower =
              C.width * (C.upper * C.upper + C.upper * C.lower +
                C.lower * C.lower) := by
          unfold RationalSubinterval.width
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        have hleft : 0 <= C.width * (C.upper + 2 * C.lower) :=
          Rat.mul_nonneg hwidth (by
            exact Rat.add_nonneg (Rat.le_trans C.lower_mem C.ordered)
              (Rat.mul_nonneg (by decide +kernel) C.lower_mem))
        have hright : 0 <= C.width * (2 * C.upper + C.lower) :=
          Rat.mul_nonneg hwidth (by
            exact Rat.add_nonneg
              (Rat.mul_nonneg (by decide +kernel)
                (Rat.le_trans C.lower_mem C.ordered)) C.lower_mem)
        have hlow : 3 * C.lower * C.lower <=
            C.upper * C.upper + C.upper * C.lower + C.lower * C.lower := by
          unfold RationalSubinterval.width at hleft
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        have hhigh : C.upper * C.upper + C.upper * C.lower +
            C.lower * C.lower <= 3 * C.upper * C.upper := by
          unfold RationalSubinterval.width at hright
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        constructor
        · rw [hfactor]
          exact Rat.mul_le_mul_of_nonneg_left hlow hwidth
        · rw [hfactor]
          exact Rat.mul_le_mul_of_nonneg_left hhigh hwidth }
  endpointPrecision_agreement := by
    intro eps k hk n
    rfl
  riemann_width := by
    intro eps
    let N := cubeEffectivePartition eps
    have hN : 0 < N := by exact cubeEffectivePartition_pos eps
    have hbound : forall k (hk : k < N),
        (cubeEffectiveBound
          ((RationalPartition.uniform 0 1 N hN (by decide +kernel)).cell k hk) 0).width <=
          6 * mesh 0 1 N := by
      intro k hk
      let C := (RationalPartition.uniform 0 1 N hN
        (by decide +kernel : (0 : Rat) <= 1)).cell k hk
      change (cubeEffectiveBound C 0).width <= 6 * mesh 0 1 N
      rw [cubeEffectiveBound_width]
      have hw : C.width = mesh 0 1 N := by
        dsimp [C]
        exact RationalPartition.uniform_cell_width 0 1 N hN
          (by decide +kernel) k hk
      rw [hw]
      have hmesh := mesh_nonneg_of_le hN
        (by decide +kernel : (0 : Rat) <= 1)
      have hsum : C.upper + C.lower <= 2 := by
        have hu := C.upper_mem
        have hl := C.lower_mem
        have hord := C.ordered
        grind
      calc
        3 * mesh 0 1 N * (C.upper + C.lower) <=
            (3 * mesh 0 1 N) * 2 := by
              exact Rat.mul_le_mul_of_nonneg_left hsum
                (Rat.mul_nonneg (by decide +kernel) hmesh)
        _ = 6 * mesh 0 1 N := by grind
    have hsum := RationalPartition.uniform_boundIntegralSum_width_le
      N hN (by decide +kernel : (0 : Rat) <= 1)
      (fun k hk => (cubeEffectiveDerivativeBound eps k hk).bound 0)
      (6 * mesh 0 1 N) hbound
    have hsum_bound :
        ((cubeEffectivePartitionOf eps).boundIntegralSum
          (fun k hk => (cubeEffectiveDerivativeBound eps k hk).bound 0)).width
          <= 6 * mesh 0 1 N := by
      change ((RationalPartition.uniform 0 1 N hN (by decide +kernel)).boundIntegralSum
          (fun k hk => (cubeEffectiveDerivativeBound eps k hk).bound 0)).width
          <= 6 * mesh 0 1 N
      have hpart : cubeEffectivePartitionOf eps =
          RationalPartition.uniform 0 1 N hN (by decide +kernel) := by
        unfold cubeEffectivePartitionOf
        congr
      cases hpart
      exact Rat.le_trans hsum (by grind)
    have hmesh : mesh 0 1 N = 1 / (N : Rat) := by
      unfold mesh
      rw [if_neg (Nat.ne_of_gt hN)]
      rw [Rat.div_def]
      grind
    have hden := FTC.one_div_den_succ_le_of_pos eps.property
    have hfinal : 6 * mesh 0 1 N <= eps.val := by
      rw [hmesh]
      dsimp [N, cubeEffectivePartition]
      have hcancel :
          (6 : Rat) * (1 / ((6 * (eps.val.den + 1) : Nat) : Rat)) =
            1 / ((eps.val.den + 1 : Nat) : Rat) := by
        rw [Rat.div_def, Rat.div_def, Rat.natCast_mul]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      rw [hcancel]
      exact hden
    exact Rat.le_trans hsum_bound hfinal
  endpoint_width := by
    intro eps
    simpa [endpointDifferenceInterval, cubePrimitiveRaw, RealFunRaw.exact,
      QInterval.width, Rat.sub_self] using (Rat.le_of_lt eps.property)

theorem cubeEffectiveFTC_equiv_endpoint :
    cubeEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      cubeEffectiveFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact effectiveDerivativeBoundFTC cubeEffectiveFTCData

/-! ## Quartic effective FTC instance

The quartic is the next polynomial regression.  Its derivative enclosure is
`[4*a^3,4*b^3]`; on `[0,1]` the enclosure width is at most `12` times the
cell width, giving an explicit `12/N` schedule. -/

def quarticPrimitiveRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => x ^ 4)

def quarticDerivativeRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => 4 * x ^ 3)

def quarticEffectivePartition (eps : QPos) : Nat :=
  12 * (eps.val.den + 1)

theorem quarticEffectivePartition_pos (eps : QPos) :
    0 < quarticEffectivePartition eps := by
  unfold quarticEffectivePartition
  omega

def quarticEffectivePartitionOf (eps : QPos) : RationalPartition 0 1 :=
  RationalPartition.uniform 0 1 (quarticEffectivePartition eps)
    (quarticEffectivePartition_pos eps) (by decide +kernel)

theorem quartic_cube_range {a b x : Rat}
    (ha : 0 <= a) (hab : a <= b) (hx : a <= x) (hxb : x <= b) :
    a ^ 3 <= x ^ 3 ∧ x ^ 3 <= b ^ 3 := by
  have hleft : 0 <= (x - a) * (x ^ 2 + x * a + a ^ 2) := by
    exact Rat.mul_nonneg (by grind)
      (Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg (by grind))
        (Rat.mul_nonneg (by grind) ha)) (Rat.pow_nonneg ha))
  have hright : 0 <= (b - x) * (b ^ 2 + b * x + x ^ 2) := by
    exact Rat.mul_nonneg (by grind)
      (Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg (by grind))
        (Rat.mul_nonneg (by grind) (by grind))) (Rat.pow_nonneg (by grind)))
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add,
    Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

def quarticEffectiveBound
    {a b : Rat} (C : RationalSubinterval a b) (_n : Nat) : QInterval :=
  { lo := 4 * C.lower ^ 3, hi := 4 * C.upper ^ 3 }

theorem quarticEffectiveBound_width
    {a b : Rat} (C : RationalSubinterval a b) (n : Nat) :
    (quarticEffectiveBound C n).width =
      4 * C.width * (C.upper ^ 2 + C.upper * C.lower + C.lower ^ 2) := by
  unfold quarticEffectiveBound RationalSubinterval.width QInterval.width
  grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem quarticEffectiveBound_contains_derivative
    {a b : Rat} (C : RationalSubinterval a b) (n : Nat)
    (ha : 0 <= C.lower) {x : Rat} (hx : C.contains x) :
    QInterval.ContainsInterval (quarticEffectiveBound C n)
      (quarticDerivativeRaw.compute x n) := by
  unfold quarticEffectiveBound quarticDerivativeRaw RealFunRaw.exact
    QInterval.ContainsInterval
  have hrange := quartic_cube_range (a := C.lower) (b := C.upper) (x := x)
    ha C.ordered hx.1 hx.2
  constructor <;> grind

def quarticEffectiveDerivativeBound (eps : QPos) (k : Nat)
    (hk : k < (quarticEffectivePartitionOf eps).pieces) :
    DerivativeBoundOnSubinterval quarticDerivativeRaw
      ((quarticEffectivePartitionOf eps).cell k hk) := by
  let C := (quarticEffectivePartitionOf eps).cell k hk
  exact {
    bound := fun n => quarticEffectiveBound C n
    evalPrecision := fun n => n
    domain_on := fun x hx => trivial
    bound_ordered := fun n => by
      rw [quarticEffectiveBound_width]
      have hw : 0 <= C.width := by
        unfold RationalSubinterval.width
        have ho := C.ordered
        grind
      have hs : 0 <= C.upper ^ 2 + C.upper * C.lower + C.lower ^ 2 := by
        exact Rat.add_nonneg (Rat.add_nonneg
          (Rat.pow_nonneg (Rat.le_trans C.lower_mem C.ordered))
          (Rat.mul_nonneg (Rat.le_trans C.lower_mem C.ordered) C.lower_mem))
          (Rat.pow_nonneg C.lower_mem)
      exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hw) hs
    contains_values := fun n x hx => by
      exact quarticEffectiveBound_contains_derivative C n C.lower_mem hx }

def quarticEffectiveFTCData :
    EffectiveDerivativeBoundFTC quarticPrimitiveRaw quarticDerivativeRaw 0 1 where
  primitive_valid := RealFunRaw.exact_valid _
  primitive_domain_lower := trivial
  primitive_domain_upper := trivial
  choosePartition := fun eps => quarticEffectivePartitionOf eps
  chooseEndpointPrecision := fun _ => 0
  chooseBoundStage := fun _ => 0
  derivativeBound := quarticEffectiveDerivativeBound
  domain_at_partition := by
    intro eps i hi
    trivial
  localControl := by
    intro eps k hk
    let C := (quarticEffectivePartitionOf eps).cell k hk
    let B := quarticEffectiveDerivativeBound eps k hk
    exact {
      primitive_domain_lower := trivial
      primitive_domain_upper := trivial
      endpointPrecision := fun _ => 0
      endpoint_contained := by
        intro n
        dsimp [C, B, quarticEffectiveDerivativeBound]
        unfold quarticEffectiveBound RationalSubinterval.scaleBound
          endpointDifferenceInterval quarticPrimitiveRaw RealFunRaw.exact
        have hw : 0 <= C.width := by
          unfold RationalSubinterval.width
          have ho := C.ordered
          grind
        have hw' : 0 <=
            ((quarticEffectivePartitionOf eps).cell k hk).width := by
          dsimp [C] at hw
          exact hw
        simp only [QInterval.scaleByRat, if_pos hw']
        have hfactor :
            C.upper ^ 4 - C.lower ^ 4 = C.width *
              (C.upper ^ 3 + C.upper ^ 2 * C.lower +
                C.upper * C.lower ^ 2 + C.lower ^ 3) := by
          unfold RationalSubinterval.width
          grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        have hlower0 : 0 <= C.lower := C.lower_mem
        have hupper0 : 0 <= C.upper := Rat.le_trans hlower0 C.ordered
        have hlow : 4 * C.lower ^ 3 <=
            C.upper ^ 3 + C.upper ^ 2 * C.lower +
              C.upper * C.lower ^ 2 + C.lower ^ 3 := by
          have hp : 0 <= C.width *
              (C.upper ^ 2 + 2 * C.upper * C.lower + 3 * C.lower ^ 2) := by
            exact Rat.mul_nonneg hw (by
              exact Rat.add_nonneg (Rat.add_nonneg
                (Rat.pow_nonneg hupper0)
                (Rat.mul_nonneg (Rat.mul_nonneg
                  (by decide +kernel : (0 : Rat) <= 2) hupper0) hlower0))
                (Rat.mul_nonneg (by decide +kernel : (0 : Rat) <= 3)
                  (Rat.pow_nonneg hlower0)))
          unfold RationalSubinterval.width at hp
          grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        have hhigh : C.upper ^ 3 + C.upper ^ 2 * C.lower +
              C.upper * C.lower ^ 2 + C.lower ^ 3 <= 4 * C.upper ^ 3 := by
          have hp : 0 <= C.width *
              (3 * C.upper ^ 2 + 2 * C.upper * C.lower + C.lower ^ 2) := by
            exact Rat.mul_nonneg hw (by
              exact Rat.add_nonneg (Rat.add_nonneg
                (Rat.mul_nonneg (by decide +kernel : (0 : Rat) <= 3)
                  (Rat.pow_nonneg hupper0))
                (Rat.mul_nonneg (Rat.mul_nonneg
                  (by decide +kernel : (0 : Rat) <= 2) hupper0) hlower0))
                (Rat.pow_nonneg hlower0))
          unfold RationalSubinterval.width at hp
          grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        constructor
        · rw [hfactor]
          exact Rat.mul_le_mul_of_nonneg_left hlow hw
        · rw [hfactor]
          exact Rat.mul_le_mul_of_nonneg_left hhigh hw }
  endpointPrecision_agreement := by
    intro eps k hk n
    rfl
  riemann_width := by
    intro eps
    let N := quarticEffectivePartition eps
    have hN : 0 < N := by exact quarticEffectivePartition_pos eps
    have hbound : forall k (hk : k < N),
        (quarticEffectiveBound
          ((RationalPartition.uniform 0 1 N hN (by decide +kernel)).cell k hk) 0).width <=
          12 * mesh 0 1 N := by
      intro k hk
      let C := (RationalPartition.uniform 0 1 N hN
        (by decide +kernel : (0 : Rat) <= 1)).cell k hk
      change (quarticEffectiveBound C 0).width <= 12 * mesh 0 1 N
      rw [quarticEffectiveBound_width]
      have hw : C.width = mesh 0 1 N := by
        dsimp [C]
        exact RationalPartition.uniform_cell_width 0 1 N hN
          (by decide +kernel) k hk
      rw [hw]
      have hm := mesh_nonneg_of_le hN
        (by decide +kernel : (0 : Rat) <= 1)
      have hs : C.upper ^ 2 + C.upper * C.lower + C.lower ^ 2 <= 3 := by
        have hu := C.upper_mem
        have hl := C.lower_mem
        have ho := C.ordered
        have hu0 : 0 <= C.upper := Rat.le_trans hl ho
        have hu2 : C.upper ^ 2 <= 1 := by
          have h := Rat.mul_le_mul_of_nonneg_left hu hu0
          calc
            C.upper ^ 2 = C.upper * C.upper := by grind [Rat.pow_succ]
            _ <= C.upper * 1 := h
            _ = C.upper := by simp
            _ <= 1 := hu
        have hl2 : C.lower ^ 2 <= 1 := by
          have h1 := Rat.mul_le_mul_of_nonneg_left ho hl
          have h2 := Rat.mul_le_mul_of_nonneg_left hu hl
          calc
            C.lower ^ 2 = C.lower * C.lower := by grind [Rat.pow_succ]
            _ <= C.lower * C.upper := h1
            _ <= C.lower * 1 := h2
            _ = C.lower := by simp
            _ <= 1 := Rat.le_trans ho hu
        have hcross : C.upper * C.lower <= 1 := by
          exact Rat.le_trans
            (Rat.mul_le_mul_of_nonneg_left (Rat.le_trans ho hu) hu0) (by grind)
        grind
      calc
        4 * mesh 0 1 N * (C.upper ^ 2 + C.upper * C.lower + C.lower ^ 2) <=
            (4 * mesh 0 1 N) * 3 := by
              exact Rat.mul_le_mul_of_nonneg_left hs
                (Rat.mul_nonneg (by decide +kernel) hm)
        _ = 12 * mesh 0 1 N := by grind
    have hsum := RationalPartition.uniform_boundIntegralSum_width_le
      N hN (by decide +kernel : (0 : Rat) <= 1)
      (fun k hk => (quarticEffectiveDerivativeBound eps k hk).bound 0)
      (12 * mesh 0 1 N) hbound
    have hsum_bound :
        ((quarticEffectivePartitionOf eps).boundIntegralSum
          (fun k hk => (quarticEffectiveDerivativeBound eps k hk).bound 0)).width
          <= 12 * mesh 0 1 N := by
      change ((RationalPartition.uniform 0 1 N hN (by decide +kernel)).boundIntegralSum
          (fun k hk => (quarticEffectiveDerivativeBound eps k hk).bound 0)).width
          <= 12 * mesh 0 1 N
      have hpart : quarticEffectivePartitionOf eps =
          RationalPartition.uniform 0 1 N hN (by decide +kernel) := by
        unfold quarticEffectivePartitionOf
        congr
      cases hpart
      exact Rat.le_trans hsum (by grind)
    have hmesh : mesh 0 1 N = 1 / (N : Rat) := by
      unfold mesh
      rw [if_neg (Nat.ne_of_gt hN)]
      rw [Rat.div_def]
      grind
    have hden := FTC.one_div_den_succ_le_of_pos eps.property
    have hfinal : 12 * mesh 0 1 N <= eps.val := by
      rw [hmesh]
      dsimp [N, quarticEffectivePartition]
      have hcancel :
          (12 : Rat) * (1 / ((12 * (eps.val.den + 1) : Nat) : Rat)) =
            1 / ((eps.val.den + 1 : Nat) : Rat) := by
        rw [Rat.div_def, Rat.div_def, Rat.natCast_mul]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      rw [hcancel]
      exact hden
    exact Rat.le_trans hsum_bound hfinal
  endpoint_width := by
    intro eps
    simpa [endpointDifferenceInterval, quarticPrimitiveRaw, RealFunRaw.exact,
      QInterval.width, Rat.sub_self] using (Rat.le_of_lt eps.property)

theorem quarticEffectiveFTC_equiv_endpoint :
    quarticEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      quarticEffectiveFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact effectiveDerivativeBoundFTC quarticEffectiveFTCData

/-! ## Correctly scaled integral target: `∫₀¹ x² dx = 1/3`

The preceding polynomial certificates calibrate the derivative/secant
mechanism using `x^2`, `x^3`, and `x^4` as primitives.  For the actual
integral target, the primitive is `x^3/3` and the derivative is `x^2`. -/

def squareIntegralPrimitiveRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => x ^ 3 / 3)

def squareIntegralDerivativeRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => x ^ 2)

/-! The square primitive exposes the adjacent-interval endpoint law on an
arbitrary rational triple.  This is the polynomial counterpart of the affine
law in `Calculus.lean`; the effective-FTC value theorem below specializes it
to the unit interval. -/

noncomputable def squarePrimitiveEndpointDifference (a b : Rat) : RealCompute :=
  endpointDifferenceRaw squareIntegralPrimitiveRaw a b
    (endpointDifference_valid_of_fun_valid (RealFunRaw.exact_valid _) trivial trivial)

theorem squarePrimitiveEndpointDifference_adjacent_additive
    (a b c : Rat) :
    (squarePrimitiveEndpointDifference a b +
      squarePrimitiveEndpointDifference b c).Equiv
      (squarePrimitiveEndpointDifference a c) := by
  unfold squarePrimitiveEndpointDifference
  apply endpointDifferenceRaw_adjacent_additive
    (RealFunRaw.exact_valid _) trivial trivial trivial

def squareIntegralPartitionOf (eps : QPos) : RationalPartition 0 1 :=
  RationalPartition.uniform 0 1 (2 * (eps.val.den + 1))
    (by omega) (by decide +kernel)

def squareIntegralBound
    {a b : Rat} (C : RationalSubinterval a b) (_n : Nat) : QInterval :=
  { lo := C.lower ^ 2, hi := C.upper ^ 2 }

theorem squareIntegralBound_width
    {a b : Rat} (C : RationalSubinterval a b) (n : Nat) :
    (squareIntegralBound C n).width = C.width * (C.upper + C.lower) := by
  unfold squareIntegralBound RationalSubinterval.width QInterval.width
  grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

def squareIntegralDerivativeBound (eps : QPos) (k : Nat)
    (hk : k < (squareIntegralPartitionOf eps).pieces) :
    DerivativeBoundOnSubinterval squareIntegralDerivativeRaw
      ((squareIntegralPartitionOf eps).cell k hk) := by
  let C := (squareIntegralPartitionOf eps).cell k hk
  exact {
    bound := fun n => squareIntegralBound C n
    evalPrecision := fun n => n
    domain_on := fun x hx => trivial
    bound_ordered := fun n => by
      rw [squareIntegralBound_width]
      have hw : 0 <= C.width := by
        unfold RationalSubinterval.width
        grind [C.ordered]
      have hs : 0 <= C.upper + C.lower := by
        exact Rat.add_nonneg (Rat.le_trans C.lower_mem C.ordered) C.lower_mem
      exact Rat.mul_nonneg hw hs
    contains_values := fun n x hx => by
      unfold squareIntegralBound squareIntegralDerivativeRaw RealFunRaw.exact
        QInterval.ContainsInterval
      have hrange := cube_square_range C.lower_mem C.ordered hx.1 hx.2
      simpa [Rat.pow_succ] using hrange }

def squareIntegralEffectiveFTCData :
    EffectiveDerivativeBoundFTC squareIntegralPrimitiveRaw
      squareIntegralDerivativeRaw 0 1 where
  primitive_valid := RealFunRaw.exact_valid _
  primitive_domain_lower := trivial
  primitive_domain_upper := trivial
  choosePartition := fun eps => squareIntegralPartitionOf eps
  chooseEndpointPrecision := fun _ => 0
  chooseBoundStage := fun _ => 0
  derivativeBound := squareIntegralDerivativeBound
  domain_at_partition := by
    intro eps i hi
    trivial
  localControl := by
    intro eps k hk
    let C := (squareIntegralPartitionOf eps).cell k hk
    let B := squareIntegralDerivativeBound eps k hk
    exact {
      primitive_domain_lower := trivial
      primitive_domain_upper := trivial
      endpointPrecision := fun _ => 0
      endpoint_contained := by
        intro n
        dsimp [C, B, squareIntegralDerivativeBound]
        unfold squareIntegralBound RationalSubinterval.scaleBound
          endpointDifferenceInterval squareIntegralPrimitiveRaw RealFunRaw.exact
        have hw : 0 <= C.width := by
          unfold RationalSubinterval.width
          grind [C.ordered]
        have hw' : 0 <=
            ((squareIntegralPartitionOf eps).cell k hk).width := by
          dsimp [C] at hw
          exact hw
        simp only [QInterval.scaleByRat, if_pos hw']
        have hfactor : C.upper ^ 3 / 3 - C.lower ^ 3 / 3 =
            C.width * ((C.upper ^ 2 + C.upper * C.lower + C.lower ^ 2) / 3) := by
          unfold RationalSubinterval.width
          rw [Rat.div_def, Rat.div_def, Rat.div_def]
          grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        have hlower : 0 <= C.lower := C.lower_mem
        have hupper : 0 <= C.upper := Rat.le_trans hlower C.ordered
        have hlow : C.lower ^ 2 <=
            (C.upper ^ 2 + C.upper * C.lower + C.lower ^ 2) / 3 := by
          have hp : 0 <= C.width * (C.upper + 2 * C.lower) :=
            Rat.mul_nonneg hw (Rat.add_nonneg hupper
              (Rat.mul_nonneg (by decide +kernel : (0 : Rat) <= 2) hlower))
          unfold RationalSubinterval.width at hp
          rw [Rat.div_def]
          grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        have hhigh :
            (C.upper ^ 2 + C.upper * C.lower + C.lower ^ 2) / 3 <=
              C.upper ^ 2 := by
          have hp : 0 <= C.width * (2 * C.upper + C.lower) :=
            Rat.mul_nonneg hw (Rat.add_nonneg
              (Rat.mul_nonneg (by decide +kernel : (0 : Rat) <= 2) hupper)
              hlower)
          unfold RationalSubinterval.width at hp
          rw [Rat.div_def]
          grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        rw [hfactor]
        constructor
        · exact Rat.mul_le_mul_of_nonneg_left hlow hw
        · exact Rat.mul_le_mul_of_nonneg_left hhigh hw }
  endpointPrecision_agreement := by
    intro eps k hk n
    rfl
  riemann_width := by
    intro eps
    let N := 2 * (eps.val.den + 1)
    have hN : 0 < N := by omega
    have hbound : forall k (hk : k < N),
        (squareIntegralBound
          ((RationalPartition.uniform 0 1 N hN (by decide +kernel)).cell k hk) 0).width <=
          2 * mesh 0 1 N := by
      intro k hk
      let C := (RationalPartition.uniform 0 1 N hN
        (by decide +kernel : (0 : Rat) <= 1)).cell k hk
      change (squareIntegralBound C 0).width <= 2 * mesh 0 1 N
      rw [squareIntegralBound_width]
      have hw : C.width = mesh 0 1 N := by
        dsimp [C]
        exact RationalPartition.uniform_cell_width 0 1 N hN
          (by decide +kernel) k hk
      rw [hw]
      have hm := mesh_nonneg_of_le hN
        (by decide +kernel : (0 : Rat) <= 1)
      have hs : C.upper + C.lower <= 2 := by
        have hu := C.upper_mem
        have hl := C.lower_mem
        have ho := C.ordered
        grind
      calc
        mesh 0 1 N * (C.upper + C.lower) <= mesh 0 1 N * 2 :=
          Rat.mul_le_mul_of_nonneg_left hs hm
        _ = 2 * mesh 0 1 N := by grind
    have hsum := RationalPartition.uniform_boundIntegralSum_width_le
      N hN (by decide +kernel : (0 : Rat) <= 1)
      (fun k hk => (squareIntegralDerivativeBound eps k hk).bound 0)
      (2 * mesh 0 1 N) hbound
    have hsum_bound :
        ((squareIntegralPartitionOf eps).boundIntegralSum
          (fun k hk => (squareIntegralDerivativeBound eps k hk).bound 0)).width
          <= 2 * mesh 0 1 N := by
      change ((RationalPartition.uniform 0 1 N hN (by decide +kernel)).boundIntegralSum
          (fun k hk => (squareIntegralDerivativeBound eps k hk).bound 0)).width
          <= 2 * mesh 0 1 N
      have hpart : squareIntegralPartitionOf eps =
          RationalPartition.uniform 0 1 N hN (by decide +kernel) := by
        unfold squareIntegralPartitionOf
        congr
      cases hpart
      exact Rat.le_trans hsum (by grind)
    have hmesh : mesh 0 1 N = 1 / (N : Rat) := by
      unfold mesh
      rw [if_neg (Nat.ne_of_gt hN), Rat.div_def]
      grind
    have hden := FTC.one_div_den_succ_le_of_pos eps.property
    have hfinal : 2 * mesh 0 1 N <= eps.val := by
      rw [hmesh]
      dsimp [N]
      have hcancel :
          (2 : Rat) * (1 / ((2 * (eps.val.den + 1) : Nat) : Rat)) =
            1 / ((eps.val.den + 1 : Nat) : Rat) := by
        rw [Rat.div_def, Rat.div_def, Rat.natCast_mul]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      rw [hcancel]
      exact hden
    exact Rat.le_trans hsum_bound hfinal
  endpoint_width := by
    intro eps
    simpa [endpointDifferenceInterval, squareIntegralPrimitiveRaw,
      RealFunRaw.exact, QInterval.width, Rat.sub_self] using
      (Rat.le_of_lt eps.property)

theorem squareIntegralEffectiveFTC_equiv_endpoint :
    squareIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      squareIntegralEffectiveFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact effectiveDerivativeBoundFTC squareIntegralEffectiveFTCData

/-! ## Correctly scaled cubic integral: `∫₀¹ x³ dx = 1/4` -/

def cubicIntegralPrimitiveRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => x ^ 4 / 4)

def cubicIntegralDerivativeRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => x ^ 3)

noncomputable def cubicPrimitiveEndpointDifference (a b : Rat) : RealCompute :=
  endpointDifferenceRaw cubicIntegralPrimitiveRaw a b
    (endpointDifference_valid_of_fun_valid (RealFunRaw.exact_valid _) trivial trivial)

theorem cubicPrimitiveEndpointDifference_adjacent_additive
    (a b c : Rat) :
    (cubicPrimitiveEndpointDifference a b +
      cubicPrimitiveEndpointDifference b c).Equiv
      (cubicPrimitiveEndpointDifference a c) := by
  unfold cubicPrimitiveEndpointDifference
  apply endpointDifferenceRaw_adjacent_additive
    (RealFunRaw.exact_valid _) trivial trivial trivial

def cubicIntegralPartitionOf (eps : QPos) : RationalPartition 0 1 :=
  RationalPartition.uniform 0 1 (3 * (eps.val.den + 1))
    (by omega) (by decide +kernel)

def cubicIntegralBound
    {a b : Rat} (C : RationalSubinterval a b) (_n : Nat) : QInterval :=
  { lo := C.lower ^ 3, hi := C.upper ^ 3 }

theorem cubicIntegralBound_width
    {a b : Rat} (C : RationalSubinterval a b) (n : Nat) :
    (cubicIntegralBound C n).width =
      C.width * (C.upper ^ 2 + C.upper * C.lower + C.lower ^ 2) := by
  unfold cubicIntegralBound RationalSubinterval.width QInterval.width
  grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

def cubicIntegralDerivativeBound (eps : QPos) (k : Nat)
    (hk : k < (cubicIntegralPartitionOf eps).pieces) :
    DerivativeBoundOnSubinterval cubicIntegralDerivativeRaw
      ((cubicIntegralPartitionOf eps).cell k hk) := by
  let C := (cubicIntegralPartitionOf eps).cell k hk
  exact {
    bound := fun n => cubicIntegralBound C n
    evalPrecision := fun n => n
    domain_on := fun x hx => trivial
    bound_ordered := fun n => by
      rw [cubicIntegralBound_width]
      have hw : 0 <= C.width := by
        unfold RationalSubinterval.width
        grind [C.ordered]
      have hs : 0 <= C.upper ^ 2 + C.upper * C.lower + C.lower ^ 2 := by
        exact Rat.add_nonneg (Rat.add_nonneg
          (Rat.pow_nonneg (Rat.le_trans C.lower_mem C.ordered))
          (Rat.mul_nonneg (Rat.le_trans C.lower_mem C.ordered) C.lower_mem))
          (Rat.pow_nonneg C.lower_mem)
      exact Rat.mul_nonneg hw hs
    contains_values := fun n x hx => by
      unfold cubicIntegralBound cubicIntegralDerivativeRaw RealFunRaw.exact
        QInterval.ContainsInterval
      have hrange := quartic_cube_range C.lower_mem C.ordered hx.1 hx.2
      simpa [Rat.pow_succ] using hrange }

def cubicIntegralEffectiveFTCData :
    EffectiveDerivativeBoundFTC cubicIntegralPrimitiveRaw
      cubicIntegralDerivativeRaw 0 1 where
  primitive_valid := RealFunRaw.exact_valid _
  primitive_domain_lower := trivial
  primitive_domain_upper := trivial
  choosePartition := fun eps => cubicIntegralPartitionOf eps
  chooseEndpointPrecision := fun _ => 0
  chooseBoundStage := fun _ => 0
  derivativeBound := cubicIntegralDerivativeBound
  domain_at_partition := by
    intro eps i hi
    trivial
  localControl := by
    intro eps k hk
    let C := (cubicIntegralPartitionOf eps).cell k hk
    let B := cubicIntegralDerivativeBound eps k hk
    exact {
      primitive_domain_lower := trivial
      primitive_domain_upper := trivial
      endpointPrecision := fun _ => 0
      endpoint_contained := by
        intro n
        dsimp [C, B, cubicIntegralDerivativeBound]
        unfold cubicIntegralBound RationalSubinterval.scaleBound
          endpointDifferenceInterval cubicIntegralPrimitiveRaw RealFunRaw.exact
        have hw : 0 <= C.width := by
          unfold RationalSubinterval.width
          grind [C.ordered]
        have hw' : 0 <=
            ((cubicIntegralPartitionOf eps).cell k hk).width := by
          dsimp [C] at hw
          exact hw
        simp only [QInterval.scaleByRat, if_pos hw']
        have hfactor : C.upper ^ 4 / 4 - C.lower ^ 4 / 4 =
            C.width * ((C.upper ^ 3 + C.upper ^ 2 * C.lower +
              C.upper * C.lower ^ 2 + C.lower ^ 3) / 4) := by
          unfold RationalSubinterval.width
          rw [Rat.div_def, Rat.div_def, Rat.div_def]
          grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        have hlower : 0 <= C.lower := C.lower_mem
        have hupper : 0 <= C.upper := Rat.le_trans hlower C.ordered
        have hlow : C.lower ^ 3 <=
            (C.upper ^ 3 + C.upper ^ 2 * C.lower +
              C.upper * C.lower ^ 2 + C.lower ^ 3) / 4 := by
          have hp : 0 <= C.width *
              (C.upper ^ 2 + 2 * C.upper * C.lower + 3 * C.lower ^ 2) :=
            Rat.mul_nonneg hw (by
              exact Rat.add_nonneg (Rat.add_nonneg
                (Rat.pow_nonneg hupper)
                (Rat.mul_nonneg (Rat.mul_nonneg
                  (by decide +kernel : (0 : Rat) <= 2) hupper) hlower))
                (Rat.mul_nonneg (by decide +kernel : (0 : Rat) <= 3)
                  (Rat.pow_nonneg hlower)))
          unfold RationalSubinterval.width at hp
          rw [Rat.div_def]
          grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        have hhigh :
            (C.upper ^ 3 + C.upper ^ 2 * C.lower +
              C.upper * C.lower ^ 2 + C.lower ^ 3) / 4 <= C.upper ^ 3 := by
          have hp : 0 <= C.width *
              (3 * C.upper ^ 2 + 2 * C.upper * C.lower + C.lower ^ 2) :=
            Rat.mul_nonneg hw (by
              exact Rat.add_nonneg (Rat.add_nonneg
                (Rat.mul_nonneg (by decide +kernel : (0 : Rat) <= 3)
                  (Rat.pow_nonneg hupper))
                (Rat.mul_nonneg (Rat.mul_nonneg
                  (by decide +kernel : (0 : Rat) <= 2) hupper) hlower))
                (Rat.pow_nonneg hlower))
          unfold RationalSubinterval.width at hp
          rw [Rat.div_def]
          grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        rw [hfactor]
        constructor
        · exact Rat.mul_le_mul_of_nonneg_left hlow hw
        · exact Rat.mul_le_mul_of_nonneg_left hhigh hw }
  endpointPrecision_agreement := by
    intro eps k hk n
    rfl
  riemann_width := by
    intro eps
    let N := 3 * (eps.val.den + 1)
    have hN : 0 < N := by omega
    have hbound : forall k (hk : k < N),
        (cubicIntegralBound
          ((RationalPartition.uniform 0 1 N hN (by decide +kernel)).cell k hk) 0).width <=
          3 * mesh 0 1 N := by
      intro k hk
      let C := (RationalPartition.uniform 0 1 N hN
        (by decide +kernel : (0 : Rat) <= 1)).cell k hk
      change (cubicIntegralBound C 0).width <= 3 * mesh 0 1 N
      rw [cubicIntegralBound_width]
      have hw : C.width = mesh 0 1 N := by
        dsimp [C]
        exact RationalPartition.uniform_cell_width 0 1 N hN
          (by decide +kernel) k hk
      rw [hw]
      have hm := mesh_nonneg_of_le hN
        (by decide +kernel : (0 : Rat) <= 1)
      have hs : C.upper ^ 2 + C.upper * C.lower + C.lower ^ 2 <= 3 := by
        have hu := C.upper_mem
        have hl := C.lower_mem
        have ho := C.ordered
        have hu0 : 0 <= C.upper := Rat.le_trans hl ho
        have hu2 : C.upper ^ 2 <= 1 := by
          have h := Rat.mul_le_mul_of_nonneg_left hu hu0
          calc
            C.upper ^ 2 = C.upper * C.upper := by grind [Rat.pow_succ]
            _ <= C.upper * 1 := h
            _ = C.upper := by simp
            _ <= 1 := hu
        have hl2 : C.lower ^ 2 <= 1 := by
          have h1 := Rat.mul_le_mul_of_nonneg_left ho hl
          have h2 := Rat.mul_le_mul_of_nonneg_left hu hl
          calc
            C.lower ^ 2 = C.lower * C.lower := by grind [Rat.pow_succ]
            _ <= C.lower * C.upper := h1
            _ <= C.lower * 1 := h2
            _ = C.lower := by simp
            _ <= 1 := Rat.le_trans ho hu
        have hcross : C.upper * C.lower <= 1 := by
          have hlow1 : C.lower <= 1 := Rat.le_trans ho hu
          exact Rat.le_trans
            (Rat.mul_le_mul_of_nonneg_left hlow1 hu0) (by grind)
        grind
      calc
        mesh 0 1 N * (C.upper ^ 2 + C.upper * C.lower + C.lower ^ 2) <=
            mesh 0 1 N * 3 := Rat.mul_le_mul_of_nonneg_left hs hm
        _ = 3 * mesh 0 1 N := by grind
    have hsum := RationalPartition.uniform_boundIntegralSum_width_le
      N hN (by decide +kernel : (0 : Rat) <= 1)
      (fun k hk => (cubicIntegralDerivativeBound eps k hk).bound 0)
      (3 * mesh 0 1 N) hbound
    have hsum_bound :
        ((cubicIntegralPartitionOf eps).boundIntegralSum
          (fun k hk => (cubicIntegralDerivativeBound eps k hk).bound 0)).width
          <= 3 * mesh 0 1 N := by
      change ((RationalPartition.uniform 0 1 N hN (by decide +kernel)).boundIntegralSum
          (fun k hk => (cubicIntegralDerivativeBound eps k hk).bound 0)).width
          <= 3 * mesh 0 1 N
      have hpart : cubicIntegralPartitionOf eps =
          RationalPartition.uniform 0 1 N hN (by decide +kernel) := by
        unfold cubicIntegralPartitionOf
        congr
      cases hpart
      exact Rat.le_trans hsum (by grind)
    have hmesh : mesh 0 1 N = 1 / (N : Rat) := by
      unfold mesh
      rw [if_neg (Nat.ne_of_gt hN), Rat.div_def]
      grind
    have hden := FTC.one_div_den_succ_le_of_pos eps.property
    have hfinal : 3 * mesh 0 1 N <= eps.val := by
      rw [hmesh]
      dsimp [N]
      have hcancel :
          (3 : Rat) * (1 / ((3 * (eps.val.den + 1) : Nat) : Rat)) =
            1 / ((eps.val.den + 1 : Nat) : Rat) := by
        rw [Rat.div_def, Rat.div_def, Rat.natCast_mul]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      rw [hcancel]
      exact hden
    exact Rat.le_trans hsum_bound hfinal
  endpoint_width := by
    intro eps
    simpa [endpointDifferenceInterval, cubicIntegralPrimitiveRaw,
      RealFunRaw.exact, QInterval.width, Rat.sub_self] using
      (Rat.le_of_lt eps.property)

theorem cubicIntegralEffectiveFTC_equiv_endpoint :
    cubicIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      cubicIntegralEffectiveFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact effectiveDerivativeBoundFTC cubicIntegralEffectiveFTCData

/-! A reusable finite power-range lemma for the remaining monomial targets. -/

theorem nonneg_power_range {n : Nat} {a b x : Rat}
    (ha : 0 <= a) (hab : a <= b) (hx : a <= x) (hxb : x <= b) :
    a ^ n <= x ^ n ∧ x ^ n <= b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hxa : 0 <= x := Rat.le_trans ha hx
      have hba : 0 <= b := Rat.le_trans hxa hxb
      have hpow : a ^ n <= x ^ n ∧ x ^ n <= b ^ n := ih
      rw [Rat.pow_succ, Rat.pow_succ, Rat.pow_succ]
      constructor
      · calc
          a ^ n * a <= x ^ n * a :=
            Rat.mul_le_mul_of_nonneg_right hpow.1 ha
          _ <= x ^ n * x :=
            Rat.mul_le_mul_of_nonneg_left hx (Rat.pow_nonneg hxa)
      · calc
          x ^ n * x <= b ^ n * x :=
            Rat.mul_le_mul_of_nonneg_right hpow.2 hxa
          _ <= b ^ n * b :=
            Rat.mul_le_mul_of_nonneg_left hxb (Rat.pow_nonneg hba)

/-! ## Correctly scaled quartic integral: `∫₀¹ x⁴ dx = 1/5` -/

def quarticIntegralPrimitiveRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => x ^ 5 / 5)

def quarticIntegralDerivativeRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => x ^ 4)

noncomputable def quarticPrimitiveEndpointDifference (a b : Rat) : RealCompute :=
  endpointDifferenceRaw quarticIntegralPrimitiveRaw a b
    (endpointDifference_valid_of_fun_valid (RealFunRaw.exact_valid _) trivial trivial)

theorem quarticPrimitiveEndpointDifference_adjacent_additive
    (a b c : Rat) :
    (quarticPrimitiveEndpointDifference a b +
      quarticPrimitiveEndpointDifference b c).Equiv
      (quarticPrimitiveEndpointDifference a c) := by
  unfold quarticPrimitiveEndpointDifference
  apply endpointDifferenceRaw_adjacent_additive
    (RealFunRaw.exact_valid _) trivial trivial trivial

def quarticIntegralPartitionOf (eps : QPos) : RationalPartition 0 1 :=
  RationalPartition.uniform 0 1 (4 * (eps.val.den + 1))
    (by omega) (by decide +kernel)

def quarticIntegralBound
    {a b : Rat} (C : RationalSubinterval a b) (_n : Nat) : QInterval :=
  { lo := C.lower ^ 4, hi := C.upper ^ 4 }

theorem quarticIntegralBound_width
    {a b : Rat} (C : RationalSubinterval a b) (n : Nat) :
    (quarticIntegralBound C n).width = C.width *
      (C.upper ^ 3 + C.upper ^ 2 * C.lower +
        C.upper * C.lower ^ 2 + C.lower ^ 3) := by
  unfold quarticIntegralBound RationalSubinterval.width QInterval.width
  grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

def quarticIntegralDerivativeBound (eps : QPos) (k : Nat)
    (hk : k < (quarticIntegralPartitionOf eps).pieces) :
    DerivativeBoundOnSubinterval quarticIntegralDerivativeRaw
      ((quarticIntegralPartitionOf eps).cell k hk) := by
  let C := (quarticIntegralPartitionOf eps).cell k hk
  exact {
    bound := fun n => quarticIntegralBound C n
    evalPrecision := fun n => n
    domain_on := fun x hx => trivial
    bound_ordered := fun n => by
      rw [quarticIntegralBound_width]
      have hw : 0 <= C.width := by
        unfold RationalSubinterval.width
        grind [C.ordered]
      have h0 : 0 <= C.lower := C.lower_mem
      have h1 : 0 <= C.upper := Rat.le_trans h0 C.ordered
      have hs : 0 <= C.upper ^ 3 + C.upper ^ 2 * C.lower +
          C.upper * C.lower ^ 2 + C.lower ^ 3 := by
        exact Rat.add_nonneg (Rat.add_nonneg
          (Rat.add_nonneg (Rat.pow_nonneg h1)
            (Rat.mul_nonneg (Rat.pow_nonneg h1) h0))
          (Rat.mul_nonneg h1 (Rat.pow_nonneg h0))) (Rat.pow_nonneg h0)
      exact Rat.mul_nonneg hw hs
    contains_values := fun n x hx => by
      unfold quarticIntegralBound quarticIntegralDerivativeRaw RealFunRaw.exact
        QInterval.ContainsInterval
      have hrange := nonneg_power_range (n := 4)
        C.lower_mem C.ordered hx.1 hx.2
      simpa using hrange }

def quarticIntegralEffectiveFTCData :
    EffectiveDerivativeBoundFTC quarticIntegralPrimitiveRaw
      quarticIntegralDerivativeRaw 0 1 where
  primitive_valid := RealFunRaw.exact_valid _
  primitive_domain_lower := trivial
  primitive_domain_upper := trivial
  choosePartition := fun eps => quarticIntegralPartitionOf eps
  chooseEndpointPrecision := fun _ => 0
  chooseBoundStage := fun _ => 0
  derivativeBound := quarticIntegralDerivativeBound
  domain_at_partition := by
    intro eps i hi
    trivial
  localControl := by
    intro eps k hk
    let C := (quarticIntegralPartitionOf eps).cell k hk
    let B := quarticIntegralDerivativeBound eps k hk
    exact {
      primitive_domain_lower := trivial
      primitive_domain_upper := trivial
      endpointPrecision := fun _ => 0
      endpoint_contained := by
        intro n
        dsimp [C, B, quarticIntegralDerivativeBound]
        unfold quarticIntegralBound RationalSubinterval.scaleBound
          endpointDifferenceInterval quarticIntegralPrimitiveRaw RealFunRaw.exact
        have hw : 0 <= C.width := by
          unfold RationalSubinterval.width
          grind [C.ordered]
        have hw' : 0 <=
            ((quarticIntegralPartitionOf eps).cell k hk).width := by
          dsimp [C] at hw
          exact hw
        simp only [QInterval.scaleByRat, if_pos hw']
        have hfactor : C.upper ^ 5 / 5 - C.lower ^ 5 / 5 =
            C.width * ((C.upper ^ 4 + C.upper ^ 3 * C.lower +
              C.upper ^ 2 * C.lower ^ 2 + C.upper * C.lower ^ 3 +
              C.lower ^ 4) / 5) := by
          unfold RationalSubinterval.width
          rw [Rat.div_def, Rat.div_def, Rat.div_def]
          grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        have h0 : 0 <= C.lower := C.lower_mem
        have h1 : 0 <= C.upper := Rat.le_trans h0 C.ordered
        have hlow : C.lower ^ 4 <=
            (C.upper ^ 4 + C.upper ^ 3 * C.lower +
              C.upper ^ 2 * C.lower ^ 2 + C.upper * C.lower ^ 3 +
              C.lower ^ 4) / 5 := by
          have hp : 0 <= C.width *
              (C.upper ^ 3 + 2 * C.upper ^ 2 * C.lower +
                3 * C.upper * C.lower ^ 2 + 4 * C.lower ^ 3) := by
            exact Rat.mul_nonneg hw (by
              exact Rat.add_nonneg (Rat.add_nonneg
                (Rat.add_nonneg (Rat.pow_nonneg h1)
                  (Rat.mul_nonneg (Rat.mul_nonneg
                    (by decide +kernel : (0 : Rat) <= 2)
                    (Rat.pow_nonneg h1)) h0))
                (Rat.mul_nonneg (Rat.mul_nonneg
                  (by decide +kernel : (0 : Rat) <= 3) h1)
                  (Rat.pow_nonneg h0)))
                (Rat.mul_nonneg (by decide +kernel : (0 : Rat) <= 4)
                  (Rat.pow_nonneg h0)))
          unfold RationalSubinterval.width at hp
          rw [Rat.div_def]
          grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        have hhigh :
            (C.upper ^ 4 + C.upper ^ 3 * C.lower +
              C.upper ^ 2 * C.lower ^ 2 + C.upper * C.lower ^ 3 +
              C.lower ^ 4) / 5 <= C.upper ^ 4 := by
          have hp : 0 <= C.width *
              (4 * C.upper ^ 3 + 3 * C.upper ^ 2 * C.lower +
                2 * C.upper * C.lower ^ 2 + C.lower ^ 3) := by
            exact Rat.mul_nonneg hw (by
              exact Rat.add_nonneg (Rat.add_nonneg
                (Rat.add_nonneg (Rat.mul_nonneg
                  (by decide +kernel : (0 : Rat) <= 4) (Rat.pow_nonneg h1))
                  (Rat.mul_nonneg (Rat.mul_nonneg
                    (by decide +kernel : (0 : Rat) <= 3)
                    (Rat.pow_nonneg h1)) h0))
                (Rat.mul_nonneg (Rat.mul_nonneg
                  (by decide +kernel : (0 : Rat) <= 2) h1)
                  (Rat.pow_nonneg h0))) (Rat.pow_nonneg h0))
          unfold RationalSubinterval.width at hp
          rw [Rat.div_def]
          grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        rw [hfactor]
        constructor
        · exact Rat.mul_le_mul_of_nonneg_left hlow hw
        · exact Rat.mul_le_mul_of_nonneg_left hhigh hw }
  endpointPrecision_agreement := by
    intro eps k hk n
    rfl
  riemann_width := by
    intro eps
    let N := 4 * (eps.val.den + 1)
    have hN : 0 < N := by omega
    have hbound : forall k (hk : k < N),
        (quarticIntegralBound
          ((RationalPartition.uniform 0 1 N hN (by decide +kernel)).cell k hk) 0).width <=
          4 * mesh 0 1 N := by
      intro k hk
      let C := (RationalPartition.uniform 0 1 N hN
        (by decide +kernel : (0 : Rat) <= 1)).cell k hk
      change (quarticIntegralBound C 0).width <= 4 * mesh 0 1 N
      rw [quarticIntegralBound_width]
      have hw : C.width = mesh 0 1 N := by
        dsimp [C]
        exact RationalPartition.uniform_cell_width 0 1 N hN
          (by decide +kernel) k hk
      rw [hw]
      have hm := mesh_nonneg_of_le hN
        (by decide +kernel : (0 : Rat) <= 1)
      have hs : C.upper ^ 3 + C.upper ^ 2 * C.lower +
          C.upper * C.lower ^ 2 + C.lower ^ 3 <= 4 := by
        have hu := C.upper_mem
        have hl := C.lower_mem
        have ho := C.ordered
        have hu0 : 0 <= C.upper := Rat.le_trans hl ho
        have hu2 := (nonneg_power_range (n := 2)
          (a := C.upper) (b := 1) (x := C.upper)
          hu0 hu (by exact Rat.le_refl) hu).2
        have hl2 := (nonneg_power_range (n := 2)
          (a := C.lower) (b := 1) (x := C.lower)
          hl (Rat.le_trans ho hu) (by exact Rat.le_refl)
          (Rat.le_trans ho hu)).2
        have hu3 := (nonneg_power_range (n := 3)
          (a := C.upper) (b := 1) (x := C.upper)
          hu0 hu (by exact Rat.le_refl) hu).2
        have hl3 := (nonneg_power_range (n := 3)
          (a := C.lower) (b := 1) (x := C.lower)
          hl (Rat.le_trans ho hu) (by exact Rat.le_refl)
          (Rat.le_trans ho hu)).2
        have hterm2 : C.upper ^ 2 * C.lower <= 1 := by
          calc
            C.upper ^ 2 * C.lower <= 1 * C.lower :=
              Rat.mul_le_mul_of_nonneg_right hu2 hl
            _ = C.lower := by simp
            _ <= 1 := Rat.le_trans ho hu
        have hterm3 : C.upper * C.lower ^ 2 <= 1 := by
          calc
            C.upper * C.lower ^ 2 <= C.upper * 1 :=
              Rat.mul_le_mul_of_nonneg_left hl2 hu0
            _ = C.upper := by simp
            _ <= 1 := hu
        grind
      calc
        mesh 0 1 N * (C.upper ^ 3 + C.upper ^ 2 * C.lower +
            C.upper * C.lower ^ 2 + C.lower ^ 3) <= mesh 0 1 N * 4 :=
          Rat.mul_le_mul_of_nonneg_left hs hm
        _ = 4 * mesh 0 1 N := by grind
    have hsum := RationalPartition.uniform_boundIntegralSum_width_le
      N hN (by decide +kernel : (0 : Rat) <= 1)
      (fun k hk => (quarticIntegralDerivativeBound eps k hk).bound 0)
      (4 * mesh 0 1 N) hbound
    have hsum_bound :
        ((quarticIntegralPartitionOf eps).boundIntegralSum
          (fun k hk => (quarticIntegralDerivativeBound eps k hk).bound 0)).width
          <= 4 * mesh 0 1 N := by
      change ((RationalPartition.uniform 0 1 N hN (by decide +kernel)).boundIntegralSum
          (fun k hk => (quarticIntegralDerivativeBound eps k hk).bound 0)).width
          <= 4 * mesh 0 1 N
      have hpart : quarticIntegralPartitionOf eps =
          RationalPartition.uniform 0 1 N hN (by decide +kernel) := by
        unfold quarticIntegralPartitionOf
        congr
      cases hpart
      exact Rat.le_trans hsum (by grind)
    have hmesh : mesh 0 1 N = 1 / (N : Rat) := by
      unfold mesh
      rw [if_neg (Nat.ne_of_gt hN), Rat.div_def]
      grind
    have hden := FTC.one_div_den_succ_le_of_pos eps.property
    have hfinal : 4 * mesh 0 1 N <= eps.val := by
      rw [hmesh]
      dsimp [N]
      have hcancel :
          (4 : Rat) * (1 / ((4 * (eps.val.den + 1) : Nat) : Rat)) =
            1 / ((eps.val.den + 1 : Nat) : Rat) := by
        rw [Rat.div_def, Rat.div_def, Rat.natCast_mul]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      rw [hcancel]
      exact hden
    exact Rat.le_trans hsum_bound hfinal
  endpoint_width := by
    intro eps
    simpa [endpointDifferenceInterval, quarticIntegralPrimitiveRaw,
      RealFunRaw.exact, QInterval.width, Rat.sub_self] using
      (Rat.le_of_lt eps.property)

theorem quarticIntegralEffectiveFTC_equiv_endpoint :
    quarticIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      quarticIntegralEffectiveFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact effectiveDerivativeBoundFTC quarticIntegralEffectiveFTCData

theorem quarticIntegralEffectiveFTC_equiv_one_fifth :
    quarticIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealCompute.ofRat (1 / 5)) := by
  let H := quarticIntegralEffectiveFTCData.toDerivativeBoundFTC
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  have hover := H.overlap (precisionAtStage n)
  change QInterval.Overlaps
    (H.boundedIntegralCompute n) { lo := 1 / 5, hi := 1 / 5 }
  have hzero : (1 / 5 : Rat) - 0 / 5 = 1 / 5 := by grind
  simpa [H, DerivativeBoundFTC.boundedIntegralCompute,
    DerivativeBoundFTC.boundedIntegralInterval,
    DerivativeBoundFTC.endpointInterval, endpointDifferenceInterval,
    quarticIntegralPrimitiveRaw, RealFunRaw.exact, Rat.pow_succ, hzero] using hover

/-! Exact endpoint anchor for the next monomial target. -/

def fifthIntegralPrimitiveRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => x ^ 6 / 6)

noncomputable def fifthPrimitiveEndpointDifference (a b : Rat) : RealCompute :=
  endpointDifferenceRaw fifthIntegralPrimitiveRaw a b
    (endpointDifference_valid_of_fun_valid (RealFunRaw.exact_valid _) trivial trivial)

theorem fifthPrimitiveEndpointDifference_adjacent_additive
    (a b c : Rat) :
    (fifthPrimitiveEndpointDifference a b +
      fifthPrimitiveEndpointDifference b c).Equiv
      (fifthPrimitiveEndpointDifference a c) := by
  unfold fifthPrimitiveEndpointDifference
  apply endpointDifferenceRaw_adjacent_additive
    (RealFunRaw.exact_valid _) trivial trivial trivial

theorem fifthIntegralEndpointInterval_eq_one_sixth (n : Nat) :
    endpointDifferenceInterval fifthIntegralPrimitiveRaw 0 1 n =
      { lo := 1 / 6, hi := 1 / 6 } := by
  unfold endpointDifferenceInterval fifthIntegralPrimitiveRaw RealFunRaw.exact
  simp [Rat.pow_succ]
  grind

theorem fifthPowerSecantAverage_range {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) :
    a ^ 5 <=
        (b ^ 5 + b ^ 4 * a + b ^ 3 * a ^ 2 +
          b ^ 2 * a ^ 3 + b * a ^ 4 + a ^ 5) / 6 ∧
      (b ^ 5 + b ^ 4 * a + b ^ 3 * a ^ 2 +
          b ^ 2 * a ^ 3 + b * a ^ 4 + a ^ 5) / 6 <= b ^ 5 := by
  have hb : 0 <= b := Rat.le_trans ha hab
  have hwidth : 0 <= b - a := by grind
  have hlow : 0 <= (b - a) *
      (b ^ 4 + 2 * b ^ 3 * a + 3 * b ^ 2 * a ^ 2 +
        4 * b * a ^ 3 + 5 * a ^ 4) := by
    exact Rat.mul_nonneg hwidth (by
      exact Rat.add_nonneg (Rat.add_nonneg
        (Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg hb)
          (Rat.mul_nonneg (Rat.mul_nonneg
            (by decide +kernel : (0 : Rat) <= 2) (Rat.pow_nonneg hb)) ha))
          (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel : (0 : Rat) <= 3)
            (Rat.pow_nonneg hb)) (Rat.pow_nonneg ha)))
        (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel : (0 : Rat) <= 4)
          hb) (Rat.pow_nonneg ha)))
        (Rat.mul_nonneg (by decide +kernel : (0 : Rat) <= 5)
          (Rat.pow_nonneg ha)))
  have hhigh : 0 <= (b - a) *
      (5 * b ^ 4 + 4 * b ^ 3 * a + 3 * b ^ 2 * a ^ 2 +
        2 * b * a ^ 3 + a ^ 4) := by
    exact Rat.mul_nonneg hwidth (by
      exact Rat.add_nonneg (Rat.add_nonneg
        (Rat.add_nonneg (Rat.add_nonneg (Rat.mul_nonneg
          (by decide +kernel : (0 : Rat) <= 5) (Rat.pow_nonneg hb))
          (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel : (0 : Rat) <= 4)
            (Rat.pow_nonneg hb)) ha))
          (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel : (0 : Rat) <= 3)
            (Rat.pow_nonneg hb)) (Rat.pow_nonneg ha)))
        (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel : (0 : Rat) <= 2)
          hb) (Rat.pow_nonneg ha))) (Rat.pow_nonneg ha))
  constructor
  · rw [Rat.div_def]
    grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  · rw [Rat.div_def]
    grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]

def fifthIntegralDerivativeRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => x ^ 5)

def fifthIntegralPartitionOf (eps : QPos) : RationalPartition 0 1 :=
  RationalPartition.uniform 0 1 (5 * (eps.val.den + 1))
    (by omega) (by decide +kernel)

def fifthIntegralBound
    {a b : Rat} (C : RationalSubinterval a b) (_n : Nat) : QInterval :=
  { lo := C.lower ^ 5, hi := C.upper ^ 5 }

theorem fifthIntegralBound_width
    {a b : Rat} (C : RationalSubinterval a b) (n : Nat) :
    (fifthIntegralBound C n).width = C.width *
      (C.upper ^ 4 + C.upper ^ 3 * C.lower + C.upper ^ 2 * C.lower ^ 2 +
        C.upper * C.lower ^ 3 + C.lower ^ 4) := by
  unfold fifthIntegralBound RationalSubinterval.width QInterval.width
  grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

def fifthIntegralDerivativeBound (eps : QPos) (k : Nat)
    (hk : k < (fifthIntegralPartitionOf eps).pieces) :
    DerivativeBoundOnSubinterval fifthIntegralDerivativeRaw
      ((fifthIntegralPartitionOf eps).cell k hk) := by
  let C := (fifthIntegralPartitionOf eps).cell k hk
  exact {
    bound := fun n => fifthIntegralBound C n
    evalPrecision := fun n => n
    domain_on := fun x hx => trivial
    bound_ordered := fun n => by
      rw [fifthIntegralBound_width]
      have hw : 0 <= C.width := by
        unfold RationalSubinterval.width
        grind [C.ordered]
      have h0 : 0 <= C.lower := C.lower_mem
      have h1 : 0 <= C.upper := Rat.le_trans h0 C.ordered
      have hs : 0 <= C.upper ^ 4 + C.upper ^ 3 * C.lower +
          C.upper ^ 2 * C.lower ^ 2 + C.upper * C.lower ^ 3 + C.lower ^ 4 := by
        exact Rat.add_nonneg (Rat.add_nonneg
          (Rat.add_nonneg (Rat.add_nonneg (Rat.pow_nonneg h1)
            (Rat.mul_nonneg (Rat.pow_nonneg h1) h0))
            (Rat.mul_nonneg (Rat.pow_nonneg h1) (Rat.pow_nonneg h0)))
          (Rat.mul_nonneg h1 (Rat.pow_nonneg h0))) (Rat.pow_nonneg h0)
      exact Rat.mul_nonneg hw hs
    contains_values := fun n x hx => by
      unfold fifthIntegralBound fifthIntegralDerivativeRaw RealFunRaw.exact
        QInterval.ContainsInterval
      have hrange := nonneg_power_range (n := 5)
        C.lower_mem C.ordered hx.1 hx.2
      simpa using hrange }

def fifthIntegralEffectiveFTCData :
    EffectiveDerivativeBoundFTC fifthIntegralPrimitiveRaw
      fifthIntegralDerivativeRaw 0 1 where
  primitive_valid := RealFunRaw.exact_valid _
  primitive_domain_lower := trivial
  primitive_domain_upper := trivial
  choosePartition := fun eps => fifthIntegralPartitionOf eps
  chooseEndpointPrecision := fun _ => 0
  chooseBoundStage := fun _ => 0
  derivativeBound := fifthIntegralDerivativeBound
  domain_at_partition := by
    intro eps i hi
    trivial
  localControl := by
    intro eps k hk
    let C := (fifthIntegralPartitionOf eps).cell k hk
    let B := fifthIntegralDerivativeBound eps k hk
    exact {
      primitive_domain_lower := trivial
      primitive_domain_upper := trivial
      endpointPrecision := fun _ => 0
      endpoint_contained := by
        intro n
        dsimp [C, B, fifthIntegralDerivativeBound]
        unfold fifthIntegralBound RationalSubinterval.scaleBound
          endpointDifferenceInterval fifthIntegralPrimitiveRaw RealFunRaw.exact
        have hw : 0 <= C.width := by
          unfold RationalSubinterval.width
          grind [C.ordered]
        have hw' : 0 <=
            ((fifthIntegralPartitionOf eps).cell k hk).width := by
          dsimp [C] at hw
          exact hw
        simp only [QInterval.scaleByRat, if_pos hw']
        have hfactor : C.upper ^ 6 / 6 - C.lower ^ 6 / 6 =
            C.width * ((C.upper ^ 5 + C.upper ^ 4 * C.lower +
              C.upper ^ 3 * C.lower ^ 2 + C.upper ^ 2 * C.lower ^ 3 +
              C.upper * C.lower ^ 4 + C.lower ^ 5) / 6) := by
          unfold RationalSubinterval.width
          rw [Rat.div_def, Rat.div_def, Rat.div_def]
          grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
            Rat.mul_assoc, Rat.mul_comm]
        have h0 : 0 <= C.lower := C.lower_mem
        have h1 : 0 <= C.upper := Rat.le_trans h0 C.ordered
        have havg := fifthPowerSecantAverage_range h0 C.ordered
        rw [hfactor]
        constructor
        · exact Rat.mul_le_mul_of_nonneg_left havg.1 hw
        · exact Rat.mul_le_mul_of_nonneg_left havg.2 hw }
  endpointPrecision_agreement := by
    intro eps k hk n
    rfl
  riemann_width := by
    intro eps
    let N := 5 * (eps.val.den + 1)
    have hN : 0 < N := by omega
    have hbound : forall k (hk : k < N),
        (fifthIntegralBound
          ((RationalPartition.uniform 0 1 N hN (by decide +kernel)).cell k hk) 0).width <=
          5 * mesh 0 1 N := by
      intro k hk
      let C := (RationalPartition.uniform 0 1 N hN
        (by decide +kernel : (0 : Rat) <= 1)).cell k hk
      change (fifthIntegralBound C 0).width <= 5 * mesh 0 1 N
      rw [fifthIntegralBound_width]
      have hw : C.width = mesh 0 1 N := by
        dsimp [C]
        exact RationalPartition.uniform_cell_width 0 1 N hN
          (by decide +kernel) k hk
      rw [hw]
      have hm := mesh_nonneg_of_le hN
        (by decide +kernel : (0 : Rat) <= 1)
      have hs : C.upper ^ 4 + C.upper ^ 3 * C.lower +
          C.upper ^ 2 * C.lower ^ 2 + C.upper * C.lower ^ 3 +
          C.lower ^ 4 <= 5 := by
        have hu := C.upper_mem
        have hl := C.lower_mem
        have ho := C.ordered
        have hu0 : 0 <= C.upper := Rat.le_trans hl ho
        have hu4 := (nonneg_power_range (n := 4)
          (a := C.upper) (b := 1) (x := C.upper)
          hu0 hu (by exact Rat.le_refl) hu).2
        have hl4 := (nonneg_power_range (n := 4)
          (a := C.lower) (b := 1) (x := C.lower)
          hl (Rat.le_trans ho hu) (by exact Rat.le_refl)
          (Rat.le_trans ho hu)).2
        have hu3 := (nonneg_power_range (n := 3)
          (a := C.upper) (b := 1) (x := C.upper)
          hu0 hu (by exact Rat.le_refl) hu).2
        have hl3 := (nonneg_power_range (n := 3)
          (a := C.lower) (b := 1) (x := C.lower)
          hl (Rat.le_trans ho hu) (by exact Rat.le_refl)
          (Rat.le_trans ho hu)).2
        have hu2 := (nonneg_power_range (n := 2)
          (a := C.upper) (b := 1) (x := C.upper)
          hu0 hu (by exact Rat.le_refl) hu).2
        have hl2 := (nonneg_power_range (n := 2)
          (a := C.lower) (b := 1) (x := C.lower)
          hl (Rat.le_trans ho hu) (by exact Rat.le_refl)
          (Rat.le_trans ho hu)).2
        have hterm1 : C.upper ^ 3 * C.lower <= 1 := by
          calc
            C.upper ^ 3 * C.lower <= 1 * C.lower :=
              Rat.mul_le_mul_of_nonneg_right hu3 hl
            _ = C.lower := by simp
            _ <= 1 := Rat.le_trans ho hu
        have hterm2 : C.upper ^ 2 * C.lower ^ 2 <= 1 := by
          exact Rat.le_trans
            (Rat.mul_le_mul_of_nonneg_right hu2 (Rat.pow_nonneg hl)) (by grind)
        have hterm3 : C.upper * C.lower ^ 3 <= 1 := by
          calc
            C.upper * C.lower ^ 3 <= C.upper * 1 :=
              Rat.mul_le_mul_of_nonneg_left hl3 hu0
            _ = C.upper := by simp
            _ <= 1 := hu
        grind
      calc
        mesh 0 1 N * (C.upper ^ 4 + C.upper ^ 3 * C.lower +
            C.upper ^ 2 * C.lower ^ 2 + C.upper * C.lower ^ 3 +
            C.lower ^ 4) <= mesh 0 1 N * 5 :=
          Rat.mul_le_mul_of_nonneg_left hs hm
        _ = 5 * mesh 0 1 N := by grind
    have hsum := RationalPartition.uniform_boundIntegralSum_width_le
      N hN (by decide +kernel : (0 : Rat) <= 1)
      (fun k hk => (fifthIntegralDerivativeBound eps k hk).bound 0)
      (5 * mesh 0 1 N) hbound
    have hsum_bound :
        ((fifthIntegralPartitionOf eps).boundIntegralSum
          (fun k hk => (fifthIntegralDerivativeBound eps k hk).bound 0)).width
          <= 5 * mesh 0 1 N := by
      change ((RationalPartition.uniform 0 1 N hN (by decide +kernel)).boundIntegralSum
          (fun k hk => (fifthIntegralDerivativeBound eps k hk).bound 0)).width
          <= 5 * mesh 0 1 N
      have hpart : fifthIntegralPartitionOf eps =
          RationalPartition.uniform 0 1 N hN (by decide +kernel) := by
        unfold fifthIntegralPartitionOf
        congr
      cases hpart
      exact Rat.le_trans hsum (by grind)
    have hmesh : mesh 0 1 N = 1 / (N : Rat) := by
      unfold mesh
      rw [if_neg (Nat.ne_of_gt hN), Rat.div_def]
      grind
    have hden := FTC.one_div_den_succ_le_of_pos eps.property
    have hfinal : 5 * mesh 0 1 N <= eps.val := by
      rw [hmesh]
      dsimp [N]
      have hcancel :
          (5 : Rat) * (1 / ((5 * (eps.val.den + 1) : Nat) : Rat)) =
            1 / ((eps.val.den + 1 : Nat) : Rat) := by
        rw [Rat.div_def, Rat.div_def, Rat.natCast_mul]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      rw [hcancel]
      exact hden
    exact Rat.le_trans hsum_bound hfinal
  endpoint_width := by
    intro eps
    simp [fifthIntegralEndpointInterval_eq_one_sixth,
      endpointDifferenceInterval, fifthIntegralPrimitiveRaw,
      RealFunRaw.exact, QInterval.width]
    grind

theorem fifthIntegralEffectiveFTC_equiv_endpoint :
    fifthIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      fifthIntegralEffectiveFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact effectiveDerivativeBoundFTC fifthIntegralEffectiveFTCData

theorem fifthIntegralEffectiveFTC_equiv_one_sixth :
    fifthIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealCompute.ofRat (1 / 6)) := by
  let H := fifthIntegralEffectiveFTCData.toDerivativeBoundFTC
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  have hover := H.overlap (precisionAtStage n)
  change QInterval.Overlaps
    (H.boundedIntegralCompute n) { lo := 1 / 6, hi := 1 / 6 }
  have hzero : (1 / 6 : Rat) - 0 / 6 = 1 / 6 := by grind
  simpa [H, DerivativeBoundFTC.boundedIntegralCompute,
    DerivativeBoundFTC.boundedIntegralInterval,
    DerivativeBoundFTC.endpointInterval, endpointDifferenceInterval,
    fifthIntegralPrimitiveRaw, RealFunRaw.exact, Rat.pow_succ, hzero] using hover

end Integral

end ComputableAnalysis


