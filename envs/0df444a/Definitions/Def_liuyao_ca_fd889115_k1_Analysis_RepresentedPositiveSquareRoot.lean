-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RepresentedPositiveSquareRoot
-- name    : liuyao_ca_fd889115_k1_Analysis_RepresentedPositiveSquareRoot
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:01:23.694999+00:00
-- url     : https://prove2.me/theorems/67667bad-959d-45ab-9f2b-7dcbfdc2fe4c
-- title:
--   Computable analysis · RepresentedPositiveSquareRoot · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/RepresentedPositiveSquareRoot.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_AlgebraicFunctions
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexExponentialApproximation
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexReciprocalLift

set_option autoImplicit true

/-!
# Positive square roots of represented reals

This file starts the lift of the rational bisection square-root algorithm to
represented positive real inputs.  The key estimate is deliberately stated
only with rational interval data: square-root bisection midpoints are
Lipschitz away from zero, up to the widths of their certified bisection
boxes.  No completed real square root occurs in the statement or proof.
-/

namespace ComputableAnalysis
namespace RepresentedPositiveSquareRoot

/-- The midpoint of a square-root certificate lies within one certificate
width of each endpoint. -/
theorem midpoint_endpoint_bounds {I : QInterval} (hI : I.lo <= I.hi) :
    I.hi - I.width <= I.midpoint /\
      I.midpoint <= I.lo + I.width := by
  have hmid := QInterval.midpoint_mem hI
  unfold QInterval.width
  grind [Rat.sub_eq_add_neg]

private theorem sqrtCertificate_midpoint_sub_le
    {q r margin : Rat} {I J : QInterval}
    (hmargin : 0 < margin)
    (hI : SqrtIntervalSpec q I) (hJ : SqrtIntervalSpec r J)
    (hmq : sq margin <= q) (hqr : q <= r) :
    J.midpoint - I.midpoint <=
      margin⁻¹ * (r - q) + I.width + J.width := by
  have hmargin_ne : margin ≠ 0 := Rat.ne_of_gt hmargin
  have hmIhi : margin <= I.hi := hI.le_hi_of_sq_le hmq
  have hImid := midpoint_endpoint_bounds hI.2.1
  have hJmid := midpoint_endpoint_bounds hJ.2.1
  have hqr0 : 0 <= r - q := by grind [Rat.sub_eq_add_neg]
  by_cases hcross : J.lo <= I.hi
  · have hgap : J.midpoint - I.midpoint <= I.width + J.width := by
      grind [Rat.sub_eq_add_neg]
    have hinv0 : 0 <= margin⁻¹ :=
      Rat.le_of_lt ((Rat.inv_pos).2 hmargin)
    have hterm0 : 0 <= margin⁻¹ * (r - q) :=
      Rat.mul_nonneg hinv0 hqr0
    grind
  · have hgap0 : 0 < J.lo - I.hi := by grind [Rat.sub_eq_add_neg]
    have hsum : margin <= J.lo + I.hi := by
      have hJlo0 : 0 <= J.lo := hJ.1
      grind
    have hprod0 : 0 <= J.lo - I.hi := Rat.le_of_lt hgap0
    have hfactor :
        (J.lo - I.hi) * (J.lo + I.hi) = sq J.lo - sq I.hi := by
      unfold sq
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg]
    have hsq : sq J.lo - sq I.hi <= r - q := by
      have hj := hJ.2.2.1
      have hi := hI.2.2.2
      grind [Rat.sub_eq_add_neg]
    have hmul : (J.lo - I.hi) * margin <= r - q := by
      calc
        (J.lo - I.hi) * margin <=
            (J.lo - I.hi) * (J.lo + I.hi) :=
          Rat.mul_le_mul_of_nonneg_left hsum hprod0
        _ = sq J.lo - sq I.hi := hfactor
        _ <= r - q := hsq
    have hdivide : J.lo - I.hi <= margin⁻¹ * (r - q) := by
      apply Rat.le_of_mul_le_mul_right (c := margin)
      · calc
          (J.lo - I.hi) * margin <= r - q := hmul
          _ = (margin⁻¹ * (r - q)) * margin := by
            grind [Rat.mul_assoc, Rat.mul_comm,
              Rat.mul_inv_cancel margin hmargin_ne]
      · exact hmargin
    grind [Rat.sub_eq_add_neg]

/-- Quantitative rational square-root continuity away from zero.

If `I` and `J` certify square roots of `q` and `r`, and both radicands are at
least `margin^2`, then their rational midpoints differ by at most
`|r-q| / margin`, plus the two finite bisection widths.  This is the estimate
needed to lift rational bisection along moving midpoint samples of a
represented input. -/
theorem sqrtCertificate_midpoint_lipschitz
    {q r margin : Rat} {I J : QInterval}
    (hmargin : 0 < margin)
    (hI : SqrtIntervalSpec q I) (hJ : SqrtIntervalSpec r J)
    (hmq : sq margin <= q) (hmr : sq margin <= r) :
    qabs (J.midpoint - I.midpoint) <=
      margin⁻¹ * qabs (r - q) + I.width + J.width := by
  by_cases hqr : q <= r
  · have hdiff0 : 0 <= r - q := by grind [Rat.sub_eq_add_neg]
    rw [qabs_eq_self_of_nonneg hdiff0]
    apply qabs_le_of_neg_le_le
    · have hcross : I.lo <= J.hi := by
        have hJhi0 : 0 <= J.hi := Rat.le_trans hJ.1 hJ.2.1
        exact le_of_sq_le_sq_of_nonneg_right hJhi0
          (Rat.le_trans hI.2.2.1 (Rat.le_trans hqr hJ.2.2.2))
      have hImid := midpoint_endpoint_bounds hI.2.1
      have hJmid := midpoint_endpoint_bounds hJ.2.1
      have hinv0 : 0 <= margin⁻¹ :=
        Rat.le_of_lt ((Rat.inv_pos).2 hmargin)
      have hterm0 : 0 <= margin⁻¹ * (r - q) :=
        Rat.mul_nonneg hinv0 hdiff0
      grind [Rat.sub_eq_add_neg]
    · exact sqrtCertificate_midpoint_sub_le hmargin hI hJ hmq hqr
  · have hrq : r <= q := by grind
    have hdiff0 : r - q <= 0 := by grind [Rat.sub_eq_add_neg]
    rw [qabs_eq_neg_of_nonpos hdiff0]
    have hswap := sqrtCertificate_midpoint_sub_le
      hmargin hJ hI hmr hrq
    have hcross : J.lo <= I.hi := by
      have hIhi0 : 0 <= I.hi := Rat.le_trans hI.1 hI.2.1
      exact le_of_sq_le_sq_of_nonneg_right hIhi0
        (Rat.le_trans hJ.2.2.1 (Rat.le_trans hrq hI.2.2.2))
    have hImid := midpoint_endpoint_bounds hI.2.1
    have hJmid := midpoint_endpoint_bounds hJ.2.1
    have hinv0 : 0 <= margin⁻¹ :=
      Rat.le_of_lt ((Rat.inv_pos).2 hmargin)
    have hqr0 : 0 <= q - r := by grind [Rat.sub_eq_add_neg]
    have hterm0 : 0 <= margin⁻¹ * (q - r) :=
      Rat.mul_nonneg hinv0 hqr0
    apply qabs_le_of_neg_le_le
    · grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    · grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-! ## Lift to represented positive inputs -/

/-- A represented real together with the finite data needed by the positive
square-root chart.  `bound` is deliberately a natural number, so it also
supplies a simple uniform modulus for the fixed rational bisection bracket. -/
structure PositiveInput (bound : Nat) (margin : Rat) where
  raw : RealCompute
  valid : raw.Valid
  margin_pos : 0 < margin
  center_le_bound : forall n,
    (raw.compute n).midpoint <= (bound : Rat)
  margin_sq_le_center : forall n,
    sq margin <= (raw.compute n).midpoint

namespace PositiveInput

def rootBound (bound : Nat) : Rat := ((bound + 1 : Nat) : Rat)

theorem rootBound_pos (bound : Nat) : 0 < rootBound bound := by
  unfold rootBound
  exact (Rat.natCast_pos).2 (Nat.succ_pos bound)

theorem center_nonneg {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    0 <= (A.raw.compute n).midpoint := by
  have hm0 : 0 <= margin := Rat.le_of_lt A.margin_pos
  have hsq0 : 0 <= sq margin := by
    unfold sq
    exact Rat.mul_nonneg hm0 hm0
  exact Rat.le_trans hsq0 (A.margin_sq_le_center n)

theorem center_le_rootBound_sq {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    (A.raw.compute n).midpoint <= sq (rootBound bound) := by
  have hb : ((bound : Nat) : Rat) <= rootBound bound := by
    unfold rootBound
    exact_mod_cast (Nat.le_succ bound)
  have hB1 : 1 <= rootBound bound := by
    unfold rootBound
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le bound))
  have hB0 : 0 <= rootBound bound := Rat.le_trans (by decide +kernel) hB1
  calc
    (A.raw.compute n).midpoint <= (bound : Rat) := A.center_le_bound n
    _ <= rootBound bound := hb
    _ = rootBound bound * 1 := by grind
    _ <= rootBound bound * rootBound bound :=
      Rat.mul_le_mul_of_nonneg_left hB1 hB0
    _ = sq (rootBound bound) := rfl

def approximation {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) : QInterval :=
  sqrtBisect (A.raw.compute n).midpoint n
    { lo := 0, hi := rootBound bound }

theorem approximation_spec {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    SqrtIntervalSpec (A.raw.compute n).midpoint (approximation A n) := by
  apply sqrtBisect_spec
  unfold SqrtIntervalSpec
  refine ⟨(by decide +kernel : (0 : Rat) <= 0), ?_, ?_,
    center_le_rootBound_sq A n⟩
  · exact Rat.le_of_lt (rootBound_pos bound)
  · simpa [sq] using center_nonneg A n

theorem approximation_width_eq {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    (approximation A n).width =
      rootBound bound / (((2 ^ n : Nat) : Rat)) := by
  unfold approximation
  rw [sqrtBisect_width_eq]
  unfold QInterval.width
  grind [Rat.sub_eq_add_neg]

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

def approximationBudget (bound : Nat) (n : Nat) : Rat :=
  ((bound + 1 : Nat) : Rat) / (((2 ^ n : Nat) : Rat))

theorem approximation_width_le_budget {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    (approximation A n).width <= approximationBudget bound n := by
  rw [approximation_width_eq]
  exact Rat.le_refl

theorem approximationBudget_le_harmonic (bound n : Nat) :
    approximationBudget bound n≤((bound+1:Nat):Rat)/((n+1:Nat):Rat) := by
  unfold approximationBudget
  have hnum0 : 0 <= (((bound + 1 : Nat) : Rat)) := Rat.natCast_nonneg
  have hpow : n + 1 <= 2 ^ n := succ_le_two_pow n
  have hone := FTC.one_div_nat_antitone (Nat.succ_pos n)
    (Nat.pow_pos (by omega : 0 < 2)) hpow
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_left (by
    simpa [Rat.div_def] using hone) hnum0

theorem approximationBudget_antitone (bound : Nat) {k n : Nat} (hkn : k≤n) :
    approximationBudget bound n≤approximationBudget bound k := by
  have hp : (0:Nat)<2 := by omega
  have h := FTC.one_div_nat_antitone (Nat.pow_pos hp) (Nat.pow_pos hp)
    (Nat.pow_le_pow_right hp hkn)
  have hm := Rat.mul_le_mul_of_nonneg_left h (Rat.natCast_nonneg (a := bound+1))
  simpa only [approximationBudget,Rat.div_def,Rat.one_mul] using hm

theorem approximationBudget_nonnegative (bound n : Nat) : 0≤approximationBudget bound n :=
  Rat.mul_nonneg Rat.natCast_nonneg
    (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr (Nat.pow_pos (by omega : 0<2)))))

theorem approximationBudget_shrinks (bound : Nat) :
    ShrinksToZero (approximationBudget bound) := by
  apply shrinksToZero_of_natOverSuccBound (C := bound + 1)
  exact approximationBudget_le_harmonic bound

theorem midpoint_sub_le_width {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (k n : Nat) (hkn : k <= n) :
    qabs ((A.raw.compute n).midpoint - (A.raw.compute k).midpoint) <=
      (A.raw.compute k).width := by
  have hkwidth := A.valid.1 k
  have hnwidth := A.valid.1 n
  have hkordered : (A.raw.compute k).lo <= (A.raw.compute k).hi := by
    unfold QInterval.width at hkwidth
    grind [Rat.sub_eq_add_neg]
  have hnordered : (A.raw.compute n).lo <= (A.raw.compute n).hi := by
    unfold QInterval.width at hnwidth
    grind [Rat.sub_eq_add_neg]
  have hmidk := QInterval.midpoint_mem hkordered
  have hmidn := QInterval.midpoint_mem hnordered
  have hnest := A.valid.2.1 k n hkn
  apply qabs_sub_le_of_common_bounds
  · exact Rat.le_trans hnest.1 hmidn.1
  · exact Rat.le_trans hmidn.2 hnest.2.2
  · exact hmidk.1
  · exact hmidk.2

/-- Direct candidates retain the full certified rational bisection interval.
This is what later makes the equation `sqrt(x)^2 = x` an interval-containment
fact rather than a limit argument. -/
def candidate {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : ComplexCompute where
  compute := fun n => QBox.ofRealInterval (approximation A n)

theorem candidate_ordered {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    ((candidate A).compute n).Ordered := by
  have hs := approximation_spec A n
  unfold candidate QBox.ofRealInterval
  exact ⟨hs.2.1, Rat.le_refl⟩

theorem candidate_widths_shrink {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    ComplexCompute.WidthsShrinkToZero (candidate A).compute := by
  intro eps
  obtain ⟨N, hN⟩ := approximationBudget_shrinks bound eps
  refine ⟨N, ?_⟩
  intro n hn
  constructor
  · change (approximation A n).width <= eps.val
    exact Rat.le_trans (approximation_width_le_budget A n) (hN n hn)
  · unfold candidate QBox.ofRealInterval QBox.height
    change (0 : Rat) - 0 <= eps.val
    grind [Rat.le_of_lt eps.property]

def radius {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) : Rat :=
  margin⁻¹ * (A.raw.compute n).width +
    3 * approximationBudget bound n

theorem radius_shrinks {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : ShrinksToZero (radius A) := by
  intro eps
  let inputEps : QPos :=
    ⟨eps.val * margin / 4, by
      exact Rat.mul_pos (Rat.mul_pos eps.property A.margin_pos)
        ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 4))⟩
  let budgetEps : QPos :=
    ⟨eps.val / 6, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property
        ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 6))⟩
  obtain ⟨Ni, hNi⟩ := A.valid.2.2 inputEps
  obtain ⟨Nb, hNb⟩ := approximationBudget_shrinks bound budgetEps
  refine ⟨Nat.max Ni Nb, ?_⟩
  intro n hn
  have hi := (hNi n (Nat.le_trans (Nat.le_max_left _ _) hn))
  have hb := hNb n (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hinv0 : 0 <= margin⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 A.margin_pos)
  unfold radius
  calc
    margin⁻¹ * (A.raw.compute n).width +
        3 * approximationBudget bound n <=
      margin⁻¹ * inputEps.val + 3 * budgetEps.val :=
        rat_add_le_add
          (Rat.mul_le_mul_of_nonneg_left hi hinv0)
          (Rat.mul_le_mul_of_nonneg_left hb (by decide +kernel))
    _ <= eps.val := by
      dsimp [inputEps, budgetEps]
      rw [Rat.div_def]
      have hm : margin ≠ 0 := Rat.ne_of_gt A.margin_pos
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel margin hm,
        Rat.mul_inv_cancel]

theorem candidate_future_contained_expand {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (k n : Nat) (hkn : k <= n) :
    ((candidate A).compute n).NestedIn
      (QBox.expand ((candidate A).compute k) (radius A k)) := by
  let q := (A.raw.compute k).midpoint
  let r := (A.raw.compute n).midpoint
  let x := (approximation A k).midpoint
  let y := (approximation A n).midpoint
  have hdist0 := sqrtCertificate_midpoint_lipschitz
    A.margin_pos (approximation_spec A k) (approximation_spec A n)
    (A.margin_sq_le_center k) (A.margin_sq_le_center n)
  have hinput := midpoint_sub_le_width A k n hkn
  have hwidthk := approximation_width_le_budget A k
  have hwidthn0 := approximation_width_le_budget A n
  have hbudget := approximationBudget_antitone bound hkn
  have hwidthn := Rat.le_trans hwidthn0 hbudget
  have hinv0 : 0 <= margin⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 A.margin_pos)
  have hbudget0 := approximationBudget_nonnegative bound k
  let midpointRadius : Rat :=
    margin⁻¹ * (A.raw.compute k).width +
      2 * approximationBudget bound k
  have hdist : qabs (y - x) <= midpointRadius := by
    have hm := Rat.mul_le_mul_of_nonneg_left hinput hinv0
    calc
      qabs (y - x) <=
          margin⁻¹ * qabs (r - q) +
            (approximation A k).width + (approximation A n).width := hdist0
      _ <= margin⁻¹ * (A.raw.compute k).width +
            approximationBudget bound k + approximationBudget bound k :=
        rat_add_le_add (rat_add_le_add hm hwidthk) hwidthn
      _ <= midpointRadius := by
        dsimp [midpointRadius]
        grind
  have hIk := (approximation_spec A k).2.1
  have hIn := (approximation_spec A n).2.1
  have hmk := QInterval.midpoint_mem hIk
  have hmn := QInterval.midpoint_mem hIn
  have hnk := midpoint_endpoint_bounds hIn
  have hlow : -midpointRadius <= y - x := by
    exact Rat.le_trans (by grind : -midpointRadius <= -qabs (y - x))
      (neg_qabs_le_self (y - x))
  have hupp : y - x <= midpointRadius :=
    Rat.le_trans (self_le_qabs (y - x)) hdist
  have hradius0 : 0 <= radius A k := by
    unfold radius
    exact Rat.add_nonneg
      (Rat.mul_nonneg hinv0 (A.valid.1 k))
      (Rat.mul_nonneg (by decide +kernel) hbudget0)
  have hcover : midpointRadius + approximationBudget bound k <= radius A k := by
    unfold radius
    grind
  unfold candidate QBox.ofRealInterval QBox.NestedIn QBox.expand
  simp only [QComplex.le_def]
  constructor
  · constructor
    · unfold QInterval.width at hwidthk hwidthn
      grind [Rat.sub_eq_add_neg]
    · grind
  · constructor
    · unfold QInterval.width at hwidthk hwidthn
      grind [Rat.sub_eq_add_neg]
    · grind

/-- Constructive positive square root, represented as the real part of a
finite-prefix stabilization of rational bisection midpoints. -/
def sqrtComplex {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : ComplexCompute :=
  ComplexCompute.cauchyStabilize (candidate A) (radius A)

def sqrt {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : RealCompute := (sqrtComplex A).realPart

theorem sqrtComplex_valid {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (sqrtComplex A).Valid := by
  unfold sqrtComplex
  exact ComplexCompute.cauchyStabilize_valid
    (candidate_ordered A) (candidate_widths_shrink A)
    (candidate_future_contained_expand A) (radius_shrinks A)

theorem sqrt_valid {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (sqrt A).Valid :=
  ComplexCompute.realPart_valid (sqrtComplex_valid A)

/-- Every output stage retains the full current rational bisection
certificate.  Combined with `approximation_spec`, this is the finite
algebraic certificate from which the represented square equation is derived. -/
theorem sqrt_contains_current_approximation
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) (n : Nat) :
    (sqrt A).compute n |>.ContainsInterval (approximation A n) := by
  have hcontains : ((candidate A).compute n).NestedIn
      ((sqrtComplex A).compute n) := by
    unfold sqrtComplex
    exact ComplexCompute.cauchyStabilize_contains_current
      (candidate_future_contained_expand A) n
  exact ⟨hcontains.1.1, hcontains.2.1⟩

/-- Squaring the current finite bisection box contains the sampled radicand
center.  This is the literal rational-box form of the algebraic equation. -/
theorem candidate_square_contains_center
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) (n : Nat) :
    (QBox.point
      { re := (A.raw.compute n).midpoint, im := 0 }).NestedIn
        (QBox.mul ((candidate A).compute n) ((candidate A).compute n)) := by
  have hs := approximation_spec A n
  have hmul := QBox.mulRealInterval_self_of_nonneg hs.1 hs.2.1
  have hzero := QBox.mulRealInterval_self_of_nonneg
    (by decide +kernel : (0 : Rat) <= 0) (Rat.le_refl : (0 : Rat) <= 0)
  have hrightZero := QBox.mulRealInterval_of_nonneg
    hs.1 hs.2.1 (by decide +kernel : (0 : Rat) <= 0)
      (Rat.le_refl : (0 : Rat) <= 0)
  have hleftZero := QBox.mulRealInterval_of_nonneg
    (by decide +kernel : (0 : Rat) <= 0) (Rat.le_refl : (0 : Rat) <= 0)
      hs.1 hs.2.1
  unfold candidate QBox.ofRealInterval QBox.mul QBox.point QBox.NestedIn
  simp only [QComplex.le_def]
  rw [hmul, hzero, hrightZero, hleftZero]
  unfold SqrtIntervalSpec sq at hs
  grind [Rat.sub_eq_add_neg]

/-- The constructed positive square root satisfies its defining equation as
an equivalence of represented complex numbers.  The proof uses, at every
stage, the rational radicand midpoint as a common point of the input box and
the square of the stabilized root box. -/
theorem sqrtComplex_square_equiv_raw
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) :
    (ComplexCompute.mul (sqrtComplex A) (sqrtComplex A)).Equiv
      (ComplexCompute.ofRealCompute A.raw) := by
  intro n
  apply (ComplexCompute.compareAt_overlap_iff
    (ComplexCompute.mul (sqrtComplex A) (sqrtComplex A))
    (ComplexCompute.ofRealCompute A.raw) n n).2
  let point : QComplex :=
    { re := (A.raw.compute n).midpoint, im := 0 }
  have hcandidate : ((candidate A).compute n).NestedIn
      ((sqrtComplex A).compute n) := by
    unfold sqrtComplex
    exact ComplexCompute.cauchyStabilize_contains_current
      (candidate_future_contained_expand A) n
  have hcandidateSq := candidate_square_contains_center A n
  have hmulNested :
      (QBox.mul ((candidate A).compute n) ((candidate A).compute n)).NestedIn
        (QBox.mul ((sqrtComplex A).compute n) ((sqrtComplex A).compute n)) :=
    QBox.mul_nested (candidate_ordered A n) (candidate_ordered A n)
      hcandidate hcandidate
  have hpointSq : (QBox.point point).NestedIn
      ((ComplexCompute.mul (sqrtComplex A) (sqrtComplex A)).compute n) :=
    QBox.nested_trans hcandidateSq hmulNested
  have hrawOrdered :
      (A.raw.compute n).lo <= (A.raw.compute n).hi := by
    have := A.valid.1 n
    unfold QInterval.width at this
    grind [Rat.sub_eq_add_neg]
  have hmid := QInterval.midpoint_mem hrawOrdered
  have hpointRaw : (QBox.point point).NestedIn
      ((ComplexCompute.ofRealCompute A.raw).compute n) := by
    unfold point QBox.point ComplexCompute.ofRealCompute QBox.NestedIn
    simp only [QComplex.le_def]
    exact ⟨⟨hmid.1, Rat.le_refl⟩, ⟨hmid.2, Rat.le_refl⟩⟩
  exact ⟨
    QComplex.le_trans hpointSq.1
      (QComplex.le_trans (QComplex.le_refl point) hpointRaw.2),
    QComplex.le_trans hpointRaw.1
      (QComplex.le_trans (QComplex.le_refl point) hpointSq.2)⟩

/-! ## A uniformly positive reboxing -/

/-- Extra bisection stages sufficient to make the rational square-root
certificate narrower than `margin/2`. -/
private def coarseGuardShift (bound : Nat) (margin : Rat) : Nat :=
  2 * (bound + 1) * (margin.den + 1)

private theorem coarse_guard_budget
    {bound : Nat} {margin : Rat} (hmargin : 0 < margin) (n : Nat) :
    approximationBudget bound (n + coarseGuardShift bound margin) <= margin / 2 := by
  let C : Nat := bound + 1
  let D : Nat := margin.den + 1
  let S : Nat := 2 * C * D
  have hC : 0 < C := by dsimp [C]; omega
  have hD : 0 < D := by dsimp [D]; omega
  have hS : 0 < S := Nat.mul_pos (Nat.mul_pos (by omega) hC) hD
  have hden : S <= n + S + 1 := by omega
  have hone := FTC.one_div_nat_antitone hS (by omega : 0 < n + S + 1) hden
  have hC0 : 0 <= (C : Rat) := Rat.natCast_nonneg
  have hscaled := Rat.mul_le_mul_of_nonneg_left hone hC0
  have hCDne : ((C : Rat) * ((2 * D : Nat) : Rat)) ≠ 0 := by
    exact Rat.ne_of_gt (Rat.mul_pos
      ((Rat.natCast_pos).2 hC)
      ((Rat.natCast_pos).2 (Nat.mul_pos (by omega) hD)))
  have hcancel :
      (C : Rat) / (S : Rat) = 1 / (((2 * D : Nat) : Rat)) := by
    dsimp [S]
    rw [show (((2 * C * D : Nat) : Rat)) =
      (C : Rat) * ((2 * D : Nat) : Rat) by
        exact_mod_cast (by
          simp [Nat.mul_comm, Nat.mul_left_comm] :
          2 * C * D = C * (2 * D))]
    rw [Rat.div_def, Rat.div_def]
    have hCne : (C : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hC)
    have h2Dne : (((2 * D : Nat) : Rat)) ≠ 0 :=
      Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.mul_pos (by omega) hD))
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hfirst : approximationBudget bound (n + coarseGuardShift bound margin) <=
      1 / (((2 * D : Nat) : Rat)) := by
    calc
      approximationBudget bound (n+coarseGuardShift bound margin)≤(C:Rat)/((n+S+1:Nat):Rat) :=
        approximationBudget_le_harmonic bound _
      _≤(C:Rat)/(S:Rat) := by simpa [Rat.div_def] using hscaled
      _=1/((2*D:Nat):Rat) := hcancel
  have hbase := FTC.one_div_den_succ_le_of_pos hmargin
  have hhalf : 1 / (((2 * D : Nat) : Rat)) <= margin / 2 := by
    have htwo : (0 : Rat) <= 1 / 2 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (by decide +kernel)
        (Rat.le_of_lt ((Rat.inv_pos).2 (by decide +kernel)))
    have hmul := Rat.mul_le_mul_of_nonneg_right hbase htwo
    dsimp [D] at hmul ⊢
    rw [Rat.div_def, Rat.div_def] at hmul ⊢
    have hdne : (((margin.den + 1 : Nat) : Rat)) ≠ 0 :=
      Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos margin.den))
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  exact Rat.le_trans hfirst hhalf

/-- Search only as far as the actual dyadic bisection budget requires.
The coarse denominator bound occurs exclusively in the termination proof. -/
private def guardSearchFrom (bound : Nat) (margin : Rat) (hp : 0<margin) (n : Nat) : Nat :=
  if approximationBudget bound n≤margin/2 then n else guardSearchFrom bound margin hp (n+1)
termination_by coarseGuardShift bound margin-n
decreasing_by
  have h0 := coarse_guard_budget (bound := bound) hp 0
  have hn : n<coarseGuardShift bound margin := by
    by_cases hn : n<coarseGuardShift bound margin
    · exact hn
    · have hm := approximationBudget_antitone bound (show coarseGuardShift bound margin≤n by omega)
      have hb : approximationBudget bound n≤margin/2 := Rat.le_trans hm (by simpa only [Nat.zero_add] using h0)
      contradiction
  omega

private theorem guardSearchFrom_spec (bound : Nat) (margin : Rat) (hp : 0<margin) (n : Nat) :
    approximationBudget bound (guardSearchFrom bound margin hp n)≤margin/2 := by
  rw [guardSearchFrom]
  split
  · assumption
  · exact guardSearchFrom_spec bound margin hp (n+1)
termination_by coarseGuardShift bound margin-n
decreasing_by
  have h0 := coarse_guard_budget (bound := bound) hp 0
  have hn : n<coarseGuardShift bound margin := by
    by_cases hn : n<coarseGuardShift bound margin
    · exact hn
    · have hm := approximationBudget_antitone bound (show coarseGuardShift bound margin≤n by omega)
      have hb : approximationBudget bound n≤margin/2 := Rat.le_trans hm (by simpa only [Nat.zero_add] using h0)
      contradiction
  omega

/-- Extra bisection stages are selected by a terminating rational budget
search. Positive-input semantics and all later guard bounds are preserved. -/
def guardShift (bound : Nat) (margin : Rat) : Nat :=
  if hp : 0<margin then guardSearchFrom bound margin hp 0 else 0

theorem approximationBudget_shift_le_half_margin
    {bound : Nat} {margin : Rat} (hmargin : 0<margin) (n : Nat) :
    approximationBudget bound (n+guardShift bound margin)≤margin/2 := by
  simp only [guardShift,dif_pos hmargin]
  exact Rat.le_trans (approximationBudget_antitone bound (show
    guardSearchFrom bound margin hmargin 0≤n+guardSearchFrom bound margin hmargin 0 by omega))
    (guardSearchFrom_spec bound margin hmargin 0)

theorem half_margin_le_shifted_approximation_lo
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) (n : Nat) :
    margin / 2 <=
      (approximation A (n + guardShift bound margin)).lo := by
  let stage := n + guardShift bound margin
  have hspec := approximation_spec A stage
  have hlower := hspec.sub_width_le_lo_of_sq_le
    (A.margin_sq_le_center stage)
  have hwidth := approximation_width_le_budget A stage
  have hbudget := approximationBudget_shift_le_half_margin
    (bound := bound) A.margin_pos n
  have hwidthHalf : (approximation A stage).width <= margin / 2 :=
    Rat.le_trans hwidth hbudget
  dsimp [stage] at hlower hwidthHalf ⊢
  grind [Rat.sub_eq_add_neg, Rat.div_def]

theorem shifted_approximation_hi_le_rootBound
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) (n : Nat) :
    (approximation A (n + guardShift bound margin)).hi <= rootBound bound := by
  let stage := n + guardShift bound margin
  let q := (A.raw.compute stage).midpoint
  have hinitial : SqrtIntervalSpec q
      { lo := 0, hi := rootBound bound } := by
    unfold SqrtIntervalSpec
    refine ⟨(by decide +kernel : (0 : Rat) <= 0),
      Rat.le_of_lt (rootBound_pos bound), ?_, ?_⟩
    · simpa [q, sq] using center_nonneg A stage
    · simpa [q] using center_le_rootBound_sq A stage
  have hcontains := sqrtBisect_contains_of_le_fuel hinitial
    (Nat.zero_le stage)
  simpa [approximation, stage, q, sqrtBisect] using hcontains.2

def guardInterval (bound : Nat) (margin : Rat) : QInterval :=
  { lo := margin / 2, hi := rootBound bound }

theorem shifted_approximation_nested_guard
    {bound : Nat} {margin : Rat} (A : PositiveInput bound margin) (n : Nat) :
    (guardInterval bound margin).ContainsInterval
      (approximation A (n + guardShift bound margin)) :=
  ⟨half_margin_le_shifted_approximation_lo A n,
    shifted_approximation_hi_le_rootBound A n⟩

/-- The positive root reboxed into the explicit compact interval
`[margin/2, rootBound]`.  Its computation remains finite rational interval
arithmetic. -/
def awayRootRaw {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : ComplexCompute where
  compute := fun n => QBox.intersection
    ((sqrtComplex A).compute (n + guardShift bound margin))
    (QBox.ofRealInterval (guardInterval bound margin))

theorem awayRootRaw_valid {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) : (awayRootRaw A).Valid := by
  let shift := guardShift bound margin
  have hsqrt := sqrtComplex_valid A
  have hcommon : forall n,
      ((candidate A).compute (n + shift)).NestedIn
        ((awayRootRaw A).compute n) := by
    intro n
    unfold awayRootRaw
    apply QBox.intersection_contains
    · unfold sqrtComplex
      exact ComplexCompute.cauchyStabilize_contains_current
        (candidate_future_contained_expand A) (n + shift)
    · have hg := shifted_approximation_nested_guard A n
      unfold QInterval.ContainsInterval at hg
      unfold candidate QBox.ofRealInterval QBox.NestedIn
      simp only [QComplex.le_def]
      exact ⟨⟨hg.1, Rat.le_refl⟩, ⟨hg.2, Rat.le_refl⟩⟩
  constructor
  · intro n
    have hordered := QBox.ordered_of_nested
      (candidate_ordered A (n + shift)) (hcommon n)
    exact (QBox.ordered_iff_width_height_nonneg _).1 hordered
  · constructor
    · intro n m hnm
      have hbox : QBox.NestedIn
          (QBox.intersection ((sqrtComplex A).compute (m + shift))
            (QBox.ofRealInterval (guardInterval bound margin)))
          (QBox.intersection ((sqrtComplex A).compute (n + shift))
            (QBox.ofRealInterval (guardInterval bound margin))) := by
        apply QBox.intersection_contains
        · apply QBox.nested_trans
          · exact QBox.intersection_contained_left _ _
          · exact ComplexCompute.valid_nestedIn hsqrt (by omega)
        · exact QBox.intersection_contained_right _ _
      exact ⟨hbox.1.1, hbox.2.1, hbox.1.2, hbox.2.2⟩
    · intro eps
      obtain ⟨N, hN⟩ := hsqrt.2.2 eps
      refine ⟨N, ?_⟩
      intro n hn
      have hsource := hN (n + shift) (Nat.le_trans hn (Nat.le_add_right n shift))
      have hcontained := QBox.intersection_contained_left
        ((sqrtComplex A).compute (n + shift))
        (QBox.ofRealInterval (guardInterval bound margin))
      have hwh := QBox.width_height_le_of_nested hcontained
      exact ⟨Rat.le_trans hwh.1 hsource.1,
        Rat.le_trans hwh.2 hsource.2⟩

/-- Every guarded output box retains the literal square-root certificate at
the shifted bisection stage used to construct it. -/
theorem awayRootRaw_contains_shifted_approximation
    {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    ((candidate A).compute (n + guardShift bound margin)).NestedIn
      ((awayRootRaw A).compute n) := by
  unfold awayRootRaw
  apply QBox.intersection_contains
  · unfold sqrtComplex
    exact ComplexCompute.cauchyStabilize_contains_current
      (candidate_future_contained_expand A)
      (n + guardShift bound margin)
  · have hg := shifted_approximation_nested_guard A n
    unfold QInterval.ContainsInterval at hg
    unfold candidate QBox.ofRealInterval QBox.NestedIn
    simp only [QComplex.le_def]
    exact ⟨⟨hg.1, Rat.le_refl⟩, ⟨hg.2, Rat.le_refl⟩⟩

theorem awayRootRaw_equiv_sqrtComplex {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    (awayRootRaw A).Equiv (sqrtComplex A) := by
  intro n
  apply (ComplexCompute.compareAt_overlap_iff (awayRootRaw A) (sqrtComplex A)
    n n).2
  let shift := guardShift bound margin
  have hleftOrdered := ComplexCompute.valid_ordered (awayRootRaw_valid A) n
  have hleftInShifted : ((awayRootRaw A).compute n).NestedIn
      ((sqrtComplex A).compute (n + shift)) := by
    exact QBox.intersection_contained_left _ _
  have hshiftedInCurrent : ((sqrtComplex A).compute (n + shift)).NestedIn
      ((sqrtComplex A).compute n) :=
    ComplexCompute.valid_nestedIn (sqrtComplex_valid A) (Nat.le_add_right n shift)
  have hleftInRight := QBox.nested_trans hleftInShifted hshiftedInCurrent
  exact ⟨
    QComplex.le_trans hleftOrdered hleftInRight.2,
    QComplex.le_trans hleftInRight.1 hleftOrdered⟩

theorem awayRootRaw_square_equiv_raw {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    (ComplexCompute.mul (awayRootRaw A) (awayRootRaw A)).Equiv
      (ComplexCompute.ofRealCompute A.raw) := by
  exact ComplexCompute.equiv_trans
    (ComplexCompute.mul_valid (awayRootRaw_valid A) (awayRootRaw_valid A))
    (ComplexCompute.mul_valid (sqrtComplex_valid A) (sqrtComplex_valid A))
    (ComplexCompute.ofRealCompute_valid A.raw A.valid)
    (ComplexCompute.mul_equiv
      (awayRootRaw_valid A) (sqrtComplex_valid A)
      (awayRootRaw_valid A) (sqrtComplex_valid A)
      (awayRootRaw_equiv_sqrtComplex A) (awayRootRaw_equiv_sqrtComplex A))
    (sqrtComplex_square_equiv_raw A)

def awayRootMargin (margin : Rat) : Rat := sq (margin / 2)

theorem awayRootMargin_pos {margin : Rat} (hmargin : 0 < margin) :
    0 < awayRootMargin margin := by
  have hhalf : 0 < margin / 2 := by
    rw [Rat.div_def]
    exact Rat.mul_pos hmargin ((Rat.inv_pos).2 (by decide +kernel))
  unfold awayRootMargin sq
  exact Rat.mul_pos hhalf hhalf

theorem awayRootRaw_nested_guard {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    ((awayRootRaw A).compute n).NestedIn
      (QBox.ofRealInterval (guardInterval bound margin)) := by
  exact QBox.intersection_contained_right _ _

theorem awayRootRaw_center_bounds {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (n : Nat) :
    margin / 2 <= ((awayRootRaw A).compute n).center.re /\
      ((awayRootRaw A).compute n).center.re <= rootBound bound /\
      ((awayRootRaw A).compute n).center.im = 0 := by
  have hordered := ComplexCompute.valid_ordered (awayRootRaw_valid A) n
  have hcenter := QBox.center_mem hordered
  have hguard := awayRootRaw_nested_guard A n
  unfold QBox.ofRealInterval QBox.NestedIn at hguard
  simp only [QComplex.le_def] at hguard hcenter
  unfold guardInterval at hguard
  constructor
  · exact Rat.le_trans hguard.1.1 hcenter.1.1
  · constructor
    · exact Rat.le_trans hcenter.2.1 hguard.2.1
    · have hlo : 0 <= ((awayRootRaw A).compute n).center.im :=
        Rat.le_trans hguard.1.2 hcenter.1.2
      have hhi : ((awayRootRaw A).compute n).center.im <= 0 :=
        Rat.le_trans hcenter.2.2 hguard.2.2
      exact Rat.le_antisymm hhi hlo

/-- The positively reboxed root is uniformly bounded and separated from
zero, hence is directly accepted by the represented reciprocal API. -/
def awayInput {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) :
    ComplexReciprocalLift.AwayInput (rootBound bound) (awayRootMargin margin) where
  raw := awayRootRaw A
  valid := awayRootRaw_valid A
  bound_nonneg := Rat.le_of_lt (rootBound_pos bound)
  margin_pos := awayRootMargin_pos A.margin_pos
  center_normBound := by
    intro n
    have hb := awayRootRaw_center_bounds A n
    have hhalf0 : 0 <= margin / 2 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (Rat.le_of_lt A.margin_pos)
        (Rat.le_of_lt ((Rat.inv_pos).2 (by decide +kernel)))
    have hre0 : 0 <= ((awayRootRaw A).compute n).center.re :=
      Rat.le_trans hhalf0 hb.1
    have hzero : qabs 0 = 0 := by decide +kernel
    unfold QComplex.normBound
    rw [hb.2.2, qabs_eq_self_of_nonneg hre0, hzero]
    grind
  center_normSq_ge := by
    intro n
    have hb := awayRootRaw_center_bounds A n
    have hhalf0 : 0 <= margin / 2 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (Rat.le_of_lt A.margin_pos)
        (Rat.le_of_lt ((Rat.inv_pos).2 (by decide +kernel)))
    have hre0 : 0 <= ((awayRootRaw A).compute n).center.re :=
      Rat.le_trans hhalf0 hb.1
    have hmul := rat_mul_le_mul_of_nonneg hhalf0 hb.1 hhalf0 hb.1
    unfold awayRootMargin sq QComplex.normSq
    rw [hb.2.2]
    grind

/-! ## Independence of the represented input -/

theorem midpoint_sub_le_width_add_width_of_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw)
    (m n : Nat) :
    qabs ((A.raw.compute m).midpoint - (B.raw.compute n).midpoint) <=
      (A.raw.compute m).width + (B.raw.compute n).width := by
  have hAw := A.valid.1 m
  have hBw := B.valid.1 n
  have hAo : (A.raw.compute m).lo <= (A.raw.compute m).hi := by
    unfold QInterval.width at hAw
    grind [Rat.sub_eq_add_neg]
  have hBo : (B.raw.compute n).lo <= (B.raw.compute n).hi := by
    unfold QInterval.width at hBw
    grind [Rat.sub_eq_add_neg]
  have hAm := QInterval.midpoint_mem hAo
  have hBm := QInterval.midpoint_mem hBo
  have hover := (RealCompute.compareAt_overlap_iff A.raw B.raw m n).1
    (RealCompute.allStagesOverlap_of_equiv A.valid B.valid hAB m n)
  apply qabs_le_of_neg_le_le
  · have hupper : (B.raw.compute n).midpoint -
        (A.raw.compute m).midpoint <=
        (B.raw.compute n).hi - (A.raw.compute m).lo := by
      grind [Rat.sub_eq_add_neg]
    have hbound : (B.raw.compute n).hi - (A.raw.compute m).lo <=
        (A.raw.compute m).width + (B.raw.compute n).width := by
      have hcross := hover.2
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have := Rat.le_trans hupper hbound
    grind [Rat.sub_eq_add_neg]
  · have hupper : (A.raw.compute m).midpoint -
        (B.raw.compute n).midpoint <=
        (A.raw.compute m).hi - (B.raw.compute n).lo := by
      grind [Rat.sub_eq_add_neg]
    have hbound : (A.raw.compute m).hi - (B.raw.compute n).lo <=
        (A.raw.compute m).width + (B.raw.compute n).width := by
      have hcross := hover.1
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    exact Rat.le_trans hupper hbound

theorem width_antitone {bound : Nat} {margin : Rat}
    (A : PositiveInput bound margin) (k n : Nat) (hkn : k <= n) :
    (A.raw.compute n).width <= (A.raw.compute k).width := by
  apply QInterval.width_le_of_contains
  have hnest := A.valid.2.1 k n hkn
  exact ⟨hnest.1, hnest.2.2⟩

def crossRadius {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (n : Nat) : Rat :=
  margin⁻¹ * ((A.raw.compute n).width + (B.raw.compute n).width) +
    3 * approximationBudget bound n

theorem radius_le_crossRadius {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (n : Nat) :
    radius A n <= crossRadius A B n := by
  have hinv0 : 0 <= margin⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 A.margin_pos)
  have hBw : 0 <= (B.raw.compute n).width := B.valid.1 n
  unfold radius crossRadius
  exact rat_add_le_add
    (Rat.mul_le_mul_of_nonneg_left (by grind) hinv0) Rat.le_refl

theorem crossRadius_shrinks {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) :
    ShrinksToZero (crossRadius A B) := by
  intro eps
  let inputEps : QPos :=
    ⟨eps.val * margin / 8, by
      exact Rat.mul_pos (Rat.mul_pos eps.property A.margin_pos)
        ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 8))⟩
  let budgetEps : QPos :=
    ⟨eps.val / 6, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property
        ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 6))⟩
  obtain ⟨NA, hNA⟩ := A.valid.2.2 inputEps
  obtain ⟨NB, hNB⟩ := B.valid.2.2 inputEps
  obtain ⟨Nc, hNc⟩ := approximationBudget_shrinks bound budgetEps
  refine ⟨Nat.max (Nat.max NA NB) Nc, ?_⟩
  intro n hn
  have hnAB : Nat.max NA NB <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hA := hNA n (Nat.le_trans (Nat.le_max_left _ _) hnAB)
  have hB := hNB n (Nat.le_trans (Nat.le_max_right _ _) hnAB)
  have hc := hNc n (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hinv0 : 0 <= margin⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 A.margin_pos)
  unfold crossRadius
  calc
    margin⁻¹ * ((A.raw.compute n).width + (B.raw.compute n).width) +
        3 * approximationBudget bound n <=
      margin⁻¹ * (inputEps.val + inputEps.val) +
        3 * budgetEps.val :=
      rat_add_le_add
        (Rat.mul_le_mul_of_nonneg_left (rat_add_le_add hA hB) hinv0)
        (Rat.mul_le_mul_of_nonneg_left hc (by decide +kernel))
    _ <= eps.val := by
      dsimp [inputEps, budgetEps]
      rw [Rat.div_def]
      have hm : margin ≠ 0 := Rat.ne_of_gt A.margin_pos
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
        Rat.mul_inv_cancel margin hm, Rat.mul_inv_cancel]

theorem candidate_future_contained_cross_expand_of_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw)
    (k n : Nat) (hkn : k <= n) :
    ((candidate A).compute n).NestedIn
      (QBox.expand ((candidate B).compute k) (crossRadius A B k)) := by
  let q := (B.raw.compute k).midpoint
  let r := (A.raw.compute n).midpoint
  let x := (approximation B k).midpoint
  let y := (approximation A n).midpoint
  have hdist0 := sqrtCertificate_midpoint_lipschitz
    A.margin_pos (approximation_spec B k) (approximation_spec A n)
    (B.margin_sq_le_center k) (A.margin_sq_le_center n)
  have hinput0 := midpoint_sub_le_width_add_width_of_equiv A B hAB n k
  have hAw := width_antitone A k n hkn
  have hinput : qabs (r - q) <=
      (A.raw.compute k).width + (B.raw.compute k).width :=
    Rat.le_trans hinput0 (rat_add_le_add hAw Rat.le_refl)
  have hwidthk := approximation_width_le_budget B k
  have hwidthn0 := approximation_width_le_budget A n
  have hbudget := approximationBudget_antitone bound hkn
  have hwidthn := Rat.le_trans hwidthn0 hbudget
  have hinv0 : 0 <= margin⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 A.margin_pos)
  have hbudget0 := approximationBudget_nonnegative bound k
  let midpointRadius : Rat :=
    margin⁻¹ * ((A.raw.compute k).width + (B.raw.compute k).width) +
      2 * approximationBudget bound k
  have hdist : qabs (y - x) <= midpointRadius := by
    calc
      qabs (y - x) <=
          margin⁻¹ * qabs (r - q) +
            (approximation B k).width + (approximation A n).width := hdist0
      _ <= margin⁻¹ * ((A.raw.compute k).width +
            (B.raw.compute k).width) +
            approximationBudget bound k + approximationBudget bound k :=
        rat_add_le_add
          (rat_add_le_add
            (Rat.mul_le_mul_of_nonneg_left hinput hinv0) hwidthk) hwidthn
      _ <= midpointRadius := by
        dsimp [midpointRadius]
        grind
  have hIk := (approximation_spec B k).2.1
  have hIn := (approximation_spec A n).2.1
  have hmk := QInterval.midpoint_mem hIk
  have hmn := QInterval.midpoint_mem hIn
  have hnk := midpoint_endpoint_bounds hIn
  have hlow : -midpointRadius <= y - x := by
    exact Rat.le_trans
      (by grind : -midpointRadius <= -qabs (y - x))
      (neg_qabs_le_self (y - x))
  have hupp : y - x <= midpointRadius :=
    Rat.le_trans (self_le_qabs (y - x)) hdist
  have hinputWidth0 : 0 <=
      (A.raw.compute k).width + (B.raw.compute k).width :=
    Rat.add_nonneg (A.valid.1 k) (B.valid.1 k)
  have hradius0 : 0 <= crossRadius A B k := by
    unfold crossRadius
    exact Rat.add_nonneg
      (Rat.mul_nonneg hinv0 hinputWidth0)
      (Rat.mul_nonneg (by decide +kernel) hbudget0)
  have hcover : midpointRadius + approximationBudget bound k <=
      crossRadius A B k := by
    unfold crossRadius
    grind
  unfold candidate QBox.ofRealInterval QBox.NestedIn QBox.expand
  simp only [QComplex.le_def]
  constructor
  · constructor
    · unfold QInterval.width at hwidthk hwidthn
      grind [Rat.sub_eq_add_neg]
    · grind
  · constructor
    · unfold QInterval.width at hwidthk hwidthn
      grind [Rat.sub_eq_add_neg]
    · grind

def crossSqrtComplex {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) : ComplexCompute :=
  ComplexCompute.cauchyStabilize (candidate A) (crossRadius A B)

theorem crossSqrtComplex_valid {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) :
    (crossSqrtComplex A B).Valid := by
  unfold crossSqrtComplex
  apply ComplexCompute.cauchyStabilize_valid
  · exact candidate_ordered A
  · exact candidate_widths_shrink A
  · intro k n hkn
    apply QBox.nested_trans (candidate_future_contained_expand A k n hkn)
    exact QBox.expand_mono_radius _ (radius_le_crossRadius A B k)
  · exact crossRadius_shrinks A B

theorem sqrtComplex_equiv_cross {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) :
    (sqrtComplex A).Equiv (crossSqrtComplex A B) := by
  unfold sqrtComplex crossSqrtComplex
  apply ComplexCompute.cauchyStabilize_equiv_of_common_candidate
  · exact candidate_ordered A
  · exact candidate_future_contained_expand A
  · intro k n hkn
    apply QBox.nested_trans (candidate_future_contained_expand A k n hkn)
    exact QBox.expand_mono_radius _ (radius_le_crossRadius A B k)

theorem crossRadius_comm {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (n : Nat) :
    crossRadius A B n = crossRadius B A n := by
  simp [crossRadius, Rat.add_comm]

theorem crossSqrtComplex_equiv_of_input_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (crossSqrtComplex A B).Equiv (crossSqrtComplex B A) := by
  intro n
  apply (ComplexCompute.compareAt_overlap_iff
    (crossSqrtComplex A B) (crossSqrtComplex B A) n n).2
  have hleft : ((candidate A).compute n).NestedIn
      ((crossSqrtComplex A B).compute n) := by
    unfold crossSqrtComplex
    apply ComplexCompute.cauchyStabilize_contains_external
      (external := fun m => (candidate A).compute m)
    · intro k m hkm
      apply QBox.nested_trans (candidate_future_contained_expand A k m hkm)
      exact QBox.expand_mono_radius _ (radius_le_crossRadius A B k)
    · exact Nat.le_refl n
  have hright : ((candidate A).compute n).NestedIn
      ((crossSqrtComplex B A).compute n) := by
    unfold crossSqrtComplex
    apply ComplexCompute.cauchyStabilize_contains_external
      (external := fun m => (candidate A).compute m)
    · intro k m hkm
      simpa [crossRadius_comm] using
        candidate_future_contained_cross_expand_of_equiv A B hAB k m hkm
    · exact Nat.le_refl n
  exact ⟨
    QComplex.le_trans hleft.1
      (QComplex.le_trans (candidate_ordered A n) hright.2),
    QComplex.le_trans hright.1
      (QComplex.le_trans (candidate_ordered A n) hleft.2)⟩

theorem sqrtComplex_equiv_of_input_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (sqrtComplex A).Equiv (sqrtComplex B) := by
  exact ComplexCompute.equiv_trans
    (sqrtComplex_valid A) (crossSqrtComplex_valid A B) (sqrtComplex_valid B)
    (sqrtComplex_equiv_cross A B)
    (ComplexCompute.equiv_trans
      (crossSqrtComplex_valid A B) (crossSqrtComplex_valid B A)
      (sqrtComplex_valid B)
      (crossSqrtComplex_equiv_of_input_equiv A B hAB)
      (ComplexCompute.equiv_symm (sqrtComplex_equiv_cross B A)))

theorem sqrt_equiv_of_input_equiv
    {bound : Nat} {margin : Rat}
    (A B : PositiveInput bound margin) (hAB : A.raw.Equiv B.raw) :
    (sqrt A).Equiv (sqrt B) :=
  ComplexCompute.realPart_equiv (sqrtComplex_equiv_of_input_equiv A B hAB)

end PositiveInput

end RepresentedPositiveSquareRoot
end ComputableAnalysis


