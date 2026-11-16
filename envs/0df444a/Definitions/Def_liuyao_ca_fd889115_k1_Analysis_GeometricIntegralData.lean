-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricIntegralData
-- name    : liuyao_ca_fd889115_k1_Analysis_GeometricIntegralData
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:49:52.185491+00:00
-- url     : https://prove2.me/theorems/7ea1045a-65cf-4cf6-9fe7-04025c86736f
-- title:
--   Computable analysis · GeometricIntegralData · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/GeometricIntegralData.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricFTCData
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCMonomials
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCStepQuadrature
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCRealProduct
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueCongruence

set_option autoImplicit true

/-! Global finite-interval FTC data and a bounded integral computation for the
actual normalized geometric sine. No independent trigonometric series is used. -/
namespace ComputableAnalysis.GeometricIntegralData
open ComputableCoefficient RealApproximationOrder FTCRealCalculus GeometricTrig
set_option maxHeartbeats 800000

theorem trig_small (cosine : Bool) (t : Rat) : Small (valueFor cosine t) 1 := by
  have H := GeometricFTCData.family_small 1 0 cosine t
  simpa only [GeometricFTCData.family,Rat.one_mul,Rat.pow_zero] using H

theorem derivative_small (cosine : Bool) (t : Rat) : Small (derivativeValue cosine t) 8 := by
  have H : Small (if cosine then Value.neg (valueFor false t) else valueFor true t) 1 := by
    cases cosine
    · exact trig_small true t
    · exact (trig_small false t).neg
  simpa only [derivativeValue,pairSlope,Rat.mul_one] using pi_small.mul H

/-- The established geometric first-order estimate includes quadrant joins. -/
def trigStep (cosine : Bool) (a b : Rat) : Step (valueFor cosine) (derivativeValue cosine) a b where
  error := 1600
  error_nonnegative := by decide +kernel
  radius := ⟨1/4,by decide +kernel⟩
  firstOrder u v _ huv _ hs := full_firstOrder_small cosine huv hs
  variation := 256
  variation_nonnegative := by decide +kernel
  lipschitz u v _ huv _ := derivative_value_lipschitz cosine huv

theorem pi_lower (n : Nat) : 1≤(pi.compute n).lo := by
  have H := (unitArea_bounds n).1
  simp only [pi,RealCompute.scaleRat,RealCompute.scaleRatCompute,RealCompute.schedule,areaSchedule,
    if_pos (show (0:Rat)≤4 by decide +kernel)]
  grind only

def inversePi : Value := Value.positiveInv piValue 0 (by
  have H := pi_lower 0
  change 0<(pi.compute 0).lo
  grind only)

private theorem pi_sample_lower (m : Nat) (hm : piValue.observation 0≤m)
    (s : RealCompute.Certified → Rat) (hs : Samples m s) : 1≤piValue.sample s := by
  have H := piValue.encloses 0 m hm s hs
  have P := pi_lower 0
  change (pi.compute 0).lo≤piValue.sample s ∧ _ at H
  grind only

theorem inversePi_small : Small inversePi 1 := by
  apply small_of_samples _ _ (piValue.observation 0)
  intro m hm s hs
  have hp := pi_sample_lower m hm s hs
  have hp0 : 0<piValue.sample s := by grind only
  have H := QInterval.one_div_le_one_div_of_pos (show (0:Rat)<1 by decide +kernel) hp
  change qabs ((piValue.sample s)⁻¹)≤1
  rw [qabs_eq_self_of_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr hp0))]
  simpa only [Rat.div_def,Rat.one_mul,show (1:Rat)⁻¹=1 by decide +kernel] using H

theorem pi_inverse_identity : (Value.mul piValue inversePi).real.preferred.Equiv (RealCompute.ofRat 1) := by
  apply Value.equiv_of_samples _ (Value.rational 1) (piValue.observation 0)
  intro m hm s hs
  have hp := pi_sample_lower m hm s hs
  change piValue.sample s*(piValue.sample s)⁻¹=1
  exact Rat.mul_inv_cancel _ (by grind only)

/-- A bounded geometric integral of sine; the normalization is explicit. -/
def sineIntegral (t : Rat) : Value := Value.mul (Value.neg inversePi) (valueFor true t)

theorem sineIntegral_small (t : Rat) : Small (sineIntegral t) 1 := by
  simpa only [sineIntegral,Rat.mul_one] using inversePi_small.neg.mul (trig_small true t)

def sineIntegralStep (a b : Rat) : Step sineIntegral (valueFor false) a b := by
  apply ((trigStep true a b).mul_constant (Value.neg inversePi) 1 (by decide +kernel) inversePi_small.neg).congr
  · intro t; exact RealCompute.equiv_refl _ (sineIntegral t).real.valid
  · intro t
    apply Value.equiv_of_samples _ (valueFor false t) (piValue.observation 0)
    intro m hm s hs
    have hp := pi_sample_lower m hm s hs
    have hc := Rat.inv_mul_cancel (piValue.sample s) (by grind only : piValue.sample s≠0)
    simp only [Value.mul,Value.neg,inversePi,Value.positiveInv,derivativeValue,pairSlope,if_true]
    grind [Rat.mul_comm]

/-- A usable bound near the removable endpoint, derived by geometric FTC. -/
theorem sine_linear_bound (t : Rat) (ht : 0≤t) : Small (valueFor false t) (8*t) := by
  have H := lipschitz_of_firstOrder (trigStep false 0 t).firstOrder
    (trigStep false 0 t).error_nonnegative (trigStep false 0 t).radius.property
    (fun x _ _ => derivative_small false x)
  have B := H 0 t (Rat.le_refl) ht (Rat.le_refl)
  have he := RealCompute.sub_equiv (x := (valueFor false t).real.preferred)
    (x' := (valueFor false t).real.preferred) (y := (valueFor false 0).real.preferred) (y' := RealCompute.ofRat 0)
    (valueFor false t).real.valid (valueFor false t).real.valid (valueFor false 0).real.valid (RealCompute.ofRat_valid 0)
    (RealCompute.equiv_refl _ (valueFor false t).real.valid) (by rw [valueFor_raw]; exact sample_zero false)
  have he' : (sub (valueFor false t) (Value.rational 0)).real.preferred.Equiv (valueFor false t).real.preferred := by
    apply arithmetic_identity; intro s; simp only [sub,Value.rational]; grind only
  have H' := B.congr (RealCompute.equiv_trans (sub (valueFor false t) (valueFor false 0)).real.valid
    (sub (valueFor false t) (Value.rational 0)).real.valid (valueFor false t).real.valid he he')
  simpa only [Rat.sub_eq_add_neg,Rat.neg_zero,Rat.add_zero] using H'

private def shiftedTrigStep (cosine : Bool) (a b shift : Rat) :
    Step (fun t => valueFor cosine (t + shift)) (fun t => derivativeValue cosine (t + shift)) a b where
  error := 1600
  error_nonnegative := by decide +kernel
  radius := ⟨1 / 4, by decide +kernel⟩
  firstOrder := by
    intro u v _ huv _ hs
    have he : v + shift - (u + shift) = v - u := by grind only
    have h := full_firstOrder_small cosine (u := u + shift) (v := v + shift)
      (by grind only) (by rw [he]; exact hs)
    simpa only [remainderValue, he] using h
  variation := 256
  variation_nonnegative := by decide +kernel
  lipschitz := by
    intro u v _ huv _
    have he : v + shift - (u + shift) = v - u := by grind only
    have h := derivative_value_lipschitz cosine (u := u + shift) (v := v + shift) (by grind only)
    simpa only [he] using h

private def pairing (dot : Bool) (shift t : Rat) : Value :=
  if dot then
    Value.add (Value.mul (valueFor true t) (valueFor true (t + shift)))
      (Value.mul (valueFor false t) (valueFor false (t + shift)))
  else
    sub (Value.mul (valueFor true t) (valueFor false (t + shift)))
      (Value.mul (valueFor false t) (valueFor true (t + shift)))

private theorem pairing_constant (dot : Bool) (a b shift : Rat) (hab : a ≤ b) :
    Same (pairing dot shift b) (pairing dot shift a) := by
  let product (left right : Bool) :=
    (trigStep left a b).mul (shiftedTrigStep right a b shift)
      1 1 8 8 (by decide) (by decide) (by decide) (by decide)
      (fun t _ _ => trig_small left t) (fun t _ _ => trig_small right (t + shift))
      (fun t _ _ => derivative_small left t) (fun t _ _ => derivative_small right (t + shift))
  have H : Step (pairing dot shift) (fun _ => Value.rational 0) a b := by
    cases dot
    · refine ((product true false).subtract (product false true)).congr
        (fun t => Same.refl (pairing false shift t)) ?_
      intro t
      apply arithmetic_identity
      intro s
      simp only [Value.add, Value.mul, Value.neg, Value.rational, derivativeValue, pairSlope, sub]
      grind only
    · refine ((product true true).add (product false false)).congr
        (fun t => Same.refl (pairing true shift t)) ?_
      intro t
      apply arithmetic_identity
      intro s
      simp only [Value.add, Value.mul, Value.neg, Value.rational, derivativeValue, pairSlope, if_true]
      grind only
  have h := H.ftc ((Step.constant (Value.rational 0) a b).hasIntegral hab)
  have hzero : Same (sub (pairing dot shift b) (pairing dot shift a)) (Value.rational 0) :=
    Same.trans (Y := sub (Value.rational 0) (Value.rational 0)) (Same.symm h)
      (RealCompute.sub_self_equiv_zero (RealCompute.ofRat_valid 0))
  exact Same.trans (Y := Value.add (sub (pairing dot shift b) (pairing dot shift a)) (pairing dot shift a))
    (RealCompute.equiv_symm (RealCompute.sub_add_cancel_equiv (pairing dot shift b).real.valid (pairing dot shift a).real.valid))
    ((hzero.add (Same.refl (pairing dot shift a))).trans (arithmetic_identity _ _ (by
      intro s
      simp [Value.add, Value.rational, Rat.zero_add])))

private theorem difference (dot : Bool) (x y : Rat) :
    Same (pairing dot (x - y) y) (valueFor dot (x - y)) := by
  let shift := x - y
  have h₁ : y + shift = x := by dsimp [shift]; grind only
  have h₀ : 0 + shift = shift := Rat.zero_add _
  have h : Same (pairing dot shift y) (pairing dot shift 0) := by
    by_cases hy : 0 ≤ y
    · exact pairing_constant dot 0 y shift hy
    · exact (pairing_constant dot y 0 shift (by grind only)).symm
  have initial (cosine : Bool) :
      Same (valueFor cosine 0) (Value.rational (if cosine then 1 else 0)) := by
    change (valueFor cosine 0).real.preferred.Equiv _
    rw [valueFor_raw]
    exact sample_zero cosine
  apply h.trans
  unfold pairing
  rw [h₀]
  cases dot
  · refine Same.trans (((initial true).mul (Same.refl (valueFor false shift))).sub
      ((initial false).mul (Same.refl (valueFor true shift)))) ?_
    apply arithmetic_identity
    intro s
    simp [shift, sub, Value.mul, Value.rational]
    grind only
  · refine Same.trans (((initial true).mul (Same.refl (valueFor true shift))).add
      ((initial false).mul (Same.refl (valueFor false shift)))) ?_
    apply arithmetic_identity
    intro s
    simp [shift, Value.add, Value.mul, Value.rational, Rat.one_mul, Rat.zero_mul, Rat.add_zero]

/-- The dot product of two geometric circle points is the cosine of
the difference of their normalized angles. -/
theorem cosine_difference (x y : Rat) :
    Same (Value.add (Value.mul (valueFor true y) (valueFor true x))
      (Value.mul (valueFor false y) (valueFor false x))) (valueFor true (x - y)) := by
  have h := difference true x y
  have he : y + (x - y) = x := by grind only
  simpa only [pairing, if_true, he] using h

theorem cosine_even (x : Rat) : Same (valueFor true (-x)) (valueFor true x) := by
  have h₁ := cosine_difference x 0
  have h₂ := cosine_difference 0 x
  rw [show x - 0 = x by grind only] at h₁
  rw [show 0 - x = -x by grind only] at h₂
  refine h₂.symm.trans (Same.trans ?_ h₁)
  apply arithmetic_identity
  intro s
  simp only [Value.add, Value.mul]
  grind only

/-- A rational lower bound on the cosine gap on a half turn. -/
theorem cosine_gap {s x : Rat} (hs : 0 < s) (hsx : s ≤ x) (hx : x ≤ 1) :
    FTCRealOrder.LE (valueFor true x) (Value.rational (1 - (s / 4) * (s / 4))) := by
  change (valueFor true x).real.preferred.Le (RealCompute.ofRat _)
  rw [valueFor_raw]
  by_cases hhalf : x ≤ 1 / 2
  · have h := sample_on_closed_quarter 0 true (q := x) (by grind only) (by grind only)
    change (sample true x).Equiv (quarter true (x - (0 : Rat) / 2)) at h
    rw [show x - (0 : Rat) / 2 = x by grind only] at h
    refine RealCompute.le_trans (quarter_valid true x)
      (RealCompute.le_of_equiv (sample_valid true x) (quarter_valid true x) h) ?_
    open ArctanSecantFoundation ArctanInverseConstruction in
    obtain ⟨n, hn⟩ := width_shrinks ⟨s / 8, by grind only⟩
    let u := (slope x n).lo
    let v := (slope x n).hi
    have hgeo := slope_geometry x n
    have hu : 0 ≤ u := hgeo.1
    have hv : 0 ≤ v ∧ v ≤ 1 := ⟨Rat.le_trans hgeo.1 hgeo.2.1, hgeo.2.2.1⟩
    have huw : v - u = ArctanInverseConstruction.width n := hgeo.2.2.2
    have hwidth : v - u ≤ s / 8 := huw ▸ hn n (Nat.le_refl n)
    let p := ArctanInverseConstruction.precision n
    have htar := (slope_target (show 0 ≤ x ∧ x ≤ 1 / 2 from ⟨by grind only, hhalf⟩) n).2 p p
    change (RealCompute.scaleRatCompute (2 * x) unitArea p).lo ≤
      ((ArctanSecantFoundation.value v).compute p).hi at htar
    simp only [RealCompute.scaleRatCompute, if_pos (show 0 ≤ 2 * x by grind only)] at htar
    have ha := Rat.mul_le_mul_of_nonneg_left (unitArea_bounds n).1 (show 0 ≤ 2 * x by grind only)
    have hb := (ArctanSecantFoundation.increment_bounds (x := 0) (y := v)
      (by decide) hv.1 p).2
    have hz : ((ArctanSecantFoundation.value 0).compute p).hi = 0 :=
      ArctanGeometry.arctanIntegralRectangleCompute_zero_upper _
    rw [hz] at hb
    rw [show ArctanGeometry.integralKernel 0 = 1 by decide +kernel] at hb
    have hc := ArctanInverseConstruction.source_width v hv n
    change ((ArctanSecantFoundation.value v).compute p).hi -
      ((ArctanSecantFoundation.value v).compute p).lo ≤ ArctanInverseConstruction.width n / 128 at hc
    change 2 * x * ((1 : Rat) / 4) ≤ 2 * x * (unitArea.compute p).lo at ha
    have hu' : s / 4 ≤ u := by
      have hsmall := hn n (Nat.le_refl n)
      grind only
    have hu1 : u ≤ 1 := Rat.le_trans hgeo.2.1 hgeo.2.2.1
    have hsq : (s / 4) * (s / 4) ≤ u * u :=
      Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hu' (by grind only))
        (Rat.mul_le_mul_of_nonneg_left hu' hu)
    have hsq1 : u * u ≤ 1 := by
      have h := Rat.mul_le_mul_of_nonneg_right hu1 hu
      grind only
    have hsq0 : 0 ≤ (s / 4) * (s / 4) := Rat.mul_nonneg (by grind only) (by grind only)
    have hproduct := Rat.mul_le_mul_of_nonneg_left (show 1 + u * u ≤ 2 by grind only) hsq0
    have hupper : ((quarter true x).compute n).hi ≤ 1 - (s / 4) * (s / 4) := by
      rw [quarter_compute]
      change (1 - u * u) / (1 + u * u) ≤ 1 - (s / 4) * (s / 4)
      have hden := RationalCircle.Stage.one_add_square_pos u
      apply Rat.le_of_mul_le_mul_right (c := 1 + u * u) _ hden
      rw [Rat.div_mul_cancel (Rat.ne_of_gt hden)]
      grind only
    intro i j
    exact Rat.le_trans (RealCompute.le_refl _ (quarter_valid true x) i n) hupper
  · have h := sample_on_closed_quarter 1 true (q := x) (by grind only) (by grind only)
    change (sample true x).Equiv (-(quarter false (x - (1 : Rat) / 2))) at h
    have hv := RealCompute.neg_valid (quarter_valid false (x - (1 : Rat) / 2))
    refine RealCompute.le_trans hv (RealCompute.le_of_equiv (sample_valid true x) hv h) ?_
    have hnonneg : (RealCompute.ofRat 0).Le (quarter false (x - (1 : Rat) / 2)) :=
      fun _ j => Rat.le_trans (quarter_bounds false _ j).1
        (RealCompute.interval_order_of_valid _ (quarter_valid false _) j)
    have hnonpos := RealCompute.le_neg_le_neg hnonneg
    have hs4 : s / 4 ≤ 1 := by grind only
    have hsq := Rat.mul_le_mul_of_nonneg_right hs4 (show 0 ≤ s / 4 by grind only)
    intro i j
    exact Rat.le_trans (hnonpos i 0) (show -(0 : Rat) ≤ 1 - (s / 4) * (s / 4) by grind only)

/-- The determinant of two geometric circle points is the sine of
the difference of their normalized angles. -/
theorem sine_difference (x y : Rat) :
    Same (sub (Value.mul (valueFor true y) (valueFor false x))
      (Value.mul (valueFor false y) (valueFor true x))) (valueFor false (x - y)) := by
  have h := difference false x y
  have he : y + (x - y) = x := by grind only
  simpa only [pairing, Bool.false_eq_true, if_false, he] using h

private def productStep (left right : Bool) (a b : Rat) :=
  (trigStep left a b).mul (trigStep right a b) 1 1 8 8
    (by decide) (by decide) (by decide) (by decide)
    (fun t _ _ => trig_small left t) (fun t _ _ => trig_small right t)
    (fun t _ _ => derivative_small left t) (fun t _ _ => derivative_small right t)

/-- The two squares use the same geometric sine and cosine as the Fourier phase. -/
def trigSquare (cosine : Bool) (t : Rat) : Value :=
  Value.mul (valueFor cosine t) (valueFor cosine t)

private def squareSum (t : Rat) : Value :=
  Value.add (trigSquare false t) (trigSquare true t)

private def squareSumStep (a b : Rat) : Step squareSum (fun _ => Value.rational 0) a b := by
  apply ((productStep false false a b).add (productStep true true a b)).congr
  · intro t
    exact Same.refl (squareSum t)
  · intro t
    apply arithmetic_identity
    intro s
    simp only [Value.add,Value.mul,Value.neg,Value.rational,derivativeValue,pairSlope,
      if_true,if_false,Bool.false_eq_true]
    grind only

private theorem squareSum_zero : Same (squareSum 0) (Value.rational 1) := by
  have hs : Same (valueFor false 0) (Value.rational 0) := by
    change (valueFor false 0).real.preferred.Equiv (RealCompute.ofRat 0)
    rw [valueFor_raw]
    exact sample_zero false
  have hc : Same (valueFor true 0) (Value.rational 1) := by
    change (valueFor true 0).real.preferred.Equiv (RealCompute.ofRat 1)
    rw [valueFor_raw]
    exact sample_zero true
  exact ((hs.mul hs).add (hc.mul hc)).trans (arithmetic_identity _ _ (by
    intro s
    simp only [Value.add,Value.mul,Value.rational]
    decide +kernel))

private theorem squareSum_difference (a b : Rat) (hab : a ≤ b) :
    Same (sub (squareSum b) (squareSum a)) (Value.rational 0) := by
  have H := (squareSumStep a b).hasIntegral hab
  let Z := Value.rational 0
  have H0 : Integral.HasIntegral (LipschitzIntegralBounds.onInterval (fun _ => Z) a b)
      (scale (b-a) Z).real.preferred :=
    (Integral.constant_hasIntegral _ Z.real.valid a b hab).congrFunction
      ⟨rfl,rfl,fun _ _ _ n => (RealCompute.equiv_refl _ Z.real.valid) n⟩
  exact Same.trans (X := sub (squareSum b) (squareSum a)) (Y := scale (b-a) Z) (H.unique H0)
    (arithmetic_identity (scale (b-a) Z) Z
      (by intro s; simp only [Z,scale,Value.rational,Rat.mul_zero]))

theorem squareSum_one (t : Rat) : Same (squareSum t) (Value.rational 1) := by
  have Z : Same (sub (squareSum t) (squareSum 0)) (Value.rational 0) := by
    by_cases h : 0 ≤ t
    · exact squareSum_difference 0 t h
    · have K := (squareSum_difference t 0 (by grind only)).neg
      exact Same.trans (X := sub (squareSum t) (squareSum 0))
        (arithmetic_identity (sub (squareSum t) (squareSum 0))
        (Value.neg (sub (squareSum 0) (squareSum t)))
        (by intro s; simp only [Value.neg,sub]; grind only))
          (K.trans (arithmetic_identity _ _ (by
            intro s; simp only [Value.neg,Value.rational,Rat.neg_zero])))
  exact Same.trans (X := squareSum t) (arithmetic_identity (squareSum t) (Value.add (sub (squareSum t) (squareSum 0)) (squareSum 0))
    (by intro s; simp only [Value.add,sub]; grind only)) ((Z.add squareSum_zero).trans
      (arithmetic_identity _ _ (by intro s; simp only [Value.add,Value.rational,Rat.zero_add])))

private def squareCorrection (cosine : Bool) (t : Rat) : Value :=
  scale (if cosine then 1/2 else -1/2)
    (Value.mul inversePi (Value.mul (valueFor false t) (valueFor true t)))

/-- Endpoint computation used by the FTC for the squares on the unit interval. -/
def squareEndpoint (cosine : Bool) (t : Rat) : Value :=
  Value.add (Value.rational (t/2)) (squareCorrection cosine t)

def trigSquareStep (cosine : Bool) (a b : Rat) (ha : 0 ≤ a) (hb : b ≤ 1) :
    Step (squareEndpoint cosine) (trigSquare cosine) a b := by
  let L := ((FTCMonomials.normalized 0).restrict a b ha hb).scale (1/2)
  let P := ((productStep false true a b).mul_constant inversePi 1 (by decide)
    inversePi_small).scale (if cosine then 1/2 else -1/2)
  apply (L.add P).congr
  · intro t
    apply arithmetic_identity
    intro s
    simp only [Value.add,Value.mul,Value.rational,squareEndpoint,squareCorrection,scale]
    have h : ((0+1 : Nat) : Rat) = 1 := rfl
    rw [h,Rat.pow_one,Rat.div_def,Rat.div_def]
    grind only
  · intro t
    have H : Same (Value.rational 1) (squareSum t) := (squareSum_one t).symm
    let U := Value.mul inversePi (Value.mul piValue
      (sub (trigSquare true t) (trigSquare false t)))
    have he : Same U (sub (trigSquare true t) (trigSquare false t)) := by
      apply Value.equiv_of_samples _ _ (piValue.observation 0)
      intro m hm s hs
      have hp := pi_sample_lower m hm s hs
      have hc := Rat.inv_mul_cancel (piValue.sample s) (by grind only : piValue.sample s≠0)
      simp only [U,Value.mul,inversePi,Value.positiveInv,sub]
      grind only
    let c : Rat := if cosine then 1/2 else -1/2
    refine Same.trans (Y := Value.add (Value.rational (1/2)) (scale c U)) ?_ ?_
    · apply arithmetic_identity
      intro s
      simp only [L,P,FTCMonomials.normalized,Step.restrict,Step.add,Step.scale,Step.mul_constant,
        productStep,Step.mul,U,trigSquare,derivativeValue,pairSlope,Value.add,Value.mul,Value.neg,
        Value.rational,sub,scale,Rat.pow_zero,if_pos,if_neg,Bool.false_eq_true]
      grind only
    have hhalf : Same (Value.rational (1/2)) (scale (1/2) (squareSum t)) :=
      Same.trans (Y := scale (1/2) (Value.rational 1))
        (arithmetic_identity (Value.rational (1/2)) (scale (1/2) (Value.rational 1))
          (by intro s; simp only [Value.rational,scale,Rat.mul_one])) (H.scale _)
    refine (hhalf.add (he.scale c)).trans ?_
    apply arithmetic_identity
    intro s
    cases cosine <;> simp only [c,squareSum,Value.add,scale,sub,if_true,if_false,Bool.false_eq_true] <;>
      grind only

def trigSquareIntegral (cosine : Bool) (a b : Rat) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : RealCompute :=
  FTCStepQuadrature.integral (trigSquareStep cosine a b ha hb) hab

theorem trigSquareIntegral_hasIntegral (cosine : Bool) (a b : Rat) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) :
    Integral.HasIntegral (LipschitzIntegralBounds.onInterval (trigSquare cosine) a b)
      (trigSquareIntegral cosine a b ha hab hb) :=
  FTCStepQuadrature.hasIntegral (trigSquareStep cosine a b ha hb) hab

theorem trigSquareIntegral_equiv_endpoint (cosine : Bool) (a b : Rat) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) :
    (trigSquareIntegral cosine a b ha hab hb).Equiv
      (sub (squareEndpoint cosine b) (squareEndpoint cosine a)).real.preferred :=
  FTCStepQuadrature.integral_equiv_endpoint (trigSquareStep cosine a b ha hb) hab

private theorem cosine_at_half : Same (valueFor true (1/2)) (Value.rational 0) := by
  change (valueFor true (1/2)).real.preferred.Equiv (RealCompute.ofRat 0)
  rw [valueFor_raw]
  have H := sample_on_closed_quarter 1 true (q := 1/2) (by decide +kernel) (by decide +kernel)
  have K : turn 1 true ((1:Rat)/2-(1:Int)/2) = -(quarter false 0) := by
    rw [show (1:Rat)/2-(1:Int)/2 = 0 by decide +kernel]
    simp [turn]
  rw [K] at H
  refine RealCompute.equiv_trans (sample_valid _ _) (RealCompute.neg_valid (quarter_valid false 0))
    (RealCompute.ofRat_valid 0) H ?_
  have hq : (quarter false 0).Equiv (RealCompute.ofRat 0) := quarter_zero false
  have hz : (-(RealCompute.ofRat 0)).Equiv (RealCompute.ofRat 0) :=
    arithmetic_identity (Value.neg (Value.rational 0)) (Value.rational 0)
      (by intro s; simp only [Value.neg,Value.rational,Rat.neg_zero])
  exact RealCompute.equiv_trans (RealCompute.neg_valid (quarter_valid false 0))
    (RealCompute.neg_valid (x := RealCompute.ofRat 0) (RealCompute.ofRat_valid 0))
    (RealCompute.ofRat_valid 0) (RealCompute.neg_equiv hq) hz

private theorem squareEndpoint_of_zero_factor (cosine : Bool) (t : Rat)
    (zero : Same (valueFor false t) (Value.rational 0) ∨
      Same (valueFor true t) (Value.rational 0)) :
    Same (squareEndpoint cosine t) (Value.rational (t/2)) := by
  have Z : Same (Value.mul (valueFor false t) (valueFor true t)) (Value.rational 0) := by
    rcases zero with hs | hc
    · refine (hs.mul (Same.refl _)).trans (arithmetic_identity _ _ ?_)
      intro s
      simp only [Value.mul,Value.rational,Rat.zero_mul]
    · refine ((Same.refl _).mul hc).trans (arithmetic_identity _ _ ?_)
      intro s
      simp only [Value.mul,Value.rational,Rat.mul_zero]
  refine ((Same.refl _).add (((Same.refl inversePi).mul Z).scale _)).trans ?_
  apply arithmetic_identity
  intro s
  simp only [Value.add,Value.mul,Value.rational,scale,Rat.mul_zero,Rat.add_zero]

/-- Both geometric squares integrate to one quarter on the first quadrant,
with the angle parameter normalized by pi. -/
theorem trigSquareIntegral_quarter (cosine : Bool) :
    (trigSquareIntegral cosine 0 (1/2) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)).Equiv (RealCompute.ofRat (1/4)) := by
  let I := parameter (trigSquareIntegral cosine 0 (1/2) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)) (trigSquareIntegral_hasIntegral cosine 0 (1/2)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)).valid
  change Same I (Value.rational (1/4))
  have H : Same I (sub (squareEndpoint cosine (1/2)) (squareEndpoint cosine 0)) :=
    trigSquareIntegral_equiv_endpoint cosine 0 (1/2)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h : Same (valueFor false 0) (Value.rational 0) := by
    change (valueFor false 0).real.preferred.Equiv (RealCompute.ofRat 0)
    rw [valueFor_raw]
    exact sample_zero false
  refine H.trans (((squareEndpoint_of_zero_factor cosine _ (Or.inr cosine_at_half)).sub
    (squareEndpoint_of_zero_factor cosine _ (Or.inl h))).trans ?_)
  apply arithmetic_identity
  intro s
  simp only [Value.rational,sub]
  decide +kernel

end ComputableAnalysis.GeometricIntegralData


