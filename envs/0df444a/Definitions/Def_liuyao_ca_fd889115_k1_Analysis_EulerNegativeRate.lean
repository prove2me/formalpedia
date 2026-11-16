-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerNegativeRate
-- name    : liuyao_ca_fd889115_k1_Analysis_EulerNegativeRate
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:50:44.91354+00:00
-- url     : https://prove2.me/theorems/c1c746ec-835e-4677-88d5-032123745c0f
-- title:
--   Computable analysis · EulerNegativeRate · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/EulerNegativeRate.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerRealOrder
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_TaylorPolynomialValues

set_option autoImplicit true

/-! Negative-rate Euler evaluation for arbitrary represented nonnegative
coefficients. Rational rate samples are primary in the proof; joint interval
images preserve the same sampled coefficient in every finite inequality. -/
namespace ComputableAnalysis.EulerNegativeRate
open ComputableCoefficient RealApproximationOrder RawLimit FTCRealOrder FTCRealCalculus
open TaylorPolynomialValues
set_option maxHeartbeats 800000

def argument (C : Value) (t : Rat) : Value := Value.neg (scale t C)

def evaluate (C : Value) (t : Rat) : Value :=
  parameter (EulerReal.eval (argument C t).real.preferred) (EulerReal.eval_valid (argument C t).real.valid)

def derivative (C : Value) (t : Rat) : Value := Value.neg (Value.mul C (evaluate C t))

def remainder (C : Value) (u v : Rat) : Value :=
  sub (sub (evaluate C v) (evaluate C u)) (scale (v-u) (derivative C u))

def majorant (C : Value) (u v : Rat) : Value :=
  scale ((v-u)*(v-u)) (Value.mul (Value.mul C C) (evaluate C u))

theorem rational_image (C : Value) (q t : Rat) (n : Nat)
    (hq : (C.real.compute n).lo≤q ∧ q≤(C.real.compute n).hi) :
    InInterval (EulerReal.negativeSample q t).real.preferred ((evaluate C t).real.compute n) := by
  have hp := QInterval.scaleRat_mem (r := t) hq
  have harg : ((argument C t).real.compute n).lo≤ -q*t ∧ -q*t≤((argument C t).real.compute n).hi := by
    change -((scale t C).real.compute n).hi≤ -q*t ∧ -q*t≤ -((scale t C).real.compute n).lo
    change ((scale t C).real.compute n).lo≤t*q ∧ t*q≤((scale t C).real.compute n).hi at hp
    constructor <;> grind only
  exact EulerReal.enclosure_covers (x := (argument C t).real.preferred) (argument C t).real.valid
    (EulerReal.input_within (argument C t).real.valid) n harg

private theorem product_image (C : Value) (q t : Rat) (n : Nat)
    (hq : InInterval (RealCompute.ofRat q) (C.real.compute n))
    (hu : InInterval (EulerReal.negativeSample q t).real.preferred ((evaluate C t).real.compute n)) :
    InInterval (scale q (EulerReal.negativeSample q t)).real.preferred
      ((Value.mul C (evaluate C t)).real.compute n) := by
  have H := RealIntervalImage.mul (x := RealCompute.ofRat q) (y := (EulerReal.negativeSample q t).real.preferred)
    (RealCompute.ofRat_valid q) (EulerReal.negativeSample q t).real.valid hq hu
  apply inInterval_congr (Value.mul (Value.rational q) (EulerReal.negativeSample q t)).real.valid
    (scale q (EulerReal.negativeSample q t)).real.valid _ H
  apply arithmetic_identity; intro s; simp only [Value.mul,Value.rational,scale]

private theorem remainder_image (C : Value) (q u v : Rat) (n : Nat)
    (hq : (C.real.compute n).lo≤q ∧ q≤(C.real.compute n).hi) :
    InInterval (EulerReal.parameterRemainder q u v).real.preferred ((remainder C u v).real.compute n) := by
  have hq' : InInterval (RealCompute.ofRat q) (C.real.compute n) := ⟨fun _ _ => hq.1,fun _ _ => hq.2⟩
  have U := rational_image C q u n hq
  have V := rational_image C q v n hq
  have P := product_image C q u n hq' U
  exact interval_sub (interval_sub V U) (interval_scale (RealIntervalImage.neg P) (v-u))

private theorem majorant_image (C : Value) (q u v : Rat) (n : Nat)
    (hq : (C.real.compute n).lo≤q ∧ q≤(C.real.compute n).hi) :
    InInterval (scale (q*q*(v-u)*(v-u)) (EulerReal.negativeSample q u)).real.preferred
      ((majorant C u v).real.compute n) := by
  have hq' : InInterval (RealCompute.ofRat q) (C.real.compute n) := ⟨fun _ _ => hq.1,fun _ _ => hq.2⟩
  have U := rational_image C q u n hq
  have Q := RealIntervalImage.mul (x := RealCompute.ofRat q) (y := RealCompute.ofRat q)
    (RealCompute.ofRat_valid q) (RealCompute.ofRat_valid q) hq' hq'
  have P := RealIntervalImage.mul (Value.mul (Value.rational q) (Value.rational q)).real.valid
    (EulerReal.negativeSample q u).real.valid Q U
  have H := interval_scale P ((v-u)*(v-u))
  apply inInterval_congr (scale ((v-u)*(v-u))
    (Value.mul (Value.mul (Value.rational q) (Value.rational q)) (EulerReal.negativeSample q u))).real.valid
    (scale (q*q*(v-u)*(v-u)) (EulerReal.negativeSample q u)).real.valid _ H
  apply arithmetic_identity; intro s; simp only [scale,Value.mul,Value.rational]; grind only

private theorem le_of_sub_nonpositive (X Y : Value) (H : LE (sub X Y) (Value.rational 0)) : LE X Y := by
  have A := le_add H (RealCompute.le_refl Y.real.preferred Y.real.valid)
  apply le_congr A
  · apply arithmetic_identity (Value.add (sub X Y) Y) X
    intro s; simp only [Value.add,sub]; grind only
  · apply arithmetic_identity (Value.add (Value.rational 0) Y) Y
    intro s; simp only [Value.add,Value.rational]; grind only

/-- The damping factor is retained in the actual represented-coefficient
first-order error. Joint images prevent independent coefficient choices. -/
theorem refined (C : Value) (B : Rat) (h0 : LE (Value.rational 0) C) (hb : Small C B)
    (u v : Rat) (huv : u<v) :
    LE (Value.rational 0) (remainder C u v) ∧ LE (remainder C u v) (majorant C u v) := by
  have point (n : Nat) : ∃ q,0≤q ∧ q≤B ∧ (C.real.compute n).lo≤q ∧ q≤(C.real.compute n).hi :=
    RealIntervalImage.common_point C.real.valid (I := {lo := 0,hi := B}) ⟨h0,hb.2⟩ n
  have lower : LE (Value.rational 0) (remainder C u v) := by
    intro i j
    obtain ⟨q,hq0,_,hq,hq'⟩ := point j
    have H := (EulerReal.negative_parameter_remainder q u v hq0 huv).1
    have cov := remainder_image C q u v j ⟨hq,hq'⟩
    exact RealCompute.le_trans (EulerReal.parameterRemainder q u v).real.valid H cov.2 0 0
  have upper : LE (sub (remainder C u v) (majorant C u v)) (Value.rational 0) := by
    intro i j
    obtain ⟨q,hq0,_,hq,hq'⟩ := point i
    let R := EulerReal.parameterRemainder q u v
    let M := scale (q*q*(v-u)*(v-u)) (EulerReal.negativeSample q u)
    have H := (EulerReal.negative_parameter_remainder q u v hq0 huv).2
    have A := RealCompute.le_sub_le_sub H (RealCompute.le_refl M.real.preferred M.real.valid)
    have A' : LE (sub R M) (Value.rational 0) := by
      apply le_congr (x := sub R M) (y := sub M M) A
      · exact RealCompute.equiv_refl _ (sub R M).real.valid
      · apply arithmetic_identity; intro s; simp only [sub,Value.rational]; grind only
    have cov := interval_sub (remainder_image C q u v i ⟨hq,hq'⟩) (majorant_image C q u v i ⟨hq,hq'⟩)
    exact RealCompute.le_trans (sub R M).real.valid cov.1 A' 0 0
  exact ⟨lower,le_of_sub_nonpositive _ _ upper⟩

theorem bounded (C : Value) (h0 : LE (Value.rational 0) C) (t : Rat) (ht : 0≤t) :
    Small (evaluate C t) 1 := by
  have H := le_scale h0 ht
  have H' : LE (Value.rational 0) (scale t C) := by
    apply le_congr H
    · apply arithmetic_identity; intro s; simp only [scale,Value.rational,Rat.mul_zero]
    · exact RealCompute.equiv_refl _ (scale t C).real.valid
  have harg : (argument C t).real.preferred.Le (RealCompute.ofRat 0) := by
    intro i j
    have A := H' 0 i
    change 0≤((scale t C).real.compute i).hi at A
    change -((scale t C).real.compute i).hi≤0
    grind only
  exact EulerReal.negative_small (argument C t).real.valid harg

private theorem firstOrder (C : Value) (B : Rat) (hB : 0≤B)
    (h0 : LE (Value.rational 0) C) (hb : Small C B) (T : Rat) :
    FTCRealOrder.FirstOrder (evaluate C) (derivative C) 0 T (B*B) 1 := by
  intro u v hu huv _ _
  have H := refined C B h0 hb u v huv
  have hs := ((hb.mul hb).mul (bounded C h0 u hu)).scale_nonnegative
    (Rat.mul_nonneg (show 0≤v-u by grind only) (show 0≤v-u by grind only))
  have he : ((v-u)*(v-u))*((B*B)*1)=(B*B)*(v-u)*(v-u) := by grind only
  rw [he] at hs
  have hm : 0≤(B*B)*(v-u)*(v-u) := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg hB hB) (by grind only)) (by grind only)
  constructor
  · exact RealCompute.le_trans (y := RealCompute.ofRat 0) (RealCompute.ofRat_valid 0)
      (fun _ _ => by change -((B*B)*(v-u)*(v-u))≤0; grind only) H.1
  · exact RealCompute.le_trans (majorant C u v).real.valid H.2 hs.2

/-- A checked FTC step for negative Euler rate with arbitrary represented
coefficient, throughout every nonnegative compact time interval. -/
def step (C : Value) (B : Rat) (hB : 0≤B)
    (h0 : LE (Value.rational 0) C) (hb : Small C B) (T : Rat) :
    Step (evaluate C) (derivative C) 0 T where
  error := B*B
  error_nonnegative := Rat.mul_nonneg hB hB
  radius := ⟨1,by decide +kernel⟩
  firstOrder := firstOrder C B hB h0 hb T
  variation := B*B
  variation_nonnegative := Rat.mul_nonneg hB hB
  lipschitz := by
    have df : ∀ t,0≤t → t≤T → Small (derivative C t) B := by
      intro t ht _
      simpa only [derivative,Rat.mul_one] using (hb.mul (bounded C h0 t ht)).neg
    have lip := lipschitz_of_firstOrder (firstOrder C B hB h0 hb T) (Rat.mul_nonneg hB hB) (by decide +kernel) df
    intro u v hu huv hv
    have H := (hb.mul (lip u v hu huv hv)).neg
    have he : B*(B*(v-u))=(B*B)*(v-u) := by grind only
    rw [he] at H
    apply H.congr
    apply arithmetic_identity; intro s; simp only [derivative,Value.neg,Value.mul,sub]; grind only

end ComputableAnalysis.EulerNegativeRate


