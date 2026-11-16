-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricDerivative
-- name    : liuyao_ca_fd889115_k1_Analysis_GeometricDerivative
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:43:07.414964+00:00
-- url     : https://prove2.me/theorems/b7a8440a-8d0f-4623-bc31-0caf8311d319
-- title:
--   Computable analysis · GeometricDerivative · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/GeometricDerivative.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricPeriodic
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricQuarterDerivative
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueBounds
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzRealCalculus

set_option autoImplicit true

/-! The geometric normalized sine/cosine derivative cycle on the full real
domain. Quarter joins are handled by their actual finite real remainders. -/
namespace ComputableAnalysis.GeometricTrig
open ComputableCoefficient RealApproximationOrder RawLimit
set_option maxHeartbeats 3000000

def turnValue (j : Int) (cosine : Bool) (q : Rat) : Value :=
  if j%4=0 then quarterValue cosine q
  else if j%4=1 then (if cosine then Value.neg (quarterValue false q) else quarterValue true q)
  else if j%4=2 then Value.neg (quarterValue cosine q)
  else (if cosine then quarterValue false q else Value.neg (quarterValue true q))

theorem turnValue_raw (j : Int) (cosine : Bool) (q : Rat) :
    (turnValue j cosine q).real.preferred=turn j cosine q := by
  by_cases h0 : j%4=0
  · simp only [turnValue,turn,if_pos h0]; rfl
  · by_cases h1 : j%4=1
    · cases cosine <;> simp only [turnValue,turn,if_neg h0,if_pos h1,Bool.false_eq_true,↓reduceIte] <;> rfl
    · by_cases h2 : j%4=2
      · simp only [turnValue,turn,if_neg h0,if_neg h1,if_pos h2]; rfl
      · cases cosine <;> simp only [turnValue,turn,if_neg h0,if_neg h1,if_neg h2,Bool.false_eq_true,↓reduceIte] <;> rfl

def valueFor (cosine : Bool) (q : Rat) : Value := turnValue (quarterIndex q) cosine (quarterArgument q/2)
theorem valueFor_raw (cosine : Bool) (q : Rat) : (valueFor cosine q).real.preferred=sample cosine q :=
  turnValue_raw _ _ _

def pairSlope (cosine : Bool) (S C : Value) : Value := Value.mul piValue (if cosine then Value.neg S else C)
def derivativeValue (cosine : Bool) (q : Rat) : Value := pairSlope cosine (valueFor false q) (valueFor true q)
def turnSlopeValue (j : Int) (cosine : Bool) (q : Rat) : Value :=
  pairSlope cosine (turnValue j false q) (turnValue j true q)

def remainderValue (cosine : Bool) (u v : Rat) : Value :=
  sub (sub (valueFor cosine v) (valueFor cosine u)) (scale (v-u) (derivativeValue cosine u))
def turnRemainder (j : Int) (cosine : Bool) (u v : Rat) : Value :=
  sub (sub (turnValue j cosine v) (turnValue j cosine u)) (scale (v-u) (turnSlopeValue j cosine u))

theorem turn_firstOrder (j : Int) (cosine : Bool) {u v : Rat}
    (hu : 0≤u ∧ u≤1/2) (hv : 0≤v ∧ v≤1/2) (huv : u<v) :
    Small (turnRemainder j cosine u v) (1600*(v-u)*(v-u)) := by
  have hj : j%4=0 ∨ j%4=1 ∨ j%4=2 ∨ j%4=3 := by omega
  rcases hj with h | h | h | h
  · apply (quarter_firstOrder cosine hu hv huv).congr
    apply arithmetic_identity
    intro s
    cases cosine <;> simp [turnRemainder,turnSlopeValue,pairSlope,turnValue,quarterRemainder,
      slopeValue,sub,scale,Value.mul,Value.neg,h]
  · cases cosine
    · apply (quarter_firstOrder true hu hv huv).congr
      apply arithmetic_identity
      intro s
      simp [turnRemainder,turnSlopeValue,pairSlope,turnValue,quarterRemainder,
        slopeValue,sub,scale,Value.mul,Value.neg,h]
    · apply (quarter_firstOrder false hu hv huv).neg.congr
      apply arithmetic_identity
      intro s
      simp [turnRemainder,turnSlopeValue,pairSlope,turnValue,quarterRemainder,
        slopeValue,sub,scale,Value.mul,Value.neg,h]
      grind only
  · apply (quarter_firstOrder cosine hu hv huv).neg.congr
    apply arithmetic_identity
    intro s
    cases cosine <;> simp [turnRemainder,turnSlopeValue,pairSlope,turnValue,quarterRemainder,
      slopeValue,sub,scale,Value.mul,Value.neg,h] <;> grind only
  · cases cosine
    · apply (quarter_firstOrder true hu hv huv).neg.congr
      apply arithmetic_identity
      intro s
      simp [turnRemainder,turnSlopeValue,pairSlope,turnValue,quarterRemainder,
        slopeValue,sub,scale,Value.mul,Value.neg,h]
      grind only
    · apply (quarter_firstOrder false hu hv huv).congr
      apply arithmetic_identity
      intro s
      simp [turnRemainder,turnSlopeValue,pairSlope,turnValue,quarterRemainder,
        slopeValue,sub,scale,Value.mul,Value.neg,h]

theorem pi_small : Small piValue 8 := by
  apply small_of_samples piValue 8 0
  intro n _ s hs
  have h := pi_sample_area n (piValue.sample s) (hs piValue.real)
  have hb := unitArea_bounds n
  apply qabs_le_of_neg_le_le <;> grind only

theorem pairSlope_congr (cosine : Bool) (S C T D : Value)
    (hS : S.real.preferred.Equiv T.real.preferred) (hC : C.real.preferred.Equiv D.real.preferred) :
    (pairSlope cosine S C).real.preferred.Equiv (pairSlope cosine T D).real.preferred := by
  cases cosine
  · exact RealCompute.mul_equiv pi_valid pi_valid C.real.valid D.real.valid
      (RealCompute.equiv_refl pi pi_valid) hC
  · exact RealCompute.mul_equiv pi_valid pi_valid (RealCompute.neg_valid S.real.valid) (RealCompute.neg_valid T.real.valid)
      (RealCompute.equiv_refl pi pi_valid) (RealCompute.neg_equiv hS)

theorem remainder_congr (A B C D U V : Value) (h : Rat)
    (hA : A.real.preferred.Equiv C.real.preferred)
    (hB : B.real.preferred.Equiv D.real.preferred)
    (hU : U.real.preferred.Equiv V.real.preferred) :
    (sub (sub B A) (scale h U)).real.preferred.Equiv (sub (sub D C) (scale h V)).real.preferred :=
  RealCompute.sub_equiv (RealCompute.sub_valid B.real.valid A.real.valid) (RealCompute.sub_valid D.real.valid C.real.valid)
    (RealCompute.scaleRat_valid U.real.valid) (RealCompute.scaleRat_valid V.real.valid)
    (RealCompute.sub_equiv B.real.valid D.real.valid A.real.valid C.real.valid hB hA) (RealCompute.scaleRat_equiv hU)

theorem piece_firstOrder (j : Int) (cosine : Bool) {u v : Rat}
    (hu : (j:Rat)/2≤u) (huv : u<v) (hv : v≤((j+1:Int):Rat)/2) :
    Small (remainderValue cosine u v) (1600*(v-u)*(v-u)) := by
  have hJ : ((j+1:Int):Rat)/2=(j:Rat)/2+1/2 := by rw [Rat.intCast_add]; grind only
  let a := u-(j:Rat)/2
  let b := v-(j:Rat)/2
  have ha : 0≤a ∧ a≤1/2 := by dsimp [a]; constructor <;> grind only
  have hb : 0≤b ∧ b≤1/2 := by dsimp [b]; constructor <;> grind only
  have hab : a<b := by dsimp [a,b]; grind only
  have eu (c : Bool) : (valueFor c u).real.preferred.Equiv (turnValue j c a).real.preferred := by
    rw [valueFor_raw,turnValue_raw]
    exact sample_on_closed_quarter j c hu (Rat.le_trans (Rat.le_of_lt huv) hv)
  have ev (c : Bool) : (valueFor c v).real.preferred.Equiv (turnValue j c b).real.preferred := by
    rw [valueFor_raw,turnValue_raw]
    exact sample_on_closed_quarter j c (Rat.le_trans hu (Rat.le_of_lt huv)) hv
  have ed := pairSlope_congr cosine (valueFor false u) (valueFor true u)
    (turnValue j false a) (turnValue j true a) (eu false) (eu true)
  have he := remainder_congr (valueFor cosine u) (valueFor cosine v)
    (turnValue j cosine a) (turnValue j cosine b) (derivativeValue cosine u) (turnSlopeValue j cosine a)
    (v-u) (eu cosine) (ev cosine) ed
  have hdelta : b-a=v-u := by dsimp [a,b]; grind only
  have hs := turn_firstOrder j cosine ha hb hab
  have he' : (turnRemainder j cosine a b).real.preferred.Equiv (remainderValue cosine u v).real.preferred := by
    unfold turnRemainder
    rw [hdelta]
    exact RealCompute.equiv_symm he
  rw [hdelta] at hs
  exact hs.congr he'

theorem derivative_value_lipschitz (cosine : Bool) {u v : Rat} (huv : u≤v) :
    Small (sub (derivativeValue cosine v) (derivativeValue cosine u)) (256*(v-u)) := by
  let E := sub (valueFor (!cosine) v) (valueFor (!cosine) u)
  have hE : Small E (32*(v-u)) := by
    change InInterval ((valueFor (!cosine) v).real.preferred-(valueFor (!cosine) u).real.preferred)
      {lo := -(32*(v-u)),hi := 32*(v-u)}
    rw [valueFor_raw,valueFor_raw]
    simpa only [Rat.neg_mul] using sample_ordered_lipschitz (!cosine) huv
  let D := if cosine then Value.neg E else E
  have hD : Small D (32*(v-u)) := by
    cases cosine
    · exact hE
    · exact hE.neg
  have hp := pi_small.mul hD
  have he : (8:Rat)*(32*(v-u))=256*(v-u) := by grind only
  rw [he] at hp
  apply hp.congr
  apply arithmetic_identity
  intro s
  cases cosine <;> simp only [D,E,derivativeValue,pairSlope,sub,Value.mul,Value.neg,
    Bool.false_eq_true,Bool.not_false,Bool.not_true,↓reduceIte] <;> grind only

theorem full_firstOrder_small (cosine : Bool) {u v : Rat}
    (huv : u<v) (hstep : v-u≤1/4) :
    Small (remainderValue cosine u v) (1600*(v-u)*(v-u)) := by
  let j := quarterIndex u
  let k := quarterIndex v
  have jL := Rat.floor_le (2*u)
  have jR := Rat.lt_floor_add_one (2*u)
  have kL := Rat.floor_le (2*v)
  have kR := Rat.lt_floor_add_one (2*v)
  change (j:Rat)≤2*u at jL
  change (k:Rat)≤2*v at kL
  change 2*u<((j+1:Int):Rat) at jR
  change 2*v<((k+1:Int):Rat) at kR
  have hjk : j≤k := Rat.floor_monotone (by grind only : 2*u≤2*v)
  have huL : (j:Rat)/2≤u := by grind only
  have huR : u<((j+1:Int):Rat)/2 := by grind only
  have hvL : (k:Rat)/2≤v := by grind only
  have hvR : v≤((k+1:Int):Rat)/2 := by grind only
  by_cases he : j=k
  · rw [←he] at hvR
    exact piece_firstOrder j cosine huL huv hvR
  have ha : k=j+1 := by
    by_cases ha : k=j+1
    · exact ha
    have hi : j+2≤k := by omega
    have hRat : ((j+2:Int):Rat)≤(k:Rat) := by exact_mod_cast hi
    rw [Rat.intCast_add] at hRat jR
    grind only
  rw [ha] at hvL hvR
  let c : Rat := ((j+1:Int):Rat)/2
  by_cases hc : v=c
  · rw [hc]
    exact piece_firstOrder j cosine huL huR Rat.le_refl
  have hcv : c<v := by change c≤v at hvL; grind only
  have h1 := piece_firstOrder j cosine huL huR (Rat.le_refl : c≤c)
  have h2 := piece_firstOrder (j+1) cosine (Rat.le_refl : c≤c) hcv hvR
  have hd := derivative_value_lipschitz cosine (Rat.le_of_lt huR)
  have hs := hd.scale_nonnegative (show 0≤v-c by grind only)
  have ht := (h1.add h2).add hs
  have hm := Rat.mul_nonneg (show 0≤c-u by grind only) (show 0≤v-c by grind only)
  have hbound : (1600*(c-u)*(c-u)+1600*(v-c)*(v-c))+(v-c)*(256*(c-u))≤
      1600*(v-u)*(v-u) := by grind only
  apply (ht.mono hbound).congr
  apply arithmetic_identity
  intro s
  simp only [Value.add,remainderValue,sub,scale]
  grind only

theorem firstOrder (cosine : Bool) : LipschitzRealExtension.FirstOrder (sample cosine)
    (fun q => (derivativeValue cosine q).real.preferred) 1600 (1/4) := by
  intro u v huv hstep
  have h := full_firstOrder_small cosine huv hstep
  change InInterval ((valueFor cosine v).real.preferred-(valueFor cosine u).real.preferred-
    RealCompute.scaleRat (v-u) (derivativeValue cosine u).real.preferred)
      {lo := -(1600*(v-u)*(v-u)),hi := 1600*(v-u)*(v-u)} at h
  rw [valueFor_raw,valueFor_raw] at h
  simpa only [Rat.neg_mul] using h

theorem derivativeValue_raw (cosine : Bool) (q : Rat) :
    (derivativeValue cosine q).real.raw=
      if cosine then RealCompute.mul pi (-(sample false q)) else RealCompute.mul pi (sample true q) := by
  cases cosine
  · change RealCompute.mul pi (valueFor true q).real.preferred=RealCompute.mul pi (sample true q)
    rw [valueFor_raw]
  · change RealCompute.mul pi (-(valueFor false q).real.preferred)=RealCompute.mul pi (-(sample false q))
    rw [valueFor_raw]

/-- The public geometric sine derivative. Rational sampling is primary;
the point and the cosine value may be arbitrary represented real values. -/
theorem sin_derivative {x : RealCompute} (hx : x.Valid) :
    RealSecantDerivative.HasDerivativeAt (fun _ => True) sin x (RealCompute.mul pi (cosAt x)) := by
  have hC := LipschitzRealExtension.constant_product_continuous cos_valid (L := 32)
    (by decide +kernel) (sample_lipschitz true) (fun n => 4*ArctanInverseConstruction.width n)
    (scaled_width_shrinks (by decide +kernel)) (sample_width true) pi pi_valid hx
  have hD : BracketContinuity.HasContinuousAt (fun _ => True)
      (fun q => (derivativeValue false q).real.preferred) x (RealCompute.mul pi (cosAt x)) := by
    apply BracketContinuity.congr_function hC (fun q _ => (derivativeValue false q).real.valid)
    intro q _
    rw [derivativeValue_raw]
    exact RealCompute.equiv_refl _ (RealCompute.mul_valid pi_valid (cos_valid q))
  exact LipschitzRealExtension.derivative_of_firstOrder (f := sin) (d := fun q => (derivativeValue false q).real.preferred)
    sin_valid (by decide +kernel) (by decide +kernel) (firstOrder false) hD

/-- The companion cosine law, including the negative sign and pi factor. -/
theorem cos_derivative {x : RealCompute} (hx : x.Valid) :
    RealSecantDerivative.HasDerivativeAt (fun _ => True) cos x (-(RealCompute.mul pi (sinAt x))) := by
  have hC := LipschitzRealExtension.constant_product_continuous sin_valid (L := 32)
    (by decide +kernel) (sample_lipschitz false) (fun n => 4*ArctanInverseConstruction.width n)
    (scaled_width_shrinks (by decide +kernel)) (sample_width false) pi pi_valid hx
  have hN := LipschitzRealExtension.continuous_neg hC
  have hD : BracketContinuity.HasContinuousAt (fun _ => True)
      (fun q => (derivativeValue true q).real.preferred) x (-(RealCompute.mul pi (sinAt x))) := by
    apply BracketContinuity.congr_function hN (fun q _ => (derivativeValue true q).real.valid)
    intro q _
    have h := arithmetic_identity (Value.neg (Value.mul piValue (valueFor false q))) (derivativeValue true q) (by
      intro s
      simp only [derivativeValue,pairSlope,Value.mul,Value.neg,↓reduceIte]
      grind only)
    change (-(RealCompute.mul pi (valueFor false q).real.preferred)).Equiv (derivativeValue true q).real.preferred at h
    rw [valueFor_raw] at h
    exact h
  exact LipschitzRealExtension.derivative_of_firstOrder (f := cos) (d := fun q => (derivativeValue true q).real.preferred)
    cos_valid (by decide +kernel) (by decide +kernel) (firstOrder true) hD

end ComputableAnalysis.GeometricTrig


