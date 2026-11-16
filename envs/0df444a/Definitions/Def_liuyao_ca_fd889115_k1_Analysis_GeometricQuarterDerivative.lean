-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricQuarterDerivative
-- name    : liuyao_ca_fd889115_k1_Analysis_GeometricQuarterDerivative
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:37:56.228071+00:00
-- url     : https://prove2.me/theorems/2421a25e-1ac9-49e9-8949-5df68d67b4bd
-- title:
--   Computable analysis · GeometricQuarterDerivative · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/GeometricQuarterDerivative.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricQuarterEstimates

set_option autoImplicit true

/-! Real first-order remainders for the geometric angle inverse. No power
series, complex number, or trigonometric derivative is used as a premise. -/
namespace ComputableAnalysis.GeometricTrig
open ArctanSecantFoundation ArctanInverseConstruction ArctanGeometry GeometricTrigChart
open RationalCircleDifferences ComputableCoefficient
set_option maxHeartbeats 3000000

theorem chartPoint_strict {x y : Rat} (hx : 0≤x ∧ x≤1/2)
    (hy : 0≤y ∧ y≤1/2) (hxy : x<y) (n : Nat) (hw : width n≤(y-x)/64) :
    chartPoint x n<chartPoint y n := by
  let c := (unitArea.compute (precision n)).midpoint
  have hc := QInterval.midpoint_mem (RealCompute.interval_order_of_valid _ unitArea_valid (precision n))
  have cb := unitArea_bounds n
  have cmin : 1/4≤c := Rat.le_trans cb.1 hc.1
  have ex := areaPoint_target hx n c hc
  have ey := areaPoint_target hy n c hc
  have eLo := neg_qabs_le_self (areaPoint y n-2*y*c)
  have eHi := self_le_qabs (areaPoint x n-2*x*c)
  have hm := Rat.mul_le_mul_of_nonneg_left cmin (show 0≤2*(y-x) by grind only)
  by_cases ho : chartPoint x n<chartPoint y n
  · exact ho
  have hvu : chartPoint y n≤chartPoint x n := by grind only
  have gx := slope_geometry x n
  have gy := slope_geometry y n
  have dx : 0≤chartPoint x n ∧ chartPoint x n≤1 := ⟨gx.1,Rat.le_trans gx.2.1 gx.2.2.1⟩
  have dy : 0≤chartPoint y n ∧ chartPoint y n≤1 := ⟨gy.1,Rat.le_trans gy.2.1 gy.2.2.1⟩
  have h := (increment_bounds dy.1 hvu (precision n)).1
  have hk := (kernel_bounds dx).1
  have hp := Rat.mul_nonneg (show 0≤chartPoint x n-chartPoint y n by grind only)
    (show 0≤integralKernel (chartPoint x n) by grind only)
  have wx := source_width (chartPoint x n) dx n
  have wy := source_width (chartPoint y n) dy n
  have ax := areaPoint_mem x n
  have ay := areaPoint_mem y n
  unfold QInterval.width at wx wy
  grind only

theorem area_sample_remainder (cosine : Bool) {u v : Rat}
    (hu : 0≤u) (huv : u≤v) (hv : v≤1) (n : Nat) (a b : Rat)
    (ha : ((value u).compute (precision n)).lo≤a ∧ a≤((value u).compute (precision n)).hi)
    (hb : ((value v).compute (precision n)).lo≤b ∧ b≤((value v).compute (precision n)).hi) :
    qabs (coordinate cosine v-coordinate cosine u-2*tangent cosine u*(b-a))≤
      16*(v-u)*(v-u)+width n/32 := by
  let Q := RealCompute.ofRat (coordinate cosine v-coordinate cosine u)-
    RealCompute.scaleRat (2*tangent cosine u) (value v-value u)
  have h := area_remainder cosine hu huv hv
  have hlo := h.1 0 (precision n)
  have hhi := h.2 (precision n) 0
  change -16*(v-u)*(v-u)≤(Q.compute (precision n)).hi at hlo
  change (Q.compute (precision n)).lo≤16*(v-u)*(v-u) at hhi
  have hdiff : ((value v-value u).compute (precision n)).lo≤b-a ∧
      b-a≤((value v-value u).compute (precision n)).hi := by
    change ((value v).compute (precision n)).lo-((value u).compute (precision n)).hi≤b-a ∧
      b-a≤((value v).compute (precision n)).hi-((value u).compute (precision n)).lo
    constructor <;> grind only
  have hscale := QInterval.scaleRat_mem (r := 2*tangent cosine u) hdiff
  have hmem : (Q.compute (precision n)).lo≤coordinate cosine v-coordinate cosine u-2*tangent cosine u*(b-a) ∧
      coordinate cosine v-coordinate cosine u-2*tangent cosine u*(b-a)≤(Q.compute (precision n)).hi := by
    change (coordinate cosine v-coordinate cosine u)-
      (QInterval.scaleRat (2*tangent cosine u) ((value v-value u).compute (precision n))).hi≤_ ∧
      _≤(coordinate cosine v-coordinate cosine u)-
      (QInterval.scaleRat (2*tangent cosine u) ((value v-value u).compute (precision n))).lo
    constructor <;> grind only
  have hwq : (Q.compute (precision n)).width=
      qabs (2*tangent cosine u)*(((value v).compute (precision n)).width+((value u).compute (precision n)).width) := by
    change (QInterval.sub
      ({lo:=coordinate cosine v-coordinate cosine u,hi:=coordinate cosine v-coordinate cosine u} : QInterval)
      (QInterval.scaleRat (2*tangent cosine u) (QInterval.sub ((value v).compute (precision n)) ((value u).compute (precision n))))).width=_
    rw [QInterval.sub_width,QInterval.scaleRat_width,QInterval.sub_width]
    change (coordinate cosine v-coordinate cosine u)-(coordinate cosine v-coordinate cosine u)+_= _
    grind only
  have wu := source_width u ⟨hu,Rat.le_trans huv hv⟩ n
  have wv := source_width v ⟨Rat.le_trans hu huv,hv⟩ n
  have tu := tangent_abs cosine ⟨hu,Rat.le_trans huv hv⟩
  have ht : qabs (2*tangent cosine u)≤2 := by
    rw [qabs_mul,show qabs (2:Rat)=2 by decide +kernel]
    have hm := Rat.mul_le_mul_of_nonneg_left tu (by decide +kernel : (0:Rat)≤2)
    simpa only [Rat.mul_one] using hm
  have hm := Rat.mul_le_mul_of_nonneg_right ht
    (show 0≤((value v).compute (precision n)).width+((value u).compute (precision n)).width from
      Rat.add_nonneg ((value_valid ⟨Rat.le_trans hu huv,hv⟩).1 _) ((value_valid ⟨hu,Rat.le_trans huv hv⟩).1 _))
  have hw : (Q.compute (precision n)).width≤width n/32 := by rw [hwq]; grind only
  unfold QInterval.width at hw
  apply qabs_le_of_neg_le_le <;> grind only

theorem pi_sample_area (n : Nat) (p : Rat)
    (hp : (pi.compute n).lo≤p ∧ p≤(pi.compute n).hi) :
    (unitArea.compute (precision n)).lo≤p/4 ∧ p/4≤(unitArea.compute (precision n)).hi := by
  change (RealCompute.scaleRatCompute 4 (RealCompute.schedule areaSchedule unitArea) n).lo≤p ∧
    p≤(RealCompute.scaleRatCompute 4 (RealCompute.schedule areaSchedule unitArea) n).hi at hp
  simp only [RealCompute.scaleRatCompute,show (0:Rat)≤4 by decide +kernel,↓reduceIte] at hp
  change 4*(unitArea.compute (precision n)).lo≤p ∧ p≤4*(unitArea.compute (precision n)).hi at hp
  constructor <;> grind only

theorem quarter_tangent_sample_error (cosine : Bool) (x : Rat) (n : Nat) (t : Rat)
    (ht : ((quarter (!cosine) x).compute n).lo≤t ∧ t≤((quarter (!cosine) x).compute n).hi) :
    qabs ((if cosine then -t else t)-tangent cosine (chartPoint x n))≤4*width n := by
  cases cosine
  · simpa only [tangent,Bool.false_eq_true,Bool.not_false,↓reduceIte,coordinate] using
      quarter_sample_error true x n ht
  · have h := quarter_sample_error false x n ht
    change qabs (t-RationalCircleDifferences.pointIm (chartPoint x n))≤4*width n at h
    change qabs (-t-(-RationalCircleDifferences.pointIm (chartPoint x n)))≤4*width n
    rw [show -t-(-RationalCircleDifferences.pointIm (chartPoint x n))=
      -(t-RationalCircleDifferences.pointIm (chartPoint x n)) by grind only,qabs_neg]
    exact h

/-- Finite error for the literal geometric sampler at two rational angles.
The numerical pi sample and all circle samples retain their independent boxes. -/
theorem quarter_firstOrder_sample (cosine : Bool) {x y : Rat}
    (hx : 0≤x ∧ x≤1/2) (hy : 0≤y ∧ y≤1/2) (hxy : x<y)
    (n : Nat) (hw : width n≤(y-x)/64) (a b t p : Rat)
    (ha : ((quarter cosine x).compute n).lo≤a ∧ a≤((quarter cosine x).compute n).hi)
    (hb : ((quarter cosine y).compute n).lo≤b ∧ b≤((quarter cosine y).compute n).hi)
    (ht : ((quarter (!cosine) x).compute n).lo≤t ∧ t≤((quarter (!cosine) x).compute n).hi)
    (hp : (pi.compute n).lo≤p ∧ p≤(pi.compute n).hi) :
    qabs (b-a-(y-x)*p*(if cosine then -t else t))≤1600*(y-x)*(y-x)+40*width n := by
  let c := p/4
  have hc := pi_sample_area n p hp
  have cp := unitArea_bounds n
  have c0 : 0≤c := by dsimp [c]; grind only
  have c2 : c≤2 := by dsimp [c]; grind only
  have p8 : qabs p≤8 := by apply qabs_le_of_neg_le_le <;> dsimp [c] at c0 c2 <;> grind only
  have pc : p=4*c := by dsimp [c]; grind only
  have gx := slope_geometry x n
  have gy := slope_geometry y n
  have dx : 0≤chartPoint x n ∧ chartPoint x n≤1 := ⟨gx.1,Rat.le_trans gx.2.1 gx.2.2.1⟩
  have dy : 0≤chartPoint y n ∧ chartPoint y n≤1 := ⟨gy.1,Rat.le_trans gy.2.1 gy.2.2.1⟩
  have huv := chartPoint_strict hx hy hxy n hw
  have hdelta := chartPoint_difference hx hy (Rat.le_of_lt hxy) n
  rw [qabs_eq_self_of_nonneg (show 0≤chartPoint y n-chartPoint x n by grind only)] at hdelta
  have hd10 : chartPoint y n-chartPoint x n≤10*(y-x) := by grind only
  have hsq := rat_mul_le_mul_of_nonneg (show 0≤chartPoint y n-chartPoint x n by grind only) hd10
    (show 0≤chartPoint y n-chartPoint x n by grind only) hd10
  have geo := area_sample_remainder cosine dx.1 (Rat.le_of_lt huv) dy.2 n
    (areaPoint x n) (areaPoint y n) (areaPoint_mem x n) (areaPoint_mem y n)
  have eX := areaPoint_target hx n c hc
  have eY := areaPoint_target hy n c hc
  have aX := quarter_sample_error cosine x n ha
  have aY := quarter_sample_error cosine y n hb
  have eT := quarter_tangent_sample_error cosine x n t ht
  have t1 := tangent_abs cosine dx
  have wp : 0≤width n := Rat.pow_nonneg (by decide +kernel)
  have hE : qabs ((b-a)-(coordinate cosine (chartPoint y n)-coordinate cosine (chartPoint x n)))≤8*width n := by
    have h := qabs_add_le (b-coordinate cosine (chartPoint y n)) (-(a-coordinate cosine (chartPoint x n)))
    rw [qabs_neg] at h
    have he : (b-coordinate cosine (chartPoint y n))+ -(a-coordinate cosine (chartPoint x n))=
        (b-a)-(coordinate cosine (chartPoint y n)-coordinate cosine (chartPoint x n)) := by grind only
    rw [he] at h
    grind only
  have hA : qabs ((areaPoint y n-areaPoint x n)-2*(y-x)*c)≤4*width n := by
    have h := qabs_add_le (areaPoint y n-2*y*c) (-(areaPoint x n-2*x*c))
    rw [qabs_neg] at h
    have he : (areaPoint y n-2*y*c)+ -(areaPoint x n-2*x*c)=
        (areaPoint y n-areaPoint x n)-2*(y-x)*c := by grind only
    rw [he] at h
    grind only
  have tm : qabs (2*tangent cosine (chartPoint x n))≤2 := by
    rw [qabs_mul,show qabs (2:Rat)=2 by decide +kernel]
    have h := Rat.mul_le_mul_of_nonneg_left t1 (by decide +kernel : (0:Rat)≤2)
    simpa only [Rat.mul_one] using h
  have hT : qabs (2*tangent cosine (chartPoint x n)*
      ((areaPoint y n-areaPoint x n)-2*(y-x)*c))≤8*width n := by
    rw [qabs_mul]
    have h := rat_mul_le_mul_of_nonneg (qabs_nonneg _) tm (qabs_nonneg _) hA
    grind only
  have hhp : qabs ((y-x)*p)≤4 := by
    rw [qabs_mul,qabs_eq_self_of_nonneg (show 0≤y-x by grind only)]
    have h := Rat.mul_le_mul_of_nonneg_left p8 (show 0≤y-x by grind only)
    grind only
  have hD : qabs ((y-x)*p*(tangent cosine (chartPoint x n)-(if cosine then -t else t)))≤16*width n := by
    rw [qabs_mul]
    have et' : qabs (tangent cosine (chartPoint x n)-(if cosine then -t else t))≤4*width n := by
      rw [show tangent cosine (chartPoint x n)-(if cosine then -t else t)=
        -((if cosine then -t else t)-tangent cosine (chartPoint x n)) by grind only,qabs_neg]
      exact eT
    have h := rat_mul_le_mul_of_nonneg (qabs_nonneg _) hhp (qabs_nonneg _) et'
    grind only
  let R := coordinate cosine (chartPoint y n)-coordinate cosine (chartPoint x n)-
    2*tangent cosine (chartPoint x n)*(areaPoint y n-areaPoint x n)
  let E := (b-a)-(coordinate cosine (chartPoint y n)-coordinate cosine (chartPoint x n))
  let A := 2*tangent cosine (chartPoint x n)*((areaPoint y n-areaPoint x n)-2*(y-x)*c)
  let D := (y-x)*p*(tangent cosine (chartPoint x n)-(if cosine then -t else t))
  have h1 := qabs_add_le_three R E A
  have h2 := qabs_add_le (R+E+A) D
  have he : R+E+A+D=b-a-(y-x)*p*(if cosine then -t else t) := by dsimp [R,E,A,D]; rw [pc]; grind only
  rw [he] at h2
  change qabs R≤16*(chartPoint y n-chartPoint x n)*(chartPoint y n-chartPoint x n)+width n/32 at geo
  change qabs E≤8*width n at hE
  change qabs A≤8*width n at hT
  change qabs D≤16*width n at hD
  grind only

def quarterRemainder (cosine : Bool) (x y : Rat) : Value :=
  RealApproximationOrder.sub
    (RealApproximationOrder.sub (quarterValue cosine y) (quarterValue cosine x))
    (RealApproximationOrder.scale (y-x) (slopeValue cosine x))

/-- Exact real first-order law for the geometric normalized quarter-circle.
Its derivative is pi times the other coordinate, with the cosine sign reversed. -/
theorem quarter_firstOrder (cosine : Bool) {x y : Rat}
    (hx : 0≤x ∧ x≤1/2) (hy : 0≤y ∧ y≤1/2) (hxy : x<y) :
    RealApproximationOrder.Small (quarterRemainder cosine x y) (1600*(y-x)*(y-x)) := by
  have he : 0<(y-x)/64 := by grind only
  obtain ⟨N,hN⟩ := width_shrinks ⟨_,he⟩
  apply RealApproximationOrder.small_of_approximate_samples _ _ (fun n => 40*width n)
    (scaled_width_shrinks (by decide +kernel)) N
  intro n hn s hs
  have hnum := quarter_firstOrder_sample cosine hx hy hxy n (hN n hn)
    ((quarterValue cosine x).sample s) ((quarterValue cosine y).sample s)
    ((quarterValue (!cosine) x).sample s) (piValue.sample s)
    (hs (quarterValue cosine x).real) (hs (quarterValue cosine y).real)
    (hs (quarterValue (!cosine) x).real) (hs piValue.real)
  cases cosine <;>
    simpa only [quarterRemainder,RealApproximationOrder.sub,RealApproximationOrder.scale,
      slopeValue,Value.mul,Value.neg,Bool.false_eq_true,Bool.not_false,Bool.not_true,
      ↓reduceIte,Rat.mul_assoc] using hnum

end ComputableAnalysis.GeometricTrig


