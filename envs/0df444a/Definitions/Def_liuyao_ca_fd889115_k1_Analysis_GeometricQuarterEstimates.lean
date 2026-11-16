-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricQuarterEstimates
-- name    : liuyao_ca_fd889115_k1_Analysis_GeometricQuarterEstimates
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:34:46.20138+00:00
-- url     : https://prove2.me/theorems/651f8754-f4d4-481d-84eb-54d20b1d07b9
-- title:
--   Computable analysis · GeometricQuarterEstimates · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/GeometricQuarterEstimates.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricSinCos

set_option autoImplicit true

/-! Quantitative real geometry for the actual arctangent-inverse quarter.
The finite estimates retain both inverse-bracket and sector-evaluation errors. -/
namespace ComputableAnalysis.GeometricTrig
open ArctanSecantFoundation ArctanInverseConstruction GeometricTrigChart
open RationalCircleDifferences ComputableCoefficient
open ArctanGeometry
set_option maxHeartbeats 3000000

theorem quarter_compute (cosine : Bool) (x : Rat) (n : Nat) :
    (quarter cosine x).compute n =
      if cosine then {lo:=coordinate true (slope x n).hi,hi:=coordinate true (slope x n).lo}
      else {lo:=coordinate false (slope x n).lo,hi:=coordinate false (slope x n).hi} := by
  cases cosine <;> rfl

theorem quarter_width (cosine : Bool) (x : Rat) (n : Nat) :
    ((quarter cosine x).compute n).width≤4*width n := by
  have hg := slope_geometry x n
  have hs : subintervalOf (slope x n) 0 1 := ⟨hg.1,hg.2.1,hg.2.2.1⟩
  have hw : 0≤width n := Rat.pow_nonneg (by decide +kernel)
  cases cosine
  · have h := (SinPiIntegral.rationalCircleSinInterval_width_le hs).2
    change ((quarter false x).compute n).width≤2*(slope x n).width at h
    rw [hg.2.2.2] at h
    grind only
  · have h := (SinPiIntegral.rationalCircleCosInterval_width_le hs).2
    change ((quarter true x).compute n).width≤4*(slope x n).width at h
    rw [hg.2.2.2] at h
    exact h

theorem quarter_sample_error (cosine : Bool) (x : Rat) (n : Nat) {y : Rat}
    (hy : ((quarter cosine x).compute n).lo≤y ∧ y≤((quarter cosine x).compute n).hi) :
    qabs (y-coordinate cosine (chartPoint x n))≤4*width n := by
  have hv := RealCompute.interval_order_of_valid _ (quarter_valid cosine x) n
  have hc : ((quarter cosine x).compute n).lo≤coordinate cosine (chartPoint x n) ∧
      coordinate cosine (chartPoint x n)≤((quarter cosine x).compute n).hi := by
    cases cosine
    · exact ⟨Rat.le_refl,hv⟩
    · exact ⟨hv,Rat.le_refl⟩
  have h := qabs_sub_le_of_common_bounds hy.1 hy.2 hc.1 hc.2
  exact Rat.le_trans h (quarter_width cosine x n)

theorem slope_target {x : Rat} (hx : 0≤x ∧ x≤1/2) (n : Nat) :
    (value (slope x n).lo).Le (ArctanInverseCircle.quarterTarget (2*x)) ∧
    (ArctanInverseCircle.quarterTarget (2*x)).Le (value (slope x n).hi) := by
  have ht : 0≤2*x ∧ 2*x≤1 := by constructor <;> grind only
  exact bracket_target _ (ArctanInverseCircle.quarterTarget_valid _)
    (ArctanInverseCircle.quarterTarget_width _ ht) (ArctanInverseCircle.quarterTarget_range _ ht) n

def areaPoint (x : Rat) (n : Nat) : Rat :=
  ((value (chartPoint x n)).compute (precision n)).midpoint

theorem areaPoint_mem (x : Rat) (n : Nat) :
    ((value (chartPoint x n)).compute (precision n)).lo≤areaPoint x n ∧
    areaPoint x n≤((value (chartPoint x n)).compute (precision n)).hi := by
  have hg := slope_geometry x n
  exact QInterval.midpoint_mem (RealCompute.interval_order_of_valid _
    (value_valid ⟨hg.1,Rat.le_trans hg.2.1 hg.2.2.1⟩) _)

/-- The inverse's actual rational chart endpoint has the prescribed geometric
angle, up to a uniform shrinking rational error. -/
theorem areaPoint_target {x : Rat} (hx : 0≤x ∧ x≤1/2) (n : Nat) (c : Rat)
    (hc : (unitArea.compute (precision n)).lo≤c ∧ c≤(unitArea.compute (precision n)).hi) :
    qabs (areaPoint x n-2*x*c)≤2*width n := by
  have hg := slope_geometry x n
  have hlD : 0≤(slope x n).lo ∧ (slope x n).lo≤1 := ⟨hg.1,Rat.le_trans hg.2.1 hg.2.2.1⟩
  have hrD : 0≤(slope x n).hi ∧ (slope x n).hi≤1 := ⟨Rat.le_trans hg.1 hg.2.1,hg.2.2.1⟩
  have hb := slope_target hx n
  have hL := hb.1 (precision n) (precision n)
  have hR := hb.2 (precision n) (precision n)
  have hx0 : 0≤2*x := by grind only
  change ((value (slope x n).lo).compute (precision n)).lo≤
    (RealCompute.scaleRatCompute (2*x) unitArea (precision n)).hi at hL
  change (RealCompute.scaleRatCompute (2*x) unitArea (precision n)).lo≤
    ((value (slope x n).hi).compute (precision n)).hi at hR
  simp only [RealCompute.scaleRatCompute,if_pos hx0] at hL hR
  have hwl := source_width (slope x n).lo hlD n
  have hwr := source_width (slope x n).hi hrD n
  have hwc := source_width 1 ⟨by decide +kernel,by decide +kernel⟩ n
  have hi := (increment_bounds hg.1 hg.2.1 (precision n)).2
  have hk := (kernel_bounds hlD).2
  have hm := Rat.mul_le_mul_of_nonneg_left hk (show 0≤(slope x n).hi-(slope x n).lo by grind only)
  have hgap : (slope x n).hi-(slope x n).lo=width n := hg.2.2.2
  have hp := areaPoint_mem x n
  have hcn := (unitArea_valid.1 (precision n))
  have hmul1 := Rat.mul_le_mul_of_nonneg_right (show 2*x≤1 by grind only) hcn
  have hmul2 := Rat.mul_le_mul_of_nonneg_left hwc hx0
  have hcl := Rat.mul_le_mul_of_nonneg_left hc.1 hx0
  have hcu := Rat.mul_le_mul_of_nonneg_left hc.2 hx0
  have hwp : 0≤width n := Rat.pow_nonneg (by decide +kernel)
  unfold QInterval.width at hwl hwr hwc hcn hmul1 hmul2
  change ((value 1).compute (precision n)).lo≤c ∧ c≤((value 1).compute (precision n)).hi at hc
  change ((value (slope x n).lo).compute (precision n)).lo≤areaPoint x n ∧
    areaPoint x n≤((value (slope x n).lo).compute (precision n)).hi at hp
  dsimp only [unitArea] at hL hR hcn hmul1 hcl hcu
  apply qabs_le_of_neg_le_le <;> grind only

theorem coordinate_lipschitz (cosine : Bool) {u v : Rat}
    (hu : 0≤u ∧ u≤1) (hv : 0≤v ∧ v≤1) :
    qabs (coordinate cosine v-coordinate cosine u)≤4*qabs (v-u) := by
  have forward (a b : Rat) (ha : 0≤a) (hab : a≤b) (hb : b≤1) :
      qabs (coordinate cosine b-coordinate cosine a)≤4*(b-a) := by
    have hI : subintervalOf ({lo:=a,hi:=b} : QInterval) 0 1 := ⟨ha,hab,hb⟩
    cases cosine
    · have h := SinPiIntegral.rationalCircleSinInterval_width_le hI
      change 0≤coordinate false b-coordinate false a ∧
        coordinate false b-coordinate false a≤2*(b-a) at h
      rw [qabs_eq_self_of_nonneg h.1]
      grind only
    · have h := SinPiIntegral.rationalCircleCosInterval_width_le hI
      change 0≤coordinate true a-coordinate true b ∧
        coordinate true a-coordinate true b≤4*(b-a) at h
      rw [qabs_eq_neg_of_nonpos (by grind only : coordinate true b-coordinate true a≤0)]
      grind only
  by_cases huv : u≤v
  · rw [qabs_eq_self_of_nonneg (show 0≤v-u by grind only)]
    exact forward u v hu.1 huv hv.2
  · have hvu : v≤u := by grind only
    have h := forward v u hv.1 hvu hu.2
    rw [show coordinate cosine v-coordinate cosine u=-(coordinate cosine u-coordinate cosine v) by grind only,qabs_neg,
      qabs_eq_neg_of_nonpos (show v-u≤0 by grind only)]
    simpa only [Rat.neg_sub] using h

theorem chartPoint_difference {x y : Rat} (hx : 0≤x ∧ x≤1/2)
    (hy : 0≤y ∧ y≤1/2) (hxy : x≤y) (n : Nat) :
    qabs (chartPoint y n-chartPoint x n)≤8*(y-x)+9*width n := by
  let c := (unitArea.compute (precision n)).midpoint
  have hc := QInterval.midpoint_mem (RealCompute.interval_order_of_valid _ unitArea_valid (precision n))
  have hxT := areaPoint_target hx n c hc
  have hyT := areaPoint_target hy n c hc
  have cb := unitArea_bounds n
  have c0 : 0≤c := by dsimp [c]; grind only
  have c2 : c≤2 := by dsimp [c]; grind only
  have hgx := slope_geometry x n
  have hgy := slope_geometry y n
  have hxD : 0≤chartPoint x n ∧ chartPoint x n≤1 := ⟨hgx.1,Rat.le_trans hgx.2.1 hgx.2.2.1⟩
  have hyD : 0≤chartPoint y n ∧ chartPoint y n≤1 := ⟨hgy.1,Rat.le_trans hgy.2.1 hgy.2.2.1⟩
  have hxW := source_width (chartPoint x n) hxD n
  have hyW := source_width (chartPoint y n) hyD n
  have hxM := areaPoint_mem x n
  have hyM := areaPoint_mem y n
  have hp : 0≤width n := Rat.pow_nonneg (by decide +kernel)
  have hgap0 := Rat.mul_nonneg (show 0≤2*(y-x) by grind only) c0
  have hgap := Rat.mul_le_mul_of_nonneg_left c2 (show 0≤2*(y-x) by grind only)
  have xlo := neg_qabs_le_self (areaPoint x n-2*x*c)
  have xhi := self_le_qabs (areaPoint x n-2*x*c)
  have ylo := neg_qabs_le_self (areaPoint y n-2*y*c)
  have yhi := self_le_qabs (areaPoint y n-2*y*c)
  have hArea : qabs (areaPoint y n-areaPoint x n)≤4*(y-x)+4*width n := by
    apply qabs_le_of_neg_le_le <;> grind only
  have aLo := neg_qabs_le_self (areaPoint y n-areaPoint x n)
  have aHi := self_le_qabs (areaPoint y n-areaPoint x n)
  unfold QInterval.width at hxW hyW
  by_cases huv : chartPoint x n≤chartPoint y n
  · rw [qabs_eq_self_of_nonneg (show 0≤chartPoint y n-chartPoint x n by grind only)]
    have hi := (increment_bounds hxD.1 huv (precision n)).1
    have hk := (kernel_bounds hyD).1
    have hm := Rat.mul_le_mul_of_nonneg_left hk (show 0≤chartPoint y n-chartPoint x n by grind only)
    grind only
  · have hvu : chartPoint y n≤chartPoint x n := by grind only
    rw [qabs_eq_neg_of_nonpos (show chartPoint y n-chartPoint x n≤0 by grind only)]
    have hi := (increment_bounds hyD.1 hvu (precision n)).1
    have hk := (kernel_bounds hxD).1
    have hm := Rat.mul_le_mul_of_nonneg_left hk (show 0≤chartPoint x n-chartPoint y n by grind only)
    grind only

theorem quarter_sample_lipschitz (cosine : Bool) {x y : Rat}
    (hx : 0≤x ∧ x≤1/2) (hy : 0≤y ∧ y≤1/2) (hxy : x≤y) (n : Nat)
    (a b : Rat)
    (ha : ((quarter cosine x).compute n).lo≤a ∧ a≤((quarter cosine x).compute n).hi)
    (hb : ((quarter cosine y).compute n).lo≤b ∧ b≤((quarter cosine y).compute n).hi) :
    qabs (b-a)≤32*(y-x)+44*width n := by
  have ex := quarter_sample_error cosine x n ha
  have ey := quarter_sample_error cosine y n hb
  have gx := slope_geometry x n
  have gy := slope_geometry y n
  have hd := coordinate_lipschitz cosine
    ⟨gx.1,Rat.le_trans gx.2.1 gx.2.2.1⟩ ⟨gy.1,Rat.le_trans gy.2.1 gy.2.2.1⟩
  change qabs (coordinate cosine (chartPoint y n)-coordinate cosine (chartPoint x n))≤
    4*qabs (chartPoint y n-chartPoint x n) at hd
  have hi := chartPoint_difference hx hy hxy n
  have hm := Rat.mul_le_mul_of_nonneg_left hi (by decide +kernel : (0:Rat)≤4)
  have h1 := qabs_add_le_three (b-coordinate cosine (chartPoint y n))
    (coordinate cosine (chartPoint y n)-coordinate cosine (chartPoint x n))
    (-(a-coordinate cosine (chartPoint x n)))
  rw [qabs_neg] at h1
  have he : (b-coordinate cosine (chartPoint y n))+
      (coordinate cosine (chartPoint y n)-coordinate cosine (chartPoint x n))+
      -(a-coordinate cosine (chartPoint x n))=b-a := by grind only
  rw [he] at h1
  grind only

theorem scaled_width_shrinks {k : Rat} (hk : 0<k) : ShrinksToZero (fun n => k*width n) := by
  intro eps
  have he : 0<eps.val/k := by rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr hk)
  obtain ⟨N,hN⟩ := width_shrinks ⟨_,he⟩
  refine ⟨N,fun n hn => ?_⟩
  have hm := Rat.mul_le_mul_of_nonneg_left (hN n hn) (Rat.le_of_lt hk)
  change k*width n≤k*(eps.val/k) at hm
  have hc := Rat.mul_inv_cancel k (Rat.ne_of_gt hk)
  have hid : k*(eps.val/k)=eps.val := by rw [Rat.div_def]; grind only
  rw [hid] at hm
  exact hm

theorem quarter_lipschitz (cosine : Bool) {x y : Rat}
    (hx : 0≤x ∧ x≤1/2) (hy : 0≤y ∧ y≤1/2) (hxy : x≤y) :
    RealApproximationOrder.Small (RealApproximationOrder.sub (quarterValue cosine y) (quarterValue cosine x))
      (32*(y-x)) := by
  apply RealApproximationOrder.small_of_approximate_samples _ _ (fun n => 44*width n)
    (scaled_width_shrinks (by decide +kernel)) 0
  intro n _ s hs
  exact quarter_sample_lipschitz cosine hx hy hxy n _ _
    (hs (quarterValue cosine x).real) (hs (quarterValue cosine y).real)

theorem area_lower {u : Rat} (hu : 0≤u ∧ u≤1) :
    (RealCompute.ofRat (u/2)).Le (value u) := by
  intro i j
  have h := (increment_bounds (x := 0) (y := u) (by decide +kernel) hu.1 j).1
  have hz : ((value 0).compute j).lo=0 := arctanIntegralRectangleCompute_zero_lower _
  rw [hz] at h
  have hm := Rat.mul_le_mul_of_nonneg_left (kernel_bounds hu).1 hu.1
  change u/2≤((value u).compute j).hi
  grind only

theorem area_increment_lower {u v : Rat} (hu : 0≤u) (huv : u≤v) (hv : v≤1) :
    (RealCompute.ofRat ((v-u)/2)).Le (value v-value u) := by
  intro i j
  have h := (increment_bounds hu huv j).1
  have hm := Rat.mul_le_mul_of_nonneg_left (kernel_bounds ⟨Rat.le_trans hu huv,hv⟩).1
    (show 0≤v-u by grind only)
  change (v-u)/2≤((value v).compute j).hi-((value u).compute j).lo
  grind only

theorem inverse_zero_lower (n : Nat) : (slope 0 n).lo=0 := by
  have hg := slope_geometry 0 n
  have hb := (slope_target (x := 0) ⟨by decide +kernel,by decide +kernel⟩ n).1
  have hl := area_lower ⟨hg.1,Rat.le_trans hg.2.1 hg.2.2.1⟩
  have hv := value_valid ⟨hg.1,Rat.le_trans hg.2.1 hg.2.2.1⟩
  have ht := RealCompute.le_trans hv hl hb 0 0
  change (slope 0 n).lo/2≤(RealCompute.scaleRatCompute (2*0) unitArea 0).hi at ht
  have hz : (RealCompute.scaleRatCompute (2*0) unitArea 0).hi=0 := by
    simp [RealCompute.scaleRatCompute]
  rw [hz] at ht
  grind only

theorem inverse_half_upper (n : Nat) : (slope (1/2) n).hi=1 := by
  have hg := slope_geometry (1/2) n
  have hb := (slope_target (x := 1/2) ⟨by decide +kernel,Rat.le_refl⟩ n).2
  have hY : unitArea.Le (ArctanInverseCircle.quarterTarget (2*(1/2))) := by
    intro i j
    change (unitArea.compute i).lo≤(RealCompute.scaleRatCompute (2*(1/2)) unitArea j).hi
    rw [show (2:Rat)*(1/2)=1 by decide +kernel]
    simp only [RealCompute.scaleRatCompute,show (0:Rat)≤1 by decide +kernel,↓reduceIte,Rat.one_mul]
    exact RealCompute.le_refl _ unitArea_valid i j
  have hA := RealCompute.le_trans (ArctanInverseCircle.quarterTarget_valid _) hY hb
  have hD : (value 1-value (slope (1/2) n).hi).Le (RealCompute.ofRat 0) := by
    intro i j
    have h := hA i i
    change ((value 1).compute i).lo≤((value (slope (1/2) n).hi).compute i).hi at h
    change ((value 1).compute i).lo-((value (slope (1/2) n).hi).compute i).hi≤0
    grind only
  have hi := area_increment_lower (Rat.le_trans hg.1 hg.2.1) hg.2.2.1 (Rat.le_refl)
  have hv := RealCompute.sub_valid unitArea_valid (value_valid ⟨Rat.le_trans hg.1 hg.2.1,hg.2.2.1⟩)
  have h := RealCompute.le_trans hv hi hD 0 0
  change (1-(slope (1/2) n).hi)/2≤0 at h
  grind only

private theorem endpoint_equiv {X : RealCompute} (hv : X.Valid) (r : Rat)
    (edge : ∀ n, (X.compute n).lo=r ∨ (X.compute n).hi=r) : X.Equiv (RealCompute.ofRat r) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).mpr
  have ho := RealCompute.interval_order_of_valid _ hv n
  have he := edge n
  change (X.compute n).lo≤r ∧ r≤(X.compute n).hi
  constructor <;> grind only

theorem quarter_zero (cosine : Bool) :
    (quarter cosine 0).Equiv (RealCompute.ofRat (if cosine then 1 else 0)) := by
  cases cosine
  · apply endpoint_equiv (quarter_valid false 0) 0
    intro n
    left
    rw [quarter_compute]
    change coordinate false (slope 0 n).lo=0
    rw [inverse_zero_lower]
    decide +kernel
  · apply endpoint_equiv (quarter_valid true 0) 1
    intro n
    right
    rw [quarter_compute]
    change coordinate true (slope 0 n).lo=1
    rw [inverse_zero_lower]
    decide +kernel

theorem quarter_half (cosine : Bool) :
    (quarter cosine (1/2)).Equiv (RealCompute.ofRat (if cosine then 0 else 1)) := by
  cases cosine
  · apply endpoint_equiv (quarter_valid false (1/2)) 1
    intro n
    right
    rw [quarter_compute]
    change coordinate false (slope (1/2) n).hi=1
    rw [inverse_half_upper]
    decide +kernel
  · apply endpoint_equiv (quarter_valid true (1/2)) 0
    intro n
    left
    rw [quarter_compute]
    change coordinate true (slope (1/2) n).hi=0
    rw [inverse_half_upper]
    decide +kernel

theorem quarter_bounds (cosine : Bool) (q : Rat) (n : Nat) :
    0≤((quarter cosine q).compute n).lo ∧ ((quarter cosine q).compute n).hi≤1 := by
  have hg := slope_geometry q n
  have hlD : 0≤(slope q n).lo ∧ (slope q n).lo≤1 := ⟨hg.1,Rat.le_trans hg.2.1 hg.2.2.1⟩
  have hrD : 0≤(slope q n).hi ∧ (slope q n).hi≤1 := ⟨Rat.le_trans hg.1 hg.2.1,hg.2.2.1⟩
  cases cosine
  · exact ⟨(coordinate_bounds false hlD).1,(coordinate_bounds false hrD).2⟩
  · exact ⟨(coordinate_bounds true hrD).1,(coordinate_bounds true hlD).2⟩

end ComputableAnalysis.GeometricTrig


