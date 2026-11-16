-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricPeriodic
-- name    : liuyao_ca_fd889115_k1_Analysis_GeometricPeriodic
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:35:25.917419+00:00
-- url     : https://prove2.me/theorems/476a28d3-4f4c-45f9-9aa5-527ccd9dfa7a
-- title:
--   Computable analysis · GeometricPeriodic · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/GeometricPeriodic.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricQuarterEstimates
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzRealExtension

set_option autoImplicit true

/-! Joining the geometric quarters, including their shared endpoints, and
deriving period-two real evaluation from the primary rational samplers. -/
namespace ComputableAnalysis.GeometricTrig
open RawLimit ComputableCoefficient GeometricTrigChart
set_option maxHeartbeats 3000000

private theorem neg_difference_bounds (x y : RealCompute) (B : Rat)
    (h : InInterval (y-x) {lo := -B,hi := B}) :
    InInterval ((-y)-(-x)) {lo := -B,hi := B} := by
  constructor
  · intro i j
    have hh := h.2 j 0
    change (y.compute j).lo-(x.compute j).hi≤B at hh
    change -B≤ -(y.compute j).lo-(-(x.compute j).hi)
    grind only
  · intro i j
    have hh := h.1 0 i
    change -B≤(y.compute i).hi-(x.compute i).lo at hh
    change -(y.compute i).hi-(-(x.compute i).lo)≤B
    grind only

private theorem swap_difference_bounds (x y : RealCompute) (B : Rat)
    (h : InInterval (y-x) {lo := -B,hi := B}) :
    InInterval (x-y) {lo := -B,hi := B} := by
  constructor
  · intro i j
    have hh := h.2 j 0
    change (y.compute j).lo-(x.compute j).hi≤B at hh
    change -B≤(x.compute j).hi-(y.compute j).lo
    grind only
  · intro i j
    have hh := h.1 0 i
    change -B≤(y.compute i).hi-(x.compute i).lo at hh
    change (x.compute i).lo-(y.compute i).hi≤B
    grind only

theorem turn_lipschitz (j : Int) (cosine : Bool) {u v : Rat}
    (hu : 0≤u ∧ u≤1/2) (hv : 0≤v ∧ v≤1/2) (huv : u≤v) :
    InInterval (turn j cosine v-turn j cosine u) {lo := -32*(v-u),hi := 32*(v-u)} := by
  have h (c : Bool) : InInterval (quarter c v-quarter c u) {lo := -(32*(v-u)),hi := 32*(v-u)} :=
    quarter_lipschitz c hu hv huv
  have hn (c : Bool) := neg_difference_bounds (quarter c u) (quarter c v) (32*(v-u)) (h c)
  have he : -(32*(v-u))=(-32:Rat)*(v-u) := by grind only
  simp only [he] at h hn
  unfold turn
  split
  · exact h cosine
  · split
    · cases cosine
      · simpa only [Bool.false_eq_true,↓reduceIte] using h true
      · exact hn false
    · split
      · exact hn cosine
      · cases cosine
        · simpa only [Bool.false_eq_true,↓reduceIte] using hn true
        · exact h false

def turnScalar (j : Int) (cosine : Bool) (s c : Rat) : Rat :=
  if j%4=0 then (if cosine then c else s)
  else if j%4=1 then (if cosine then -s else c)
  else if j%4=2 then -(if cosine then c else s)
  else (if cosine then s else -c)

theorem turn_equiv_scalar (j : Int) (cosine : Bool) (q s c : Rat)
    (hs : (quarter false q).Equiv (RealCompute.ofRat s))
    (hc : (quarter true q).Equiv (RealCompute.ofRat c)) :
    (turn j cosine q).Equiv (RealCompute.ofRat (turnScalar j cosine s c)) := by
  have negRat (r : Rat) : (-RealCompute.ofRat r).Equiv (RealCompute.ofRat (-r)) := by
    intro n
    apply (RealCompute.compareAt_overlap_iff _ _ n n).mpr
    change -r≤ -r ∧ -r≤ -r
    exact ⟨Rat.le_refl,Rat.le_refl⟩
  have hnegS := RealCompute.equiv_trans (x := -(quarter false q)) (y := -(RealCompute.ofRat s))
    (z := RealCompute.ofRat (-s)) (RealCompute.neg_valid (quarter_valid false q))
    (RealCompute.neg_valid (RealCompute.ofRat_valid s)) (RealCompute.ofRat_valid (-s)) (RealCompute.neg_equiv hs) (negRat s)
  have hnegC := RealCompute.equiv_trans (x := -(quarter true q)) (y := -(RealCompute.ofRat c))
    (z := RealCompute.ofRat (-c)) (RealCompute.neg_valid (quarter_valid true q))
    (RealCompute.neg_valid (RealCompute.ofRat_valid c)) (RealCompute.ofRat_valid (-c)) (RealCompute.neg_equiv hc) (negRat c)
  unfold turn turnScalar
  split
  · cases cosine
    · simpa only [Bool.false_eq_true,↓reduceIte] using hs
    · exact hc
  · split
    · cases cosine
      · simpa only [Bool.false_eq_true,↓reduceIte] using hc
      · exact hnegS
    · split
      · cases cosine
        · simpa only [Bool.false_eq_true,↓reduceIte] using hnegS
        · exact hnegC
      · cases cosine
        · simpa only [Bool.false_eq_true,↓reduceIte] using hnegC
        · exact hs

theorem turnScalar_join (j : Int) (cosine : Bool) :
    turnScalar j cosine 1 0=turnScalar (j+1) cosine 0 1 := by
  have hj : j%4=0 ∨ j%4=1 ∨ j%4=2 ∨ j%4=3 := by omega
  rcases hj with h | h | h | h
  · have he : (j+1)%4=1 := by omega
    cases cosine <;> simp only [turnScalar,h,he,Bool.false_eq_true,↓reduceIte] <;> decide +kernel
  · have he : (j+1)%4=2 := by omega
    cases cosine <;> simp only [turnScalar,h,he,Bool.false_eq_true,↓reduceIte] <;> decide +kernel
  · have he : (j+1)%4=3 := by omega
    cases cosine <;> simp only [turnScalar,h,he,Bool.false_eq_true,↓reduceIte] <;> decide +kernel
  · have he : (j+1)%4=0 := by omega
    cases cosine <;> simp only [turnScalar,h,he,Bool.false_eq_true,↓reduceIte] <;> decide +kernel

theorem turn_join (j : Int) (cosine : Bool) :
    (turn j cosine (1/2)).Equiv (turn (j+1) cosine 0) := by
  have hl := turn_equiv_scalar j cosine (1/2) 1 0 (quarter_half false) (quarter_half true)
  have hr := turn_equiv_scalar (j+1) cosine 0 0 1 (quarter_zero false) (quarter_zero true)
  rw [turnScalar_join] at hl
  exact RealCompute.equiv_trans (y := RealCompute.ofRat (turnScalar (j+1) cosine 0 1))
    (turn_valid j cosine (1/2)) (RealCompute.ofRat_valid _)
    (turn_valid (j+1) cosine 0) hl (RealCompute.equiv_symm hr)

theorem quarterIndex_inside {j : Int} {q : Rat}
    (hl : (j:Rat)/2≤q) (hr : q<((j+1:Int):Rat)/2) : quarterIndex q=j := by
  have h1 : (j:Rat)≤2*q := by grind only
  have h2 : 2*q<((j+1:Int):Rat) := by grind only
  have hL : j≤(2*q).floor := Rat.le_floor_iff.mpr h1
  have hR : (2*q).floor<j+1 := Rat.floor_lt_iff.mpr h2
  unfold quarterIndex
  omega

theorem sample_on_closed_quarter (j : Int) (cosine : Bool) {q : Rat}
    (hl : (j:Rat)/2≤q) (hr : q≤((j+1:Int):Rat)/2) :
    (sample cosine q).Equiv (turn j cosine (q-(j:Rat)/2)) := by
  by_cases he : q=((j+1:Int):Rat)/2
  · have hi : quarterIndex q=j+1 := by
      unfold quarterIndex
      rw [show 2*q=((j+1:Int):Rat) by grind only,Rat.floor_intCast]
    have ht : quarterArgument q/2=0 := by unfold quarterArgument; rw [hi]; grind only
    have hd : q-(j:Rat)/2=1/2 := by rw [Rat.intCast_add] at he; grind only
    unfold sample
    rw [hi,ht,hd]
    exact RealCompute.equiv_symm (turn_join j cosine)
  · have hi := quarterIndex_inside hl (show q<((j+1:Int):Rat)/2 by grind only)
    have ht : quarterArgument q/2=q-(j:Rat)/2 := by unfold quarterArgument; rw [hi]; grind only
    unfold sample
    rw [hi,ht]
    exact RealCompute.equiv_refl _ (turn_valid _ _ _)

theorem sample_piece_lipschitz (j : Int) (cosine : Bool) {u v : Rat}
    (hu : (j:Rat)/2≤u) (huv : u≤v) (hv : v≤((j+1:Int):Rat)/2) :
    InInterval (sample cosine v-sample cosine u) {lo := -32*(v-u),hi := 32*(v-u)} := by
  have hhalf : ((j+1:Int):Rat)/2=(j:Rat)/2+1/2 := by rw [Rat.intCast_add]; grind only
  have h := turn_lipschitz j cosine (u := u-(j:Rat)/2) (v := v-(j:Rat)/2)
    ⟨by grind only,by grind only⟩ ⟨by grind only,by grind only⟩ (by grind only)
  have he : (v-(j:Rat)/2)-(u-(j:Rat)/2)=v-u := by grind only
  rw [he] at h
  have eu := sample_on_closed_quarter j cosine hu (Rat.le_trans huv hv)
  have ev := sample_on_closed_quarter j cosine (Rat.le_trans hu huv) hv
  exact inInterval_congr (RealCompute.sub_valid (turn_valid _ _ _) (turn_valid _ _ _))
    (RealCompute.sub_valid (sample_valid _ _) (sample_valid _ _))
    (RealCompute.equiv_symm (RealCompute.sub_equiv (sample_valid _ _) (turn_valid _ _ _)
      (sample_valid _ _) (turn_valid _ _ _) ev eu)) h

theorem turn_bounds (j : Int) (cosine : Bool) (q : Rat) (n : Nat) :
    -1≤((turn j cosine q).compute n).lo ∧ ((turn j cosine q).compute n).hi≤1 := by
  have pos (c : Bool) : -1≤((quarter c q).compute n).lo ∧ ((quarter c q).compute n).hi≤1 := by
    have h := quarter_bounds c q n
    constructor <;> grind only
  have neg (c : Bool) : -1≤((-(quarter c q)).compute n).lo ∧ ((-(quarter c q)).compute n).hi≤1 := by
    have h := quarter_bounds c q n
    change -1≤ -((quarter c q).compute n).hi ∧ -((quarter c q).compute n).lo≤1
    constructor <;> grind only
  unfold turn
  split
  · exact pos cosine
  · split
    · cases cosine
      · simpa only [Bool.false_eq_true,↓reduceIte] using pos true
      · exact neg false
    · split
      · exact neg cosine
      · cases cosine
        · simpa only [Bool.false_eq_true,↓reduceIte] using neg true
        · exact pos false

theorem sample_bounds (cosine : Bool) (q : Rat) (n : Nat) :
    -1≤((sample cosine q).compute n).lo ∧ ((sample cosine q).compute n).hi≤1 := turn_bounds _ _ _ _

private theorem two_difference_bounds (x y z : RealCompute) (hx : x.Valid) (hy : y.Valid) (hz : z.Valid)
    (B C : Rat) (h1 : InInterval (y-x) {lo := -B,hi := B})
    (h2 : InInterval (z-y) {lo := -C,hi := C}) : InInterval (z-x) {lo := -(B+C),hi := B+C} := by
  have hv := RealCompute.add_valid (RealCompute.sub_valid hy hx) (RealCompute.sub_valid hz hy)
  have he := RealCompute.sub_add_sub_cancel_middle_equiv hx hy hz
  have ht := RealCompute.sub_valid hz hx
  have hl := RealCompute.le_trans hv (RealCompute.le_add_le_add h1.1 h2.1) (RealCompute.le_of_equiv hv ht he)
  have hu := RealCompute.le_trans hv (RealCompute.le_of_equiv ht hv (RealCompute.equiv_symm he)) (RealCompute.le_add_le_add h1.2 h2.2)
  constructor
  · intro i j
    have h := hl i j
    change -B+ -C≤((z-x).compute j).hi at h
    change -(B+C)≤((z-x).compute j).hi
    grind only
  · intro i j; exact hu i j

theorem sample_ordered_lipschitz (cosine : Bool) {u v : Rat} (huv : u≤v) :
    InInterval (sample cosine v-sample cosine u) {lo := -32*(v-u),hi := 32*(v-u)} := by
  let j := quarterIndex u
  let k := quarterIndex v
  have jL := Rat.floor_le (2*u)
  have jR := Rat.lt_floor_add_one (2*u)
  have kL := Rat.floor_le (2*v)
  have kR := Rat.lt_floor_add_one (2*v)
  change (j:Rat)≤2*u at jL
  change ((k:Rat))≤2*v at kL
  change 2*u<((j+1:Int):Rat) at jR
  change 2*v<((k+1:Int):Rat) at kR
  have hjk : j≤k := Rat.floor_monotone (by grind only : 2*u≤2*v)
  have huL : (j:Rat)/2≤u := by grind only
  have huR : u≤((j+1:Int):Rat)/2 := by grind only
  have hvL : (k:Rat)/2≤v := by grind only
  have hvR : v≤((k+1:Int):Rat)/2 := by grind only
  by_cases he : j=k
  · rw [←he] at hvR
    exact sample_piece_lipschitz j cosine huL huv hvR
  by_cases ha : k=j+1
  · rw [ha] at hvL hvR
    let c : Rat := ((j+1:Int):Rat)/2
    have h1 := sample_piece_lipschitz j cosine huL huR (Rat.le_refl : c≤c)
    have h2 := sample_piece_lipschitz (j+1) cosine (Rat.le_refl : c≤c) hvL hvR
    have h := two_difference_bounds (sample cosine u) (sample cosine c) (sample cosine v)
      (sample_valid cosine u) (sample_valid cosine c) (sample_valid cosine v)
      (32*(c-u)) (32*(v-c)) (by simpa only [Rat.neg_mul] using h1) (by simpa only [Rat.neg_mul] using h2)
    have hb : 32*(c-u)+32*(v-c)=32*(v-u) := by grind only
    rw [hb] at h
    simpa only [Rat.neg_mul] using h
  · have hi : j+2≤k := by omega
    have hRat : ((j+2:Int):Rat)≤(k:Rat) := by exact_mod_cast hi
    rw [Rat.intCast_add] at hRat jR
    have gap : 1/2≤v-u := by grind only
    constructor
    · intro i n
      have huB := sample_bounds cosine u n
      have hvB := sample_bounds cosine v n
      have hoU := RealCompute.interval_order_of_valid _ (sample_valid cosine u) n
      have hoV := RealCompute.interval_order_of_valid _ (sample_valid cosine v) n
      change -32*(v-u)≤((sample cosine v).compute n).hi-((sample cosine u).compute n).lo
      grind only
    · intro n i
      have huB := sample_bounds cosine u n
      have hvB := sample_bounds cosine v n
      have hoU := RealCompute.interval_order_of_valid _ (sample_valid cosine u) n
      have hoV := RealCompute.interval_order_of_valid _ (sample_valid cosine v) n
      change ((sample cosine v).compute n).lo-((sample cosine u).compute n).hi≤32*(v-u)
      grind only

theorem sample_lipschitz (cosine : Bool) : LipschitzRealExtension.Lipschitz (sample cosine) 32 := by
  intro u v
  by_cases h : u≤v
  · have hs := sample_ordered_lipschitz cosine h
    rw [qabs_eq_self_of_nonneg (show 0≤v-u by grind only)]
    exact hs
  · have hvu : v≤u := by grind only
    have hs := swap_difference_bounds (sample cosine v) (sample cosine u) (32*(u-v))
      (by simpa only [Rat.neg_mul] using sample_ordered_lipschitz cosine hvu)
    rw [qabs_eq_neg_of_nonpos (show v-u≤0 by grind only)]
    have he : 32*(-(v-u))=32*(u-v) := by grind only
    have hl : -32*(-(v-u))=-(32*(u-v)) := by grind only
    simpa only [InInterval,he,hl] using hs

theorem turn_width (j : Int) (cosine : Bool) (q : Rat) (n : Nat) :
    ((turn j cosine q).compute n).width≤4*ArctanInverseConstruction.width n := by
  have pos (c : Bool) := quarter_width c q n
  have neg (c : Bool) : ((-(quarter c q)).compute n).width≤4*ArctanInverseConstruction.width n := by
    change -((quarter c q).compute n).lo-(-((quarter c q).compute n).hi)≤_
    have h := pos c
    unfold QInterval.width at h
    grind only
  unfold turn
  split
  · exact pos cosine
  · split
    · cases cosine
      · simpa only [Bool.false_eq_true,↓reduceIte] using pos true
      · exact neg false
    · split
      · exact neg cosine
      · cases cosine
        · simpa only [Bool.false_eq_true,↓reduceIte] using neg true
        · exact pos false

theorem sample_width (cosine : Bool) (q : Rat) (n : Nat) :
    ((sample cosine q).compute n).width≤4*ArctanInverseConstruction.width n := turn_width _ _ _ _

/-- Derived evaluation at an arbitrary real name. The code samples only the
primary rational geometric function and never tests a real quadrant. -/
def sinAt (x : RealCompute) : RealCompute := LipschitzRealExtension.extend sin 32 x
def cosAt (x : RealCompute) : RealCompute := LipschitzRealExtension.extend cos 32 x

theorem sinAt_valid {x : RealCompute} (hx : x.Valid) : (sinAt x).Valid :=
  LipschitzRealExtension.valid sin_valid (by decide +kernel) (sample_lipschitz false)
    (fun n => 4*ArctanInverseConstruction.width n) (scaled_width_shrinks (by decide +kernel)) (sample_width false) hx
theorem cosAt_valid {x : RealCompute} (hx : x.Valid) : (cosAt x).Valid :=
  LipschitzRealExtension.valid cos_valid (by decide +kernel) (sample_lipschitz true)
    (fun n => 4*ArctanInverseConstruction.width n) (scaled_width_shrinks (by decide +kernel)) (sample_width true) hx

theorem sinAt_rational (q : Rat) : (sinAt (RealCompute.ofRat q)).Equiv (sin q) :=
  LipschitzRealExtension.rational_agreement sin_valid (by decide +kernel) (sample_lipschitz false) q
theorem cosAt_rational (q : Rat) : (cosAt (RealCompute.ofRat q)).Equiv (cos q) :=
  LipschitzRealExtension.rational_agreement cos_valid (by decide +kernel) (sample_lipschitz true) q

theorem sinAt_congr {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) (he : x.Equiv y) :
    (sinAt x).Equiv (sinAt y) := LipschitzRealExtension.congr sin_valid (by decide +kernel) (sample_lipschitz false) hx hy he
theorem cosAt_congr {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) (he : x.Equiv y) :
    (cosAt x).Equiv (cosAt y) := LipschitzRealExtension.congr cos_valid (by decide +kernel) (sample_lipschitz true) hx hy he

theorem sinAt_period_compute (x : RealCompute) (n : Nat) :
    (sinAt (x+RealCompute.ofRat 2)).compute n=(sinAt x).compute n :=
  LipschitzRealExtension.period_compute sin 32 2 sin_period x n
theorem cosAt_period_compute (x : RealCompute) (n : Nat) :
    (cosAt (x+RealCompute.ofRat 2)).compute n=(cosAt x).compute n :=
  LipschitzRealExtension.period_compute cos 32 2 cos_period x n

theorem sinAt_period {x : RealCompute} (hx : x.Valid) :
    (sinAt (x+RealCompute.ofRat 2)).Equiv (sinAt x) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).mpr
  rw [sinAt_period_compute]
  have h := RealCompute.interval_order_of_valid _ (sinAt_valid hx) n
  exact ⟨h,h⟩
theorem cosAt_period {x : RealCompute} (hx : x.Valid) :
    (cosAt (x+RealCompute.ofRat 2)).Equiv (cosAt x) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).mpr
  rw [cosAt_period_compute]
  have h := RealCompute.interval_order_of_valid _ (cosAt_valid hx) n
  exact ⟨h,h⟩

end ComputableAnalysis.GeometricTrig


