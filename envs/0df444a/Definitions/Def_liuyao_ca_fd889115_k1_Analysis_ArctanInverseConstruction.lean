-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ArctanInverseConstruction
-- name    : liuyao_ca_fd889115_k1_Analysis_ArctanInverseConstruction
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:14:03.243879+00:00
-- url     : https://prove2.me/theorems/e7ce7d96-d112-46b9-a3f8-07c0e8638d0b
-- title:
--   Computable analysis · ArctanInverseConstruction · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ArctanInverseConstruction.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ArctanSecantFoundation

set_option autoImplicit true

/-! Specific interval inversion of geometric arctangent on the unit branch.
The primary input is a rational target angle; represented targets use the
same algorithm as an add-on. No generic inverse function theorem is used. -/
namespace ComputableAnalysis.ArctanInverseConstruction
open ArctanSecantFoundation
set_option maxHeartbeats 100000

def precision (n : Nat) : Nat := 256*2^n
def width (n : Nat) : Rat := ((1:Rat)/2)^n
def step (Y : RealCompute) (n : Nat) (I : QInterval) : QInterval :=
  let M := (value I.midpoint).compute (precision n)
  let T := Y.compute (precision n)
  if M.hi<T.lo then {lo:=I.midpoint,hi:=I.hi}
  else if T.hi<M.lo then {lo:=I.lo,hi:=I.midpoint}
  else {lo:=I.lo+I.width/4,hi:=I.hi-I.width/4}

def bracket (Y : RealCompute) : Nat → QInterval
  | 0 => {lo:=0,hi:=1}
  | n+1 => step Y n (bracket Y n)

def inverse (y : Rat) : RealCompute := {compute:=bracket (RealCompute.ofRat y)}
def inverseExtension (Y : RealCompute) : RealCompute := {compute:=bracket Y}

theorem step_geometry (Y : RealCompute) (n : Nat) (I : QInterval)
    (ho : I.lo≤I.hi) :
    I.lo≤(step Y n I).lo ∧ (step Y n I).lo≤(step Y n I).hi ∧
    (step Y n I).hi≤I.hi ∧ (step Y n I).width=I.width/2 := by
  by_cases h : ((value I.midpoint).compute (precision n)).hi<(Y.compute (precision n)).lo
  · simp only [step,if_pos h]
    unfold QInterval.midpoint QInterval.width
    dsimp; grind [Rat.div_def]
  · by_cases h' : (Y.compute (precision n)).hi<((value I.midpoint).compute (precision n)).lo
    · simp only [step,if_neg h,if_pos h']
      unfold QInterval.midpoint QInterval.width
      dsimp; grind [Rat.div_def]
    · simp only [step,if_neg h,if_neg h']
      unfold QInterval.width
      dsimp; grind [Rat.div_def]

theorem bracket_geometry (Y : RealCompute) (n : Nat) :
    0≤(bracket Y n).lo ∧ (bracket Y n).lo≤(bracket Y n).hi ∧
    (bracket Y n).hi≤1 ∧ (bracket Y n).width=width n := by
  induction n with
  | zero => unfold bracket width QInterval.width; decide +kernel
  | succ n ih =>
    have h := step_geometry Y n (bracket Y n) ih.2.1
    refine ⟨Rat.le_trans ih.1 h.1,h.2.1,Rat.le_trans h.2.2.1 ih.2.2.1,?_⟩
    change (step Y n (bracket Y n)).width=width (n+1)
    rw [h.2.2.2,ih.2.2.2]
    unfold width; rw [Rat.pow_succ]; simp only [Rat.div_def,Rat.one_mul]

theorem inverseExtension_valid (Y : RealCompute) : (inverseExtension Y).Valid := by
  refine ⟨fun n => ?_,?_,?_⟩
  · have h := bracket_geometry Y n
    change 0≤(bracket Y n).hi-(bracket Y n).lo
    grind
  · intro n m hnm
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
    induction k with
    | zero => exact ⟨Rat.le_refl,(bracket_geometry Y n).2.1,Rat.le_refl⟩
    | succ k ih =>
      have ih := ih (by omega)
      have h := step_geometry Y (n+k) (bracket Y (n+k)) (bracket_geometry Y (n+k)).2.1
      exact ⟨Rat.le_trans ih.1 h.1,h.2.1,Rat.le_trans h.2.2.1 ih.2.2⟩
  · intro eps
    refine ⟨RationalMajorant.halfDecayShift 1 eps,fun n hn => ?_⟩
    rw [show (inverseExtension Y).compute n=bracket Y n from rfl,(bracket_geometry Y n).2.2.2]
    exact Rat.le_trans (Rat.le_refl) (by
      simpa [width] using RationalMajorant.halfDecayShift_spec_of_le (by decide +kernel : (0:Rat)≤1) eps hn)

theorem inverse_valid (y : Rat) : (inverse y).Valid := inverseExtension_valid _

theorem width_reciprocal (n : Nat) : width n=1/((2^n:Nat):Rat) :=
  RationalMajorant.half_pow_eq_one_div_nat_two_pow n

theorem source_width (x : Rat) (hx : 0≤x ∧ x≤1) (n : Nat) :
    ((value x).compute (precision n)).width≤width n/128 := by
  have h := arctanScheduledRectangleOnUnit_width_le x hx.1 hx.2 (precision n)
  change ((value x).compute (precision n)).width≤1/((16*(precision n+1):Nat):Rat) at h
  have hp : 0<(2^n:Nat) := Nat.pow_pos (by decide)
  have hc := Rat.mul_inv_cancel ((2^n:Nat):Rat) (by exact_mod_cast Nat.ne_of_gt hp)
  have he := width_reciprocal n
  rw [he]
  apply Rat.le_trans h
  have hd : 0<((16*(precision n+1):Nat):Rat) := by exact_mod_cast (by unfold precision; omega : 0<16*(precision n+1))
  have hd' : 0<((2^n:Nat):Rat) := by exact_mod_cast hp
  have hcc := Rat.mul_inv_cancel ((16*(precision n+1):Nat):Rat) (Rat.ne_of_gt hd)
  have hden : 128*((2^n:Nat):Rat)≤((16*(precision n+1):Nat):Rat) := by
    unfold precision; exact_mod_cast (by omega : 128*2^n≤16*(256*2^n+1))
  apply Rat.le_of_mul_le_mul_right (c:=((16*(precision n+1):Nat):Rat)*((2^n:Nat):Rat)) _ (Rat.mul_pos hd hd')
  simp only [Rat.div_def,Rat.one_mul]
  grind [Rat.mul_assoc,Rat.mul_comm]

private theorem separated_le {X Y : RealCompute} (hx : X.Valid) (hy : Y.Valid)
    (p : Nat) (h : (X.compute p).hi≤(Y.compute p).lo) : X.Le Y := by
  intro n m
  exact Rat.le_trans (RealCompute.le_refl X hx n p)
    (Rat.le_trans h (RealCompute.le_refl Y hy p m))

theorem step_brackets (Y : RealCompute) (hy : Y.Valid) (n : Nat) (I : QInterval)
    (hg : 0≤I.lo ∧ I.lo≤I.hi ∧ I.hi≤1 ∧ I.width=width n)
    (ht : (Y.compute (precision n)).width≤width n/128)
    (hb : (value I.lo).Le Y ∧ Y.Le (value I.hi)) :
    (value (step Y n I).lo).Le Y ∧ Y.Le (value (step Y n I).hi) := by
  have hm : 0≤I.midpoint ∧ I.midpoint≤1 := by
    unfold QInterval.midpoint; grind [Rat.div_def]
  have hmv := value_valid hm
  let p := precision n
  unfold step
  dsimp only
  split
  · next h => exact ⟨separated_le hmv hy p (Rat.le_of_lt h),hb.2⟩
  · next hnot =>
    split
    · next h => exact ⟨hb.1,separated_le hy hmv p (Rat.le_of_lt h)⟩
    · next hnot' =>
      let l := I.lo+I.width/4
      let r := I.hi-I.width/4
      have hl : 0≤l ∧ l≤I.midpoint := by dsimp [l]; unfold QInterval.width QInterval.midpoint; grind [Rat.div_def]
      have hr : I.midpoint≤r ∧ r≤1 := by dsimp [r]; unfold QInterval.width QInterval.midpoint; grind [Rat.div_def]
      have hld : 0≤l ∧ l≤1 := ⟨hl.1,Rat.le_trans hl.2 hm.2⟩
      have hrd : 0≤r ∧ r≤1 := ⟨Rat.le_trans hm.1 hr.1,hr.2⟩
      have hwM := source_width I.midpoint hm n
      have hwL := source_width l hld n
      have hwR := source_width r hrd n
      have hgapL := (increment_bounds hl.1 hl.2 p).1
      have hgapR := (increment_bounds hm.1 hr.1 p).1
      have hkM := (kernel_bounds hm).1
      have hkR := (kernel_bounds hrd).1
      have hmL := Rat.mul_le_mul_of_nonneg_left hkM (by grind : 0≤I.midpoint-l)
      have hmR := Rat.mul_le_mul_of_nonneg_left hkR (by grind : 0≤r-I.midpoint)
      have hdeltaL : I.midpoint-l=width n/4 := by
        dsimp [l]; rw [←hg.2.2.2]; unfold QInterval.midpoint QInterval.width; grind [Rat.div_def]
      have hdeltaR : r-I.midpoint=width n/4 := by
        dsimp [r]; rw [←hg.2.2.2]; unfold QInterval.midpoint QInterval.width; grind [Rat.div_def]
      rw [hdeltaL] at hgapL hmL
      rw [hdeltaR] at hgapR hmR
      have hwpos : 0<width n := Rat.pow_pos (by decide +kernel)
      constructor
      · apply separated_le (value_valid hld) hy p
        change ((value l).compute p).hi≤(Y.compute p).lo
        dsimp [p] at *
        unfold QInterval.width at hwM hwL ht
        grind [Rat.div_def]
      · apply separated_le hy (value_valid hrd) p
        change (Y.compute p).hi≤((value r).compute p).lo
        dsimp [p] at *
        unfold QInterval.width at hwM hwR ht
        grind [Rat.div_def]

theorem bracket_target (Y : RealCompute) (hy : Y.Valid)
    (ht : ∀ n, (Y.compute (precision n)).width≤width n/128)
    (hrange : (value 0).Le Y ∧ Y.Le (value 1)) (n : Nat) :
    (value (bracket Y n).lo).Le Y ∧ Y.Le (value (bracket Y n).hi) := by
  induction n with
  | zero => exact hrange
  | succ n ih => exact step_brackets Y hy n (bracket Y n) (bracket_geometry Y n) (ht n) ih

theorem rational_target (y : Rat)
    (hrange : (value 0).Le (RealCompute.ofRat y) ∧ (RealCompute.ofRat y).Le (value 1)) (n : Nat) :
    (value ((inverse y).compute n).lo).Le (RealCompute.ofRat y) ∧
      (RealCompute.ofRat y).Le (value ((inverse y).compute n).hi) := by
  apply bracket_target (RealCompute.ofRat y) (show (RealCompute.ofRat y).Valid from RealCompute.ofRat_valid y) (fun n => ?_) hrange n
  change y-y≤width n/128
  have h : 0≤width n/128 := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.pow_nonneg (by decide +kernel)) (by decide +kernel)
  grind

def forwardCandidate (Y : RealCompute) : RealCompute where
  compute n :=
    {lo:=((value (bracket Y n).lo).compute (precision n)).lo,
     hi:=((value (bracket Y n).hi).compute (precision n)).hi}

private theorem image_width_bound (A B : QInterval) (w : Rat)
    (hw : 0≤w) (ha : A.width≤w/128) (hb : B.width≤w/128)
    (hc : B.lo-A.hi≤w) : B.hi-A.lo≤2*w := by
  unfold QInterval.width at ha hb
  grind only [Rat.div_def]

theorem forward_width (Y : RealCompute) (n : Nat) :
    ((forwardCandidate Y).compute n).width≤2*width n := by
  have hg := bracket_geometry Y n
  have hl := source_width (bracket Y n).lo ⟨hg.1,Rat.le_trans hg.2.1 hg.2.2.1⟩ n
  have hu := source_width (bracket Y n).hi ⟨Rat.le_trans hg.1 hg.2.1,hg.2.2.1⟩ n
  have hi := (increment_bounds hg.1 hg.2.1 (precision n)).2
  have hk := (kernel_bounds ⟨hg.1,Rat.le_trans hg.2.1 hg.2.2.1⟩).2
  have hm := Rat.mul_le_mul_of_nonneg_left hk (by grind : 0≤(bracket Y n).hi-(bracket Y n).lo)
  have hw : 0≤width n := Rat.pow_nonneg (by decide +kernel)
  have hc : ((value (bracket Y n).hi).compute (precision n)).lo-
      ((value (bracket Y n).lo).compute (precision n)).hi≤width n := by
    have h := Rat.le_trans hi hm
    rw [Rat.mul_one] at h
    change _≤(bracket Y n).width at h
    rw [hg.2.2.2] at h
    exact h
  exact image_width_bound ((value (bracket Y n).lo).compute (precision n))
    ((value (bracket Y n).hi).compute (precision n)) (width n) hw hl hu hc

theorem width_shrinks : ShrinksToZero width := by
  intro eps
  exact ⟨RationalMajorant.halfDecayShift 1 eps,fun n hn => by
    simpa [width] using RationalMajorant.halfDecayShift_spec_of_le (by decide +kernel : (0:Rat)≤1) eps hn⟩

def forward (Y : RealCompute) : RealCompute :=
  RealCompute.prefixStabilize (forwardCandidate Y) (fun n => (Y.compute n).width)

/-- Evaluating the forward function through the constructed shrinking input
brackets gives the exact target. This is the derived irrational evaluation,
proved from rational endpoint computations. -/
theorem forward_valid_and_target (Y : RealCompute) (hy : Y.Valid)
    (ht : ∀ n, (Y.compute (precision n)).width≤width n/128)
    (hrange : (value 0).Le Y ∧ Y.Le (value 1)) :
    (forward Y).Valid ∧ (forward Y).Equiv Y := by
  have hb := bracket_target Y hy ht hrange
  have hover : (forwardCandidate Y).Equiv Y := by
    intro n
    apply (RealCompute.compareAt_overlap_iff _ _ n n).2
    exact ⟨(hb n).1 (precision n) n,(hb n).2 n (precision n)⟩
  have hs : RealCompute.WidthsShrinkToZero (forwardCandidate Y).compute := by
    intro eps
    let half : QPos := ⟨eps.val/2,by rw [Rat.div_def]; exact Rat.mul_pos eps.property (by decide +kernel)⟩
    obtain ⟨N,hN⟩ := width_shrinks half
    refine ⟨N,fun n hn => ?_⟩
    have h := Rat.mul_le_mul_of_nonneg_left (hN n hn) (by decide +kernel : (0:Rat)≤2)
    dsimp [half] at h
    have hc := Rat.mul_inv_cancel (2:Rat) (by decide +kernel)
    exact Rat.le_trans (forward_width Y n) (by grind only [Rat.div_def])
  exact ⟨RealCompute.prefixStabilize_valid hs hy hover (fun _ => Rat.le_refl) hy.2.2,
    RealCompute.prefixStabilize_equiv_anchor hy hover (fun _ => Rat.le_refl)⟩

theorem rational_forward_target (y : Rat)
    (hrange : (value 0).Le (RealCompute.ofRat y) ∧ (RealCompute.ofRat y).Le (value 1)) :
    (forward (RealCompute.ofRat y)).Valid ∧ (forward (RealCompute.ofRat y)).Equiv (RealCompute.ofRat y) := by
  apply forward_valid_and_target _ (show (RealCompute.ofRat y).Valid from RealCompute.ofRat_valid y)
    (fun n => ?_) hrange
  · change y-y≤width n/128
    have h : 0≤width n/128 := by rw [Rat.div_def]; exact Rat.mul_nonneg (Rat.pow_nonneg (by decide +kernel)) (by decide +kernel)
    grind

end ComputableAnalysis.ArctanInverseConstruction


