-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EffectiveImproperIntegral
-- name    : liuyao_ca_fd889115_k1_Analysis_EffectiveImproperIntegral
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:09:45.483088+00:00
-- url     : https://prove2.me/theorems/46442e45-938c-4bc3-916c-a6ed4862aa3f
-- title:
--   Computable analysis · EffectiveImproperIntegral · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/EffectiveImproperIntegral.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RepresentedSeries
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralLimitValueAgreement
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueCongruence
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealIntervalImage

set_option autoImplicit true

/-! A literal interval computation from independently constructed compact
integrals and a quantitative Cauchy tail. No value of the improper integral,
closed form, or damping identity is assumed by the constructor. -/
namespace ComputableAnalysis.EffectiveImproperIntegral
open ComputableCoefficient RealApproximationOrder RawLimit Integral
set_option maxHeartbeats 800000

structure Data where
  compact : Nat → Value
  error : Nat → Rat
  nonnegative : ∀ n,0≤error n
  shrinks : ShrinksToZero error
  tail : ∀ n m,n≤m → Small (sub (compact m) (compact n)) (error n)

def Data.raw (D : Data) : RealCompute :=
  RepresentedSeries.sum D.compact D.error

private def Data.observations (D : Data) (n : Nat) (y : RealCompute) : Prop :=
  ∃ m,n≤m ∧ y=(D.compact m).real.preferred

private theorem Data.observations_antitone (D : Data) :
    ∀ n m,n≤m → ∀ y,D.observations m y → D.observations n y := by
  rintro n m hnm y ⟨k,hk,rfl⟩
  exact ⟨k,Nat.le_trans hnm hk,rfl⟩

private theorem Data.box_covers (D : Data) (n : Nat) (y : RealCompute) (hy : D.observations n y) :
    InInterval y (RepresentedSeries.box D.compact D.error n) := by
  obtain ⟨m,hm,rfl⟩ := hy
  exact inInterval_of_sub_bound (D.compact m).real.valid (D.compact n).real.valid (D.error n)
    (D.tail n m hm).1 (D.tail n m hm).2 (RepresentedSeries.stage D.compact n)

theorem Data.valid (D : Data) : D.raw.Valid :=
  prefix_valid (tests := D.observations) (s := fun n => n)
    D.observations_antitone
    (fun n => ⟨(D.compact n).real.preferred,(D.compact n).real.valid,n,Nat.le_refl _,rfl⟩)
    D.box_covers (RepresentedSeries.box_shrinks D.compact D.error D.shrinks)

/-- Every later compact value is covered by every earlier output box. -/
theorem Data.covers (D : Data) (n m : Nat) (hnm : n≤m) :
    InInterval (D.compact m).real.preferred (D.raw.compute n) :=
  by
  have hr : runningMax (fun n => n) n=n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [runningMax,ih]; omega
  apply prefix_cover (tests := D.observations) (s := fun n => n) D.observations_antitone
    D.box_covers n (D.compact m).real.preferred
  exact ⟨m,by rw [hr]; exact hnm,rfl⟩

theorem Data.tendsTo (D : Data) :
    TendsTo (fun n => (D.compact n).real.preferred) D.raw := by
  refine ⟨D.valid, fun n => (D.compact n).real.valid, ?_⟩
  intro m eps
  refine ⟨m, fun n hmn => ?_⟩
  apply RealIntervalImage.weaken (D.covers m n hmn)
  change (D.raw.compute m).lo - eps.val ≤ (D.raw.compute m).lo ∧
    (D.raw.compute m).hi ≤ (D.raw.compute m).hi + eps.val
  have hp := eps.property
  constructor <;> grind only

/-- A certified error for the independently computed compact integral at n. -/
theorem Data.within (D : Data) (n : Nat) : Within D.raw (D.compact n).real.preferred (D.error n) := by
  intro i j
  let m := max i n
  have hmI : i≤m := Nat.le_max_left _ _
  have hmN : n≤m := Nat.le_max_right _ _
  have hc := D.covers i m hmI
  have ht := inInterval_of_sub_bound (D.compact m).real.valid (D.compact n).real.valid (D.error n)
    (D.tail n m hmN).1 (D.tail n m hmN).2 j
  constructor
  · exact RealCompute.le_trans (D.compact m).real.valid hc.1 ht.2 0 0
  · have H := RealCompute.le_trans (D.compact m).real.valid ht.1 hc.2 0 0
    change ((D.compact n).real.compute j).lo-D.error n≤(D.raw.compute i).hi at H
    change ((D.compact n).real.compute j).lo≤(D.raw.compute i).hi+D.error n
    grind only

private theorem within_congr_right {I J K : RealCompute} {eps : Rat}
    (h : Within I J eps) (hI : I.Valid) (hJ : J.Valid) (hK : K.Valid) (he : J.Equiv K) : Within I K eps := by
  have hs : Within J I eps := by intro n m; exact ⟨(h m n).2,(h m n).1⟩
  have H := hs.congr_left hJ hK hI he
  intro n m
  exact ⟨(H m n).2,(H m n).1⟩

/-- Actual compact integral witnesses and the proved Cauchy tail certify the
computed raw value in the existing exhaustion-integral specification. -/
theorem Data.hasIntegralLimit (D : Data) (F : Nat → FunctionOnInterval)
    (compact : ∀ n,HasIntegral (F n) (D.compact n).real.preferred) : HasIntegralLimit F D.raw := by
  refine ⟨D.valid,fun n => ⟨(D.compact n).real.preferred,compact n⟩,?_⟩
  intro eps
  obtain ⟨N,hN⟩ := D.shrinks eps
  refine ⟨N,fun n hn J hJ => ?_⟩
  have H := within_congr_right (D.within n) D.valid (D.compact n).real.valid hJ.valid ((compact n).unique hJ)
  intro i j
  have hb := hN n hn
  have ht := H i j
  constructor <;> grind only

def Data.value (D : Data) : Value := parameter D.raw D.valid

theorem Data.distance (D : Data) (n : Nat) : Small (sub D.value (D.compact n)) (D.error n) := by
  constructor
  · intro i j
    have H := (D.within n j j).2
    change ((D.compact n).real.compute j).lo≤(D.raw.compute j).hi+D.error n at H
    change -(D.error n)≤(D.raw.compute j).hi-((D.compact n).real.compute j).lo
    grind only
  · intro i j
    have H := (D.within n i i).1
    change (D.raw.compute i).lo≤((D.compact n).real.compute i).hi+D.error n at H
    change (D.raw.compute i).lo-((D.compact n).real.compute i).hi≤D.error n
    grind only

/-- Shrinking finite error bounds imply an exact represented order bound. -/
theorem small_of_errors (X : Value) (B : Rat) (e : Nat → Rat)
    (he : ShrinksToZero e) (H : ∀ n,Small X (B+e n)) : Small X B := by
  constructor
  · intro i j
    change -B≤(X.real.compute j).hi
    by_cases h : -B≤(X.real.compute j).hi
    · exact h
    have hp : 0<(-B-(X.real.compute j).hi)/2 := by grind only
    obtain ⟨N,hN⟩ := he ⟨_,hp⟩
    have hn := hN N (Nat.le_refl _)
    have hh := (H N).1 0 j
    change -(B+e N)≤(X.real.compute j).hi at hh
    change e N≤(-B-(X.real.compute j).hi)/2 at hn
    grind only
  · intro i j
    change (X.real.compute i).lo≤B
    by_cases h : (X.real.compute i).lo≤B
    · exact h
    have hp : 0<((X.real.compute i).lo-B)/2 := by grind only
    obtain ⟨N,hN⟩ := he ⟨_,hp⟩
    have hn := hN N (Nat.le_refl _)
    have hh := (H N).2 i 0
    change (X.real.compute i).lo≤B+e N at hh
    change e N≤((X.real.compute i).lo-B)/2 at hn
    grind only

/-- Pass an eventual uniform finite-integral bound to the computed improper
integral; this uses no proposed closed form. -/
theorem Data.uniform_bound (D : Data) (K : Value) (B : Rat) (N : Nat)
    (H : ∀ n,N≤n → Small (sub (D.compact n) K) B) : Small (sub D.value K) B := by
  let e := fun n => D.error (max N n)
  have es : ShrinksToZero e := by
    intro eps
    obtain ⟨M,hM⟩ := D.shrinks eps
    exact ⟨M,fun n hn => hM (max N n) (by omega)⟩
  apply small_of_errors (sub D.value K) B e es
  intro n
  have F := (D.distance (max N n)).add (H (max N n) (Nat.le_max_left _ _))
  have hc : D.error (max N n)+B=B+e n := by dsimp [e]; grind only
  rw [hc] at F
  apply F.congr
  apply arithmetic_identity; intro s; simp only [Value.add,sub]; grind only

/-- A closed form is a separate theorem: it must itself have the actual
integral-limit role for this exhaustion. -/
theorem Data.identify (D : Data) (F : Nat → FunctionOnInterval)
    (compact : ∀ n,HasIntegral (F n) (D.compact n).real.preferred)
    {I : RealCompute} (hI : HasIntegralLimit F I) : D.raw.Equiv I :=
  (D.hasIntegralLimit F compact).unique hI

/-- A derivative has integral zero if its compact integrals are identified
by the FTC and both boundary values of its primitive decay. -/
theorem Data.integral_eq_zero_of_decaying_boundary (D : Data)
    (left right : Nat → Value) (bound : Nat → Rat) (shrinks : ShrinksToZero bound)
    (hleft : ∀ n, Small (left n) (bound n)) (hright : ∀ n, Small (right n) (bound n))
    (ftc : ∀ n, Same (D.compact n) (sub (right n) (left n))) :
    D.raw.Equiv (RealCompute.ofRat 0) := by
  have hsmall : Small D.value 0 := by
    apply small_of_errors D.value 0 (fun n => D.error n + (bound n + bound n))
    · intro eps
      let e : QPos := ⟨eps.val / 3, Rat.mul_pos eps.property (by decide +kernel)⟩
      obtain ⟨N, hN⟩ := D.shrinks e
      obtain ⟨M, hM⟩ := shrinks e
      refine ⟨max N M, fun n hn => ?_⟩
      have hn' := hN n (by omega)
      have hm' := hM n (by omega)
      change D.error n ≤ eps.val / 3 at hn'
      change bound n ≤ eps.val / 3 at hm'
      grind only
    · intro n
      have hs : Small (D.compact n) (bound n + bound n) := by
        apply ((hright n).add (hleft n).neg).congr
        refine Same.trans (Y := sub (right n) (left n)) ?_ (ftc n).symm
        apply arithmetic_identity
        intro s
        simp only [Value.add, Value.neg, sub]
        grind only
      simpa only [Rat.zero_add] using ((D.distance n).add hs).congr (y := D.value)
        (arithmetic_identity _ _ (by intro s; simp only [Value.add, sub]; grind only))
  have hupper : D.raw.Le (RealCompute.ofRat 0) := hsmall.2
  have hlower : (RealCompute.ofRat 0).Le D.raw := by
    intro i j
    change (0 : Rat) ≤ (D.raw.compute j).hi
    have h := hsmall.1 i j
    change -(0 : Rat) ≤ (D.raw.compute j).hi at h
    rwa [Rat.neg_zero] at h
  exact RealCompute.equiv_of_le_of_ge hupper hlower

end ComputableAnalysis.EffectiveImproperIntegral


