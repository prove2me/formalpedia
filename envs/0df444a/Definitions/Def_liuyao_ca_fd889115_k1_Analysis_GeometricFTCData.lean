-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricFTCData
-- name    : liuyao_ca_fd889115_k1_Analysis_GeometricFTCData
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:47:40.06974+00:00
-- url     : https://prove2.me/theorems/cf9dd4e9-95cb-47c8-b464-787e49998562
-- title:
--   Computable analysis · GeometricFTCData · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/GeometricFTCData.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricTaylorData
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCRealCalculus

set_option autoImplicit true

/-! Actual FTC data for geometric sine and cosine and every successive
pulled-back derivative. The rational parameter t traverses the segment from
zero to the supplied rational angle q, including negative angles. -/
namespace ComputableAnalysis.GeometricFTCData
open ComputableCoefficient RealApproximationOrder FTCRealOrder FTCRealCalculus GeometricTrig
set_option maxHeartbeats 600000

theorem firstOrder_any (cosine : Bool) (u v : Rat) (hs : qabs (v-u)≤1/4) :
    Small (sub (sub (valueFor cosine v) (valueFor cosine u)) (scale (v-u) (derivativeValue cosine u)))
      (1856*qabs (v-u)*qabs (v-u)) := by
  by_cases he : u=v
  · subst v
    simp only [Rat.sub_self,show qabs (0:Rat)=0 by decide +kernel,Rat.mul_zero]
    have hz : Small (Value.rational 0) 0 := by
      simpa only [show qabs (0:Rat)=0 by decide +kernel] using rational_small 0
    apply hz.congr
    apply arithmetic_identity
    intro s
    simp only [Value.rational,sub,scale]
    grind only
  by_cases huv : u<v
  · have hp : 0≤v-u := by grind only
    rw [qabs_eq_self_of_nonneg hp] at hs ⊢
    apply (full_firstOrder_small cosine huv hs).mono
    have hh := Rat.mul_nonneg hp hp
    grind only
  · have hvu : v<u := by grind only
    have hp : 0≤u-v := by grind only
    have ha : qabs (v-u)=u-v := by
      rw [show v-u= -(u-v) by grind only,qabs_neg,qabs_eq_self_of_nonneg hp]
    rw [ha] at hs ⊢
    have h := (full_firstOrder_small cosine hvu hs).neg
    have hd := (derivative_value_lipschitz cosine (Rat.le_of_lt hvu)).scale_nonnegative hp
    have ht := h.add hd
    have hr : 1600*(u-v)*(u-v)+(u-v)*(256*(u-v))=1856*(u-v)*(u-v) := by grind only
    rw [hr] at ht
    apply ht.congr
    apply arithmetic_identity
    intro s
    simp only [remainderValue,Value.neg,Value.add,sub,scale]
    grind only

def magnitude (q : Rat) : Rat := 8*qabs q
def error (q : Rat) : Rat := 1856*qabs q*qabs q

def radius (q : Rat) : QPos := ⟨1/(4*(qabs q+1)),by
  rw [Rat.div_def,Rat.one_mul]
  exact Rat.inv_pos.mpr (by have := qabs_nonneg q; grind only)⟩

/-- Successive derivatives of the actual geometric function along t ↦ q*t. -/
def family (q : Rat) : Nat → Bool → Rat → Value
  | 0,cosine,t => valueFor cosine (q*t)
  | n+1,cosine,t => scale q (Value.mul piValue
      (if cosine then Value.neg (family q n false t) else family q n true t))

theorem family_small (q : Rat) (n : Nat) (cosine : Bool) (t : Rat) :
    Small (family q n cosine t) ((magnitude q)^n) := by
  induction n generalizing cosine with
  | zero =>
    constructor
    · intro i j
      change -(magnitude q^0)≤((valueFor cosine (q*t)).real.preferred.compute j).hi
      rw [Rat.pow_zero,valueFor_raw]
      exact Rat.le_trans (sample_bounds cosine (q*t) j).1 (RealCompute.interval_order_of_valid _ (sample_valid _ _) j)
    · intro i j
      change ((valueFor cosine (q*t)).real.preferred.compute i).lo≤magnitude q^0
      rw [Rat.pow_zero,valueFor_raw]
      exact Rat.le_trans (RealCompute.interval_order_of_valid _ (sample_valid _ _) i) (sample_bounds cosine (q*t) i).2
  | succ n ih =>
    have h (c : Bool) := scale_small (pi_small.mul (ih c)) q
    have hn := scale_small (pi_small.mul ((ih false).neg)) q
    have he : qabs q*(8*magnitude q^n)=magnitude q^(n+1) := by
      rw [Rat.pow_succ]
      unfold magnitude
      grind only
    rw [he] at h hn
    cases cosine
    · exact h true
    · exact hn

private theorem radius_spec (q h : Rat) (hh : 0≤h) (hs : h≤(radius q).val) :
    qabs q*h≤1/4 := by
  have hQ := qabs_nonneg q
  have hc : (radius q).val*(4*(qabs q+1))=1 :=
    Rat.div_mul_cancel (by grind only : 4*(qabs q+1)≠0)
  have hp := (radius q).property
  have hm := Rat.mul_le_mul_of_nonneg_left hs hQ
  have hquarter : (4:Rat)*(1/4)=1 := by decide +kernel
  grind only

theorem family_firstOrder (q : Rat) (n : Nat) (cosine : Bool) :
    ∀ {a b : Rat}, FTCRealOrder.FirstOrder (family q n cosine) (family q (n+1) cosine) a b
      (error q*magnitude q^n) (radius q).val := by
  induction n generalizing cosine with
  | zero =>
    intro a b u v hu huv hv hs
    have hp : 0≤v-u := by grind only
    have he : qabs (q*v-q*u)=qabs q*(v-u) := by
      rw [show q*v-q*u=q*(v-u) by grind only,qabs_mul,qabs_eq_self_of_nonneg hp]
    have H := firstOrder_any cosine (q*u) (q*v) (by rw [he]; exact radius_spec q (v-u) hp hs)
    rw [he] at H
    have hr : 1856*(qabs q*(v-u))*(qabs q*(v-u))=(error q*magnitude q^0)*(v-u)*(v-u) := by
      rw [Rat.pow_zero,Rat.mul_one]
      unfold error
      grind only
    rw [hr] at H
    apply H.congr
    apply arithmetic_identity
    intro s
    cases cosine <;> simp only [family,derivativeValue,pairSlope,Value.mul,Value.neg,sub,scale,
      Bool.false_eq_true,↓reduceIte] <;> grind only
  | succ n ih =>
    intro a b u v hu huv hv hs
    have h (c : Bool) := scale_small (pi_small.mul (ih c u v hu huv hv hs)) q
    have hn := scale_small (pi_small.mul ((ih false u v hu huv hv hs).neg)) q
    have he : qabs q*(8*((error q*magnitude q^n)*(v-u)*(v-u)))=
        (error q*magnitude q^(n+1))*(v-u)*(v-u) := by
      rw [Rat.pow_succ]
      unfold magnitude
      grind only
    rw [he] at h hn
    cases cosine
    · apply (h true).congr
      apply arithmetic_identity
      intro s
      simp only [family,Value.mul,Value.neg,sub,scale,Bool.false_eq_true,↓reduceIte]
      grind only
    · apply hn.congr
      apply arithmetic_identity
      intro s
      simp only [family,Value.mul,Value.neg,sub,scale,↓reduceIte]
      grind only

/-- A real FTC step whose source is the actual geometric derivative family. -/
def step (q : Rat) (n : Nat) (cosine : Bool) {a b : Rat} :
    Step (family q n cosine) (family q (n+1) cosine) a b where
  error := error q*magnitude q^n
  error_nonnegative := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg q)) (qabs_nonneg q))
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg q)))
  radius := radius q
  firstOrder := family_firstOrder q n cosine
  variation := magnitude q^(n+2)
  variation_nonnegative := Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg q))
  lipschitz := lipschitz_of_firstOrder (family_firstOrder q (n+1) cosine)
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg q)) (qabs_nonneg q))
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg q))))
    (radius q).property (fun t _ _ => family_small q (n+2) cosine t)

end ComputableAnalysis.GeometricFTCData


