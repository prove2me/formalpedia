-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzRealExtension
-- name    : liuyao_ca_fd889115_k1_Analysis_LipschitzRealExtension
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:57:28.640631+00:00
-- url     : https://prove2.me/theorems/b4cdd766-66e0-44b1-ac68-a61da7f80dec
-- title:
--   Computable analysis · LipschitzRealExtension · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/LipschitzRealExtension.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ParametrizedContinuity

set_option autoImplicit true

/-! Derived real evaluation of a rational-input function. Finite-prefix
intersections cover whole input intervals; no real branch/equality test is
used. Periodic rational samplers yield periodic represented-real extensions. -/
namespace ComputableAnalysis.LipschitzRealExtension
open RawLimit BracketDerivative
set_option maxHeartbeats 2000000

def Lipschitz (f : Rat → RealCompute) (L : Rat) : Prop :=
  ∀ u v, (RealCompute.ofRat (-L*qabs (v-u))).Le (f v-f u) ∧
    (f v-f u).Le (RealCompute.ofRat (L*qabs (v-u)))

theorem translated_enclosure {x y : RealCompute} (hx : x.Valid) (hy : y.Valid)
    (D : Rat) (h : (RealCompute.ofRat (-D)).Le (y-x) ∧ (y-x).Le (RealCompute.ofRat D)) (n : Nat) :
    InInterval y {lo:=(x.compute n).lo-D,hi:=(x.compute n).hi+D} := by
  constructor
  · intro i j
    let k := max n j
    have hh := h.1 0 k
    have hn := hx.2.1 n k (Nat.le_max_left _ _)
    have hj := hy.2.1 j k (Nat.le_max_right _ _)
    change -D≤(y.compute k).hi-(x.compute k).lo at hh
    change (x.compute n).lo-D≤(y.compute j).hi
    grind only
  · intro i j
    let k := max n i
    have hh := h.2 k 0
    have hn := hx.2.1 n k (Nat.le_max_left _ _)
    have hi := hy.2.1 i k (Nat.le_max_right _ _)
    change (y.compute k).lo-(x.compute k).hi≤D at hh
    change (y.compute i).lo≤(x.compute n).hi+D
    grind only

def box (f : Rat → RealCompute) (L : Rat) (x : RealCompute) (n : Nat) : QInterval :=
  QInterval.expand ((f (x.compute n).lo).compute n) (L*(x.compute n).width)

def interval (f : Rat → RealCompute) (L : Rat) (x : RealCompute) : Nat → QInterval
  | 0 => box f L x 0
  | n+1 => QInterval.intersection (interval f L x n) (box f L x (n+1))

def extend (f : Rat → RealCompute) (L : Rat) (x : RealCompute) : RealCompute where
  compute := interval f L x

theorem box_covers {f : Rat → RealCompute} {L : Rat} (hf : ∀ q, (f q).Valid)
    (hL : 0≤L) (lip : Lipschitz f L) {x : RealCompute} (n : Nat) {r : Rat}
    (hr : (x.compute n).lo≤r ∧ r≤(x.compute n).hi) : InInterval (f r) (box f L x n) := by
  have h := translated_enclosure (hf (x.compute n).lo) (hf r)
    (L*qabs (r-(x.compute n).lo)) (by simpa only [Rat.neg_mul] using lip (x.compute n).lo r) n
  have hm := Rat.mul_le_mul_of_nonneg_left (show qabs (r-(x.compute n).lo)≤(x.compute n).width by
    rw [qabs_eq_self_of_nonneg (show 0≤r-(x.compute n).lo by grind only)]
    unfold QInterval.width
    grind only) hL
  constructor
  · intro i j
    have hh := h.1 i j
    change ((f (x.compute n).lo).compute n).lo-L*(x.compute n).width≤((f r).compute j).hi
    change ((f (x.compute n).lo).compute n).lo-L*qabs (r-(x.compute n).lo)≤((f r).compute j).hi at hh
    grind only
  · intro i j
    have hh := h.2 i j
    change ((f r).compute i).lo≤((f (x.compute n).lo).compute n).hi+L*(x.compute n).width
    change ((f r).compute i).lo≤((f (x.compute n).lo).compute n).hi+L*qabs (r-(x.compute n).lo) at hh
    grind only

theorem covers {f : Rat → RealCompute} {L : Rat} (hf : ∀ q, (f q).Valid)
    (hL : 0≤L) (lip : Lipschitz f L) {x : RealCompute} (hx : x.Valid) (n : Nat) {r : Rat}
    (hr : (x.compute n).lo≤r ∧ r≤(x.compute n).hi) : InInterval (f r) (interval f L x n) := by
  induction n with
  | zero => exact box_covers hf hL lip 0 hr
  | succ n ih =>
    have nest := hx.2.1 n (n+1) (by omega)
    have hp := ih ⟨Rat.le_trans nest.1 hr.1,Rat.le_trans hr.2 nest.2.2⟩
    have hb := box_covers hf hL lip (n+1) hr
    constructor
    · intro i j
      have h1 := hp.1 i j
      have h2 := hb.1 i j
      change (interval f L x n).lo≤((f r).compute j).hi at h1
      change (box f L x (n+1)).lo≤((f r).compute j).hi at h2
      change max (interval f L x n).lo (box f L x (n+1)).lo≤((f r).compute j).hi
      grind
    · intro i j
      have h1 := hp.2 i j
      have h2 := hb.2 i j
      change ((f r).compute i).lo≤(interval f L x n).hi at h1
      change ((f r).compute i).lo≤(box f L x (n+1)).hi at h2
      change ((f r).compute i).lo≤min (interval f L x n).hi (box f L x (n+1)).hi
      grind

private theorem current_contains (f : Rat → RealCompute) (L : Rat) (x : RealCompute) (n : Nat) :
    (box f L x n).ContainsInterval (interval f L x n) := by
  cases n with
  | zero => exact ⟨Rat.le_refl,Rat.le_refl⟩
  | succ n => exact QInterval.intersection_contained_right _ _

theorem valid {f : Rat → RealCompute} {L : Rat} (hf : ∀ q, (f q).Valid)
    (hL : 0≤L) (lip : Lipschitz f L) (w : Nat → Rat) (hw : ShrinksToZero w)
    (widths : ∀ q n, ((f q).compute n).width≤w n) {x : RealCompute} (hx : x.Valid) :
    (extend f L x).Valid := by
  have ordered (n : Nat) : (interval f L x n).lo≤(interval f L x n).hi := by
    have ho := RealCompute.interval_order_of_valid _ hx n
    have hc := covers hf hL lip hx n ⟨Rat.le_refl,ho⟩
    exact RealCompute.le_trans (x := RealCompute.ofRat (interval f L x n).lo)
      (z := RealCompute.ofRat (interval f L x n).hi) (hf (x.compute n).lo) hc.1 hc.2 0 0
  refine ⟨fun n => by
    change 0≤(interval f L x n).hi-(interval f L x n).lo
    have := ordered n
    grind only,?_,?_⟩
  · intro n m hnm
    change (interval f L x n).lo≤(interval f L x m).lo ∧
      (interval f L x m).lo≤(interval f L x m).hi ∧ (interval f L x m).hi≤(interval f L x n).hi
    induction hnm with
    | refl => exact ⟨Rat.le_refl,ordered n,Rat.le_refl⟩
    | @step m hnm ih =>
      have hs := QInterval.intersection_contained_left (interval f L x m) (box f L x (m+1))
      exact ⟨Rat.le_trans ih.1 hs.1,ordered (m+1),Rat.le_trans hs.2 ih.2.2⟩
  · intro eps
    let small : QPos := ⟨eps.val/(4*(L+1)),by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by grind only))⟩
    obtain ⟨N,hN⟩ := hx.2.2 small
    obtain ⟨M,hM⟩ := hw ⟨eps.val/2,by have := eps.property; grind only⟩
    refine ⟨max N M,fun n hn => ?_⟩
    have hi := hN n (by omega)
    have hs := hM n (by omega)
    have hc := current_contains f L x n
    have hfwidth := widths (x.compute n).lo n
    have hm := Rat.mul_le_mul_of_nonneg_left hi (show 0≤2*L by grind only)
    have he : small.val*(4*(L+1))=eps.val := by
      dsimp [small]
      exact Rat.div_mul_cancel (by grind only : 4*(L+1)≠0)
    have hp := small.property
    have hb : 2*L*small.val≤eps.val/2 := by grind only
    have hm' := Rat.le_trans hm hb
    change w n≤eps.val/2 at hs
    unfold QInterval.ContainsInterval box QInterval.expand QInterval.width at hc
    dsimp only at hc
    unfold QInterval.width at hfwidth
    unfold QInterval.width at hm'
    change (interval f L x n).hi-(interval f L x n).lo≤eps.val
    grind only

theorem congr {f : Rat → RealCompute} {L : Rat} (hf : ∀ q, (f q).Valid)
    (hL : 0≤L) (lip : Lipschitz f L) {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (he : x.Equiv y) : (extend f L x).Equiv (extend f L y) := by
  intro n
  have ho := (RealCompute.compareAt_overlap_iff _ _ n n).mp (he n)
  unfold QInterval.Overlaps at ho
  have hxo := RealCompute.interval_order_of_valid _ hx n
  have hyo := RealCompute.interval_order_of_valid _ hy n
  let r := max (x.compute n).lo (y.compute n).lo
  have hrx : (x.compute n).lo≤r ∧ r≤(x.compute n).hi := by dsimp [r]; grind
  have hry : (y.compute n).lo≤r ∧ r≤(y.compute n).hi := by dsimp [r]; grind
  have hc := covers hf hL lip hx n hrx
  have hd := covers hf hL lip hy n hry
  apply (RealCompute.compareAt_overlap_iff _ _ n n).mpr
  exact ⟨RealCompute.le_trans (hf r) hc.1 hd.2 0 0,RealCompute.le_trans (hf r) hd.1 hc.2 0 0⟩

theorem rational_agreement {f : Rat → RealCompute} {L : Rat} (hf : ∀ q, (f q).Valid)
    (hL : 0≤L) (lip : Lipschitz f L) (q : Rat) : (extend f L (RealCompute.ofRat q)).Equiv (f q) := by
  intro n
  exact (RealCompute.compareAt_overlap_iff _ _ n n).mpr
    ⟨(covers hf hL lip (x := RealCompute.ofRat q) (RealCompute.ofRat_valid q) n ⟨Rat.le_refl,Rat.le_refl⟩).1 0 n,
     (covers hf hL lip (x := RealCompute.ofRat q) (RealCompute.ofRat_valid q) n ⟨Rat.le_refl,Rat.le_refl⟩).2 n 0⟩

theorem period_compute (f : Rat → RealCompute) (L T : Rat)
    (period : ∀ q, f (q+T)=f q) (x : RealCompute) (n : Nat) :
    (extend f L (x+RealCompute.ofRat T)).compute n=(extend f L x).compute n := by
  have box_eq (n : Nat) : box f L (x+RealCompute.ofRat T) n=box f L x n := by
    unfold box
    change QInterval.expand ((f ((x.compute n).lo+T)).compute n)
      (L*(((x.compute n).hi+T)-((x.compute n).lo+T)))=_
    rw [period]
    have he : ((x.compute n).hi+T)-((x.compute n).lo+T)=(x.compute n).width := by
      unfold QInterval.width
      grind only
    rw [he]
  change interval f L (x+RealCompute.ofRat T) n=interval f L x n
  induction n with
  | zero => exact box_eq 0
  | succ n ih => simp only [interval,ih,box_eq]

end ComputableAnalysis.LipschitzRealExtension


