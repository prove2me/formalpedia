-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealReciprocal
-- name    : liuyao_ca_fd889115_k1_Analysis_RealReciprocal
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:57:04.564931+00:00
-- url     : https://prove2.me/theorems/f22c0130-e811-4dc7-89e9-14ad54b964df
-- title:
--   Computable analysis · RealReciprocal · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/RealReciprocal.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PositiveReciprocal
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Numbers

set_option autoImplicit true

/-! A signed reciprocal on the genuine nonzero domain. The first separated
input interval is found by executable search; proof-only existence establishes
termination. No sign test or equality decision on real values is performed. -/
namespace ComputableAnalysis.CertifiedReciprocal

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

private def next (p : Nat → Prop) (m n : Nat) : Prop := m=n+1 ∧ ¬p n

private theorem accessible (p : Nat → Prop) (d n : Nat) (h : p (n+d)) :
    Acc (next p) n := by
  induction d generalizing n with
  | zero =>
    apply Acc.intro
    intro m hm
    exact False.elim (hm.2 (by simpa using h))
  | succ d ih =>
    apply Acc.intro
    intro m hm
    rcases hm with ⟨rfl,_⟩
    apply ih
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

private def searchFrom (p : Nat → Prop) [DecidablePred p] (n : Nat)
    (h : Acc (next p) n) : {k // p k} :=
  Acc.rec (motive := fun _ _ => {k // p k})
    (fun n _ recurse => if hn : p n then ⟨n,hn⟩ else recurse (n+1) ⟨rfl,hn⟩) h

private theorem searchFrom_le (p : Nat → Prop) [DecidablePred p] (n : Nat)
    (h : Acc (next p) n) (m : Nat) (hnm : n ≤ m) (hm : p m) :
    (searchFrom p n h).val ≤ m := by
  induction h generalizing m with
  | intro n children ih =>
    dsimp [searchFrom]
    split
    · exact hnm
    · apply ih (n+1) ⟨rfl,‹¬p n›⟩ m
      · by_cases h : n=m
        · subst m; contradiction
        · omega
      · exact hm

private theorem searchAccessible (p : Nat → Prop) (h : ∃ n,p n) : Acc (next p) 0 := by
  obtain ⟨n,hn⟩ := h
  exact accessible p n 0 (by simpa using hn)

private def first (p : Nat → Prop) [DecidablePred p] (h : ∃ n,p n) : {n // p n} :=
  searchFrom p 0 (searchAccessible p h)

private theorem first_le (p : Nat → Prop) [DecidablePred p] (h : ∃ n,p n)
    (m : Nat) (hm : p m) : (first p h).val ≤ m :=
  searchFrom_le p 0 (searchAccessible p h) m (Nat.zero_le m) hm

private theorem first_agrees (p q : Nat → Prop) [DecidablePred p] [DecidablePred q]
    (hp : ∃ n,p n) (hq : ∃ n,q n)
    (h : ∀ j,j ≤ (first p hp).val → (p j ↔ q j)) :
    (first p hp).val = (first q hq).val := by
  have hqle := first_le q hq _ ((h _ (Nat.le_refl _)).mp (first p hp).property)
  have hple := first_le p hp _ ((h _ hqle).mpr (first q hq).property)
  exact Nat.le_antisymm hple hqle

def Nonzero (x : RealCompute) : Prop := ¬x.Equiv (RealCompute.ofRat 0)

def Separated (x : RealCompute) (n : Nat) : Prop :=
  0 < (x.compute n).lo ∨ (x.compute n).hi < 0

instance (x : RealCompute) : DecidablePred (Separated x) := fun n => inferInstanceAs
  (Decidable (0 < (x.compute n).lo ∨ (x.compute n).hi < 0))

theorem nonzero_of_separated (x : RealCompute) (n : Nat) (h : Separated x n) : Nonzero x := by
  intro heq
  have ho := (RealCompute.compareAt_overlap_iff _ _ n n).mp (heq n)
  change (x.compute n).lo ≤ 0 ∧ 0 ≤ (x.compute n).hi at ho
  dsimp [Separated] at h
  grind

theorem exists_separated (x : RealCompute) (h : Nonzero x) : ∃ n,Separated x n := by
  by_cases hex : ∃ n,Separated x n
  · exact hex
  · exfalso
    apply h
    apply RealCompute.sameStageOverlap_equiv
    intro n
    apply (RealCompute.compareAt_overlap_iff _ _ n n).mpr
    have hn : ¬Separated x n := fun hn => hex ⟨n,hn⟩
    change (x.compute n).lo ≤ 0 ∧ 0 ≤ (x.compute n).hi
    dsimp [Separated] at hn
    grind

def pivot (x : RealCompute) (h : Nonzero x) : Nat := (first (Separated x) (exists_separated x h)).val

theorem pivot_spec (x : RealCompute) (h : Nonzero x) : Separated x (pivot x h) :=
  (first (Separated x) (exists_separated x h)).property

theorem pivot_congr {x z : RealCompute} (hx : Nonzero x) (hz : Nonzero z)
    (h : ∀ j,j ≤ pivot x hx → x.compute j=z.compute j) : pivot x hx=pivot z hz := by
  apply first_agrees
  intro j hj
  change (0 < (x.compute j).lo ∨ (x.compute j).hi < 0) ↔
    (0 < (z.compute j).lo ∨ (z.compute j).hi < 0)
  rw [h j hj]

def reciprocal (x : RealCompute) (h : Nonzero x) : RealCompute :=
  if 0 < (x.compute (pivot x h)).lo then
    x.positiveReciprocal (x.compute (pivot x h)).lo
  else
    -((-x).positiveReciprocal (-(x.compute (pivot x h)).hi))

theorem reciprocal_valid (x : RealCompute) (hx : x.Valid) (hnz : Nonzero x) :
    (reciprocal x hnz).Valid := by
  have hp := pivot_spec x hnz
  unfold reciprocal
  split
  · apply RealCompute.positiveReciprocal_valid x _ hx ‹_›
    intro n
    exact RealCompute.le_refl x hx (pivot x hnz) n
  · apply RealCompute.neg_valid
    apply RealCompute.positiveReciprocal_valid (-x) _ (RealCompute.neg_valid hx)
    · dsimp [Separated] at hp
      grind
    · intro n
      have hle := RealCompute.le_refl x hx n (pivot x hnz)
      change -(x.compute (pivot x hnz)).hi ≤ -(x.compute n).lo
      grind

private theorem inv_antitone_pos {a b : Rat} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have hb : 0 < b := by grind
  have ia := Rat.le_of_lt (Rat.inv_pos.mpr ha)
  have ib := Rat.le_of_lt (Rat.inv_pos.mpr hb)
  have hm := Rat.mul_le_mul_of_nonneg_left hab (Rat.mul_nonneg ia ib)
  have ca := Rat.mul_inv_cancel a (by grind : a≠0)
  have cb := Rat.mul_inv_cancel b (by grind : b≠0)
  have ea : a⁻¹*b⁻¹*a=b⁻¹ := by
    calc
      _ = (a*a⁻¹)*b⁻¹ := by grind
      _ = b⁻¹ := by rw [ca,Rat.one_mul]
  have eb : a⁻¹*b⁻¹*b=a⁻¹ := by
    calc
      _ = (b*b⁻¹)*a⁻¹ := by grind
      _ = a⁻¹ := by rw [cb,Rat.one_mul]
  simpa only [ea,eb] using hm

private theorem positive_congr (x z : RealCompute) (hx : x.Valid) (hz : z.Valid)
    (a b : Rat) (ha : 0<a) (hb : 0<b)
    (hax : ∀n,a ≤ (x.compute n).hi) (hbz : ∀n,b ≤ (z.compute n).hi)
    (heq : x.Equiv z) : (x.positiveReciprocal a).Equiv (z.positiveReciprocal b) := by
  have hxz := RealCompute.le_of_equiv hx hz heq
  have hzx := RealCompute.le_of_equiv hz hx (RealCompute.equiv_symm heq)
  have haz := RealCompute.le_trans hx (show (RealCompute.ofRat a).Le x from fun _ n => hax n) hxz
  have hbx := RealCompute.le_trans hz (show (RealCompute.ofRat b).Le z from fun _ n => hbz n) hzx
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).mpr
  rw [RealCompute.positiveReciprocal_compute x a ha n,RealCompute.positiveReciprocal_compute z b hb n]
  have hxzn := hxz n n
  have hzxn := hzx n n
  have hazn := haz 0 n
  have hbxn := hbx 0 n
  change a ≤ (z.compute n).hi at hazn
  change b ≤ (x.compute n).hi at hbxn
  have hla : 0 < maxRat2 (x.compute n).lo a := by dsimp [maxRat2]; split <;> grind
  have hlb : 0 < maxRat2 (z.compute n).lo b := by dsimp [maxRat2]; split <;> grind
  have hba : maxRat2 (z.compute n).lo b ≤ (x.compute n).hi := by
    dsimp [maxRat2]; split <;> grind
  have hab : maxRat2 (x.compute n).lo a ≤ (z.compute n).hi := by
    dsimp [maxRat2]; split <;> grind
  exact ⟨by simpa [Rat.div_def] using inv_antitone_pos hlb hba,
    by simpa [Rat.div_def] using inv_antitone_pos hla hab⟩

/-- Positive reciprocal computations agree across valid equivalent names and
different certified positive lower bounds. -/
theorem positiveReciprocal_congr (x z : RealCompute) (hx : x.Valid) (hz : z.Valid)
    (a b : Rat) (ha : 0<a) (hb : 0<b)
    (hax : ∀ n,a≤(x.compute n).hi) (hbz : ∀ n,b≤(z.compute n).hi)
    (heq : x.Equiv z) : (x.positiveReciprocal a).Equiv (z.positiveReciprocal b) :=
  positive_congr x z hx hz a b ha hb hax hbz heq

theorem reciprocal_congr (x z : RealCompute) (hx : x.Valid) (hz : z.Valid)
    (hnx : Nonzero x) (hnz : Nonzero z) (heq : x.Equiv z) :
    (reciprocal x hnx).Equiv (reciprocal z hnz) := by
  have hp := pivot_spec x hnx
  have hq := pivot_spec z hnz
  have hxz := RealCompute.le_of_equiv hx hz heq
  have hzx := RealCompute.le_of_equiv hz hx (RealCompute.equiv_symm heq)
  unfold reciprocal
  split <;> split
  · apply positive_congr x z hx hz _ _ ‹_› ‹_›
    · intro n; exact RealCompute.le_refl x hx (pivot x hnx) n
    · intro n; exact RealCompute.le_refl z hz (pivot z hnz) n
    · exact heq
  · have h := hxz (pivot x hnx) (pivot z hnz)
    dsimp [Separated] at hq
    grind
  · have h := hzx (pivot z hnz) (pivot x hnx)
    dsimp [Separated] at hp
    grind
  · apply RealCompute.neg_equiv
    apply positive_congr (-x) (-z) (RealCompute.neg_valid hx) (RealCompute.neg_valid hz)
      _ _ (by dsimp [Separated] at hp; grind) (by dsimp [Separated] at hq; grind)
    · intro n
      have h := RealCompute.le_refl x hx n (pivot x hnx)
      change -(x.compute (pivot x hnx)).hi ≤ -(x.compute n).lo
      grind
    · intro n
      have h := RealCompute.le_refl z hz n (pivot z hnz)
      change -(z.compute (pivot z hnz)).hi ≤ -(z.compute n).lo
      grind
    · exact RealCompute.neg_equiv heq

private def reciprocalBox (P I : QInterval) : QInterval :=
  if 0 < P.lo then ⟨1/I.hi,1/maxRat2 I.lo P.lo⟩
  else ⟨-(1/maxRat2 (-I.hi) (-P.hi)),-(1/(-I.lo))⟩

theorem reciprocal_compute (x : RealCompute) (h : Nonzero x) (n : Nat) :
    (reciprocal x h).compute n = reciprocalBox (x.compute (pivot x h)) (x.compute n) := by
  have hp := pivot_spec x h
  unfold reciprocal reciprocalBox
  split
  · rw [RealCompute.positiveReciprocal_compute x _ ‹_› n]
  · have hlo : 0 < -(x.compute (pivot x h)).hi := by dsimp [Separated] at hp; grind
    change (⟨-(((-x).positiveReciprocal _).compute n).hi,
      -(((-x).positiveReciprocal _).compute n).lo⟩ : QInterval) = _
    rw [RealCompute.positiveReciprocal_compute (-x) _ hlo n]
    rfl

/-- A reciprocal output interval uses a finite prefix of its denominator name. -/
theorem reciprocal_compute_congr (x z : RealCompute) (hx : Nonzero x) (hz : Nonzero z) (n : Nat)
    (h : ∀ j,j ≤ max (pivot x hx) n → x.compute j=z.compute j) :
    (reciprocal x hx).compute n = (reciprocal z hz).compute n := by
  have hp := pivot_congr hx hz (fun j hj => h j (Nat.le_trans hj (Nat.le_max_left _ _)))
  rw [reciprocal_compute x hx n,reciprocal_compute z hz n,← hp,
    h _ (Nat.le_max_left _ _),h _ (Nat.le_max_right _ _)]

theorem mul_reciprocal (x : RealCompute) (hx : x.Valid) (hnz : Nonzero x) :
    (x*reciprocal x hnz).Equiv (RealCompute.ofRat 1) := by
  have hp := pivot_spec x hnz
  have hr := reciprocal_valid x hx hnz
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).mpr
  have ho := RealCompute.interval_order_of_valid x hx n
  have hro := RealCompute.interval_order_of_valid _ hr n
  change (QBox.mulRealInterval (x.compute n).lo (x.compute n).hi
    ((reciprocal x hnz).compute n).lo ((reciprocal x hnz).compute n).hi).Overlaps ⟨1,1⟩
  rw [reciprocal_compute] at hro ⊢
  dsimp [reciprocalBox] at hro ⊢
  by_cases hsign : 0 < (x.compute (pivot x hnz)).lo
  · simp only [if_pos hsign] at hro ⊢
    have hbound := RealCompute.le_refl x hx (pivot x hnz) n
    have hn : (x.compute n).hi ≠ 0 := by grind
    have hc := Rat.mul_inv_cancel (x.compute n).hi hn
    have hc' := QBox.mulRealInterval_contains ho Rat.le_refl Rat.le_refl hro
    change (QBox.mulRealInterval (x.compute n).lo (x.compute n).hi
      (1/(x.compute n).hi) (1/maxRat2 (x.compute n).lo (x.compute (pivot x hnz)).lo)).Overlaps
      ⟨1,1⟩
    simpa only [QInterval.Overlaps,Rat.div_def,Rat.one_mul,hc] using hc'
  · simp only [if_neg hsign] at hro ⊢
    have hbound := RealCompute.le_refl x hx n (pivot x hnz)
    have hn : -(x.compute n).lo ≠ 0 := by dsimp [Separated] at hp; grind
    have hc := Rat.mul_inv_cancel (-(x.compute n).lo) hn
    have hc' := QBox.mulRealInterval_contains Rat.le_refl ho hro Rat.le_refl
    change (QBox.mulRealInterval (x.compute n).lo (x.compute n).hi
      (-(1/maxRat2 (-(x.compute n).hi) (-(x.compute (pivot x hnz)).hi)))
      (-(1/(-(x.compute n).lo)))).Overlaps ⟨1,1⟩
    have hprod : (x.compute n).lo * (-(1/(-(x.compute n).lo))) = 1 := by
      dsimp [Rat.div_def]; grind
    simpa only [hprod,QInterval.Overlaps] using hc'

end ComputableAnalysis.CertifiedReciprocal


