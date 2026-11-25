-- Prove2me | Definitions.Def_DetDLP_W3_FpSlotBits
-- name    : DetDLP_W3_FpSlotBits
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:02:33.5798+00:00
-- url     : https://prove2.me/theorems/d4984448-648d-4b6e-844f-2d2f3fb2e776
-- title:
--   Bit-level witnesses for a finite-field hash slot
-- statement:
--   Ripple carries, multiplier incidences, and an OR scan give each accepting finite-field hash slot a unique bit-level witness.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_W3_FpNativeCert
import Definitions.Def_DetDLP_W3_FpCarryPins
import Definitions.Def_DetDLP_W3_FpMulIncidence

set_option autoImplicit false
namespace DetDLP

/-- Sound on every witness, with exactly one extension of each accepting input. -/
def w3_slotLift {A : Type} (P : Prop) (Q : A → Prop) := (∀ a, Q a → P) ∧ (P → ∃! a, Q a)

theorem w3_slotLiftProd {A B : Type} {P R : Prop} {Q : A → Prop} {S : B → Prop}
    (h : w3_slotLift P Q) (k : w3_slotLift R S) :
    w3_slotLift (P ∧ R) (fun w : A × B => Q w.1 ∧ S w.2) := by
  refine ⟨fun w hw => ⟨h.1 _ hw.1,k.1 _ hw.2⟩,?_⟩
  rintro ⟨hp,hr⟩; obtain ⟨a,ha,ua⟩ := h.2 hp; obtain ⟨b,hb,ub⟩ := k.2 hr
  exact ⟨(a,b),⟨ha,hb⟩,fun w hw => Prod.ext (ua _ hw.1) (ub _ hw.2)⟩

/-- Low-to-high OR scan. The boundary pins the outgoing prefix to true. -/
def w3_slotOr : (d : ℕ) → ℕ → Bool → (Fin d → Bool) → Prop
  | 0, _, b, _ => b = true
  | d+1, u, b, t => t 0 = (b || decide (u%2 = 1)) ∧
    w3_slotOr d (u/2) (t 0) (fun i => t i.succ)

theorem w3_slotOr_spec {d u : ℕ} (b : Bool) (hu : u < 2^d) :
    w3_slotLift (b = true ∨ u ≠ 0) (w3_slotOr d u b) := by
  induction d generalizing b u with
  | zero =>
    have hz : u = 0 := by simpa using hu
    subst u; exact ⟨fun _ h => Or.inl h, fun h =>
      ⟨Fin.elim0,h.resolve_right (not_not_intro rfl),fun _ _ => Subsingleton.elim ..⟩⟩
  | succ d ih =>
    rw [pow_succ] at hu
    let v := b || decide (u%2 = 1)
    have he : (v = true ∨ u/2 ≠ 0) ↔ (b = true ∨ u ≠ 0) := by
      simp only [v, Bool.or_eq_true, decide_eq_true_eq]
      by_cases h : b = true <;> simp [h] <;> omega
    have ht := ih v (by omega : u/2 < 2^d)
    refine ⟨?_,?_⟩
    · rintro t ⟨h0,hs⟩; change t 0 = v at h0; rw [h0] at hs; exact he.mp (ht.1 _ hs)
    · intro h; obtain ⟨t,hs,us⟩ := ht.2 (he.mpr h)
      refine ⟨Fin.cons v t,⟨by simp [v],by simpa only [Fin.cons_zero,Fin.cons_succ] using hs⟩,?_⟩
      rintro s ⟨h0,hr⟩; change s 0 = v at h0; rw [h0] at hr
      have hh := us _ hr
      funext i; cases i using Fin.cases with
      | zero => simpa using h0
      | succ i => simpa using congrFun hh i

abbrev w3_slotDiff (d : ℕ) := Fin (2^d) × (Fin (d+1) → Bool)

def w3_slotLt (d u B : ℕ) (r : w3_slotDiff d) := w3_addColumns (d+1) u r.1.val B true r.2

theorem w3_slotLt_spec {d u B : ℕ} (hu : u < 2^d) (hB : B ≤ 2^d) :
    w3_slotLift (u < B) (w3_slotLt d u B) := by
  have hw : 2^d < 2^(d+1) := by rw [pow_succ]; have := Nat.two_pow_pos d; omega
  have calcEq (r : w3_slotDiff d) (h : w3_slotLt d u B r) : u+r.1.val+1 = B :=
    w3_addColumns_sound (hu.trans hw) (r.1.isLt.trans hw) (hB.trans_lt hw) h
  refine ⟨fun r h => by have := calcEq r h; omega,?_⟩
  intro h; let v : Fin (2^d) := ⟨B-1-u,by omega⟩
  obtain ⟨t,ht,ut⟩ := w3_addColumns_unique (hu.trans hw) (v.isLt.trans hw) (hB.trans_lt hw)
    (cin := true) (by change u+(B-1-u)+1 = B; omega)
  refine ⟨(v,t),ht,?_⟩; rintro ⟨a,c⟩ hc
  have he := calcEq (a,c) hc
  have hav : a = v := Fin.ext (by change u+a.val+1 = B at he; change a.val = B-1-u; omega)
  subst a; exact Prod.ext rfl (ut c hc)

abbrev w3_slotMulInc {d : ℕ} (hd : 1 ≤ d) (x y : ℕ) (r : w3_mulRun d hd) :=
  (∀ i, r.2 (w4_M5PortTensor.ext hd i) = w3_mulBus d x y r.1.val i) ∧
    ∀ g, w3_fpMulTests d hd g (fun e => r.2 ((w3_fpMulLayout d hd).bit e.1)) = true

abbrev w3_slotHashAux (d : ℕ) := (Fin (2*d) → Bool) × Fin (2^(d+1)) ×
    (Fin (d+1) → Bool) × (Fin (d+1) → Bool)

def w3_slotHashBits {d p : ℕ} (hd : 1 ≤ d) (a b x z : ℕ) (r : w3_fpHashCert d p hd)
    (w : w3_slotHashAux d) :=
  let m := r.1.2
  (w3_slotMulInc hd a x m.2.1 ∧ w3_slotMulInc hd m.1.val p m.2.2 ∧
    w3_addColumns (2*d) m.2.2.1.val r.1.1.val m.2.1.1.val false w.1) ∧
  w3_addColumns (d+1) r.1.1.val b w.2.1.val false w.2.2.1 ∧
  w3_addColumns (d+1) z (if r.2 then p else 0) w.2.1.val false w.2.2.2

theorem w3_slotHash_spec {d p a b x z : ℕ} (hd : 1 ≤ d) (hp : p < 2^d) (hb : b < p)
    (hz : z < p) (r : w3_fpHashCert d p hd) :
    w3_slotLift (w3_fpHashCheck hd a b x z r) (w3_slotHashBits hd a b x z r) := by
  have hw : 2^d ≤ 2^(d+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hu := r.1.1.isLt
  have h2 : r.1.1.val < 2^(2*d) := lt_of_lt_of_le (hu.trans hp) (Nat.pow_le_pow_right (by decide) (by omega))
  have hc : (if r.2 then p else 0) < 2^(d+1) := by split <;> omega
  have hm := w3_addColumns_modTwo hd h2 r.1.2 (p := p) (x := a) (y := x)
  rw [w3_fpMulPins_inc hd a x,w3_fpMulPins_inc hd r.1.2.1.val p] at hm
  refine ⟨?_,?_⟩
  · rintro ⟨c,s,l,t⟩ ⟨⟨h1,hp',h3⟩,hl,ht⟩
    have he := w3_addColumns_sound r.1.2.2.2.1.isLt h2 r.1.2.2.1.1.isLt h3
    have leq := w3_addColumns_sound ((hu.trans hp).trans_le hw) ((hb.trans hp).trans_le hw) s.isLt hl
    have req := w3_addColumns_sound ((hz.trans hp).trans_le hw) hc s.isLt ht
    exact ⟨hm.mpr ⟨h1,hp',w3_addColumns_unique r.1.2.2.2.1.isLt h2 r.1.2.2.1.1.isLt he⟩,by simpa using leq.trans req.symm⟩
  · rintro ⟨hm',he⟩; obtain ⟨h1,hp',c,hc',uc⟩ := hm.mp hm'
    let s : Fin (2^(d+1)) := ⟨r.1.1.val+b,by rw [pow_succ]; omega⟩
    obtain ⟨l,hl,ul⟩ := w3_addColumns_unique ((hu.trans hp).trans_le hw) ((hb.trans hp).trans_le hw) s.isLt (cin := false) (by simp [s])
    obtain ⟨t,ht,ut⟩ := w3_addColumns_unique ((hz.trans hp).trans_le hw) hc s.isLt (cin := false) (by simpa [s] using he.symm)
    refine ⟨(c,s,l,t),⟨⟨h1,hp',hc'⟩,hl,ht⟩,?_⟩
    rintro ⟨e,v,j,k⟩ ⟨⟨_,_,hh⟩,hj,hk⟩
    have hv : v = s := Fin.ext (by simpa [s] using (w3_addColumns_sound ((hu.trans hp).trans_le hw) ((hb.trans hp).trans_le hw) v.isLt hj).symm)
    subst v; exact Prod.ext (uc e hh) (Prod.ext rfl (Prod.ext (ul j hj) (ut k hk)))

/-- The last comparison uses the larger word width, without assuming `k ≤ d`. -/
abbrev w3_fpSlotAux (d k : ℕ) := ((Fin d → Bool) × w3_slotDiff d ×
    w3_slotDiff k × w3_slotDiff (max d k)) × w3_slotHashAux d

def w3_fpSlotWordBits {d p m k : ℕ} (hd : 1 ≤ d) (seed : FpSeed p m) (i : Fin m) (T x : ℕ)
    (z : Fin (2^k)) (r : w3_fpHashCert d p hd) (w : w3_fpSlotAux d k) :=
  (w3_slotOr d x false w.1.1 ∧ w3_slotLt d x p w.1.2.1 ∧
    w3_slotLt k z.val T w.1.2.2.1 ∧ w3_slotLt (max d k) z.val p w.1.2.2.2) ∧
  w3_slotHashBits hd ((seed i).1.val+1) (seed i).2.val x z.val r w.2

abbrev w3_fpSlotBits {d p m k : ℕ} (hd : 1 ≤ d) (seed : FpSeed p m) (i : Fin m) (T : ℕ)
    (s : w3_fpRawSlot d p k hd) := w3_fpSlotWordBits hd seed i T s.1.val s.2.1 s.2.2

theorem w3_fpSlotBits_spec {d p m k : ℕ} (hd : 1 ≤ d) (hp : p < 2^d) (seed : FpSeed p m)
    (i : Fin m) (T : ℕ) (hT : T ≤ 2^k) (s : w3_fpRawSlot d p k hd) :
    w3_slotLift (w3_fpSlotCheck hd seed i T s) (w3_fpSlotBits hd seed i T s) := by
  have hx := s.1.isLt.trans hp
  have ho := w3_slotOr_spec false hx
  simp only [Bool.false_eq_true,false_or] at ho
  have hd' : 2^d ≤ 2^(max d k) := Nat.pow_le_pow_right (by decide) (le_max_left ..)
  have hk' : 2^k ≤ 2^(max d k) := Nat.pow_le_pow_right (by decide) (le_max_right ..)
  have R := w3_slotLiftProd ho (w3_slotLiftProd (w3_slotLt_spec hx hp.le)
    (w3_slotLiftProd (w3_slotLt_spec s.2.1.isLt hT) (w3_slotLt_spec (s.2.1.isLt.trans_le hk') (hp.le.trans hd'))))
  have H (hz : s.2.1.val < p) := w3_slotHash_spec (a := (seed i).1.val+1) (x := s.1.val)
    hd hp (seed i).2.isLt hz s.2.2
  constructor
  · rintro w ⟨hr,hh⟩; obtain ⟨hn,_,ht,hz⟩ := R.1 _ hr
    exact ⟨hn,ht,hz,(H hz).1 _ hh⟩
  · rintro ⟨hn,ht,hz,hh⟩; exact (w3_slotLiftProd R (H hz)).2 ⟨⟨hn,s.1.isLt,ht,hz⟩,hh⟩

noncomputable def w3_fpSlotBitsEquiv {d p m k : ℕ} (hd : 1 ≤ d) (hp : p < 2^d)
    (seed : FpSeed p m) (i : Fin m) (T : ℕ) (hT : T ≤ 2^k) :
    {t : w3_fpRawSlot d p k hd × w3_fpSlotAux d k // w3_fpSlotBits hd seed i T t.1 t.2} ≃
      {s // w3_fpSlotCheck (k := k) hd seed i T s} := by
  let H := w3_fpSlotBits_spec hd hp seed i T hT (k := k)
  apply Equiv.ofBijective (fun t => ⟨t.1.1,(H _).1 _ t.2⟩)
  constructor
  · rintro ⟨⟨s,u⟩,hu⟩ ⟨⟨t,v⟩,hv⟩ he
    have eq : s = t := congrArg Subtype.val he
    subst t; exact Subtype.ext (Prod.ext rfl (((H s).2 ((H s).1 u hu)).unique hu hv))
  · rintro ⟨s,hs⟩; obtain ⟨w,hw,_⟩ := (H s).2 hs; exact ⟨⟨(s,w),hw⟩,rfl⟩

/-- The input domain is all d-bit words, including non-residues. Decoding obtains the
    `Fin p` bound from the difference and its column constraints. -/
noncomputable def w3_fpSlotWordEquiv {d p m k : ℕ} (hd : 1 ≤ d) (hp : p < 2^d)
    (seed : FpSeed p m) (i : Fin m) (T : ℕ) (hT : T ≤ 2^k) :
    {t : (Fin (2^d) × Fin (2^k) × w3_fpHashCert d p hd) × w3_fpSlotAux d k //
      w3_fpSlotWordBits hd seed i T t.1.1.val t.1.2.1 t.1.2.2 t.2} ≃
    {s // w3_fpSlotCheck (k := k) hd seed i T s} := by
  apply Equiv.trans _ (w3_fpSlotBitsEquiv hd hp seed i T hT)
  exact {
    toFun := fun t => ⟨((⟨t.1.1.1.val,(w3_slotLt_spec t.1.1.1.isLt hp.le).1 _ t.2.1.2.1⟩,t.1.1.2),t.1.2),t.2⟩
    invFun := fun t => ⟨((⟨t.1.1.1.val,t.1.1.1.isLt.trans hp⟩,t.1.1.2),t.1.2),t.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end DetDLP


