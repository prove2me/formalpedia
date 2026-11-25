-- Prove2me | Definitions.Def_DetDLP_S8J_HashGateLayout
-- name    : DetDLP_S8J_HashGateLayout
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:30:37.912794+00:00
-- url     : https://prove2.me/theorems/f437d74e-2ea6-490f-bdfd-0784ec47fb1e
-- title:
--   Sum layouts and wired hash-check components
-- statement:
--   Combines factor layouts by disjoint sum and supplies wired multiplier and ripple-adder checks with component-degree bounds and hash-slot witness relations.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_W3_FpSlotBits
import Definitions.Def_DetDLP_S8C_AddSound

set_option autoImplicit false
namespace DetDLP.S8J

attribute [-simp] Fin.natAdd_eq_addNat
def splitMap {m n u v : ℕ} (f : Fin m → Fin u) (g : Fin n → Fin v) : Fin (m+n) → Fin (u+v) :=
  Fin.addCases (Fin.castAdd v ∘ f) (Fin.natAdd u ∘ g)

def join (A B : w3_FactorLayout) : w3_FactorLayout where
  ng := A.ng+B.ng
  nb := A.nb+B.nb
  ne := A.ne+B.ne
  gate := splitMap A.gate B.gate
  bit := splitMap A.bit B.bit
  rep := splitMap A.rep B.rep
  rep_bit i := by induction i using Fin.addCases <;> simp [splitMap,A.rep_bit,B.rep_bit]

abbrev Accept (A : w3_FactorLayout) (t : w3_factorTest A) (x : Fin A.nb → Bool) :=
  ∀ g, t g (fun e => x (A.bit e.1)) = true

def joinTest {A B : w3_FactorLayout} (s : w3_factorTest A) (t : w3_factorTest B) :
    w3_factorTest (join A B) := Fin.addCases
  (fun g x => s g fun e => x ⟨Fin.castAdd _ e.1, by simp [join,splitMap,e.2]⟩)
  (fun g x => t g fun e => x ⟨Fin.natAdd _ e.1, by simp [join,splitMap,e.2]⟩)

theorem join_iff {A B : w3_FactorLayout} (s : w3_factorTest A) (t : w3_factorTest B)
    (x : Fin (A.nb+B.nb) → Bool) : Accept _ (joinTest s t) x ↔
      Accept A s (x ∘ Fin.castAdd B.nb) ∧ Accept B t (x ∘ Fin.natAdd A.nb) := by
  constructor
  · intro h
    exact ⟨fun g => by simpa [joinTest,join,splitMap] using h (Fin.castAdd B.ng g),
      fun g => by simpa [joinTest,join,splitMap] using h (Fin.natAdd A.ng g)⟩
  · rintro ⟨h,k⟩ i
    induction i using Fin.addCases with
    | left g => simpa [joinTest,join,splitMap] using h g
    | right g => simpa [joinTest,join,splitMap] using k g

def degreeOf {n m : ℕ} (f : Fin n → Fin m) (v : Fin m) :=
  ((List.finRange n).filter fun i => decide (f i = v)).length

private theorem ranges (n m : ℕ) : List.finRange (n+m) =
    (List.finRange n).map (Fin.castAdd m) ++ (List.finRange m).map (Fin.natAdd n) := by
  apply List.ext_getElem <;> simp
  case h =>
    intro i hi
    by_cases h : i < n
    · rw [List.getElem_append_left (by simpa using h)]; simp
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt h)]; apply Fin.ext; simp; omega

private theorem apart {n m : ℕ} (i : Fin n) (j : Fin m) : Fin.castAdd m i ≠ Fin.natAdd n j := by
  intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd,Fin.val_natAdd] at this; omega

@[simp] theorem degree_left {m n u v : ℕ} (f : Fin m → Fin u) (g : Fin n → Fin v) (i : Fin u) :
    degreeOf (splitMap f g) (Fin.castAdd v i) = degreeOf f i := by
  simp [degreeOf,ranges m n,List.filter_map,splitMap,Function.comp_def,apart,Ne.symm (apart _ _)]

@[simp] theorem degree_right {m n u v : ℕ} (f : Fin m → Fin u) (g : Fin n → Fin v) (i : Fin v) :
    degreeOf (splitMap f g) (Fin.natAdd u i) = degreeOf g i := by
  simp [degreeOf,ranges m n,List.filter_map,splitMap,Function.comp_def,apart]

def Shape (A : w3_FactorLayout) (D : ℝ) (B : ℕ) :=
  (∀ i, (degreeOf A.gate i : ℝ) < D) ∧ ∀ i, degreeOf A.bit i ≤ B

theorem join_shape {A B : w3_FactorLayout} {D : ℝ} {b : ℕ} (h : Shape A D b) (k : Shape B D b) :
    Shape (join A B) D b := by
  constructor <;> intro i <;> induction i using Fin.addCases <;>
    simp [join,h.1,h.2,k.1,k.2]

def links (A : w3_FactorLayout) {k : ℕ} (l r : Fin k → Fin A.nb) : w3_FactorLayout where
  ng := A.ng+k
  nb := A.nb
  ne := A.ne+(k+k)
  gate := splitMap A.gate (Fin.addCases id id)
  bit := Fin.addCases A.bit (Fin.addCases l r)
  rep := Fin.castAdd _ ∘ A.rep
  rep_bit i := by simp [A.rep_bit]

def linksTest {A : w3_FactorLayout} {k : ℕ} (l r : Fin k → Fin A.nb) (t : w3_factorTest A) :
    w3_factorTest (links A l r) := Fin.addCases
  (fun g x => t g (fun e => x ⟨Fin.castAdd _ e.1, by simp [links,splitMap,e.2]⟩))
  (fun i x => decide (x ⟨Fin.natAdd A.ne (Fin.castAdd k i),by simp [links,splitMap]⟩ =
    x ⟨Fin.natAdd A.ne (Fin.natAdd k i),by simp [links,splitMap]⟩))

theorem links_iff {A : w3_FactorLayout} {k : ℕ} (l r : Fin k → Fin A.nb) (t : w3_factorTest A)
    (x : Fin A.nb → Bool) : Accept _ (linksTest l r t) x ↔ Accept A t x ∧ ∀ i, x (l i) = x (r i) := by
  constructor
  · intro h; exact ⟨fun g => by simpa [linksTest,links] using h (Fin.castAdd k g),
      fun i => by simpa [linksTest,links] using h (Fin.natAdd A.ng i)⟩
  · rintro ⟨ht,hw⟩ g; induction g using Fin.addCases with
    | left g => simpa [linksTest,links] using ht g
    | right i => simpa [linksTest,links] using hw i

noncomputable def pinTest {A : w3_FactorLayout} (t : w3_factorTest A) (p : Fin A.nb → Option Bool) :
    w3_factorTest A := by
  classical exact fun g x => t g x && decide (∀ e, ∀ v, p (A.bit e.val) = some v → x e = v)

theorem pin_iff {A : w3_FactorLayout} (t : w3_factorTest A) (p : Fin A.nb → Option Bool)
    (x : Fin A.nb → Bool) : Accept A (pinTest t p) x ↔ Accept A t x ∧ ∀ b v, p b = some v → x b = v := by
  classical
  simp only [Accept,pinTest,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · intro h; refine ⟨fun g => (h g).1,fun b v hv => ?_⟩
    let e := A.rep b
    have H := (h (A.gate e)).2 ⟨e,rfl⟩ v
    simpa only [e,A.rep_bit] using H
      (by simpa only [e,A.rep_bit] using hv)
  · rintro ⟨h,k⟩ g; exact ⟨h g,fun e v hv => k _ _ hv⟩

namespace HashGateLayout
open S8C.AddLayout

def layout (d : ℕ) (hd : 1 ≤ d) : w3_FactorLayout :=
  join (join (w3_fpMulLayout d hd) (w3_fpMulLayout d hd))
    (join (S8C.AddLayout.layout (2*d)) (join (S8C.AddLayout.layout (d+1)) (S8C.AddLayout.layout (d+1))))

noncomputable def degreeCap (d : ℕ) : ℝ := max 8 (136*((d:ℝ)+1)^((3:ℝ)/4))

theorem edges {d : ℕ} (hd : 1 ≤ d) : (layout d hd).ne < 5000*(d+2) := by
  have h := (w3_fpMulIncidenceBounds hd).1
  change _ + _ + (2*d*5+((d+1)*5+(d+1)*5)) < _
  omega

theorem shape {d : ℕ} (hd : 1 ≤ d) : Shape (layout d hd) (degreeCap d) 2 := by
  have hm : Shape (w3_fpMulLayout d hd) (degreeCap d) 2 := by
    constructor
    · intro i; have h := (w3_fpMulIncidenceBounds hd).2.2 i
      rw [w3_gateDegree] at h
      exact h.trans_le (le_max_right ..)
    · intro i; exact ((w3_bitDegree _ _).symm.trans ((w3_fpMulIncidenceBounds hd).2.1 i)).le
  have ha (n : ℕ) : Shape (S8C.AddLayout.layout n) (degreeCap d) 2 := by
    constructor
    · intro i; have h := (w3_gateDegree (S8C.AddLayout.layout n) i).symm.le.trans (gateDegree i)
      exact (Nat.cast_le.mpr h).trans_lt ((by norm_num : (5:ℝ) < 8).trans_le (le_max_left ..))
    · intro i; exact (w3_bitDegree _ _).symm.le.trans (bitDegree i)
  exact join_shape (join_shape hm hm) (join_shape (ha _) (join_shape (ha _) (ha _)))

def addBits {n : ℕ} (a b z : ℕ) (c : Fin n → Bool) (k : Fin (n*4)) :=
  let i : Fin n := ⟨k.val/4,by omega⟩
  match k.val%4 with
  | 0 => a.testBit i.val
  | 1 => b.testBit i.val
  | 2 => z.testBit i.val
  | _ => c i

theorem addBits_iff {n : ℕ} (hn : 0 < n) (a b z : ℕ) (cin : Bool) (c : Fin n → Bool) :
    Accept (S8C.AddLayout.layout n) (test cin) (addBits a b z c) ↔ w3_addColumns n a b z cin c := by
  refine (test_iff cin (addBits a b z c)).trans ?_
  rw [← columns_iff hn]
  have h (i : Fin n) (l : Fin 4) : (reg i l).val/4 = i.val := by simp only [reg]; omega
  have k (i : Fin n) (l : Fin 4) : (reg i l).val%4 = l.val := by simp only [reg]; omega
  simp only [addBits,h,k]; rfl

noncomputable def mulTest {d : ℕ} (hd : 1 ≤ d) (x y u : ℕ) : w3_factorTest (w3_fpMulLayout d hd) := by
  classical
  exact fun g a => w3_fpMulTests d hd g a && decide (∀ (e : {e // (w3_fpMulLayout d hd).gate e = g}) (i : Fin (4*d)),
      (w3_fpMulLayout d hd).bit e.val = w4_M5PortTensor.ext hd i → a e = w3_mulBus d x y u i)

theorem mulTest_iff {d : ℕ} (hd : 1 ≤ d) (x y : ℕ) (r : w3_mulRun d hd) :
    Accept _ (mulTest hd x y r.1.val) r.2 ↔ w3_slotMulInc hd x y r := by
  classical
  let A := w3_fpMulLayout d hd
  constructor
  · intro h
    simp only [Accept,mulTest,Bool.and_eq_true,decide_eq_true_eq] at h
    refine ⟨fun i => ?_,fun g => (h g).1⟩
    let b := w4_M5PortTensor.ext hd i
    let e := A.rep b
    have hb : A.bit e = b := A.rep_bit b
    exact (congrArg r.2 hb).symm.trans ((h (A.gate e)).2 ⟨e,rfl⟩ i hb)
  · rintro ⟨hp,ht⟩ g
    simp only [mulTest,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨ht g,fun e i he => (congrArg r.2 he).trans (hp i)⟩

noncomputable def tests {d p : ℕ} (hd : 1 ≤ d) (a x : ℕ) (r : w3_fpHashCert d p hd) :
    w3_factorTest (layout d hd) :=
  joinTest (joinTest (mulTest hd a x r.1.2.2.1.1.val) (mulTest hd r.1.2.1.val p r.1.2.2.2.1.val))
    (joinTest (test false) (joinTest (test false) (test false)))

def encode {d p : ℕ} (hd : 1 ≤ d) (b z : ℕ) (r : w3_fpHashCert d p hd) (w : w3_slotHashAux d) :
    Fin (layout d hd).nb → Bool :=
  Fin.append (Fin.append r.1.2.2.1.2 r.1.2.2.2.2)
    (Fin.append (addBits r.1.2.2.2.1.val r.1.1.val r.1.2.2.1.1.val w.1)
      (Fin.append (addBits r.1.1.val b w.2.1.val w.2.2.1)
        (addBits z (if r.2 then p else 0) w.2.1.val w.2.2.2)))

@[simp] theorem appendL {n m : ℕ} (u : Fin n → Bool) (v : Fin m → Bool) :
    Fin.append u v ∘ Fin.castAdd m = u := funext (Fin.append_left u v)
@[simp] theorem appendR {n m : ℕ} (u : Fin n → Bool) (v : Fin m → Bool) :
    Fin.append u v ∘ Fin.natAdd n = v := funext (Fin.append_right u v)

theorem joined {A B : w3_FactorLayout} (s : w3_factorTest A) (t : w3_factorTest B)
    (u : Fin A.nb → Bool) (v : Fin B.nb → Bool) :
    Accept (join A B) (joinTest s t) (Fin.append u v) ↔ Accept A s u ∧ Accept B t v := by
  exact (join_iff s t (Fin.append u v)).trans (by rw [appendL,appendR])

set_option maxHeartbeats 1600000 in
theorem encode_iff {d p : ℕ} (hd : 1 ≤ d) (a b x z : ℕ) (r : w3_fpHashCert d p hd) (w : w3_slotHashAux d) :
    Accept _ (tests hd a x r) (encode hd b z r w) ↔ w3_slotHashBits hd a b x z r w := by
  unfold tests encode layout
  erw [joined,joined,joined,joined]
  let m := r.1.2
  have H₁ := mulTest_iff hd a x m.2.1
  have H₂ := mulTest_iff hd m.1.val p m.2.2
  have H₃ := addBits_iff (by omega : 0 < 2*d) m.2.2.1.val r.1.1.val m.2.1.1.val false w.1
  have H₄ := addBits_iff (by omega : 0 < d+1) r.1.1.val b w.2.1.val false w.2.2.1
  have H₅ := addBits_iff (by omega : 0 < d+1) z (if r.2 then p else 0) w.2.1.val false w.2.2.2
  constructor
  · rintro ⟨⟨u,v⟩,t,l,k⟩; exact ⟨⟨H₁.mp u,H₂.mp v,H₃.mp t⟩,H₄.mp l,H₅.mp k⟩
  · rintro ⟨⟨u,v,t⟩,l,k⟩; exact ⟨⟨H₁.mpr u,H₂.mpr v⟩,H₃.mpr t,H₄.mpr l,H₅.mpr k⟩

def carry {n : ℕ} (u : Fin (n*4) → Bool) (i : Fin n) := u (reg i 3)

def addPin {n : ℕ} (a b z : ℕ) (k : Fin (n*4)) : Option Bool :=
  if k.val%4 = 3 then none else some (addBits a b z (fun _ => false) k)

theorem addPin_iff {n : ℕ} (a b z : ℕ) (u : Fin (n*4) → Bool) :
    (∀ k v, addPin a b z k = some v → u k = v) ↔ u = addBits a b z (carry u) := by
  have div (k : Fin (n*4)) (h : k.val%4 = 3) : reg (⟨k.val/4,by omega⟩ : Fin n) 3 = k := by
    apply Fin.ext; change 4*(k.val/4)+3 = k.val; omega
  constructor
  · intro H; funext k; by_cases h : k.val%4 = 3
    · simp [addBits,h,carry,div k h]
    · have hh := H k (addBits a b z (fun _ => false) k) (by simp [addPin,h]); have hk : k.val%4 < 4 := by omega
      rw [hh]; interval_cases hi : k.val%4 <;> simp [addBits,hi] <;> omega
  · intro H k v h; by_cases h' : k.val%4 = 3
    · simp [addPin,h'] at h
    · have hk : k.val%4 < 4 := by omega
      have hv := congrFun H k
      interval_cases hi : k.val%4 <;> simp [addPin,addBits,hi] at hv h <;> first | exact hv.trans h | omega

noncomputable def pinnedAdd {n : ℕ} (a b z : ℕ) :=
  pinTest (A := S8C.AddLayout.layout n) (test false) (addPin a b z)

theorem pinnedAdd_spec {n : ℕ} (hn : 0 < n) (a b z : ℕ) :
    (∃ u, Accept _ (pinnedAdd (n := n) a b z) u) ↔ ∃ c, w3_addColumns n a b z false c := by
  constructor
  · rintro ⟨u,hu⟩; obtain ⟨ht,hp⟩ := (pin_iff _ _ u).mp hu
    exact ⟨carry u,(addBits_iff hn ..).mp ((addPin_iff _ _ _ _).mp hp ▸ ht)⟩
  · rintro ⟨c,hc⟩; let u := addBits a b z c
    refine ⟨u,(pin_iff _ _ _).mpr ⟨(addBits_iff hn ..).mpr hc,?_⟩⟩
    intro k v hv; by_cases h : k.val%4 = 3
    · simp [addPin,h] at hv
    · have hk : k.val%4 < 4 := by omega
      interval_cases hi : k.val%4 <;> simp_all [addPin,u,addBits]

theorem exists_join {A B : w3_FactorLayout} (s : w3_factorTest A) (t : w3_factorTest B) :
    (∃ x, Accept _ (joinTest s t) x) ↔ (∃ u, Accept A s u) ∧ (∃ v, Accept B t v) := by
  constructor
  · rintro ⟨x,h⟩; obtain ⟨hu,hv⟩ := (join_iff s t x).mp h; exact ⟨⟨_,hu⟩,⟨_,hv⟩⟩
  · rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩; exact ⟨_,(joined s t u v).mpr ⟨hu,hv⟩⟩

noncomputable def pinnedMul {d : ℕ} (hd : 1 ≤ d) (a x : ℕ) (r : w3_mulRun d hd) :=
  pinTest (mulTest hd a x r.1.val) (fun i => some (r.2 i))

theorem pinnedMul_spec {d : ℕ} (hd : 1 ≤ d) (a x : ℕ) (r : w3_mulRun d hd) :
    (∃ u, Accept _ (pinnedMul hd a x r) u) ↔ w3_slotMulInc hd a x r := by
  constructor
  · rintro ⟨u,hu⟩; obtain ⟨ht,hp⟩ := (pin_iff _ _ u).mp hu
    have he : u = r.2 := funext fun i => hp i _ rfl
    exact (mulTest_iff hd a x r).mp (he ▸ ht)
  · intro h; exact ⟨r.2,(pin_iff _ _ _).mpr ⟨(mulTest_iff hd a x r).mpr h,fun _ _ h => Option.some.inj h⟩⟩

noncomputable def fixedTests {d p : ℕ} (hd : 1 ≤ d) (a b x z : ℕ) (r : w3_fpHashCert d p hd) :
    w3_factorTest (layout d hd) :=
  let m := r.1.2
  let u := r.1.1.val
  joinTest (joinTest (pinnedMul hd a x m.2.1) (pinnedMul hd m.1.val p m.2.2))
    (joinTest (pinnedAdd m.2.2.1.val u m.2.1.1.val)
      (joinTest (pinnedAdd u b (u+b)) (pinnedAdd z (if r.2 then p else 0) (u+b))))

set_option maxHeartbeats 1600000 in
theorem fixed_iff {d p a b x z : ℕ} (hd : 1 ≤ d) (hp : p < 2^d) (hb : b < p) (hz : z < p)
    (r : w3_fpHashCert d p hd) : (∃ u, Accept _ (fixedTests hd a b x z r) u) ↔ w3_fpHashCheck hd a b x z r := by
  unfold fixedTests layout
  erw [exists_join,exists_join,exists_join,exists_join]
  let m := r.1.2
  let u := r.1.1.val
  let s : Fin (2^(d+1)) := ⟨u+b,by have hu := r.1.1.isLt; dsimp [u]; rw [pow_succ]; omega⟩
  have H := w3_slotHash_spec (a := a) (x := x) hd hp hb hz r
  have X := pinnedMul_spec hd a x m.2.1
  have Y := pinnedMul_spec hd m.1.val p m.2.2
  have C := pinnedAdd_spec (by omega : 0 < 2*d) m.2.2.1.val u m.2.1.1.val
  have L := pinnedAdd_spec (by omega : 0 < d+1) u b s.val
  have R := pinnedAdd_spec (by omega : 0 < d+1) z (if r.2 then p else 0) s.val
  constructor
  · rintro ⟨⟨h,j⟩,k,l,t⟩
    obtain ⟨c,hc⟩ := C.mp k; obtain ⟨v,hv⟩ := L.mp l; obtain ⟨w,hw⟩ := R.mp t
    exact H.1 (c,s,v,w) ⟨⟨X.mp h,Y.mp j,hc⟩,hv,hw⟩
  · intro ok; obtain ⟨⟨c,s',v,w⟩,⟨⟨hx,hy,hc⟩,hv,hw⟩,_⟩ := H.2 ok
    have hu := r.1.1.isLt
    have hpow : 2^d ≤ 2^(d+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have he := w3_addColumns_sound ((hu.trans hp).trans_le hpow) ((hb.trans hp).trans_le hpow) s'.isLt hv
    have hh : s' = s := Fin.ext (by simpa [s,u] using he.symm)
    subst s'
    exact ⟨⟨X.mpr hx,Y.mpr hy⟩,C.mpr ⟨_,hc⟩,L.mpr ⟨_,hv⟩,R.mpr ⟨_,hw⟩⟩

theorem satisfies_iff {d p a b x z : ℕ} (hd : 1 ≤ d) (hp : p < 2^d) (hb : b < p) (hz : z < p)
    (r : w3_fpHashCert d p hd) : Nonempty {v // (w3_factorGraph (layout d hd)).Satisfies
      (w3_factorChecks _ (fixedTests hd a b x z r)) v} ↔ w3_fpHashCheck hd a b x z r := by
  rw [← fixed_iff hd hp hb hz r]
  exact (w3_factorEquiv _ _).nonempty_congr.trans (by simp)

end HashGateLayout
attribute [simp] Fin.natAdd_eq_addNat
end DetDLP.S8J


