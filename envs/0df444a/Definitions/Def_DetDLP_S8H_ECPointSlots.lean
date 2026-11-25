-- Prove2me | Definitions.Def_DetDLP_S8H_ECPointSlots
-- name    : DetDLP_S8H_ECPointSlots
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:21:48.947924+00:00
-- url     : https://prove2.me/theorems/8a0437d9-a53f-444b-968f-e9c6e55139bb
-- title:
--   Bit-level arithmetic transcripts for single-point curve queries
-- statement:
--   For each coordinate triple, the seven modular multiply-add checks have a unique extension to multiplication-wire assignments and column carries. The resulting order-query witnesses are equivalent to curve points, including one encoding for infinity. Adding a certified strict inequality, a parity-selected hash, and the requested coordinate prefix gives an equivalence with the points counted by the element query.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8H_ECPointArithmetic
import Definitions.Def_DetDLP_W3_FpSlotBits

set_option autoImplicit false
namespace DetDLP.S8H.ECPointSlots
open ECPointArithmetic M89S1

variable {p : ℕ} [Fact p.Prime]

abbrev C (p : ℕ) := Bool × ZMod p × ZMod p
abbrev Transcript (p : ℕ) := (Fin 7 → Run p) × (Fin 7 → w3_slotHashAux (width p))

def slots (E : WeierstrassCurve (ZMod p)) (x y α β : ZMod p) (t : Transcript p) :=
  ∀ i, let a := args E x y α β (fun j => (t.1 j).1) i
       w3_slotHashBits (Nat.succ_pos (bitLen p)) a.1.val a.2.2.val a.2.1.val (t.1 i).1.val (t.1 i).2 (t.2 i)

theorem sound {E : WeierstrassCurve (ZMod p)} {x y α β : ZMod p} {t : Transcript p}
    (h : slots E x y α β t) : runsOK E x y α β t.1 := fun i =>
  (w3_slotHash_spec _ (fits p) (ZMod.val_lt _) (ZMod.val_lt _) _).1 _ (h i)

theorem slot_unique (mul : w3_modMulInterface) (E : WeierstrassCurve (ZMod p)) (x y α β : ZMod p) :
    ∃! t, slots E x y α β t := by
  classical
  obtain ⟨r,hr,ur⟩ := runs_unique mul E x y α β
  let a := args E x y α β (fun j => (r j).1)
  have ex (i : Fin 7) := (w3_slotHash_spec (Nat.succ_pos (bitLen p)) (fits p)
    (a i).2.2.val_lt (r i).1.val_lt (r i).2 (a := (a i).1.val) (x := (a i).2.1.val)).2 (hr i)
  choose c hc using fun i => (ex i).exists
  refine ⟨(r,c),hc,?_⟩
  rintro ⟨s,d⟩ hh
  obtain rfl : s = r := ur s (sound hh)
  exact Prod.ext rfl (funext fun i => (ex i).unique (hh i) (hc i))

theorem values (mul : w3_modMulInterface) {E : WeierstrassCurve (ZMod p)} {x y α β : ZMod p}
    {t : Transcript p} (h : slots E x y α β t) (i : Fin 7) :
    (t.1 i).1 = outputs E x y α β i :=
  congrFun (only_outputs _ _ _ _ _ _ (fun j => gate_sound mul (sound h j))) i

/-- Raw coordinates use just one representative for infinity. -/
def pointOK (E : WeierstrassCurve (ZMod p)) (c : C p) :=
  if c.1 then c.2.1 = 0 ∧ c.2.2 = 0 else E.toAffine.Equation c.2.1 c.2.2

def coordEquiv (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] :
    {c // pointOK E c} ≃ E.toAffine.Point where
  toFun c := match c with
    | ⟨(true,_,_),_⟩ => .zero
    | ⟨(false,x,y),h⟩ => .some x y (E.toAffine.equation_iff_nonsingular.mp h)
  invFun P := match P with
    | .zero => ⟨(true,0,0),rfl,rfl⟩
    | .some x y h => ⟨(false,x,y),h.1⟩
  left_inv c := by
    rcases c with ⟨⟨tag,x,y⟩,h⟩
    cases tag
    · rfl
    · obtain ⟨rfl,rfl⟩ : x = 0 ∧ y = 0 := h; rfl
  right_inv P := by cases P <;> rfl

def word (b : ℕ) (c : C p) := c.1 :: (digitWord b c.2.1.val ++ digitWord b c.2.2.val)

@[simp] theorem word_coords {E : WeierstrassCurve (ZMod p)} (b : ℕ) (P : E.toAffine.Point) :
    word b (coords P) = ecWord b P := by cases P <;> simp [word,coords,ecWord]

def checkCurve (c : C p) (t : Transcript p) :=
  if c.1 then c.2.1 = 0 ∧ c.2.2 = 0 else (t.1 2).1 = (t.1 5).1

theorem checkCurve_iff (mul : w3_modMulInterface) {E : WeierstrassCurve (ZMod p)} {c : C p}
    {α β : ZMod p} {t : Transcript p} (h : slots E c.2.1 c.2.2 α β t) :
    checkCurve c t ↔ pointOK E c := by
  simp only [checkCurve,pointOK,values mul h,curve_iff]

def orderOK (E : WeierstrassCurve (ZMod p)) (w : C p × Transcript p) :=
  slots E w.1.2.1 w.1.2.2 0 0 w.2 ∧ checkCurve w.1 w.2

theorem orderLift (mul : w3_modMulInterface) (E : WeierstrassCurve (ZMod p)) (c : C p) :
    w3_slotLift (pointOK E c) (fun t => orderOK E (c,t)) := by
  refine ⟨fun t h => (checkCurve_iff mul h.1).mp h.2,?_⟩
  intro hc; obtain ⟨t,ht,ut⟩ := slot_unique mul E c.2.1 c.2.2 0 0
  exact ⟨t,⟨ht,(checkCurve_iff mul ht).mpr hc⟩,fun u hu => ut u hu.1⟩

noncomputable def project {A B : Type} {P : A → Prop} {Q : A × B → Prop}
    (h : ∀ a, w3_slotLift (P a) (fun b => Q (a,b))) : {w // Q w} ≃ {a // P a} where
  toFun w := ⟨w.1.1,(h w.1.1).1 w.1.2 w.2⟩
  invFun a := ⟨(a.1,((h a.1).2 a.2).exists.choose),((h a.1).2 a.2).exists.choose_spec⟩
  left_inv w := by
    let h' := (h w.1.1).2 ((h _).1 _ w.2)
    exact Subtype.ext (Prod.ext rfl (h'.unique h'.exists.choose_spec w.2))
  right_inv _ := rfl

noncomputable def orderEquiv (mul : w3_modMulInterface) (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] :
    {w // orderOK E w} ≃ E.toAffine.Point := (project (orderLift mul E)).trans (coordEquiv E)

variable {m : ℕ} {E : WeierstrassCurve (ZMod p)} [E.IsElliptic]

def elemOK (E : WeierstrassCurve (ZMod p)) (S : ECSeed p m) (i : Fin m) (T b : ℕ)
    (η : List Bool) (w : C p × (Transcript p × w3_slotDiff (width p))) :=
  let c := w.1
  let t := w.2.1
  slots E c.2.1 c.2.2 (alpha S i c.2.2) (beta S i c.2.2) t ∧
    checkCurve c t ∧ c.1 = false ∧ w3_slotLt (width p) (t.1 6).1.val T w.2.2 ∧
    (word b c).take η.length = η

def elemPoint (E : WeierstrassCurve (ZMod p)) (S : ECSeed p m) (i : Fin m) (T b : ℕ)
    (η : List Bool) (c : C p) :=
  pointOK E c ∧ c.1 = false ∧
    (outputs E c.2.1 c.2.2 (alpha S i c.2.2) (beta S i c.2.2) 6).val < T ∧
    (word b c).take η.length = η

theorem elemLift (mul : w3_modMulInterface) (S : ECSeed p m) (i : Fin m) (T b : ℕ)
    (hT : T ≤ p) (η : List Bool) (c : C p) :
    w3_slotLift (elemPoint E S i T b η c) (fun w => elemOK E S i T b η (c,w)) := by
  let l (t : Transcript p) := w3_slotLt_spec ((t.1 6).1.val_lt.trans (fits p)) (hT.trans (fits p).le)
  constructor
  · rintro ⟨t,d⟩ ⟨ht,hc,ha,hd,hpre⟩
    exact ⟨(checkCurve_iff mul ht).mp hc,ha,values mul ht 6 ▸ (l t).1 d hd,hpre⟩
  · rintro ⟨hc,ha,hl,hpre⟩
    obtain ⟨t,ht,ut⟩ := slot_unique mul E c.2.1 c.2.2 (alpha S i c.2.2) (beta S i c.2.2)
    obtain ⟨d,hd,ud⟩ := (l t).2 (by rw [values mul ht]; exact hl)
    refine ⟨(t,d),⟨ht,(checkCurve_iff mul ht).mpr hc,ha,hd,hpre⟩,?_⟩
    rintro ⟨y,z⟩ ⟨hy,_,_,hz,_⟩
    obtain rfl := ut y hy
    exact Prod.ext rfl (ud z hz)

theorem coords_decode (c : {c // pointOK E c}) : coords (coordEquiv E c) = c.1 := by
  rcases c with ⟨⟨tag,x,y⟩,h⟩; cases tag
  · rfl
  · obtain ⟨rfl,rfl⟩ : x = 0 ∧ y = 0 := h; rfl

theorem elemPoint_iff (S : ECSeed p m) (i : Fin m) (T b : ℕ) (η : List Bool) (P : E.toAffine.Point) :
    elemPoint E S i T b η (coords P) ↔ ECPointGadget.elemPin b T S i η P = true := by
  have ok : pointOK E (coords P) := by cases P with
    | zero => exact ⟨rfl,rfl⟩
    | some x y h => exact h.1
  simp only [elemPoint,ok,true_and,word_coords,ECPointGadget.elemPin,Bool.and_eq_true,decide_eq_true_eq,
    ← outputs_mem S i T P,and_assoc]

noncomputable def elemEquiv (mul : w3_modMulInterface) (S : ECSeed p m) (i : Fin m) (T b : ℕ)
    (hT : T ≤ p) (η : List Bool) : {w // elemOK E S i T b η w} ≃
    {P : E.toAffine.Point // ECPointGadget.elemPin b T S i η P = true} := by
  refine (project (elemLift mul S i T b hT η)).trans ?_
  refine { toFun := fun c => ⟨coordEquiv E ⟨c.1,c.2.1⟩, (elemPoint_iff ..).mp ?_⟩,
           invFun := fun P => ⟨coords P.1,(elemPoint_iff ..).mpr P.2⟩,
           left_inv := ?_, right_inv := ?_ }
  · rw [coords_decode]; exact c.2
  · intro c; exact Subtype.ext (coords_decode _)
  · rintro ⟨P,h⟩; apply Subtype.ext; cases P <;> rfl

end DetDLP.S8H.ECPointSlots


