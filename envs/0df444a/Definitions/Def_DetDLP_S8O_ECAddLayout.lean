-- Prove2me | Definitions.Def_DetDLP_S8O_ECAddLayout
-- name    : DetDLP_S8O_ECAddLayout
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:34:24.158248+00:00
-- url     : https://prove2.me/theorems/9e74e769-aa7f-4184-92ef-56215d268bf1
-- title:
--   Certified short Weierstrass EC addition layout
-- statement:
--   Private helper definition in the elliptic-curve pair-query development.
-- source:
--   S. Liu, B. Zhang, and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University Preprint, Section 2.4 and 3.1–3.2

import Definitions.Def_DetDLP_S8K_ECAddArithmetic
import Definitions.Def_DetDLP_S8H_ECPointSlots
import Definitions.Def_DetDLP_S8J_HashGateLayout

/-! Slot refinement for the coordinate conversion and addition in Section 2.4,
Lemma 2.4 (pp. 9–10) of S. Liu, B. Zhang and K. Ren, “A Deterministic
Subexponential-time Algorithm for the Discrete Logarithm Problem”, Zhejiang
University Preprint, 23 November 2026. -/
set_option autoImplicit false
namespace DetDLP.S8O.ECAddLayout
open S8H.ECPointArithmetic S8K.ECAddArithmetic
variable {p : ℕ} [Fact p.Prime]

structure Clause (W : Type) where
  residue : Prop
  bits : W → Prop
  lift : w3_slotLift residue bits

private def both {A B : Type} (a : Clause A) (b : Clause B) : Clause (A × B) :=
  ⟨a.residue ∧ b.residue, fun w => a.bits w.1 ∧ b.bits w.2, w3_slotLiftProd a.lift b.lift⟩

private def plain (P Q : Prop) (h : P ↔ Q) : Clause Unit :=
  ⟨P, fun _ => Q, fun _ => h.mpr, fun hp => ⟨(),h.mp hp,fun _ _ => rfl⟩⟩

private def wordEq (x y : ZMod p) := ∀ i : Fin (width p), x.val.testBit i = y.val.testBit i

private theorem eq_bits (x y : ZMod p) : x = y ↔ wordEq x y := by
  refine ⟨fun e _ => e ▸ rfl, fun h => ZMod.val_injective p (Nat.eq_of_testBit_eq fun i => ?_)⟩
  by_cases hi : i < width p
  · exact h ⟨i,hi⟩
  · have H := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_eq_false_of_lt (x.val_lt.trans_le ((fits p).le.trans H)),
        Nat.testBit_eq_false_of_lt (y.val_lt.trans_le ((fits p).le.trans H))]

private def finalCoords (out expected : Coords p) := plain (out = expected)
  (out.1 = expected.1 ∧ wordEq out.2.1 expected.2.1 ∧ wordEq out.2.2 expected.2.2)
  (by simp only [← eq_bits, Prod.ext_iff])

abbrev GateAux (p : ℕ) := w3_slotHashAux (width p) × w3_slotDiff (width p)
private def hash (a x b : ZMod p) (r : Run p) : Clause (GateAux p) where
  residue := gate a x b r.1 r.2
  bits w := w3_slotHashBits (Nat.succ_pos _) a.val b.val x.val r.1.val r.2 w.1 ∧
    w3_slotLt (width p) r.1.val p w.2
  lift := by
    have H := w3_slotHash_spec (a := a.val) (x := x.val) (Nat.succ_pos _) (fits p) b.val_lt r.1.val_lt r.2
    have L := w3_slotLt_spec (r.1.val_lt.trans (fits p)) (fits p).le
    exact ⟨fun w h => H.1 w.1 h.1, fun hr => (w3_slotLiftProd H L).2 ⟨hr,r.1.val_lt⟩⟩

private def inv (u : ZMod p) (z : ZeroInvCert p) :=
  both (hash u z.2.1 0 z.2.2)
    (plain (if z.1 then u = 0 ∧ z.2.1 = 0 else z.2.2.1 = 1)
      (if z.1 then wordEq u 0 ∧ wordEq z.2.1 0 else wordEq z.2.2.1 1) (by simp only [← eq_bits]))

variable (E : WeierstrassCurve (ZMod p))

def mapChecks (P out : Coords p) (c : MapCert p) :=
  let (i,x,y) := P
  let (X,t,u,Y,_) := c
  both (both (hash 36 x (3*E.b₂) X) (both (hash E.a₁ x E.a₃ t)
    (both (hash 2 y t.1 u) (both (hash 108 u.1 0 Y) (plain True True Iff.rfl)))))
    (finalCoords out (if i then (true,0,0) else (false,X.1,Y.1)))

def addChecks (P Q out : Coords p) (c : AddCert p) :=
  let (i,x,y) := P; let (j,z,w) := Q
  let (ux,bx,uy,by',dy,chord,sq,num,tan,lsq,tx,X,dx,ty,Y,_) := c
  let l := if !i && !j && !bx.1 then chord.1 else if !i && !j && bx.1 && !by'.1 then tan.1 else 0
  both (both (hash (-1) x z ux) <| both (inv ux.1 bx) <| both (hash 1 y w uy) <| both (inv uy.1 by') <|
    both (hash (-1) y w dy) <| both (hash dy.1 bx.2.1 0 chord) <| both (hash x x 0 sq) <|
    both (hash 3 sq.1 (-27*E.c₄) num) <| both (hash num.1 by'.2.1 0 tan) <| both (hash l l 0 lsq) <|
    both (hash (-1) x lsq.1 tx) <| both (hash (-1) z tx.1 X) <| both (hash (-1) X.1 x dx) <|
    both (hash l dx.1 0 ty) <| both (hash (-1) y ty.1 Y) (plain True True Iff.rfl))
    (finalCoords out (if i then Q else if j then (false,x,y) else if bx.1 && by'.1 then (true,0,0) else (false,X.1,Y.1)))

theorem ecToSW_lift (P out : Coords p) (c : MapCert p) :
    w3_slotLift (ecToSWOK E P out c) (mapChecks E P out c).bits := (mapChecks E P out c).lift

theorem swAdd_lift (P Q out : Coords p) (c : AddCert p) :
    w3_slotLift (swAddOK E P Q out c) (addChecks E P Q out c).bits := (addChecks E P Q out c).lift

private theorem extend {C A : Type} {P : C → Prop} {Q : C → A → Prop}
    (h : ∃! c, P c) (k : ∀ c, w3_slotLift (P c) (Q c)) : ∃! w : C × A, Q w.1 w.2 := by
  obtain ⟨c,hc,uc⟩ := h; obtain ⟨a,ha,ua⟩ := (k c).2 hc
  refine ⟨(c,a),ha,?_⟩; rintro ⟨d,b⟩ hb
  obtain rfl := uc d ((k d).1 b hb); exact Prod.ext rfl (ua _ hb)

theorem ecToSW_unique_bits [E.IsElliptic] (hp : 3 < p) (mul : w3_modMulInterface) (P : E.toAffine.Point) :
    ∃! w : MapCert p × _, (mapChecks E (coords P) (coords (S8K.SWEquiv.equiv E (S8K.SWEquiv.six_ne_zero hp) P)) w.1).bits w.2 :=
  extend (ecToSW_unique E hp mul P) (ecToSW_lift E _ _)

theorem swAdd_unique_bits (mul : w3_modMulInterface) (P Q : (S8K.SWEquiv.short E).toAffine.Point) :
    ∃! w : AddCert p × _, (addChecks E (coords P) (coords Q) (coords (P+Q)) w.1).bits w.2 :=
  extend (swAdd_unique E mul P Q) (swAdd_lift E _ _ _)

private noncomputable def erase {I O W : Type} (f : I → O) (q : I → O → W → Prop)
    (h : ∀ i, ∃! w, q i (f i) w) (s : ∀ i o w, q i o w → o = f i) :
    {t : I × O × W // q t.1 t.2.1 t.2.2} ≃ I where
  toFun t := t.1.1
  invFun i := ⟨(i,f i,(h i).exists.choose),(h i).exists.choose_spec⟩
  left_inv := by
    rintro ⟨⟨i,o,w⟩,hw⟩; obtain rfl := s i o w hw
    exact Subtype.ext (Prod.ext rfl (Prod.ext rfl ((h i).unique (h i).exists.choose_spec hw)))
  right_inv _ := rfl

noncomputable def ecToSW_slotEquiv [E.IsElliptic] (hp : 3 < p) (mul : w3_modMulInterface) :
    {t : E.toAffine.Point × Coords p × (MapCert p × _) //
      (mapChecks E (coords t.1) t.2.1 t.2.2.1).bits t.2.2.2} ≃ E.toAffine.Point :=
  erase _ (fun (P : E.toAffine.Point) o (w : MapCert p × _) => (mapChecks E (coords P) o w.1).bits w.2)
    (ecToSW_unique_bits E hp mul) (fun P o w h =>
    ecToSW_sound E hp mul P o w.1 ((ecToSW_lift E _ _ _).1 _ h))

abbrev SWPoint (E : WeierstrassCurve (ZMod p)) := (S8K.SWEquiv.short E).toAffine.Point
noncomputable def swAdd_slotEquiv (mul : w3_modMulInterface) :
    {t : (SWPoint E × SWPoint E) × Coords p × (AddCert p × _) //
      (addChecks E (coords t.1.1) (coords t.1.2) t.2.1 t.2.2.1).bits t.2.2.2} ≃ SWPoint E × SWPoint E :=
  erase _ (fun (i : SWPoint E × SWPoint E) o (w : AddCert p × _) =>
    (addChecks E (coords i.1) (coords i.2) o w.1).bits w.2)
    (fun i => swAdd_unique_bits E mul i.1 i.2) (fun i o w h =>
    swAdd_sound E mul i.1 i.2 o w.1 ((swAdd_lift E _ _ _ _).1 _ h))

open S8J HashGateLayout
/-- Only the hash sublayouts; equality, range and branch wiring is not included. -/
def hashBank (d : ℕ) (hd : 1 ≤ d) : ℕ → w3_FactorLayout
  | 0 => HashGateLayout.layout d hd
  | n+1 => join (HashGateLayout.layout d hd) (hashBank d hd n)

theorem hashBank_edges {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    (hashBank d hd n).ne < (n+1)*(5000*(d+2)) := by
  induction n with
  | zero => simpa [hashBank] using edges hd
  | succ n ih =>
    change (HashGateLayout.layout d hd).ne + (hashBank d hd n).ne < _
    rw [Nat.succ_mul]; have := edges hd; omega

theorem hashBank_shape {d : ℕ} (hd : 1 ≤ d) (n : ℕ) : Shape (hashBank d hd n) (degreeCap d) 2 := by
  induction n with
  | zero => exact shape hd
  | succ n ih => exact join_shape (shape hd) ih

theorem hashBank_degree {d : ℕ} (hd : 1 ≤ d) (n : ℕ) (v : Fin (w3_factorGraph (hashBank d hd n)).nV) :
    (w3_factorGraph (hashBank d hd n)).deg v ≤ max 12 ⌈136*((d:ℝ)+1)^((3:ℝ)/4)⌉₊ := by
  let A := hashBank d hd n; have H := hashBank_shape hd n
  change Fin (A.ng + A.nb) at v
  induction v using Fin.addCases with
  | left g =>
    rw [w3_gateDegree]; change degreeOf A.gate g ≤ _
    have h := H.1 g
    rcases lt_max_iff.mp h with h | h
    · exact le_trans (by exact_mod_cast h.le : degreeOf A.gate g ≤ 8) (by omega)
    · exact le_trans (by exact_mod_cast (h.le.trans (Nat.le_ceil _))) (le_max_right ..)
  | right b => rw [w3_bitDegree]; exact (H.2 b).trans (by omega)
end DetDLP.S8O.ECAddLayout


