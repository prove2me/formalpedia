-- Prove2me | Definitions.Def_DetDLP_S8G_AtomSliceEquiv
-- name    : DetDLP_S8G_AtomSliceEquiv
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T09:28:22.222727+00:00
-- url     : https://prove2.me/theorems/87b02f13-d816-47c0-82fd-ce884d46b189
-- title:
--   Tag 1 m-atom register slice to Checked bijection
-- statement:
--   Fix a prime $p$, a seed $S$, and a threshold $T\le p$. The predicate `atomBankOK` checks the $i$-th atom with coefficients $(S_i^{(1)}+1,S_i^{(2)})$. The equivalence `atomBankEquiv` identifies the accepted bank with `FpMoment.Checked S T`. Its inverse recovers the unique nonzero, threshold, and hash witnesses for each atom. For every $i\in\operatorname{Fin}(m)$, the first register word evaluates to the residue of the corresponding decoded unit.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8G_SeedAndAtomBank
import Definitions.Def_DetDLP_S8G_FpMomentCert
import Definitions.Def_DetDLP_S8C3_Semantics

set_option autoImplicit false
namespace DetDLP.S8G.AtomSliceEquiv
open S8H0 RegisterMap ResidueWires SignalBank S8C SeedAndAtomBank
noncomputable section
variable {p m : ℕ} [Fact p.Prime]
private abbrev d (p : ℕ) := atomWidth p
private abbrev hd (p : ℕ) : 1 ≤ d p := FpAtomRows.atomWidth_pos p
private abbrev e (p : ℕ) := (w4_M5GraphBounds.graph (d p) (hd p)).nE
private abbrev Slot (p : ℕ) := (atomSlot (d p) (e p)).Data
private abbrev Extra (p : ℕ) := Bits (d p) × w3_slotDiff (d p) × w3_slotHashAux (d p)
private abbrev Valid (v : Slot p) :=
  let r := v.2.2.2.1
  below p v.1 ∧ (value v.1.1).val ≠ 0 ∧ below p r.1 ∧ below p r.2.1.1

private def unitEq : {x : Triple (d p) // below p x ∧ (value x.1).val ≠ 0} ≃ (ZMod p)ˣ := by
  let f := zmodEquiv (d:=d p) (primeFitsAtom p).le
  refine (Equiv.subtypeEquivRight (q := fun x => ∃ _ : below p x, (value x.1).val ≠ 0) (fun _ => by simp)).trans ?_
  refine (Equiv.subtypeSubtypeEquivSubtypeExists (below p) (fun x => (value x.val.1).val ≠ 0)).symm.trans ((Equiv.subtypeEquiv f ?_).trans unitsEquivNeZero.symm)
  intro x; change (value x.val.1).val ≠ 0 ↔ f x ≠ 0
  have h : (f x).val = (value x.val.1).val := by
    change (↑((finEquiv _ x).val) : ZMod p).val = _; rw [ZMod.val_natCast_of_lt (finEquiv _ x).isLt]; apply finEquiv_val
  rw [← h, ZMod.val_ne_zero]

private def typed : {v : Slot p // Valid v} ≃ ((ZMod p)ˣ × AtomRun p) × Extra p := by
  let split : {v : Slot p // Valid v} ≃
      ({x : Triple (d p) // below p x ∧ (value x.1).val ≠ 0} × CheckedRun (d p) p (hd p)) × _ :=
    { toFun := fun w =>
        let r := w.val.2.2.2.1
        ((⟨w.val.1,w.prop.1,w.prop.2.1⟩,⟨r.1,w.prop.2.2.1⟩,(⟨r.2.1.1,w.prop.2.2.2⟩,r.2.1.2),r.2.2),
          w.val.2.1,w.val.2.2.1,w.val.2.2.2.2)
      invFun := fun ⟨⟨x,z,⟨r,q⟩,c⟩,o,di,a⟩ =>
        ⟨(x.val,o,di,(z.val,(r.val,q),c),a),x.prop.1,x.prop.2,z.prop,r.prop⟩
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let runE := (runEquiv (hd p) (primeFitsAtom p).le).trans ((zmodFin p).symm.prodCongr (Equiv.refl _))
  exact split.trans ((unitEq.prodCongr runE).prodCongr ((Equiv.refl _).prodCongr
    (((numBits _).prodCongr (Equiv.refl _)).prodCongr (auxEquiv _))))

private def witnesses (S : FpSeed p m) (i : Fin m) (T : ℕ) (t : (ZMod p)ˣ × AtomRun p) (w : Extra p) :=
  let x := (w3_fpResidue t.1).val
  w3_slotOr (d p) x false w.1 ∧ w3_slotLt (d p) t.2.1.val T w.2.1 ∧
    w3_slotHashBits (hd p) ((S i).1.val+1) (S i).2.val x t.2.1.val t.2.2 w.2.2

/-- At every slot the two hash inputs come from the corresponding entry of the fixed seed. -/
def atomBankOK (S : FpSeed p m) (T : ℕ) (v : (atomBankShape m (d p) (e p)).Data) : Prop :=
  ∀ i, ∃ h : Valid (v i), let t := typed ⟨v i,h⟩; witnesses S i T t.1 t.2

private theorem liftW (S : FpSeed p m) (i : Fin m) {T : ℕ} (hT : T ≤ p) (t : (ZMod p)ˣ × AtomRun p) :
    w3_slotLift (atomOK S i T (w3_fpResidue t.1) t.2) (witnesses S i T t) := by
  have O := w3_slotOr_spec false ((w3_fpResidue t.1).isLt.trans (primeFitsAtom p))
  have L := w3_slotLt_spec (t.2.1.isLt.trans (primeFitsAtom p)) (hT.trans (primeFitsAtom p).le)
  have H := w3_slotHash_spec (a:=(S i).1.val+1) (x:=(w3_fpResidue t.1).val) (hd p)
    (primeFitsAtom p) (S i).2.isLt t.2.1.isLt t.2.2
  constructor
  · intro w ⟨o,l,h⟩; exact ⟨(O.1 _ o).resolve_left (by decide),L.1 _ l,H.1 _ h⟩
  · rintro ⟨ho,hl,hh⟩; obtain ⟨o,Oo,Uo⟩ := O.2 (.inr ho)
    obtain ⟨l,Ll,Ul⟩ := L.2 hl; obtain ⟨h,Hh,Uh⟩ := H.2 hh
    exact ⟨(o,l,h),⟨Oo,Ll,Hh⟩,fun ⟨a,b,c⟩ ⟨A,B,C⟩ => by rw [Uo a A,Ul b B,Uh c C]⟩

private def forget {α β : Type} {P : α → Prop} {Q : α → β → Prop}
    (h : ∀ a, w3_slotLift (P a) (Q a)) : {v : α × β // Q v.1 v.2} ≃ Subtype P where
  toFun v := ⟨v.val.1,(h _).1 _ v.prop⟩
  invFun v := ⟨(v.val,((h _).2 v.prop).choose),((h _).2 v.prop).choose_spec.1⟩
  left_inv v := Subtype.ext (Prod.ext rfl (((h _).2 ((h _).1 _ v.prop)).choose_spec.2 _ v.prop).symm)
  right_inv _ := rfl

private def slotEquiv (S : FpSeed p m) (i : Fin m) {T : ℕ} (hT : T ≤ p) :
    {v : Slot p // ∃ h : Valid v, let t := typed ⟨v,h⟩; witnesses S i T t.1 t.2} ≃
    {t : (ZMod p)ˣ × AtomRun p // atomOK S i T (w3_fpResidue t.1) t.2} :=
  (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm.trans
    ((Equiv.subtypeEquivOfSubtype typed).trans (forget (liftW S i hT)))

/-- Decode each atom independently; the inverse restores its unique auxiliary witnesses. -/
def atomBankEquiv (S : FpSeed p m) {T : ℕ} (hT : T ≤ p) :
    {v : (atomBankShape m (d p) (e p)).Data // atomBankOK S T v} ≃ FpMoment.Checked S T :=
  Equiv.subtypePiEquivPi.trans ((Equiv.piCongrRight fun i => slotEquiv S i hT).trans
    { toFun := fun f => ⟨(fun i => (f i).val.1,fun i => (f i).val.2),fun i => (f i).prop⟩
      invFun := fun v i => ⟨(v.val.1 i,v.val.2 i),v.prop i⟩
      left_inv := fun _ => rfl, right_inv := fun _ => rfl })

/-- The first word of slot `i` is the residue of the decoded unit, as a natural number. -/
theorem atomBankEquiv_residue (S : FpSeed p m) {T : ℕ} (hT : T ≤ p)
    (v : {v // atomBankOK S T v}) (i : Fin m) :
    (value (v.val i).1.1).val = (w3_fpResidue ((atomBankEquiv S hT v).val.1 i)).val := by
  let x : {x : Triple (d p) // below p x} := ⟨(v.val i).1,(v.prop i).choose.1⟩
  change _ = ((zmodFin p) (finEquiv _ x)).val
  rw [show ((zmodFin p) (finEquiv _ x)).val = (finEquiv (primeFitsAtom p).le x).val by
    apply ZMod.val_natCast_of_lt; exact (finEquiv _ x).isLt]
  exact (finEquiv_val _ x).symm

/-- A routed copy of the residue word evaluates to the same residue at every bit index. -/
theorem atomBankEquiv_word_eval {s : Shape} (S : FpSeed p m) {T : ℕ} (hT : T ≤ p)
    (v : {v // atomBankOK S T v}) (i : Fin m) (q : GateRoutes.Path (.word (d p)) s)
    (u : Bits (s.size+1)) (hq : ∀ j, (q (.word j)).get (s.decode (u ∘ Fin.castSucc)) = (v.val i).1.1 j) :
    HashRows.evalWord (GateRoutes.word q) u (w3_fpResidue ((atomBankEquiv S hT v).val.1 i)).val := by
  rw [← atomBankEquiv_residue S hT v i]
  exact GateRoutes.word_eval q u _ hq

end
end DetDLP.S8G.AtomSliceEquiv


