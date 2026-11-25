-- Prove2me | Definitions.Def_DetDLP_S8M_ECAtomSlot
-- name    : DetDLP_S8M_ECAtomSlot
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:58:04.438001+00:00
-- url     : https://prove2.me/theorems/d81662ca-716d-42c1-a884-e05a989ffe10
-- title:
--   Reusable single EC factor-block point register slot and slice bijection
-- statement:
--   A reusable single-slot register block for an elliptic-curve factor block, together with its acceptance characterization on the decoded local slice. The theorem \(\texttt{slotBlock\_iff}\) identifies satisfaction of the routed block with satisfaction of the underlying network on the pulled-back assignment. The decoded-slice equivalence relates the accepted slice witnesses to factor-block points, and \(\texttt{slotEquiv\_coords}\) records how the flag and canonical coordinate registers project to point coordinates.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H4_Semantics
import Theorems.Thm_DetDLP_w3_m5_modmul_r2

set_option autoImplicit false
namespace DetDLP.S8M.ECAtomSlot
open S8H0 RegisterMap NamedBlocks HashRows ResidueWires S8H4 RangeRows
abbrev slotShape := Routes.bank
private abbrev edges {d : ℕ} (hd : 1 ≤ d) := (w4_M5GraphBounds.graph d hd).nE

/-- Recover a structured register address from its flattened index. -/
def address : (s : Shape) → Fin s.size → Addr s
  | .bit, _ => .bit
  | .word _, j => .word j
  | .pair l r, j => 
    if h : j.val < l.size then .fst (address l ⟨j.val,h⟩)
    else .snd (address r ⟨j.val-l.size,by have := j.isLt; change j.val < l.size+r.size at this; omega⟩)
  | .vec _ t, j => .vec (finProdFinEquiv.symm j).1 (address t (finProdFinEquiv.symm j).2)

def route {l s : Shape} (path : GateRoutes.Path l s) : Fin (l.size+1) → Fin (s.size+1) :=
  Fin.lastCases (Fin.last _) fun j => (path (address l j)).index.castSucc

private def fixed {d : ℕ} (hd : 1 ≤ d) (p T : ℕ) (c : GateRoutes.Coeff) : B ((slotShape d (edges hd)).size+1) :=
  let base := joinB (RangeRows.block d (edges hd) p) <| joinB (many 5 fun g =>
    HashRows.block p (GateRoutes.wires hd p c g.castSucc)) (CurveRows.block d (edges hd))
  let ltT := NamedBlocks.add (s:=slotShape d (edges hd)) (n:=d+1) true
    (pad fun i : Fin d => Ref.reg (.fst (oa 6 (.fst (.word i)))))
    (pad fun i : Fin d => .reg (.snd (.snd (.snd (.fst (.word i)))))) (fun i => .pin (T.testBit i))
    (fun i => .reg (.snd (.snd (.snd (.snd (.word i))))))
  joinB ⟨base.core, Routes.network.embed ∘ base.name⟩ <| joinB (HashRows.block p (Routes.network.six hd p c)) <|
    joinB (rows 1 1 (fun _ _ => .reg (.fst CurveRows.flag)) (fun _ r => decide (r 0 = false))) ltT

variable {d : ℕ} {s : Shape} (hd : 1 ≤ d) (p T : ℕ) (c : GateRoutes.Coeff)
variable (a0W b0W a1W b1W : Word s) (path : GateRoutes.Path (slotShape d (edges hd)) s)
/-- Local arithmetic and one seven-input seed-selection row per bit. -/
def slotBlock : B (s.size+1) :=
  let F := fixed hd p T c
  let wire (r : Ref (slotShape d (edges hd))) : Ref s := match r with
    | .reg a => .reg (path a) | .pin b => .pin b | .masked b a => .masked b (path a)
  joinB ⟨F.core, route path ∘ F.name⟩ <| rows d 7 (fun j =>
    ![wire (Routes.network.coord ya 0),wire (Routes.network.a6Reg j),wire (Routes.network.b6Reg j),
      a0W j,b0W j,a1W j,b1W j]) fun _ r =>
      decide (r 1 = (if r 0 then r 5 else r 3) ∧ r 2 = (if r 0 then r 6 else r 4))

private theorem address_index {t : Shape} (a : Addr t) : address t a.index = a := by
  induction a with
  | bit => rfl
  | word => rfl
  | fst a ih => simp [Addr.index,address,Fin.castAdd,ih]
  | snd a ih => simp [Addr.index,address,Fin.natAdd,ih]
  | vec j a ih => simp [Addr.index,address,ih]

/-- Evaluate the routed block by restricting the assignment to this slot. -/
theorem slotBlock_iff (u : Bits (s.size+1)) (a0 b0 a1 b1 : ℕ)
    (A : evalWord a0W u a0) (B0 : evalWord b0W u b0) (C : evalWord a1W u a1) (D : evalWord b1W u b1) :
    (slotBlock hd p T c a0W b0W a1W b1W path).OK u ↔
    (Routes.network hd p T a0 b0 a1 b1 c []).OK (u ∘ route path) := by
  let x := u ∘ route path
  have R (a : Addr (slotShape d (edges hd))) : (Ref.reg (path a)).eval u = (Ref.reg a).eval x := by
    change u _ = u (Fin.lastCases _ _ a.index.castSucc); rw [Fin.lastCases_castSucc,address_index]; rfl
  simp only [slotBlock,joinB_iff]; change (fixed hd p T c).OK x ∧ _ ↔ _
  simp only [fixed,Routes.network,joinB_iff,rows_iff,decide_eq_true_eq,List.length_nil]
  have test (q : Bool) (a b j : ℕ) : (if q then a else b).testBit j = (if q then a.testBit j else b.testBit j) := by cases q <;> rfl
  have R' (a : Addr (slotShape d (edges hd))) : (Ref.reg (path a)).eval u = (Ref.reg a).eval (u ∘ route path) := R a
  dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,Function.comp_apply]
  constructor
  · rintro ⟨⟨h,g,f,l⟩,m⟩; refine ⟨h,g,?_,f,l,fun j => Fin.elim0 j⟩; intro j
    have H := m j; simp [Routes.network.coord,GateRoutes.word,padded,show 0 < d by omega,
      Routes.network.a6Reg,Routes.network.b6Reg,A j,B0 j,C j,D j,test] at H ⊢
    simpa only [R' (.snd (.fst (.word j))), R' (.snd (.snd (.fst (.word j)))),
      R' (.fst (ya (.fst (.word ⟨0,by omega⟩))))] using H
  · rintro ⟨h,g,m,f,l,_⟩; refine ⟨⟨h,g,f,l⟩,?_⟩; intro j
    have H := m j; simp [Routes.network.coord,GateRoutes.word,padded,show 0 < d by omega,
      Routes.network.a6Reg,Routes.network.b6Reg,A j,B0 j,C j,D j,test] at H ⊢
    simpa only [R' (.snd (.fst (.word j))), R' (.snd (.snd (.fst (.word j)))),
      R' (.fst (ya (.fst (.word ⟨0,by omega⟩))))] using H

open GateSemantics S8H ECPointSlots ECPointArithmetic
open private valid unpack decoded from Definitions.Def_DetDLP_S8H4_Semantics
noncomputable section
variable {p m : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)} [E.IsElliptic]
variable {T : ℕ} (S : ECSeed p m) (i : Fin m)
private abbrev bankP (p : ℕ) := slotShape (GateSemantics.d p) (e p)
/-- Raw slice predicate: the seed-selection registers are fixed before the arithmetic tests. -/
def sliceOK (E : WeierstrassCurve (ZMod p)) (T : ℕ) (v : (bankP p).Data) : Prop :=
  ∃ h : valid S i v, elemOK E S i T (bitLen p) [] (unpack S i ⟨v,h⟩)

omit [E.IsElliptic] in
/-- The ambient block constrains exactly the decoded local slice; other registers are not counted. -/
theorem slotBlock_slice_iff (path : GateRoutes.Path (bankP p) s) (u : Bits (s.size+1))
    (A : evalWord a0W u ((S i false).1.val+1)) (B0 : evalWord b0W u (S i false).2.val)
    (C : evalWord a1W u ((S i true).1.val+1)) (D : evalWord b1W u (S i true).2.val) :
    (slotBlock (GateSemantics.hd p) p T (coeff E) a0W b0W a1W b1W path).OK u ↔
      sliceOK S i E T ((bankP p).decode ((u ∘ route path) ∘ Fin.castSucc)) :=
  (slotBlock_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B0 C D).trans (decoded T [] E S i _)

/-- Accepted decoded slices, including their full witnesses, correspond one-to-one to factor points. -/
def slotEquiv (hT : T ≤ p) : {v // sliceOK S i E T v} ≃ {P : E.toAffine.Point // P ∈ ecFactorBlock E T S i} :=
  (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm.trans ((Equiv.subtypeEquivOfSubtype (unpack S i)).trans
    ((elemEquiv w3_m5_modmul_r2 S i T (bitLen p) hT []).trans (Equiv.subtypeEquivRight fun P => by
      simp [ECPointGadget.elemPin,ecFactorBlock])))

variable (hT : T ≤ p) (v : {v // sliceOK S i E T v})
/-- The forward map reads the flag and the canonical values of both coordinate registers. -/
theorem slotEquiv_coords : let P := (slotEquiv S i hT v).val; let q := coords P
    q.1 = v.val.1.1.1 ∧ q.2.1.val = (value v.val.1.1.2.1.1).val ∧
      q.2.2.val = (value v.val.1.1.2.2.1).val := by
  let t := unpack S i ⟨v.val,v.prop.choose⟩
  have ht : elemOK E S i T (bitLen p) [] t := v.prop.choose_spec
  let q := (project (elemLift (E:=E) w3_m5_modmul_r2 S i T (bitLen p) hT [])) ⟨t,ht⟩
  have H : coords (slotEquiv S i hT v).val = t.1 := coords_decode (E:=E) ⟨q.val,q.prop.1⟩
  dsimp only; rw [H]; exact ⟨rfl,resVal _ _,resVal _ _⟩
end
end DetDLP.S8M.ECAtomSlot


