-- Prove2me | Definitions.Def_DetDLP_S8L_PacketCode
-- name    : DetDLP_S8L_PacketCode
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T11:16:15.352845+00:00
-- url     : https://prove2.me/theorems/665c20fb-facd-48e5-959b-d1f517842084
-- title:
--   Indexed packet codes for the pair circuit
-- statement:
--   A code gives the counts, incidence maps, and register names of a block. For a family of $n$ blocks of equal size, quotient and remainder identify the block and the local incidence.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8L_Bounds
import Definitions.Def_DetDLP_S8L_FpPairPacket
import Definitions.Def_DetDLP_S8H0_BaseCode

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
namespace DetDLP.S8L.MakePacket
open S8H0 RegisterMap NamedBlocks GateSemantics S8H.PointAddresses S8C Groundwork M89S1 S8G.FpAtomRows
abbrev NC := Code × (ℕ → ℕ)
def catN (a b : NC) : NC := (sum a.1 b.1, fun i => if i < a.1.ne then a.2 i else b.2 (i-a.1.ne))
def Fits {k : ℕ} (c : NC) (b : B k) := Models c.1 b.core.A ∧ ∀ i : Fin b.core.A.ne, c.2 i = (b.name i).val
theorem cat_spec {k : ℕ} {a b : NC} {u v : B k} (h : Fits a u) (j : Fits b v) : Fits (catN a b) (joinB u v) := by
  refine ⟨sum_spec h.1 j.1,fun i => ?_⟩; induction i using Fin.addCases with
  | left i => simp [catN,joinB,h.1.ne,i.isLt,h.2]
  | right i => simp [catN,joinB,h.1.ne,j.2]
def rowN (n m : ℕ) (f : ℕ → ℕ → ℕ) : NC := (BaseCode.rowsCode n m, fun i => f (i/m) (i%m))
def colN (n : ℕ) (a b z c : ℕ → ℕ) : NC := (S8H.PointAddresses.add n, fun i =>
  let k := (S8H.PointAddresses.add n).bit i; let j := k/4; if k%4=0 then a j else if k%4=1 then b j else if k%4=2 then z j else c j)
theorem row_spec {s : Shape} {n m : ℕ} {f : ℕ → ℕ → ℕ} {r : Fin n → Fin m → Ref s} (t) (h : ∀ (i : Fin n) (j : Fin m), f i j = (r i j).source.val) : Fits (rowN n m f) (rows n m r t) := ⟨⟨rfl,rfl,rfl,fun _ => rfl,fun _ => rfl⟩,fun i => h (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2⟩
theorem col_spec {s : Shape} {n : ℕ} {a b z c : ℕ → ℕ} {A B Z C : Fin n → Ref s} (v : Bool)
    (ha : ∀ i : Fin n, a i = (A i).source.val) (hb : ∀ i : Fin n, b i = (B i).source.val) (hz : ∀ i : Fin n, z i = (Z i).source.val) (hc : ∀ i : Fin n, c i = (C i).source.val) : Fits (colN n a b z c) (NamedBlocks.add v A B Z C) := by
  refine ⟨add_spec _,fun i => ?_⟩; simp only [colN,(add_spec n).bit i]; let k := (AddLayout.layout n).bit i
  change (if k.val%4=0 then _ else _) = (colRef A B Z C k).source.val
  generalize hk : k.val%4 = x; unfold colRef; rw [hk]; have hj : k.val/4 < n := by have := k.isLt; change k.val < n*4 at this; omega
  rcases x with _|_|_|x <;> first | exact ha ⟨_,hj⟩ | exact hb ⟨_,hj⟩ | exact hz ⟨_,hj⟩ | exact hc ⟨_,hj⟩
def prodN (d e off : ℕ) (a b z : ℕ → ℕ) : NC := catN (S8H.PointAddresses.mul d,fun i => off + if i<e then i else i-e) (rowN (4*d) 2 fun j k => if k=0 then off+(if j<2*d then j else e-2*d+(j-2*d)) else if j<d then a j else if j<2*d then b (j-d) else z (j-2*d))
theorem ext_spec {d : ℕ} (h : 1 ≤ d) (j : Fin (4*d)) : (if j.val<2*d then j.val else (w4_M5GraphBounds.graph d h).nE-2*d+(j.val-2*d)) = (w4_M5PortTensor.ext h j).val := by
  unfold w4_M5PortTensor.ext w4_M5PortTensor.extEdge; by_cases h₁ : j.val<d <;> by_cases h₂ : j.val<2*d <;> simp only [h₁,h₂,if_true,if_false,dif_pos,dif_neg,reduceDIte,reduceIte] <;> try omega
  · change j.val = j.val + d*0; omega
  · change j.val = (j.val-d) + d*1; omega
  · let n := w4_MulParams.n0 d; let t := w4_M5GraphBounds.W d; let u := w4_MulParams.L2 d * (w4_MulParams.L1 d*t); let v := (2*n-1)*t
    change w4_M5GraphBounds.edgeCount d t-2*d+(j.val-2*d) = 2*d+(2*(n*t)+(2*u+(2*u+(u+(u+(2*n*t+(v+(v+(j.val-2*d)))))))))
    unfold w4_M5GraphBounds.edgeCount; dsimp [v,u,n,t]; omega
theorem prod_spec {s : Shape} {d o : ℕ} (h : 1 ≤ d) {a b z : ℕ → ℕ} {A B Z : HashRows.Word s} {R : Fin (w4_M5GraphBounds.graph d h).nE → Ref s} (hw : ∀ i : Fin _, o+i.val = (R i).source.val) (ha : ∀ j, a j = (A j).source.val) (hb : ∀ j, b j = (B j).source.val) (hz : ∀ j, z j = (Z j).source.val) : Fits (prodN d (w4_M5GraphBounds.graph d h).nE o a b z) (HashRows.product h A B Z R) := by
  apply cat_spec
  · refine ⟨mul_spec h,fun i => ?_⟩; have hh := (mul_spec h).bit i; simp only [S8H.PointAddresses.mul,wires_eq h] at hh; exact (congrArg (o+·) hh).trans (hw _)
  · apply row_spec; intro i j; fin_cases j
    · exact (congrArg (o+·) (ext_spec h i)).trans (hw _)
    · change (if i.val<d then _ else _) = (HashRows.busRef d A B Z i).source.val; unfold HashRows.busRef; split_ifs <;> first | apply ha | apply hb | apply hz
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const PolyT.mul PolyT.div PolyT.mod PolyT.length w4_M5Evaluator.clog2_poly w4_M5Evaluator.vertexCount_poly w4_M5EdgeNat.srcNat_poly w4_M5EdgeNat.dstNat_poly
theorem wiresP {α : Type} [Enc α] {D : α → ℕ} (h : PolyT D) : PolyT fun x => wires (D x) := mul_poly.nb h
attribute [local fun_prop] wiresP P2M_Groundwork_PolyT_ite__226169acf219 PolyT.decide_lt PolyT.decide_eq
def Eff {α : Type} [Enc α] (F : α → NC) := (PolyT fun x => (F x).1.ng) ∧ (PolyT fun x => (F x).1.ne) ∧ ∀ {I : α → ℕ}, PolyT I → (PolyT fun x => (F x).1.gate (I x)) ∧ (PolyT fun x => (F x).2 (I x))
theorem catP {α : Type} [Enc α] {A B : α → NC} (a : Eff A) (b : Eff B) : Eff (fun x => catN (A x) (B x)) := by
  refine ⟨PolyT.add a.1 b.1,PolyT.add a.2.1 b.2.1,fun h => ?_⟩; have j := b.2.2 (PolyT.sub h a.2.1); have i := a.2.2 h; have k := PolyT.decide_lt h a.2.1
  exact ⟨P2M_Groundwork_PolyT_ite__226169acf219 k i.1 (PolyT.add a.1 j.1),P2M_Groundwork_PolyT_ite__226169acf219 k i.2 j.2⟩
def manyN (n : ℕ) (c : Code) (f : ℕ → ℕ → ℕ) : NC :=
  (⟨n*c.ng,n*c.nb,n*c.ne,fun i => i/c.ne*c.ng+c.gate (i%c.ne),fun i => i/c.ne*c.nb+c.bit (i%c.ne)⟩,fun i => f (i/c.ne) (i%c.ne))
theorem many_spec {k : ℕ} (n : ℕ) (c : Code) (f : ℕ → ℕ → ℕ) (u : Fin n → B (k+1)) (h : ∀ i : Fin n, Fits (c,f i) (u i)) : Fits (manyN n c f) (Routes.allRows n u) := by
  induction n generalizing f with
  | zero => exact ⟨⟨by simp [manyN]; rfl,by simp [manyN]; rfl,by simp [manyN]; rfl,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩,fun i => Fin.elim0 i⟩
  | succ n ih =>
    let v := Routes.allRows n (fun j => u j.succ)
    have a := h 0
    have b := ih (fun i => f (i+1)) (fun j => u j.succ) (fun j => h j.succ)
    have t := cat_spec a b
    have left (i : Fin (u 0).core.A.ne) : i.val < c.ne := a.1.ne.symm ▸ i.isLt
    have right (i : Fin v.core.A.ne) : 0 < c.ne := by have := i.isLt; change i.val < v.core.A.ne at this; have hn : n*c.ne=v.core.A.ne := b.1.ne; by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hn; omega
    change Fits _ (joinB (u 0) v)
    refine ⟨⟨?_,?_,?_,?_,?_⟩,?_⟩
    · exact (Nat.succ_mul n c.ng).trans ((Nat.add_comm ..).trans t.1.ng)
    · exact (Nat.succ_mul n c.nb).trans ((Nat.add_comm ..).trans t.1.nb)
    · exact (Nat.succ_mul n c.ne).trans ((Nat.add_comm ..).trans t.1.ne)
    all_goals intro i; induction i using Fin.addCases with
      | left i => simp [manyN,joinB,S8J.join,S8J.splitMap,Nat.div_eq_of_lt (left i),Nat.mod_eq_of_lt (left i)] <;> first | exact a.1.gate i | exact a.1.bit i | exact a.2 i
      | right i =>
        have D : (c.ne+i.val)/c.ne = i.val/c.ne+1 := by rw [Nat.add_comm, Nat.add_div_right _ (right i)]
        simp [manyN,joinB,S8J.join,S8J.splitMap,← a.1.ne,D,Nat.add_mul,← a.1.ng,← a.1.nb] <;> first | rw [show (v.core.A.gate i).val = _ from (b.1.gate i).symm]; change _ = c.ng+(i.val/c.ne*c.ng+c.gate (i.val%c.ne)); omega | rw [show (v.core.A.bit i).val = _ from (b.1.bit i).symm]; change _ = c.nb+(i.val/c.ne*c.nb+c.bit (i.val%c.ne)); omega | exact b.2 i
def regs (m d e : ℕ) := (Routes.bank m d e).size
def wd (o n pin j : ℕ) := if j<n then o+j else pin
def rangeN (d pin o : ℕ) := colN (d+1) (wd o d pin) (wd (o+d) d pin) (fun _ => pin) (o+2*d+·)
def atomN (m d e i : ℕ) : NC :=
  let pin := regs m d e; let w := fun o n => wd o n pin; let P := fun (_ : ℕ) => pin
  let o := i*(Routes.atom d e).size; let tr := 3*d+1; let t := o+tr+2*d
  let z := t+tr; let r := z+tr; let q := r+tr; let a := q+d; let b := a+2*d+e; let cp := b+2*d+e; let aux := cp+1
  let h := catN (catN (prodN d e (a+2*d) P (w o d) (w a (2*d))) (prodN d e (b+2*d) (w q d) P (w b (2*d)))) (catN (colN (2*d) (w b (2*d)) (w r d) (w a (2*d)) (aux+·)) (catN (colN (d+1) (w r d) P (w (aux+2*d) (d+1)) (aux+3*d+1+·)) (colN (d+1) (w z d) (fun _ => cp) (w (aux+2*d) (d+1)) (aux+4*d+2+·))))
  catN h (catN (rangeN d pin o) (catN (colN d (o+tr+·) P (w o d) (o+tr+d+·)) (catN (rangeN d pin z) (catN (rangeN d pin r) (catN (rangeN d pin t) (rowN d 2 fun j k => if k=0 then z+j else t+j))))))
def interm (m d e i : ℕ) := 2*m*(Routes.atom d e).size+(2*m-1)*(stageShape d e).size+i*(triple d).size
def stageN (m d e i : ℕ) : NC :=
  let pin := regs m d e; let w := fun o n => wd o n pin; let P := fun (_ : ℕ) => pin
  let s := 2*m*(Routes.atom d e).size+i*(stageShape d e).size; let a := s+d; let b := a+2*d+e
  let x := w (if i=0 then 0 else interm m d e (i-1)) d; let z := fun j => if i<2*m-2 then w (interm m d e i) d j else pin
  catN (catN (prodN d e (a+2*d) x (w ((i+1)*(Routes.atom d e).size) d) (w a (2*d))) (prodN d e (b+2*d) (w s d) P (w b (2*d)))) (colN (2*d) (w b (2*d)) z (w a (2*d)) (b+2*d+e+·))
def repeated (n : ℕ) (f : ℕ → NC) := manyN n (f 0).1 (fun j => (f j).2)
def dig (m d e j : ℕ) := let b := d-1; if j/b/2 < m then wd ((j/b/2+(if j/b%2=0 then 0 else m))*(Routes.atom d e).size) d (regs m d e) (b-1-j%b) else regs m d e
def base (m d e l : ℕ) :=
  catN (AnchoredLayout.anchorCode (regs m d e+1),id) (catN (AnchoredLayout.anchorCode 1,fun _ => regs m d e) (catN (repeated (2*m) (atomN m d e)) (catN (repeated (2*m-1) (stageN m d e)) (catN (repeated (2*m-2) (fun i => rangeN d (regs m d e) (interm m d e i))) (catN (rowN 1 0 fun _ _ => 0) (rowN l 1 fun j _ => dig m d e j))))))
end DetDLP.S8L.MakePacket


