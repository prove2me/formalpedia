-- Prove2me | Definitions.Def_DetDLP_S8C3_MakePacket
-- name    : DetDLP_S8C3_MakePacket
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T09:16:24.53917+00:00
-- url     : https://prove2.me/theorems/8adea065-3661-4f60-9008-900779944a0a
-- title:
--   Tag 3 uniform PolyT BTN instance builder
-- statement:
--   Defines a uniform polynomial-time constructor for the Tag 3 graph-instance packet. For each input word, it decodes the prime, prefix, and network width, then uses the explicit arithmetic register map `sigNat(d,e,mlen,i)` to represent the anchored `S8C3.Semantics.layout` block as `PointAddresses.Code`. The map respects the source convention that every `.pin _` is assigned the final register index; its prefix length is clipped to `min η.length (bitLen p)` for the signal while the full prefix length determines the allocated rows. `CycleCode.models` and `CycleCode.packetEndpoints` identify the code with the cyclic graph layout and its subdivision endpoints; the `PolyT` endpoint bounds are discharged with unary padding. The resulting `make : List Bool → List Bool` satisfies `make_poly : Groundwork.PolyT make` and, on every Tag 3 word `S8C3.word T S i η`, agrees with `encodeBTNInstance` applied to the subdivision of `w3_factorGraph (S8C3.Semantics.layout p T ((S i).1.val + 1) (S i).2.val η))` at the prescribed scale parameters.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8C3_Semantics
import Definitions.Def_DetDLP_S8C3_Packet
import Definitions.Def_DetDLP_S8H0_BaseCode

set_option autoImplicit false
namespace DetDLP.S8C3.MakePacket
open S8H0 RegisterMap NamedBlocks GateSemantics S8H.PointAddresses S8C Groundwork M89S1
private abbrev NC := Code × (ℕ → ℕ)
private def catN (a b : NC) : NC := (sum a.1 b.1, fun i => if i < a.1.ne then a.2 i else b.2 (i-a.1.ne))
private def Fits {k : ℕ} (c : NC) (b : B k) := Models c.1 b.core.A ∧ ∀ i : Fin b.core.A.ne, c.2 i = (b.name i).val
private theorem cat_spec {k : ℕ} {a b : NC} {u v : B k} (h : Fits a u) (j : Fits b v) : Fits (catN a b) (joinB u v) := by
  refine ⟨sum_spec h.1 j.1,fun i => ?_⟩; induction i using Fin.addCases with
  | left i => simp [catN,joinB,h.1.ne,i.isLt,h.2]
  | right i => simp [catN,joinB,h.1.ne,j.2]
private def regs (d e : ℕ) := (Routes.bank d e).size
private def rowN (n m : ℕ) (f : ℕ → ℕ → ℕ) : NC := (BaseCode.rowsCode n m, fun i => f (i/m) (i%m))
private def colN (n : ℕ) (a b z c : ℕ → ℕ) : NC := (S8H.PointAddresses.add n, fun i =>
  let k := (S8H.PointAddresses.add n).bit i; let j := k/4; if k%4=0 then a j else if k%4=1 then b j else if k%4=2 then z j else c j)
private theorem row_spec {s : Shape} {n m : ℕ} {f : ℕ → ℕ → ℕ} {r : Fin n → Fin m → Ref s} (t) (h : ∀ (i : Fin n) (j : Fin m), f i j = (r i j).source.val) : Fits (rowN n m f) (rows n m r t) := ⟨⟨rfl,rfl,rfl,fun _ => rfl,fun _ => rfl⟩,fun i => h (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2⟩
private theorem col_spec {s : Shape} {n : ℕ} {a b z c : ℕ → ℕ} {A B Z C : Fin n → Ref s} (v : Bool)
    (ha : ∀ i : Fin n, a i = (A i).source.val) (hb : ∀ i : Fin n, b i = (B i).source.val) (hz : ∀ i : Fin n, z i = (Z i).source.val) (hc : ∀ i : Fin n, c i = (C i).source.val) : Fits (colN n a b z c) (NamedBlocks.add v A B Z C) := by
  refine ⟨add_spec _,fun i => ?_⟩; simp only [colN,(add_spec n).bit i]; let k := (AddLayout.layout n).bit i
  change (if k.val%4=0 then _ else _) = (colRef A B Z C k).source.val
  generalize hk : k.val%4 = x; unfold colRef; rw [hk]; have hj : k.val/4 < n := by have := k.isLt; change k.val < n*4 at this; omega
  rcases x with _|_|_|x <;> first | exact ha ⟨_,hj⟩ | exact hb ⟨_,hj⟩ | exact hz ⟨_,hj⟩ | exact hc ⟨_,hj⟩
private def scanN (n : ℕ) (x t : ℕ → ℕ) (c : ℕ) : NC := (⟨n+1,3*n+1,3*n+1,fun i => i/3,id⟩,fun i =>
  if i%3=0 then if i/3=0 then c else t (i/3-1) else if i%3=1 then x (i/3) else t (i/3))
private theorem scan_spec {s : Shape} (n : ℕ) (x t : ℕ → ℕ) (c : Ref s) (X T : Fin n → Ref s) (hx : ∀ j : Fin n, x j = (X j).source.val) (ht : ∀ j : Fin n, t j = (T j).source.val) : Fits (scanN n x t c.source.val) (Routes.scan n X c T) := by
  induction n generalizing x t c with
  | zero => rw [Routes.scan]; exact ⟨⟨rfl,rfl,rfl,fun i => by change i.val/3 = i.val/1; have := i.isLt; change i.val < 1 at this; omega,fun _ => rfl⟩,fun i => by have hi : i.val=0 := Nat.lt_one_iff.mp i.isLt; change (if i.val%3=0 then _ else _) = c.source.val; simp [hi]⟩
  | succ n ih =>
    let f := fun (_ j : ℕ) => if j=0 then c.source.val else if j=1 then x 0 else t 0
    have H := cat_spec (row_spec (f:=f) (r:=fun (_ : Fin 1) => ![c,X 0,T 0]) (fun _ v => decide (v 2 = (v 0 || v 1))) (by intro _ j; fin_cases j <;> first | rfl | exact hx 0 | exact ht 0)) (ih (fun j => x (j+1)) (fun j => t (j+1)) (T 0) (X ∘ Fin.succ) (T ∘ Fin.succ) (fun j => hx j.succ) (fun j => ht j.succ))
    rw [Routes.scan]; convert H using 1; apply Prod.ext
    · simp only [scanN,catN,rowN,BaseCode.rowsCode,sum,Code.mk.injEq]; refine ⟨by omega,by omega,by omega,?_,?_⟩ <;> funext i <;> simp [id] <;> omega
    · funext i; simp [scanN,catN,rowN,BaseCode.rowsCode,f,← ht 0]; split_ifs <;> (first | rfl | omega | congr 1 <;> omega)
private def prodN (d e off : ℕ) (a b z : ℕ → ℕ) : NC := catN (S8H.PointAddresses.mul d,fun i => off + if i<e then i else i-e) (rowN (4*d) 2 fun j k => if k=0 then off+(if j<2*d then j else e-2*d+(j-2*d)) else if j<d then a j else if j<2*d then b (j-d) else z (j-2*d))
private def body (d e l : ℕ) : NC :=
  let pin := fun (_ : ℕ) => regs d e; let w := fun o n j => if j<n then o+j else pin j
  let r := fun o u => colN (d+1) (w o d) (w u d) pin (fun j => u+d+j)
  let tr := 3*d+1; let q := 3*tr; let m := q+d; let m' := m+2*d+e; let cp := m'+2*d+e; let aux := cp+1; let z := tr; let rem := 2*tr; let lt := aux+5*d+3
  let h := catN (catN (prodN d e (m+2*d) pin (w 0 d) (w m (2*d))) (prodN d e (m'+2*d) (w q d) pin (w m' (2*d)))) (catN (colN (2*d) (w m' (2*d)) (w rem d) (w m (2*d)) (aux+·)) (catN (colN (d+1) (w rem d) pin (w (aux+2*d) (d+1)) (aux+3*d+1+·)) (colN (d+1) (w z d) (fun _ => cp) (w (aux+2*d) (d+1)) (aux+4*d+2+·))))
  catN (AnchoredLayout.anchorCode 1,pin) (catN (r 0 d) (catN (r z (z+d)) (catN (r rem (rem+d)) (catN h (catN (r z lt) (catN (scanN d id (lt+2*d+1+·) (pin 0)) (rowN l 1 fun j _ => d-2-j)))))))
private def base (d e l : ℕ) := catN (AnchoredLayout.anchorCode (regs d e+1),id) (body d e l)
def sigNat (d e mlen i : ℕ) := (base d e mlen).2 i
private theorem ext_spec {d : ℕ} (h : 1 ≤ d) (j : Fin (4*d)) : (if j.val<2*d then j.val else (w4_M5GraphBounds.graph d h).nE-2*d+(j.val-2*d)) = (w4_M5PortTensor.ext h j).val := by
  unfold w4_M5PortTensor.ext w4_M5PortTensor.extEdge; by_cases h₁ : j.val<d <;> by_cases h₂ : j.val<2*d <;> simp only [h₁,h₂,if_true,if_false,dif_pos,dif_neg,reduceDIte,reduceIte] <;> try omega
  · change j.val = j.val + d*0; omega
  · change j.val = (j.val-d) + d*1; omega
  · let n := w4_MulParams.n0 d; let t := w4_M5GraphBounds.W d; let u := w4_MulParams.L2 d * (w4_MulParams.L1 d*t); let v := (2*n-1)*t
    change w4_M5GraphBounds.edgeCount d t-2*d+(j.val-2*d) = 2*d+(2*(n*t)+(2*u+(2*u+(u+(u+(2*n*t+(v+(v+(j.val-2*d)))))))))
    unfold w4_M5GraphBounds.edgeCount; dsimp [v,u,n,t]; omega
private theorem prod_spec {s : Shape} {d o : ℕ} (h : 1 ≤ d) {a b z : ℕ → ℕ} {A B Z : HashRows.Word s} {R : Fin (w4_M5GraphBounds.graph d h).nE → Ref s} (hw : ∀ i : Fin _, o+i.val = (R i).source.val) (ha : ∀ j, a j = (A j).source.val) (hb : ∀ j, b j = (B j).source.val) (hz : ∀ j, z j = (Z j).source.val) : Fits (prodN d (w4_M5GraphBounds.graph d h).nE o a b z) (HashRows.product h A B Z R) := by
  apply cat_spec
  · refine ⟨mul_spec h,fun i => ?_⟩; have hh := (mul_spec h).bit i; simp only [S8H.PointAddresses.mul,wires_eq h] at hh; exact (congrArg (o+·) hh).trans (hw _)
  · apply row_spec; intro i j; fin_cases j
    · exact (congrArg (o+·) (ext_spec h i)).trans (hw _)
    · change (if i.val<d then _ else _) = (HashRows.busRef d A B Z i).source.val; unfold HashRows.busRef; split_ifs <;> first | apply ha | apply hb | apply hz
set_option maxHeartbeats 1400000 in
private theorem body_spec (p T a b : ℕ) (η : W) : Fits (body (d p) (e p) η.length) (Semantics.net p T a b η) := by
  unfold body Semantics.net Routes.network HashRows.block; dsimp only
  refine cat_spec ?_ (cat_spec ?_ (cat_spec ?_ (cat_spec ?_ (cat_spec (cat_spec (cat_spec ?_ ?_) (cat_spec ?_ (cat_spec ?_ ?_))) (cat_spec ?_ (cat_spec ?_ ?_))))))
  · exact ⟨AnchoredLayout.anchorModels 1,fun _ => rfl⟩
  all_goals first | apply col_spec | apply prod_spec | apply scan_spec | apply row_spec
  all_goals have hd := hd p; intros; try simp only [Routes.wires,Routes.rw,Routes.xp,Routes.zp,Routes.rp,Routes.remp,Routes.auxp,Routes.ltp,Routes.orp,GateRoutes.word,HashRows.padded,HashRows.pub,RangeRows.pad,id_eq]
  all_goals (try split_ifs) <;> (try simp [Ref.source,Addr.index,Routes.bank,regs,Shape.size,triple,run,RegisterMap.mul,GateRoutes.auxShape,e]) <;> omega
private abbrev core (p T a b : ℕ) (η : W) := AnchoredLayout.block (Semantics.net p T a b η).core (regs (d p) (e p)+1)
theorem models (p T a b : ℕ) (η : W) : Models (base (d p) (e p) η.length).1 (core p T a b η).A := sum_spec (AnchoredLayout.anchorModels _) (body_spec p T a b η).1
theorem sigNat_spec (p T a b : ℕ) (η : W) (i : Fin (core p T a b η).A.ne) : sigNat (d p) (e p) (min η.length (bitLen p)) i = (AnchoredLayout.signal (Semantics.net p T a b η).core (Semantics.net p T a b η).name i).val := by
  let u : B (regs (d p) (e p)+1) := ⟨⟨AnchoredLayout.anchors _,fun _ _ => true⟩,id⟩
  have h : Fits (AnchoredLayout.anchorCode (regs (d p) (e p)+1),id) u := ⟨AnchoredLayout.anchorModels _,fun _ => rfl⟩
  exact (cat_spec h (body_spec p T a b η)).2 i
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const PolyT.mul PolyT.div PolyT.mod PolyT.length w4_M5Evaluator.clog2_poly w4_M5Evaluator.vertexCount_poly w4_M5EdgeNat.srcNat_poly w4_M5EdgeNat.dstNat_poly
private theorem wiresP {α : Type} [Enc α] {D : α → ℕ} (h : PolyT D) : PolyT fun x => wires (D x) := mul_poly.nb h
attribute [local fun_prop] wiresP P2M_Groundwork_PolyT_ite__226169acf219 PolyT.decide_lt PolyT.decide_eq
private def Eff {α : Type} [Enc α] (F : α → NC) := (PolyT fun x => (F x).1.ng) ∧ (PolyT fun x => (F x).1.ne) ∧ ∀ {I : α → ℕ}, PolyT I → (PolyT fun x => (F x).1.gate (I x)) ∧ (PolyT fun x => (F x).2 (I x))
private theorem catP {α : Type} [Enc α] {A B : α → NC} (a : Eff A) (b : Eff B) : Eff (fun x => catN (A x) (B x)) := by
  refine ⟨PolyT.add a.1 b.1,PolyT.add a.2.1 b.2.1,fun h => ?_⟩; have j := b.2.2 (PolyT.sub h a.2.1); have i := a.2.2 h; have k := PolyT.decide_lt h a.2.1
  exact ⟨P2M_Groundwork_PolyT_ite__226169acf219 k i.1 (PolyT.add a.1 j.1),P2M_Groundwork_PolyT_ite__226169acf219 k i.2 j.2⟩
set_option maxHeartbeats 2000000 in
private theorem baseP {α : Type} [Enc α] {D E L : α → ℕ} (hd : PolyT D) (he : PolyT E) (hl : PolyT L) : Eff (fun x => base (D x) (E x) (L x)) := by
  unfold base body prodN; refine catP ?_ (catP ?_ (catP ?_ (catP ?_ (catP ?_ (catP (catP (catP (catP ?_ ?_) (catP ?_ ?_)) (catP ?_ (catP ?_ ?_))) (catP ?_ (catP ?_ ?_)))))))
  all_goals unfold Eff; refine ⟨?_,?_,fun hi => ⟨?_,?_⟩⟩ <;> simp only [scanN,colN,rowN,regs,Routes.bank,Shape.size,triple,run,RegisterMap.mul,GateRoutes.auxShape,AnchoredLayout.anchorCode,BaseCode.rowsCode,S8H.PointAddresses.mul,S8H.PointAddresses.add,id_eq] <;> fun_prop (disch := assumption)
theorem sigNat_poly {α : Type} [Enc α] {D E L I : α → ℕ} (hd : PolyT D) (he : PolyT E) (hl : PolyT L) (hi : PolyT I) : PolyT fun x => sigNat (D x) (E x) (L x) (I x) := ((baseP hd he hl).2.2 hi).2
private abbrev width (w : W) := d (Packet.prime w)
private def addr (w : W) := (base (width w) (wires (width w)) (Packet.pfx w).length).1
private def name (w : W) := sigNat (width w) (wires (width w)) (min (Packet.pfx w).length (bitLen (Packet.prime w)))
private def cyc (w : W) := CycleCode.code (addr w) (name w)
def make (w : W) : W := outerPacket w (S8H.WirePacket.packet ((cyc w).ng+(cyc w).nb) (cyc w).ne (cyc w).gate (fun j => (cyc w).ng+(cyc w).bit j)) (S8G.FpMoment.Code.sizeField w)
private theorem cycle_spec (p T a b : ℕ) (η : W) : Models (CycleCode.code (base (d p) (e p) η.length).1 (sigNat (d p) (e p) (min η.length (bitLen p)))) (Semantics.layout p T a b η) := by
  have h := CycleCode.models (models p T a b η) (sigNat (d p) (e p) (min η.length (bitLen p)))
  have k := AnchoredLayout.next_congr (fun i : Fin (core p T a b η).A.ne => sigNat (d p) (e p) (min η.length (bitLen p)) i) (AnchoredLayout.signal (Semantics.net p T a b η).core (Semantics.net p T a b η).name) (by intro i j; rw [sigNat_spec,sigNat_spec]; exact Fin.val_inj)
  obtain ⟨_,he,hs,_⟩ := CycleCode.packetEndpoints (models p T a b η) (sigNat (d p) (e p) (min η.length (bitLen p)))
  have H : Models _ _ := ⟨h.ng,h.nb,he,hs,h.bit⟩; rw [k] at H; exact H
open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
private theorem dataM (w : W) : Models (cyc w) (Semantics.layout (Packet.prime w) 0 0 0 (Packet.pfx w)) := by simpa only [cyc,addr,name,width,wires_eq (hd _)] using cycle_spec (Packet.prime w) 0 0 0 (Packet.pfx w)
private def big (w : W) := (((Packet.prime w-1).bits ++ Packet.pfx w) ++ [false,false]).flatMap (fun _ => List.replicate 80000 ())
private theorem bound (w : W) : (cyc w).ng+(cyc w).nb+(cyc w).ne ≤ (big w).length ∧ (cyc w).ne+(cyc w).ne ≤ (big w).length := by
  have M := dataM w; have H := w3_incDims _ (Semantics.gate_surj (Packet.prime w) 0 0 0 (Packet.pfx w)); rw [← M.ng,← M.nb,← M.ne] at H
  have E := w4_M5GraphBounds.graph_edge_bound (hd (Packet.prime w)); rw [← wires_eq] at E
  have L : (big w).length = (width w+1+(Packet.pfx w).length)*80000 := by
    have h : width w = (Packet.prime w-1).bits.length+1 := congrArg (·+1) (S8G.FpMoment.Code.width_eq _).symm
    rw [h]; simp only [big,List.length_flatMap,List.length_replicate,List.map_const',List.sum_replicate_nat,List.length_append,List.length_cons,List.length_nil]; omega
  rw [L]; suffices (cyc w).ne*3 ≤ (width w+1+(Packet.pfx w).length)*80000 by omega
  simp only [cyc,CycleCode.code,addr,base,body,prodN,catN,scanN,colN,rowN,regs,Routes.bank,Shape.size,RegisterMap.triple,run,RegisterMap.mul,GateRoutes.auxShape,AnchoredLayout.anchorCode,BaseCode.rowsCode,S8H.PointAddresses.mul,S8H.PointAddresses.add,sum]; change wires (width w) < 1100*(width w+1) at E; omega
attribute [local fun_prop] first_poly more_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f
set_option maxHeartbeats 1500000 in
theorem make_poly : PolyT make := by
  have hp : PolyT Packet.prime := by unfold Packet.prime S8G.FpMoment.Code.prime second; fun_prop
  have hf : PolyT Packet.pfx := by unfold Packet.pfx third second; fun_prop
  have D : PolyT width := by unfold width d S8H.ECPointArithmetic.width bitLen; fun_prop (disch := assumption)
  have B := baseP D (wiresP D) (PolyT.length hf); have hV := PolyT.add (PolyT.add B.1 B.2.1) B.2.1; have hE := PolyT.add B.2.1 (PolyT.add B.2.1 B.2.1)
  have hb : PolyT big := by unfold big; apply PolyT.flatMap (PolyT.const _); fun_prop (disch := assumption)
  have U {q : W → ℕ} (hq : PolyT q) (hl : ∀ w, q w ≤ (big w).length) : Unary q := (PolyT.unary_min_length hq hb).congr fun w => by simp only [min_eq_left (hl w)]
  have c := CycleCode.endpoints_poly (c:=addr) (name:=name) B.1 B.2.1 (U B.2.1 (fun w => le_trans (show (addr w).ne ≤ (cyc w).ne+(cyc w).ne by simp [cyc,CycleCode.code]; omega) (bound w).2)) ((baseP (PolyT.comp D (PolyT.fst PolyT.id')) (PolyT.comp (wiresP D) (PolyT.fst PolyT.id')) (PolyT.comp (PolyT.length hf) (PolyT.fst PolyT.id'))).2.2 (PolyT.snd PolyT.id')).1 (by apply sigNat_poly (PolyT.comp D (PolyT.fst PolyT.id')) (PolyT.comp (wiresP D) (PolyT.fst PolyT.id')) _ (PolyT.snd PolyT.id'); exact (PolyT.length (PolyT.unary_min_length (PolyT.comp (w4_M5Evaluator.clog2_poly hp) (PolyT.fst PolyT.id')) (PolyT.comp hf (PolyT.fst PolyT.id')))).congr (fun w => by simp [min_comm,bitLen]))
  exact outerPacket_poly PolyT.id' (S8H.WirePacket.packet_poly (nv:=fun w => (cyc w).ng+(cyc w).nb) (ne:=fun w => (cyc w).ne) (src:=fun w => (cyc w).gate) (dst:=fun w j => (cyc w).ng+(cyc w).bit j) hV hE (U (PolyT.add hV hE) (fun w => (bound w).1)) (U (PolyT.add hE hE) (fun w => (bound w).2)) c.1 (PolyT.add (PolyT.comp (f:=fun w : W => (cyc w).ng) (g:=Prod.fst (β:=ℕ)) (PolyT.add B.1 B.2.1) (PolyT.fst PolyT.id')) c.2)) S8G.FpMoment.Code.sizeField_poly

private theorem packet_model {c : Code} {A : w3_FactorLayout} (M : Models c A) : S8H.WirePacket.packet (c.ng+c.nb) c.ne c.gate (fun j => c.ng+c.bit j) = (w3_factorGraph A).subdivision.encode := by
  let G := w3_factorGraph A; have hv : c.ng+c.nb=G.nV := by rw [M.ng,M.nb]; rfl
  have he : c.ne=G.nE := M.ne; rw [hv,he]; exact S8H.WirePacket.packet_eq G _ _ (fun j => M.gate j) (fun j => by rw [M.ng,M.bit j]; rfl)
set_option maxHeartbeats 1500000 in
theorem make_word (p : ℕ) [Fact p.Prime] (T : ℕ) (S : FpSeed p (blockCount (bitLen p))) (i : Fin (blockCount (bitLen p))) (η : W) : make (word T S i η) = encodeBTNInstance (word T S i η) (w3_factorGraph (Semantics.layout p T ((S i).1.val+1) (S i).2.val η)).subdivision (S8G.FpMoment.scale (blockCount (bitLen p)) (bitLen p)) (S8G.FpMoment.scale (blockCount (bitLen p)) (bitLen p)) 1 := by
  obtain ⟨hp,_,_,_,hf⟩ := Packet.fields T S i η; let w := word T S i η; let G := w3_factorGraph (Semantics.layout p T ((S i).1.val+1) (S i).2.val η)
  have M : Models (cyc w) (Semantics.layout p T ((S i).1.val+1) (S i).2.val η) := by simpa only [cyc,addr,name,width,w,hp,hf,wires_eq (hd p)] using cycle_spec p T ((S i).1.val+1) (S i).2.val η
  change outerPacket w _ _ = _; rw [packet_model M,S8G.FpMoment.Code.sizeField,show S8G.FpMoment.Code.prime w=p from hp,S8G.FpMoment.Code.width_eq,S8G.FpMoment.Code.slots_eq,outerPacket_eq]
end DetDLP.S8C3.MakePacket


