-- Prove2me | Definitions.Def_DetDLP_S8C3_PortEval
-- name    : DetDLP_S8C3_PortEval
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T09:44:21.202281+00:00
-- url     : https://prove2.me/theorems/45f377b7-44aa-4671-b2b3-39e1e0a56e68
-- title:
--   Tag 3 uniform PolyT port evaluator
-- statement:
--   For a tag-3 element query, the port algorithm returns the local subdivision tensor on each vertex and incident-bit word. At a multiplication gate the bits are reordered into the multiplier port order; at a copy or subdivision vertex the algorithm tests equality of all incident bits. The block dispatch and the packet decoder are polynomial-time functions of the encoded query.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8C3_MakePacket
import Definitions.Def_DetDLP_S8H0_LocalGateEq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DetDLP.S8C3.PortEval
open S8H0 Groundwork GateAgree RegisterMap NamedBlocks GateSemantics S8J S8J.CircuitRealizes S8C
private theorem rank {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) (hf : Function.Injective f) (l : List α) (i : α) : (l.map f).idxOf (f i) = l.idxOf i := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : x = i <;> simp_all [hf.eq_iff, eq_comm]
private abbrev Code := ℕ × (ℕ → W → Bool)
private def cat (a b : Code) : Code := (a.1+b.1, fun i w => if i<a.1 then a.2 i w else b.2 (i-a.1) w)
private def Fits (c : Code) (B : Block) := c.1 = B.A.ng ∧ ∀ (i : Fin B.A.ng) (w : W), c.2 i w = localCheck B.A B.t i w
private theorem catFits {a b : Code} {A B : Block} (ha : Fits a A) (hb : Fits b B) : Fits (cat a b) ⟨join A.A B.A,joinTest A.t B.t⟩ := by
  refine ⟨congrArg₂ (·+·) ha.1 hb.1,fun i w => ?_⟩; induction i using Fin.addCases with
  | left i => simp only [cat,ha.1,Fin.val_castAdd,if_pos i.isLt,ha.2,LocalGateEq.join_left]
  | right i => simp only [cat,ha.1,Fin.val_natAdd,Nat.not_lt_of_le (Nat.le_add_right ..),if_false,Nat.add_sub_cancel_left,hb.2,LocalGateEq.join_right]
private theorem catB {k : ℕ} {a b : Code} {A B : B k} (ha : Fits a A.core) (hb : Fits b B.core) : Fits (cat a b) (joinB A B).core := catFits ha hb
private theorem fiberRank {m n k : ℕ} (gate : Fin n → Fin k) (g : Fin k) (f : Fin m → Fin n) (hf : StrictMono f) (hs : ∀ e, gate e = g ↔ ∃ j, f j = e) (j : Fin m) : ((List.finRange n).filter fun e => decide (gate e = g)).idxOf (f j) = j.val := by
  have h : ((List.finRange n).filter fun e => decide (gate e = g)) = List.ofFn f := by
    apply List.Pairwise.eq_of_mem_iff (r := (·<·))
    · exact List.Pairwise.sublist List.filter_sublist (List.pairwise_ofFn.mpr (fun _ _ h => h) : (List.ofFn (id : Fin n → Fin n)).Pairwise (·<·))
    · exact List.pairwise_ofFn.mpr hf
    · intro e; simpa using hs e
  rw [h,List.ofFn_eq_map,rank _ hf.injective,List.idxOf_finRange]
private theorem rowsLocal {s : Shape} {n m : ℕ} (r : Fin n → Fin m → Ref s) (t) (i : Fin n) (w : W) : let B := (rows n m r t).core; localCheck B.A B.t i w = t i fun j => (r i j).read (w.getD j.val false) := by
  unfold rows localCheck mapped; dsimp only; congr 1; funext j
  change (r (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1 (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2).read _ = _; rw [Equiv.symm_apply_apply]; apply congrArg ((r i j).read); apply congrArg (fun k => w.getD k false)
  apply fiberRank _ i (fun j => finProdFinEquiv (i,j)) _ _ j
  · intro x y h; change (finProdFinEquiv (i,x)).val < (finProdFinEquiv (i,y)).val; simp [finProdFinEquiv_apply_val,h]
  · intro e; constructor
    · intro h; exact ⟨(finProdFinEquiv.symm e).2,by rw [←h]; exact finProdFinEquiv.apply_symm_apply e⟩
    · rintro ⟨j,rfl⟩; simp
private theorem addLocal {s : Shape} {n : ℕ} (v : Bool) (a b z c : Fin n → Ref s) (i : Fin n) (w : W) : let B := (NamedBlocks.add v a b z c).core; localCheck B.A B.t i w = CoreCheck.column n i ((a i).read (w.getD 0 false)) ((b i).read (w.getD 1 false)) ((z i).read (w.getD 2 false)) (if i.val=0 then v else (c (AddLayout.prev i)).read (w.getD 4 false)) ((c i).read (w.getD 3 false)) := by
  have H (j : Fin 5) : (gateEdges (AddLayout.layout n) i).idxOf (AddLayout.pos i j) = j.val := by
    apply fiberRank _ i (AddLayout.pos i) _ _ j
    · intro x y h; change 5*i.val+x.val < 5*i.val+y.val; omega
    · intro e; constructor
      · intro h; refine ⟨⟨e.val%5,by omega⟩,?_⟩; have hh := congrArg Fin.val h; change e.val/5=i.val at hh; apply Fin.ext; change 5*i.val+e.val%5=e.val; omega
      · rintro ⟨j,rfl⟩; exact AddLayout.col_pos ..
  have R (i : Fin n) (j : Fin 4) : colRef a b z c (AddLayout.reg i j) = (match j.val with | 0 => a i | 1 => b i | 2 => z i | _ => c i) := by
    have eq : (AddLayout.reg i j).val%4 = j.val := by change (4*i.val+j.val)%4=j.val; omega
    have eq' : (AddLayout.reg i j).val/4 = i.val := by change (4*i.val+j.val)/4=i.val; omega
    simp only [colRef,eq,eq']; fin_cases j <;> rfl
  unfold NamedBlocks.add mapped localCheck AddLayout.test; dsimp only; simp only [gateEdges,AddLayout.layout] at H ⊢; simp [AddLayout.bit_pos,CoreCheck.column,R,imp_iff_not_or]; erw [H 0,H 1,H 2,H 3,H 4]; rfl
private abbrev Reader := ℕ → Bool → Bool
private def regR (d : ℕ) : Reader := fun i b => decide (i<d) && b
private def pinR (k : ℕ) : Reader := fun i _ => k.testBit i
private def colC (n : ℕ) (v : Bool) (a b z : Reader) : Code := (n,fun i w => CoreCheck.column n i (a i (w.getD 0 false)) (b i (w.getD 1 false)) (z i (w.getD 2 false)) (if i=0 then v else w.getD 4 false) (w.getD 3 false))
private def prodC (q : List Unit) (d : ℕ) (a b z : Reader) : Code := cat (w4_M5GraphBounds.vertexCount d,fun i w => w4_M5Dispatch.evalNat q i (CoreCheck.reorder q i w)) (4*d,fun i w => decide (w.getD 0 false = (if i<d then a i (w.getD 1 false) else if i<2*d then b (i-d) (w.getD 1 false) else z (i-2*d) (w.getD 1 false))))
private def scanC (n : ℕ) (f : Bool → Bool) : Code := (n+1,fun i w => if i<n then decide (w.getD 2 false = ((if i=0 then f (w.getD 0 false) else w.getD 0 false) || w.getD 1 false)) else if i=0 then f (w.getD 0 false) else w.getD 0 false)
private def body (q : List Unit) (d e p T a b : ℕ) (η : W) : Code :=
  let r := fun k => colC (d+1) true (regR d) (regR d) (pinR k)
  let h := cat (cat (prodC q d (pinR a) (regR d) (regR (2*d))) (prodC q d (regR d) (pinR p) (regR (2*d)))) (cat (colC (2*d) false (regR (2*d)) (regR d) (regR (2*d))) (cat (colC (d+1) false (regR d) (pinR b) (regR (d+1))) (colC (d+1) false (regR d) (fun i x => p.testBit i && x) (regR (d+1)))))
  cat ((Routes.bank d e).size+1,fun _ _ => true) (cat (1,fun _ w => !w.getD 0 false) (cat (r p) (cat (r p) (cat (r p) (cat h (cat (r T) (cat (scanC d (fun _ => false)) (η.length,fun i w => decide (i<d-1 ∧ regR d (d-2-i) (w.getD 0 false) = η.getD i false)))))))))
private theorem colFits {s : Shape} {n : ℕ} (v : Bool) {a b z : Reader} {A B Z C : Fin n → Ref s} (ha : ∀ (i : Fin n) x, a i x = (A i).read x) (hb : ∀ (i : Fin n) x, b i x = (B i).read x) (hz : ∀ (i : Fin n) x, z i x = (Z i).read x) (hc : ∀ (i : Fin n) x, (C i).read x = x) : Fits (colC n v a b z) (NamedBlocks.add v A B Z C).core := ⟨rfl, fun i w => by rw [addLocal]; simp [colC,ha,hb,hz,hc]⟩
private theorem prodFits {s : Shape} {d : ℕ} (h : 1 ≤ d) {a b z : Reader} {A B Z : HashRows.Word s} {C : Fin (w3_fpMulLayout d h).nb → Addr s} (ha : ∀ i x, a i x = (A i).read x) (hb : ∀ i x, b i x = (B i).read x) (hz : ∀ i x, z i x = (Z i).read x)  : Fits (prodC (List.replicate d ()) d a b z) (HashRows.product h A B Z (fun i => .reg (C i))).core := by
  apply catFits
  · refine ⟨rfl,fun i w => ?_⟩; change w4_M5Dispatch.evalNat _ _ _ = _
    generalize hq : List.replicate d () = q; have hl : q.length=d := by simp [←hq]
    subst d
    exact (LocalGateEq.mul_register_local q h C i w).symm
  · refine ⟨rfl,fun i w => ?_⟩; unfold eqs; erw [rowsLocal]; simp [HashRows.busRef,Ref.read]; split_ifs <;> simp [ha,hb,hz,Ref.read]
private theorem scanFits {s : Shape} (n : ℕ) (x t : Fin n → Ref s) (c : Ref s) (hx : ∀ i b, (x i).read b=b) (ht : ∀ i b, (t i).read b=b) : Fits (scanC n c.read) (Routes.scan n x c t).core := by
  induction n generalizing c with
  | zero => refine ⟨rfl,fun i w => ?_⟩; fin_cases i; unfold Routes.scan; erw [rowsLocal]; rfl
  | succ n ih =>
    let row : Code := (1, fun _ w => decide (w.getD 2 false = (c.read (w.getD 0 false) || w.getD 1 false)))
    have hrow : Fits row (rows 1 3 (fun _ => ![c,x 0,t 0]) (fun _ v => decide (v 2 = (v 0 || v 1)))).core := by
      refine ⟨rfl,fun i w => ?_⟩; rw [rowsLocal]; simp [row,hx,ht]
    have H := catB hrow (ih (x ∘ Fin.succ) (t ∘ Fin.succ) (t 0) (fun j => hx j.succ) (fun j => ht j.succ))
    rw [Routes.scan]; convert H using 1; apply Prod.ext
    · change n+1+1=1+(n+1); omega
    · funext i w; simp [cat,row,scanC,ht]; split_ifs <;> (first | rfl | contradiction | (have : i=0 := by omega; simp_all) | omega)
private abbrev core (p T a b : ℕ) (η : W) := AnchoredLayout.block (Semantics.net p T a b η).core ((Routes.bank (d p) (e p)).size+1)
private abbrev wiring (p T a b : ℕ) (η : W) := AnchoredLayout.wiring (Semantics.net p T a b η).core (Semantics.net p T a b η).name
private theorem bodyFits (p T a b : ℕ) (η : W) : Fits (body (List.replicate (d p) ()) (d p) (e p) p T a b η) (core p T a b η) := by
  unfold body core AnchoredLayout.block Semantics.net Routes.network HashRows.block; dsimp only
  refine catFits (A:=⟨AnchoredLayout.anchors _,fun _ _ => true⟩) (B:=(Semantics.net p T a b η).core) ?_ ?_
  · exact ⟨rfl,fun _ _ => rfl⟩
  unfold Semantics.net Routes.network HashRows.block
  refine catB ?_ (catB ?_ (catB ?_ (catB ?_ (catB (catB (catB ?_ ?_) (catB ?_ (catB ?_ ?_))) (catB ?_ (catB ?_ ?_))))))
  · refine ⟨rfl,fun i w => ?_⟩; fin_cases i; rfl
  all_goals first | apply colFits | apply prodFits | apply scanFits | refine ⟨rfl,fun i w => ?_⟩
  all_goals try (unfold Routes.pref; erw [rowsLocal])
  all_goals intros; simp only [Routes.orp,Routes.wires,Routes.rw,GateRoutes.word,HashRows.padded,HashRows.pub,regR,pinR,RangeRows.pad,Ref.read]; try split_ifs <;> simp_all [Ref.read,List.getD_eq_getElem?_getD]
  all_goals have hi : i.val<η.length := i.isLt; simp_all [List.getElem?_eq_getElem] <;> first | rfl | omega
open S8H.PointAddresses DetDLP_W1_Queries M89S1
private def code (w : W) := let p := Packet.prime w; body (CoreCheck.pad p) (d p) (wires (d p)) p (Packet.threshold w) (Packet.coeff w 0) (Packet.coeff w 1) (Packet.pfx w)
private def check (z : S8H0.PortEval.Input) := if z.2.1 < (code z.1).1 then (code z.1).2 z.2.1 z.2.2 else S8H0.PortEval.agree z.2.2
def port := S8C.portPacket check
attribute [local fun_prop] first_poly more_poly w4_M5Evaluator.clog2_poly PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const PolyT.mul PolyT.length PolyT.getD PolyT.testBit PolyT.decide_lt PolyT.decide_eq CoreCheck.reorder_poly CoreCheck.column_poly CoreCheck.pad_poly w4_M5Dispatch.evalNat_poly w4_M5Evaluator.vertexCount_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219
private def Eff {α : Type} [Enc α] (f : α → Code) := (PolyT fun x => (f x).1) ∧ ∀ {i : α → ℕ} {w : α → W}, PolyT i → PolyT w → PolyT fun x => (f x).2 (i x) (w x)
private theorem catP {α : Type} [Enc α] {f g : α → Code} (h : Eff f) (k : Eff g) : Eff fun x => cat (f x) (g x) := ⟨PolyT.add h.1 k.1,fun hi hw => P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hi h.1) (h.2 hi hw) (k.2 (PolyT.sub hi h.1) hw)⟩
private theorem bodyP {α : Type} [Enc α] {q : α → List Unit} {D E P T A B : α → ℕ} {η : α → W} (hq : PolyT q) (hd : PolyT D) (he : PolyT E) (hp : PolyT P) (ht : PolyT T) (ha : PolyT A) (hb : PolyT B) (hf : PolyT η) : Eff fun x => body (q x) (D x) (E x) (P x) (T x) (A x) (B x) (η x) := by
  unfold body prodC; refine catP ?_ (catP ?_ (catP ?_ (catP ?_ (catP ?_ (catP (catP (catP (catP ?_ ?_) (catP ?_ ?_)) (catP ?_ (catP ?_ ?_))) (catP ?_ (catP ?_ ?_)))))))
  all_goals refine ⟨?_,fun hi hw => ?_⟩ <;> simp only [Routes.bank,Shape.size,RegisterMap.triple,run,RegisterMap.mul,GateRoutes.auxShape,colC,scanC,regR,pinR] <;> fun_prop (disch := assumption)
theorem port_poly : PolyT port := by
  let f := fun z : S8H0.PortEval.Input => z.1
  have hf : PolyT f := PolyT.fst PolyT.id'
  have hp := PolyT.comp S8G.FpMoment.Code.prime_poly hf
  have hd : PolyT fun x => d (Packet.prime (f x)) := by unfold d S8H.ECPointArithmetic.width bitLen; fun_prop
  have he := mul_poly.nb hd
  have ht := PolyT.comp S8G.FpMoment.Code.idx_poly hf
  have hη : PolyT Packet.pfx := by unfold Packet.pfx third second; fun_prop (disch := first | apply more_poly | apply first_poly)
  have H := bodyP (CoreCheck.pad_poly hp) hd he hp ht (PolyT.comp (Packet.coeff_poly 0) hf) (PolyT.comp (Packet.coeff_poly 1) hf) (PolyT.comp hη hf)
  apply S8C.portPacket_poly; exact P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt (PolyT.fst (PolyT.snd PolyT.id')) H.1) (H.2 (by fun_prop) (by fun_prop)) (PolyT.comp S8H0.PortEval.agree_poly (by fun_prop))
private theorem nonGate {k : ℕ} (B : Block) (W : Wiring B.A.ne k) (v : Fin (G B W).subdivision.nV) (a) (hv : ¬v.val<B.A.ng) : S8H0.PortEval.agree (List.ofFn a) = (G B W).subdivisionTensor (CircuitRealizes.T B W) v a := by
  induction v using Fin.addCases with
  | right e => exact S8H0.PortEval.edge_eq _ _ e a
  | left v => induction v using Fin.addCases with
    | left g => induction g using Fin.addCases with
      | left g => exact False.elim (hv g.isLt)
      | right b => exact S8H0.PortEval.cycle_eq B.A.gate W.next B.t b a
    | right b => exact S8H0.PortEval.bit_eq _ _ b a
open w4_M5Network in
theorem port_word {p m : ℕ} (T : ℕ) (S : FpSeed p m) (i : Fin m) (η : W) (v : Fin (w3_factorGraph (Semantics.layout p T ((S i).1.val+1) (S i).2.val η)).subdivision.nV) (a) : port (encodePortQuery (word T S i η) v.val (List.ofFn a)) = encodeNatListBin [if (w3_factorGraph (Semantics.layout p T ((S i).1.val+1) (S i).2.val η)).subdivisionTensor (w3_factorChecks _ (Semantics.tests p T ((S i).1.val+1) (S i).2.val η)) v a then 1 else 0] := by
  let C := core p T ((S i).1.val+1) (S i).2.val η; let W := wiring p T ((S i).1.val+1) (S i).2.val η
  have H : Fits (code (word T S i η)) C := by
    obtain ⟨hp,ht,_,_,hf⟩ := Packet.fields T S i η
    have hq : CoreCheck.pad p = List.replicate (d p) () := by
      have h : (CoreCheck.pad p).length=d p := by simp [CoreCheck.pad,d,S8H.ECPointArithmetic.width,←S8G.FpMoment.Code.width_eq,S8G.FpMoment.Code.width]
      rw [←h]; exact List.eq_replicate_of_mem (by simp)
    have h0 : Packet.coeff (word T S i η) 0 = (S i).1.val+1 := Packet.coeff_word T S i η (0 : Fin 2)
    have h1 : Packet.coeff (word T S i η) 1 = (S i).2.val := Packet.coeff_word T S i η (1 : Fin 2)
    simp only [code,hp,ht,hf,h0,h1,hq,wires_eq (hd p)]; exact bodyFits ..
  unfold port; rw [S8C.portPacket_eq]; suffices check (word T S i η,v.val,List.ofFn a) = (G C W).subdivisionTensor (CircuitRealizes.T C W) v a by rw [this]; rfl
  unfold check; dsimp only; rw [H.1]; split
  · rename_i hv; let g : Fin C.A.ng := ⟨v.val,hv⟩; exact (H.2 g _).trans (core_tensor C W g a)
  · exact nonGate C W v a (by assumption)
end DetDLP.S8C3.PortEval


