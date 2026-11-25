-- Prove2me | Definitions.Def_DetDLP_S8H0_OrderMake
-- name    : DetDLP_S8H0_OrderMake
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T09:37:33.063718+00:00
-- url     : https://prove2.me/theorems/ae84bc17-57f2-4205-82d5-4c76ed0349d1
-- title:
--   Tag 0 uniform PolyT BTN instance builder
-- statement:
--   Constructs the explicit arithmetic register-name table and uniform polynomial-time BTN instance packet builder for Tag 0 elliptic curve point-counting queries.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_BaseCode
import Definitions.Def_DetDLP_S8H0_OrderPacket
import Definitions.Def_DetDLP_S8H_WirePacket
import Definitions.Def_DetDLP_S8H0_GraphBudget
set_option autoImplicit false
namespace DetDLP.S8H0.OrderMake
open Groundwork S8H.PointAddresses GateRoutes GateSemantics PointGraph RegisterMap NamedBlocks BaseCode
private abbrev R := ℕ × (ℕ → ℕ)
private def cat (a b : R) : R := (a.1+b.1, fun i => if i<a.1 then a.2 i else b.2 (i-a.1))
private def seven : (n : ℕ) → (Fin (n+1) → R) → R | 0,f => f 0 | n+1,f => cat (f 0) (seven n fun g => f g.succ)
private def plusRows (n : ℕ) (a b z c : ℕ → ℕ) : R := (n*5, fun i => let k := (S8H.PointAddresses.add n).bit i; let j := k/4
  if k%4=0 then a j else if k%4=1 then b j else if k%4=2 then z j else c j)
private def pad (n t off i : ℕ) := if i<n then off+i else t
private abbrev top (d e : ℕ) := (bank d e).size
private abbrev tri (d : ℕ) := (triple d).size
private abbrev headN (d : ℕ) := 1+(tri d+tri d)
private abbrev start (d e : ℕ) (g : Fin 7) := headN d + (run d e).size*g.val
private def checkR (d e off : ℕ) : R := plusRows (d+1) (pad d (top d e) off) (pad d (top d e) (off+d)) (fun _ => top d e) (fun i => (off+d)+d+i)
private def prodR (d e off : ℕ) (a b z : ℕ → ℕ) : R := cat (e+e, fun i => off+(if i<e then i else i-e)) ((4*d)*2,fun i => let j := i/2; if i%2=0 then off+(if j<2*d then j else e-2*d+(j-2*d)) else if j<d then a j else if j<2*d then b (j-d) else z (j-2*d))
private def hashR (d e : ℕ) (g : Fin 7) : R := Id.run do
  let t := top d e; let pub := fun _ : ℕ => t; let w := pad d t; let o := start d e; let r := o g + tri d; let q := r+tri d; let m := q+d; let m' := m+(2*d+e); let u := headN d+7*(run d e).size+(auxShape d).size*g.val
  let (a,x,b) := ![(pub,w 1,w (1+tri d)),(pub,w (o 0),pub),(w (o 1),w (1+tri d),pub),(pub,w 1,pub), (w (o 3),w 1,pub),(w (o 4),w 1,pub),(pub,w 1,pub)] g
  let p1 := pad (2*d) t m; let p2 := pad (2*d) t m'; let s := pad (d+1) t (u+2*d)
  return cat (cat (prodR d e (m+2*d) a x p1) (prodR d e (m'+2*d) (w q) pub p2))
    (cat (plusRows (2*d) p2 (w r) p1 (u+·)) (cat (plusRows (d+1) (w r) b s (u+2*d+(d+1)+·)) (plusRows (d+1) (w (o g)) (fun _ => m'+(2*d+e)) s (u+2*d+(d+1)+(d+1)+·))))
private def route (d e : ℕ) : R := let t := top d e; let f := checkR d e; let o := start d e; let ranges := cat (cat (f 1) (f (1+tri d))) (seven 6 fun g => cat (f (o g)) (f (o g+tri d)))
  let curve : R := (d*5,fun i => let j := i/5; if i%5=0 then 0 else if i%5=1 then 1+j else if i%5=2 then 1+tri d+j else if i%5=3 then o 2+j else o 5+j); cat (t+1,id) (cat (1,fun _ => t) (cat ranges (cat (seven 6 (hashR d e)) curve)))
def sigNat (d e i : ℕ) := (route d e).2 i
private def Tracks {k : ℕ} (a : R) (b : B k) := a.1=b.core.A.ne ∧ ∀ i, a.2 i.val=(b.name i).val
private theorem cat_ok {k} {a b : R} {u v : B k} (h : Tracks a u) (j : Tracks b v) : Tracks (cat a b) (joinB u v) := by
  refine ⟨congrArg₂ Nat.add h.1 j.1,?_⟩; intro i; induction i using Fin.addCases with
  | left i => simpa [cat,joinB,h.1,i.isLt] using h.2 i | right i => simpa [cat,joinB,h.1] using j.2 i
private theorem seven_ok {k} (n) (f : Fin (n+1) → R) (b : Fin (n+1) → B k) (h : ∀ g, Tracks (f g) (b g)) : Tracks (seven n f) (RangeRows.many n b) := by induction n with | zero => exact h 0 | succ n ih => exact cat_ok (h 0) (ih _ _ fun _ => h _)
private theorem plus_ok {s n} {a b z c : ℕ → ℕ} {A B Z C : Fin n → Ref s} (v : Bool) (h : ∀ j : Fin n, a j=(A j).source.val ∧ b j=(B j).source.val ∧ z j=(Z j).source.val ∧ c j=(C j).source.val) : Tracks (plusRows n a b z c) (NamedBlocks.add v A B Z C) := by
  refine ⟨rfl,?_⟩; intro i; simp only [plusRows,(add_spec n).bit i,NamedBlocks.add,mapped,colRef]; generalize (S8C.AddLayout.layout n).bit i=k; generalize hj : k.val%4=l; have hl : l<4 := hj ▸ Nat.mod_lt _ (by decide); have H := h (⟨k.val/4,by have := k.isLt; change _<n*4 at this; omega⟩ : Fin n); interval_cases l <;> norm_num <;> tauto
private theorem ext_val {d} (hd : 1≤d) (i : Fin (4*d)) : (w4_M5PortTensor.ext hd i).val = if i.val<2*d then i.val else (w4_M5GraphBounds.graph d hd).nE-2*d+(i.val-2*d) := by
  unfold w4_M5PortTensor.ext w4_M5PortTensor.extEdge; split
  · rw [if_pos (by omega)]; change i.val+d*0=i.val; omega
  · split
    · change i.val-d+d*1=i.val; omega
    · change _ = w4_M5GraphBounds.edgeCount d _-2*d+_; unfold w4_M5GraphBounds.edgeCount; change 2*d+(_+(_+(_+(_+(_+(_+(_+(_+(i.val-2*d))))))))) = _; omega
private theorem prod_ok {s d} {hd : 1≤d} {off} {a b z : ℕ → ℕ} {A B Z : HashRows.Word s} {W : Fin (w3_fpMulLayout d hd).nb → Ref s} (h : ∀ j, a j=(A j).source.val ∧ b j=(B j).source.val ∧ z j=(Z j).source.val) (hw : ∀ j, off+j.val=(W j).source.val) : Tracks (prodR d (w4_M5GraphBounds.graph d hd).nE off a b z) (HashRows.product hd A B Z W) := by
  apply cat_ok <;> refine ⟨rfl,?_⟩
  · intro i; have H := hw ((w3_fpMulLayout d hd).bit i); rw [← (mul_spec hd).bit i] at H; simpa only [S8H.PointAddresses.mul,wires_eq hd,mapped] using H
  · intro i; obtain ⟨⟨j,k⟩,rfl⟩ := finProdFinEquiv.surjective i; fin_cases k <;> simp [eqs,rows,mapped,HashRows.busRef,finProdFinEquiv_apply_val,show (1+2*j.val)/2=j.val by omega]
    · simpa only [ext_val] using hw (w4_M5PortTensor.ext hd j)
    · split <;> first | exact (h _).1 | split <;> first | exact (h _).2.1 | exact (h _).2.2
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
private theorem padded_val {s n} (f : Fin n → Ref s) (j) : (HashRows.padded f j).source.val = if h:j<n then (f ⟨j,h⟩).source.val else s.size := by unfold HashRows.padded; split <;> rfl
private theorem rpad_val {s n m} (f : Fin n → Ref s) (j : Fin m) : (RangeRows.pad f j).source.val = if h:j.val<n then (f ⟨j,h⟩).source.val else s.size := by unfold RangeRows.pad; split <;> rfl
private theorem hash_ok {d} (hd : 1≤d) (p) (c : Coeff) (g) : Tracks (hashR d (w4_M5GraphBounds.graph d hd).nE g) (HashRows.block p (wires hd p c g)) := by
  dsimp only [hashR,Id.run,HashRows.block]; refine cat_ok (cat_ok (prod_ok ?_ ?_) (prod_ok ?_ ?_)) (cat_ok (plus_ok _ ?_) (cat_ok (plus_ok _ ?_) (plus_ok _ ?_)))
  all_goals intro j; repeat' apply And.intro
  case refine_1.left | refine_1.right.left | refine_6.right.left => fin_cases g <;> (
       try dsimp only [checkR,pad,RangeRows.checker,RangeRows.xa,RangeRows.ya,RangeRows.oa,RangeRows.ra,GateRoutes.wires,operands,rword,GateRoutes.word,HashRows.pub,quot,runPath,m1,m2,aux,cm,CurveRows.refs,CurveRows.flag,CurveRows.xbit,CurveRows.ybit,CurveRows.outbit,Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,Fin.ofNat,Fin.succ]
       try simp only [eq_mpr_eq_cast,cast_eq,padded_val,rpad_val,pad]
       try split
       all_goals try simp_all only [↓reduceDIte,↓reduceIte]
       all_goals try dsimp only [GateSemantics.e,Ref.source,Addr.index,Fin.castSucc,Fin.castAdd,Fin.natAdd,finProdFinEquiv,start,top,headN,tri,bank,run,triple,RegisterMap.mul,auxShape,Shape.size,Fin.castLE,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,EquivLike.coe,Fin.last]
       all_goals first | rfl | omega)
  all_goals (
       try dsimp only [checkR,pad,RangeRows.checker,RangeRows.xa,RangeRows.ya,RangeRows.oa,RangeRows.ra,GateRoutes.wires,operands,rword,GateRoutes.word,HashRows.pub,quot,runPath,m1,m2,aux,cm,CurveRows.refs,CurveRows.flag,CurveRows.xbit,CurveRows.ybit,CurveRows.outbit,Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,Fin.ofNat,Fin.succ]
       try simp only [eq_mpr_eq_cast,cast_eq,padded_val,rpad_val,pad]
       try split
       all_goals try simp_all only [↓reduceDIte,↓reduceIte]
       all_goals try dsimp only [GateSemantics.e,Ref.source,Addr.index,Fin.castSucc,Fin.castAdd,Fin.natAdd,finProdFinEquiv,start,top,headN,tri,bank,run,triple,RegisterMap.mul,auxShape,Shape.size,Fin.castLE,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,EquivLike.coe,Fin.last]
       all_goals first | rfl | omega)
private theorem net_ok (p) (c : Coeff) : Tracks (route (d p) (e p)) ⟨C p c,AnchoredLayout.signal (net p c).core (net p c).name⟩ := by
  let anchor (k : ℕ) : B k := ⟨⟨AnchoredLayout.anchors k,fun _ _ => true⟩,id⟩
  change Tracks _ (joinB (anchor _) (net p c)); apply cat_ok ⟨rfl,fun _ => rfl⟩; apply cat_ok ⟨rfl,fun _ => rfl⟩; apply cat_ok
  · apply cat_ok; all_goals first | apply seven_ok; intro g; apply cat_ok | apply cat_ok
    all_goals apply plus_ok; intro j
    all_goals repeat' apply And.intro
    all_goals (
         try dsimp only [checkR,pad,RangeRows.checker,RangeRows.xa,RangeRows.ya,RangeRows.oa,RangeRows.ra,GateRoutes.wires,operands,rword,GateRoutes.word,HashRows.pub,quot,runPath,m1,m2,aux,cm,CurveRows.refs,CurveRows.flag,CurveRows.xbit,CurveRows.ybit,CurveRows.outbit,Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,Fin.ofNat,Fin.succ]
         try simp only [eq_mpr_eq_cast,cast_eq,padded_val,rpad_val,pad]
         try split
         all_goals try simp_all only [↓reduceDIte,↓reduceIte]
         all_goals try dsimp only [GateSemantics.e,Ref.source,Addr.index,Fin.castSucc,Fin.castAdd,Fin.natAdd,finProdFinEquiv,start,top,headN,tri,bank,run,triple,RegisterMap.mul,auxShape,Shape.size,Fin.castLE,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,EquivLike.coe,Fin.last]
         all_goals first | rfl | omega)
  · apply cat_ok (seven_ok _ _ _ fun g => hash_ok (hd p) p c g); refine ⟨rfl,?_⟩; intro i
    obtain ⟨⟨j,k⟩,rfl⟩ := finProdFinEquiv.surjective i; fin_cases k <;> simp [CurveRows.block,rows,mapped,finProdFinEquiv_apply_val,show ∀ k : Fin 5, (k.val+5*j.val)/5=j.val by intro k; omega] <;> (
         try dsimp only [checkR,pad,RangeRows.checker,RangeRows.xa,RangeRows.ya,RangeRows.oa,RangeRows.ra,GateRoutes.wires,operands,rword,GateRoutes.word,HashRows.pub,quot,runPath,m1,m2,aux,cm,CurveRows.refs,CurveRows.flag,CurveRows.xbit,CurveRows.ybit,CurveRows.outbit,Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,Fin.ofNat,Fin.succ]
         try simp only [eq_mpr_eq_cast,cast_eq,padded_val,rpad_val,pad]
         try split
         all_goals try simp_all only [↓reduceDIte,↓reduceIte]
         all_goals try dsimp only [GateSemantics.e,Ref.source,Addr.index,Fin.castSucc,Fin.castAdd,Fin.natAdd,finProdFinEquiv,start,top,headN,tri,bank,run,triple,RegisterMap.mul,auxShape,Shape.size,Fin.castLE,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,EquivLike.coe,Fin.last]
         all_goals first | rfl | omega)
theorem sigNat_spec (p) (c : Coeff) (i : Fin (C p c).A.ne) : sigNat (d p) (e p) i.val=sigName p c i.val := (net_ok p c).2 i |>.trans (sigName_spec ..).symm
attribute [local fun_prop] PolyT.mul PolyT.div PolyT.mod PolyT.sub PolyT.ite' PolyT.decide_lt PolyT.decide_eq PolyT.const PolyT.comp PolyT.id' PolyT.fst PolyT.snd w4_M5Evaluator.clog2_poly
private def Good {α} [Enc α] (f : α → R) := PolyT (fun x => (f x).1) ∧ ∀ i : α → ℕ, PolyT i → PolyT fun x => (f x).2 (i x)
private theorem catP {α} [Enc α] {a b : α → R} (h : Good a) (j : Good b) : Good fun x => cat (a x) (b x) := by refine ⟨PolyT.add h.1 j.1,fun i hi => PolyT.ite' (PolyT.decide_lt hi h.1) (h.2 _ hi) (j.2 _ (PolyT.sub hi h.1))⟩
private theorem sevenP {α} [Enc α] (n) (f : α → Fin (n+1) → R) (h : ∀ g, Good fun x => f x g) : Good fun x => seven n (f x) := by induction n with | zero => exact h 0 | succ n ih => exact catP (h 0) (ih _ fun g => h g.succ)
private abbrev PW {α} [Enc α] (f : α → ℕ → ℕ) := ∀ {i : α → ℕ}, PolyT i → PolyT fun x => f x (i x)
private theorem plusP {α} [Enc α] {n : α → ℕ} {a b z c : α → ℕ → ℕ} (hn : PolyT n) (ha : PW a) (hb : PW b) (hz : PW z) (hc : PW c) : Good fun x => plusRows (n x) (a x) (b x) (z x) (c x) := by
  refine ⟨PolyT.mul hn (PolyT.const 5),?_⟩; intro i hi; let k x := (S8H.PointAddresses.add (n x)).bit (i x); have hk := add_poly id (by intros; assumption) |>.bit hn hi; have h : PolyT k := hk; have j := PolyT.div h (PolyT.const 4); have m := PolyT.mod h (PolyT.const 4)
  exact PolyT.ite' (PolyT.decide_eq m (PolyT.const 0)) (ha j) (PolyT.ite' (PolyT.decide_eq m (PolyT.const 1)) (hb j) (PolyT.ite' (PolyT.decide_eq m (PolyT.const 2)) (hz j) (hc j)))
private theorem prodP {α} [Enc α] {d e o : α → ℕ} {a b z : α → ℕ → ℕ} (hd : PolyT d) (he : PolyT e) (ho : PolyT o) (ha : PW a) (hb : PW b) (hz : PW z) : Good fun x => prodR (d x) (e x) (o x) (a x) (b x) (z x) := by
  apply catP
  · exact ⟨PolyT.add he he,fun i hi => PolyT.add ho (PolyT.ite' (PolyT.decide_lt hi he) hi (PolyT.sub hi he))⟩
  · refine ⟨by dsimp; fun_prop,fun i hi => ?_⟩; have j := PolyT.div hi (PolyT.const 2); have t := PolyT.mul (PolyT.const 2) hd
    exact PolyT.ite' (PolyT.decide_eq (PolyT.mod hi (PolyT.const 2)) (PolyT.const 0)) (PolyT.add ho (PolyT.ite' (PolyT.decide_lt j t) j (PolyT.add (PolyT.sub he t) (PolyT.sub j t)))) (PolyT.ite' (PolyT.decide_lt j hd) (ha j) (PolyT.ite' (PolyT.decide_lt j t) (hb (PolyT.sub j hd)) (hz (PolyT.sub j t))))
theorem sigNat_poly {α} [Enc α] {D E I : α → ℕ} (hD : PolyT D) (hE : PolyT E) (hI : PolyT I) : PolyT fun x => sigNat (D x) (E x) (I x) := by
  have hc (off : α → ℕ) (h : PolyT off) : Good fun x => checkR (D x) (E x) (off x) := by apply plusP <;> (
       try unfold PW
       intros
       try dsimp only [pad,start,headN,tri,top,bank,run,triple,RegisterMap.mul,auxShape,Shape.size,Id.run]
       fun_prop (disch := solve_by_elim))
  have hh (g : Fin 7) : Good fun x => hashR (D x) (E x) g := by
    fin_cases g <;> refine catP (catP (prodP ?_ ?_ ?_ ?_ ?_ ?_) (prodP ?_ ?_ ?_ ?_ ?_ ?_)) (catP (plusP ?_ ?_ ?_ ?_ ?_) (catP (plusP ?_ ?_ ?_ ?_ ?_) (plusP ?_ ?_ ?_ ?_ ?_))) <;> (
         try unfold PW
         intros
         try dsimp only [pad,start,headN,tri,top,bank,run,triple,RegisterMap.mul,auxShape,Shape.size,Id.run]
         fun_prop (disch := solve_by_elim))
  have hr : Good fun x => route (D x) (E x) := by
    refine catP ?_ (catP ?_ (catP (catP (catP (hc _ ?_) (hc _ ?_)) (sevenP _ _ fun g => catP (hc _ ?_) (hc _ ?_))) (catP (sevenP _ _ hh) ?_))) <;> first
      | constructor <;> (
         try unfold PW
         intros
         try dsimp only [pad,start,headN,tri,top,bank,run,triple,RegisterMap.mul,auxShape,Shape.size,Id.run]
         fun_prop (disch := solve_by_elim))
      | (
         try unfold PW
         intros
         try dsimp only [pad,start,headN,tri,top,bank,run,triple,RegisterMap.mul,auxShape,Shape.size,Id.run]
         fun_prop (disch := solve_by_elim))
  exact hr.2 I hI
open DetDLP_W1_Queries M89S1 S8H S8C OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
private abbrev W := List Bool
private def field (w : W) := first (second w)
private def prime (w : W) := PolyT.bval (field w)
private abbrev code (p : ℕ) := CycleCode.code (baseCode p) (sigNat (d p) (e p))
def make (w : W) := let p := prime w; let a := code p; outerPacket w (WirePacket.packet (a.ng+a.nb) a.ne a.gate (fun i => a.ng+a.bit i)) (OrderPacket.scale (bitLen p))
private theorem small {f : W → ℕ} (h : PolyT f) (b : ∀ w, f w ≤ 4*OrderPacket.scale (bitLen (prime w))) : Unary f := by
  have hf : PolyT field := first_poly (first_poly (more_poly PolyT.id'))
  let l (w : W) := ((field w)++[false,false]).flatMap fun _ => List.replicate 4194304 (); have hl : PolyT l := PolyT.flatMap (PolyT.const _) (PolyT.append hf (PolyT.const _))
  have H (w : W) : f w ≤ (l w).length := by
    have hb : bitLen (prime w) ≤ (field w).length := Nat.clog_le_of_le_pow (PolyT.bval_lt (field w)).le; specialize b w
    simp only [l,List.length_flatMap,List.map_const',List.sum_replicate_nat,List.length_replicate,List.length_append,List.length_cons,List.length_nil] ; change f w ≤ ((field w).length+2)*4194304; apply b.trans; unfold OrderPacket.scale; rw [← Nat.mul_assoc,Nat.mul_comm ((field w).length+2)]; exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hb 2)
  simpa only [Nat.min_eq_left (H _)] using PolyT.unary_min_length h hl
theorem make_poly : PolyT make := by
  have hp : PolyT prime := by unfold prime field second; apply PolyT.comp (f:=PolyT.bval) _ (first_poly (first_poly (more_poly PolyT.id'))); fun_prop
  let f := fun w => baseCode (prime w); have g := uniform.ng hp; have n := uniform.ne hp; have ga := PolyT.add g n; have N := PolyT.add n (PolyT.add n n); have V := PolyT.add ga n
  have bounds (w : W) := And.intro (GraphBudget.gateBudget (prime w) ⟨0,0,0,0,0⟩) (GraphBudget.edgeBudget (prime w) ⟨0,0,0,0,0⟩)
  have bound (w : W) : let a := f w; a.ng+a.ne ≤ OrderPacket.scale (bitLen (prime w)) ∧ 2*(a.ne+(a.ne+a.ne)) < OrderPacket.scale (bitLen (prime w)) := by
    have M := cycle_models (prime w) ⟨0,0,0,0,0⟩; exact ⟨M.ng.trans_le (bounds w).1,by have H := (bounds w).2; rw [← M.ne] at H; exact H⟩
  have bo {a b s : ℕ} (h : a+b ≤ s ∧ 2*(b+(b+b))<s) : b≤4*s ∧ a+b+b+(b+(b+b))≤4*s ∧ (b+(b+b))+(b+(b+b))≤4*s := by omega
  have hs : PolyT fun z : W × ℕ => sigNat (d (prime z.1)) (e (prime z.1)) z.2 := by
    have h : PolyT fun z : W × ℕ => d (prime z.1) := by unfold d ECPointArithmetic.width bitLen; fun_prop
    apply sigNat_poly h _ (PolyT.snd PolyT.id'); exact (mul_poly.nb h).congr fun z => wires_eq (hd _) 
  have H := CycleCode.endpoints_poly (c:=f) (name:=fun w => sigNat (d (prime w)) (e (prime w))) g n (small n fun w => (bo (bound w)).1) (uniform.gate (PolyT.comp hp (PolyT.fst PolyT.id')) (PolyT.snd PolyT.id')) hs
  have s : PolyT fun w => OrderPacket.scale (bitLen (prime w)) := by unfold OrderPacket.scale bitLen; fun_prop
  have gg := PolyT.comp ga (PolyT.fst (PolyT.id' (α:=W × ℕ))); have dst := PolyT.add gg H.2
  exact outerPacket_poly PolyT.id' (WirePacket.packet_poly (src:=fun w => (code (prime w)).gate) (dst:=fun w i => (code (prime w)).ng+(code (prime w)).bit i) V N (small (PolyT.add V N) fun w => (bo (bound w)).2.1) (small (PolyT.add N N) fun w => (bo (bound w)).2.2) H.1 dst) s
theorem make_word (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) : make (OrderPacket.word E) = encodeBTNInstance (OrderPacket.word E) (w3_factorGraph (layout p (coeff E))).subdivision (OrderPacket.scale (bitLen p)) (OrderPacket.scale (bitLen p)) 1 := by
  have hp : prime (OrderPacket.word E)=p := by simp [prime,field,second,OrderPacket.word,queryWord,encodeCurveInput,encodeNatListBin]
  have M := CycleCode.packetEndpoints (models p (coeff E)) (sigNat (d p) (e p)); dsimp only at M
  have hn := AnchoredLayout.next_congr (fun i : Fin (C p (coeff E)).A.ne => sigNat (d p) (e p) i.val) (AnchoredLayout.signal (net p (coeff E)).core (net p (coeff E)).name) (by intro i j; rw [sigNat_spec,sigNat_spec,sigName_spec,sigName_spec]; exact Fin.val_inj)
  rw [hn] at M; simp only [make,hp,code]; rw [M.1,M.2.1,WirePacket.packet_eq _ _ _ M.2.2.1 M.2.2.2]; exact outerPacket_eq ..
end DetDLP.S8H0.OrderMake


