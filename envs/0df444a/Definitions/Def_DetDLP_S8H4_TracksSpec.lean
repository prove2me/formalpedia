-- Prove2me | Definitions.Def_DetDLP_S8H4_TracksSpec
-- name    : DetDLP_S8H4_TracksSpec
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T02:38:48.064812+00:00
-- url     : https://prove2.me/theorems/0591ac72-c708-5ee6-9833-b53faf906a03
-- title:
--   EC element signal-name specification
-- statement:
--   The computed address agrees with the anchored signal name at every edge of the element network.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H4_TracksHashSpec
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
namespace DetDLP.S8H4.TracksSpec
open Groundwork S8H0 S8H.PointAddresses GateRoutes GateSemantics PointGraph RegisterMap NamedBlocks TracksPoly
open TracksRowsSpec TracksHashSpec
set_option maxHeartbeats 3000000
private theorem base_ok {d} (hd : 1≤d) (p) (c : Coeff) : Tracks (baseR d (w4_M5GraphBounds.graph d hd).nE) (joinB (RangeRows.block _ _ p) (joinB (RangeRows.many 5 fun g => HashRows.block p (wires hd p c g.castSucc)) (CurveRows.block _ _))) := by
  apply cat_ok
  · apply cat_ok; all_goals first | apply many_ok; intro g; apply cat_ok | apply cat_ok
    all_goals apply plus_ok; intro j
    all_goals repeat' apply And.intro
    all_goals (
         try dsimp only [checkR,pad,RangeRows.checker,RangeRows.xa,RangeRows.ya,RangeRows.oa,RangeRows.ra,GateRoutes.wires,operands,rword,GateRoutes.word,HashRows.pub,quot,runPath,m1,m2,aux,cm,CurveRows.refs,CurveRows.flag,CurveRows.xbit,CurveRows.ybit,CurveRows.outbit,Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,Fin.ofNat,Fin.succ]
         try simp only [eq_mpr_eq_cast,cast_eq,padded_val,rpad_val,pad]
         try split
         all_goals try simp_all only [↓reduceDIte,↓reduceIte]
         all_goals try dsimp only [GateSemantics.e,GateRoutes.S,Ref.source,Addr.index,Fin.castSucc,Fin.castAdd,Fin.natAdd,finProdFinEquiv,start,top,headN,TracksPoly.tri,bank,run,triple,RegisterMap.mul,auxShape,Shape.size,Fin.castLE,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,EquivLike.coe,Fin.last]
         all_goals first | rfl | omega)
  · apply cat_ok (many_ok _ _ _ fun g => hash_ok hd p c g.castSucc); refine ⟨rfl,?_⟩; intro i
    obtain ⟨⟨j,k⟩,rfl⟩ := finProdFinEquiv.surjective i; fin_cases k <;> simp [curveR,CurveRows.block,rows,mapped,finProdFinEquiv_apply_val,show ∀ k : Fin 5, (k.val+5*j.val)/5=j.val by intro k; omega] <;> (
         try dsimp only [checkR,pad,RangeRows.checker,RangeRows.xa,RangeRows.ya,RangeRows.oa,RangeRows.ra,GateRoutes.wires,operands,rword,GateRoutes.word,HashRows.pub,quot,runPath,m1,m2,aux,cm,CurveRows.refs,CurveRows.flag,CurveRows.xbit,CurveRows.ybit,CurveRows.outbit,Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,Fin.ofNat,Fin.succ]
         try simp only [eq_mpr_eq_cast,cast_eq,padded_val,rpad_val,pad]
         try split
         all_goals try simp_all only [↓reduceDIte,↓reduceIte]
         all_goals try dsimp only [GateSemantics.e,GateRoutes.S,Ref.source,Addr.index,Fin.castSucc,Fin.castAdd,Fin.natAdd,finProdFinEquiv,start,top,headN,TracksPoly.tri,bank,run,triple,RegisterMap.mul,auxShape,Shape.size,Fin.castLE,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,EquivLike.coe,Fin.last]
         all_goals first | rfl | omega)
private theorem size_eq (d e) : (Routes.bank d e).size = newTop d e := by change top d e + (d+(d+(d+(d+1)))) = _; unfold newTop; omega
private theorem remap_ok {d e} {a : R} {b : B (top d e+1)} (h : Tracks a b) : Tracks (remap a (top d e) (newTop d e)) ⟨b.core, Routes.network.embed ∘ b.name⟩ := by
  refine ⟨h.1,fun i => ?_⟩; simp only [remap,h.2,Function.comp_apply]; generalize b.name i=j
  induction j using Fin.lastCases with
  | last => simp only [Fin.val_last,ite_true, ↓reduceIte]; exact (size_eq ..).symm.trans (congrArg Fin.val (Fin.lastCases_last (motive:=fun _ : Fin (top d e+1) => Fin ((Routes.bank d e).size+1)) (last:=Fin.last _) (cast:=fun i => (i.castAdd _).castSucc))).symm
  | cast j => simp only [Fin.val_castSucc,if_neg (Nat.ne_of_lt j.isLt)]; exact (congrArg Fin.val (Fin.lastCases_castSucc (motive:=fun _ : Fin (top d e+1) => Fin ((Routes.bank d e).size+1)) (last:=Fin.last _) (cast:=fun i => (i.castAdd _).castSucc) j)).symm
private theorem digit_ok {d e b} (hb : b≤d) (i : ℕ) : (preR d e b 0).2 i = ((Routes.network.digits (d:=d) (e:=e) b)[i]?.getD (.pin false)).source.val := by
  cases i with
  | zero => rfl
  | succ i =>
    simp only [preR,Nat.succ_ne_zero,if_false,Nat.add_one_sub_one,Routes.network.digits,List.getElem?_cons_succ,List.getElem?_append,List.length_ofFn,List.getElem?_ofFn]
    split_ifs <;> simp_all (config := {failIfUnchanged := false}) only [↓reduceDIte,↓reduceIte,Option.getD_some,Option.getD_none,Routes.network.coord,GateRoutes.word,HashRows.padded,Fin.val_rev] <;> (try split_ifs) <;> dsimp only [Ref.source,Addr.index,Fin.castAdd,Fin.castSucc,Fin.castLE,Fin.natAdd,Fin.last,RangeRows.xa,RangeRows.ya,Routes.bank,Shape.size,newTop,TracksPoly.tri,top] <;> omega
private theorem body_ok {d} (hd : 1≤d) (p T a0 b0 a1 b1) (hb : bitLen p ≤ d) (c : Coeff) (η : List Bool) : let e := (w4_M5GraphBounds.graph d hd).nE; Tracks (cat (remap (baseR d e) (top d e) (newTop d e)) (cat (hash6R d e) (cat (muxR d e) (cat (flagR d e) (cat (ltR d e) (preR d e (bitLen p) η.length)))))) (Routes.network hd p T a0 b0 a1 b1 c η) := by
  refine cat_ok (remap_ok (base_ok hd p c)) (cat_ok (hash6_ok hd p c) (cat_ok ?_ (cat_ok ⟨rfl,fun _ => rfl⟩ (cat_ok (plus_ok _ ?_) ?_))))
  · refine ⟨rfl,?_⟩; intro i; obtain ⟨⟨j,k⟩,rfl⟩ := finProdFinEquiv.surjective i; fin_cases k <;> simp [muxR,rows,mapped,finProdFinEquiv_apply_val,show ∀ k : Fin 3,(k.val+3*j.val)/3=j.val by intro k; omega,Routes.network.coord,GateRoutes.word,HashRows.padded,show 0<d by omega,Routes.network.a6Reg,Routes.network.b6Reg,Ref.source,Addr.index,RangeRows.ya,Shape.size,top,TracksPoly.tri,Fin.castSucc,Fin.castAdd,Fin.natAdd] <;> dsimp only [Fin.castLE] <;> omega
  · intro j; repeat' apply And.intro
    all_goals try simp only [pad,rpad_val]
    all_goals (try split) <;> (try simp_all only [↓reduceDIte,↓reduceIte]) <;> dsimp only [Ref.source,Addr.index,Fin.natAdd,Fin.castAdd,Fin.castSucc,Fin.castLE,Fin.last,RangeRows.oa,Routes.bank,newTop,top,start,headN,TracksPoly.tri,Shape.size,finProdFinEquiv,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,EquivLike.coe] <;> omega
  · refine ⟨by simp [preR,rows,mapped],?_⟩; intro i; obtain ⟨⟨j,k⟩,rfl⟩ := finProdFinEquiv.surjective i; fin_cases k; simpa [preR,rows,mapped,finProdFinEquiv_apply_val] using digit_ok (e:=(w4_M5GraphBounds.graph d hd).nE) hb j.val
private abbrev net (p T a0 b0 a1 b1) (c : Coeff) (η : List Bool) := joinB (PointGraph.zeroLast (Routes.bank (d p) (e p)).size) (Routes.network (hd p) p T a0 b0 a1 b1 c η)
private theorem net_ok (p T a0 b0 a1 b1) (c : Coeff) (η : List Bool) : let n := net p T a0 b0 a1 b1 c η; Tracks (route (d p) (e p) (bitLen p) η.length) ⟨AnchoredLayout.block n.core _,AnchoredLayout.signal n.core n.name⟩ := by
  let anchor (k : ℕ) : B k := ⟨⟨AnchoredLayout.anchors k,fun _ _ => true⟩,id⟩
  change Tracks _ (joinB (anchor _) (net p T a0 b0 a1 b1 c η)); exact cat_ok ⟨congrArg (·+1) (size_eq ..).symm,fun _ => rfl⟩ (cat_ok ⟨rfl,fun _ => (size_eq ..).symm⟩ (body_ok (hd p) p T a0 b0 a1 b1 (Nat.le_succ _) c η))
theorem sigNat_spec (p T a0 b0 a1 b1) (c : Coeff) (η : List Bool) : let n := joinB (PointGraph.zeroLast (Routes.bank (d p) (e p)).size) (Routes.network (hd p) p T a0 b0 a1 b1 c η); ∀ i : Fin (AnchoredLayout.block n.core ((Routes.bank (d p) (e p)).size+1)).A.ne, sigNat (d p) (e p) (bitLen p) η.length i.val = (AnchoredLayout.signal n.core n.name i).val := (net_ok p T a0 b0 a1 b1 c η).2
end DetDLP.S8H4.TracksSpec


