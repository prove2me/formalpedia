-- Prove2me | Definitions.Def_DetDLP_S8H4_TracksHashSpec
-- name    : DetDLP_S8H4_TracksHashSpec
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T02:19:06.221998+00:00
-- url     : https://prove2.me/theorems/b92331b6-c679-5f6c-85fe-fbee3cc8ad53
-- title:
--   Signal names in EC hash blocks
-- statement:
--   Both kinds of hash block use the computed natural-number addresses.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H4_TracksRowsSpec
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
namespace DetDLP.S8H4.TracksHashSpec
open Groundwork S8H0 S8H.PointAddresses GateRoutes GateSemantics PointGraph RegisterMap NamedBlocks TracksPoly
open TracksRowsSpec
set_option maxHeartbeats 3000000
theorem hash_ok {d} (hd : 1≤d) (p) (c : Coeff) (g) : Tracks (hashR d (w4_M5GraphBounds.graph d hd).nE g) (HashRows.block p (wires hd p c g)) := by
  dsimp only [hashR,hashR',Id.run,HashRows.block]; refine cat_ok (cat_ok (prod_ok ?_ ?_) (prod_ok ?_ ?_)) (cat_ok (plus_ok _ ?_) (cat_ok (plus_ok _ ?_) (plus_ok _ ?_)))
  all_goals intro j; repeat' apply And.intro
  case refine_1.left | refine_1.right.left | refine_6.right.left => fin_cases g <;> (
       try dsimp only [checkR,pad,RangeRows.checker,RangeRows.xa,RangeRows.ya,RangeRows.oa,RangeRows.ra,GateRoutes.wires,operands,rword,GateRoutes.word,HashRows.pub,quot,runPath,m1,m2,aux,cm,CurveRows.refs,CurveRows.flag,CurveRows.xbit,CurveRows.ybit,CurveRows.outbit,Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,Fin.ofNat,Fin.succ]
       try simp only [eq_mpr_eq_cast,cast_eq,padded_val,rpad_val,pad]
       try split
       all_goals try simp_all only [↓reduceDIte,↓reduceIte]
       all_goals try dsimp only [GateSemantics.e,GateRoutes.S,Ref.source,Addr.index,Fin.castSucc,Fin.castAdd,Fin.natAdd,finProdFinEquiv,start,top,headN,TracksPoly.tri,bank,run,triple,RegisterMap.mul,auxShape,Shape.size,Fin.castLE,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,EquivLike.coe,Fin.last]
       all_goals first | rfl | omega)
  all_goals (
       try dsimp only [checkR,pad,RangeRows.checker,RangeRows.xa,RangeRows.ya,RangeRows.oa,RangeRows.ra,GateRoutes.wires,operands,rword,GateRoutes.word,HashRows.pub,quot,runPath,m1,m2,aux,cm,CurveRows.refs,CurveRows.flag,CurveRows.xbit,CurveRows.ybit,CurveRows.outbit,Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,Fin.ofNat,Fin.succ]
       try simp only [eq_mpr_eq_cast,cast_eq,padded_val,rpad_val,pad]
       try split
       all_goals try simp_all only [↓reduceDIte,↓reduceIte]
       all_goals try dsimp only [GateSemantics.e,GateRoutes.S,Ref.source,Addr.index,Fin.castSucc,Fin.castAdd,Fin.natAdd,finProdFinEquiv,start,top,headN,TracksPoly.tri,bank,run,triple,RegisterMap.mul,auxShape,Shape.size,Fin.castLE,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,EquivLike.coe,Fin.last]
       all_goals first | rfl | omega)
theorem hash6_ok {d} (hd : 1≤d) (p) (c : Coeff) : Tracks (hash6R d (w4_M5GraphBounds.graph d hd).nE) (HashRows.block p (Routes.network.six hd p c)) := by
  unfold hash6R hashR' HashRows.block; refine cat_ok (cat_ok (prod_ok ?_ ?_) (prod_ok ?_ ?_)) (cat_ok (plus_ok _ ?_) (cat_ok (plus_ok _ ?_) (plus_ok _ ?_)))
  all_goals intro j; repeat' apply And.intro
  all_goals dsimp only [Routes.network.six,Routes.network.coord,Routes.network.a6Reg,Routes.network.b6Reg,Function.comp_apply,GateRoutes.wires,rword,GateRoutes.word,quot,runPath,m1,m2,aux,cm,RangeRows.xa,RangeRows.oa,RangeRows.ra,HashRows.pub]
  all_goals try simp only [HashRows.padded,pad]
  all_goals try split <;> try simp_all only [↓reduceDIte,↓reduceIte]
  all_goals try dsimp only [Routes.network.b6Reg,Ref.source,Addr.index,Fin.castSucc,Fin.castAdd,Fin.natAdd,finProdFinEquiv,start,headN,Fin.castLE,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,EquivLike.coe,Fin.last,Routes.bank,Shape.size,newTop,top,TracksPoly.tri,triple,run,RegisterMap.mul,auxShape]
  all_goals first | rfl | omega
end DetDLP.S8H4.TracksHashSpec


