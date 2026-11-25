-- Prove2me | Definitions.Def_DetDLP_S8L_StageOnly
-- name    : DetDLP_S8L_StageOnly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T19:58:57.09744+00:00
-- url     : https://prove2.me/theorems/8b44769d-b87e-4ced-b508-604cba8d5504
-- title:
--   Tag 5 stage Fits lemma
-- statement:
--   Proves stage_spec and stageC for Tag 5 finite-field pair-collision queries.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8L_PacketCode
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2400000
namespace DetDLP.S8L.MakePacket
open S8H0 RegisterMap NamedBlocks GateSemantics S8H.PointAddresses S8C Groundwork M89S1 S8G.FpAtomRows
theorem stage_spec {m d : ℕ} (hd : 1≤d) (p X : ℕ) (i : Fin (2*m-1)) : Fits (stageN m d (Routes.G hd) i) (Routes.stage hd p X i) := by
  unfold stageN Routes.stage stageBlock stageProducts stageSum; dsimp only
  refine cat_spec (cat_spec ?_ ?_) ?_
  all_goals first | apply prod_spec | apply col_spec
  all_goals intros; try simp only [Routes.elem,Routes.acc,GateRoutes.word,HashRows.padded,HashRows.pub,RangeRows.pad,wd]
  all_goals (try split_ifs) <;> (try dsimp [EquivLike.coe,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,finProdFinEquiv,Routes.elem,Routes.acc,GateRoutes.word,HashRows.pub,HashRows.padded,Routes.A,Routes.intermediate,wd,interm,Ref.source,Addr.index,regs,Routes.bank,Shape.size,triple,run,RegisterMap.mul,GateRoutes.auxShape,Routes.atom,Routes.extra,stageShape]) <;> (try split_ifs) <;> (try dsimp [EquivLike.coe,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,finProdFinEquiv,Ref.source,Addr.index,Routes.A,Routes.intermediate,Routes.bank,Shape.size,triple,run,RegisterMap.mul,GateRoutes.auxShape,Routes.atom,Routes.extra,stageShape,Fin.castLE,Fin.castSucc,Fin.castAdd,Fin.natAdd,Fin.ofNat,Fin.last]) <;> (first | contradiction | omega | ring_nf <;> omega)
theorem stageC (m d e i : ℕ) : (stageN m d e i).1 = (stageN m d e 0).1 := rfl
end DetDLP.S8L.MakePacket


