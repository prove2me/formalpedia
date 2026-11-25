-- Prove2me | Definitions.Def_DetDLP_S8L_RangeOnly
-- name    : DetDLP_S8L_RangeOnly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T20:15:26.873424+00:00
-- url     : https://prove2.me/theorems/29c01760-59ec-450b-a3c8-fe904b26a33d
-- title:
--   Tag 5 intermediate range and prefix digit Fits lemmas
-- statement:
--   Proves range_spec and dig_spec for Tag 5 finite-field pair-collision queries.
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
theorem range_spec {m d e : ℕ} (p : ℕ) (i : Fin (2*m-2)) : Fits (rangeN d (regs m d e) (interm m d e i)) (RangeRows.checker p (Routes.intermediate (d:=d) (e:=e) i)) := by
  apply col_spec
  all_goals intros; try simp only [Routes.elem,Routes.acc,GateRoutes.word,HashRows.padded,HashRows.pub,RangeRows.pad,wd]
  all_goals (try split_ifs) <;> (try dsimp [EquivLike.coe,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,finProdFinEquiv,Routes.elem,Routes.acc,GateRoutes.word,HashRows.pub,HashRows.padded,Routes.A,Routes.intermediate,wd,interm,Ref.source,Addr.index,regs,Routes.bank,Shape.size,triple,run,RegisterMap.mul,GateRoutes.auxShape,Routes.atom,Routes.extra,stageShape]) <;> (try split_ifs) <;> (try dsimp [EquivLike.coe,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,finProdFinEquiv,Ref.source,Addr.index,Routes.A,Routes.intermediate,Routes.bank,Shape.size,triple,run,RegisterMap.mul,GateRoutes.auxShape,Routes.atom,Routes.extra,stageShape,Fin.castLE,Fin.castSucc,Fin.castAdd,Fin.natAdd,Fin.ofNat,Fin.last]) <;> (first | contradiction | omega | ring_nf <;> omega)
theorem dig_spec {m e : ℕ} (p j : ℕ) : dig m (Semantics.width p) e j = (Routes.digit (m:=m) (d:=Semantics.width p) (e:=e) p j).source.val := by
  simp only [dig,Semantics.width,Nat.add_sub_cancel,Routes.digit,Routes.elem,GateRoutes.word,wd]; split_ifs <;> try omega
  all_goals (try dsimp [HashRows.padded,Routes.A,Ref.source,Addr.index,regs,Routes.bank,Shape.size]) <;> (try split_ifs) <;> (try dsimp [EquivLike.coe,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,finProdFinEquiv,Ref.source,Addr.index,Fin.castLE,Fin.castSucc,Fin.castAdd,Fin.natAdd,regs,Routes.bank,Shape.size]) <;> (first | rfl | omega | ring_nf <;> omega)
end DetDLP.S8L.MakePacket


