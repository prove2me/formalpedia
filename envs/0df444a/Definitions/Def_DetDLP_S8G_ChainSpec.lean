-- Prove2me | Definitions.Def_DetDLP_S8G_ChainSpec
-- name    : DetDLP_S8G_ChainSpec
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T00:15:37.41567+00:00
-- url     : https://prove2.me/theorems/9f62a2fd-f12b-4400-a914-a636331af5ba

import Definitions.Def_DetDLP_S8G_PacketCode_v2
import Definitions.Def_DetDLP_S8G_SeedSpec
set_option autoImplicit false
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8G.MakePacket
open DetDLP.S8G.MakePacketV2
open S8H S8H0 RegisterMap NamedBlocks RangeRows GateRoutes HashRows SeedAndAtomBank Routes
open S8H.PointAddresses S8J.CircuitRealizes S8H.MakeCombinators FpMoment.Code M89S1 S8C Groundwork FpAtomRows ResidueWires

theorem chain_spec {s d} (hd : 1 ≤ d) (p m base a z : ℕ) (q : Path (chainShape (m-1) d (edges hd)) s)
    (X Z : Word s) (Y : Fin (m-1) → Word s) (hq : At base q)
    (hx : Names (bus d s.size a) X) (hz : Names (bus d s.size z) Z)
    (hy : ∀ i : Fin (m-1), Names (bus d s.size (a+(i.val+1)*(atomSlot d (edges hd)).size)) (Y i)) :
    Fits (chainN m d (edges hd) s.size z base a) (chainBlock hd p X Y Z q) := by
  unfold chainN chainBlock; dsimp only
  refine cat_spec ?_ (cat_spec ?_ ?_)
  · apply row_spec; intro i j; fin_cases j <;> first | exact hx _ | exact hz _
  · apply all_spec; intro i; apply col_spec
    all_goals intro j; (try dsimp only [checkN,checker]); (try simp only [bus,pad,internal]); (try split_ifs) <;> first | rfl | (refine Eq.trans ?_ (hq _).symm; dsimp [EquivLike.coe,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,finProdFinEquiv,Ref.source,Addr.index,Fin.castAdd,Fin.castLE,Fin.castSucc,Fin.natAdd,Fin.ofNat,Fin.last,Routes.bank,productShape,seedShape,atomBankShape,chainShape,stageShape,seedSlot,atomSlot,run,RegisterMap.mul,auxShape,triple,Shape.size]; first | rfl | omega | ring)
  · apply all_spec; intro i
    unfold stageAt stageBlock stageProducts stageSum; dsimp only
    refine cat_spec (cat_spec ?_ ?_) ?_
    all_goals first | apply prod_spec | apply col_spec
    all_goals intro j
    all_goals try (have hj : j.val < edges hd := j.isLt; simp only [word,padded,dif_pos hj])
    all_goals try (split_ifs <;> first | exact hx _ | exact hz _ | exact hy i _ | skip)
    all_goals try exact hy i _
    all_goals try exact (srcP _).symm
    all_goals try ((try simp only [residueWord,internal,word,padded,pub,bus,srcR,srcP,Fin.isLt,dif_pos,if_true]); (try split_ifs) <;> first | rfl | (refine Eq.trans ?_ (hq _).symm; dsimp [EquivLike.coe,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,finProdFinEquiv,Ref.source,Addr.index,Fin.castAdd,Fin.castLE,Fin.castSucc,Fin.natAdd,Fin.ofNat,Fin.last,Routes.bank,productShape,seedShape,atomBankShape,chainShape,stageShape,seedSlot,atomSlot,run,RegisterMap.mul,auxShape,triple,Shape.size]; first | rfl | omega | ring) | omega)

end DetDLP.S8G.MakePacket


