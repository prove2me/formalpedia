-- Prove2me | Definitions.Def_DetDLP_S8G_SeedSpec
-- name    : DetDLP_S8G_SeedSpec
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T00:05:33.156989+00:00
-- url     : https://prove2.me/theorems/06484a84-32de-4217-bc68-2ad9dd0b6ca1

import Definitions.Def_DetDLP_S8G_PacketCode_v2
import Definitions.Def_DetDLP_S8G_AtomSpec
set_option autoImplicit false
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8G.MakePacket
open DetDLP.S8G.MakePacketV2
open S8H S8H0 RegisterMap NamedBlocks RangeRows GateRoutes HashRows SeedAndAtomBank Routes
open S8H.PointAddresses S8J.CircuitRealizes S8H.MakeCombinators FpMoment.Code M89S1 S8C Groundwork FpAtomRows ResidueWires

theorem all_spec {s n} {f : ℕ → NC} {r : Fin n → B (Shape.size s+1)} (h : ∀ j : Fin n, Fits (f j) (r j)) : Fits (allN n f) (allRows n r) := by
  cases n with | zero => simp only [allN,if_true,allRows]; apply row_spec; intro i; exact i.elim0 | succ n => exact manyN_spec n f r h

theorem seed_spec {s m} (p : ℕ) (η : List Bool) (q : Path (seedShape m (bitLen p+1)) s)
    (hq : At 0 q) : Fits (seedN m (bitLen p+1) s.size η.length) (seedBlock p m η q) := by
  unfold At at hq
  unfold seedN seedBlock; dsimp only
  apply cat_spec
  · apply all_spec; intro i
    unfold seedSlotBlock checkN checker sumRows
    refine cat_spec ?_ (cat_spec ?_ ?_)
    all_goals
      apply col_spec <;> (
        (try unfold Names); intros
        try (rename_i j; have hj := Fin.isLt j; change _ < (w4_M5GraphBounds.graph _ _).nE at hj)
        simp only [bus,word,padded,pad,pub,srcR,srcP,srcM,seedA,seedB,Fin.isLt,dif_pos,if_true] <;>
          (try split_ifs) <;> simp only [hq,srcR,srcM,srcP,idxV,idxL,idxR,idxW,triple,run,RegisterMap.mul,auxShape,Shape.size,Nat.zero_add,Nat.add_zero] <;> (try refine Eq.trans ?_ (hq _).symm) <;> (try simp only [idxV,idxL,idxR,idxW,triple,run,RegisterMap.mul,auxShape,Shape.size,Nat.zero_add,Nat.add_zero]) <;> (try dsimp [EquivLike.coe,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,finProdFinEquiv,Addr.index,Shape.size,seedShape,seedSlot,triple,run,RegisterMap.mul,auxShape,Fin.castAdd,Fin.castLE,Fin.castSucc,Fin.natAdd,Fin.ofNat]) <;> first | omega | (ring_nf <;> omega))
  · apply row_spec; intro i j
    simp only [Nat.add_sub_cancel,prefixBit]
    by_cases h : i.val < m*2*bitLen p
    · have sub (a b : ℕ) : a-1-b = a-(b+1) := by omega
      have pair0 (k : Fin (m*2)) : ((finProdFinEquiv.symm k).2 = 0) ↔ k.val%2 = 0 := by exact Fin.ext_iff
      simp only [dif_pos h,if_pos h,sub,pair0,pDiv,pMod,Fin.rev,Fin.val_zero]
      split_ifs <;> simp only [seedA,seedB,word,padded] <;> split_ifs <;> simp_all only [Fin.ext_iff,Fin.val_zero,srcR,srcP,hq,idxL,idxR,idxW,idxV,pDiv,pMod,Nat.zero_add] <;> (try refine Eq.trans ?_ (hq _).symm) <;> (try simp only [idxV,idxL,idxR,idxW,pDiv,pMod,Shape.size,Nat.zero_add]) <;> (try dsimp [EquivLike.coe,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,finProdFinEquiv,Addr.index,Shape.size,seedShape,seedSlot,triple,run,RegisterMap.mul,auxShape,Fin.castAdd,Fin.castLE,Fin.castSucc,Fin.natAdd,Fin.ofNat]) <;> first | omega | (ring_nf <;> omega) | contradiction
    · simp only [dif_neg h,if_neg h,srcP]

end DetDLP.S8G.MakePacket


