-- Prove2me | Definitions.Def_DetDLP_S8G_AtomSpec
-- name    : DetDLP_S8G_AtomSpec
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T23:44:45.136705+00:00
-- url     : https://prove2.me/theorems/0feded03-ba36-4a9c-bcc9-e73f6432e323

import Definitions.Def_DetDLP_S8G_PacketCode_v2
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8G.MakePacket
open DetDLP.S8G.MakePacketV2
open S8H S8H0 RegisterMap NamedBlocks RangeRows GateRoutes HashRows SeedAndAtomBank Routes
open S8H.PointAddresses S8J.CircuitRealizes S8H.MakeCombinators FpMoment.Code M89S1 S8C Groundwork FpAtomRows ResidueWires
abbrev At {s t : Shape} (o : ℕ) (q : Path t s) := ∀ a, (q a).index.val = o + a.index.val
theorem idxV {n : ℕ} {s : Shape} (i : Fin n) (a : Addr s) : (Addr.vec i a).index.val = i.val*s.size+a.index.val := by change a.index.val+s.size*i.val=_; ac_rfl
theorem idxL {s t : Shape} (a : Addr s) : (Addr.fst (v:=t) a).index.val=a.index.val := rfl
theorem idxR {s t : Shape} (a : Addr t) : (Addr.snd (u:=s) a).index.val=s.size+a.index.val := rfl
theorem idxW {n : ℕ} (i : Fin n) : (Addr.word i).index.val=i.val := rfl
theorem idxBit : Addr.bit.index.val=0 := rfl
theorem srcR {s : Shape} (a : Addr s) : (Ref.reg a).source.val=a.index.val := rfl
theorem srcM {s : Shape} (v : Bool) (a : Addr s) : (Ref.masked v a).source.val=a.index.val := rfl
theorem srcP {s : Shape} (v : Bool) : (Ref.pin (s:=s) v).source.val=s.size := rfl
theorem pDiv {m n : ℕ} (i : Fin (m*n)) : (finProdFinEquiv.symm i).1.val = i.val/n := rfl
theorem pMod {m n : ℕ} (i : Fin (m*n)) : (finProdFinEquiv.symm i).2.val = i.val%n := rfl
theorem scan_eq {s : Shape} (n : ℕ) (x : Fin n → Ref s) (c : Ref s) (t : Fin n → Ref s) :
    orRows n x c t = S8C3.Routes.scan n x c t := by
  induction n generalizing c with | zero => rfl | succ n ih => simp only [orRows,S8C3.Routes.scan,ih]
theorem atom_spec {s d} (hd : 1 ≤ d) (p T o a b : ℕ) (A B : Word s) (q : Path (atomSlot d (edges hd)) s)
    (hq : At o q) (ha : Names (bus d s.size a) A) (hb : Names (bus d s.size b) B) :
    Fits (atomN d (edges hd) s.size o a b) (atomSlotBlock hd p T A B q) := by
  unfold At at hq
  unfold Names at ha hb
  unfold atomN atomSlotBlock checkN checker
  dsimp only
  refine cat_spec ?_ (cat_spec ?_ (cat_spec ?_ (cat_spec ?_ (cat_spec ?_ ?_))))
  · apply col_spec
    all_goals intro i
    all_goals try simp only [bus,pad,word,padded,pub,srcR,srcP,srcM]
    all_goals try split_ifs
    all_goals try simp only [srcR,srcP,srcM]
    all_goals first | (refine Eq.trans ?_ (hq _).symm; simp only [idxL,idxR,idxV,idxW,idxBit,atomSlot,Shape.size,triple,run,RegisterMap.mul,auxShape] <;> omega) | omega
  · rw [scan_eq]; apply scan_spec
    · intro i
      (try simp only [bus,pad,word,padded,pub,srcR,srcP,Fin.isLt,dif_pos,if_true]); (try split_ifs) <;> (try simp only [srcR,srcP]) <;>
        first | (refine Eq.trans ?_ (hq _).symm; simp only [idxL,idxR,idxV,idxW,idxBit,atomSlot,Shape.size,triple,run,RegisterMap.mul,auxShape]; try omega) | omega
    · intro i
      (try simp only [srcR,srcP]); (try split_ifs) <;>
        first | (refine Eq.trans ?_ (hq _).symm; simp only [idxL,idxR,idxV,idxW,idxBit,atomSlot,Shape.size,triple,run,RegisterMap.mul,auxShape]; try omega) | omega
  · apply col_spec
    all_goals intro i
    all_goals try simp only [bus,pad,word,padded,pub,srcR,srcP,srcM]
    all_goals try split_ifs
    all_goals try simp only [srcR,srcP,srcM]
    all_goals first | (refine Eq.trans ?_ (hq _).symm; simp only [idxL,idxR,idxV,idxW,idxBit,atomSlot,Shape.size,triple,run,RegisterMap.mul,auxShape] <;> omega) | omega
  · apply col_spec
    all_goals intro i
    all_goals try simp only [bus,pad,word,padded,pub,srcR,srcP,srcM]
    all_goals try split_ifs
    all_goals try simp only [srcR,srcP,srcM]
    all_goals first | (refine Eq.trans ?_ (hq _).symm; simp only [idxL,idxR,idxV,idxW,idxBit,atomSlot,Shape.size,triple,run,RegisterMap.mul,auxShape] <;> omega) | omega
  · apply col_spec
    all_goals intro i
    all_goals try simp only [bus,pad,word,padded,pub,srcR,srcP,srcM]
    all_goals try split_ifs
    all_goals try simp only [srcR,srcP,srcM]
    all_goals first | (refine Eq.trans ?_ (hq _).symm; simp only [idxL,idxR,idxV,idxW,idxBit,atomSlot,Shape.size,triple,run,RegisterMap.mul,auxShape] <;> omega) | omega
  · apply genHash_spec
    · intro i; exact ha i
    · intro i
      (try dsimp only)
      (try simp only [bus,pad,word,padded,pub,srcR,srcP,srcM]); (try split_ifs) <;> (try simp only [srcR,srcP,srcM]) <;>
        first | (refine Eq.trans ?_ (hq _).symm; simp only [idxL,idxR,idxV,idxW,idxBit,atomSlot,Shape.size,triple,run,RegisterMap.mul,auxShape]; try omega) | omega
    · intro i; exact hb i
    all_goals intro i
    all_goals try (have hi := i.isLt; change _ < edges hd at hi)
    all_goals (try simp only [bus,pad,word,padded,pub,srcR,srcP,srcM,Fin.isLt,dif_pos,if_true]); (try split_ifs) <;> (try simp only [srcR,srcP,srcM]) <;>
      (try dsimp only) <;> first | rfl | (refine Eq.trans ?_ (hq _).symm; simp only [idxL,idxR,idxV,idxW,idxBit,atomSlot,Shape.size,triple,run,RegisterMap.mul,auxShape]; try omega) | omega | contradiction
end DetDLP.S8G.MakePacket


