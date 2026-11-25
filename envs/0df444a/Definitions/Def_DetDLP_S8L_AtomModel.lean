-- Prove2me | Definitions.Def_DetDLP_S8L_AtomModel
-- name    : DetDLP_S8L_AtomModel
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T12:50:13.812606+00:00
-- url     : https://prove2.me/theorems/50fb6568-e462-4cc8-9cc9-86669c7667f6
-- title:
--   Atom row model
-- statement:
--   Proves that the numeric atom packet code models each routed atom row.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8L_PacketCode
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
namespace DetDLP.S8L.MakePacket
open S8H0 RegisterMap NamedBlocks GateSemantics S8H.PointAddresses S8C Groundwork M89S1 S8G.FpAtomRows
private theorem pair_val {n m : ℕ} (i : Fin n) (j : Fin m) : (finProdFinEquiv (i,j)).val = j.val+m*i.val := rfl
private theorem idxV {n : ℕ} {s : Shape} (i : Fin n) (a : Addr s) : (Addr.vec i a).index.val = i.val*s.size+a.index.val := by change a.index.val+s.size*i.val=_; ac_rfl
private theorem idxL {s t : Shape} (a : Addr s) : (Addr.fst (v:=t) a).index.val=a.index.val := rfl
private theorem idxR {s t : Shape} (a : Addr t) : (Addr.snd (u:=s) a).index.val=s.size+a.index.val := rfl
theorem atom_spec {m d : ℕ} (hd : 1≤d) (p T : ℕ) (cs : Fin m → ℕ × ℕ) (i : Fin (2*m)) : Fits (atomN m d (Routes.G hd) i) (Routes.atomRows hd p T cs i) := by
  unfold atomN Routes.atomRows HashRows.block; dsimp only
  refine cat_spec (cat_spec (cat_spec ?_ ?_) (cat_spec ?_ (cat_spec ?_ ?_))) (cat_spec ?_ (cat_spec ?_ (cat_spec ?_ (cat_spec ?_ (cat_spec ?_ ?_)))))
  all_goals first | apply prod_spec | apply col_spec | apply row_spec
  all_goals intros; try (rename_i j; guard_hyp j : Fin 2; fin_cases j)
  all_goals try simp only [Routes.hash,Routes.elem,GateRoutes.word,HashRows.padded,HashRows.pub,RangeRows.pad,wd]
  all_goals (try split_ifs) <;> (try simp only [Routes.hash,Routes.elem,GateRoutes.word,HashRows.padded,HashRows.pub,RangeRows.pad,wd,Routes.A,Routes.H,Routes.R,Routes.M₁,Routes.M₂,Ref.source,Fin.val_castSucc,Fin.val_last,idxL,idxR,idxV])
  all_goals (try split_ifs) <;> (try dsimp [EquivLike.coe,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,finProdFinEquiv,Ref.source,Addr.index,regs,Routes.bank,Shape.size,triple,run,RegisterMap.mul,GateRoutes.auxShape,Routes.atom,Routes.extra,stageShape]) <;> (try simp [Fin.castAdd,Fin.natAdd, Nat.mul_comm _ (i:ℕ)]) <;> try omega
  contradiction
end DetDLP.S8L.MakePacket


