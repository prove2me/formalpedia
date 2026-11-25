-- Prove2me | Definitions.Def_DetDLP_S8M_AtomMapPortFits
-- name    : DetDLP_S8M_AtomMapPortFits
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T04:31:15.277769+00:00
-- url     : https://prove2.me/theorems/e73fa55c-e6a3-5643-a0ff-42b38b1f1421
-- title:
--   Tag 6 Atom Map Port Fits
-- statement:
--   Fits the Tag 6 atom-map port circuit to its named block rows.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_AtomBasePortFits
import Definitions.Def_DetDLP_S8M_ECAtomSlot
import Definitions.Def_DetDLP_S8M_ECMapRows
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8M.PortEval
open S8H0 S8H.PortCombinators S8J S8J.CircuitRealizes NamedBlocks RegisterMap GateRoutes LocalGateEq PortPoly
variable {s : Shape} {d : ℕ}
private theorem ranges {e : ℕ} (p : ℕ) : FitsG (tile 16 (rangeG d p)) (RangeRows.block d e p).core := by
  apply tiles_join (n:=2) (m:=14)
  · exact tiles_join (n:=1) (m:=1) (tile_one (range_spec ..)) (tile_one (range_spec ..))
  · exact tile_many (n:=6) (t:=2) _ fun i => tiles_join (n:=1) (m:=1) (tile_one (range_spec ..)) (tile_one (range_spec ..))
open private fixed from Definitions.Def_DetDLP_S8M_ECAtomSlot
abbrev edges {d : ℕ} (hd : 1 ≤ d) := (w4_M5GraphBounds.graph d hd).nE
private theorem sixFits (hd : 1 ≤ d) (p : ℕ) (c : Coeff) : FitsG (PortPoly.hash (List.replicate d ()) d p 0 0 0) (HashRows.block p (S8H4.Routes.network.six hd p c)).core := by
  unfold PortPoly.hash genHashG HashRows.block; dsimp only [S8H4.Routes.network.six,GateRoutes.wires]
  refine catB (catB ?_ ?_) (catB ?_ (catB ?_ ?_))
  all_goals first | apply prod_spec | apply add_spec
  all_goals intros; simp only [Function.comp_apply,rd,if_pos,regR,pinR,S8H4.Routes.network.coord,GateRoutes.rword,GateRoutes.quot,GateRoutes.word,HashRows.padded,HashRows.pub,Ref.read] <;> split_ifs <;> rfl

theorem fixedFits (hd : 1 ≤ d) (p T : ℕ) (c : Coeff) : FitsG (atomFixed (List.replicate d ()) d p T c) (fixed hd p T c).core := by
  unfold atomFixed fixed; dsimp only
  refine catB (catG_spec (ranges p) (catB (many_spec fun i => hash_spec hd p c i.castSucc) ?_)) (catB (sixFits hd p c) (catB ?_ ?_))
  · refine ⟨rfl,fun i w => ?_⟩; unfold CurveRows.block; rw [rows_local]; rfl
  · refine ⟨rfl,fun i w => ?_⟩; rw [rows_local]; cases h : w.getD 0 false <;> simp [zeroLastG,Ref.read,h]
  · apply add_spec <;> intros <;> simp only [regR,pinR,RangeRows.pad,Ref.read] <;> split_ifs <;> rfl
theorem atomFits (hd : 1 ≤ d) (p T b m j : ℕ) (c : Coeff) (η : W) (u : Path (ECAtomSlot.slotShape d (edges hd)) s) : let v := fun k => HashRows.pub (s:=s) (coord η b ((j%m)*4+k)); FitsG (atomG (atomFixed (List.replicate d ()) d p T c) b d m j η) (ECAtomSlot.slotBlock hd p T c (v 0) (v 1) (v 2) (v 3) u).core := by
  dsimp only; unfold atomG ECAtomSlot.slotBlock; dsimp only; refine catB (fixedFits hd p T c) ⟨rfl,fun i w => ?_⟩; rw [rows_local]
  have h : (0:ℕ)<d := by omega
  cases hw : w.getD 0 false <;> simp [S8H4.Routes.network.coord,S8H4.Routes.network.a6Reg,S8H4.Routes.network.b6Reg,GateRoutes.word,HashRows.padded,h,HashRows.pub,Ref.read,bit,List.getD_eq_getElem?_getD] at hw ⊢ <;> simp [hw]
open private ECMapRows.gw ECMapRows.ranges ECMapRows.args4 ECMapRows.maskEq ECMapRows.rwrd from Definitions.Def_DetDLP_S8M_ECMapRows
abbrev Reads (r : Reader) (v : HashRows.Word s) := ∀ i b, r i b = (v i).read b
theorem wordReads {k : ℕ} (f : Path (.word k) s) : Reads (regR k) (GateRoutes.word f) := by intro i x; simp only [regR,GateRoutes.word,HashRows.padded]; split_ifs <;> rfl
private theorem paddedProd (hd : 1 ≤ d) {a b z : Reader} {A B Z : HashRows.Word s} (f : Path (.word (edges hd)) s) (ha : Reads a A) (hb : Reads b B) (hz : Reads z Z) : FitsG (prodG (List.replicate d ()) d a b z) (HashRows.product hd A B Z (RangeRows.pad (fun i => .reg (f (.word i))))).core := by
  have H : (RangeRows.pad (n:=(w3_fpMulLayout d hd).nb) (fun i => Ref.reg (f (.word i)))) = (fun i => Ref.reg (f (.word ⟨i.val,i.isLt⟩))) := by funext i; exact dif_pos i.isLt
  rw [H]; exact prod_spec hd ha hb hz
theorem hashFits (hd : 1 ≤ d) (p a x b : ℕ) {A X B : HashRows.Word s} (ha : Reads (rd d a) A) (hx : Reads (rd d x) X) (hb : Reads (rd d b) B) (f : Path (ECMapRows.slot d (edges hd)) s) : FitsG (PortPoly.hash (List.replicate d ()) d p a x b) (HashRows.block p (ECMapRows.gw hd p A X B f)).core := by
  unfold PortPoly.hash genHashG HashRows.block ECMapRows.gw; dsimp only
  refine catB (catB ?_ ?_) (catB ?_ (catB ?_ ?_))
  · exact paddedProd hd _ ha hx (wordReads _)
  · exact paddedProd hd _ (wordReads _) (fun _ _ => rfl) (wordReads _)
  all_goals apply add_spec <;> intros <;> first | apply hb | (simp only [regR,pinR,ECMapRows.rwrd,GateRoutes.word,HashRows.padded,HashRows.pub,Ref.read] <;> split_ifs <;> rfl)

end DetDLP.S8M.PortEval


