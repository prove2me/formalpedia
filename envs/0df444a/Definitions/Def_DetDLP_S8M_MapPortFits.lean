-- Prove2me | Definitions.Def_DetDLP_S8M_MapPortFits
-- name    : DetDLP_S8M_MapPortFits
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T05:10:14.618143+00:00
-- url     : https://prove2.me/theorems/101ccf2f-8b9b-5540-916f-c67d1f165ebc
-- title:
--   Tag 6 Map Port Fits
-- statement:
--   Fits the Tag 6 map-port circuit to its named block rows.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_AtomMapPortFits
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8M.PortEval
open S8H0 S8H.PortCombinators S8J S8J.CircuitRealizes NamedBlocks RegisterMap GateRoutes LocalGateEq PortPoly
variable {s : Shape} {d : ℕ}
open private ECMapRows.gw ECMapRows.ranges ECMapRows.args4 ECMapRows.maskEq ECMapRows.rwrd from Definitions.Def_DetDLP_S8M_ECMapRows
theorem mapFits (hd : 1 ≤ d) (p b2 a1 a3 : ℕ) (fl : Ref s) (x y : HashRows.Word s) (q : Path (ECMapRows.mapShape d ((w4_M5GraphBounds.graph d hd).nE)) s) (hf : ∀ z, fl.read z = z) (hx : Reads (regR d) x) (hy : Reads (regR d) y) : FitsG (mapG (List.replicate d ()) d p b2 a1 a3) (ECMapRows.mapBlock hd p b2 a1 a3 fl x y q).core := by
  unfold mapG ECMapRows.mapBlock ECMapRows.ranges; dsimp only
  refine catB (tiles_join (n:=2) (m:=8) (tiles_join (n:=1) (m:=1) (tile_one (range_spec ..)) (tile_one (range_spec ..))) (tile_many (n:=3) (t:=2) _ fun _ => tiles_join (n:=1) (m:=1) (tile_one (range_spec ..)) (tile_one (range_spec ..)))) (catB ?_ (catB ?_ ?_))
  · refine catB ?_ (catB ?_ (catB ?_ ?_))
    all_goals apply hashFits <;> first | exact hx | exact hy | apply wordReads | intro i z; rfl
  · refine ⟨rfl,fun i w => ?_⟩; rw [eqs_local]; change (_ == _) = decide (_ = fl.read _); rw [hf]; rfl
  · apply tiles_join (n:=1) (m:=1)
    all_goals apply tile_one; refine ⟨rfl,fun i w => ?_⟩; unfold ECMapRows.maskEq; rw [rows_local]; have hi : i.val < d := i.isLt; simp [ECMapRows.rwrd,GateRoutes.word,HashRows.padded,hi,Ref.read,bit]; change (_ = _) ↔ _ = (!fl.read _ && _); rw [hf]
end DetDLP.S8M.PortEval


