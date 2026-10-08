-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells27
-- name    : CK_CKLaneC_SAxis_Data_Cells27
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T05:39:10.37625+00:00
-- url     : https://prove2.me/theorems/f06d7d57-662c-4208-84bf-bb6780405f68
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells27` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells27` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells27` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells27 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells27.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells27 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 27 (cells 1080..1109). -/

def cell1080 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (192493 / 12800 : ℚ), (19289 / 1280 : ℚ), (.chain [(12, 14)]), (.chain [(12, 14)]), (.chain [(12, 14)]), (.chain [(12, 14), (12, 15)]), (.chain [(12, 14), (12, 15), (12, 16)]), (.chain [(12, 14), (12, 15)]), .one⟩
theorem cell1080_ok : cell1080.check T = true := by decide +kernel

def cell1081 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (19289 / 1280 : ℚ), (193287 / 12800 : ℚ), (.chain [(12, 15)]), (.chain [(12, 15)]), (.chain [(12, 15)]), (.chain [(12, 15), (12, 16)]), (.chain [(12, 15), (12, 16), (12, 17)]), (.chain [(12, 15), (12, 16)]), .one⟩
theorem cell1081_ok : cell1081.check T = true := by decide +kernel

def cell1082 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (193287 / 12800 : ℚ), (48421 / 3200 : ℚ), (.chain [(12, 16)]), (.chain [(12, 16)]), (.chain [(12, 16)]), (.chain [(12, 16)]), (.chain [(12, 16), (12, 17)]), (.chain [(12, 16), (12, 17)]), .one⟩
theorem cell1082_ok : cell1082.check T = true := by decide +kernel

def cell1083 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (48421 / 3200 : ℚ), (194081 / 12800 : ℚ), (.chain [(12, 16)]), (.chain [(12, 16)]), (.chain [(12, 16)]), (.chain [(12, 16), (12, 17)]), (.chain [(12, 16), (12, 17), (12, 18)]), (.chain [(12, 16), (12, 17), (12, 18)]), .one⟩
theorem cell1083_ok : cell1083.check T = true := by decide +kernel

def cell1084 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (194081 / 12800 : ℚ), (97239 / 6400 : ℚ), (.chain [(12, 17)]), (.chain [(12, 17)]), (.chain [(12, 17)]), (.chain [(12, 17), (12, 18)]), (.chain [(12, 17), (12, 18), (12, 19)]), (.chain [(12, 17), (12, 18)]), .one⟩
theorem cell1084_ok : cell1084.check T = true := by decide +kernel

def cell1085 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (97239 / 6400 : ℚ), (7795 / 512 : ℚ), (.chain [(12, 18)]), (.chain [(12, 18)]), (.chain [(12, 18)]), (.chain [(12, 18), (12, 19)]), (.chain [(12, 18), (12, 19), (12, 20)]), (.chain [(12, 18), (12, 19)]), .one⟩
theorem cell1085_ok : cell1085.check T = true := by decide +kernel

def cell1086 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (7795 / 512 : ℚ), (24409 / 1600 : ℚ), (.chain [(12, 19)]), (.chain [(12, 19)]), (.chain [(12, 19)]), (.chain [(12, 19), (12, 20)]), (.chain [(12, 19), (12, 20), (12, 21)]), (.chain [(12, 19), (12, 20)]), .one⟩
theorem cell1086_ok : cell1086.check T = true := by decide +kernel

def cell1087 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (24409 / 1600 : ℚ), (195669 / 12800 : ℚ), (.chain [(12, 20)]), (.chain [(12, 20)]), (.chain [(12, 20)]), (.chain [(12, 20)]), (.chain [(12, 20), (12, 21)]), (.chain [(12, 20), (12, 21)]), .one⟩
theorem cell1087_ok : cell1087.check T = true := by decide +kernel

def cell1088 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (195669 / 12800 : ℚ), (98033 / 6400 : ℚ), (.chain [(12, 20)]), (.chain [(12, 20)]), (.chain [(12, 20)]), (.chain [(12, 20), (12, 21)]), (.chain [(12, 20), (12, 21), (12, 22)]), (.chain [(12, 20), (12, 21), (12, 22)]), .one⟩
theorem cell1088_ok : cell1088.check T = true := by decide +kernel

def cell1089 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (98033 / 6400 : ℚ), (196463 / 12800 : ℚ), (.chain [(12, 21)]), (.chain [(12, 21)]), (.chain [(12, 21)]), (.chain [(12, 21), (12, 22)]), (.chain [(12, 21), (12, 22), (12, 23)]), (.chain [(12, 21), (12, 22)]), .one⟩
theorem cell1089_ok : cell1089.check T = true := by decide +kernel

def cell1090 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (196463 / 12800 : ℚ), (9843 / 640 : ℚ), (.chain [(12, 22)]), (.chain [(12, 22)]), (.chain [(12, 22)]), (.chain [(12, 22), (12, 23)]), (.chain [(12, 22), (12, 23), (12, 24)]), (.chain [(12, 22), (12, 23)]), .one⟩
theorem cell1090_ok : cell1090.check T = true := by decide +kernel

def cell1091 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (9843 / 640 : ℚ), (197257 / 12800 : ℚ), (.chain [(12, 23)]), (.chain [(12, 23)]), (.chain [(12, 23)]), (.chain [(12, 23)]), (.chain [(12, 23), (12, 24)]), (.chain [(12, 23), (12, 24)]), .one⟩
theorem cell1091_ok : cell1091.check T = true := by decide +kernel

def cell1092 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (197257 / 12800 : ℚ), (98827 / 6400 : ℚ), (.chain [(12, 23)]), (.chain [(12, 23)]), (.chain [(12, 23)]), (.chain [(12, 23), (12, 24)]), (.chain [(12, 23), (12, 24), (12, 25)]), (.chain [(12, 23), (12, 24), (12, 25)]), .one⟩
theorem cell1092_ok : cell1092.check T = true := by decide +kernel

def cell1093 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (98827 / 6400 : ℚ), (198051 / 12800 : ℚ), (.chain [(12, 24)]), (.chain [(12, 24)]), (.chain [(12, 24)]), (.chain [(12, 24), (12, 25)]), (.chain [(12, 24), (12, 25), (12, 26)]), (.chain [(12, 24), (12, 25)]), .one⟩
theorem cell1093_ok : cell1093.check T = true := by decide +kernel

def cell1094 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (198051 / 12800 : ℚ), (12403 / 800 : ℚ), (.chain [(12, 25)]), (.chain [(12, 25)]), (.chain [(12, 25)]), (.chain [(12, 25), (12, 26)]), (.chain [(12, 25), (12, 26), (12, 27)]), (.chain [(12, 25), (12, 26)]), .one⟩
theorem cell1094_ok : cell1094.check T = true := by decide +kernel

def cell1095 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (12403 / 800 : ℚ), (39769 / 2560 : ℚ), (.chain [(12, 26)]), (.chain [(12, 26)]), (.chain [(12, 26)]), (.chain [(12, 26)]), (.chain [(12, 26), (12, 27)]), (.chain [(12, 26), (12, 27)]), .one⟩
theorem cell1095_ok : cell1095.check T = true := by decide +kernel

def cell1096 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (39769 / 2560 : ℚ), (99621 / 6400 : ℚ), (.chain [(12, 26)]), (.chain [(12, 26)]), (.chain [(12, 26)]), (.chain [(12, 26), (12, 27)]), (.chain [(12, 26), (12, 27), (12, 28)]), (.chain [(12, 26), (12, 27), (12, 28)]), .one⟩
theorem cell1096_ok : cell1096.check T = true := by decide +kernel

def cell1097 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (99621 / 6400 : ℚ), (199639 / 12800 : ℚ), (.chain [(12, 27)]), (.chain [(12, 27)]), (.chain [(12, 27)]), (.chain [(12, 27), (12, 28)]), (.chain [(12, 27), (12, 28), (12, 29)]), (.chain [(12, 27), (12, 28), (12, 29)]), .one⟩
theorem cell1097_ok : cell1097.check T = true := by decide +kernel

def cell1098 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (199639 / 12800 : ℚ), (50009 / 3200 : ℚ), (.chain [(12, 28)]), (.chain [(12, 28)]), (.chain [(12, 28)]), (.chain [(12, 28), (12, 29)]), (.chain [(12, 28), (12, 29), (12, 30)]), (.chain [(12, 28), (12, 29)]), .one⟩
theorem cell1098_ok : cell1098.check T = true := by decide +kernel

def cell1099 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (50009 / 3200 : ℚ), (200433 / 12800 : ℚ), (.chain [(12, 29)]), (.chain [(12, 29)]), (.chain [(12, 29)]), (.chain [(12, 29), (12, 30)]), (.chain [(12, 29), (12, 30), (12, 31)]), (.chain [(12, 29), (12, 30)]), .one⟩
theorem cell1099_ok : cell1099.check T = true := by decide +kernel

def cell1100 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (200433 / 12800 : ℚ), (20083 / 1280 : ℚ), (.chain [(12, 30)]), (.chain [(12, 30)]), (.chain [(12, 30)]), (.chain [(12, 30)]), (.chain [(12, 30), (12, 31)]), (.chain [(12, 30), (12, 31)]), .one⟩
theorem cell1100_ok : cell1100.check T = true := by decide +kernel

def cell1101 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (20083 / 1280 : ℚ), (201227 / 12800 : ℚ), (.chain [(12, 30)]), (.chain [(12, 30)]), (.chain [(12, 30)]), (.chain [(12, 30), (12, 31)]), (.chain [(12, 30), (12, 31), (13, 0)]), (.chain [(12, 30), (12, 31), (13, 0)]), .one⟩
theorem cell1101_ok : cell1101.check T = true := by decide +kernel

def cell1102 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (201227 / 12800 : ℚ), (25203 / 1600 : ℚ), (.chain [(12, 31)]), (.chain [(12, 31)]), (.chain [(12, 31)]), (.chain [(12, 31), (13, 0)]), (.chain [(12, 31), (13, 0), (13, 1)]), (.chain [(12, 31), (13, 0)]), .one⟩
theorem cell1102_ok : cell1102.check T = true := by decide +kernel

def cell1103 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (25203 / 1600 : ℚ), (101209 / 6400 : ℚ), (.chain [(13, 0)]), (.chain [(13, 0)]), (.chain [(13, 0)]), (.chain [(13, 0), (13, 1)]), (.chain [(13, 0), (13, 1), (13, 2)]), (.chain [(13, 0), (13, 1), (13, 2)]), .one⟩
theorem cell1103_ok : cell1103.check T = true := by decide +kernel

def cell1104 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (101209 / 6400 : ℚ), (40563 / 2560 : ℚ), (.chain [(13, 1)]), (.chain [(13, 1)]), (.chain [(13, 1)]), (.chain [(13, 1), (13, 2)]), (.chain [(13, 1), (13, 2), (13, 3)]), (.chain [(13, 1), (13, 2), (13, 3)]), .one⟩
theorem cell1104_ok : cell1104.check T = true := by decide +kernel

def cell1105 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (40563 / 2560 : ℚ), (50803 / 3200 : ℚ), (.chain [(13, 2)]), (.chain [(13, 2)]), (.chain [(13, 2)]), (.chain [(13, 2), (13, 3)]), (.chain [(13, 2), (13, 3), (13, 4)]), (.chain [(13, 2), (13, 3), (13, 4)]), .one⟩
theorem cell1105_ok : cell1105.check T = true := by decide +kernel

def cell1106 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (50803 / 3200 : ℚ), (203609 / 12800 : ℚ), (.chain [(13, 3)]), (.chain [(13, 3)]), (.chain [(13, 3)]), (.chain [(13, 3), (13, 4)]), (.chain [(13, 3), (13, 4), (13, 5)]), (.chain [(13, 3), (13, 4)]), .one⟩
theorem cell1106_ok : cell1106.check T = true := by decide +kernel

def cell1107 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (203609 / 12800 : ℚ), (102003 / 6400 : ℚ), (.chain [(13, 4)]), (.chain [(13, 4)]), (.chain [(13, 4)]), (.chain [(13, 4), (13, 5)]), (.chain [(13, 4), (13, 5), (13, 6)]), (.chain [(13, 4), (13, 5)]), .one⟩
theorem cell1107_ok : cell1107.check T = true := by decide +kernel

def cell1108 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (102003 / 6400 : ℚ), (204403 / 12800 : ℚ), (.chain [(13, 5)]), (.chain [(13, 5)]), (.chain [(13, 5)]), (.chain [(13, 5)]), (.chain [(13, 5), (13, 6)]), (.chain [(13, 5), (13, 6)]), .one⟩
theorem cell1108_ok : cell1108.check T = true := by decide +kernel

def cell1109 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (204403 / 12800 : ℚ), (16 : ℚ), (.chain [(13, 5)]), (.chain [(13, 5)]), (.chain [(13, 5)]), (.chain [(13, 5), (13, 6)]), (.chain [(13, 5), (13, 6), (13, 7)]), (.chain [(13, 5), (13, 6), (13, 7)]), .one⟩
theorem cell1109_ok : cell1109.check T = true := by decide +kernel

def cells27 : List CellW := [cell1080, cell1081, cell1082, cell1083, cell1084, cell1085, cell1086, cell1087, cell1088, cell1089, cell1090, cell1091, cell1092, cell1093, cell1094, cell1095, cell1096, cell1097, cell1098, cell1099, cell1100, cell1101, cell1102, cell1103, cell1104, cell1105, cell1106, cell1107, cell1108, cell1109]

theorem cells27_valid : ∀ w ∈ cells27, w.check T = true :=
  (forall_mem_cons_of cell1080_ok (forall_mem_cons_of cell1081_ok (forall_mem_cons_of cell1082_ok (forall_mem_cons_of cell1083_ok (forall_mem_cons_of cell1084_ok (forall_mem_cons_of cell1085_ok (forall_mem_cons_of cell1086_ok (forall_mem_cons_of cell1087_ok (forall_mem_cons_of cell1088_ok (forall_mem_cons_of cell1089_ok (forall_mem_cons_of cell1090_ok (forall_mem_cons_of cell1091_ok (forall_mem_cons_of cell1092_ok (forall_mem_cons_of cell1093_ok (forall_mem_cons_of cell1094_ok (forall_mem_cons_of cell1095_ok (forall_mem_cons_of cell1096_ok (forall_mem_cons_of cell1097_ok (forall_mem_cons_of cell1098_ok (forall_mem_cons_of cell1099_ok (forall_mem_cons_of cell1100_ok (forall_mem_cons_of cell1101_ok (forall_mem_cons_of cell1102_ok (forall_mem_cons_of cell1103_ok (forall_mem_cons_of cell1104_ok (forall_mem_cons_of cell1105_ok (forall_mem_cons_of cell1106_ok (forall_mem_cons_of cell1107_ok (forall_mem_cons_of cell1108_ok (forall_mem_cons_of cell1109_ok forall_mem_nil_of))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


