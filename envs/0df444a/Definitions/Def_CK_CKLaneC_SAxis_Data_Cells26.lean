-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells26
-- name    : CK_CKLaneC_SAxis_Data_Cells26
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:15:10.219007+00:00
-- url     : https://prove2.me/theorems/220b80a0-726c-4355-8767-154e32bb9e54
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells26` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells26` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells26` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells26 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells26.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells26 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 26 (cells 1040..1079). -/

def cell1040 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (176613 / 12800 : ℚ), (17701 / 1280 : ℚ), (.chain [(11, 15)]), (.chain [(11, 15)]), (.chain [(11, 15)]), (.chain [(11, 15), (11, 16)]), (.chain [(11, 15), (11, 16), (11, 17)]), (.chain [(11, 15), (11, 16)]), .one⟩
theorem cell1040_ok : cell1040.check T = true := by decide +kernel

def cell1041 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (17701 / 1280 : ℚ), (177407 / 12800 : ℚ), (.chain [(11, 16)]), (.chain [(11, 16)]), (.chain [(11, 16)]), (.chain [(11, 16), (11, 17)]), (.chain [(11, 16), (11, 17), (11, 18)]), (.chain [(11, 16), (11, 17)]), .one⟩
theorem cell1041_ok : cell1041.check T = true := by decide +kernel

def cell1042 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (177407 / 12800 : ℚ), (44451 / 3200 : ℚ), (.chain [(11, 17)]), (.chain [(11, 17)]), (.chain [(11, 17)]), (.chain [(11, 17)]), (.chain [(11, 17), (11, 18)]), (.chain [(11, 17), (11, 18)]), .one⟩
theorem cell1042_ok : cell1042.check T = true := by decide +kernel

def cell1043 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (44451 / 3200 : ℚ), (178201 / 12800 : ℚ), (.chain [(11, 17)]), (.chain [(11, 17)]), (.chain [(11, 17)]), (.chain [(11, 17), (11, 18)]), (.chain [(11, 17), (11, 18), (11, 19)]), (.chain [(11, 17), (11, 18), (11, 19)]), .one⟩
theorem cell1043_ok : cell1043.check T = true := by decide +kernel

def cell1044 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (178201 / 12800 : ℚ), (89299 / 6400 : ℚ), (.chain [(11, 18)]), (.chain [(11, 18)]), (.chain [(11, 18)]), (.chain [(11, 18), (11, 19)]), (.chain [(11, 18), (11, 19), (11, 20)]), (.chain [(11, 18), (11, 19)]), .one⟩
theorem cell1044_ok : cell1044.check T = true := by decide +kernel

def cell1045 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (89299 / 6400 : ℚ), (35799 / 2560 : ℚ), (.chain [(11, 19)]), (.chain [(11, 19)]), (.chain [(11, 19)]), (.chain [(11, 19), (11, 20)]), (.chain [(11, 19), (11, 20), (11, 21)]), (.chain [(11, 19), (11, 20)]), .one⟩
theorem cell1045_ok : cell1045.check T = true := by decide +kernel

def cell1046 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (35799 / 2560 : ℚ), (2803 / 200 : ℚ), (.chain [(11, 20)]), (.chain [(11, 20)]), (.chain [(11, 20)]), (.chain [(11, 20), (11, 21)]), (.chain [(11, 20), (11, 21), (11, 22)]), (.chain [(11, 20), (11, 21)]), .one⟩
theorem cell1046_ok : cell1046.check T = true := by decide +kernel

def cell1047 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (2803 / 200 : ℚ), (179789 / 12800 : ℚ), (.chain [(11, 21)]), (.chain [(11, 21)]), (.chain [(11, 21)]), (.chain [(11, 21)]), (.chain [(11, 21), (11, 22)]), (.chain [(11, 21), (11, 22)]), .one⟩
theorem cell1047_ok : cell1047.check T = true := by decide +kernel

def cell1048 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (179789 / 12800 : ℚ), (90093 / 6400 : ℚ), (.chain [(11, 21)]), (.chain [(11, 21)]), (.chain [(11, 21)]), (.chain [(11, 21), (11, 22)]), (.chain [(11, 21), (11, 22), (11, 23)]), (.chain [(11, 21), (11, 22), (11, 23)]), .one⟩
theorem cell1048_ok : cell1048.check T = true := by decide +kernel

def cell1049 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (90093 / 6400 : ℚ), (180583 / 12800 : ℚ), (.chain [(11, 22)]), (.chain [(11, 22)]), (.chain [(11, 22)]), (.chain [(11, 22), (11, 23)]), (.chain [(11, 22), (11, 23), (11, 24)]), (.chain [(11, 22), (11, 23)]), .one⟩
theorem cell1049_ok : cell1049.check T = true := by decide +kernel

def cell1050 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (180583 / 12800 : ℚ), (9049 / 640 : ℚ), (.chain [(11, 23)]), (.chain [(11, 23)]), (.chain [(11, 23)]), (.chain [(11, 23), (11, 24)]), (.chain [(11, 23), (11, 24), (11, 25)]), (.chain [(11, 23), (11, 24)]), .one⟩
theorem cell1050_ok : cell1050.check T = true := by decide +kernel

def cell1051 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (9049 / 640 : ℚ), (181377 / 12800 : ℚ), (.chain [(11, 24)]), (.chain [(11, 24)]), (.chain [(11, 24)]), (.chain [(11, 24)]), (.chain [(11, 24), (11, 25)]), (.chain [(11, 24), (11, 25)]), .one⟩
theorem cell1051_ok : cell1051.check T = true := by decide +kernel

def cell1052 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (181377 / 12800 : ℚ), (90887 / 6400 : ℚ), (.chain [(11, 24)]), (.chain [(11, 24)]), (.chain [(11, 24)]), (.chain [(11, 24), (11, 25)]), (.chain [(11, 24), (11, 25), (11, 26)]), (.chain [(11, 24), (11, 25), (11, 26)]), .one⟩
theorem cell1052_ok : cell1052.check T = true := by decide +kernel

def cell1053 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (90887 / 6400 : ℚ), (182171 / 12800 : ℚ), (.chain [(11, 25)]), (.chain [(11, 25)]), (.chain [(11, 25)]), (.chain [(11, 25), (11, 26)]), (.chain [(11, 25), (11, 26), (11, 27)]), (.chain [(11, 25), (11, 26)]), .one⟩
theorem cell1053_ok : cell1053.check T = true := by decide +kernel

def cell1054 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (182171 / 12800 : ℚ), (22821 / 1600 : ℚ), (.chain [(11, 26)]), (.chain [(11, 26)]), (.chain [(11, 26)]), (.chain [(11, 26), (11, 27)]), (.chain [(11, 26), (11, 27), (11, 28)]), (.chain [(11, 26), (11, 27)]), .one⟩
theorem cell1054_ok : cell1054.check T = true := by decide +kernel

def cell1055 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (22821 / 1600 : ℚ), (36593 / 2560 : ℚ), (.chain [(11, 27)]), (.chain [(11, 27)]), (.chain [(11, 27)]), (.chain [(11, 27)]), (.chain [(11, 27), (11, 28)]), (.chain [(11, 27), (11, 28)]), .one⟩
theorem cell1055_ok : cell1055.check T = true := by decide +kernel

def cell1056 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (36593 / 2560 : ℚ), (91681 / 6400 : ℚ), (.chain [(11, 27)]), (.chain [(11, 27)]), (.chain [(11, 27)]), (.chain [(11, 27), (11, 28)]), (.chain [(11, 27), (11, 28), (11, 29)]), (.chain [(11, 27), (11, 28), (11, 29)]), .one⟩
theorem cell1056_ok : cell1056.check T = true := by decide +kernel

def cell1057 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (91681 / 6400 : ℚ), (183759 / 12800 : ℚ), (.chain [(11, 28)]), (.chain [(11, 28)]), (.chain [(11, 28)]), (.chain [(11, 28), (11, 29)]), (.chain [(11, 28), (11, 29), (11, 30)]), (.chain [(11, 28), (11, 29), (11, 30)]), .one⟩
theorem cell1057_ok : cell1057.check T = true := by decide +kernel

def cell1058 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (183759 / 12800 : ℚ), (46039 / 3200 : ℚ), (.chain [(11, 29)]), (.chain [(11, 29)]), (.chain [(11, 29)]), (.chain [(11, 29), (11, 30)]), (.chain [(11, 29), (11, 30), (11, 31)]), (.chain [(11, 29), (11, 30)]), .one⟩
theorem cell1058_ok : cell1058.check T = true := by decide +kernel

def cell1059 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (46039 / 3200 : ℚ), (184553 / 12800 : ℚ), (.chain [(11, 30)]), (.chain [(11, 30)]), (.chain [(11, 30)]), (.chain [(11, 30), (11, 31)]), (.chain [(11, 30), (11, 31), (12, 0)]), (.chain [(11, 30), (11, 31)]), .one⟩
theorem cell1059_ok : cell1059.check T = true := by decide +kernel

def cell1060 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (184553 / 12800 : ℚ), (3699 / 256 : ℚ), (.chain [(11, 31)]), (.chain [(11, 31)]), (.chain [(11, 31)]), (.chain [(11, 31)]), (.chain [(11, 31), (12, 0)]), (.chain [(11, 31), (12, 0)]), .one⟩
theorem cell1060_ok : cell1060.check T = true := by decide +kernel

def cell1061 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (3699 / 256 : ℚ), (185347 / 12800 : ℚ), (.chain [(11, 31)]), (.chain [(11, 31)]), (.chain [(11, 31)]), (.chain [(11, 31), (12, 0)]), (.chain [(11, 31), (12, 0), (12, 1)]), (.chain [(11, 31), (12, 0), (12, 1)]), .one⟩
theorem cell1061_ok : cell1061.check T = true := by decide +kernel

def cell1062 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (185347 / 12800 : ℚ), (11609 / 800 : ℚ), (.chain [(12, 0)]), (.chain [(12, 0)]), (.chain [(12, 0)]), (.chain [(12, 0), (12, 1)]), (.chain [(12, 0), (12, 1), (12, 2)]), (.chain [(12, 0), (12, 1)]), .one⟩
theorem cell1062_ok : cell1062.check T = true := by decide +kernel

def cell1063 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (11609 / 800 : ℚ), (186141 / 12800 : ℚ), (.chain [(12, 1)]), (.chain [(12, 1)]), (.chain [(12, 1)]), (.chain [(12, 1), (12, 2)]), (.chain [(12, 1), (12, 2), (12, 3)]), (.chain [(12, 1), (12, 2)]), .one⟩
theorem cell1063_ok : cell1063.check T = true := by decide +kernel

def cell1064 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (186141 / 12800 : ℚ), (93269 / 6400 : ℚ), (.chain [(12, 2)]), (.chain [(12, 2)]), (.chain [(12, 2)]), (.chain [(12, 2)]), (.chain [(12, 2), (12, 3)]), (.chain [(12, 2), (12, 3)]), .one⟩
theorem cell1064_ok : cell1064.check T = true := by decide +kernel

def cell1065 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (93269 / 6400 : ℚ), (37387 / 2560 : ℚ), (.chain [(12, 2)]), (.chain [(12, 2)]), (.chain [(12, 2)]), (.chain [(12, 2), (12, 3)]), (.chain [(12, 2), (12, 3), (12, 4)]), (.chain [(12, 2), (12, 3), (12, 4)]), .one⟩
theorem cell1065_ok : cell1065.check T = true := by decide +kernel

def cell1066 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (37387 / 2560 : ℚ), (46833 / 3200 : ℚ), (.chain [(12, 3)]), (.chain [(12, 3)]), (.chain [(12, 3)]), (.chain [(12, 3), (12, 4)]), (.chain [(12, 3), (12, 4), (12, 5)]), (.chain [(12, 3), (12, 4), (12, 5)]), .one⟩
theorem cell1066_ok : cell1066.check T = true := by decide +kernel

def cell1067 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (46833 / 3200 : ℚ), (187729 / 12800 : ℚ), (.chain [(12, 4)]), (.chain [(12, 4)]), (.chain [(12, 4)]), (.chain [(12, 4), (12, 5)]), (.chain [(12, 4), (12, 5), (12, 6)]), (.chain [(12, 4), (12, 5)]), .one⟩
theorem cell1067_ok : cell1067.check T = true := by decide +kernel

def cell1068 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (187729 / 12800 : ℚ), (94063 / 6400 : ℚ), (.chain [(12, 5)]), (.chain [(12, 5)]), (.chain [(12, 5)]), (.chain [(12, 5), (12, 6)]), (.chain [(12, 5), (12, 6), (12, 7)]), (.chain [(12, 5), (12, 6)]), .one⟩
theorem cell1068_ok : cell1068.check T = true := by decide +kernel

def cell1069 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (94063 / 6400 : ℚ), (188523 / 12800 : ℚ), (.chain [(12, 6)]), (.chain [(12, 6)]), (.chain [(12, 6)]), (.chain [(12, 6)]), (.chain [(12, 6), (12, 7)]), (.chain [(12, 6), (12, 7)]), .one⟩
theorem cell1069_ok : cell1069.check T = true := by decide +kernel

def cell1070 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (188523 / 12800 : ℚ), (4723 / 320 : ℚ), (.chain [(12, 6)]), (.chain [(12, 6)]), (.chain [(12, 6)]), (.chain [(12, 6), (12, 7)]), (.chain [(12, 6), (12, 7), (12, 8)]), (.chain [(12, 6), (12, 7), (12, 8)]), .one⟩
theorem cell1070_ok : cell1070.check T = true := by decide +kernel

def cell1071 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (4723 / 320 : ℚ), (189317 / 12800 : ℚ), (.chain [(12, 7)]), (.chain [(12, 7)]), (.chain [(12, 7)]), (.chain [(12, 7), (12, 8)]), (.chain [(12, 7), (12, 8), (12, 9)]), (.chain [(12, 7), (12, 8)]), .one⟩
theorem cell1071_ok : cell1071.check T = true := by decide +kernel

def cell1072 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (189317 / 12800 : ℚ), (94857 / 6400 : ℚ), (.chain [(12, 8)]), (.chain [(12, 8)]), (.chain [(12, 8)]), (.chain [(12, 8), (12, 9)]), (.chain [(12, 8), (12, 9), (12, 10)]), (.chain [(12, 8), (12, 9)]), .one⟩
theorem cell1072_ok : cell1072.check T = true := by decide +kernel

def cell1073 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (94857 / 6400 : ℚ), (190111 / 12800 : ℚ), (.chain [(12, 9)]), (.chain [(12, 9)]), (.chain [(12, 9)]), (.chain [(12, 9)]), (.chain [(12, 9), (12, 10)]), (.chain [(12, 9), (12, 10)]), .one⟩
theorem cell1073_ok : cell1073.check T = true := by decide +kernel

def cell1074 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (190111 / 12800 : ℚ), (47627 / 3200 : ℚ), (.chain [(12, 9)]), (.chain [(12, 9)]), (.chain [(12, 9)]), (.chain [(12, 9), (12, 10)]), (.chain [(12, 9), (12, 10), (12, 11)]), (.chain [(12, 9), (12, 10), (12, 11)]), .one⟩
theorem cell1074_ok : cell1074.check T = true := by decide +kernel

def cell1075 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (47627 / 3200 : ℚ), (38181 / 2560 : ℚ), (.chain [(12, 10)]), (.chain [(12, 10)]), (.chain [(12, 10)]), (.chain [(12, 10), (12, 11)]), (.chain [(12, 10), (12, 11), (12, 12)]), (.chain [(12, 10), (12, 11)]), .one⟩
theorem cell1075_ok : cell1075.check T = true := by decide +kernel

def cell1076 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (38181 / 2560 : ℚ), (95651 / 6400 : ℚ), (.chain [(12, 11)]), (.chain [(12, 11)]), (.chain [(12, 11)]), (.chain [(12, 11), (12, 12)]), (.chain [(12, 11), (12, 12), (12, 13)]), (.chain [(12, 11), (12, 12)]), .one⟩
theorem cell1076_ok : cell1076.check T = true := by decide +kernel

def cell1077 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (95651 / 6400 : ℚ), (191699 / 12800 : ℚ), (.chain [(12, 12)]), (.chain [(12, 12)]), (.chain [(12, 12)]), (.chain [(12, 12), (12, 13)]), (.chain [(12, 12), (12, 13), (12, 14)]), (.chain [(12, 12), (12, 13)]), .one⟩
theorem cell1077_ok : cell1077.check T = true := by decide +kernel

def cell1078 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (191699 / 12800 : ℚ), (6003 / 400 : ℚ), (.chain [(12, 13)]), (.chain [(12, 13)]), (.chain [(12, 13)]), (.chain [(12, 13)]), (.chain [(12, 13), (12, 14)]), (.chain [(12, 13), (12, 14)]), .one⟩
theorem cell1078_ok : cell1078.check T = true := by decide +kernel

def cell1079 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (6003 / 400 : ℚ), (192493 / 12800 : ℚ), (.chain [(12, 13)]), (.chain [(12, 13)]), (.chain [(12, 13)]), (.chain [(12, 13), (12, 14)]), (.chain [(12, 13), (12, 14), (12, 15)]), (.chain [(12, 13), (12, 14), (12, 15)]), .one⟩
theorem cell1079_ok : cell1079.check T = true := by decide +kernel

def cells26 : List CellW := [cell1040, cell1041, cell1042, cell1043, cell1044, cell1045, cell1046, cell1047, cell1048, cell1049, cell1050, cell1051, cell1052, cell1053, cell1054, cell1055, cell1056, cell1057, cell1058, cell1059, cell1060, cell1061, cell1062, cell1063, cell1064, cell1065, cell1066, cell1067, cell1068, cell1069, cell1070, cell1071, cell1072, cell1073, cell1074, cell1075, cell1076, cell1077, cell1078, cell1079]

theorem cells26_valid : ∀ w ∈ cells26, w.check T = true :=
  (forall_mem_cons_of cell1040_ok (forall_mem_cons_of cell1041_ok (forall_mem_cons_of cell1042_ok (forall_mem_cons_of cell1043_ok (forall_mem_cons_of cell1044_ok (forall_mem_cons_of cell1045_ok (forall_mem_cons_of cell1046_ok (forall_mem_cons_of cell1047_ok (forall_mem_cons_of cell1048_ok (forall_mem_cons_of cell1049_ok (forall_mem_cons_of cell1050_ok (forall_mem_cons_of cell1051_ok (forall_mem_cons_of cell1052_ok (forall_mem_cons_of cell1053_ok (forall_mem_cons_of cell1054_ok (forall_mem_cons_of cell1055_ok (forall_mem_cons_of cell1056_ok (forall_mem_cons_of cell1057_ok (forall_mem_cons_of cell1058_ok (forall_mem_cons_of cell1059_ok (forall_mem_cons_of cell1060_ok (forall_mem_cons_of cell1061_ok (forall_mem_cons_of cell1062_ok (forall_mem_cons_of cell1063_ok (forall_mem_cons_of cell1064_ok (forall_mem_cons_of cell1065_ok (forall_mem_cons_of cell1066_ok (forall_mem_cons_of cell1067_ok (forall_mem_cons_of cell1068_ok (forall_mem_cons_of cell1069_ok (forall_mem_cons_of cell1070_ok (forall_mem_cons_of cell1071_ok (forall_mem_cons_of cell1072_ok (forall_mem_cons_of cell1073_ok (forall_mem_cons_of cell1074_ok (forall_mem_cons_of cell1075_ok (forall_mem_cons_of cell1076_ok (forall_mem_cons_of cell1077_ok (forall_mem_cons_of cell1078_ok (forall_mem_cons_of cell1079_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


