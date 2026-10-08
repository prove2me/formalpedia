-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells25
-- name    : CK_CKLaneC_SAxis_Data_Cells25
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T08:02:01.14082+00:00
-- url     : https://prove2.me/theorems/a975e2b4-a333-40a8-a2e3-865cb64a6f19
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells25` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells25` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells25` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells25 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells25.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells25 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 25 (cells 1000..1039). -/

def cell1000 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (160733 / 12800 : ℚ), (16113 / 1280 : ℚ), (.chain [(10, 16)]), (.chain [(10, 16)]), (.chain [(10, 16)]), (.chain [(10, 16), (10, 17)]), (.chain [(10, 16), (10, 17), (10, 18)]), (.chain [(10, 16), (10, 17)]), .one⟩
theorem cell1000_ok : cell1000.check T = true := by decide +kernel

def cell1001 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (16113 / 1280 : ℚ), (161527 / 12800 : ℚ), (.chain [(10, 17)]), (.chain [(10, 17)]), (.chain [(10, 17)]), (.chain [(10, 17), (10, 18)]), (.chain [(10, 17), (10, 18), (10, 19)]), (.chain [(10, 17), (10, 18)]), .one⟩
theorem cell1001_ok : cell1001.check T = true := by decide +kernel

def cell1002 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (161527 / 12800 : ℚ), (40481 / 3200 : ℚ), (.chain [(10, 18)]), (.chain [(10, 18)]), (.chain [(10, 18)]), (.chain [(10, 18)]), (.chain [(10, 18), (10, 19)]), (.chain [(10, 18), (10, 19)]), .one⟩
theorem cell1002_ok : cell1002.check T = true := by decide +kernel

def cell1003 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (40481 / 3200 : ℚ), (162321 / 12800 : ℚ), (.chain [(10, 18)]), (.chain [(10, 18)]), (.chain [(10, 18)]), (.chain [(10, 18), (10, 19)]), (.chain [(10, 18), (10, 19), (10, 20)]), (.chain [(10, 18), (10, 19), (10, 20)]), .one⟩
theorem cell1003_ok : cell1003.check T = true := by decide +kernel

def cell1004 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (162321 / 12800 : ℚ), (81359 / 6400 : ℚ), (.chain [(10, 19)]), (.chain [(10, 19)]), (.chain [(10, 19)]), (.chain [(10, 19), (10, 20)]), (.chain [(10, 19), (10, 20), (10, 21)]), (.chain [(10, 19), (10, 20)]), .one⟩
theorem cell1004_ok : cell1004.check T = true := by decide +kernel

def cell1005 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (81359 / 6400 : ℚ), (32623 / 2560 : ℚ), (.chain [(10, 20)]), (.chain [(10, 20)]), (.chain [(10, 20)]), (.chain [(10, 20), (10, 21)]), (.chain [(10, 20), (10, 21), (10, 22)]), (.chain [(10, 20), (10, 21)]), .one⟩
theorem cell1005_ok : cell1005.check T = true := by decide +kernel

def cell1006 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (32623 / 2560 : ℚ), (20439 / 1600 : ℚ), (.chain [(10, 21)]), (.chain [(10, 21)]), (.chain [(10, 21)]), (.chain [(10, 21)]), (.chain [(10, 21), (10, 22)]), (.chain [(10, 21), (10, 22)]), .one⟩
theorem cell1006_ok : cell1006.check T = true := by decide +kernel

def cell1007 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (20439 / 1600 : ℚ), (163909 / 12800 : ℚ), (.chain [(10, 21)]), (.chain [(10, 21)]), (.chain [(10, 21)]), (.chain [(10, 21), (10, 22)]), (.chain [(10, 21), (10, 22), (10, 23)]), (.chain [(10, 21), (10, 22), (10, 23)]), .one⟩
theorem cell1007_ok : cell1007.check T = true := by decide +kernel

def cell1008 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (163909 / 12800 : ℚ), (82153 / 6400 : ℚ), (.chain [(10, 22)]), (.chain [(10, 22)]), (.chain [(10, 22)]), (.chain [(10, 22), (10, 23)]), (.chain [(10, 22), (10, 23), (10, 24)]), (.chain [(10, 22), (10, 23), (10, 24)]), .one⟩
theorem cell1008_ok : cell1008.check T = true := by decide +kernel

def cell1009 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (82153 / 6400 : ℚ), (164703 / 12800 : ℚ), (.chain [(10, 23)]), (.chain [(10, 23)]), (.chain [(10, 23)]), (.chain [(10, 23), (10, 24)]), (.chain [(10, 23), (10, 24), (10, 25)]), (.chain [(10, 23), (10, 24)]), .one⟩
theorem cell1009_ok : cell1009.check T = true := by decide +kernel

def cell1010 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (164703 / 12800 : ℚ), (1651 / 128 : ℚ), (.chain [(10, 24)]), (.chain [(10, 24)]), (.chain [(10, 24)]), (.chain [(10, 24), (10, 25)]), (.chain [(10, 24), (10, 25), (10, 26)]), (.chain [(10, 24), (10, 25)]), .one⟩
theorem cell1010_ok : cell1010.check T = true := by decide +kernel

def cell1011 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (1651 / 128 : ℚ), (165497 / 12800 : ℚ), (.chain [(10, 25)]), (.chain [(10, 25)]), (.chain [(10, 25)]), (.chain [(10, 25)]), (.chain [(10, 25), (10, 26)]), (.chain [(10, 25), (10, 26)]), .one⟩
theorem cell1011_ok : cell1011.check T = true := by decide +kernel

def cell1012 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (165497 / 12800 : ℚ), (82947 / 6400 : ℚ), (.chain [(10, 25)]), (.chain [(10, 25)]), (.chain [(10, 25)]), (.chain [(10, 25), (10, 26)]), (.chain [(10, 25), (10, 26), (10, 27)]), (.chain [(10, 25), (10, 26), (10, 27)]), .one⟩
theorem cell1012_ok : cell1012.check T = true := by decide +kernel

def cell1013 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (82947 / 6400 : ℚ), (166291 / 12800 : ℚ), (.chain [(10, 26)]), (.chain [(10, 26)]), (.chain [(10, 26)]), (.chain [(10, 26), (10, 27)]), (.chain [(10, 26), (10, 27), (10, 28)]), (.chain [(10, 26), (10, 27)]), .one⟩
theorem cell1013_ok : cell1013.check T = true := by decide +kernel

def cell1014 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (166291 / 12800 : ℚ), (5209 / 400 : ℚ), (.chain [(10, 27)]), (.chain [(10, 27)]), (.chain [(10, 27)]), (.chain [(10, 27), (10, 28)]), (.chain [(10, 27), (10, 28), (10, 29)]), (.chain [(10, 27), (10, 28)]), .one⟩
theorem cell1014_ok : cell1014.check T = true := by decide +kernel

def cell1015 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (5209 / 400 : ℚ), (33417 / 2560 : ℚ), (.chain [(10, 28)]), (.chain [(10, 28)]), (.chain [(10, 28)]), (.chain [(10, 28)]), (.chain [(10, 28), (10, 29)]), (.chain [(10, 28), (10, 29)]), .one⟩
theorem cell1015_ok : cell1015.check T = true := by decide +kernel

def cell1016 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (33417 / 2560 : ℚ), (83741 / 6400 : ℚ), (.chain [(10, 28)]), (.chain [(10, 28)]), (.chain [(10, 28)]), (.chain [(10, 28), (10, 29)]), (.chain [(10, 28), (10, 29), (10, 30)]), (.chain [(10, 28), (10, 29), (10, 30)]), .one⟩
theorem cell1016_ok : cell1016.check T = true := by decide +kernel

def cell1017 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (83741 / 6400 : ℚ), (167879 / 12800 : ℚ), (.chain [(10, 29)]), (.chain [(10, 29)]), (.chain [(10, 29)]), (.chain [(10, 29), (10, 30)]), (.chain [(10, 29), (10, 30), (10, 31)]), (.chain [(10, 29), (10, 30), (10, 31)]), .one⟩
theorem cell1017_ok : cell1017.check T = true := by decide +kernel

def cell1018 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (167879 / 12800 : ℚ), (42069 / 3200 : ℚ), (.chain [(10, 30)]), (.chain [(10, 30)]), (.chain [(10, 30)]), (.chain [(10, 30), (10, 31)]), (.chain [(10, 30), (10, 31), (11, 0)]), (.chain [(10, 30), (10, 31)]), .one⟩
theorem cell1018_ok : cell1018.check T = true := by decide +kernel

def cell1019 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (42069 / 3200 : ℚ), (168673 / 12800 : ℚ), (.chain [(10, 31)]), (.chain [(10, 31)]), (.chain [(10, 31)]), (.chain [(10, 31), (11, 0)]), (.chain [(10, 31), (11, 0), (11, 1)]), (.chain [(10, 31), (11, 0)]), .one⟩
theorem cell1019_ok : cell1019.check T = true := by decide +kernel

def cell1020 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (168673 / 12800 : ℚ), (16907 / 1280 : ℚ), (.chain [(11, 0)]), (.chain [(11, 0)]), (.chain [(11, 0)]), (.chain [(11, 0)]), (.chain [(11, 0), (11, 1)]), (.chain [(11, 0), (11, 1)]), .one⟩
theorem cell1020_ok : cell1020.check T = true := by decide +kernel

def cell1021 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (16907 / 1280 : ℚ), (169467 / 12800 : ℚ), (.chain [(11, 0)]), (.chain [(11, 0)]), (.chain [(11, 0)]), (.chain [(11, 0), (11, 1)]), (.chain [(11, 0), (11, 1), (11, 2)]), (.chain [(11, 0), (11, 1), (11, 2)]), .one⟩
theorem cell1021_ok : cell1021.check T = true := by decide +kernel

def cell1022 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (169467 / 12800 : ℚ), (21233 / 1600 : ℚ), (.chain [(11, 1)]), (.chain [(11, 1)]), (.chain [(11, 1)]), (.chain [(11, 1), (11, 2)]), (.chain [(11, 1), (11, 2), (11, 3)]), (.chain [(11, 1), (11, 2)]), .one⟩
theorem cell1022_ok : cell1022.check T = true := by decide +kernel

def cell1023 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (21233 / 1600 : ℚ), (170261 / 12800 : ℚ), (.chain [(11, 2)]), (.chain [(11, 2)]), (.chain [(11, 2)]), (.chain [(11, 2), (11, 3)]), (.chain [(11, 2), (11, 3), (11, 4)]), (.chain [(11, 2), (11, 3)]), .one⟩
theorem cell1023_ok : cell1023.check T = true := by decide +kernel

def cell1024 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (170261 / 12800 : ℚ), (85329 / 6400 : ℚ), (.chain [(11, 3)]), (.chain [(11, 3)]), (.chain [(11, 3)]), (.chain [(11, 3)]), (.chain [(11, 3), (11, 4)]), (.chain [(11, 3), (11, 4)]), .one⟩
theorem cell1024_ok : cell1024.check T = true := by decide +kernel

def cell1025 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (85329 / 6400 : ℚ), (34211 / 2560 : ℚ), (.chain [(11, 3)]), (.chain [(11, 3)]), (.chain [(11, 3)]), (.chain [(11, 3), (11, 4)]), (.chain [(11, 3), (11, 4), (11, 5)]), (.chain [(11, 3), (11, 4), (11, 5)]), .one⟩
theorem cell1025_ok : cell1025.check T = true := by decide +kernel

def cell1026 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (34211 / 2560 : ℚ), (42863 / 3200 : ℚ), (.chain [(11, 4)]), (.chain [(11, 4)]), (.chain [(11, 4)]), (.chain [(11, 4), (11, 5)]), (.chain [(11, 4), (11, 5), (11, 6)]), (.chain [(11, 4), (11, 5)]), .one⟩
theorem cell1026_ok : cell1026.check T = true := by decide +kernel

def cell1027 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (42863 / 3200 : ℚ), (171849 / 12800 : ℚ), (.chain [(11, 5)]), (.chain [(11, 5)]), (.chain [(11, 5)]), (.chain [(11, 5), (11, 6)]), (.chain [(11, 5), (11, 6), (11, 7)]), (.chain [(11, 5), (11, 6)]), .one⟩
theorem cell1027_ok : cell1027.check T = true := by decide +kernel

def cell1028 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (171849 / 12800 : ℚ), (86123 / 6400 : ℚ), (.chain [(11, 6)]), (.chain [(11, 6)]), (.chain [(11, 6)]), (.chain [(11, 6), (11, 7)]), (.chain [(11, 6), (11, 7), (11, 8)]), (.chain [(11, 6), (11, 7)]), .one⟩
theorem cell1028_ok : cell1028.check T = true := by decide +kernel

def cell1029 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (86123 / 6400 : ℚ), (172643 / 12800 : ℚ), (.chain [(11, 7)]), (.chain [(11, 7)]), (.chain [(11, 7)]), (.chain [(11, 7)]), (.chain [(11, 7), (11, 8)]), (.chain [(11, 7), (11, 8)]), .one⟩
theorem cell1029_ok : cell1029.check T = true := by decide +kernel

def cell1030 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (172643 / 12800 : ℚ), (2163 / 160 : ℚ), (.chain [(11, 7)]), (.chain [(11, 7)]), (.chain [(11, 7)]), (.chain [(11, 7), (11, 8)]), (.chain [(11, 7), (11, 8), (11, 9)]), (.chain [(11, 7), (11, 8), (11, 9)]), .one⟩
theorem cell1030_ok : cell1030.check T = true := by decide +kernel

def cell1031 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (2163 / 160 : ℚ), (173437 / 12800 : ℚ), (.chain [(11, 8)]), (.chain [(11, 8)]), (.chain [(11, 8)]), (.chain [(11, 8), (11, 9)]), (.chain [(11, 8), (11, 9), (11, 10)]), (.chain [(11, 8), (11, 9)]), .one⟩
theorem cell1031_ok : cell1031.check T = true := by decide +kernel

def cell1032 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (173437 / 12800 : ℚ), (86917 / 6400 : ℚ), (.chain [(11, 9)]), (.chain [(11, 9)]), (.chain [(11, 9)]), (.chain [(11, 9), (11, 10)]), (.chain [(11, 9), (11, 10), (11, 11)]), (.chain [(11, 9), (11, 10)]), .one⟩
theorem cell1032_ok : cell1032.check T = true := by decide +kernel

def cell1033 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (86917 / 6400 : ℚ), (174231 / 12800 : ℚ), (.chain [(11, 10)]), (.chain [(11, 10)]), (.chain [(11, 10)]), (.chain [(11, 10)]), (.chain [(11, 10), (11, 11)]), (.chain [(11, 10), (11, 11)]), .one⟩
theorem cell1033_ok : cell1033.check T = true := by decide +kernel

def cell1034 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (174231 / 12800 : ℚ), (43657 / 3200 : ℚ), (.chain [(11, 10)]), (.chain [(11, 10)]), (.chain [(11, 10)]), (.chain [(11, 10), (11, 11)]), (.chain [(11, 10), (11, 11), (11, 12)]), (.chain [(11, 10), (11, 11), (11, 12)]), .one⟩
theorem cell1034_ok : cell1034.check T = true := by decide +kernel

def cell1035 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (43657 / 3200 : ℚ), (7001 / 512 : ℚ), (.chain [(11, 11)]), (.chain [(11, 11)]), (.chain [(11, 11)]), (.chain [(11, 11), (11, 12)]), (.chain [(11, 11), (11, 12), (11, 13)]), (.chain [(11, 11), (11, 12)]), .one⟩
theorem cell1035_ok : cell1035.check T = true := by decide +kernel

def cell1036 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (7001 / 512 : ℚ), (87711 / 6400 : ℚ), (.chain [(11, 12)]), (.chain [(11, 12)]), (.chain [(11, 12)]), (.chain [(11, 12), (11, 13)]), (.chain [(11, 12), (11, 13), (11, 14)]), (.chain [(11, 12), (11, 13)]), .one⟩
theorem cell1036_ok : cell1036.check T = true := by decide +kernel

def cell1037 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (87711 / 6400 : ℚ), (175819 / 12800 : ℚ), (.chain [(11, 13)]), (.chain [(11, 13)]), (.chain [(11, 13)]), (.chain [(11, 13), (11, 14)]), (.chain [(11, 13), (11, 14), (11, 15)]), (.chain [(11, 13), (11, 14)]), .one⟩
theorem cell1037_ok : cell1037.check T = true := by decide +kernel

def cell1038 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (175819 / 12800 : ℚ), (22027 / 1600 : ℚ), (.chain [(11, 14)]), (.chain [(11, 14)]), (.chain [(11, 14)]), (.chain [(11, 14)]), (.chain [(11, 14), (11, 15)]), (.chain [(11, 14), (11, 15)]), .one⟩
theorem cell1038_ok : cell1038.check T = true := by decide +kernel

def cell1039 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (22027 / 1600 : ℚ), (176613 / 12800 : ℚ), (.chain [(11, 14)]), (.chain [(11, 14)]), (.chain [(11, 14)]), (.chain [(11, 14), (11, 15)]), (.chain [(11, 14), (11, 15), (11, 16)]), (.chain [(11, 14), (11, 15), (11, 16)]), .one⟩
theorem cell1039_ok : cell1039.check T = true := by decide +kernel

def cells25 : List CellW := [cell1000, cell1001, cell1002, cell1003, cell1004, cell1005, cell1006, cell1007, cell1008, cell1009, cell1010, cell1011, cell1012, cell1013, cell1014, cell1015, cell1016, cell1017, cell1018, cell1019, cell1020, cell1021, cell1022, cell1023, cell1024, cell1025, cell1026, cell1027, cell1028, cell1029, cell1030, cell1031, cell1032, cell1033, cell1034, cell1035, cell1036, cell1037, cell1038, cell1039]

theorem cells25_valid : ∀ w ∈ cells25, w.check T = true :=
  (forall_mem_cons_of cell1000_ok (forall_mem_cons_of cell1001_ok (forall_mem_cons_of cell1002_ok (forall_mem_cons_of cell1003_ok (forall_mem_cons_of cell1004_ok (forall_mem_cons_of cell1005_ok (forall_mem_cons_of cell1006_ok (forall_mem_cons_of cell1007_ok (forall_mem_cons_of cell1008_ok (forall_mem_cons_of cell1009_ok (forall_mem_cons_of cell1010_ok (forall_mem_cons_of cell1011_ok (forall_mem_cons_of cell1012_ok (forall_mem_cons_of cell1013_ok (forall_mem_cons_of cell1014_ok (forall_mem_cons_of cell1015_ok (forall_mem_cons_of cell1016_ok (forall_mem_cons_of cell1017_ok (forall_mem_cons_of cell1018_ok (forall_mem_cons_of cell1019_ok (forall_mem_cons_of cell1020_ok (forall_mem_cons_of cell1021_ok (forall_mem_cons_of cell1022_ok (forall_mem_cons_of cell1023_ok (forall_mem_cons_of cell1024_ok (forall_mem_cons_of cell1025_ok (forall_mem_cons_of cell1026_ok (forall_mem_cons_of cell1027_ok (forall_mem_cons_of cell1028_ok (forall_mem_cons_of cell1029_ok (forall_mem_cons_of cell1030_ok (forall_mem_cons_of cell1031_ok (forall_mem_cons_of cell1032_ok (forall_mem_cons_of cell1033_ok (forall_mem_cons_of cell1034_ok (forall_mem_cons_of cell1035_ok (forall_mem_cons_of cell1036_ok (forall_mem_cons_of cell1037_ok (forall_mem_cons_of cell1038_ok (forall_mem_cons_of cell1039_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


