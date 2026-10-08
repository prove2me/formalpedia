-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells00
-- name    : CK_CKLaneC_SAxis_Data_Cells00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:32:07.742184+00:00
-- url     : https://prove2.me/theorems/8d072adc-47cf-4b20-8afc-2d6a9f00911e
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells00` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells00` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells00` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells00 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells00.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells00 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 0 (cells 0..39). -/

def cell0000 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (27 / 400 : ℚ), (3 / 40 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0000_ok : cell0000.check T = true := by decide +kernel

def cell0001 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (3 / 40 : ℚ), (33 / 400 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0001_ok : cell0001.check T = true := by decide +kernel

def cell0002 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (33 / 400 : ℚ), (9 / 100 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0002_ok : cell0002.check T = true := by decide +kernel

def cell0003 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (3 / 40 : ℚ), (9 / 100 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0003_ok : cell0003.check T = true := by decide +kernel

def cell0004 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (3 / 50 : ℚ), (27 / 400 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0004_ok : cell0004.check T = true := by decide +kernel

def cell0005 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (27 / 400 : ℚ), (3 / 40 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0005_ok : cell0005.check T = true := by decide +kernel

def cell0006 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (3 / 50 : ℚ), (3 / 40 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0006_ok : cell0006.check T = true := by decide +kernel

def cell0007 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (3 / 40 : ℚ), (9 / 100 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0007_ok : cell0007.check T = true := by decide +kernel

def cell0008 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (3 / 40 : ℚ), (9 / 100 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0008_ok : cell0008.check T = true := by decide +kernel

def cell0009 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (9 / 100 : ℚ), (21 / 200 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0009_ok : cell0009.check T = true := by decide +kernel

def cell0010 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (9 / 100 : ℚ), (21 / 200 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0010_ok : cell0010.check T = true := by decide +kernel

def cell0011 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (21 / 200 : ℚ), (3 / 25 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0011_ok : cell0011.check T = true := by decide +kernel

def cell0012 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (21 / 200 : ℚ), (3 / 25 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0012_ok : cell0012.check T = true := by decide +kernel

def cell0013 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (9 / 100 : ℚ), (21 / 200 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0013_ok : cell0013.check T = true := by decide +kernel

def cell0014 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (21 / 200 : ℚ), (3 / 25 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0014_ok : cell0014.check T = true := by decide +kernel

def cell0015 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (3 / 25 : ℚ), (3469 / 25600 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0015_ok : cell0015.check T = true := by decide +kernel

def cell0016 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (3 / 25 : ℚ), (6541 / 51200 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0016_ok : cell0016.check T = true := by decide +kernel

def cell0017 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (6541 / 51200 : ℚ), (3469 / 25600 : ℚ), .reg, .reg, .reg, .reg, (.chain [(0, 8), (0, 9), (0, 10)]), .reg, .three⟩
theorem cell0017_ok : cell0017.check T = true := by decide +kernel

def cell0018 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (3 / 25 : ℚ), (6541 / 51200 : ℚ), .reg, .reg, .reg, .reg, (.chain [(0, 8), (0, 9), (0, 10)]), .reg, .three⟩
theorem cell0018_ok : cell0018.check T = true := by decide +kernel

def cell0019 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (6541 / 51200 : ℚ), (3469 / 25600 : ℚ), .reg, .reg, .reg, .reg, (.chain [(0, 9), (0, 10), (0, 11)]), .reg, .three⟩
theorem cell0019_ok : cell0019.check T = true := by decide +kernel

def cell0020 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (3469 / 25600 : ℚ), (1467 / 10240 : ℚ), .reg, .reg, .reg, .reg, .reg, .reg, .three⟩
theorem cell0020_ok : cell0020.check T = true := by decide +kernel

def cell0021 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (1467 / 10240 : ℚ), (1933 / 12800 : ℚ), .reg, .reg, .reg, .reg, (.chain [(0, 7), (0, 8), (0, 9)]), .reg, .three⟩
theorem cell0021_ok : cell0021.check T = true := by decide +kernel

def cell0022 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (3469 / 25600 : ℚ), (1467 / 10240 : ℚ), .reg, .reg, .reg, .reg, (.chain [(0, 7), (0, 8), (0, 9), (0, 10)]), .reg, .three⟩
theorem cell0022_ok : cell0022.check T = true := by decide +kernel

def cell0023 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (1467 / 10240 : ℚ), (1933 / 12800 : ℚ), .reg, .reg, .reg, .reg, (.chain [(0, 8), (0, 9), (0, 10)]), (.chain [(0, 8), (0, 9)]), .three⟩
theorem cell0023_ok : cell0023.check T = true := by decide +kernel

def cell0024 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (3469 / 25600 : ℚ), (1467 / 10240 : ℚ), .reg, .reg, .reg, .reg, (.chain [(0, 9), (0, 10), (0, 11)]), .reg, .three⟩
theorem cell0024_ok : cell0024.check T = true := by decide +kernel

def cell0025 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (1467 / 10240 : ℚ), (1933 / 12800 : ℚ), .reg, (.chain [(0, 10)]), .reg, .reg, (.chain [(0, 10), (0, 11), (0, 12)]), (.chain [(0, 8), (0, 9), (0, 10)]), .three⟩
theorem cell0025_ok : cell0025.check T = true := by decide +kernel

def cell0026 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (3469 / 25600 : ℚ), (1467 / 10240 : ℚ), .reg, (.chain [(0, 10)]), .reg, .reg, (.chain [(0, 10), (0, 11), (0, 12)]), (.chain [(0, 8), (0, 9), (0, 10)]), .three⟩
theorem cell0026_ok : cell0026.check T = true := by decide +kernel

def cell0027 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (1467 / 10240 : ℚ), (1933 / 12800 : ℚ), .reg, (.chain [(0, 11)]), .reg, .reg, (.chain [(0, 11), (0, 12), (0, 13)]), (.chain [(0, 9), (0, 10)]), .three⟩
theorem cell0027_ok : cell0027.check T = true := by decide +kernel

def cell0028 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (1933 / 12800 : ℚ), (8129 / 51200 : ℚ), .reg, .reg, .reg, .reg, (.chain [(0, 8), (0, 9), (0, 10)]), (.chain [(0, 8), (0, 9), (0, 10)]), .three⟩
theorem cell0028_ok : cell0028.check T = true := by decide +kernel

def cell0029 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (8129 / 51200 : ℚ), (4263 / 25600 : ℚ), .reg, .reg, .reg, (.chain [(0, 9), (0, 10)]), (.chain [(0, 9), (0, 10), (0, 11)]), (.chain [(0, 9), (0, 10), (0, 11)]), .three⟩
theorem cell0029_ok : cell0029.check T = true := by decide +kernel

def cell0030 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (1933 / 12800 : ℚ), (8129 / 51200 : ℚ), .reg, (.chain [(0, 9)]), .reg, .reg, (.chain [(0, 9), (0, 10), (0, 11)]), (.chain [(0, 9), (0, 10)]), .three⟩
theorem cell0030_ok : cell0030.check T = true := by decide +kernel

def cell0031 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (8129 / 51200 : ℚ), (4263 / 25600 : ℚ), .reg, (.chain [(0, 10)]), (.chain [(0, 10)]), (.chain [(0, 9), (0, 10)]), (.chain [(0, 10), (0, 11), (0, 12)]), (.chain [(0, 10), (0, 11)]), .three⟩
theorem cell0031_ok : cell0031.check T = true := by decide +kernel

def cell0032 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (1933 / 12800 : ℚ), (8129 / 51200 : ℚ), .reg, (.chain [(0, 10)]), (.chain [(0, 9)]), .reg, (.chain [(0, 10), (0, 11), (0, 12), (0, 13)]), (.chain [(0, 9), (0, 10), (0, 11)]), .three⟩
theorem cell0032_ok : cell0032.check T = true := by decide +kernel

def cell0033 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (8129 / 51200 : ℚ), (4263 / 25600 : ℚ), .reg, (.chain [(0, 11)]), (.chain [(0, 10)]), (.chain [(0, 9), (0, 10)]), (.chain [(0, 11), (0, 12), (0, 13)]), (.chain [(0, 10), (0, 11), (0, 12)]), .three⟩
theorem cell0033_ok : cell0033.check T = true := by decide +kernel

def cell0034 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (1933 / 12800 : ℚ), (8129 / 51200 : ℚ), .reg, (.chain [(0, 12)]), (.chain [(0, 10)]), .reg, (.chain [(0, 12), (0, 13), (0, 14)]), (.chain [(0, 10), (0, 11)]), .three⟩
theorem cell0034_ok : cell0034.check T = true := by decide +kernel

def cell0035 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (8129 / 51200 : ℚ), (4263 / 25600 : ℚ), .reg, (.chain [(0, 13)]), (.chain [(0, 11)]), (.chain [(0, 9), (0, 10)]), (.chain [(0, 13), (0, 14)]), (.chain [(0, 11), (0, 12)]), .three⟩
theorem cell0035_ok : cell0035.check T = true := by decide +kernel

def cell0036 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (4263 / 25600 : ℚ), (8923 / 51200 : ℚ), (.chain [(0, 10)]), (.chain [(0, 10)]), (.chain [(0, 10)]), (.chain [(0, 10), (0, 11)]), (.chain [(0, 10), (0, 11), (0, 12)]), (.chain [(0, 10), (0, 11)]), .three⟩
theorem cell0036_ok : cell0036.check T = true := by decide +kernel

def cell0037 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (8923 / 51200 : ℚ), (233 / 1280 : ℚ), (.chain [(0, 11)]), (.chain [(0, 11)]), (.chain [(0, 11)]), (.chain [(0, 11), (0, 12)]), (.chain [(0, 11), (0, 12), (0, 13)]), (.chain [(0, 11), (0, 12)]), .three⟩
theorem cell0037_ok : cell0037.check T = true := by decide +kernel

def cell0038 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (4263 / 25600 : ℚ), (8923 / 51200 : ℚ), (.chain [(0, 10)]), (.chain [(0, 11)]), (.chain [(0, 11)]), (.chain [(0, 10), (0, 11)]), (.chain [(0, 11), (0, 12), (0, 13)]), (.chain [(0, 11), (0, 12)]), .three⟩
theorem cell0038_ok : cell0038.check T = true := by decide +kernel

def cell0039 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (8923 / 51200 : ℚ), (233 / 1280 : ℚ), (.chain [(0, 11)]), (.chain [(0, 12)]), (.chain [(0, 11)]), (.chain [(0, 11), (0, 12)]), (.chain [(0, 12), (0, 13), (0, 14)]), (.chain [(0, 11), (0, 12), (0, 13)]), .three⟩
theorem cell0039_ok : cell0039.check T = true := by decide +kernel

def cells00 : List CellW := [cell0000, cell0001, cell0002, cell0003, cell0004, cell0005, cell0006, cell0007, cell0008, cell0009, cell0010, cell0011, cell0012, cell0013, cell0014, cell0015, cell0016, cell0017, cell0018, cell0019, cell0020, cell0021, cell0022, cell0023, cell0024, cell0025, cell0026, cell0027, cell0028, cell0029, cell0030, cell0031, cell0032, cell0033, cell0034, cell0035, cell0036, cell0037, cell0038, cell0039]

theorem cells00_valid : ∀ w ∈ cells00, w.check T = true :=
  (forall_mem_cons_of cell0000_ok (forall_mem_cons_of cell0001_ok (forall_mem_cons_of cell0002_ok (forall_mem_cons_of cell0003_ok (forall_mem_cons_of cell0004_ok (forall_mem_cons_of cell0005_ok (forall_mem_cons_of cell0006_ok (forall_mem_cons_of cell0007_ok (forall_mem_cons_of cell0008_ok (forall_mem_cons_of cell0009_ok (forall_mem_cons_of cell0010_ok (forall_mem_cons_of cell0011_ok (forall_mem_cons_of cell0012_ok (forall_mem_cons_of cell0013_ok (forall_mem_cons_of cell0014_ok (forall_mem_cons_of cell0015_ok (forall_mem_cons_of cell0016_ok (forall_mem_cons_of cell0017_ok (forall_mem_cons_of cell0018_ok (forall_mem_cons_of cell0019_ok (forall_mem_cons_of cell0020_ok (forall_mem_cons_of cell0021_ok (forall_mem_cons_of cell0022_ok (forall_mem_cons_of cell0023_ok (forall_mem_cons_of cell0024_ok (forall_mem_cons_of cell0025_ok (forall_mem_cons_of cell0026_ok (forall_mem_cons_of cell0027_ok (forall_mem_cons_of cell0028_ok (forall_mem_cons_of cell0029_ok (forall_mem_cons_of cell0030_ok (forall_mem_cons_of cell0031_ok (forall_mem_cons_of cell0032_ok (forall_mem_cons_of cell0033_ok (forall_mem_cons_of cell0034_ok (forall_mem_cons_of cell0035_ok (forall_mem_cons_of cell0036_ok (forall_mem_cons_of cell0037_ok (forall_mem_cons_of cell0038_ok (forall_mem_cons_of cell0039_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


