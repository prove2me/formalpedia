-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells01
-- name    : CK_CKLaneC_SAxis_Data_Cells01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T04:15:28.803693+00:00
-- url     : https://prove2.me/theorems/53705001-fc9a-41f2-a807-3ca523cbe9b8
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells01` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells01` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells01` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells01 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells01.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells01 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 1 (cells 40..79). -/

def cell0040 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (4263 / 25600 : ℚ), (8923 / 51200 : ℚ), (.chain [(0, 10)]), (.chain [(0, 12)]), (.chain [(0, 11)]), (.chain [(0, 10), (0, 11)]), (.chain [(0, 12), (0, 13), (0, 14)]), (.chain [(0, 11), (0, 12), (0, 13)]), .three⟩
theorem cell0040_ok : cell0040.check T = true := by decide +kernel

def cell0041 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (8923 / 51200 : ℚ), (233 / 1280 : ℚ), (.chain [(0, 11)]), (.chain [(0, 13)]), (.chain [(0, 12)]), (.chain [(0, 11), (0, 12)]), (.chain [(0, 13), (0, 14), (0, 15)]), (.chain [(0, 12), (0, 13)]), .three⟩
theorem cell0041_ok : cell0041.check T = true := by decide +kernel

def cell0042 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (4263 / 25600 : ℚ), (8923 / 51200 : ℚ), (.chain [(0, 10)]), (.chain [(0, 13)]), (.chain [(0, 12)]), (.chain [(0, 10), (0, 11)]), (.chain [(0, 13), (0, 14), (0, 15)]), (.chain [(0, 12), (0, 13)]), .three⟩
theorem cell0042_ok : cell0042.check T = true := by decide +kernel

def cell0043 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (8923 / 51200 : ℚ), (233 / 1280 : ℚ), (.chain [(0, 11)]), (.chain [(0, 14)]), (.chain [(0, 13)]), (.chain [(0, 11), (0, 12)]), (.chain [(0, 14), (0, 15), (0, 16)]), (.chain [(0, 13), (0, 14)]), .three⟩
theorem cell0043_ok : cell0043.check T = true := by decide +kernel

def cell0044 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (233 / 1280 : ℚ), (9717 / 51200 : ℚ), (.chain [(0, 12)]), (.chain [(0, 12)]), (.chain [(0, 12)]), (.chain [(0, 12), (0, 13)]), (.chain [(0, 12), (0, 13), (0, 14)]), (.chain [(0, 12), (0, 13)]), .three⟩
theorem cell0044_ok : cell0044.check T = true := by decide +kernel

def cell0045 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (9717 / 51200 : ℚ), (5057 / 25600 : ℚ), (.chain [(0, 13)]), (.chain [(0, 13)]), (.chain [(0, 13)]), (.chain [(0, 13)]), (.chain [(0, 13), (0, 14)]), (.chain [(0, 13), (0, 14)]), .three⟩
theorem cell0045_ok : cell0045.check T = true := by decide +kernel

def cell0046 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (233 / 1280 : ℚ), (9717 / 51200 : ℚ), (.chain [(0, 12)]), (.chain [(0, 13)]), (.chain [(0, 12)]), (.chain [(0, 12), (0, 13)]), (.chain [(0, 13), (0, 14), (0, 15)]), (.chain [(0, 12), (0, 13), (0, 14)]), .three⟩
theorem cell0046_ok : cell0046.check T = true := by decide +kernel

def cell0047 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (9717 / 51200 : ℚ), (5057 / 25600 : ℚ), (.chain [(0, 13)]), (.chain [(0, 14)]), (.chain [(0, 13)]), (.chain [(0, 13)]), (.chain [(0, 14), (0, 15)]), (.chain [(0, 13), (0, 14)]), .three⟩
theorem cell0047_ok : cell0047.check T = true := by decide +kernel

def cell0048 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (233 / 1280 : ℚ), (9717 / 51200 : ℚ), (.chain [(0, 12)]), (.chain [(0, 14)]), (.chain [(0, 13)]), (.chain [(0, 12), (0, 13)]), (.chain [(0, 14), (0, 15), (0, 16)]), (.chain [(0, 13), (0, 14)]), .three⟩
theorem cell0048_ok : cell0048.check T = true := by decide +kernel

def cell0049 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (9717 / 51200 : ℚ), (5057 / 25600 : ℚ), (.chain [(0, 13)]), (.chain [(0, 15)]), (.chain [(0, 14)]), (.chain [(0, 13)]), (.chain [(0, 15), (0, 16)]), (.chain [(0, 14), (0, 15)]), .three⟩
theorem cell0049_ok : cell0049.check T = true := by decide +kernel

def cell0050 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (233 / 1280 : ℚ), (9717 / 51200 : ℚ), (.chain [(0, 12)]), (.chain [(0, 15)]), (.chain [(0, 13)]), (.chain [(0, 12), (0, 13)]), (.chain [(0, 15), (0, 16), (0, 17)]), (.chain [(0, 13), (0, 14), (0, 15)]), .three⟩
theorem cell0050_ok : cell0050.check T = true := by decide +kernel

def cell0051 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (9717 / 51200 : ℚ), (5057 / 25600 : ℚ), (.chain [(0, 13)]), (.chain [(0, 16)]), (.chain [(0, 14)]), (.chain [(0, 13)]), (.chain [(0, 16), (0, 17)]), (.chain [(0, 14), (0, 15)]), .three⟩
theorem cell0051_ok : cell0051.check T = true := by decide +kernel

def cell0052 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (5057 / 25600 : ℚ), (10511 / 51200 : ℚ), (.chain [(0, 13)]), (.chain [(0, 13)]), (.chain [(0, 13)]), (.chain [(0, 13), (0, 14)]), (.chain [(0, 13), (0, 14), (0, 15)]), (.chain [(0, 13), (0, 14), (0, 15)]), .three⟩
theorem cell0052_ok : cell0052.check T = true := by decide +kernel

def cell0053 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (10511 / 51200 : ℚ), (2727 / 12800 : ℚ), (.chain [(0, 14)]), (.chain [(0, 14)]), (.chain [(0, 14)]), (.chain [(0, 14), (0, 15)]), (.chain [(0, 14), (0, 15), (0, 16)]), (.chain [(0, 14), (0, 15)]), .three⟩
theorem cell0053_ok : cell0053.check T = true := by decide +kernel

def cell0054 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (5057 / 25600 : ℚ), (10511 / 51200 : ℚ), (.chain [(0, 13)]), (.chain [(0, 14)]), (.chain [(0, 14)]), (.chain [(0, 13), (0, 14)]), (.chain [(0, 14), (0, 15), (0, 16)]), (.chain [(0, 14), (0, 15)]), .three⟩
theorem cell0054_ok : cell0054.check T = true := by decide +kernel

def cell0055 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (10511 / 51200 : ℚ), (2727 / 12800 : ℚ), (.chain [(0, 14)]), (.chain [(0, 15)]), (.chain [(0, 15)]), (.chain [(0, 14), (0, 15)]), (.chain [(0, 15), (0, 16), (0, 17)]), (.chain [(0, 15), (0, 16)]), .three⟩
theorem cell0055_ok : cell0055.check T = true := by decide +kernel

def cell0056 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (5057 / 25600 : ℚ), (10511 / 51200 : ℚ), (.chain [(0, 13)]), (.chain [(0, 15)]), (.chain [(0, 14)]), (.chain [(0, 13), (0, 14)]), (.chain [(0, 15), (0, 16), (0, 17)]), (.chain [(0, 14), (0, 15), (0, 16)]), .three⟩
theorem cell0056_ok : cell0056.check T = true := by decide +kernel

def cell0057 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (10511 / 51200 : ℚ), (2727 / 12800 : ℚ), (.chain [(0, 14)]), (.chain [(0, 16)]), (.chain [(0, 15)]), (.chain [(0, 14), (0, 15)]), (.chain [(0, 16), (0, 17), (0, 18)]), (.chain [(0, 15), (0, 16)]), .three⟩
theorem cell0057_ok : cell0057.check T = true := by decide +kernel

def cell0058 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (5057 / 25600 : ℚ), (10511 / 51200 : ℚ), (.chain [(0, 13)]), (.chain [(0, 16)]), (.chain [(0, 15)]), (.chain [(0, 13), (0, 14)]), (.chain [(0, 16), (0, 17), (0, 18)]), (.chain [(0, 15), (0, 16)]), .three⟩
theorem cell0058_ok : cell0058.check T = true := by decide +kernel

def cell0059 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (10511 / 51200 : ℚ), (2727 / 12800 : ℚ), (.chain [(0, 14)]), (.chain [(0, 17)]), (.chain [(0, 16)]), (.chain [(0, 14), (0, 15)]), (.chain [(0, 17), (0, 18), (0, 19)]), (.chain [(0, 16), (0, 17)]), .three⟩
theorem cell0059_ok : cell0059.check T = true := by decide +kernel

def cell0060 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (2727 / 12800 : ℚ), (2261 / 10240 : ℚ), (.chain [(0, 15)]), (.chain [(0, 15)]), (.chain [(0, 15)]), (.chain [(0, 15), (0, 16)]), (.chain [(0, 15), (0, 16), (0, 17)]), (.chain [(0, 15), (0, 16)]), .three⟩
theorem cell0060_ok : cell0060.check T = true := by decide +kernel

def cell0061 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (2261 / 10240 : ℚ), (5851 / 25600 : ℚ), (.chain [(0, 16)]), (.chain [(0, 16)]), (.chain [(0, 16)]), (.chain [(0, 16)]), (.chain [(0, 16), (0, 17)]), (.chain [(0, 16), (0, 17)]), .three⟩
theorem cell0061_ok : cell0061.check T = true := by decide +kernel

def cell0062 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (2727 / 12800 : ℚ), (2261 / 10240 : ℚ), (.chain [(0, 15)]), (.chain [(0, 16)]), (.chain [(0, 15)]), (.chain [(0, 15), (0, 16)]), (.chain [(0, 16), (0, 17), (0, 18)]), (.chain [(0, 15), (0, 16), (0, 17)]), .three⟩
theorem cell0062_ok : cell0062.check T = true := by decide +kernel

def cell0063 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (2261 / 10240 : ℚ), (5851 / 25600 : ℚ), (.chain [(0, 16)]), (.chain [(0, 17)]), (.chain [(0, 16)]), (.chain [(0, 16)]), (.chain [(0, 17), (0, 18)]), (.chain [(0, 16), (0, 17)]), .three⟩
theorem cell0063_ok : cell0063.check T = true := by decide +kernel

def cell0064 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (5851 / 25600 : ℚ), (12099 / 51200 : ℚ), (.chain [(0, 16)]), (.chain [(0, 16)]), (.chain [(0, 16)]), (.chain [(0, 16), (0, 17)]), (.chain [(0, 16), (0, 17), (0, 18)]), (.chain [(0, 16), (0, 17), (0, 18)]), .three⟩
theorem cell0064_ok : cell0064.check T = true := by decide +kernel

def cell0065 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (12099 / 51200 : ℚ), (781 / 3200 : ℚ), (.chain [(0, 17)]), (.chain [(0, 17)]), (.chain [(0, 17)]), (.chain [(0, 17), (0, 18)]), (.chain [(0, 17), (0, 18), (0, 19)]), (.chain [(0, 17), (0, 18)]), .three⟩
theorem cell0065_ok : cell0065.check T = true := by decide +kernel

def cell0066 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (5851 / 25600 : ℚ), (12099 / 51200 : ℚ), (.chain [(0, 16)]), (.chain [(0, 17)]), (.chain [(0, 17)]), (.chain [(0, 16), (0, 17)]), (.chain [(0, 17), (0, 18), (0, 19)]), (.chain [(0, 17), (0, 18)]), .three⟩
theorem cell0066_ok : cell0066.check T = true := by decide +kernel

def cell0067 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (12099 / 51200 : ℚ), (781 / 3200 : ℚ), (.chain [(0, 17)]), (.chain [(0, 18)]), (.chain [(0, 18)]), (.chain [(0, 17), (0, 18)]), (.chain [(0, 18), (0, 19)]), (.chain [(0, 18), (0, 19)]), .three⟩
theorem cell0067_ok : cell0067.check T = true := by decide +kernel

def cell0068 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (2727 / 12800 : ℚ), (2261 / 10240 : ℚ), (.chain [(0, 15)]), (.chain [(0, 17)]), (.chain [(0, 16)]), (.chain [(0, 15), (0, 16)]), (.chain [(0, 17), (0, 18)]), (.chain [(0, 16), (0, 17)]), .three⟩
theorem cell0068_ok : cell0068.check T = true := by decide +kernel

def cell0069 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (2261 / 10240 : ℚ), (5851 / 25600 : ℚ), (.chain [(0, 16)]), (.chain [(0, 18)]), (.chain [(0, 17)]), (.chain [(0, 16)]), (.chain [(0, 18), (0, 19)]), (.chain [(0, 17), (0, 18)]), .three⟩
theorem cell0069_ok : cell0069.check T = true := by decide +kernel

def cell0070 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (2727 / 12800 : ℚ), (2261 / 10240 : ℚ), (.chain [(0, 15)]), (.chain [(0, 18)]), (.chain [(0, 16)]), (.chain [(0, 15), (0, 16)]), (.chain [(0, 18), (0, 19)]), (.chain [(0, 16), (0, 17), (0, 18)]), .three⟩
theorem cell0070_ok : cell0070.check T = true := by decide +kernel

def cell0071 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (2261 / 10240 : ℚ), (5851 / 25600 : ℚ), (.chain [(0, 16)]), (.chain [(0, 18)]), (.chain [(0, 17)]), (.chain [(0, 16)]), (.chain [(0, 18), (0, 19), (0, 20)]), (.chain [(0, 17), (0, 18)]), .three⟩
theorem cell0071_ok : cell0071.check T = true := by decide +kernel

def cell0072 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (5851 / 25600 : ℚ), (12099 / 51200 : ℚ), (.chain [(0, 16)]), (.chain [(0, 18)]), (.chain [(0, 17)]), (.chain [(0, 16), (0, 17)]), (.chain [(0, 18), (0, 19), (0, 20)]), (.chain [(0, 17), (0, 18)]), .three⟩
theorem cell0072_ok : cell0072.check T = true := by decide +kernel

def cell0073 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (12099 / 51200 : ℚ), (781 / 3200 : ℚ), (.chain [(0, 17)]), (.chain [(0, 19)]), (.chain [(0, 18)]), (.chain [(0, 17), (0, 18)]), (.chain [(0, 19), (0, 20)]), (.chain [(0, 18), (0, 19)]), .three⟩
theorem cell0073_ok : cell0073.check T = true := by decide +kernel

def cell0074 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (5851 / 25600 : ℚ), (781 / 3200 : ℚ), (.chain [(0, 16)]), (.chain [(0, 19)]), (.chain [(0, 18)]), (.chain [(0, 16), (0, 17), (0, 18)]), (.chain [(0, 19), (0, 20), (0, 21)]), (.chain [(0, 18), (0, 19)]), .three⟩
theorem cell0074_ok : cell0074.check T = true := by decide +kernel

def cell0075 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (781 / 3200 : ℚ), (12893 / 51200 : ℚ), (.chain [(0, 18)]), (.chain [(0, 18)]), (.chain [(0, 18)]), (.chain [(0, 18)]), (.chain [(0, 18), (0, 19)]), (.chain [(0, 18), (0, 19)]), .three⟩
theorem cell0075_ok : cell0075.check T = true := by decide +kernel

def cell0076 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (12893 / 51200 : ℚ), (1329 / 5120 : ℚ), (.chain [(0, 18)]), (.chain [(0, 18)]), (.chain [(0, 18)]), (.chain [(0, 18), (0, 19)]), (.chain [(0, 18), (0, 19), (0, 20)]), (.chain [(0, 18), (0, 19)]), .three⟩
theorem cell0076_ok : cell0076.check T = true := by decide +kernel

def cell0077 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (781 / 3200 : ℚ), (12893 / 51200 : ℚ), (.chain [(0, 18)]), (.chain [(0, 19)]), (.chain [(0, 18)]), (.chain [(0, 18)]), (.chain [(0, 19), (0, 20)]), (.chain [(0, 18), (0, 19)]), .three⟩
theorem cell0077_ok : cell0077.check T = true := by decide +kernel

def cell0078 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (12893 / 51200 : ℚ), (1329 / 5120 : ℚ), (.chain [(0, 18)]), (.chain [(0, 19)]), (.chain [(0, 19)]), (.chain [(0, 18), (0, 19)]), (.chain [(0, 19), (0, 20), (0, 21)]), (.chain [(0, 19), (0, 20)]), .three⟩
theorem cell0078_ok : cell0078.check T = true := by decide +kernel

def cell0079 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (1329 / 5120 : ℚ), (13687 / 51200 : ℚ), (.chain [(0, 19)]), (.chain [(0, 19)]), (.chain [(0, 19)]), (.chain [(0, 19), (0, 20)]), (.chain [(0, 19), (0, 20)]), (.chain [(0, 19), (0, 20)]), .three⟩
theorem cell0079_ok : cell0079.check T = true := by decide +kernel

def cells01 : List CellW := [cell0040, cell0041, cell0042, cell0043, cell0044, cell0045, cell0046, cell0047, cell0048, cell0049, cell0050, cell0051, cell0052, cell0053, cell0054, cell0055, cell0056, cell0057, cell0058, cell0059, cell0060, cell0061, cell0062, cell0063, cell0064, cell0065, cell0066, cell0067, cell0068, cell0069, cell0070, cell0071, cell0072, cell0073, cell0074, cell0075, cell0076, cell0077, cell0078, cell0079]

theorem cells01_valid : ∀ w ∈ cells01, w.check T = true :=
  (forall_mem_cons_of cell0040_ok (forall_mem_cons_of cell0041_ok (forall_mem_cons_of cell0042_ok (forall_mem_cons_of cell0043_ok (forall_mem_cons_of cell0044_ok (forall_mem_cons_of cell0045_ok (forall_mem_cons_of cell0046_ok (forall_mem_cons_of cell0047_ok (forall_mem_cons_of cell0048_ok (forall_mem_cons_of cell0049_ok (forall_mem_cons_of cell0050_ok (forall_mem_cons_of cell0051_ok (forall_mem_cons_of cell0052_ok (forall_mem_cons_of cell0053_ok (forall_mem_cons_of cell0054_ok (forall_mem_cons_of cell0055_ok (forall_mem_cons_of cell0056_ok (forall_mem_cons_of cell0057_ok (forall_mem_cons_of cell0058_ok (forall_mem_cons_of cell0059_ok (forall_mem_cons_of cell0060_ok (forall_mem_cons_of cell0061_ok (forall_mem_cons_of cell0062_ok (forall_mem_cons_of cell0063_ok (forall_mem_cons_of cell0064_ok (forall_mem_cons_of cell0065_ok (forall_mem_cons_of cell0066_ok (forall_mem_cons_of cell0067_ok (forall_mem_cons_of cell0068_ok (forall_mem_cons_of cell0069_ok (forall_mem_cons_of cell0070_ok (forall_mem_cons_of cell0071_ok (forall_mem_cons_of cell0072_ok (forall_mem_cons_of cell0073_ok (forall_mem_cons_of cell0074_ok (forall_mem_cons_of cell0075_ok (forall_mem_cons_of cell0076_ok (forall_mem_cons_of cell0077_ok (forall_mem_cons_of cell0078_ok (forall_mem_cons_of cell0079_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


