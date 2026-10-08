-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells08
-- name    : CK_CKLaneC_SAxis_Data_Cells08
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:36:47.950981+00:00
-- url     : https://prove2.me/theorems/dbfa3e4f-f352-47db-9a73-b80e7acfe4a2
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells08` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells08` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells08` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells08 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells08.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells08 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 8 (cells 320..359). -/

def cell0320 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (6093 / 5120 : ℚ), (15431 / 12800 : ℚ), (.chain [(1, 20)]), (.chain [(1, 20)]), (.chain [(1, 20)]), (.chain [(1, 20)]), (.chain [(1, 20), (1, 21)]), (.chain [(1, 20), (1, 21)]), .three⟩
theorem cell0320_ok : cell0320.check T = true := by decide +kernel

def cell0321 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (15431 / 12800 : ℚ), (31259 / 25600 : ℚ), (.chain [(1, 20)]), (.chain [(1, 20)]), (.chain [(1, 20)]), (.chain [(1, 20), (1, 21)]), (.chain [(1, 20), (1, 21)]), (.chain [(1, 20), (1, 21)]), .three⟩
theorem cell0321_ok : cell0321.check T = true := by decide +kernel

def cell0322 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (31259 / 25600 : ℚ), (3957 / 3200 : ℚ), (.chain [(1, 21)]), (.chain [(1, 21)]), (.chain [(1, 21)]), (.chain [(1, 21)]), (.chain [(1, 21), (1, 22)]), (.chain [(1, 21)]), .three⟩
theorem cell0322_ok : cell0322.check T = true := by decide +kernel

def cell0323 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (15431 / 12800 : ℚ), (31259 / 25600 : ℚ), (.chain [(1, 20)]), (.chain [(1, 21)]), (.chain [(1, 21)]), (.chain [(1, 20), (1, 21)]), (.chain [(1, 21), (1, 22)]), (.chain [(1, 21)]), .three⟩
theorem cell0323_ok : cell0323.check T = true := by decide +kernel

def cell0324 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (31259 / 25600 : ℚ), (3957 / 3200 : ℚ), (.chain [(1, 21)]), (.chain [(1, 21)]), (.chain [(1, 21)]), (.chain [(1, 21)]), (.chain [(1, 21), (1, 22)]), (.chain [(1, 21), (1, 22)]), .three⟩
theorem cell0324_ok : cell0324.check T = true := by decide +kernel

def cell0325 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (3957 / 3200 : ℚ), (32053 / 25600 : ℚ), (.chain [(1, 21)]), (.chain [(1, 21)]), (.chain [(1, 21)]), (.chain [(1, 21)]), (.chain [(1, 21), (1, 22)]), (.chain [(1, 21), (1, 22)]), .three⟩
theorem cell0325_ok : cell0325.check T = true := by decide +kernel

def cell0326 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (32053 / 25600 : ℚ), (649 / 512 : ℚ), (.chain [(1, 21)]), (.chain [(1, 21)]), (.chain [(1, 21)]), (.chain [(1, 21), (1, 22)]), (.chain [(1, 21), (1, 22)]), (.chain [(1, 21), (1, 22)]), .two⟩
theorem cell0326_ok : cell0326.check T = true := by decide +kernel

def cell0327 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (3957 / 3200 : ℚ), (32053 / 25600 : ℚ), (.chain [(1, 21)]), (.chain [(1, 22)]), (.chain [(1, 21)]), (.chain [(1, 21)]), (.chain [(1, 22)]), (.chain [(1, 21), (1, 22)]), .two⟩
theorem cell0327_ok : cell0327.check T = true := by decide +kernel

def cell0328 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (32053 / 25600 : ℚ), (649 / 512 : ℚ), (.chain [(1, 21)]), (.chain [(1, 22)]), (.chain [(1, 22)]), (.chain [(1, 21), (1, 22)]), (.chain [(1, 22), (1, 23)]), (.chain [(1, 22)]), .three⟩
theorem cell0328_ok : cell0328.check T = true := by decide +kernel

def cell0329 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (649 / 512 : ℚ), (32847 / 25600 : ℚ), (.chain [(1, 22)]), (.chain [(1, 22)]), (.chain [(1, 22)]), (.chain [(1, 22)]), (.chain [(1, 22), (1, 23)]), (.chain [(1, 22)]), .three⟩
theorem cell0329_ok : cell0329.check T = true := by decide +kernel

def cell0330 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (32847 / 25600 : ℚ), (8311 / 6400 : ℚ), (.chain [(1, 22)]), (.chain [(1, 22)]), (.chain [(1, 22)]), (.chain [(1, 22), (1, 23)]), (.chain [(1, 22), (1, 23)]), (.chain [(1, 22), (1, 23)]), .three⟩
theorem cell0330_ok : cell0330.check T = true := by decide +kernel

def cell0331 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (649 / 512 : ℚ), (32847 / 25600 : ℚ), (.chain [(1, 22)]), (.chain [(1, 22)]), (.chain [(1, 22)]), (.chain [(1, 22)]), (.chain [(1, 22), (1, 23)]), (.chain [(1, 22), (1, 23)]), .three⟩
theorem cell0331_ok : cell0331.check T = true := by decide +kernel

def cell0332 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (32847 / 25600 : ℚ), (8311 / 6400 : ℚ), (.chain [(1, 22)]), (.chain [(1, 23)]), (.chain [(1, 22)]), (.chain [(1, 22), (1, 23)]), (.chain [(1, 23), (1, 24)]), (.chain [(1, 22), (1, 23)]), .three⟩
theorem cell0332_ok : cell0332.check T = true := by decide +kernel

def cell0333 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (8311 / 6400 : ℚ), (33641 / 25600 : ℚ), (.chain [(1, 23)]), (.chain [(1, 23)]), (.chain [(1, 23)]), (.chain [(1, 23)]), (.chain [(1, 23)]), (.chain [(1, 23)]), .three⟩
theorem cell0333_ok : cell0333.check T = true := by decide +kernel

def cell0334 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (33641 / 25600 : ℚ), (17019 / 12800 : ℚ), (.chain [(1, 23)]), (.chain [(1, 23)]), (.chain [(1, 23)]), (.chain [(1, 23)]), (.chain [(1, 23), (1, 24)]), (.chain [(1, 23), (1, 24)]), .three⟩
theorem cell0334_ok : cell0334.check T = true := by decide +kernel

def cell0335 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (8311 / 6400 : ℚ), (33641 / 25600 : ℚ), (.chain [(1, 23)]), (.chain [(1, 23)]), (.chain [(1, 23)]), (.chain [(1, 23)]), (.chain [(1, 23), (1, 24)]), (.chain [(1, 23)]), .three⟩
theorem cell0335_ok : cell0335.check T = true := by decide +kernel

def cell0336 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (33641 / 25600 : ℚ), (17019 / 12800 : ℚ), (.chain [(1, 23)]), (.chain [(1, 23)]), (.chain [(1, 23)]), (.chain [(1, 23)]), (.chain [(1, 23), (1, 24)]), (.chain [(1, 23), (1, 24)]), .three⟩
theorem cell0336_ok : cell0336.check T = true := by decide +kernel

def cell0337 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (17019 / 12800 : ℚ), (6887 / 5120 : ℚ), (.chain [(1, 23)]), (.chain [(1, 23)]), (.chain [(1, 23)]), (.chain [(1, 23), (1, 24)]), (.chain [(1, 23), (1, 24)]), (.chain [(1, 23), (1, 24)]), .three⟩
theorem cell0337_ok : cell0337.check T = true := by decide +kernel

def cell0338 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (6887 / 5120 : ℚ), (2177 / 1600 : ℚ), (.chain [(1, 24)]), (.chain [(1, 24)]), (.chain [(1, 24)]), (.chain [(1, 24)]), (.chain [(1, 24), (1, 25)]), (.chain [(1, 24)]), .three⟩
theorem cell0338_ok : cell0338.check T = true := by decide +kernel

def cell0339 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (17019 / 12800 : ℚ), (6887 / 5120 : ℚ), (.chain [(1, 23)]), (.chain [(1, 24)]), (.chain [(1, 24)]), (.chain [(1, 23), (1, 24)]), (.chain [(1, 24), (1, 25)]), (.chain [(1, 24)]), .three⟩
theorem cell0339_ok : cell0339.check T = true := by decide +kernel

def cell0340 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (6887 / 5120 : ℚ), (2177 / 1600 : ℚ), (.chain [(1, 24)]), (.chain [(1, 24)]), (.chain [(1, 24)]), (.chain [(1, 24)]), (.chain [(1, 24), (1, 25)]), (.chain [(1, 24), (1, 25)]), .three⟩
theorem cell0340_ok : cell0340.check T = true := by decide +kernel

def cell0341 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (2177 / 1600 : ℚ), (17813 / 12800 : ℚ), (.chain [(1, 24)]), (.chain [(1, 24)]), (.chain [(1, 24)]), (.chain [(1, 24), (1, 25)]), (.chain [(1, 24), (1, 25)]), (.chain [(1, 24), (1, 25)]), .three⟩
theorem cell0341_ok : cell0341.check T = true := by decide +kernel

def cell0342 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (2177 / 1600 : ℚ), (17813 / 12800 : ℚ), (.chain [(1, 24)]), (.chain [(1, 24)]), (.chain [(1, 24)]), (.chain [(1, 24), (1, 25)]), (.chain [(1, 24), (1, 25)]), (.chain [(1, 24), (1, 25)]), .two⟩
theorem cell0342_ok : cell0342.check T = true := by decide +kernel

def cell0343 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (2177 / 1600 : ℚ), (35229 / 25600 : ℚ), (.chain [(1, 24)]), (.chain [(1, 25)]), (.chain [(1, 24)]), (.chain [(1, 24), (1, 25)]), (.chain [(1, 25), (1, 26)]), (.chain [(1, 24), (1, 25)]), .three⟩
theorem cell0343_ok : cell0343.check T = true := by decide +kernel

def cell0344 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (35229 / 25600 : ℚ), (17813 / 12800 : ℚ), (.chain [(1, 25)]), (.chain [(1, 25)]), (.chain [(1, 25)]), (.chain [(1, 25)]), (.chain [(1, 25), (1, 26)]), (.chain [(1, 25)]), .three⟩
theorem cell0344_ok : cell0344.check T = true := by decide +kernel

def cell0345 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (17813 / 12800 : ℚ), (36023 / 25600 : ℚ), (.chain [(1, 25)]), (.chain [(1, 25)]), (.chain [(1, 25)]), (.chain [(1, 25)]), (.chain [(1, 25), (1, 26)]), (.chain [(1, 25), (1, 26)]), .three⟩
theorem cell0345_ok : cell0345.check T = true := by decide +kernel

def cell0346 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (36023 / 25600 : ℚ), (1821 / 1280 : ℚ), (.chain [(1, 25)]), (.chain [(1, 25)]), (.chain [(1, 25)]), (.chain [(1, 25), (1, 26)]), (.chain [(1, 25), (1, 26)]), (.chain [(1, 25), (1, 26)]), .three⟩
theorem cell0346_ok : cell0346.check T = true := by decide +kernel

def cell0347 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (17813 / 12800 : ℚ), (36023 / 25600 : ℚ), (.chain [(1, 25)]), (.chain [(1, 25)]), (.chain [(1, 25)]), (.chain [(1, 25)]), (.chain [(1, 25), (1, 26)]), (.chain [(1, 25), (1, 26)]), .three⟩
theorem cell0347_ok : cell0347.check T = true := by decide +kernel

def cell0348 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (36023 / 25600 : ℚ), (1821 / 1280 : ℚ), (.chain [(1, 25)]), (.chain [(1, 26)]), (.chain [(1, 26)]), (.chain [(1, 25), (1, 26)]), (.chain [(1, 26), (1, 27)]), (.chain [(1, 26)]), .three⟩
theorem cell0348_ok : cell0348.check T = true := by decide +kernel

def cell0349 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (1821 / 1280 : ℚ), (36817 / 25600 : ℚ), (.chain [(1, 26)]), (.chain [(1, 26)]), (.chain [(1, 26)]), (.chain [(1, 26)]), (.chain [(1, 26), (1, 27)]), (.chain [(1, 26)]), .three⟩
theorem cell0349_ok : cell0349.check T = true := by decide +kernel

def cell0350 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (36817 / 25600 : ℚ), (18607 / 12800 : ℚ), (.chain [(1, 26)]), (.chain [(1, 26)]), (.chain [(1, 26)]), (.chain [(1, 26)]), (.chain [(1, 26), (1, 27)]), (.chain [(1, 26), (1, 27)]), .three⟩
theorem cell0350_ok : cell0350.check T = true := by decide +kernel

def cell0351 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (1821 / 1280 : ℚ), (36817 / 25600 : ℚ), (.chain [(1, 26)]), (.chain [(1, 26)]), (.chain [(1, 26)]), (.chain [(1, 26)]), (.chain [(1, 26), (1, 27)]), (.chain [(1, 26), (1, 27)]), .three⟩
theorem cell0351_ok : cell0351.check T = true := by decide +kernel

def cell0352 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (36817 / 25600 : ℚ), (18607 / 12800 : ℚ), (.chain [(1, 26)]), (.chain [(1, 27)]), (.chain [(1, 26)]), (.chain [(1, 26)]), (.chain [(1, 27)]), (.chain [(1, 26), (1, 27)]), .three⟩
theorem cell0352_ok : cell0352.check T = true := by decide +kernel

def cell0353 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (18607 / 12800 : ℚ), (37611 / 25600 : ℚ), (.chain [(1, 26)]), (.chain [(1, 26)]), (.chain [(1, 26)]), (.chain [(1, 26), (1, 27)]), (.chain [(1, 26), (1, 27)]), (.chain [(1, 26), (1, 27)]), .three⟩
theorem cell0353_ok : cell0353.check T = true := by decide +kernel

def cell0354 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (37611 / 25600 : ℚ), (4751 / 3200 : ℚ), (.chain [(1, 27)]), (.chain [(1, 27)]), (.chain [(1, 27)]), (.chain [(1, 27)]), (.chain [(1, 27), (1, 28)]), (.chain [(1, 27)]), .three⟩
theorem cell0354_ok : cell0354.check T = true := by decide +kernel

def cell0355 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (18607 / 12800 : ℚ), (4751 / 3200 : ℚ), (.chain [(1, 26)]), (.chain [(1, 27)]), (.chain [(1, 27)]), (.chain [(1, 26), (1, 27)]), (.chain [(1, 27), (1, 28)]), (.chain [(1, 27), (1, 28)]), .three⟩
theorem cell0355_ok : cell0355.check T = true := by decide +kernel

def cell0356 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (4751 / 3200 : ℚ), (7681 / 5120 : ℚ), (.chain [(1, 27)]), (.chain [(1, 27)]), (.chain [(1, 27)]), (.chain [(1, 27), (1, 28)]), (.chain [(1, 27), (1, 28)]), (.chain [(1, 27), (1, 28)]), .three⟩
theorem cell0356_ok : cell0356.check T = true := by decide +kernel

def cell0357 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (7681 / 5120 : ℚ), (19401 / 12800 : ℚ), (.chain [(1, 28)]), (.chain [(1, 28)]), (.chain [(1, 28)]), (.chain [(1, 28)]), (.chain [(1, 28), (1, 29)]), (.chain [(1, 28)]), .three⟩
theorem cell0357_ok : cell0357.check T = true := by decide +kernel

def cell0358 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (4751 / 3200 : ℚ), (19401 / 12800 : ℚ), (.chain [(1, 27)]), (.chain [(1, 28)]), (.chain [(1, 27)]), (.chain [(1, 27), (1, 28)]), (.chain [(1, 28), (1, 29)]), (.chain [(1, 27), (1, 28), (1, 29)]), .two⟩
theorem cell0358_ok : cell0358.check T = true := by decide +kernel

def cell0359 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (19401 / 12800 : ℚ), (9899 / 6400 : ℚ), (.chain [(1, 28)]), (.chain [(1, 28)]), (.chain [(1, 28)]), (.chain [(1, 28), (1, 29)]), (.chain [(1, 28), (1, 29)]), (.chain [(1, 28), (1, 29)]), .three⟩
theorem cell0359_ok : cell0359.check T = true := by decide +kernel

def cells08 : List CellW := [cell0320, cell0321, cell0322, cell0323, cell0324, cell0325, cell0326, cell0327, cell0328, cell0329, cell0330, cell0331, cell0332, cell0333, cell0334, cell0335, cell0336, cell0337, cell0338, cell0339, cell0340, cell0341, cell0342, cell0343, cell0344, cell0345, cell0346, cell0347, cell0348, cell0349, cell0350, cell0351, cell0352, cell0353, cell0354, cell0355, cell0356, cell0357, cell0358, cell0359]

theorem cells08_valid : ∀ w ∈ cells08, w.check T = true :=
  (forall_mem_cons_of cell0320_ok (forall_mem_cons_of cell0321_ok (forall_mem_cons_of cell0322_ok (forall_mem_cons_of cell0323_ok (forall_mem_cons_of cell0324_ok (forall_mem_cons_of cell0325_ok (forall_mem_cons_of cell0326_ok (forall_mem_cons_of cell0327_ok (forall_mem_cons_of cell0328_ok (forall_mem_cons_of cell0329_ok (forall_mem_cons_of cell0330_ok (forall_mem_cons_of cell0331_ok (forall_mem_cons_of cell0332_ok (forall_mem_cons_of cell0333_ok (forall_mem_cons_of cell0334_ok (forall_mem_cons_of cell0335_ok (forall_mem_cons_of cell0336_ok (forall_mem_cons_of cell0337_ok (forall_mem_cons_of cell0338_ok (forall_mem_cons_of cell0339_ok (forall_mem_cons_of cell0340_ok (forall_mem_cons_of cell0341_ok (forall_mem_cons_of cell0342_ok (forall_mem_cons_of cell0343_ok (forall_mem_cons_of cell0344_ok (forall_mem_cons_of cell0345_ok (forall_mem_cons_of cell0346_ok (forall_mem_cons_of cell0347_ok (forall_mem_cons_of cell0348_ok (forall_mem_cons_of cell0349_ok (forall_mem_cons_of cell0350_ok (forall_mem_cons_of cell0351_ok (forall_mem_cons_of cell0352_ok (forall_mem_cons_of cell0353_ok (forall_mem_cons_of cell0354_ok (forall_mem_cons_of cell0355_ok (forall_mem_cons_of cell0356_ok (forall_mem_cons_of cell0357_ok (forall_mem_cons_of cell0358_ok (forall_mem_cons_of cell0359_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


