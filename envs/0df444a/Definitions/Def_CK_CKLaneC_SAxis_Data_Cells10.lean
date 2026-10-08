-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells10
-- name    : CK_CKLaneC_SAxis_Data_Cells10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T07:58:35.831336+00:00
-- url     : https://prove2.me/theorems/800cdd5a-bbf2-46f2-bb8d-86062a360953
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells10` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells10` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells10` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells10 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells10.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells10 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 10 (cells 400..439). -/

def cell0400 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (753 / 320 : ℚ), (15457 / 6400 : ℚ), (.chain [(2, 17)]), (.chain [(2, 17)]), (.chain [(2, 17)]), (.chain [(2, 17), (2, 18), (2, 19)]), (.chain [(2, 17), (2, 18), (2, 19), (2, 20)]), (.chain [(2, 17), (2, 18), (2, 19)]), .one⟩
theorem cell0400_ok : cell0400.check T = true := by decide +kernel

def cell0401 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (15457 / 6400 : ℚ), (7927 / 3200 : ℚ), (.chain [(2, 19)]), (.chain [(2, 19)]), (.chain [(2, 19)]), (.chain [(2, 19), (2, 20)]), (.chain [(2, 19), (2, 20), (2, 21)]), (.chain [(2, 19), (2, 20)]), .one⟩
theorem cell0401_ok : cell0401.check T = true := by decide +kernel

def cell0402 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (15457 / 6400 : ℚ), (7927 / 3200 : ℚ), (.chain [(2, 19)]), (.chain [(2, 19)]), (.chain [(2, 19)]), (.chain [(2, 19), (2, 20)]), (.chain [(2, 19), (2, 20), (2, 21)]), (.chain [(2, 19), (2, 20), (2, 21)]), .one⟩
theorem cell0402_ok : cell0402.check T = true := by decide +kernel

def cell0403 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (7927 / 3200 : ℚ), (16251 / 6400 : ℚ), (.chain [(2, 20)]), (.chain [(2, 20)]), (.chain [(2, 20)]), (.chain [(2, 20), (2, 21), (2, 22)]), (.chain [(2, 20), (2, 21), (2, 22), (2, 23)]), (.chain [(2, 20), (2, 21), (2, 22)]), .one⟩
theorem cell0403_ok : cell0403.check T = true := by decide +kernel

def cell0404 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (16251 / 6400 : ℚ), (2081 / 800 : ℚ), (.chain [(2, 22)]), (.chain [(2, 22)]), (.chain [(2, 22)]), (.chain [(2, 22), (2, 23)]), (.chain [(2, 22), (2, 23), (2, 24)]), (.chain [(2, 22), (2, 23), (2, 24)]), .one⟩
theorem cell0404_ok : cell0404.check T = true := by decide +kernel

def cell0405 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (2081 / 800 : ℚ), (3409 / 1280 : ℚ), (.chain [(2, 23)]), (.chain [(2, 23)]), (.chain [(2, 23)]), (.chain [(2, 23), (2, 24), (2, 25)]), (.chain [(2, 23), (2, 24), (2, 25), (2, 26)]), (.chain [(2, 23), (2, 24), (2, 25)]), .one⟩
theorem cell0405_ok : cell0405.check T = true := by decide +kernel

def cell0406 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (3409 / 1280 : ℚ), (8721 / 3200 : ℚ), (.chain [(2, 25)]), (.chain [(2, 25)]), (.chain [(2, 25)]), (.chain [(2, 25), (2, 26)]), (.chain [(2, 25), (2, 26), (2, 27)]), (.chain [(2, 25), (2, 26), (2, 27)]), .one⟩
theorem cell0406_ok : cell0406.check T = true := by decide +kernel

def cell0407 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (8721 / 3200 : ℚ), (17839 / 6400 : ℚ), (.chain [(2, 26)]), (.chain [(2, 26)]), (.chain [(2, 26)]), (.chain [(2, 26), (2, 27), (2, 28)]), (.chain [(2, 26), (2, 27), (2, 28), (2, 29)]), (.chain [(2, 26), (2, 27), (2, 28)]), .one⟩
theorem cell0407_ok : cell0407.check T = true := by decide +kernel

def cell0408 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (17839 / 6400 : ℚ), (4559 / 1600 : ℚ), (.chain [(2, 28)]), (.chain [(2, 28)]), (.chain [(2, 28)]), (.chain [(2, 28), (2, 29)]), (.chain [(2, 28), (2, 29), (2, 30)]), (.chain [(2, 28), (2, 29), (2, 30)]), .one⟩
theorem cell0408_ok : cell0408.check T = true := by decide +kernel

def cell0409 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (4559 / 1600 : ℚ), (18633 / 6400 : ℚ), (.chain [(2, 29)]), (.chain [(2, 29)]), (.chain [(2, 29)]), (.chain [(2, 29), (2, 30), (2, 31)]), (.chain [(2, 29), (2, 30), (2, 31), (3, 0)]), (.chain [(2, 29), (2, 30), (2, 31)]), .one⟩
theorem cell0409_ok : cell0409.check T = true := by decide +kernel

def cell0410 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (18633 / 6400 : ℚ), (1903 / 640 : ℚ), (.chain [(2, 31)]), (.chain [(2, 31)]), (.chain [(2, 31)]), (.chain [(2, 31), (3, 0)]), (.chain [(2, 31), (3, 0), (3, 1)]), (.chain [(2, 31), (3, 0), (3, 1)]), .one⟩
theorem cell0410_ok : cell0410.check T = true := by decide +kernel

def cell0411 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (1903 / 640 : ℚ), (19427 / 6400 : ℚ), (.chain [(3, 0)]), (.chain [(3, 0)]), (.chain [(3, 0)]), (.chain [(3, 0), (3, 1), (3, 2)]), (.chain [(3, 0), (3, 1), (3, 2), (3, 3)]), (.chain [(3, 0), (3, 1), (3, 2), (3, 3)]), .one⟩
theorem cell0411_ok : cell0411.check T = true := by decide +kernel

def cell0412 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (19427 / 6400 : ℚ), (1239 / 400 : ℚ), (.chain [(3, 2)]), (.chain [(3, 2)]), (.chain [(3, 2)]), (.chain [(3, 2), (3, 3), (3, 4)]), (.chain [(3, 2), (3, 3), (3, 4), (3, 5)]), (.chain [(3, 2), (3, 3), (3, 4)]), .one⟩
theorem cell0412_ok : cell0412.check T = true := by decide +kernel

def cell0413 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (1239 / 400 : ℚ), (20221 / 6400 : ℚ), (.chain [(3, 4)]), (.chain [(3, 4)]), (.chain [(3, 4)]), (.chain [(3, 4), (3, 5)]), (.chain [(3, 4), (3, 5), (3, 6)]), (.chain [(3, 4), (3, 5), (3, 6)]), .one⟩
theorem cell0413_ok : cell0413.check T = true := by decide +kernel

def cell0414 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (20221 / 6400 : ℚ), (10309 / 3200 : ℚ), (.chain [(3, 5)]), (.chain [(3, 5)]), (.chain [(3, 5)]), (.chain [(3, 5), (3, 6), (3, 7)]), (.chain [(3, 5), (3, 6), (3, 7), (3, 8)]), (.chain [(3, 5), (3, 6), (3, 7)]), .one⟩
theorem cell0414_ok : cell0414.check T = true := by decide +kernel

def cell0415 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (10309 / 3200 : ℚ), (4203 / 1280 : ℚ), (.chain [(3, 7)]), (.chain [(3, 7)]), (.chain [(3, 7)]), (.chain [(3, 7), (3, 8)]), (.chain [(3, 7), (3, 8), (3, 9)]), (.chain [(3, 7), (3, 8), (3, 9)]), .one⟩
theorem cell0415_ok : cell0415.check T = true := by decide +kernel

def cell0416 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (4203 / 1280 : ℚ), (5353 / 1600 : ℚ), (.chain [(3, 8)]), (.chain [(3, 8)]), (.chain [(3, 8)]), (.chain [(3, 8), (3, 9), (3, 10)]), (.chain [(3, 8), (3, 9), (3, 10), (3, 11)]), (.chain [(3, 8), (3, 9), (3, 10)]), .one⟩
theorem cell0416_ok : cell0416.check T = true := by decide +kernel

def cell0417 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (5353 / 1600 : ℚ), (21809 / 6400 : ℚ), (.chain [(3, 10)]), (.chain [(3, 10)]), (.chain [(3, 10)]), (.chain [(3, 10), (3, 11)]), (.chain [(3, 10), (3, 11), (3, 12)]), (.chain [(3, 10), (3, 11), (3, 12)]), .one⟩
theorem cell0417_ok : cell0417.check T = true := by decide +kernel

def cell0418 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (21809 / 6400 : ℚ), (11103 / 3200 : ℚ), (.chain [(3, 11)]), (.chain [(3, 11)]), (.chain [(3, 11)]), (.chain [(3, 11), (3, 12), (3, 13)]), (.chain [(3, 11), (3, 12), (3, 13), (3, 14)]), (.chain [(3, 11), (3, 12), (3, 13)]), .one⟩
theorem cell0418_ok : cell0418.check T = true := by decide +kernel

def cell0419 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (11103 / 3200 : ℚ), (22603 / 6400 : ℚ), (.chain [(3, 13)]), (.chain [(3, 13)]), (.chain [(3, 13)]), (.chain [(3, 13), (3, 14)]), (.chain [(3, 13), (3, 14), (3, 15)]), (.chain [(3, 13), (3, 14), (3, 15)]), .one⟩
theorem cell0419_ok : cell0419.check T = true := by decide +kernel

def cell0420 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (22603 / 6400 : ℚ), (115 / 32 : ℚ), (.chain [(3, 14)]), (.chain [(3, 14)]), (.chain [(3, 14)]), (.chain [(3, 14), (3, 15), (3, 16)]), (.chain [(3, 14), (3, 15), (3, 16), (3, 17)]), (.chain [(3, 14), (3, 15), (3, 16)]), .one⟩
theorem cell0420_ok : cell0420.check T = true := by decide +kernel

def cell0421 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (115 / 32 : ℚ), (23397 / 6400 : ℚ), (.chain [(3, 16)]), (.chain [(3, 16)]), (.chain [(3, 16)]), (.chain [(3, 16), (3, 17), (3, 18)]), (.chain [(3, 16), (3, 17), (3, 18), (3, 19)]), (.chain [(3, 16), (3, 17), (3, 18)]), .one⟩
theorem cell0421_ok : cell0421.check T = true := by decide +kernel

def cell0422 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (23397 / 6400 : ℚ), (11897 / 3200 : ℚ), (.chain [(3, 18)]), (.chain [(3, 18)]), (.chain [(3, 18)]), (.chain [(3, 18), (3, 19)]), (.chain [(3, 18), (3, 19), (3, 20)]), (.chain [(3, 18), (3, 19), (3, 20)]), .one⟩
theorem cell0422_ok : cell0422.check T = true := by decide +kernel

def cell0423 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (11897 / 3200 : ℚ), (24191 / 6400 : ℚ), (.chain [(3, 19)]), (.chain [(3, 19)]), (.chain [(3, 19)]), (.chain [(3, 19), (3, 20), (3, 21)]), (.chain [(3, 19), (3, 20), (3, 21), (3, 22)]), (.chain [(3, 19), (3, 20), (3, 21)]), .one⟩
theorem cell0423_ok : cell0423.check T = true := by decide +kernel

def cell0424 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (24191 / 6400 : ℚ), (6147 / 1600 : ℚ), (.chain [(3, 21)]), (.chain [(3, 21)]), (.chain [(3, 21)]), (.chain [(3, 21), (3, 22)]), (.chain [(3, 21), (3, 22), (3, 23)]), (.chain [(3, 21), (3, 22), (3, 23)]), .one⟩
theorem cell0424_ok : cell0424.check T = true := by decide +kernel

def cell0425 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (6147 / 1600 : ℚ), (4997 / 1280 : ℚ), (.chain [(3, 22)]), (.chain [(3, 22)]), (.chain [(3, 22)]), (.chain [(3, 22), (3, 23), (3, 24)]), (.chain [(3, 22), (3, 23), (3, 24), (3, 25)]), (.chain [(3, 22), (3, 23), (3, 24)]), .one⟩
theorem cell0425_ok : cell0425.check T = true := by decide +kernel

def cell0426 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (4997 / 1280 : ℚ), (12691 / 3200 : ℚ), (.chain [(3, 24)]), (.chain [(3, 24)]), (.chain [(3, 24)]), (.chain [(3, 24), (3, 25)]), (.chain [(3, 24), (3, 25), (3, 26)]), (.chain [(3, 24), (3, 25), (3, 26)]), .one⟩
theorem cell0426_ok : cell0426.check T = true := by decide +kernel

def cell0427 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (12691 / 3200 : ℚ), (25779 / 6400 : ℚ), (.chain [(3, 25)]), (.chain [(3, 25)]), (.chain [(3, 25)]), (.chain [(3, 25), (3, 26), (3, 27)]), (.chain [(3, 25), (3, 26), (3, 27), (3, 28)]), (.chain [(3, 25), (3, 26), (3, 27)]), .one⟩
theorem cell0427_ok : cell0427.check T = true := by decide +kernel

def cell0428 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (25779 / 6400 : ℚ), (409 / 100 : ℚ), (.chain [(3, 27)]), (.chain [(3, 27)]), (.chain [(3, 27)]), (.chain [(3, 27), (3, 28)]), (.chain [(3, 27), (3, 28), (3, 29)]), (.chain [(3, 27), (3, 28), (3, 29)]), .one⟩
theorem cell0428_ok : cell0428.check T = true := by decide +kernel

def cell0429 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (409 / 100 : ℚ), (26573 / 6400 : ℚ), (.chain [(3, 28)]), (.chain [(3, 28)]), (.chain [(3, 28)]), (.chain [(3, 28), (3, 29), (3, 30)]), (.chain [(3, 28), (3, 29), (3, 30), (3, 31)]), (.chain [(3, 28), (3, 29), (3, 30)]), .one⟩
theorem cell0429_ok : cell0429.check T = true := by decide +kernel

def cell0430 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (26573 / 6400 : ℚ), (2697 / 640 : ℚ), (.chain [(3, 30)]), (.chain [(3, 30)]), (.chain [(3, 30)]), (.chain [(3, 30), (3, 31)]), (.chain [(3, 30), (3, 31), (4, 0)]), (.chain [(3, 30), (3, 31), (4, 0)]), .one⟩
theorem cell0430_ok : cell0430.check T = true := by decide +kernel

def cell0431 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (2697 / 640 : ℚ), (27367 / 6400 : ℚ), (.chain [(3, 31)]), (.chain [(3, 31)]), (.chain [(3, 31)]), (.chain [(3, 31), (4, 0), (4, 1)]), (.chain [(3, 31), (4, 0), (4, 1), (4, 2)]), (.chain [(3, 31), (4, 0), (4, 1), (4, 2)]), .one⟩
theorem cell0431_ok : cell0431.check T = true := by decide +kernel

def cell0432 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (27367 / 6400 : ℚ), (6941 / 1600 : ℚ), (.chain [(4, 1)]), (.chain [(4, 1)]), (.chain [(4, 1)]), (.chain [(4, 1), (4, 2), (4, 3)]), (.chain [(4, 1), (4, 2), (4, 3), (4, 4)]), (.chain [(4, 1), (4, 2), (4, 3)]), .one⟩
theorem cell0432_ok : cell0432.check T = true := by decide +kernel

def cell0433 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (6941 / 1600 : ℚ), (28161 / 6400 : ℚ), (.chain [(4, 3)]), (.chain [(4, 3)]), (.chain [(4, 3)]), (.chain [(4, 3), (4, 4)]), (.chain [(4, 3), (4, 4), (4, 5)]), (.chain [(4, 3), (4, 4), (4, 5)]), .one⟩
theorem cell0433_ok : cell0433.check T = true := by decide +kernel

def cell0434 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (28161 / 6400 : ℚ), (14279 / 3200 : ℚ), (.chain [(4, 4)]), (.chain [(4, 4)]), (.chain [(4, 4)]), (.chain [(4, 4), (4, 5), (4, 6)]), (.chain [(4, 4), (4, 5), (4, 6), (4, 7)]), (.chain [(4, 4), (4, 5), (4, 6)]), .one⟩
theorem cell0434_ok : cell0434.check T = true := by decide +kernel

def cell0435 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (14279 / 3200 : ℚ), (5791 / 1280 : ℚ), (.chain [(4, 6)]), (.chain [(4, 6)]), (.chain [(4, 6)]), (.chain [(4, 6), (4, 7)]), (.chain [(4, 6), (4, 7), (4, 8)]), (.chain [(4, 6), (4, 7), (4, 8)]), .one⟩
theorem cell0435_ok : cell0435.check T = true := by decide +kernel

def cell0436 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (5791 / 1280 : ℚ), (3669 / 800 : ℚ), (.chain [(4, 7)]), (.chain [(4, 7)]), (.chain [(4, 7)]), (.chain [(4, 7), (4, 8), (4, 9)]), (.chain [(4, 7), (4, 8), (4, 9), (4, 10)]), (.chain [(4, 7), (4, 8), (4, 9)]), .one⟩
theorem cell0436_ok : cell0436.check T = true := by decide +kernel

def cell0437 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (3669 / 800 : ℚ), (29749 / 6400 : ℚ), (.chain [(4, 9)]), (.chain [(4, 9)]), (.chain [(4, 9)]), (.chain [(4, 9), (4, 10)]), (.chain [(4, 9), (4, 10), (4, 11)]), (.chain [(4, 9), (4, 10), (4, 11)]), .one⟩
theorem cell0437_ok : cell0437.check T = true := by decide +kernel

def cell0438 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (29749 / 6400 : ℚ), (15073 / 3200 : ℚ), (.chain [(4, 10)]), (.chain [(4, 10)]), (.chain [(4, 10)]), (.chain [(4, 10), (4, 11), (4, 12)]), (.chain [(4, 10), (4, 11), (4, 12), (4, 13)]), (.chain [(4, 10), (4, 11), (4, 12)]), .one⟩
theorem cell0438_ok : cell0438.check T = true := by decide +kernel

def cell0439 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (15073 / 3200 : ℚ), (30543 / 6400 : ℚ), (.chain [(4, 12)]), (.chain [(4, 12)]), (.chain [(4, 12)]), (.chain [(4, 12), (4, 13)]), (.chain [(4, 12), (4, 13), (4, 14)]), (.chain [(4, 12), (4, 13), (4, 14)]), .one⟩
theorem cell0439_ok : cell0439.check T = true := by decide +kernel

def cells10 : List CellW := [cell0400, cell0401, cell0402, cell0403, cell0404, cell0405, cell0406, cell0407, cell0408, cell0409, cell0410, cell0411, cell0412, cell0413, cell0414, cell0415, cell0416, cell0417, cell0418, cell0419, cell0420, cell0421, cell0422, cell0423, cell0424, cell0425, cell0426, cell0427, cell0428, cell0429, cell0430, cell0431, cell0432, cell0433, cell0434, cell0435, cell0436, cell0437, cell0438, cell0439]

theorem cells10_valid : ∀ w ∈ cells10, w.check T = true :=
  (forall_mem_cons_of cell0400_ok (forall_mem_cons_of cell0401_ok (forall_mem_cons_of cell0402_ok (forall_mem_cons_of cell0403_ok (forall_mem_cons_of cell0404_ok (forall_mem_cons_of cell0405_ok (forall_mem_cons_of cell0406_ok (forall_mem_cons_of cell0407_ok (forall_mem_cons_of cell0408_ok (forall_mem_cons_of cell0409_ok (forall_mem_cons_of cell0410_ok (forall_mem_cons_of cell0411_ok (forall_mem_cons_of cell0412_ok (forall_mem_cons_of cell0413_ok (forall_mem_cons_of cell0414_ok (forall_mem_cons_of cell0415_ok (forall_mem_cons_of cell0416_ok (forall_mem_cons_of cell0417_ok (forall_mem_cons_of cell0418_ok (forall_mem_cons_of cell0419_ok (forall_mem_cons_of cell0420_ok (forall_mem_cons_of cell0421_ok (forall_mem_cons_of cell0422_ok (forall_mem_cons_of cell0423_ok (forall_mem_cons_of cell0424_ok (forall_mem_cons_of cell0425_ok (forall_mem_cons_of cell0426_ok (forall_mem_cons_of cell0427_ok (forall_mem_cons_of cell0428_ok (forall_mem_cons_of cell0429_ok (forall_mem_cons_of cell0430_ok (forall_mem_cons_of cell0431_ok (forall_mem_cons_of cell0432_ok (forall_mem_cons_of cell0433_ok (forall_mem_cons_of cell0434_ok (forall_mem_cons_of cell0435_ok (forall_mem_cons_of cell0436_ok (forall_mem_cons_of cell0437_ok (forall_mem_cons_of cell0438_ok (forall_mem_cons_of cell0439_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


