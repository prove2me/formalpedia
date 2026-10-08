-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells11
-- name    : CK_CKLaneC_SAxis_Data_Cells11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:12:30.630312+00:00
-- url     : https://prove2.me/theorems/b1339f88-d371-4ab6-a0d2-2eaea6dbf246
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells11` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells11` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells11` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells11 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells11.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells11 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 11 (cells 440..479). -/

def cell0440 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (30543 / 6400 : ℚ), (61483 / 12800 : ℚ), (.chain [(4, 13)]), (.chain [(4, 13)]), (.chain [(4, 13)]), (.chain [(4, 13), (4, 14)]), (.chain [(4, 13), (4, 14), (4, 15)]), (.chain [(4, 13), (4, 14), (4, 15)]), .one⟩
theorem cell0440_ok : cell0440.check T = true := by decide +kernel

def cell0441 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (61483 / 12800 : ℚ), (1547 / 320 : ℚ), (.chain [(4, 14)]), (.chain [(4, 14)]), (.chain [(4, 14)]), (.chain [(4, 14), (4, 15)]), (.chain [(4, 14), (4, 15), (4, 16)]), (.chain [(4, 14), (4, 15)]), .one⟩
theorem cell0441_ok : cell0441.check T = true := by decide +kernel

def cell0442 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (1547 / 320 : ℚ), (62277 / 12800 : ℚ), (.chain [(4, 15)]), (.chain [(4, 15)]), (.chain [(4, 15)]), (.chain [(4, 15), (4, 16)]), (.chain [(4, 15), (4, 16), (4, 17)]), (.chain [(4, 15), (4, 16)]), .one⟩
theorem cell0442_ok : cell0442.check T = true := by decide +kernel

def cell0443 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (62277 / 12800 : ℚ), (31337 / 6400 : ℚ), (.chain [(4, 16)]), (.chain [(4, 16)]), (.chain [(4, 16)]), (.chain [(4, 16), (4, 17)]), (.chain [(4, 16), (4, 17), (4, 18)]), (.chain [(4, 16), (4, 17)]), .one⟩
theorem cell0443_ok : cell0443.check T = true := by decide +kernel

def cell0444 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (31337 / 6400 : ℚ), (63071 / 12800 : ℚ), (.chain [(4, 17)]), (.chain [(4, 17)]), (.chain [(4, 17)]), (.chain [(4, 17)]), (.chain [(4, 17), (4, 18)]), (.chain [(4, 17), (4, 18)]), .one⟩
theorem cell0444_ok : cell0444.check T = true := by decide +kernel

def cell0445 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (63071 / 12800 : ℚ), (15867 / 3200 : ℚ), (.chain [(4, 17)]), (.chain [(4, 17)]), (.chain [(4, 17)]), (.chain [(4, 17), (4, 18)]), (.chain [(4, 17), (4, 18), (4, 19)]), (.chain [(4, 17), (4, 18), (4, 19)]), .one⟩
theorem cell0445_ok : cell0445.check T = true := by decide +kernel

def cell0446 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (15867 / 3200 : ℚ), (12773 / 2560 : ℚ), (.chain [(4, 18)]), (.chain [(4, 18)]), (.chain [(4, 18)]), (.chain [(4, 18), (4, 19)]), (.chain [(4, 18), (4, 19), (4, 20)]), (.chain [(4, 18), (4, 19)]), .one⟩
theorem cell0446_ok : cell0446.check T = true := by decide +kernel

def cell0447 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (12773 / 2560 : ℚ), (32131 / 6400 : ℚ), (.chain [(4, 19)]), (.chain [(4, 19)]), (.chain [(4, 19)]), (.chain [(4, 19), (4, 20)]), (.chain [(4, 19), (4, 20), (4, 21)]), (.chain [(4, 19), (4, 20)]), .one⟩
theorem cell0447_ok : cell0447.check T = true := by decide +kernel

def cell0448 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (32131 / 6400 : ℚ), (64659 / 12800 : ℚ), (.chain [(4, 20)]), (.chain [(4, 20)]), (.chain [(4, 20)]), (.chain [(4, 20)]), (.chain [(4, 20), (4, 21)]), (.chain [(4, 20), (4, 21)]), .one⟩
theorem cell0448_ok : cell0448.check T = true := by decide +kernel

def cell0449 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (64659 / 12800 : ℚ), (2033 / 400 : ℚ), (.chain [(4, 20)]), (.chain [(4, 20)]), (.chain [(4, 20)]), (.chain [(4, 20), (4, 21)]), (.chain [(4, 20), (4, 21), (4, 22)]), (.chain [(4, 20), (4, 21), (4, 22)]), .one⟩
theorem cell0449_ok : cell0449.check T = true := by decide +kernel

def cell0450 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (2033 / 400 : ℚ), (65453 / 12800 : ℚ), (.chain [(4, 21)]), (.chain [(4, 21)]), (.chain [(4, 21)]), (.chain [(4, 21), (4, 22)]), (.chain [(4, 21), (4, 22), (4, 23)]), (.chain [(4, 21), (4, 22)]), .one⟩
theorem cell0450_ok : cell0450.check T = true := by decide +kernel

def cell0451 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (65453 / 12800 : ℚ), (1317 / 256 : ℚ), (.chain [(4, 22)]), (.chain [(4, 22)]), (.chain [(4, 22)]), (.chain [(4, 22), (4, 23)]), (.chain [(4, 22), (4, 23), (4, 24)]), (.chain [(4, 22), (4, 23)]), .one⟩
theorem cell0451_ok : cell0451.check T = true := by decide +kernel

def cell0452 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (1317 / 256 : ℚ), (66247 / 12800 : ℚ), (.chain [(4, 23)]), (.chain [(4, 23)]), (.chain [(4, 23)]), (.chain [(4, 23), (4, 24)]), (.chain [(4, 23), (4, 24), (4, 25)]), (.chain [(4, 23), (4, 24)]), .one⟩
theorem cell0452_ok : cell0452.check T = true := by decide +kernel

def cell0453 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (66247 / 12800 : ℚ), (16661 / 3200 : ℚ), (.chain [(4, 24)]), (.chain [(4, 24)]), (.chain [(4, 24)]), (.chain [(4, 24)]), (.chain [(4, 24), (4, 25)]), (.chain [(4, 24), (4, 25)]), .one⟩
theorem cell0453_ok : cell0453.check T = true := by decide +kernel

def cell0454 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (16661 / 3200 : ℚ), (67041 / 12800 : ℚ), (.chain [(4, 24)]), (.chain [(4, 24)]), (.chain [(4, 24)]), (.chain [(4, 24), (4, 25)]), (.chain [(4, 24), (4, 25), (4, 26)]), (.chain [(4, 24), (4, 25), (4, 26)]), .one⟩
theorem cell0454_ok : cell0454.check T = true := by decide +kernel

def cell0455 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (67041 / 12800 : ℚ), (33719 / 6400 : ℚ), (.chain [(4, 25)]), (.chain [(4, 25)]), (.chain [(4, 25)]), (.chain [(4, 25), (4, 26)]), (.chain [(4, 25), (4, 26), (4, 27)]), (.chain [(4, 25), (4, 26)]), .one⟩
theorem cell0455_ok : cell0455.check T = true := by decide +kernel

def cell0456 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (33719 / 6400 : ℚ), (13567 / 2560 : ℚ), (.chain [(4, 26)]), (.chain [(4, 26)]), (.chain [(4, 26)]), (.chain [(4, 26), (4, 27)]), (.chain [(4, 26), (4, 27), (4, 28)]), (.chain [(4, 26), (4, 27)]), .one⟩
theorem cell0456_ok : cell0456.check T = true := by decide +kernel

def cell0457 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (13567 / 2560 : ℚ), (8529 / 1600 : ℚ), (.chain [(4, 27)]), (.chain [(4, 27)]), (.chain [(4, 27)]), (.chain [(4, 27)]), (.chain [(4, 27), (4, 28)]), (.chain [(4, 27), (4, 28)]), .one⟩
theorem cell0457_ok : cell0457.check T = true := by decide +kernel

def cell0458 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (8529 / 1600 : ℚ), (68629 / 12800 : ℚ), (.chain [(4, 27)]), (.chain [(4, 27)]), (.chain [(4, 27)]), (.chain [(4, 27), (4, 28)]), (.chain [(4, 27), (4, 28), (4, 29)]), (.chain [(4, 27), (4, 28), (4, 29)]), .one⟩
theorem cell0458_ok : cell0458.check T = true := by decide +kernel

def cell0459 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (68629 / 12800 : ℚ), (34513 / 6400 : ℚ), (.chain [(4, 28)]), (.chain [(4, 28)]), (.chain [(4, 28)]), (.chain [(4, 28), (4, 29)]), (.chain [(4, 28), (4, 29), (4, 30)]), (.chain [(4, 28), (4, 29)]), .one⟩
theorem cell0459_ok : cell0459.check T = true := by decide +kernel

def cell0460 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (34513 / 6400 : ℚ), (69423 / 12800 : ℚ), (.chain [(4, 29)]), (.chain [(4, 29)]), (.chain [(4, 29)]), (.chain [(4, 29), (4, 30)]), (.chain [(4, 29), (4, 30), (4, 31)]), (.chain [(4, 29), (4, 30)]), .one⟩
theorem cell0460_ok : cell0460.check T = true := by decide +kernel

def cell0461 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (69423 / 12800 : ℚ), (3491 / 640 : ℚ), (.chain [(4, 30)]), (.chain [(4, 30)]), (.chain [(4, 30)]), (.chain [(4, 30)]), (.chain [(4, 30), (4, 31)]), (.chain [(4, 30), (4, 31)]), .one⟩
theorem cell0461_ok : cell0461.check T = true := by decide +kernel

def cell0462 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (3491 / 640 : ℚ), (70217 / 12800 : ℚ), (.chain [(4, 30)]), (.chain [(4, 30)]), (.chain [(4, 30)]), (.chain [(4, 30), (4, 31)]), (.chain [(4, 30), (4, 31), (5, 0)]), (.chain [(4, 30), (4, 31), (5, 0)]), .one⟩
theorem cell0462_ok : cell0462.check T = true := by decide +kernel

def cell0463 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (3491 / 640 : ℚ), (70217 / 12800 : ℚ), (.chain [(4, 30)]), (.chain [(4, 31)]), (.chain [(4, 31)]), (.chain [(4, 30), (4, 31)]), (.chain [(4, 31), (5, 0)]), (.chain [(4, 31), (5, 0)]), .one⟩
theorem cell0463_ok : cell0463.check T = true := by decide +kernel

def cell0464 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (70217 / 12800 : ℚ), (35307 / 6400 : ℚ), (.chain [(4, 31)]), (.chain [(4, 31)]), (.chain [(4, 31)]), (.chain [(4, 31), (5, 0)]), (.chain [(4, 31), (5, 0), (5, 1)]), (.chain [(4, 31), (5, 0)]), .one⟩
theorem cell0464_ok : cell0464.check T = true := by decide +kernel

def cell0465 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (70217 / 12800 : ℚ), (35307 / 6400 : ℚ), (.chain [(4, 31)]), (.chain [(5, 0)]), (.chain [(5, 0)]), (.chain [(4, 31), (5, 0)]), (.chain [(5, 0), (5, 1)]), (.chain [(5, 0), (5, 1)]), .one⟩
theorem cell0465_ok : cell0465.check T = true := by decide +kernel

def cell0466 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (35307 / 6400 : ℚ), (71011 / 12800 : ℚ), (.chain [(5, 0)]), (.chain [(5, 0)]), (.chain [(5, 0)]), (.chain [(5, 0), (5, 1)]), (.chain [(5, 0), (5, 1)]), (.chain [(5, 0), (5, 1)]), .one⟩
theorem cell0466_ok : cell0466.check T = true := by decide +kernel

def cell0467 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (35307 / 6400 : ℚ), (71011 / 12800 : ℚ), (.chain [(5, 0)]), (.chain [(5, 1)]), (.chain [(5, 0)]), (.chain [(5, 0), (5, 1)]), (.chain [(5, 1), (5, 2)]), (.chain [(5, 0), (5, 1)]), .one⟩
theorem cell0467_ok : cell0467.check T = true := by decide +kernel

def cell0468 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (71011 / 12800 : ℚ), (4463 / 800 : ℚ), (.chain [(5, 1)]), (.chain [(5, 1)]), (.chain [(5, 1)]), (.chain [(5, 1), (5, 2)]), (.chain [(5, 1), (5, 2)]), (.chain [(5, 1), (5, 2)]), .one⟩
theorem cell0468_ok : cell0468.check T = true := by decide +kernel

def cell0469 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (71011 / 12800 : ℚ), (4463 / 800 : ℚ), (.chain [(5, 1)]), (.chain [(5, 1)]), (.chain [(5, 1)]), (.chain [(5, 1), (5, 2)]), (.chain [(5, 1), (5, 2), (5, 3)]), (.chain [(5, 1), (5, 2)]), .one⟩
theorem cell0469_ok : cell0469.check T = true := by decide +kernel

def cell0470 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (4463 / 800 : ℚ), (14361 / 2560 : ℚ), (.chain [(5, 2)]), (.chain [(5, 2)]), (.chain [(5, 2)]), (.chain [(5, 2)]), (.chain [(5, 2), (5, 3)]), (.chain [(5, 2), (5, 3)]), .one⟩
theorem cell0470_ok : cell0470.check T = true := by decide +kernel

def cell0471 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (4463 / 800 : ℚ), (14361 / 2560 : ℚ), (.chain [(5, 2)]), (.chain [(5, 2)]), (.chain [(5, 2)]), (.chain [(5, 2)]), (.chain [(5, 2), (5, 3)]), (.chain [(5, 2), (5, 3)]), .one⟩
theorem cell0471_ok : cell0471.check T = true := by decide +kernel

def cell0472 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (14361 / 2560 : ℚ), (36101 / 6400 : ℚ), (.chain [(5, 2)]), (.chain [(5, 2)]), (.chain [(5, 2)]), (.chain [(5, 2), (5, 3)]), (.chain [(5, 2), (5, 3), (5, 4)]), (.chain [(5, 2), (5, 3)]), .one⟩
theorem cell0472_ok : cell0472.check T = true := by decide +kernel

def cell0473 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (14361 / 2560 : ℚ), (36101 / 6400 : ℚ), (.chain [(5, 2)]), (.chain [(5, 3)]), (.chain [(5, 3)]), (.chain [(5, 2), (5, 3)]), (.chain [(5, 3), (5, 4)]), (.chain [(5, 3), (5, 4)]), .one⟩
theorem cell0473_ok : cell0473.check T = true := by decide +kernel

def cell0474 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (36101 / 6400 : ℚ), (72599 / 12800 : ℚ), (.chain [(5, 3)]), (.chain [(5, 3)]), (.chain [(5, 3)]), (.chain [(5, 3), (5, 4)]), (.chain [(5, 3), (5, 4)]), (.chain [(5, 3), (5, 4)]), .one⟩
theorem cell0474_ok : cell0474.check T = true := by decide +kernel

def cell0475 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (36101 / 6400 : ℚ), (72599 / 12800 : ℚ), (.chain [(5, 3)]), (.chain [(5, 4)]), (.chain [(5, 3)]), (.chain [(5, 3), (5, 4)]), (.chain [(5, 4), (5, 5)]), (.chain [(5, 3), (5, 4)]), .one⟩
theorem cell0475_ok : cell0475.check T = true := by decide +kernel

def cell0476 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (72599 / 12800 : ℚ), (18249 / 3200 : ℚ), (.chain [(5, 4)]), (.chain [(5, 4)]), (.chain [(5, 4)]), (.chain [(5, 4), (5, 5)]), (.chain [(5, 4), (5, 5)]), (.chain [(5, 4), (5, 5)]), .one⟩
theorem cell0476_ok : cell0476.check T = true := by decide +kernel

def cell0477 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (72599 / 12800 : ℚ), (18249 / 3200 : ℚ), (.chain [(5, 4)]), (.chain [(5, 4)]), (.chain [(5, 4)]), (.chain [(5, 4), (5, 5)]), (.chain [(5, 4), (5, 5), (5, 6)]), (.chain [(5, 4), (5, 5)]), .one⟩
theorem cell0477_ok : cell0477.check T = true := by decide +kernel

def cell0478 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (18249 / 3200 : ℚ), (73393 / 12800 : ℚ), (.chain [(5, 5)]), (.chain [(5, 5)]), (.chain [(5, 5)]), (.chain [(5, 5)]), (.chain [(5, 5), (5, 6)]), (.chain [(5, 5), (5, 6)]), .one⟩
theorem cell0478_ok : cell0478.check T = true := by decide +kernel

def cell0479 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (18249 / 3200 : ℚ), (73393 / 12800 : ℚ), (.chain [(5, 5)]), (.chain [(5, 5)]), (.chain [(5, 5)]), (.chain [(5, 5)]), (.chain [(5, 5), (5, 6)]), (.chain [(5, 5), (5, 6)]), .one⟩
theorem cell0479_ok : cell0479.check T = true := by decide +kernel

def cells11 : List CellW := [cell0440, cell0441, cell0442, cell0443, cell0444, cell0445, cell0446, cell0447, cell0448, cell0449, cell0450, cell0451, cell0452, cell0453, cell0454, cell0455, cell0456, cell0457, cell0458, cell0459, cell0460, cell0461, cell0462, cell0463, cell0464, cell0465, cell0466, cell0467, cell0468, cell0469, cell0470, cell0471, cell0472, cell0473, cell0474, cell0475, cell0476, cell0477, cell0478, cell0479]

theorem cells11_valid : ∀ w ∈ cells11, w.check T = true :=
  (forall_mem_cons_of cell0440_ok (forall_mem_cons_of cell0441_ok (forall_mem_cons_of cell0442_ok (forall_mem_cons_of cell0443_ok (forall_mem_cons_of cell0444_ok (forall_mem_cons_of cell0445_ok (forall_mem_cons_of cell0446_ok (forall_mem_cons_of cell0447_ok (forall_mem_cons_of cell0448_ok (forall_mem_cons_of cell0449_ok (forall_mem_cons_of cell0450_ok (forall_mem_cons_of cell0451_ok (forall_mem_cons_of cell0452_ok (forall_mem_cons_of cell0453_ok (forall_mem_cons_of cell0454_ok (forall_mem_cons_of cell0455_ok (forall_mem_cons_of cell0456_ok (forall_mem_cons_of cell0457_ok (forall_mem_cons_of cell0458_ok (forall_mem_cons_of cell0459_ok (forall_mem_cons_of cell0460_ok (forall_mem_cons_of cell0461_ok (forall_mem_cons_of cell0462_ok (forall_mem_cons_of cell0463_ok (forall_mem_cons_of cell0464_ok (forall_mem_cons_of cell0465_ok (forall_mem_cons_of cell0466_ok (forall_mem_cons_of cell0467_ok (forall_mem_cons_of cell0468_ok (forall_mem_cons_of cell0469_ok (forall_mem_cons_of cell0470_ok (forall_mem_cons_of cell0471_ok (forall_mem_cons_of cell0472_ok (forall_mem_cons_of cell0473_ok (forall_mem_cons_of cell0474_ok (forall_mem_cons_of cell0475_ok (forall_mem_cons_of cell0476_ok (forall_mem_cons_of cell0477_ok (forall_mem_cons_of cell0478_ok (forall_mem_cons_of cell0479_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


