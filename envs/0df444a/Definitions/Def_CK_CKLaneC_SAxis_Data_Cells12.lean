-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells12
-- name    : CK_CKLaneC_SAxis_Data_Cells12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:43:17.608983+00:00
-- url     : https://prove2.me/theorems/8526c305-1a5d-4aa7-97ab-775b0bd2b18f
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells12` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells12` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells12` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells12 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells12.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells12 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 12 (cells 480..519). -/

def cell0480 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (73393 / 12800 : ℚ), (7379 / 1280 : ℚ), (.chain [(5, 5)]), (.chain [(5, 5)]), (.chain [(5, 5)]), (.chain [(5, 5), (5, 6)]), (.chain [(5, 5), (5, 6), (5, 7)]), (.chain [(5, 5), (5, 6)]), .one⟩
theorem cell0480_ok : cell0480.check T = true := by decide +kernel

def cell0481 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (73393 / 12800 : ℚ), (7379 / 1280 : ℚ), (.chain [(5, 5)]), (.chain [(5, 6)]), (.chain [(5, 6)]), (.chain [(5, 5), (5, 6)]), (.chain [(5, 6), (5, 7)]), (.chain [(5, 6), (5, 7)]), .one⟩
theorem cell0481_ok : cell0481.check T = true := by decide +kernel

def cell0482 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (7379 / 1280 : ℚ), (74187 / 12800 : ℚ), (.chain [(5, 6)]), (.chain [(5, 6)]), (.chain [(5, 6)]), (.chain [(5, 6), (5, 7)]), (.chain [(5, 6), (5, 7), (5, 8)]), (.chain [(5, 6), (5, 7)]), .one⟩
theorem cell0482_ok : cell0482.check T = true := by decide +kernel

def cell0483 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (7379 / 1280 : ℚ), (74187 / 12800 : ℚ), (.chain [(5, 6)]), (.chain [(5, 7)]), (.chain [(5, 6)]), (.chain [(5, 6), (5, 7)]), (.chain [(5, 7), (5, 8)]), (.chain [(5, 6), (5, 7), (5, 8)]), .one⟩
theorem cell0483_ok : cell0483.check T = true := by decide +kernel

def cell0484 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (74187 / 12800 : ℚ), (9323 / 1600 : ℚ), (.chain [(5, 7)]), (.chain [(5, 7)]), (.chain [(5, 7)]), (.chain [(5, 7), (5, 8)]), (.chain [(5, 7), (5, 8)]), (.chain [(5, 7), (5, 8)]), .one⟩
theorem cell0484_ok : cell0484.check T = true := by decide +kernel

def cell0485 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (74187 / 12800 : ℚ), (9323 / 1600 : ℚ), (.chain [(5, 7)]), (.chain [(5, 8)]), (.chain [(5, 7)]), (.chain [(5, 7), (5, 8)]), (.chain [(5, 8), (5, 9)]), (.chain [(5, 7), (5, 8)]), .one⟩
theorem cell0485_ok : cell0485.check T = true := by decide +kernel

def cell0486 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (9323 / 1600 : ℚ), (74981 / 12800 : ℚ), (.chain [(5, 8)]), (.chain [(5, 8)]), (.chain [(5, 8)]), (.chain [(5, 8), (5, 9)]), (.chain [(5, 8), (5, 9)]), (.chain [(5, 8), (5, 9)]), .one⟩
theorem cell0486_ok : cell0486.check T = true := by decide +kernel

def cell0487 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (9323 / 1600 : ℚ), (74981 / 12800 : ℚ), (.chain [(5, 8)]), (.chain [(5, 8)]), (.chain [(5, 8)]), (.chain [(5, 8), (5, 9)]), (.chain [(5, 8), (5, 9), (5, 10)]), (.chain [(5, 8), (5, 9)]), .one⟩
theorem cell0487_ok : cell0487.check T = true := by decide +kernel

def cell0488 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (74981 / 12800 : ℚ), (37689 / 6400 : ℚ), (.chain [(5, 9)]), (.chain [(5, 9)]), (.chain [(5, 9)]), (.chain [(5, 9)]), (.chain [(5, 9), (5, 10)]), (.chain [(5, 9), (5, 10)]), .one⟩
theorem cell0488_ok : cell0488.check T = true := by decide +kernel

def cell0489 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (74981 / 12800 : ℚ), (37689 / 6400 : ℚ), (.chain [(5, 9)]), (.chain [(5, 9)]), (.chain [(5, 9)]), (.chain [(5, 9)]), (.chain [(5, 9), (5, 10)]), (.chain [(5, 9), (5, 10)]), .one⟩
theorem cell0489_ok : cell0489.check T = true := by decide +kernel

def cell0490 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (37689 / 6400 : ℚ), (3031 / 512 : ℚ), (.chain [(5, 9)]), (.chain [(5, 9)]), (.chain [(5, 9)]), (.chain [(5, 9), (5, 10)]), (.chain [(5, 9), (5, 10), (5, 11)]), (.chain [(5, 9), (5, 10)]), .one⟩
theorem cell0490_ok : cell0490.check T = true := by decide +kernel

def cell0491 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (37689 / 6400 : ℚ), (3031 / 512 : ℚ), (.chain [(5, 9)]), (.chain [(5, 10)]), (.chain [(5, 10)]), (.chain [(5, 9), (5, 10)]), (.chain [(5, 10), (5, 11)]), (.chain [(5, 10), (5, 11)]), .one⟩
theorem cell0491_ok : cell0491.check T = true := by decide +kernel

def cell0492 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (3031 / 512 : ℚ), (19043 / 3200 : ℚ), (.chain [(5, 10)]), (.chain [(5, 10)]), (.chain [(5, 10)]), (.chain [(5, 10), (5, 11)]), (.chain [(5, 10), (5, 11)]), (.chain [(5, 10), (5, 11)]), .one⟩
theorem cell0492_ok : cell0492.check T = true := by decide +kernel

def cell0493 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (3031 / 512 : ℚ), (19043 / 3200 : ℚ), (.chain [(5, 10)]), (.chain [(5, 11)]), (.chain [(5, 10)]), (.chain [(5, 10), (5, 11)]), (.chain [(5, 11), (5, 12)]), (.chain [(5, 10), (5, 11)]), .one⟩
theorem cell0493_ok : cell0493.check T = true := by decide +kernel

def cell0494 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (19043 / 3200 : ℚ), (76569 / 12800 : ℚ), (.chain [(5, 11)]), (.chain [(5, 11)]), (.chain [(5, 11)]), (.chain [(5, 11), (5, 12)]), (.chain [(5, 11), (5, 12)]), (.chain [(5, 11), (5, 12)]), .one⟩
theorem cell0494_ok : cell0494.check T = true := by decide +kernel

def cell0495 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (19043 / 3200 : ℚ), (76569 / 12800 : ℚ), (.chain [(5, 11)]), (.chain [(5, 11)]), (.chain [(5, 11)]), (.chain [(5, 11), (5, 12)]), (.chain [(5, 11), (5, 12), (5, 13)]), (.chain [(5, 11), (5, 12)]), .one⟩
theorem cell0495_ok : cell0495.check T = true := by decide +kernel

def cell0496 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (76569 / 12800 : ℚ), (38483 / 6400 : ℚ), (.chain [(5, 12)]), (.chain [(5, 12)]), (.chain [(5, 12)]), (.chain [(5, 12)]), (.chain [(5, 12), (5, 13)]), (.chain [(5, 12), (5, 13)]), .one⟩
theorem cell0496_ok : cell0496.check T = true := by decide +kernel

def cell0497 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (76569 / 12800 : ℚ), (38483 / 6400 : ℚ), (.chain [(5, 12)]), (.chain [(5, 12)]), (.chain [(5, 12)]), (.chain [(5, 12)]), (.chain [(5, 12), (5, 13)]), (.chain [(5, 12), (5, 13)]), .one⟩
theorem cell0497_ok : cell0497.check T = true := by decide +kernel

def cell0498 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (38483 / 6400 : ℚ), (154329 / 25600 : ℚ), (.chain [(5, 12)]), (.chain [(5, 12)]), (.chain [(5, 12)]), (.chain [(5, 12), (5, 13)]), (.chain [(5, 12), (5, 13)]), (.chain [(5, 12), (5, 13)]), .one⟩
theorem cell0498_ok : cell0498.check T = true := by decide +kernel

def cell0499 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (154329 / 25600 : ℚ), (77363 / 12800 : ℚ), (.chain [(5, 13)]), (.chain [(5, 13)]), (.chain [(5, 13)]), (.chain [(5, 13)]), (.chain [(5, 13), (5, 14)]), (.chain [(5, 13)]), .one⟩
theorem cell0499_ok : cell0499.check T = true := by decide +kernel

def cell0500 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (38483 / 6400 : ℚ), (77363 / 12800 : ℚ), (.chain [(5, 12)]), (.chain [(5, 13)]), (.chain [(5, 13)]), (.chain [(5, 12), (5, 13)]), (.chain [(5, 13), (5, 14)]), (.chain [(5, 13), (5, 14)]), .one⟩
theorem cell0500_ok : cell0500.check T = true := by decide +kernel

def cell0501 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (77363 / 12800 : ℚ), (243 / 40 : ℚ), (.chain [(5, 13)]), (.chain [(5, 13)]), (.chain [(5, 13)]), (.chain [(5, 13), (5, 14)]), (.chain [(5, 13), (5, 14), (5, 15)]), (.chain [(5, 13), (5, 14)]), .one⟩
theorem cell0501_ok : cell0501.check T = true := by decide +kernel

def cell0502 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (77363 / 12800 : ℚ), (243 / 40 : ℚ), (.chain [(5, 13)]), (.chain [(5, 14)]), (.chain [(5, 13)]), (.chain [(5, 13), (5, 14)]), (.chain [(5, 14), (5, 15)]), (.chain [(5, 13), (5, 14), (5, 15)]), .one⟩
theorem cell0502_ok : cell0502.check T = true := by decide +kernel

def cell0503 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (243 / 40 : ℚ), (78157 / 12800 : ℚ), (.chain [(5, 14)]), (.chain [(5, 14)]), (.chain [(5, 14)]), (.chain [(5, 14), (5, 15)]), (.chain [(5, 14), (5, 15)]), (.chain [(5, 14), (5, 15)]), .one⟩
theorem cell0503_ok : cell0503.check T = true := by decide +kernel

def cell0504 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (243 / 40 : ℚ), (78157 / 12800 : ℚ), (.chain [(5, 14)]), (.chain [(5, 15)]), (.chain [(5, 14)]), (.chain [(5, 14), (5, 15)]), (.chain [(5, 15), (5, 16)]), (.chain [(5, 14), (5, 15)]), .one⟩
theorem cell0504_ok : cell0504.check T = true := by decide +kernel

def cell0505 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (243 / 40 : ℚ), (78157 / 12800 : ℚ), (.chain [(5, 14)]), (.chain [(5, 15)]), (.chain [(5, 14)]), (.chain [(5, 14), (5, 15)]), (.chain [(5, 15), (5, 16)]), (.chain [(5, 14), (5, 15)]), .one⟩
theorem cell0505_ok : cell0505.check T = true := by decide +kernel

def cell0506 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (78157 / 12800 : ℚ), (39277 / 6400 : ℚ), (.chain [(5, 15)]), (.chain [(5, 15)]), (.chain [(5, 15)]), (.chain [(5, 15), (5, 16)]), (.chain [(5, 15), (5, 16)]), (.chain [(5, 15), (5, 16)]), .one⟩
theorem cell0506_ok : cell0506.check T = true := by decide +kernel

def cell0507 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (78157 / 12800 : ℚ), (39277 / 6400 : ℚ), (.chain [(5, 15)]), (.chain [(5, 15)]), (.chain [(5, 15)]), (.chain [(5, 15), (5, 16)]), (.chain [(5, 15), (5, 16), (5, 17)]), (.chain [(5, 15), (5, 16)]), .one⟩
theorem cell0507_ok : cell0507.check T = true := by decide +kernel

def cell0508 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (39277 / 6400 : ℚ), (78951 / 12800 : ℚ), (.chain [(5, 16)]), (.chain [(5, 16)]), (.chain [(5, 16)]), (.chain [(5, 16)]), (.chain [(5, 16), (5, 17)]), (.chain [(5, 16)]), .one⟩
theorem cell0508_ok : cell0508.check T = true := by decide +kernel

def cell0509 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (39277 / 6400 : ℚ), (78951 / 12800 : ℚ), (.chain [(5, 16)]), (.chain [(5, 16)]), (.chain [(5, 16)]), (.chain [(5, 16)]), (.chain [(5, 16), (5, 17)]), (.chain [(5, 16), (5, 17)]), .one⟩
theorem cell0509_ok : cell0509.check T = true := by decide +kernel

def cell0510 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (39277 / 6400 : ℚ), (78951 / 12800 : ℚ), (.chain [(5, 16)]), (.chain [(5, 16)]), (.chain [(5, 16)]), (.chain [(5, 16)]), (.chain [(5, 16), (5, 17)]), (.chain [(5, 16), (5, 17)]), .one⟩
theorem cell0510_ok : cell0510.check T = true := by decide +kernel

def cell0511 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (78951 / 12800 : ℚ), (158299 / 25600 : ℚ), (.chain [(5, 16)]), (.chain [(5, 16)]), (.chain [(5, 16)]), (.chain [(5, 16), (5, 17)]), (.chain [(5, 16), (5, 17)]), (.chain [(5, 16), (5, 17)]), .one⟩
theorem cell0511_ok : cell0511.check T = true := by decide +kernel

def cell0512 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (158299 / 25600 : ℚ), (19837 / 3200 : ℚ), (.chain [(5, 17)]), (.chain [(5, 17)]), (.chain [(5, 17)]), (.chain [(5, 17)]), (.chain [(5, 17), (5, 18)]), (.chain [(5, 17)]), .one⟩
theorem cell0512_ok : cell0512.check T = true := by decide +kernel

def cell0513 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (78951 / 12800 : ℚ), (19837 / 3200 : ℚ), (.chain [(5, 16)]), (.chain [(5, 17)]), (.chain [(5, 17)]), (.chain [(5, 16), (5, 17)]), (.chain [(5, 17), (5, 18)]), (.chain [(5, 17), (5, 18)]), .one⟩
theorem cell0513_ok : cell0513.check T = true := by decide +kernel

def cell0514 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (19837 / 3200 : ℚ), (15949 / 2560 : ℚ), (.chain [(5, 17)]), (.chain [(5, 17)]), (.chain [(5, 17)]), (.chain [(5, 17), (5, 18)]), (.chain [(5, 17), (5, 18)]), (.chain [(5, 17), (5, 18)]), .one⟩
theorem cell0514_ok : cell0514.check T = true := by decide +kernel

def cell0515 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (19837 / 3200 : ℚ), (159093 / 25600 : ℚ), (.chain [(5, 17)]), (.chain [(5, 18)]), (.chain [(5, 17)]), (.chain [(5, 17)]), (.chain [(5, 18)]), (.chain [(5, 17), (5, 18)]), .one⟩
theorem cell0515_ok : cell0515.check T = true := by decide +kernel

def cell0516 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (159093 / 25600 : ℚ), (15949 / 2560 : ℚ), (.chain [(5, 17)]), (.chain [(5, 18)]), (.chain [(5, 18)]), (.chain [(5, 17), (5, 18)]), (.chain [(5, 18), (5, 19)]), (.chain [(5, 18)]), .three⟩
theorem cell0516_ok : cell0516.check T = true := by decide +kernel

def cell0517 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (15949 / 2560 : ℚ), (40071 / 6400 : ℚ), (.chain [(5, 18)]), (.chain [(5, 18)]), (.chain [(5, 18)]), (.chain [(5, 18), (5, 19)]), (.chain [(5, 18), (5, 19)]), (.chain [(5, 18), (5, 19)]), .one⟩
theorem cell0517_ok : cell0517.check T = true := by decide +kernel

def cell0518 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (15949 / 2560 : ℚ), (159887 / 25600 : ℚ), (.chain [(5, 18)]), (.chain [(5, 18)]), (.chain [(5, 18)]), (.chain [(5, 18)]), (.chain [(5, 18), (5, 19)]), (.chain [(5, 18), (5, 19)]), .one⟩
theorem cell0518_ok : cell0518.check T = true := by decide +kernel

def cell0519 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (159887 / 25600 : ℚ), (40071 / 6400 : ℚ), (.chain [(5, 18)]), (.chain [(5, 19)]), (.chain [(5, 19)]), (.chain [(5, 18), (5, 19)]), (.chain [(5, 19), (5, 20)]), (.chain [(5, 19)]), .one⟩
theorem cell0519_ok : cell0519.check T = true := by decide +kernel

def cells12 : List CellW := [cell0480, cell0481, cell0482, cell0483, cell0484, cell0485, cell0486, cell0487, cell0488, cell0489, cell0490, cell0491, cell0492, cell0493, cell0494, cell0495, cell0496, cell0497, cell0498, cell0499, cell0500, cell0501, cell0502, cell0503, cell0504, cell0505, cell0506, cell0507, cell0508, cell0509, cell0510, cell0511, cell0512, cell0513, cell0514, cell0515, cell0516, cell0517, cell0518, cell0519]

theorem cells12_valid : ∀ w ∈ cells12, w.check T = true :=
  (forall_mem_cons_of cell0480_ok (forall_mem_cons_of cell0481_ok (forall_mem_cons_of cell0482_ok (forall_mem_cons_of cell0483_ok (forall_mem_cons_of cell0484_ok (forall_mem_cons_of cell0485_ok (forall_mem_cons_of cell0486_ok (forall_mem_cons_of cell0487_ok (forall_mem_cons_of cell0488_ok (forall_mem_cons_of cell0489_ok (forall_mem_cons_of cell0490_ok (forall_mem_cons_of cell0491_ok (forall_mem_cons_of cell0492_ok (forall_mem_cons_of cell0493_ok (forall_mem_cons_of cell0494_ok (forall_mem_cons_of cell0495_ok (forall_mem_cons_of cell0496_ok (forall_mem_cons_of cell0497_ok (forall_mem_cons_of cell0498_ok (forall_mem_cons_of cell0499_ok (forall_mem_cons_of cell0500_ok (forall_mem_cons_of cell0501_ok (forall_mem_cons_of cell0502_ok (forall_mem_cons_of cell0503_ok (forall_mem_cons_of cell0504_ok (forall_mem_cons_of cell0505_ok (forall_mem_cons_of cell0506_ok (forall_mem_cons_of cell0507_ok (forall_mem_cons_of cell0508_ok (forall_mem_cons_of cell0509_ok (forall_mem_cons_of cell0510_ok (forall_mem_cons_of cell0511_ok (forall_mem_cons_of cell0512_ok (forall_mem_cons_of cell0513_ok (forall_mem_cons_of cell0514_ok (forall_mem_cons_of cell0515_ok (forall_mem_cons_of cell0516_ok (forall_mem_cons_of cell0517_ok (forall_mem_cons_of cell0518_ok (forall_mem_cons_of cell0519_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


