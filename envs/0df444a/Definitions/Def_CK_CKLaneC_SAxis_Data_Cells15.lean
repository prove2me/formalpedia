-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells15
-- name    : CK_CKLaneC_SAxis_Data_Cells15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T07:58:29.416309+00:00
-- url     : https://prove2.me/theorems/0dfaf84c-4d25-4871-b2b1-b870d0d6805a
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells15` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells15` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells15` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells15 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells15.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells15 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 15 (cells 600..639). -/

def cell0600 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (88479 / 12800 : ℚ), (35471 / 5120 : ℚ), (.chain [(6, 3)]), (.chain [(6, 3)]), (.chain [(6, 3)]), (.chain [(6, 3)]), (.chain [(6, 3), (6, 4)]), (.chain [(6, 3), (6, 4)]), .one⟩
theorem cell0600_ok : cell0600.check T = true := by decide +kernel

def cell0601 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (35471 / 5120 : ℚ), (22219 / 3200 : ℚ), (.chain [(6, 3)]), (.chain [(6, 4)]), (.chain [(6, 4)]), (.chain [(6, 3), (6, 4)]), (.chain [(6, 4), (6, 5)]), (.chain [(6, 4)]), .one⟩
theorem cell0601_ok : cell0601.check T = true := by decide +kernel

def cell0602 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (22219 / 3200 : ℚ), (178149 / 25600 : ℚ), (.chain [(6, 4)]), (.chain [(6, 4)]), (.chain [(6, 4)]), (.chain [(6, 4)]), (.chain [(6, 4), (6, 5)]), (.chain [(6, 4)]), .one⟩
theorem cell0602_ok : cell0602.check T = true := by decide +kernel

def cell0603 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (178149 / 25600 : ℚ), (89273 / 12800 : ℚ), (.chain [(6, 4)]), (.chain [(6, 4)]), (.chain [(6, 4)]), (.chain [(6, 4)]), (.chain [(6, 4), (6, 5)]), (.chain [(6, 4), (6, 5)]), .one⟩
theorem cell0603_ok : cell0603.check T = true := by decide +kernel

def cell0604 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (22219 / 3200 : ℚ), (178149 / 25600 : ℚ), (.chain [(6, 4)]), (.chain [(6, 4)]), (.chain [(6, 4)]), (.chain [(6, 4)]), (.chain [(6, 4), (6, 5)]), (.chain [(6, 4), (6, 5)]), .one⟩
theorem cell0604_ok : cell0604.check T = true := by decide +kernel

def cell0605 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (178149 / 25600 : ℚ), (89273 / 12800 : ℚ), (.chain [(6, 4)]), (.chain [(6, 5)]), (.chain [(6, 4)]), (.chain [(6, 4)]), (.chain [(6, 5)]), (.chain [(6, 4), (6, 5)]), .one⟩
theorem cell0605_ok : cell0605.check T = true := by decide +kernel

def cell0606 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (89273 / 12800 : ℚ), (178943 / 25600 : ℚ), (.chain [(6, 4)]), (.chain [(6, 4)]), (.chain [(6, 4)]), (.chain [(6, 4), (6, 5)]), (.chain [(6, 4), (6, 5)]), (.chain [(6, 4), (6, 5)]), .one⟩
theorem cell0606_ok : cell0606.check T = true := by decide +kernel

def cell0607 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (178943 / 25600 : ℚ), (8967 / 1280 : ℚ), (.chain [(6, 5)]), (.chain [(6, 5)]), (.chain [(6, 5)]), (.chain [(6, 5)]), (.chain [(6, 5), (6, 6)]), (.chain [(6, 5), (6, 6)]), .one⟩
theorem cell0607_ok : cell0607.check T = true := by decide +kernel

def cell0608 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (89273 / 12800 : ℚ), (178943 / 25600 : ℚ), (.chain [(6, 4)]), (.chain [(6, 5)]), (.chain [(6, 5)]), (.chain [(6, 4), (6, 5)]), (.chain [(6, 5), (6, 6)]), (.chain [(6, 5)]), .three⟩
theorem cell0608_ok : cell0608.check T = true := by decide +kernel

def cell0609 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (178943 / 25600 : ℚ), (8967 / 1280 : ℚ), (.chain [(6, 5)]), (.chain [(6, 5)]), (.chain [(6, 5)]), (.chain [(6, 5)]), (.chain [(6, 5), (6, 6)]), (.chain [(6, 5), (6, 6)]), .one⟩
theorem cell0609_ok : cell0609.check T = true := by decide +kernel

def cell0610 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (8967 / 1280 : ℚ), (179737 / 25600 : ℚ), (.chain [(6, 5)]), (.chain [(6, 5)]), (.chain [(6, 5)]), (.chain [(6, 5), (6, 6)]), (.chain [(6, 5), (6, 6)]), (.chain [(6, 5), (6, 6)]), .one⟩
theorem cell0610_ok : cell0610.check T = true := by decide +kernel

def cell0611 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (179737 / 25600 : ℚ), (90067 / 12800 : ℚ), (.chain [(6, 6)]), (.chain [(6, 6)]), (.chain [(6, 6)]), (.chain [(6, 6)]), (.chain [(6, 6), (6, 7)]), (.chain [(6, 6)]), .one⟩
theorem cell0611_ok : cell0611.check T = true := by decide +kernel

def cell0612 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (8967 / 1280 : ℚ), (179737 / 25600 : ℚ), (.chain [(6, 5)]), (.chain [(6, 6)]), (.chain [(6, 6)]), (.chain [(6, 5), (6, 6)]), (.chain [(6, 6), (6, 7)]), (.chain [(6, 6)]), .one⟩
theorem cell0612_ok : cell0612.check T = true := by decide +kernel

def cell0613 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (179737 / 25600 : ℚ), (90067 / 12800 : ℚ), (.chain [(6, 6)]), (.chain [(6, 6)]), (.chain [(6, 6)]), (.chain [(6, 6)]), (.chain [(6, 6), (6, 7)]), (.chain [(6, 6), (6, 7)]), .one⟩
theorem cell0613_ok : cell0613.check T = true := by decide +kernel

def cell0614 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (90067 / 12800 : ℚ), (2827 / 400 : ℚ), (.chain [(6, 6)]), (.chain [(6, 6)]), (.chain [(6, 6)]), (.chain [(6, 6), (6, 7)]), (.chain [(6, 6), (6, 7)]), (.chain [(6, 6), (6, 7)]), .one⟩
theorem cell0614_ok : cell0614.check T = true := by decide +kernel

def cell0615 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (90067 / 12800 : ℚ), (2827 / 400 : ℚ), (.chain [(6, 6)]), (.chain [(6, 6)]), (.chain [(6, 6)]), (.chain [(6, 6), (6, 7)]), (.chain [(6, 6), (6, 7)]), (.chain [(6, 6), (6, 7)]), .one⟩
theorem cell0615_ok : cell0615.check T = true := by decide +kernel

def cell0616 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (90067 / 12800 : ℚ), (180531 / 25600 : ℚ), (.chain [(6, 6)]), (.chain [(6, 7)]), (.chain [(6, 6)]), (.chain [(6, 6)]), (.chain [(6, 7)]), (.chain [(6, 6), (6, 7)]), .one⟩
theorem cell0616_ok : cell0616.check T = true := by decide +kernel

def cell0617 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (180531 / 25600 : ℚ), (2827 / 400 : ℚ), (.chain [(6, 6)]), (.chain [(6, 7)]), (.chain [(6, 7)]), (.chain [(6, 6), (6, 7)]), (.chain [(6, 7), (6, 8)]), (.chain [(6, 7)]), .one⟩
theorem cell0617_ok : cell0617.check T = true := by decide +kernel

def cell0618 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (2827 / 400 : ℚ), (7253 / 1024 : ℚ), (.chain [(6, 7)]), (.chain [(6, 7)]), (.chain [(6, 7)]), (.chain [(6, 7)]), (.chain [(6, 7), (6, 8)]), (.chain [(6, 7)]), .one⟩
theorem cell0618_ok : cell0618.check T = true := by decide +kernel

def cell0619 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (7253 / 1024 : ℚ), (90861 / 12800 : ℚ), (.chain [(6, 7)]), (.chain [(6, 7)]), (.chain [(6, 7)]), (.chain [(6, 7), (6, 8)]), (.chain [(6, 7), (6, 8)]), (.chain [(6, 7), (6, 8)]), .one⟩
theorem cell0619_ok : cell0619.check T = true := by decide +kernel

def cell0620 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (2827 / 400 : ℚ), (7253 / 1024 : ℚ), (.chain [(6, 7)]), (.chain [(6, 7)]), (.chain [(6, 7)]), (.chain [(6, 7)]), (.chain [(6, 7), (6, 8)]), (.chain [(6, 7), (6, 8)]), .one⟩
theorem cell0620_ok : cell0620.check T = true := by decide +kernel

def cell0621 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (7253 / 1024 : ℚ), (90861 / 12800 : ℚ), (.chain [(6, 7)]), (.chain [(6, 8)]), (.chain [(6, 7)]), (.chain [(6, 7), (6, 8)]), (.chain [(6, 8), (6, 9)]), (.chain [(6, 7), (6, 8)]), .one⟩
theorem cell0621_ok : cell0621.check T = true := by decide +kernel

def cell0622 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (90861 / 12800 : ℚ), (182119 / 25600 : ℚ), (.chain [(6, 8)]), (.chain [(6, 8)]), (.chain [(6, 8)]), (.chain [(6, 8)]), (.chain [(6, 8)]), (.chain [(6, 8)]), .one⟩
theorem cell0622_ok : cell0622.check T = true := by decide +kernel

def cell0623 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (182119 / 25600 : ℚ), (45629 / 6400 : ℚ), (.chain [(6, 8)]), (.chain [(6, 8)]), (.chain [(6, 8)]), (.chain [(6, 8)]), (.chain [(6, 8), (6, 9)]), (.chain [(6, 8), (6, 9)]), .three⟩
theorem cell0623_ok : cell0623.check T = true := by decide +kernel

def cell0624 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (90861 / 12800 : ℚ), (45629 / 6400 : ℚ), (.chain [(6, 8)]), (.chain [(6, 8)]), (.chain [(6, 8)]), (.chain [(6, 8)]), (.chain [(6, 8), (6, 9)]), (.chain [(6, 8), (6, 9)]), .one⟩
theorem cell0624_ok : cell0624.check T = true := by decide +kernel

def cell0625 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (90861 / 12800 : ℚ), (45629 / 6400 : ℚ), (.chain [(6, 8)]), (.chain [(6, 8)]), (.chain [(6, 8)]), (.chain [(6, 8)]), (.chain [(6, 8), (6, 9)]), (.chain [(6, 8), (6, 9)]), .one⟩
theorem cell0625_ok : cell0625.check T = true := by decide +kernel

def cell0626 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (45629 / 6400 : ℚ), (182913 / 25600 : ℚ), (.chain [(6, 8)]), (.chain [(6, 8)]), (.chain [(6, 8)]), (.chain [(6, 8), (6, 9)]), (.chain [(6, 8), (6, 9)]), (.chain [(6, 8), (6, 9)]), .one⟩
theorem cell0626_ok : cell0626.check T = true := by decide +kernel

def cell0627 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (182913 / 25600 : ℚ), (18331 / 2560 : ℚ), (.chain [(6, 9)]), (.chain [(6, 9)]), (.chain [(6, 9)]), (.chain [(6, 9)]), (.chain [(6, 9), (6, 10)]), (.chain [(6, 9)]), .one⟩
theorem cell0627_ok : cell0627.check T = true := by decide +kernel

def cell0628 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (45629 / 6400 : ℚ), (182913 / 25600 : ℚ), (.chain [(6, 8)]), (.chain [(6, 9)]), (.chain [(6, 9)]), (.chain [(6, 8), (6, 9)]), (.chain [(6, 9), (6, 10)]), (.chain [(6, 9)]), .one⟩
theorem cell0628_ok : cell0628.check T = true := by decide +kernel

def cell0629 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (182913 / 25600 : ℚ), (18331 / 2560 : ℚ), (.chain [(6, 9)]), (.chain [(6, 9)]), (.chain [(6, 9)]), (.chain [(6, 9)]), (.chain [(6, 9), (6, 10)]), (.chain [(6, 9), (6, 10)]), .one⟩
theorem cell0629_ok : cell0629.check T = true := by decide +kernel

def cell0630 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (18331 / 2560 : ℚ), (183707 / 25600 : ℚ), (.chain [(6, 9)]), (.chain [(6, 9)]), (.chain [(6, 9)]), (.chain [(6, 9), (6, 10)]), (.chain [(6, 9), (6, 10)]), (.chain [(6, 9), (6, 10)]), .one⟩
theorem cell0630_ok : cell0630.check T = true := by decide +kernel

def cell0631 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (183707 / 25600 : ℚ), (23013 / 3200 : ℚ), (.chain [(6, 10)]), (.chain [(6, 10)]), (.chain [(6, 10)]), (.chain [(6, 10)]), (.chain [(6, 10)]), (.chain [(6, 10)]), .one⟩
theorem cell0631_ok : cell0631.check T = true := by decide +kernel

def cell0632 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (18331 / 2560 : ℚ), (183707 / 25600 : ℚ), (.chain [(6, 9)]), (.chain [(6, 10)]), (.chain [(6, 9)]), (.chain [(6, 9), (6, 10)]), (.chain [(6, 10), (6, 11)]), (.chain [(6, 9), (6, 10)]), .one⟩
theorem cell0632_ok : cell0632.check T = true := by decide +kernel

def cell0633 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (183707 / 25600 : ℚ), (23013 / 3200 : ℚ), (.chain [(6, 10)]), (.chain [(6, 10)]), (.chain [(6, 10)]), (.chain [(6, 10)]), (.chain [(6, 10), (6, 11)]), (.chain [(6, 10)]), .three⟩
theorem cell0633_ok : cell0633.check T = true := by decide +kernel

def cell0634 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (23013 / 3200 : ℚ), (184501 / 25600 : ℚ), (.chain [(6, 10)]), (.chain [(6, 10)]), (.chain [(6, 10)]), (.chain [(6, 10)]), (.chain [(6, 10), (6, 11)]), (.chain [(6, 10), (6, 11)]), .one⟩
theorem cell0634_ok : cell0634.check T = true := by decide +kernel

def cell0635 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (184501 / 25600 : ℚ), (92449 / 12800 : ℚ), (.chain [(6, 10)]), (.chain [(6, 10)]), (.chain [(6, 10)]), (.chain [(6, 10), (6, 11)]), (.chain [(6, 10), (6, 11)]), (.chain [(6, 10), (6, 11)]), .one⟩
theorem cell0635_ok : cell0635.check T = true := by decide +kernel

def cell0636 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (23013 / 3200 : ℚ), (184501 / 25600 : ℚ), (.chain [(6, 10)]), (.chain [(6, 10)]), (.chain [(6, 10)]), (.chain [(6, 10)]), (.chain [(6, 10), (6, 11)]), (.chain [(6, 10), (6, 11)]), .one⟩
theorem cell0636_ok : cell0636.check T = true := by decide +kernel

def cell0637 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (184501 / 25600 : ℚ), (92449 / 12800 : ℚ), (.chain [(6, 10)]), (.chain [(6, 11)]), (.chain [(6, 11)]), (.chain [(6, 10), (6, 11)]), (.chain [(6, 11), (6, 12)]), (.chain [(6, 11)]), .one⟩
theorem cell0637_ok : cell0637.check T = true := by decide +kernel

def cell0638 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (92449 / 12800 : ℚ), (46423 / 6400 : ℚ), (.chain [(6, 11)]), (.chain [(6, 11)]), (.chain [(6, 11)]), (.chain [(6, 11)]), (.chain [(6, 11), (6, 12)]), (.chain [(6, 11), (6, 12)]), .one⟩
theorem cell0638_ok : cell0638.check T = true := by decide +kernel

def cell0639 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (92449 / 12800 : ℚ), (46423 / 6400 : ℚ), (.chain [(6, 11)]), (.chain [(6, 11)]), (.chain [(6, 11)]), (.chain [(6, 11)]), (.chain [(6, 11), (6, 12)]), (.chain [(6, 11), (6, 12)]), .one⟩
theorem cell0639_ok : cell0639.check T = true := by decide +kernel

def cells15 : List CellW := [cell0600, cell0601, cell0602, cell0603, cell0604, cell0605, cell0606, cell0607, cell0608, cell0609, cell0610, cell0611, cell0612, cell0613, cell0614, cell0615, cell0616, cell0617, cell0618, cell0619, cell0620, cell0621, cell0622, cell0623, cell0624, cell0625, cell0626, cell0627, cell0628, cell0629, cell0630, cell0631, cell0632, cell0633, cell0634, cell0635, cell0636, cell0637, cell0638, cell0639]

theorem cells15_valid : ∀ w ∈ cells15, w.check T = true :=
  (forall_mem_cons_of cell0600_ok (forall_mem_cons_of cell0601_ok (forall_mem_cons_of cell0602_ok (forall_mem_cons_of cell0603_ok (forall_mem_cons_of cell0604_ok (forall_mem_cons_of cell0605_ok (forall_mem_cons_of cell0606_ok (forall_mem_cons_of cell0607_ok (forall_mem_cons_of cell0608_ok (forall_mem_cons_of cell0609_ok (forall_mem_cons_of cell0610_ok (forall_mem_cons_of cell0611_ok (forall_mem_cons_of cell0612_ok (forall_mem_cons_of cell0613_ok (forall_mem_cons_of cell0614_ok (forall_mem_cons_of cell0615_ok (forall_mem_cons_of cell0616_ok (forall_mem_cons_of cell0617_ok (forall_mem_cons_of cell0618_ok (forall_mem_cons_of cell0619_ok (forall_mem_cons_of cell0620_ok (forall_mem_cons_of cell0621_ok (forall_mem_cons_of cell0622_ok (forall_mem_cons_of cell0623_ok (forall_mem_cons_of cell0624_ok (forall_mem_cons_of cell0625_ok (forall_mem_cons_of cell0626_ok (forall_mem_cons_of cell0627_ok (forall_mem_cons_of cell0628_ok (forall_mem_cons_of cell0629_ok (forall_mem_cons_of cell0630_ok (forall_mem_cons_of cell0631_ok (forall_mem_cons_of cell0632_ok (forall_mem_cons_of cell0633_ok (forall_mem_cons_of cell0634_ok (forall_mem_cons_of cell0635_ok (forall_mem_cons_of cell0636_ok (forall_mem_cons_of cell0637_ok (forall_mem_cons_of cell0638_ok (forall_mem_cons_of cell0639_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


