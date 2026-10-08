-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells17
-- name    : CK_CKLaneC_SAxis_Data_Cells17
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T04:14:44.56489+00:00
-- url     : https://prove2.me/theorems/9452c296-71c2-4660-915d-898df42432d3
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells17` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells17` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells17` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells17 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells17.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells17 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 17 (cells 680..719). -/

def cell0680 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (96419 / 12800 : ℚ), (6051 / 800 : ℚ), (.chain [(6, 18)]), (.chain [(6, 19)]), (.chain [(6, 19)]), (.chain [(6, 18), (6, 19)]), (.chain [(6, 19), (6, 20)]), (.chain [(6, 19), (6, 20)]), .one⟩
theorem cell0680_ok : cell0680.check T = true := by decide +kernel

def cell0681 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (96419 / 12800 : ℚ), (6051 / 800 : ℚ), (.chain [(6, 18)]), (.chain [(6, 19)]), (.chain [(6, 19)]), (.chain [(6, 18), (6, 19)]), (.chain [(6, 19), (6, 20)]), (.chain [(6, 19), (6, 20)]), .one⟩
theorem cell0681_ok : cell0681.check T = true := by decide +kernel

def cell0682 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (6051 / 800 : ℚ), (194029 / 25600 : ℚ), (.chain [(6, 19)]), (.chain [(6, 19)]), (.chain [(6, 19)]), (.chain [(6, 19), (6, 20)]), (.chain [(6, 19), (6, 20)]), (.chain [(6, 19), (6, 20)]), .one⟩
theorem cell0682_ok : cell0682.check T = true := by decide +kernel

def cell0683 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (194029 / 25600 : ℚ), (97213 / 12800 : ℚ), (.chain [(6, 20)]), (.chain [(6, 20)]), (.chain [(6, 20)]), (.chain [(6, 20)]), (.chain [(6, 20)]), (.chain [(6, 20)]), .one⟩
theorem cell0683_ok : cell0683.check T = true := by decide +kernel

def cell0684 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (6051 / 800 : ℚ), (194029 / 25600 : ℚ), (.chain [(6, 19)]), (.chain [(6, 20)]), (.chain [(6, 19)]), (.chain [(6, 19), (6, 20)]), (.chain [(6, 20), (6, 21)]), (.chain [(6, 19), (6, 20)]), .one⟩
theorem cell0684_ok : cell0684.check T = true := by decide +kernel

def cell0685 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (194029 / 25600 : ℚ), (97213 / 12800 : ℚ), (.chain [(6, 20)]), (.chain [(6, 20)]), (.chain [(6, 20)]), (.chain [(6, 20)]), (.chain [(6, 20), (6, 21)]), (.chain [(6, 20)]), .one⟩
theorem cell0685_ok : cell0685.check T = true := by decide +kernel

def cell0686 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (97213 / 12800 : ℚ), (194823 / 25600 : ℚ), (.chain [(6, 20)]), (.chain [(6, 20)]), (.chain [(6, 20)]), (.chain [(6, 20)]), (.chain [(6, 20), (6, 21)]), (.chain [(6, 20), (6, 21)]), .three⟩
theorem cell0686_ok : cell0686.check T = true := by decide +kernel

def cell0687 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (194823 / 25600 : ℚ), (9761 / 1280 : ℚ), (.chain [(6, 20)]), (.chain [(6, 20)]), (.chain [(6, 20)]), (.chain [(6, 20), (6, 21)]), (.chain [(6, 20), (6, 21)]), (.chain [(6, 20), (6, 21)]), .one⟩
theorem cell0687_ok : cell0687.check T = true := by decide +kernel

def cell0688 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (97213 / 12800 : ℚ), (194823 / 25600 : ℚ), (.chain [(6, 20)]), (.chain [(6, 20)]), (.chain [(6, 20)]), (.chain [(6, 20)]), (.chain [(6, 20), (6, 21)]), (.chain [(6, 20), (6, 21)]), .one⟩
theorem cell0688_ok : cell0688.check T = true := by decide +kernel

def cell0689 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (194823 / 25600 : ℚ), (9761 / 1280 : ℚ), (.chain [(6, 20)]), (.chain [(6, 21)]), (.chain [(6, 21)]), (.chain [(6, 20), (6, 21)]), (.chain [(6, 21), (6, 22)]), (.chain [(6, 21)]), .one⟩
theorem cell0689_ok : cell0689.check T = true := by decide +kernel

def cell0690 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (9761 / 1280 : ℚ), (195617 / 25600 : ℚ), (.chain [(6, 21)]), (.chain [(6, 21)]), (.chain [(6, 21)]), (.chain [(6, 21)]), (.chain [(6, 21), (6, 22)]), (.chain [(6, 21)]), .one⟩
theorem cell0690_ok : cell0690.check T = true := by decide +kernel

def cell0691 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (195617 / 25600 : ℚ), (98007 / 12800 : ℚ), (.chain [(6, 21)]), (.chain [(6, 21)]), (.chain [(6, 21)]), (.chain [(6, 21), (6, 22)]), (.chain [(6, 21), (6, 22)]), (.chain [(6, 21), (6, 22)]), .one⟩
theorem cell0691_ok : cell0691.check T = true := by decide +kernel

def cell0692 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (9761 / 1280 : ℚ), (195617 / 25600 : ℚ), (.chain [(6, 21)]), (.chain [(6, 21)]), (.chain [(6, 21)]), (.chain [(6, 21)]), (.chain [(6, 21), (6, 22)]), (.chain [(6, 21), (6, 22)]), .one⟩
theorem cell0692_ok : cell0692.check T = true := by decide +kernel

def cell0693 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (195617 / 25600 : ℚ), (98007 / 12800 : ℚ), (.chain [(6, 21)]), (.chain [(6, 22)]), (.chain [(6, 21)]), (.chain [(6, 21), (6, 22)]), (.chain [(6, 22), (6, 23)]), (.chain [(6, 21), (6, 22)]), .one⟩
theorem cell0693_ok : cell0693.check T = true := by decide +kernel

def cell0694 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (98007 / 12800 : ℚ), (196411 / 25600 : ℚ), (.chain [(6, 22)]), (.chain [(6, 22)]), (.chain [(6, 22)]), (.chain [(6, 22)]), (.chain [(6, 22)]), (.chain [(6, 22)]), .one⟩
theorem cell0694_ok : cell0694.check T = true := by decide +kernel

def cell0695 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (196411 / 25600 : ℚ), (24601 / 3200 : ℚ), (.chain [(6, 22)]), (.chain [(6, 22)]), (.chain [(6, 22)]), (.chain [(6, 22)]), (.chain [(6, 22), (6, 23)]), (.chain [(6, 22), (6, 23)]), .three⟩
theorem cell0695_ok : cell0695.check T = true := by decide +kernel

def cell0696 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (98007 / 12800 : ℚ), (24601 / 3200 : ℚ), (.chain [(6, 22)]), (.chain [(6, 22)]), (.chain [(6, 22)]), (.chain [(6, 22)]), (.chain [(6, 22), (6, 23)]), (.chain [(6, 22), (6, 23)]), .one⟩
theorem cell0696_ok : cell0696.check T = true := by decide +kernel

def cell0697 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (98007 / 12800 : ℚ), (24601 / 3200 : ℚ), (.chain [(6, 22)]), (.chain [(6, 22)]), (.chain [(6, 22)]), (.chain [(6, 22)]), (.chain [(6, 22), (6, 23)]), (.chain [(6, 22), (6, 23)]), .one⟩
theorem cell0697_ok : cell0697.check T = true := by decide +kernel

def cell0698 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (24601 / 3200 : ℚ), (39441 / 5120 : ℚ), (.chain [(6, 22)]), (.chain [(6, 22)]), (.chain [(6, 22)]), (.chain [(6, 22), (6, 23)]), (.chain [(6, 22), (6, 23)]), (.chain [(6, 22), (6, 23)]), .one⟩
theorem cell0698_ok : cell0698.check T = true := by decide +kernel

def cell0699 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (39441 / 5120 : ℚ), (98801 / 12800 : ℚ), (.chain [(6, 23)]), (.chain [(6, 23)]), (.chain [(6, 23)]), (.chain [(6, 23)]), (.chain [(6, 23), (6, 24)]), (.chain [(6, 23)]), .one⟩
theorem cell0699_ok : cell0699.check T = true := by decide +kernel

def cell0700 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (24601 / 3200 : ℚ), (39441 / 5120 : ℚ), (.chain [(6, 22)]), (.chain [(6, 23)]), (.chain [(6, 23)]), (.chain [(6, 22), (6, 23)]), (.chain [(6, 23), (6, 24)]), (.chain [(6, 23)]), .one⟩
theorem cell0700_ok : cell0700.check T = true := by decide +kernel

def cell0701 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (39441 / 5120 : ℚ), (98801 / 12800 : ℚ), (.chain [(6, 23)]), (.chain [(6, 23)]), (.chain [(6, 23)]), (.chain [(6, 23)]), (.chain [(6, 23), (6, 24)]), (.chain [(6, 23), (6, 24)]), .one⟩
theorem cell0701_ok : cell0701.check T = true := by decide +kernel

def cell0702 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (98801 / 12800 : ℚ), (197999 / 25600 : ℚ), (.chain [(6, 23)]), (.chain [(6, 23)]), (.chain [(6, 23)]), (.chain [(6, 23)]), (.chain [(6, 23), (6, 24)]), (.chain [(6, 23), (6, 24)]), .one⟩
theorem cell0702_ok : cell0702.check T = true := by decide +kernel

def cell0703 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (197999 / 25600 : ℚ), (49599 / 6400 : ℚ), (.chain [(6, 23)]), (.chain [(6, 23)]), (.chain [(6, 23)]), (.chain [(6, 23), (6, 24)]), (.chain [(6, 23), (6, 24)]), (.chain [(6, 23), (6, 24)]), .one⟩
theorem cell0703_ok : cell0703.check T = true := by decide +kernel

def cell0704 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (98801 / 12800 : ℚ), (197999 / 25600 : ℚ), (.chain [(6, 23)]), (.chain [(6, 24)]), (.chain [(6, 23)]), (.chain [(6, 23)]), (.chain [(6, 24)]), (.chain [(6, 23), (6, 24)]), .one⟩
theorem cell0704_ok : cell0704.check T = true := by decide +kernel

def cell0705 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (197999 / 25600 : ℚ), (49599 / 6400 : ℚ), (.chain [(6, 23)]), (.chain [(6, 24)]), (.chain [(6, 24)]), (.chain [(6, 23), (6, 24)]), (.chain [(6, 24), (6, 25)]), (.chain [(6, 24)]), .three⟩
theorem cell0705_ok : cell0705.check T = true := by decide +kernel

def cell0706 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (49599 / 6400 : ℚ), (198793 / 25600 : ℚ), (.chain [(6, 24)]), (.chain [(6, 24)]), (.chain [(6, 24)]), (.chain [(6, 24)]), (.chain [(6, 24), (6, 25)]), (.chain [(6, 24), (6, 25)]), .one⟩
theorem cell0706_ok : cell0706.check T = true := by decide +kernel

def cell0707 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (198793 / 25600 : ℚ), (19919 / 2560 : ℚ), (.chain [(6, 24)]), (.chain [(6, 24)]), (.chain [(6, 24)]), (.chain [(6, 24), (6, 25)]), (.chain [(6, 24), (6, 25)]), (.chain [(6, 24), (6, 25)]), .one⟩
theorem cell0707_ok : cell0707.check T = true := by decide +kernel

def cell0708 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (49599 / 6400 : ℚ), (198793 / 25600 : ℚ), (.chain [(6, 24)]), (.chain [(6, 24)]), (.chain [(6, 24)]), (.chain [(6, 24)]), (.chain [(6, 24), (6, 25)]), (.chain [(6, 24), (6, 25)]), .one⟩
theorem cell0708_ok : cell0708.check T = true := by decide +kernel

def cell0709 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (198793 / 25600 : ℚ), (19919 / 2560 : ℚ), (.chain [(6, 24)]), (.chain [(6, 25)]), (.chain [(6, 25)]), (.chain [(6, 24), (6, 25)]), (.chain [(6, 25), (6, 26)]), (.chain [(6, 25)]), .one⟩
theorem cell0709_ok : cell0709.check T = true := by decide +kernel

def cell0710 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (19919 / 2560 : ℚ), (199587 / 25600 : ℚ), (.chain [(6, 25)]), (.chain [(6, 25)]), (.chain [(6, 25)]), (.chain [(6, 25)]), (.chain [(6, 25), (6, 26)]), (.chain [(6, 25)]), .one⟩
theorem cell0710_ok : cell0710.check T = true := by decide +kernel

def cell0711 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (199587 / 25600 : ℚ), (12499 / 1600 : ℚ), (.chain [(6, 25)]), (.chain [(6, 25)]), (.chain [(6, 25)]), (.chain [(6, 25)]), (.chain [(6, 25), (6, 26)]), (.chain [(6, 25), (6, 26)]), .three⟩
theorem cell0711_ok : cell0711.check T = true := by decide +kernel

def cell0712 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (19919 / 2560 : ℚ), (199587 / 25600 : ℚ), (.chain [(6, 25)]), (.chain [(6, 25)]), (.chain [(6, 25)]), (.chain [(6, 25)]), (.chain [(6, 25), (6, 26)]), (.chain [(6, 25), (6, 26)]), .one⟩
theorem cell0712_ok : cell0712.check T = true := by decide +kernel

def cell0713 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (199587 / 25600 : ℚ), (12499 / 1600 : ℚ), (.chain [(6, 25)]), (.chain [(6, 26)]), (.chain [(6, 25)]), (.chain [(6, 25)]), (.chain [(6, 26)]), (.chain [(6, 25), (6, 26)]), .one⟩
theorem cell0713_ok : cell0713.check T = true := by decide +kernel

def cell0714 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (12499 / 1600 : ℚ), (200381 / 25600 : ℚ), (.chain [(6, 25)]), (.chain [(6, 25)]), (.chain [(6, 25)]), (.chain [(6, 25), (6, 26)]), (.chain [(6, 25), (6, 26)]), (.chain [(6, 25), (6, 26)]), .one⟩
theorem cell0714_ok : cell0714.check T = true := by decide +kernel

def cell0715 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (200381 / 25600 : ℚ), (100389 / 12800 : ℚ), (.chain [(6, 26)]), (.chain [(6, 26)]), (.chain [(6, 26)]), (.chain [(6, 26)]), (.chain [(6, 26), (6, 27)]), (.chain [(6, 26)]), .one⟩
theorem cell0715_ok : cell0715.check T = true := by decide +kernel

def cell0716 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (12499 / 1600 : ℚ), (100389 / 12800 : ℚ), (.chain [(6, 25)]), (.chain [(6, 26)]), (.chain [(6, 26)]), (.chain [(6, 25), (6, 26)]), (.chain [(6, 26), (6, 27)]), (.chain [(6, 26), (6, 27)]), .one⟩
theorem cell0716_ok : cell0716.check T = true := by decide +kernel

def cell0717 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (12499 / 1600 : ℚ), (100389 / 12800 : ℚ), (.chain [(6, 25)]), (.chain [(6, 26)]), (.chain [(6, 26)]), (.chain [(6, 25), (6, 26)]), (.chain [(6, 26), (6, 27)]), (.chain [(6, 26), (6, 27)]), .one⟩
theorem cell0717_ok : cell0717.check T = true := by decide +kernel

def cell0718 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (100389 / 12800 : ℚ), (8047 / 1024 : ℚ), (.chain [(6, 26)]), (.chain [(6, 26)]), (.chain [(6, 26)]), (.chain [(6, 26), (6, 27)]), (.chain [(6, 26), (6, 27)]), (.chain [(6, 26), (6, 27)]), .one⟩
theorem cell0718_ok : cell0718.check T = true := by decide +kernel

def cell0719 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (8047 / 1024 : ℚ), (50393 / 6400 : ℚ), (.chain [(6, 27)]), (.chain [(6, 27)]), (.chain [(6, 27)]), (.chain [(6, 27)]), (.chain [(6, 27)]), (.chain [(6, 27)]), .one⟩
theorem cell0719_ok : cell0719.check T = true := by decide +kernel

def cells17 : List CellW := [cell0680, cell0681, cell0682, cell0683, cell0684, cell0685, cell0686, cell0687, cell0688, cell0689, cell0690, cell0691, cell0692, cell0693, cell0694, cell0695, cell0696, cell0697, cell0698, cell0699, cell0700, cell0701, cell0702, cell0703, cell0704, cell0705, cell0706, cell0707, cell0708, cell0709, cell0710, cell0711, cell0712, cell0713, cell0714, cell0715, cell0716, cell0717, cell0718, cell0719]

theorem cells17_valid : ∀ w ∈ cells17, w.check T = true :=
  (forall_mem_cons_of cell0680_ok (forall_mem_cons_of cell0681_ok (forall_mem_cons_of cell0682_ok (forall_mem_cons_of cell0683_ok (forall_mem_cons_of cell0684_ok (forall_mem_cons_of cell0685_ok (forall_mem_cons_of cell0686_ok (forall_mem_cons_of cell0687_ok (forall_mem_cons_of cell0688_ok (forall_mem_cons_of cell0689_ok (forall_mem_cons_of cell0690_ok (forall_mem_cons_of cell0691_ok (forall_mem_cons_of cell0692_ok (forall_mem_cons_of cell0693_ok (forall_mem_cons_of cell0694_ok (forall_mem_cons_of cell0695_ok (forall_mem_cons_of cell0696_ok (forall_mem_cons_of cell0697_ok (forall_mem_cons_of cell0698_ok (forall_mem_cons_of cell0699_ok (forall_mem_cons_of cell0700_ok (forall_mem_cons_of cell0701_ok (forall_mem_cons_of cell0702_ok (forall_mem_cons_of cell0703_ok (forall_mem_cons_of cell0704_ok (forall_mem_cons_of cell0705_ok (forall_mem_cons_of cell0706_ok (forall_mem_cons_of cell0707_ok (forall_mem_cons_of cell0708_ok (forall_mem_cons_of cell0709_ok (forall_mem_cons_of cell0710_ok (forall_mem_cons_of cell0711_ok (forall_mem_cons_of cell0712_ok (forall_mem_cons_of cell0713_ok (forall_mem_cons_of cell0714_ok (forall_mem_cons_of cell0715_ok (forall_mem_cons_of cell0716_ok (forall_mem_cons_of cell0717_ok (forall_mem_cons_of cell0718_ok (forall_mem_cons_of cell0719_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


