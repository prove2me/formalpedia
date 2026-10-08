-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells18
-- name    : CK_CKLaneC_SAxis_Data_Cells18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T05:02:10.442996+00:00
-- url     : https://prove2.me/theorems/b753dd8f-32b4-4859-baa8-fe4264690f6c
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells18` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells18` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells18` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells18 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells18.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells18 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 18 (cells 720..759). -/

def cell0720 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (100389 / 12800 : ℚ), (50393 / 6400 : ℚ), (.chain [(6, 26)]), (.chain [(6, 27)]), (.chain [(6, 26)]), (.chain [(6, 26), (6, 27)]), (.chain [(6, 27), (6, 28)]), (.chain [(6, 26), (6, 27)]), .one⟩
theorem cell0720_ok : cell0720.check T = true := by decide +kernel

def cell0721 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (100389 / 12800 : ℚ), (50393 / 6400 : ℚ), (.chain [(6, 26)]), (.chain [(6, 27)]), (.chain [(6, 27)]), (.chain [(6, 26), (6, 27)]), (.chain [(6, 27), (6, 28)]), (.chain [(6, 27)]), .one⟩
theorem cell0721_ok : cell0721.check T = true := by decide +kernel

def cell0722 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (50393 / 6400 : ℚ), (201969 / 25600 : ℚ), (.chain [(6, 27)]), (.chain [(6, 27)]), (.chain [(6, 27)]), (.chain [(6, 27)]), (.chain [(6, 27), (6, 28)]), (.chain [(6, 27), (6, 28)]), .three⟩
theorem cell0722_ok : cell0722.check T = true := by decide +kernel

def cell0723 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (201969 / 25600 : ℚ), (101183 / 12800 : ℚ), (.chain [(6, 27)]), (.chain [(6, 27)]), (.chain [(6, 27)]), (.chain [(6, 27), (6, 28)]), (.chain [(6, 27), (6, 28)]), (.chain [(6, 27), (6, 28)]), .one⟩
theorem cell0723_ok : cell0723.check T = true := by decide +kernel

def cell0724 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (50393 / 6400 : ℚ), (201969 / 25600 : ℚ), (.chain [(6, 27)]), (.chain [(6, 27)]), (.chain [(6, 27)]), (.chain [(6, 27)]), (.chain [(6, 27), (6, 28)]), (.chain [(6, 27), (6, 28)]), .one⟩
theorem cell0724_ok : cell0724.check T = true := by decide +kernel

def cell0725 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (201969 / 25600 : ℚ), (101183 / 12800 : ℚ), (.chain [(6, 27)]), (.chain [(6, 28)]), (.chain [(6, 28)]), (.chain [(6, 27), (6, 28)]), (.chain [(6, 28), (6, 29)]), (.chain [(6, 28)]), .one⟩
theorem cell0725_ok : cell0725.check T = true := by decide +kernel

def cell0726 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (101183 / 12800 : ℚ), (202763 / 25600 : ℚ), (.chain [(6, 28)]), (.chain [(6, 28)]), (.chain [(6, 28)]), (.chain [(6, 28)]), (.chain [(6, 28), (6, 29)]), (.chain [(6, 28)]), .one⟩
theorem cell0726_ok : cell0726.check T = true := by decide +kernel

def cell0727 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (202763 / 25600 : ℚ), (5079 / 640 : ℚ), (.chain [(6, 28)]), (.chain [(6, 28)]), (.chain [(6, 28)]), (.chain [(6, 28), (6, 29)]), (.chain [(6, 28), (6, 29)]), (.chain [(6, 28), (6, 29)]), .one⟩
theorem cell0727_ok : cell0727.check T = true := by decide +kernel

def cell0728 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (101183 / 12800 : ℚ), (202763 / 25600 : ℚ), (.chain [(6, 28)]), (.chain [(6, 28)]), (.chain [(6, 28)]), (.chain [(6, 28)]), (.chain [(6, 28), (6, 29)]), (.chain [(6, 28), (6, 29)]), .one⟩
theorem cell0728_ok : cell0728.check T = true := by decide +kernel

def cell0729 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (202763 / 25600 : ℚ), (5079 / 640 : ℚ), (.chain [(6, 28)]), (.chain [(6, 29)]), (.chain [(6, 28)]), (.chain [(6, 28), (6, 29)]), (.chain [(6, 29), (6, 30)]), (.chain [(6, 28), (6, 29)]), .one⟩
theorem cell0729_ok : cell0729.check T = true := by decide +kernel

def cell0730 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (5079 / 640 : ℚ), (101977 / 12800 : ℚ), (.chain [(6, 29)]), (.chain [(6, 29)]), (.chain [(6, 29)]), (.chain [(6, 29)]), (.chain [(6, 29), (6, 30)]), (.chain [(6, 29)]), .one⟩
theorem cell0730_ok : cell0730.check T = true := by decide +kernel

def cell0731 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (5079 / 640 : ℚ), (101977 / 12800 : ℚ), (.chain [(6, 29)]), (.chain [(6, 29)]), (.chain [(6, 29)]), (.chain [(6, 29)]), (.chain [(6, 29), (6, 30)]), (.chain [(6, 29), (6, 30)]), .one⟩
theorem cell0731_ok : cell0731.check T = true := by decide +kernel

def cell0732 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (5079 / 640 : ℚ), (101977 / 12800 : ℚ), (.chain [(6, 29)]), (.chain [(6, 29)]), (.chain [(6, 29)]), (.chain [(6, 29)]), (.chain [(6, 29), (6, 30)]), (.chain [(6, 29), (6, 30)]), .one⟩
theorem cell0732_ok : cell0732.check T = true := by decide +kernel

def cell0733 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (5079 / 640 : ℚ), (101977 / 12800 : ℚ), (.chain [(6, 29)]), (.chain [(6, 29)]), (.chain [(6, 29)]), (.chain [(6, 29)]), (.chain [(6, 29), (6, 30)]), (.chain [(6, 29), (6, 30)]), .one⟩
theorem cell0733_ok : cell0733.check T = true := by decide +kernel

def cell0734 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (101977 / 12800 : ℚ), (204351 / 25600 : ℚ), (.chain [(6, 29)]), (.chain [(6, 29)]), (.chain [(6, 29)]), (.chain [(6, 29), (6, 30)]), (.chain [(6, 29), (6, 30)]), (.chain [(6, 29), (6, 30)]), .one⟩
theorem cell0734_ok : cell0734.check T = true := by decide +kernel

def cell0735 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (204351 / 25600 : ℚ), (51187 / 6400 : ℚ), (.chain [(6, 30)]), (.chain [(6, 30)]), (.chain [(6, 30)]), (.chain [(6, 30)]), (.chain [(6, 30), (6, 31)]), (.chain [(6, 30)]), .one⟩
theorem cell0735_ok : cell0735.check T = true := by decide +kernel

def cell0736 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (101977 / 12800 : ℚ), (204351 / 25600 : ℚ), (.chain [(6, 29)]), (.chain [(6, 30)]), (.chain [(6, 30)]), (.chain [(6, 29), (6, 30)]), (.chain [(6, 30), (6, 31)]), (.chain [(6, 30)]), .one⟩
theorem cell0736_ok : cell0736.check T = true := by decide +kernel

def cell0737 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (204351 / 25600 : ℚ), (51187 / 6400 : ℚ), (.chain [(6, 30)]), (.chain [(6, 30)]), (.chain [(6, 30)]), (.chain [(6, 30)]), (.chain [(6, 30), (6, 31)]), (.chain [(6, 30), (6, 31)]), .one⟩
theorem cell0737_ok : cell0737.check T = true := by decide +kernel

def cell0738 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (51187 / 6400 : ℚ), (102771 / 12800 : ℚ), (.chain [(6, 30)]), (.chain [(6, 30)]), (.chain [(6, 30)]), (.chain [(6, 30), (6, 31)]), (.chain [(6, 30), (6, 31)]), (.chain [(6, 30), (6, 31)]), .one⟩
theorem cell0738_ok : cell0738.check T = true := by decide +kernel

def cell0739 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (51187 / 6400 : ℚ), (102771 / 12800 : ℚ), (.chain [(6, 30)]), (.chain [(6, 30)]), (.chain [(6, 30)]), (.chain [(6, 30), (6, 31)]), (.chain [(6, 30), (6, 31)]), (.chain [(6, 30), (6, 31)]), .one⟩
theorem cell0739_ok : cell0739.check T = true := by decide +kernel

def cell0740 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (51187 / 6400 : ℚ), (41029 / 5120 : ℚ), (.chain [(6, 30)]), (.chain [(6, 31)]), (.chain [(6, 30)]), (.chain [(6, 30)]), (.chain [(6, 31)]), (.chain [(6, 30), (6, 31)]), .one⟩
theorem cell0740_ok : cell0740.check T = true := by decide +kernel

def cell0741 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (41029 / 5120 : ℚ), (102771 / 12800 : ℚ), (.chain [(6, 30)]), (.chain [(6, 31)]), (.chain [(6, 31)]), (.chain [(6, 30), (6, 31)]), (.chain [(6, 31), (7, 0)]), (.chain [(6, 31)]), .three⟩
theorem cell0741_ok : cell0741.check T = true := by decide +kernel

def cell0742 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (102771 / 12800 : ℚ), (205939 / 25600 : ℚ), (.chain [(6, 31)]), (.chain [(6, 31)]), (.chain [(6, 31)]), (.chain [(6, 31)]), (.chain [(6, 31), (7, 0)]), (.chain [(6, 31)]), .one⟩
theorem cell0742_ok : cell0742.check T = true := by decide +kernel

def cell0743 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (205939 / 25600 : ℚ), (403 / 50 : ℚ), (.chain [(6, 31)]), (.chain [(6, 31)]), (.chain [(6, 31)]), (.chain [(6, 31), (7, 0)]), (.chain [(6, 31), (7, 0)]), (.chain [(6, 31), (7, 0)]), .one⟩
theorem cell0743_ok : cell0743.check T = true := by decide +kernel

def cell0744 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (102771 / 12800 : ℚ), (205939 / 25600 : ℚ), (.chain [(6, 31)]), (.chain [(6, 31)]), (.chain [(6, 31)]), (.chain [(6, 31)]), (.chain [(6, 31), (7, 0)]), (.chain [(6, 31), (7, 0)]), .one⟩
theorem cell0744_ok : cell0744.check T = true := by decide +kernel

def cell0745 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (205939 / 25600 : ℚ), (403 / 50 : ℚ), (.chain [(6, 31)]), (.chain [(7, 0)]), (.chain [(6, 31)]), (.chain [(6, 31), (7, 0)]), (.chain [(7, 0), (7, 1)]), (.chain [(6, 31), (7, 0)]), .one⟩
theorem cell0745_ok : cell0745.check T = true := by decide +kernel

def cell0746 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (403 / 50 : ℚ), (206733 / 25600 : ℚ), (.chain [(7, 0)]), (.chain [(7, 0)]), (.chain [(7, 0)]), (.chain [(7, 0)]), (.chain [(7, 0), (7, 1)]), (.chain [(7, 0)]), .one⟩
theorem cell0746_ok : cell0746.check T = true := by decide +kernel

def cell0747 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (206733 / 25600 : ℚ), (20713 / 2560 : ℚ), (.chain [(7, 0)]), (.chain [(7, 0)]), (.chain [(7, 0)]), (.chain [(7, 0)]), (.chain [(7, 0), (7, 1)]), (.chain [(7, 0), (7, 1)]), .three⟩
theorem cell0747_ok : cell0747.check T = true := by decide +kernel

def cell0748 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (403 / 50 : ℚ), (20713 / 2560 : ℚ), (.chain [(7, 0)]), (.chain [(7, 0)]), (.chain [(7, 0)]), (.chain [(7, 0)]), (.chain [(7, 0), (7, 1)]), (.chain [(7, 0), (7, 1)]), .one⟩
theorem cell0748_ok : cell0748.check T = true := by decide +kernel

def cell0749 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (20713 / 2560 : ℚ), (207527 / 25600 : ℚ), (.chain [(7, 0)]), (.chain [(7, 0)]), (.chain [(7, 0)]), (.chain [(7, 0), (7, 1)]), (.chain [(7, 0), (7, 1)]), (.chain [(7, 0), (7, 1)]), .one⟩
theorem cell0749_ok : cell0749.check T = true := by decide +kernel

def cell0750 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (207527 / 25600 : ℚ), (51981 / 6400 : ℚ), (.chain [(7, 1)]), (.chain [(7, 1)]), (.chain [(7, 1)]), (.chain [(7, 1)]), (.chain [(7, 1), (7, 2)]), (.chain [(7, 1)]), .one⟩
theorem cell0750_ok : cell0750.check T = true := by decide +kernel

def cell0751 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (20713 / 2560 : ℚ), (51981 / 6400 : ℚ), (.chain [(7, 0)]), (.chain [(7, 1)]), (.chain [(7, 1)]), (.chain [(7, 0), (7, 1)]), (.chain [(7, 1), (7, 2)]), (.chain [(7, 1), (7, 2)]), .one⟩
theorem cell0751_ok : cell0751.check T = true := by decide +kernel

def cell0752 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (51981 / 6400 : ℚ), (208321 / 25600 : ℚ), (.chain [(7, 1)]), (.chain [(7, 1)]), (.chain [(7, 1)]), (.chain [(7, 1), (7, 2)]), (.chain [(7, 1), (7, 2)]), (.chain [(7, 1), (7, 2)]), .one⟩
theorem cell0752_ok : cell0752.check T = true := by decide +kernel

def cell0753 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (208321 / 25600 : ℚ), (104359 / 12800 : ℚ), (.chain [(7, 2)]), (.chain [(7, 2)]), (.chain [(7, 2)]), (.chain [(7, 2)]), (.chain [(7, 2)]), (.chain [(7, 2)]), .one⟩
theorem cell0753_ok : cell0753.check T = true := by decide +kernel

def cell0754 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (51981 / 6400 : ℚ), (104359 / 12800 : ℚ), (.chain [(7, 1)]), (.chain [(7, 2)]), (.chain [(7, 1)]), (.chain [(7, 1), (7, 2)]), (.chain [(7, 2), (7, 3)]), (.chain [(7, 1), (7, 2)]), .one⟩
theorem cell0754_ok : cell0754.check T = true := by decide +kernel

def cell0755 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (51981 / 6400 : ℚ), (104359 / 12800 : ℚ), (.chain [(7, 1)]), (.chain [(7, 2)]), (.chain [(7, 2)]), (.chain [(7, 1), (7, 2)]), (.chain [(7, 2), (7, 3)]), (.chain [(7, 2)]), .one⟩
theorem cell0755_ok : cell0755.check T = true := by decide +kernel

def cell0756 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (104359 / 12800 : ℚ), (26189 / 3200 : ℚ), (.chain [(7, 2)]), (.chain [(7, 2)]), (.chain [(7, 2)]), (.chain [(7, 2), (7, 3)]), (.chain [(7, 2), (7, 3)]), (.chain [(7, 2), (7, 3)]), .one⟩
theorem cell0756_ok : cell0756.check T = true := by decide +kernel

def cell0757 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (104359 / 12800 : ℚ), (26189 / 3200 : ℚ), (.chain [(7, 2)]), (.chain [(7, 2)]), (.chain [(7, 2)]), (.chain [(7, 2), (7, 3)]), (.chain [(7, 2), (7, 3)]), (.chain [(7, 2), (7, 3)]), .one⟩
theorem cell0757_ok : cell0757.check T = true := by decide +kernel

def cell0758 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (104359 / 12800 : ℚ), (41823 / 5120 : ℚ), (.chain [(7, 2)]), (.chain [(7, 2)]), (.chain [(7, 2)]), (.chain [(7, 2)]), (.chain [(7, 2), (7, 3)]), (.chain [(7, 2), (7, 3)]), .one⟩
theorem cell0758_ok : cell0758.check T = true := by decide +kernel

def cell0759 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (41823 / 5120 : ℚ), (26189 / 3200 : ℚ), (.chain [(7, 2)]), (.chain [(7, 3)]), (.chain [(7, 3)]), (.chain [(7, 2), (7, 3)]), (.chain [(7, 3), (7, 4)]), (.chain [(7, 3)]), .one⟩
theorem cell0759_ok : cell0759.check T = true := by decide +kernel

def cells18 : List CellW := [cell0720, cell0721, cell0722, cell0723, cell0724, cell0725, cell0726, cell0727, cell0728, cell0729, cell0730, cell0731, cell0732, cell0733, cell0734, cell0735, cell0736, cell0737, cell0738, cell0739, cell0740, cell0741, cell0742, cell0743, cell0744, cell0745, cell0746, cell0747, cell0748, cell0749, cell0750, cell0751, cell0752, cell0753, cell0754, cell0755, cell0756, cell0757, cell0758, cell0759]

theorem cells18_valid : ∀ w ∈ cells18, w.check T = true :=
  (forall_mem_cons_of cell0720_ok (forall_mem_cons_of cell0721_ok (forall_mem_cons_of cell0722_ok (forall_mem_cons_of cell0723_ok (forall_mem_cons_of cell0724_ok (forall_mem_cons_of cell0725_ok (forall_mem_cons_of cell0726_ok (forall_mem_cons_of cell0727_ok (forall_mem_cons_of cell0728_ok (forall_mem_cons_of cell0729_ok (forall_mem_cons_of cell0730_ok (forall_mem_cons_of cell0731_ok (forall_mem_cons_of cell0732_ok (forall_mem_cons_of cell0733_ok (forall_mem_cons_of cell0734_ok (forall_mem_cons_of cell0735_ok (forall_mem_cons_of cell0736_ok (forall_mem_cons_of cell0737_ok (forall_mem_cons_of cell0738_ok (forall_mem_cons_of cell0739_ok (forall_mem_cons_of cell0740_ok (forall_mem_cons_of cell0741_ok (forall_mem_cons_of cell0742_ok (forall_mem_cons_of cell0743_ok (forall_mem_cons_of cell0744_ok (forall_mem_cons_of cell0745_ok (forall_mem_cons_of cell0746_ok (forall_mem_cons_of cell0747_ok (forall_mem_cons_of cell0748_ok (forall_mem_cons_of cell0749_ok (forall_mem_cons_of cell0750_ok (forall_mem_cons_of cell0751_ok (forall_mem_cons_of cell0752_ok (forall_mem_cons_of cell0753_ok (forall_mem_cons_of cell0754_ok (forall_mem_cons_of cell0755_ok (forall_mem_cons_of cell0756_ok (forall_mem_cons_of cell0757_ok (forall_mem_cons_of cell0758_ok (forall_mem_cons_of cell0759_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


