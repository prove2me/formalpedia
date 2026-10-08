-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells16
-- name    : CK_CKLaneC_SAxis_Data_Cells16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T05:59:38.725218+00:00
-- url     : https://prove2.me/theorems/59b2cd36-e512-4f3e-b45d-6a3b5f0d1cb8
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells16` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells16` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells16` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells16 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells16.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells16 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 16 (cells 640..679). -/

def cell0640 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (92449 / 12800 : ℚ), (37059 / 5120 : ℚ), (.chain [(6, 11)]), (.chain [(6, 11)]), (.chain [(6, 11)]), (.chain [(6, 11)]), (.chain [(6, 11), (6, 12)]), (.chain [(6, 11), (6, 12)]), .one⟩
theorem cell0640_ok : cell0640.check T = true := by decide +kernel

def cell0641 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (37059 / 5120 : ℚ), (46423 / 6400 : ℚ), (.chain [(6, 11)]), (.chain [(6, 12)]), (.chain [(6, 11)]), (.chain [(6, 11)]), (.chain [(6, 12)]), (.chain [(6, 11), (6, 12)]), .one⟩
theorem cell0641_ok : cell0641.check T = true := by decide +kernel

def cell0642 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (46423 / 6400 : ℚ), (186089 / 25600 : ℚ), (.chain [(6, 11)]), (.chain [(6, 11)]), (.chain [(6, 11)]), (.chain [(6, 11), (6, 12)]), (.chain [(6, 11), (6, 12)]), (.chain [(6, 11), (6, 12)]), .one⟩
theorem cell0642_ok : cell0642.check T = true := by decide +kernel

def cell0643 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (186089 / 25600 : ℚ), (93243 / 12800 : ℚ), (.chain [(6, 12)]), (.chain [(6, 12)]), (.chain [(6, 12)]), (.chain [(6, 12)]), (.chain [(6, 12), (6, 13)]), (.chain [(6, 12)]), .one⟩
theorem cell0643_ok : cell0643.check T = true := by decide +kernel

def cell0644 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (46423 / 6400 : ℚ), (93243 / 12800 : ℚ), (.chain [(6, 11)]), (.chain [(6, 12)]), (.chain [(6, 12)]), (.chain [(6, 11), (6, 12)]), (.chain [(6, 12), (6, 13)]), (.chain [(6, 12), (6, 13)]), .one⟩
theorem cell0644_ok : cell0644.check T = true := by decide +kernel

def cell0645 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (46423 / 6400 : ℚ), (93243 / 12800 : ℚ), (.chain [(6, 11)]), (.chain [(6, 12)]), (.chain [(6, 12)]), (.chain [(6, 11), (6, 12)]), (.chain [(6, 12), (6, 13)]), (.chain [(6, 12), (6, 13)]), .one⟩
theorem cell0645_ok : cell0645.check T = true := by decide +kernel

def cell0646 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (93243 / 12800 : ℚ), (186883 / 25600 : ℚ), (.chain [(6, 12)]), (.chain [(6, 12)]), (.chain [(6, 12)]), (.chain [(6, 12), (6, 13)]), (.chain [(6, 12), (6, 13)]), (.chain [(6, 12), (6, 13)]), .one⟩
theorem cell0646_ok : cell0646.check T = true := by decide +kernel

def cell0647 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (186883 / 25600 : ℚ), (2341 / 320 : ℚ), (.chain [(6, 13)]), (.chain [(6, 13)]), (.chain [(6, 13)]), (.chain [(6, 13)]), (.chain [(6, 13), (6, 14)]), (.chain [(6, 13)]), .one⟩
theorem cell0647_ok : cell0647.check T = true := by decide +kernel

def cell0648 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (93243 / 12800 : ℚ), (186883 / 25600 : ℚ), (.chain [(6, 12)]), (.chain [(6, 13)]), (.chain [(6, 12)]), (.chain [(6, 12), (6, 13)]), (.chain [(6, 13), (6, 14)]), (.chain [(6, 12), (6, 13)]), .one⟩
theorem cell0648_ok : cell0648.check T = true := by decide +kernel

def cell0649 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (186883 / 25600 : ℚ), (2341 / 320 : ℚ), (.chain [(6, 13)]), (.chain [(6, 13)]), (.chain [(6, 13)]), (.chain [(6, 13)]), (.chain [(6, 13), (6, 14)]), (.chain [(6, 13), (6, 14)]), .one⟩
theorem cell0649_ok : cell0649.check T = true := by decide +kernel

def cell0650 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (2341 / 320 : ℚ), (187677 / 25600 : ℚ), (.chain [(6, 13)]), (.chain [(6, 13)]), (.chain [(6, 13)]), (.chain [(6, 13)]), (.chain [(6, 13), (6, 14)]), (.chain [(6, 13), (6, 14)]), .three⟩
theorem cell0650_ok : cell0650.check T = true := by decide +kernel

def cell0651 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (187677 / 25600 : ℚ), (94037 / 12800 : ℚ), (.chain [(6, 13)]), (.chain [(6, 13)]), (.chain [(6, 13)]), (.chain [(6, 13), (6, 14)]), (.chain [(6, 13), (6, 14)]), (.chain [(6, 13), (6, 14)]), .one⟩
theorem cell0651_ok : cell0651.check T = true := by decide +kernel

def cell0652 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (2341 / 320 : ℚ), (187677 / 25600 : ℚ), (.chain [(6, 13)]), (.chain [(6, 14)]), (.chain [(6, 13)]), (.chain [(6, 13)]), (.chain [(6, 14)]), (.chain [(6, 13), (6, 14)]), .one⟩
theorem cell0652_ok : cell0652.check T = true := by decide +kernel

def cell0653 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (187677 / 25600 : ℚ), (94037 / 12800 : ℚ), (.chain [(6, 13)]), (.chain [(6, 14)]), (.chain [(6, 14)]), (.chain [(6, 13), (6, 14)]), (.chain [(6, 14), (6, 15)]), (.chain [(6, 14)]), .one⟩
theorem cell0653_ok : cell0653.check T = true := by decide +kernel

def cell0654 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (94037 / 12800 : ℚ), (188471 / 25600 : ℚ), (.chain [(6, 14)]), (.chain [(6, 14)]), (.chain [(6, 14)]), (.chain [(6, 14)]), (.chain [(6, 14), (6, 15)]), (.chain [(6, 14)]), .one⟩
theorem cell0654_ok : cell0654.check T = true := by decide +kernel

def cell0655 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (188471 / 25600 : ℚ), (47217 / 6400 : ℚ), (.chain [(6, 14)]), (.chain [(6, 14)]), (.chain [(6, 14)]), (.chain [(6, 14), (6, 15)]), (.chain [(6, 14), (6, 15)]), (.chain [(6, 14), (6, 15)]), .one⟩
theorem cell0655_ok : cell0655.check T = true := by decide +kernel

def cell0656 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (94037 / 12800 : ℚ), (188471 / 25600 : ℚ), (.chain [(6, 14)]), (.chain [(6, 14)]), (.chain [(6, 14)]), (.chain [(6, 14)]), (.chain [(6, 14), (6, 15)]), (.chain [(6, 14), (6, 15)]), .one⟩
theorem cell0656_ok : cell0656.check T = true := by decide +kernel

def cell0657 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (188471 / 25600 : ℚ), (47217 / 6400 : ℚ), (.chain [(6, 14)]), (.chain [(6, 15)]), (.chain [(6, 14)]), (.chain [(6, 14), (6, 15)]), (.chain [(6, 15), (6, 16)]), (.chain [(6, 14), (6, 15)]), .one⟩
theorem cell0657_ok : cell0657.check T = true := by decide +kernel

def cell0658 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (47217 / 6400 : ℚ), (37853 / 5120 : ℚ), (.chain [(6, 15)]), (.chain [(6, 15)]), (.chain [(6, 15)]), (.chain [(6, 15)]), (.chain [(6, 15)]), (.chain [(6, 15)]), .one⟩
theorem cell0658_ok : cell0658.check T = true := by decide +kernel

def cell0659 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (37853 / 5120 : ℚ), (94831 / 12800 : ℚ), (.chain [(6, 15)]), (.chain [(6, 15)]), (.chain [(6, 15)]), (.chain [(6, 15)]), (.chain [(6, 15), (6, 16)]), (.chain [(6, 15), (6, 16)]), .three⟩
theorem cell0659_ok : cell0659.check T = true := by decide +kernel

def cell0660 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (47217 / 6400 : ℚ), (94831 / 12800 : ℚ), (.chain [(6, 15)]), (.chain [(6, 15)]), (.chain [(6, 15)]), (.chain [(6, 15)]), (.chain [(6, 15), (6, 16)]), (.chain [(6, 15), (6, 16)]), .one⟩
theorem cell0660_ok : cell0660.check T = true := by decide +kernel

def cell0661 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (47217 / 6400 : ℚ), (94831 / 12800 : ℚ), (.chain [(6, 15)]), (.chain [(6, 15)]), (.chain [(6, 15)]), (.chain [(6, 15)]), (.chain [(6, 15), (6, 16)]), (.chain [(6, 15), (6, 16)]), .one⟩
theorem cell0661_ok : cell0661.check T = true := by decide +kernel

def cell0662 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (94831 / 12800 : ℚ), (190059 / 25600 : ℚ), (.chain [(6, 15)]), (.chain [(6, 15)]), (.chain [(6, 15)]), (.chain [(6, 15), (6, 16)]), (.chain [(6, 15), (6, 16)]), (.chain [(6, 15), (6, 16)]), .one⟩
theorem cell0662_ok : cell0662.check T = true := by decide +kernel

def cell0663 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (190059 / 25600 : ℚ), (23807 / 3200 : ℚ), (.chain [(6, 16)]), (.chain [(6, 16)]), (.chain [(6, 16)]), (.chain [(6, 16)]), (.chain [(6, 16), (6, 17)]), (.chain [(6, 16)]), .one⟩
theorem cell0663_ok : cell0663.check T = true := by decide +kernel

def cell0664 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (94831 / 12800 : ℚ), (190059 / 25600 : ℚ), (.chain [(6, 15)]), (.chain [(6, 16)]), (.chain [(6, 16)]), (.chain [(6, 15), (6, 16)]), (.chain [(6, 16), (6, 17)]), (.chain [(6, 16)]), .one⟩
theorem cell0664_ok : cell0664.check T = true := by decide +kernel

def cell0665 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (190059 / 25600 : ℚ), (23807 / 3200 : ℚ), (.chain [(6, 16)]), (.chain [(6, 16)]), (.chain [(6, 16)]), (.chain [(6, 16)]), (.chain [(6, 16), (6, 17)]), (.chain [(6, 16), (6, 17)]), .one⟩
theorem cell0665_ok : cell0665.check T = true := by decide +kernel

def cell0666 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (23807 / 3200 : ℚ), (190853 / 25600 : ℚ), (.chain [(6, 16)]), (.chain [(6, 16)]), (.chain [(6, 16)]), (.chain [(6, 16), (6, 17)]), (.chain [(6, 16), (6, 17)]), (.chain [(6, 16), (6, 17)]), .one⟩
theorem cell0666_ok : cell0666.check T = true := by decide +kernel

def cell0667 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (190853 / 25600 : ℚ), (3825 / 512 : ℚ), (.chain [(6, 17)]), (.chain [(6, 17)]), (.chain [(6, 17)]), (.chain [(6, 17)]), (.chain [(6, 17)]), (.chain [(6, 17)]), .one⟩
theorem cell0667_ok : cell0667.check T = true := by decide +kernel

def cell0668 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (23807 / 3200 : ℚ), (190853 / 25600 : ℚ), (.chain [(6, 16)]), (.chain [(6, 17)]), (.chain [(6, 16)]), (.chain [(6, 16), (6, 17)]), (.chain [(6, 17), (6, 18)]), (.chain [(6, 16), (6, 17)]), .one⟩
theorem cell0668_ok : cell0668.check T = true := by decide +kernel

def cell0669 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (190853 / 25600 : ℚ), (3825 / 512 : ℚ), (.chain [(6, 17)]), (.chain [(6, 17)]), (.chain [(6, 17)]), (.chain [(6, 17)]), (.chain [(6, 17), (6, 18)]), (.chain [(6, 17)]), .three⟩
theorem cell0669_ok : cell0669.check T = true := by decide +kernel

def cell0670 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (3825 / 512 : ℚ), (191647 / 25600 : ℚ), (.chain [(6, 17)]), (.chain [(6, 17)]), (.chain [(6, 17)]), (.chain [(6, 17)]), (.chain [(6, 17), (6, 18)]), (.chain [(6, 17), (6, 18)]), .one⟩
theorem cell0670_ok : cell0670.check T = true := by decide +kernel

def cell0671 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (191647 / 25600 : ℚ), (48011 / 6400 : ℚ), (.chain [(6, 17)]), (.chain [(6, 17)]), (.chain [(6, 17)]), (.chain [(6, 17), (6, 18)]), (.chain [(6, 17), (6, 18)]), (.chain [(6, 17), (6, 18)]), .one⟩
theorem cell0671_ok : cell0671.check T = true := by decide +kernel

def cell0672 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (3825 / 512 : ℚ), (191647 / 25600 : ℚ), (.chain [(6, 17)]), (.chain [(6, 17)]), (.chain [(6, 17)]), (.chain [(6, 17)]), (.chain [(6, 17), (6, 18)]), (.chain [(6, 17), (6, 18)]), .one⟩
theorem cell0672_ok : cell0672.check T = true := by decide +kernel

def cell0673 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (191647 / 25600 : ℚ), (48011 / 6400 : ℚ), (.chain [(6, 17)]), (.chain [(6, 18)]), (.chain [(6, 18)]), (.chain [(6, 17), (6, 18)]), (.chain [(6, 18), (6, 19)]), (.chain [(6, 18)]), .one⟩
theorem cell0673_ok : cell0673.check T = true := by decide +kernel

def cell0674 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (48011 / 6400 : ℚ), (96419 / 12800 : ℚ), (.chain [(6, 18)]), (.chain [(6, 18)]), (.chain [(6, 18)]), (.chain [(6, 18)]), (.chain [(6, 18), (6, 19)]), (.chain [(6, 18), (6, 19)]), .one⟩
theorem cell0674_ok : cell0674.check T = true := by decide +kernel

def cell0675 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (48011 / 6400 : ℚ), (96419 / 12800 : ℚ), (.chain [(6, 18)]), (.chain [(6, 18)]), (.chain [(6, 18)]), (.chain [(6, 18)]), (.chain [(6, 18), (6, 19)]), (.chain [(6, 18), (6, 19)]), .one⟩
theorem cell0675_ok : cell0675.check T = true := by decide +kernel

def cell0676 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (48011 / 6400 : ℚ), (192441 / 25600 : ℚ), (.chain [(6, 18)]), (.chain [(6, 18)]), (.chain [(6, 18)]), (.chain [(6, 18)]), (.chain [(6, 18), (6, 19)]), (.chain [(6, 18), (6, 19)]), .one⟩
theorem cell0676_ok : cell0676.check T = true := by decide +kernel

def cell0677 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (192441 / 25600 : ℚ), (96419 / 12800 : ℚ), (.chain [(6, 18)]), (.chain [(6, 19)]), (.chain [(6, 18)]), (.chain [(6, 18)]), (.chain [(6, 19)]), (.chain [(6, 18), (6, 19)]), .one⟩
theorem cell0677_ok : cell0677.check T = true := by decide +kernel

def cell0678 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (96419 / 12800 : ℚ), (38647 / 5120 : ℚ), (.chain [(6, 18)]), (.chain [(6, 18)]), (.chain [(6, 18)]), (.chain [(6, 18), (6, 19)]), (.chain [(6, 18), (6, 19)]), (.chain [(6, 18), (6, 19)]), .one⟩
theorem cell0678_ok : cell0678.check T = true := by decide +kernel

def cell0679 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (38647 / 5120 : ℚ), (6051 / 800 : ℚ), (.chain [(6, 19)]), (.chain [(6, 19)]), (.chain [(6, 19)]), (.chain [(6, 19)]), (.chain [(6, 19), (6, 20)]), (.chain [(6, 19)]), .one⟩
theorem cell0679_ok : cell0679.check T = true := by decide +kernel

def cells16 : List CellW := [cell0640, cell0641, cell0642, cell0643, cell0644, cell0645, cell0646, cell0647, cell0648, cell0649, cell0650, cell0651, cell0652, cell0653, cell0654, cell0655, cell0656, cell0657, cell0658, cell0659, cell0660, cell0661, cell0662, cell0663, cell0664, cell0665, cell0666, cell0667, cell0668, cell0669, cell0670, cell0671, cell0672, cell0673, cell0674, cell0675, cell0676, cell0677, cell0678, cell0679]

theorem cells16_valid : ∀ w ∈ cells16, w.check T = true :=
  (forall_mem_cons_of cell0640_ok (forall_mem_cons_of cell0641_ok (forall_mem_cons_of cell0642_ok (forall_mem_cons_of cell0643_ok (forall_mem_cons_of cell0644_ok (forall_mem_cons_of cell0645_ok (forall_mem_cons_of cell0646_ok (forall_mem_cons_of cell0647_ok (forall_mem_cons_of cell0648_ok (forall_mem_cons_of cell0649_ok (forall_mem_cons_of cell0650_ok (forall_mem_cons_of cell0651_ok (forall_mem_cons_of cell0652_ok (forall_mem_cons_of cell0653_ok (forall_mem_cons_of cell0654_ok (forall_mem_cons_of cell0655_ok (forall_mem_cons_of cell0656_ok (forall_mem_cons_of cell0657_ok (forall_mem_cons_of cell0658_ok (forall_mem_cons_of cell0659_ok (forall_mem_cons_of cell0660_ok (forall_mem_cons_of cell0661_ok (forall_mem_cons_of cell0662_ok (forall_mem_cons_of cell0663_ok (forall_mem_cons_of cell0664_ok (forall_mem_cons_of cell0665_ok (forall_mem_cons_of cell0666_ok (forall_mem_cons_of cell0667_ok (forall_mem_cons_of cell0668_ok (forall_mem_cons_of cell0669_ok (forall_mem_cons_of cell0670_ok (forall_mem_cons_of cell0671_ok (forall_mem_cons_of cell0672_ok (forall_mem_cons_of cell0673_ok (forall_mem_cons_of cell0674_ok (forall_mem_cons_of cell0675_ok (forall_mem_cons_of cell0676_ok (forall_mem_cons_of cell0677_ok (forall_mem_cons_of cell0678_ok (forall_mem_cons_of cell0679_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


