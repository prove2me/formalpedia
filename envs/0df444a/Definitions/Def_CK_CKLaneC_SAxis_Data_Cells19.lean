-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells19
-- name    : CK_CKLaneC_SAxis_Data_Cells19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T05:04:29.238521+00:00
-- url     : https://prove2.me/theorems/dc447f47-6500-4d3b-aef5-a38788481f5d
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells19` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells19` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells19` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells19 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells19.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells19 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 19 (cells 760..799). -/

def cell0760 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (26189 / 3200 : ℚ), (209909 / 25600 : ℚ), (.chain [(7, 3)]), (.chain [(7, 3)]), (.chain [(7, 3)]), (.chain [(7, 3)]), (.chain [(7, 3), (7, 4)]), (.chain [(7, 3)]), .one⟩
theorem cell0760_ok : cell0760.check T = true := by decide +kernel

def cell0761 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (209909 / 25600 : ℚ), (105153 / 12800 : ℚ), (.chain [(7, 3)]), (.chain [(7, 3)]), (.chain [(7, 3)]), (.chain [(7, 3), (7, 4)]), (.chain [(7, 3), (7, 4)]), (.chain [(7, 3), (7, 4)]), .one⟩
theorem cell0761_ok : cell0761.check T = true := by decide +kernel

def cell0762 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (26189 / 3200 : ℚ), (105153 / 12800 : ℚ), (.chain [(7, 3)]), (.chain [(7, 3)]), (.chain [(7, 3)]), (.chain [(7, 3), (7, 4)]), (.chain [(7, 3), (7, 4), (7, 5)]), (.chain [(7, 3), (7, 4)]), .one⟩
theorem cell0762_ok : cell0762.check T = true := by decide +kernel

def cell0763 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (105153 / 12800 : ℚ), (210703 / 25600 : ℚ), (.chain [(7, 4)]), (.chain [(7, 4)]), (.chain [(7, 4)]), (.chain [(7, 4)]), (.chain [(7, 4)]), (.chain [(7, 4)]), .one⟩
theorem cell0763_ok : cell0763.check T = true := by decide +kernel

def cell0764 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (210703 / 25600 : ℚ), (2111 / 256 : ℚ), (.chain [(7, 4)]), (.chain [(7, 4)]), (.chain [(7, 4)]), (.chain [(7, 4)]), (.chain [(7, 4), (7, 5)]), (.chain [(7, 4), (7, 5)]), .one⟩
theorem cell0764_ok : cell0764.check T = true := by decide +kernel

def cell0765 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (105153 / 12800 : ℚ), (2111 / 256 : ℚ), (.chain [(7, 4)]), (.chain [(7, 4)]), (.chain [(7, 4)]), (.chain [(7, 4)]), (.chain [(7, 4), (7, 5)]), (.chain [(7, 4), (7, 5)]), .one⟩
theorem cell0765_ok : cell0765.check T = true := by decide +kernel

def cell0766 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (2111 / 256 : ℚ), (211497 / 25600 : ℚ), (.chain [(7, 4)]), (.chain [(7, 4)]), (.chain [(7, 4)]), (.chain [(7, 4), (7, 5)]), (.chain [(7, 4), (7, 5)]), (.chain [(7, 4), (7, 5)]), .one⟩
theorem cell0766_ok : cell0766.check T = true := by decide +kernel

def cell0767 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (211497 / 25600 : ℚ), (105947 / 12800 : ℚ), (.chain [(7, 5)]), (.chain [(7, 5)]), (.chain [(7, 5)]), (.chain [(7, 5)]), (.chain [(7, 5), (7, 6)]), (.chain [(7, 5)]), .one⟩
theorem cell0767_ok : cell0767.check T = true := by decide +kernel

def cell0768 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (2111 / 256 : ℚ), (105947 / 12800 : ℚ), (.chain [(7, 4)]), (.chain [(7, 5)]), (.chain [(7, 5)]), (.chain [(7, 4), (7, 5)]), (.chain [(7, 5), (7, 6)]), (.chain [(7, 5), (7, 6)]), .one⟩
theorem cell0768_ok : cell0768.check T = true := by decide +kernel

def cell0769 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (105947 / 12800 : ℚ), (13293 / 1600 : ℚ), (.chain [(7, 5)]), (.chain [(7, 5)]), (.chain [(7, 5)]), (.chain [(7, 5), (7, 6)]), (.chain [(7, 5), (7, 6)]), (.chain [(7, 5), (7, 6)]), .one⟩
theorem cell0769_ok : cell0769.check T = true := by decide +kernel

def cell0770 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (105947 / 12800 : ℚ), (13293 / 1600 : ℚ), (.chain [(7, 5)]), (.chain [(7, 6)]), (.chain [(7, 5)]), (.chain [(7, 5), (7, 6)]), (.chain [(7, 6), (7, 7)]), (.chain [(7, 5), (7, 6)]), .one⟩
theorem cell0770_ok : cell0770.check T = true := by decide +kernel

def cell0771 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (105947 / 12800 : ℚ), (13293 / 1600 : ℚ), (.chain [(7, 5)]), (.chain [(7, 6)]), (.chain [(7, 5)]), (.chain [(7, 5), (7, 6)]), (.chain [(7, 6), (7, 7)]), (.chain [(7, 5), (7, 6)]), .one⟩
theorem cell0771_ok : cell0771.check T = true := by decide +kernel

def cell0772 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (13293 / 1600 : ℚ), (106741 / 12800 : ℚ), (.chain [(7, 6)]), (.chain [(7, 6)]), (.chain [(7, 6)]), (.chain [(7, 6), (7, 7)]), (.chain [(7, 6), (7, 7)]), (.chain [(7, 6), (7, 7)]), .one⟩
theorem cell0772_ok : cell0772.check T = true := by decide +kernel

def cell0773 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (13293 / 1600 : ℚ), (42617 / 5120 : ℚ), (.chain [(7, 6)]), (.chain [(7, 6)]), (.chain [(7, 6)]), (.chain [(7, 6)]), (.chain [(7, 6), (7, 7)]), (.chain [(7, 6), (7, 7)]), .one⟩
theorem cell0773_ok : cell0773.check T = true := by decide +kernel

def cell0774 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (42617 / 5120 : ℚ), (106741 / 12800 : ℚ), (.chain [(7, 6)]), (.chain [(7, 7)]), (.chain [(7, 6)]), (.chain [(7, 6), (7, 7)]), (.chain [(7, 7), (7, 8)]), (.chain [(7, 6), (7, 7)]), .one⟩
theorem cell0774_ok : cell0774.check T = true := by decide +kernel

def cell0775 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (106741 / 12800 : ℚ), (213879 / 25600 : ℚ), (.chain [(7, 7)]), (.chain [(7, 7)]), (.chain [(7, 7)]), (.chain [(7, 7)]), (.chain [(7, 7)]), (.chain [(7, 7)]), .one⟩
theorem cell0775_ok : cell0775.check T = true := by decide +kernel

def cell0776 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (213879 / 25600 : ℚ), (53569 / 6400 : ℚ), (.chain [(7, 7)]), (.chain [(7, 7)]), (.chain [(7, 7)]), (.chain [(7, 7)]), (.chain [(7, 7), (7, 8)]), (.chain [(7, 7), (7, 8)]), .three⟩
theorem cell0776_ok : cell0776.check T = true := by decide +kernel

def cell0777 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (106741 / 12800 : ℚ), (53569 / 6400 : ℚ), (.chain [(7, 7)]), (.chain [(7, 7)]), (.chain [(7, 7)]), (.chain [(7, 7)]), (.chain [(7, 7), (7, 8)]), (.chain [(7, 7), (7, 8)]), .one⟩
theorem cell0777_ok : cell0777.check T = true := by decide +kernel

def cell0778 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (53569 / 6400 : ℚ), (214673 / 25600 : ℚ), (.chain [(7, 7)]), (.chain [(7, 7)]), (.chain [(7, 7)]), (.chain [(7, 7), (7, 8)]), (.chain [(7, 7), (7, 8)]), (.chain [(7, 7), (7, 8)]), .one⟩
theorem cell0778_ok : cell0778.check T = true := by decide +kernel

def cell0779 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (214673 / 25600 : ℚ), (21507 / 2560 : ℚ), (.chain [(7, 8)]), (.chain [(7, 8)]), (.chain [(7, 8)]), (.chain [(7, 8)]), (.chain [(7, 8), (7, 9)]), (.chain [(7, 8)]), .one⟩
theorem cell0779_ok : cell0779.check T = true := by decide +kernel

def cell0780 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (53569 / 6400 : ℚ), (21507 / 2560 : ℚ), (.chain [(7, 7)]), (.chain [(7, 8)]), (.chain [(7, 8)]), (.chain [(7, 7), (7, 8)]), (.chain [(7, 8), (7, 9)]), (.chain [(7, 8), (7, 9)]), .one⟩
theorem cell0780_ok : cell0780.check T = true := by decide +kernel

def cell0781 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (21507 / 2560 : ℚ), (26983 / 3200 : ℚ), (.chain [(7, 8)]), (.chain [(7, 8)]), (.chain [(7, 8)]), (.chain [(7, 8), (7, 9)]), (.chain [(7, 8), (7, 9)]), (.chain [(7, 8), (7, 9)]), .one⟩
theorem cell0781_ok : cell0781.check T = true := by decide +kernel

def cell0782 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (21507 / 2560 : ℚ), (26983 / 3200 : ℚ), (.chain [(7, 8)]), (.chain [(7, 9)]), (.chain [(7, 8)]), (.chain [(7, 8), (7, 9)]), (.chain [(7, 9), (7, 10)]), (.chain [(7, 8), (7, 9)]), .one⟩
theorem cell0782_ok : cell0782.check T = true := by decide +kernel

def cell0783 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (26983 / 3200 : ℚ), (108329 / 12800 : ℚ), (.chain [(7, 9)]), (.chain [(7, 9)]), (.chain [(7, 9)]), (.chain [(7, 9), (7, 10)]), (.chain [(7, 9), (7, 10)]), (.chain [(7, 9), (7, 10)]), .one⟩
theorem cell0783_ok : cell0783.check T = true := by decide +kernel

def cell0784 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (26983 / 3200 : ℚ), (216261 / 25600 : ℚ), (.chain [(7, 9)]), (.chain [(7, 9)]), (.chain [(7, 9)]), (.chain [(7, 9)]), (.chain [(7, 9), (7, 10)]), (.chain [(7, 9), (7, 10)]), .one⟩
theorem cell0784_ok : cell0784.check T = true := by decide +kernel

def cell0785 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (216261 / 25600 : ℚ), (108329 / 12800 : ℚ), (.chain [(7, 9)]), (.chain [(7, 10)]), (.chain [(7, 10)]), (.chain [(7, 9), (7, 10)]), (.chain [(7, 10), (7, 11)]), (.chain [(7, 10)]), .one⟩
theorem cell0785_ok : cell0785.check T = true := by decide +kernel

def cell0786 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (108329 / 12800 : ℚ), (54363 / 6400 : ℚ), (.chain [(7, 10)]), (.chain [(7, 10)]), (.chain [(7, 10)]), (.chain [(7, 10)]), (.chain [(7, 10), (7, 11)]), (.chain [(7, 10), (7, 11)]), .one⟩
theorem cell0786_ok : cell0786.check T = true := by decide +kernel

def cell0787 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (108329 / 12800 : ℚ), (54363 / 6400 : ℚ), (.chain [(7, 10)]), (.chain [(7, 10)]), (.chain [(7, 10)]), (.chain [(7, 10)]), (.chain [(7, 10), (7, 11)]), (.chain [(7, 10), (7, 11)]), .one⟩
theorem cell0787_ok : cell0787.check T = true := by decide +kernel

def cell0788 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (54363 / 6400 : ℚ), (217849 / 25600 : ℚ), (.chain [(7, 10)]), (.chain [(7, 10)]), (.chain [(7, 10)]), (.chain [(7, 10), (7, 11)]), (.chain [(7, 10), (7, 11)]), (.chain [(7, 10), (7, 11)]), .one⟩
theorem cell0788_ok : cell0788.check T = true := by decide +kernel

def cell0789 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (217849 / 25600 : ℚ), (109123 / 12800 : ℚ), (.chain [(7, 11)]), (.chain [(7, 11)]), (.chain [(7, 11)]), (.chain [(7, 11)]), (.chain [(7, 11), (7, 12)]), (.chain [(7, 11), (7, 12)]), .one⟩
theorem cell0789_ok : cell0789.check T = true := by decide +kernel

def cell0790 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (54363 / 6400 : ℚ), (109123 / 12800 : ℚ), (.chain [(7, 10)]), (.chain [(7, 11)]), (.chain [(7, 11)]), (.chain [(7, 10), (7, 11)]), (.chain [(7, 11), (7, 12)]), (.chain [(7, 11), (7, 12)]), .one⟩
theorem cell0790_ok : cell0790.check T = true := by decide +kernel

def cell0791 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (109123 / 12800 : ℚ), (1369 / 160 : ℚ), (.chain [(7, 11)]), (.chain [(7, 11)]), (.chain [(7, 11)]), (.chain [(7, 11), (7, 12)]), (.chain [(7, 11), (7, 12), (7, 13)]), (.chain [(7, 11), (7, 12)]), .one⟩
theorem cell0791_ok : cell0791.check T = true := by decide +kernel

def cell0792 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (109123 / 12800 : ℚ), (1369 / 160 : ℚ), (.chain [(7, 11)]), (.chain [(7, 12)]), (.chain [(7, 12)]), (.chain [(7, 11), (7, 12)]), (.chain [(7, 12), (7, 13)]), (.chain [(7, 12), (7, 13)]), .one⟩
theorem cell0792_ok : cell0792.check T = true := by decide +kernel

def cell0793 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (1369 / 160 : ℚ), (109917 / 12800 : ℚ), (.chain [(7, 12)]), (.chain [(7, 12)]), (.chain [(7, 12)]), (.chain [(7, 12), (7, 13)]), (.chain [(7, 12), (7, 13)]), (.chain [(7, 12), (7, 13)]), .one⟩
theorem cell0793_ok : cell0793.check T = true := by decide +kernel

def cell0794 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (1369 / 160 : ℚ), (109917 / 12800 : ℚ), (.chain [(7, 12)]), (.chain [(7, 13)]), (.chain [(7, 12)]), (.chain [(7, 12), (7, 13)]), (.chain [(7, 13), (7, 14)]), (.chain [(7, 12), (7, 13)]), .one⟩
theorem cell0794_ok : cell0794.check T = true := by decide +kernel

def cell0795 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (1369 / 160 : ℚ), (109917 / 12800 : ℚ), (.chain [(7, 12)]), (.chain [(7, 13)]), (.chain [(7, 12)]), (.chain [(7, 12), (7, 13)]), (.chain [(7, 13), (7, 14)]), (.chain [(7, 12), (7, 13)]), .one⟩
theorem cell0795_ok : cell0795.check T = true := by decide +kernel

def cell0796 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (109917 / 12800 : ℚ), (55157 / 6400 : ℚ), (.chain [(7, 13)]), (.chain [(7, 13)]), (.chain [(7, 13)]), (.chain [(7, 13), (7, 14)]), (.chain [(7, 13), (7, 14)]), (.chain [(7, 13), (7, 14)]), .one⟩
theorem cell0796_ok : cell0796.check T = true := by decide +kernel

def cell0797 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (109917 / 12800 : ℚ), (55157 / 6400 : ℚ), (.chain [(7, 13)]), (.chain [(7, 13)]), (.chain [(7, 13)]), (.chain [(7, 13), (7, 14)]), (.chain [(7, 13), (7, 14), (7, 15)]), (.chain [(7, 13), (7, 14)]), .one⟩
theorem cell0797_ok : cell0797.check T = true := by decide +kernel

def cell0798 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (55157 / 6400 : ℚ), (8841 / 1024 : ℚ), (.chain [(7, 14)]), (.chain [(7, 14)]), (.chain [(7, 14)]), (.chain [(7, 14)]), (.chain [(7, 14)]), (.chain [(7, 14)]), .one⟩
theorem cell0798_ok : cell0798.check T = true := by decide +kernel

def cell0799 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (8841 / 1024 : ℚ), (110711 / 12800 : ℚ), (.chain [(7, 14)]), (.chain [(7, 14)]), (.chain [(7, 14)]), (.chain [(7, 14)]), (.chain [(7, 14), (7, 15)]), (.chain [(7, 14), (7, 15)]), .three⟩
theorem cell0799_ok : cell0799.check T = true := by decide +kernel

def cells19 : List CellW := [cell0760, cell0761, cell0762, cell0763, cell0764, cell0765, cell0766, cell0767, cell0768, cell0769, cell0770, cell0771, cell0772, cell0773, cell0774, cell0775, cell0776, cell0777, cell0778, cell0779, cell0780, cell0781, cell0782, cell0783, cell0784, cell0785, cell0786, cell0787, cell0788, cell0789, cell0790, cell0791, cell0792, cell0793, cell0794, cell0795, cell0796, cell0797, cell0798, cell0799]

theorem cells19_valid : ∀ w ∈ cells19, w.check T = true :=
  (forall_mem_cons_of cell0760_ok (forall_mem_cons_of cell0761_ok (forall_mem_cons_of cell0762_ok (forall_mem_cons_of cell0763_ok (forall_mem_cons_of cell0764_ok (forall_mem_cons_of cell0765_ok (forall_mem_cons_of cell0766_ok (forall_mem_cons_of cell0767_ok (forall_mem_cons_of cell0768_ok (forall_mem_cons_of cell0769_ok (forall_mem_cons_of cell0770_ok (forall_mem_cons_of cell0771_ok (forall_mem_cons_of cell0772_ok (forall_mem_cons_of cell0773_ok (forall_mem_cons_of cell0774_ok (forall_mem_cons_of cell0775_ok (forall_mem_cons_of cell0776_ok (forall_mem_cons_of cell0777_ok (forall_mem_cons_of cell0778_ok (forall_mem_cons_of cell0779_ok (forall_mem_cons_of cell0780_ok (forall_mem_cons_of cell0781_ok (forall_mem_cons_of cell0782_ok (forall_mem_cons_of cell0783_ok (forall_mem_cons_of cell0784_ok (forall_mem_cons_of cell0785_ok (forall_mem_cons_of cell0786_ok (forall_mem_cons_of cell0787_ok (forall_mem_cons_of cell0788_ok (forall_mem_cons_of cell0789_ok (forall_mem_cons_of cell0790_ok (forall_mem_cons_of cell0791_ok (forall_mem_cons_of cell0792_ok (forall_mem_cons_of cell0793_ok (forall_mem_cons_of cell0794_ok (forall_mem_cons_of cell0795_ok (forall_mem_cons_of cell0796_ok (forall_mem_cons_of cell0797_ok (forall_mem_cons_of cell0798_ok (forall_mem_cons_of cell0799_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


