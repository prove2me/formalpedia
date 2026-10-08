-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells20
-- name    : CK_CKLaneC_SAxis_Data_Cells20
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T02:16:40.507449+00:00
-- url     : https://prove2.me/theorems/46e66a89-0b8c-4b35-9c02-825eb82254fb
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells20` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells20` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells20` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells20 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells20.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells20 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 20 (cells 800..839). -/

def cell0800 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (55157 / 6400 : ℚ), (110711 / 12800 : ℚ), (.chain [(7, 14)]), (.chain [(7, 14)]), (.chain [(7, 14)]), (.chain [(7, 14)]), (.chain [(7, 14), (7, 15)]), (.chain [(7, 14), (7, 15)]), .one⟩
theorem cell0800_ok : cell0800.check T = true := by decide +kernel

def cell0801 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (110711 / 12800 : ℚ), (27777 / 3200 : ℚ), (.chain [(7, 14)]), (.chain [(7, 14)]), (.chain [(7, 14)]), (.chain [(7, 14), (7, 15)]), (.chain [(7, 14), (7, 15), (7, 16)]), (.chain [(7, 14), (7, 15)]), .one⟩
theorem cell0801_ok : cell0801.check T = true := by decide +kernel

def cell0802 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (110711 / 12800 : ℚ), (27777 / 3200 : ℚ), (.chain [(7, 14)]), (.chain [(7, 15)]), (.chain [(7, 15)]), (.chain [(7, 14), (7, 15)]), (.chain [(7, 15), (7, 16)]), (.chain [(7, 15), (7, 16)]), .one⟩
theorem cell0802_ok : cell0802.check T = true := by decide +kernel

def cell0803 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (27777 / 3200 : ℚ), (22301 / 2560 : ℚ), (.chain [(7, 15)]), (.chain [(7, 15)]), (.chain [(7, 15)]), (.chain [(7, 15), (7, 16)]), (.chain [(7, 15), (7, 16)]), (.chain [(7, 15), (7, 16)]), .one⟩
theorem cell0803_ok : cell0803.check T = true := by decide +kernel

def cell0804 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (27777 / 3200 : ℚ), (22301 / 2560 : ℚ), (.chain [(7, 15)]), (.chain [(7, 16)]), (.chain [(7, 15)]), (.chain [(7, 15), (7, 16)]), (.chain [(7, 16), (7, 17)]), (.chain [(7, 15), (7, 16)]), .one⟩
theorem cell0804_ok : cell0804.check T = true := by decide +kernel

def cell0805 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (22301 / 2560 : ℚ), (55951 / 6400 : ℚ), (.chain [(7, 16)]), (.chain [(7, 16)]), (.chain [(7, 16)]), (.chain [(7, 16), (7, 17)]), (.chain [(7, 16), (7, 17)]), (.chain [(7, 16), (7, 17)]), .one⟩
theorem cell0805_ok : cell0805.check T = true := by decide +kernel

def cell0806 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (22301 / 2560 : ℚ), (55951 / 6400 : ℚ), (.chain [(7, 16)]), (.chain [(7, 16)]), (.chain [(7, 16)]), (.chain [(7, 16), (7, 17)]), (.chain [(7, 16), (7, 17), (7, 18)]), (.chain [(7, 16), (7, 17)]), .one⟩
theorem cell0806_ok : cell0806.check T = true := by decide +kernel

def cell0807 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (55951 / 6400 : ℚ), (112299 / 12800 : ℚ), (.chain [(7, 17)]), (.chain [(7, 17)]), (.chain [(7, 17)]), (.chain [(7, 17)]), (.chain [(7, 17), (7, 18)]), (.chain [(7, 17), (7, 18)]), .one⟩
theorem cell0807_ok : cell0807.check T = true := by decide +kernel

def cell0808 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (55951 / 6400 : ℚ), (112299 / 12800 : ℚ), (.chain [(7, 17)]), (.chain [(7, 17)]), (.chain [(7, 17)]), (.chain [(7, 17)]), (.chain [(7, 17), (7, 18)]), (.chain [(7, 17), (7, 18)]), .one⟩
theorem cell0808_ok : cell0808.check T = true := by decide +kernel

def cell0809 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (112299 / 12800 : ℚ), (44999 / 5120 : ℚ), (.chain [(7, 17)]), (.chain [(7, 17)]), (.chain [(7, 17)]), (.chain [(7, 17), (7, 18)]), (.chain [(7, 17), (7, 18)]), (.chain [(7, 17), (7, 18)]), .one⟩
theorem cell0809_ok : cell0809.check T = true := by decide +kernel

def cell0810 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (44999 / 5120 : ℚ), (14087 / 1600 : ℚ), (.chain [(7, 18)]), (.chain [(7, 18)]), (.chain [(7, 18)]), (.chain [(7, 18)]), (.chain [(7, 18), (7, 19)]), (.chain [(7, 18)]), .one⟩
theorem cell0810_ok : cell0810.check T = true := by decide +kernel

def cell0811 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (112299 / 12800 : ℚ), (14087 / 1600 : ℚ), (.chain [(7, 17)]), (.chain [(7, 18)]), (.chain [(7, 18)]), (.chain [(7, 17), (7, 18)]), (.chain [(7, 18), (7, 19)]), (.chain [(7, 18), (7, 19)]), .one⟩
theorem cell0811_ok : cell0811.check T = true := by decide +kernel

def cell0812 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (14087 / 1600 : ℚ), (113093 / 12800 : ℚ), (.chain [(7, 18)]), (.chain [(7, 18)]), (.chain [(7, 18)]), (.chain [(7, 18), (7, 19)]), (.chain [(7, 18), (7, 19), (7, 20)]), (.chain [(7, 18), (7, 19)]), .one⟩
theorem cell0812_ok : cell0812.check T = true := by decide +kernel

def cell0813 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (14087 / 1600 : ℚ), (113093 / 12800 : ℚ), (.chain [(7, 18)]), (.chain [(7, 19)]), (.chain [(7, 18)]), (.chain [(7, 18), (7, 19)]), (.chain [(7, 19), (7, 20)]), (.chain [(7, 18), (7, 19), (7, 20)]), .one⟩
theorem cell0813_ok : cell0813.check T = true := by decide +kernel

def cell0814 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (113093 / 12800 : ℚ), (11349 / 1280 : ℚ), (.chain [(7, 19)]), (.chain [(7, 19)]), (.chain [(7, 19)]), (.chain [(7, 19), (7, 20)]), (.chain [(7, 19), (7, 20)]), (.chain [(7, 19), (7, 20)]), .one⟩
theorem cell0814_ok : cell0814.check T = true := by decide +kernel

def cell0815 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (113093 / 12800 : ℚ), (11349 / 1280 : ℚ), (.chain [(7, 19)]), (.chain [(7, 20)]), (.chain [(7, 19)]), (.chain [(7, 19), (7, 20)]), (.chain [(7, 20), (7, 21)]), (.chain [(7, 19), (7, 20)]), .one⟩
theorem cell0815_ok : cell0815.check T = true := by decide +kernel

def cell0816 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (113093 / 12800 : ℚ), (11349 / 1280 : ℚ), (.chain [(7, 19)]), (.chain [(7, 20)]), (.chain [(7, 19)]), (.chain [(7, 19), (7, 20)]), (.chain [(7, 20), (7, 21)]), (.chain [(7, 19), (7, 20)]), .one⟩
theorem cell0816_ok : cell0816.check T = true := by decide +kernel

def cell0817 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (11349 / 1280 : ℚ), (113887 / 12800 : ℚ), (.chain [(7, 20)]), (.chain [(7, 20)]), (.chain [(7, 20)]), (.chain [(7, 20), (7, 21)]), (.chain [(7, 20), (7, 21)]), (.chain [(7, 20), (7, 21)]), .one⟩
theorem cell0817_ok : cell0817.check T = true := by decide +kernel

def cell0818 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (11349 / 1280 : ℚ), (113887 / 12800 : ℚ), (.chain [(7, 20)]), (.chain [(7, 20)]), (.chain [(7, 20)]), (.chain [(7, 20), (7, 21)]), (.chain [(7, 20), (7, 21), (7, 22)]), (.chain [(7, 20), (7, 21)]), .one⟩
theorem cell0818_ok : cell0818.check T = true := by decide +kernel

def cell0819 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (113887 / 12800 : ℚ), (228171 / 25600 : ℚ), (.chain [(7, 21)]), (.chain [(7, 21)]), (.chain [(7, 21)]), (.chain [(7, 21)]), (.chain [(7, 21)]), (.chain [(7, 21)]), .one⟩
theorem cell0819_ok : cell0819.check T = true := by decide +kernel

def cell0820 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (228171 / 25600 : ℚ), (28571 / 3200 : ℚ), (.chain [(7, 21)]), (.chain [(7, 21)]), (.chain [(7, 21)]), (.chain [(7, 21)]), (.chain [(7, 21), (7, 22)]), (.chain [(7, 21), (7, 22)]), .three⟩
theorem cell0820_ok : cell0820.check T = true := by decide +kernel

def cell0821 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (113887 / 12800 : ℚ), (28571 / 3200 : ℚ), (.chain [(7, 21)]), (.chain [(7, 21)]), (.chain [(7, 21)]), (.chain [(7, 21)]), (.chain [(7, 21), (7, 22)]), (.chain [(7, 21), (7, 22)]), .one⟩
theorem cell0821_ok : cell0821.check T = true := by decide +kernel

def cell0822 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (28571 / 3200 : ℚ), (114681 / 12800 : ℚ), (.chain [(7, 21)]), (.chain [(7, 21)]), (.chain [(7, 21)]), (.chain [(7, 21), (7, 22)]), (.chain [(7, 21), (7, 22), (7, 23)]), (.chain [(7, 21), (7, 22)]), .one⟩
theorem cell0822_ok : cell0822.check T = true := by decide +kernel

def cell0823 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (28571 / 3200 : ℚ), (114681 / 12800 : ℚ), (.chain [(7, 21)]), (.chain [(7, 22)]), (.chain [(7, 22)]), (.chain [(7, 21), (7, 22)]), (.chain [(7, 22), (7, 23)]), (.chain [(7, 22), (7, 23)]), .one⟩
theorem cell0823_ok : cell0823.check T = true := by decide +kernel

def cell0824 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (114681 / 12800 : ℚ), (57539 / 6400 : ℚ), (.chain [(7, 22)]), (.chain [(7, 22)]), (.chain [(7, 22)]), (.chain [(7, 22), (7, 23)]), (.chain [(7, 22), (7, 23)]), (.chain [(7, 22), (7, 23)]), .one⟩
theorem cell0824_ok : cell0824.check T = true := by decide +kernel

def cell0825 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (114681 / 12800 : ℚ), (57539 / 6400 : ℚ), (.chain [(7, 22)]), (.chain [(7, 23)]), (.chain [(7, 22)]), (.chain [(7, 22), (7, 23)]), (.chain [(7, 23), (7, 24)]), (.chain [(7, 22), (7, 23)]), .one⟩
theorem cell0825_ok : cell0825.check T = true := by decide +kernel

def cell0826 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (57539 / 6400 : ℚ), (4619 / 512 : ℚ), (.chain [(7, 23)]), (.chain [(7, 23)]), (.chain [(7, 23)]), (.chain [(7, 23), (7, 24)]), (.chain [(7, 23), (7, 24)]), (.chain [(7, 23), (7, 24)]), .one⟩
theorem cell0826_ok : cell0826.check T = true := by decide +kernel

def cell0827 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (57539 / 6400 : ℚ), (4619 / 512 : ℚ), (.chain [(7, 23)]), (.chain [(7, 23)]), (.chain [(7, 23)]), (.chain [(7, 23), (7, 24)]), (.chain [(7, 23), (7, 24), (7, 25)]), (.chain [(7, 23), (7, 24)]), .one⟩
theorem cell0827_ok : cell0827.check T = true := by decide +kernel

def cell0828 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (4619 / 512 : ℚ), (3621 / 400 : ℚ), (.chain [(7, 24)]), (.chain [(7, 24)]), (.chain [(7, 24)]), (.chain [(7, 24)]), (.chain [(7, 24), (7, 25)]), (.chain [(7, 24), (7, 25)]), .one⟩
theorem cell0828_ok : cell0828.check T = true := by decide +kernel

def cell0829 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (4619 / 512 : ℚ), (3621 / 400 : ℚ), (.chain [(7, 24)]), (.chain [(7, 24)]), (.chain [(7, 24)]), (.chain [(7, 24)]), (.chain [(7, 24), (7, 25)]), (.chain [(7, 24), (7, 25)]), .one⟩
theorem cell0829_ok : cell0829.check T = true := by decide +kernel

def cell0830 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (3621 / 400 : ℚ), (116269 / 12800 : ℚ), (.chain [(7, 24)]), (.chain [(7, 24)]), (.chain [(7, 24)]), (.chain [(7, 24), (7, 25)]), (.chain [(7, 24), (7, 25), (7, 26)]), (.chain [(7, 24), (7, 25)]), .one⟩
theorem cell0830_ok : cell0830.check T = true := by decide +kernel

def cell0831 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (3621 / 400 : ℚ), (116269 / 12800 : ℚ), (.chain [(7, 24)]), (.chain [(7, 25)]), (.chain [(7, 25)]), (.chain [(7, 24), (7, 25)]), (.chain [(7, 25), (7, 26)]), (.chain [(7, 25), (7, 26)]), .one⟩
theorem cell0831_ok : cell0831.check T = true := by decide +kernel

def cell0832 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (116269 / 12800 : ℚ), (58333 / 6400 : ℚ), (.chain [(7, 25)]), (.chain [(7, 25)]), (.chain [(7, 25)]), (.chain [(7, 25), (7, 26)]), (.chain [(7, 25), (7, 26)]), (.chain [(7, 25), (7, 26)]), .one⟩
theorem cell0832_ok : cell0832.check T = true := by decide +kernel

def cell0833 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (116269 / 12800 : ℚ), (58333 / 6400 : ℚ), (.chain [(7, 25)]), (.chain [(7, 26)]), (.chain [(7, 25)]), (.chain [(7, 25), (7, 26)]), (.chain [(7, 26), (7, 27)]), (.chain [(7, 25), (7, 26)]), .one⟩
theorem cell0833_ok : cell0833.check T = true := by decide +kernel

def cell0834 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (58333 / 6400 : ℚ), (117063 / 12800 : ℚ), (.chain [(7, 26)]), (.chain [(7, 26)]), (.chain [(7, 26)]), (.chain [(7, 26), (7, 27)]), (.chain [(7, 26), (7, 27)]), (.chain [(7, 26), (7, 27)]), .one⟩
theorem cell0834_ok : cell0834.check T = true := by decide +kernel

def cell0835 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (58333 / 6400 : ℚ), (117063 / 12800 : ℚ), (.chain [(7, 26)]), (.chain [(7, 26)]), (.chain [(7, 26)]), (.chain [(7, 26), (7, 27)]), (.chain [(7, 26), (7, 27), (7, 28)]), (.chain [(7, 26), (7, 27)]), .one⟩
theorem cell0835_ok : cell0835.check T = true := by decide +kernel

def cell0836 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (117063 / 12800 : ℚ), (5873 / 640 : ℚ), (.chain [(7, 27)]), (.chain [(7, 27)]), (.chain [(7, 27)]), (.chain [(7, 27), (7, 28)]), (.chain [(7, 27), (7, 28)]), (.chain [(7, 27), (7, 28)]), .one⟩
theorem cell0836_ok : cell0836.check T = true := by decide +kernel

def cell0837 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (117063 / 12800 : ℚ), (5873 / 640 : ℚ), (.chain [(7, 27)]), (.chain [(7, 27)]), (.chain [(7, 27)]), (.chain [(7, 27), (7, 28)]), (.chain [(7, 27), (7, 28), (7, 29)]), (.chain [(7, 27), (7, 28)]), .one⟩
theorem cell0837_ok : cell0837.check T = true := by decide +kernel

def cell0838 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (5873 / 640 : ℚ), (117857 / 12800 : ℚ), (.chain [(7, 28)]), (.chain [(7, 28)]), (.chain [(7, 28)]), (.chain [(7, 28)]), (.chain [(7, 28), (7, 29)]), (.chain [(7, 28), (7, 29)]), .one⟩
theorem cell0838_ok : cell0838.check T = true := by decide +kernel

def cell0839 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (5873 / 640 : ℚ), (117857 / 12800 : ℚ), (.chain [(7, 28)]), (.chain [(7, 28)]), (.chain [(7, 28)]), (.chain [(7, 28)]), (.chain [(7, 28), (7, 29)]), (.chain [(7, 28), (7, 29)]), .one⟩
theorem cell0839_ok : cell0839.check T = true := by decide +kernel

def cells20 : List CellW := [cell0800, cell0801, cell0802, cell0803, cell0804, cell0805, cell0806, cell0807, cell0808, cell0809, cell0810, cell0811, cell0812, cell0813, cell0814, cell0815, cell0816, cell0817, cell0818, cell0819, cell0820, cell0821, cell0822, cell0823, cell0824, cell0825, cell0826, cell0827, cell0828, cell0829, cell0830, cell0831, cell0832, cell0833, cell0834, cell0835, cell0836, cell0837, cell0838, cell0839]

theorem cells20_valid : ∀ w ∈ cells20, w.check T = true :=
  (forall_mem_cons_of cell0800_ok (forall_mem_cons_of cell0801_ok (forall_mem_cons_of cell0802_ok (forall_mem_cons_of cell0803_ok (forall_mem_cons_of cell0804_ok (forall_mem_cons_of cell0805_ok (forall_mem_cons_of cell0806_ok (forall_mem_cons_of cell0807_ok (forall_mem_cons_of cell0808_ok (forall_mem_cons_of cell0809_ok (forall_mem_cons_of cell0810_ok (forall_mem_cons_of cell0811_ok (forall_mem_cons_of cell0812_ok (forall_mem_cons_of cell0813_ok (forall_mem_cons_of cell0814_ok (forall_mem_cons_of cell0815_ok (forall_mem_cons_of cell0816_ok (forall_mem_cons_of cell0817_ok (forall_mem_cons_of cell0818_ok (forall_mem_cons_of cell0819_ok (forall_mem_cons_of cell0820_ok (forall_mem_cons_of cell0821_ok (forall_mem_cons_of cell0822_ok (forall_mem_cons_of cell0823_ok (forall_mem_cons_of cell0824_ok (forall_mem_cons_of cell0825_ok (forall_mem_cons_of cell0826_ok (forall_mem_cons_of cell0827_ok (forall_mem_cons_of cell0828_ok (forall_mem_cons_of cell0829_ok (forall_mem_cons_of cell0830_ok (forall_mem_cons_of cell0831_ok (forall_mem_cons_of cell0832_ok (forall_mem_cons_of cell0833_ok (forall_mem_cons_of cell0834_ok (forall_mem_cons_of cell0835_ok (forall_mem_cons_of cell0836_ok (forall_mem_cons_of cell0837_ok (forall_mem_cons_of cell0838_ok (forall_mem_cons_of cell0839_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


