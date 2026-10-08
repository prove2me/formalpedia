-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells21
-- name    : CK_CKLaneC_SAxis_Data_Cells21
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:29:04.379998+00:00
-- url     : https://prove2.me/theorems/418cd2ed-4d6a-4034-991a-09e04f777305
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells21` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells21` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells21` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells21 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells21.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells21 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 21 (cells 840..879). -/

def cell0840 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (117857 / 12800 : ℚ), (59127 / 6400 : ℚ), (.chain [(7, 28)]), (.chain [(7, 28)]), (.chain [(7, 28)]), (.chain [(7, 28), (7, 29)]), (.chain [(7, 28), (7, 29), (7, 30)]), (.chain [(7, 28), (7, 29)]), .one⟩
theorem cell0840_ok : cell0840.check T = true := by decide +kernel

def cell0841 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (117857 / 12800 : ℚ), (59127 / 6400 : ℚ), (.chain [(7, 28)]), (.chain [(7, 29)]), (.chain [(7, 29)]), (.chain [(7, 28), (7, 29)]), (.chain [(7, 29), (7, 30)]), (.chain [(7, 29), (7, 30)]), .one⟩
theorem cell0841_ok : cell0841.check T = true := by decide +kernel

def cell0842 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (59127 / 6400 : ℚ), (118651 / 12800 : ℚ), (.chain [(7, 29)]), (.chain [(7, 29)]), (.chain [(7, 29)]), (.chain [(7, 29), (7, 30)]), (.chain [(7, 29), (7, 30)]), (.chain [(7, 29), (7, 30)]), .one⟩
theorem cell0842_ok : cell0842.check T = true := by decide +kernel

def cell0843 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (59127 / 6400 : ℚ), (118651 / 12800 : ℚ), (.chain [(7, 29)]), (.chain [(7, 30)]), (.chain [(7, 29)]), (.chain [(7, 29), (7, 30)]), (.chain [(7, 30), (7, 31)]), (.chain [(7, 29), (7, 30)]), .one⟩
theorem cell0843_ok : cell0843.check T = true := by decide +kernel

def cell0844 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (118651 / 12800 : ℚ), (14881 / 1600 : ℚ), (.chain [(7, 30)]), (.chain [(7, 30)]), (.chain [(7, 30)]), (.chain [(7, 30), (7, 31)]), (.chain [(7, 30), (7, 31)]), (.chain [(7, 30), (7, 31)]), .one⟩
theorem cell0844_ok : cell0844.check T = true := by decide +kernel

def cell0845 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (118651 / 12800 : ℚ), (14881 / 1600 : ℚ), (.chain [(7, 30)]), (.chain [(7, 30)]), (.chain [(7, 30)]), (.chain [(7, 30), (7, 31)]), (.chain [(7, 30), (7, 31), (8, 0)]), (.chain [(7, 30), (7, 31)]), .one⟩
theorem cell0845_ok : cell0845.check T = true := by decide +kernel

def cell0846 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (14881 / 1600 : ℚ), (23889 / 2560 : ℚ), (.chain [(7, 31)]), (.chain [(7, 31)]), (.chain [(7, 31)]), (.chain [(7, 31)]), (.chain [(7, 31), (8, 0)]), (.chain [(7, 31), (8, 0)]), .one⟩
theorem cell0846_ok : cell0846.check T = true := by decide +kernel

def cell0847 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (14881 / 1600 : ℚ), (23889 / 2560 : ℚ), (.chain [(7, 31)]), (.chain [(7, 31)]), (.chain [(7, 31)]), (.chain [(7, 31)]), (.chain [(7, 31), (8, 0)]), (.chain [(7, 31), (8, 0)]), .one⟩
theorem cell0847_ok : cell0847.check T = true := by decide +kernel

def cell0848 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (23889 / 2560 : ℚ), (59921 / 6400 : ℚ), (.chain [(7, 31)]), (.chain [(7, 31)]), (.chain [(7, 31)]), (.chain [(7, 31), (8, 0)]), (.chain [(7, 31), (8, 0), (8, 1)]), (.chain [(7, 31), (8, 0)]), .one⟩
theorem cell0848_ok : cell0848.check T = true := by decide +kernel

def cell0849 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (23889 / 2560 : ℚ), (59921 / 6400 : ℚ), (.chain [(7, 31)]), (.chain [(8, 0)]), (.chain [(8, 0)]), (.chain [(7, 31), (8, 0)]), (.chain [(8, 0), (8, 1)]), (.chain [(8, 0), (8, 1)]), .one⟩
theorem cell0849_ok : cell0849.check T = true := by decide +kernel

def cell0850 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (59921 / 6400 : ℚ), (120239 / 12800 : ℚ), (.chain [(8, 0)]), (.chain [(8, 0)]), (.chain [(8, 0)]), (.chain [(8, 0), (8, 1)]), (.chain [(8, 0), (8, 1)]), (.chain [(8, 0), (8, 1)]), .one⟩
theorem cell0850_ok : cell0850.check T = true := by decide +kernel

def cell0851 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (59921 / 6400 : ℚ), (120239 / 12800 : ℚ), (.chain [(8, 0)]), (.chain [(8, 1)]), (.chain [(8, 0)]), (.chain [(8, 0), (8, 1)]), (.chain [(8, 1), (8, 2)]), (.chain [(8, 0), (8, 1)]), .one⟩
theorem cell0851_ok : cell0851.check T = true := by decide +kernel

def cell0852 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (120239 / 12800 : ℚ), (30159 / 3200 : ℚ), (.chain [(8, 1)]), (.chain [(8, 1)]), (.chain [(8, 1)]), (.chain [(8, 1), (8, 2)]), (.chain [(8, 1), (8, 2)]), (.chain [(8, 1), (8, 2)]), .one⟩
theorem cell0852_ok : cell0852.check T = true := by decide +kernel

def cell0853 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (120239 / 12800 : ℚ), (30159 / 3200 : ℚ), (.chain [(8, 1)]), (.chain [(8, 1)]), (.chain [(8, 1)]), (.chain [(8, 1), (8, 2)]), (.chain [(8, 1), (8, 2), (8, 3)]), (.chain [(8, 1), (8, 2)]), .one⟩
theorem cell0853_ok : cell0853.check T = true := by decide +kernel

def cell0854 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (30159 / 3200 : ℚ), (121033 / 12800 : ℚ), (.chain [(8, 2)]), (.chain [(8, 2)]), (.chain [(8, 2)]), (.chain [(8, 2), (8, 3)]), (.chain [(8, 2), (8, 3)]), (.chain [(8, 2), (8, 3)]), .one⟩
theorem cell0854_ok : cell0854.check T = true := by decide +kernel

def cell0855 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (30159 / 3200 : ℚ), (121033 / 12800 : ℚ), (.chain [(8, 2)]), (.chain [(8, 2)]), (.chain [(8, 2)]), (.chain [(8, 2), (8, 3)]), (.chain [(8, 2), (8, 3), (8, 4)]), (.chain [(8, 2), (8, 3)]), .one⟩
theorem cell0855_ok : cell0855.check T = true := by decide +kernel

def cell0856 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (121033 / 12800 : ℚ), (12143 / 1280 : ℚ), (.chain [(8, 3)]), (.chain [(8, 3)]), (.chain [(8, 3)]), (.chain [(8, 3)]), (.chain [(8, 3), (8, 4)]), (.chain [(8, 3), (8, 4)]), .one⟩
theorem cell0856_ok : cell0856.check T = true := by decide +kernel

def cell0857 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (121033 / 12800 : ℚ), (12143 / 1280 : ℚ), (.chain [(8, 3)]), (.chain [(8, 3)]), (.chain [(8, 3)]), (.chain [(8, 3)]), (.chain [(8, 3), (8, 4)]), (.chain [(8, 3), (8, 4)]), .one⟩
theorem cell0857_ok : cell0857.check T = true := by decide +kernel

def cell0858 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (12143 / 1280 : ℚ), (121827 / 12800 : ℚ), (.chain [(8, 3)]), (.chain [(8, 3)]), (.chain [(8, 3)]), (.chain [(8, 3), (8, 4)]), (.chain [(8, 3), (8, 4), (8, 5)]), (.chain [(8, 3), (8, 4)]), .one⟩
theorem cell0858_ok : cell0858.check T = true := by decide +kernel

def cell0859 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (12143 / 1280 : ℚ), (121827 / 12800 : ℚ), (.chain [(8, 3)]), (.chain [(8, 4)]), (.chain [(8, 4)]), (.chain [(8, 3), (8, 4)]), (.chain [(8, 4), (8, 5)]), (.chain [(8, 4), (8, 5)]), .one⟩
theorem cell0859_ok : cell0859.check T = true := by decide +kernel

def cell0860 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (121827 / 12800 : ℚ), (7639 / 800 : ℚ), (.chain [(8, 4)]), (.chain [(8, 4)]), (.chain [(8, 4)]), (.chain [(8, 4), (8, 5)]), (.chain [(8, 4), (8, 5)]), (.chain [(8, 4), (8, 5)]), .one⟩
theorem cell0860_ok : cell0860.check T = true := by decide +kernel

def cell0861 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (121827 / 12800 : ℚ), (7639 / 800 : ℚ), (.chain [(8, 4)]), (.chain [(8, 5)]), (.chain [(8, 4)]), (.chain [(8, 4), (8, 5)]), (.chain [(8, 5), (8, 6)]), (.chain [(8, 4), (8, 5)]), .one⟩
theorem cell0861_ok : cell0861.check T = true := by decide +kernel

def cell0862 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (7639 / 800 : ℚ), (122621 / 12800 : ℚ), (.chain [(8, 5)]), (.chain [(8, 5)]), (.chain [(8, 5)]), (.chain [(8, 5), (8, 6)]), (.chain [(8, 5), (8, 6)]), (.chain [(8, 5), (8, 6)]), .one⟩
theorem cell0862_ok : cell0862.check T = true := by decide +kernel

def cell0863 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (7639 / 800 : ℚ), (122621 / 12800 : ℚ), (.chain [(8, 5)]), (.chain [(8, 5)]), (.chain [(8, 5)]), (.chain [(8, 5), (8, 6)]), (.chain [(8, 5), (8, 6), (8, 7)]), (.chain [(8, 5), (8, 6)]), .one⟩
theorem cell0863_ok : cell0863.check T = true := by decide +kernel

def cell0864 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (122621 / 12800 : ℚ), (61509 / 6400 : ℚ), (.chain [(8, 6)]), (.chain [(8, 6)]), (.chain [(8, 6)]), (.chain [(8, 6)]), (.chain [(8, 6), (8, 7)]), (.chain [(8, 6), (8, 7)]), .one⟩
theorem cell0864_ok : cell0864.check T = true := by decide +kernel

def cell0865 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (122621 / 12800 : ℚ), (61509 / 6400 : ℚ), (.chain [(8, 6)]), (.chain [(8, 6)]), (.chain [(8, 6)]), (.chain [(8, 6)]), (.chain [(8, 6), (8, 7)]), (.chain [(8, 6), (8, 7)]), .one⟩
theorem cell0865_ok : cell0865.check T = true := by decide +kernel

def cell0866 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (61509 / 6400 : ℚ), (24683 / 2560 : ℚ), (.chain [(8, 6)]), (.chain [(8, 6)]), (.chain [(8, 6)]), (.chain [(8, 6), (8, 7)]), (.chain [(8, 6), (8, 7), (8, 8)]), (.chain [(8, 6), (8, 7)]), .one⟩
theorem cell0866_ok : cell0866.check T = true := by decide +kernel

def cell0867 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (61509 / 6400 : ℚ), (24683 / 2560 : ℚ), (.chain [(8, 6)]), (.chain [(8, 7)]), (.chain [(8, 7)]), (.chain [(8, 6), (8, 7)]), (.chain [(8, 7), (8, 8)]), (.chain [(8, 7), (8, 8)]), .one⟩
theorem cell0867_ok : cell0867.check T = true := by decide +kernel

def cell0868 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (24683 / 2560 : ℚ), (30953 / 3200 : ℚ), (.chain [(8, 7)]), (.chain [(8, 7)]), (.chain [(8, 7)]), (.chain [(8, 7), (8, 8)]), (.chain [(8, 7), (8, 8)]), (.chain [(8, 7), (8, 8)]), .one⟩
theorem cell0868_ok : cell0868.check T = true := by decide +kernel

def cell0869 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (24683 / 2560 : ℚ), (30953 / 3200 : ℚ), (.chain [(8, 7)]), (.chain [(8, 8)]), (.chain [(8, 7)]), (.chain [(8, 7), (8, 8)]), (.chain [(8, 8), (8, 9)]), (.chain [(8, 7), (8, 8)]), .one⟩
theorem cell0869_ok : cell0869.check T = true := by decide +kernel

def cell0870 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (30953 / 3200 : ℚ), (124209 / 12800 : ℚ), (.chain [(8, 8)]), (.chain [(8, 8)]), (.chain [(8, 8)]), (.chain [(8, 8), (8, 9)]), (.chain [(8, 8), (8, 9)]), (.chain [(8, 8), (8, 9)]), .one⟩
theorem cell0870_ok : cell0870.check T = true := by decide +kernel

def cell0871 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (30953 / 3200 : ℚ), (124209 / 12800 : ℚ), (.chain [(8, 8)]), (.chain [(8, 8)]), (.chain [(8, 8)]), (.chain [(8, 8), (8, 9)]), (.chain [(8, 8), (8, 9), (8, 10)]), (.chain [(8, 8), (8, 9)]), .one⟩
theorem cell0871_ok : cell0871.check T = true := by decide +kernel

def cell0872 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (124209 / 12800 : ℚ), (62303 / 6400 : ℚ), (.chain [(8, 9)]), (.chain [(8, 9)]), (.chain [(8, 9)]), (.chain [(8, 9)]), (.chain [(8, 9), (8, 10)]), (.chain [(8, 9), (8, 10)]), .one⟩
theorem cell0872_ok : cell0872.check T = true := by decide +kernel

def cell0873 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (124209 / 12800 : ℚ), (62303 / 6400 : ℚ), (.chain [(8, 9)]), (.chain [(8, 9)]), (.chain [(8, 9)]), (.chain [(8, 9)]), (.chain [(8, 9), (8, 10)]), (.chain [(8, 9), (8, 10)]), .one⟩
theorem cell0873_ok : cell0873.check T = true := by decide +kernel

def cell0874 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (62303 / 6400 : ℚ), (125003 / 12800 : ℚ), (.chain [(8, 9)]), (.chain [(8, 9)]), (.chain [(8, 9)]), (.chain [(8, 9), (8, 10)]), (.chain [(8, 9), (8, 10), (8, 11)]), (.chain [(8, 9), (8, 10), (8, 11)]), .one⟩
theorem cell0874_ok : cell0874.check T = true := by decide +kernel

def cell0875 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (62303 / 6400 : ℚ), (125003 / 12800 : ℚ), (.chain [(8, 9)]), (.chain [(8, 10)]), (.chain [(8, 10)]), (.chain [(8, 9), (8, 10)]), (.chain [(8, 10), (8, 11)]), (.chain [(8, 10), (8, 11)]), .one⟩
theorem cell0875_ok : cell0875.check T = true := by decide +kernel

def cell0876 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (125003 / 12800 : ℚ), (627 / 64 : ℚ), (.chain [(8, 10)]), (.chain [(8, 10)]), (.chain [(8, 10)]), (.chain [(8, 10), (8, 11)]), (.chain [(8, 10), (8, 11), (8, 12)]), (.chain [(8, 10), (8, 11)]), .one⟩
theorem cell0876_ok : cell0876.check T = true := by decide +kernel

def cell0877 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (125003 / 12800 : ℚ), (627 / 64 : ℚ), (.chain [(8, 10)]), (.chain [(8, 11)]), (.chain [(8, 11)]), (.chain [(8, 10), (8, 11)]), (.chain [(8, 11), (8, 12)]), (.chain [(8, 11), (8, 12)]), .one⟩
theorem cell0877_ok : cell0877.check T = true := by decide +kernel

def cell0878 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (627 / 64 : ℚ), (125797 / 12800 : ℚ), (.chain [(8, 11)]), (.chain [(8, 11)]), (.chain [(8, 11)]), (.chain [(8, 11), (8, 12)]), (.chain [(8, 11), (8, 12)]), (.chain [(8, 11), (8, 12)]), .one⟩
theorem cell0878_ok : cell0878.check T = true := by decide +kernel

def cell0879 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (627 / 64 : ℚ), (125797 / 12800 : ℚ), (.chain [(8, 11)]), (.chain [(8, 12)]), (.chain [(8, 11)]), (.chain [(8, 11), (8, 12)]), (.chain [(8, 12), (8, 13)]), (.chain [(8, 11), (8, 12)]), .one⟩
theorem cell0879_ok : cell0879.check T = true := by decide +kernel

def cells21 : List CellW := [cell0840, cell0841, cell0842, cell0843, cell0844, cell0845, cell0846, cell0847, cell0848, cell0849, cell0850, cell0851, cell0852, cell0853, cell0854, cell0855, cell0856, cell0857, cell0858, cell0859, cell0860, cell0861, cell0862, cell0863, cell0864, cell0865, cell0866, cell0867, cell0868, cell0869, cell0870, cell0871, cell0872, cell0873, cell0874, cell0875, cell0876, cell0877, cell0878, cell0879]

theorem cells21_valid : ∀ w ∈ cells21, w.check T = true :=
  (forall_mem_cons_of cell0840_ok (forall_mem_cons_of cell0841_ok (forall_mem_cons_of cell0842_ok (forall_mem_cons_of cell0843_ok (forall_mem_cons_of cell0844_ok (forall_mem_cons_of cell0845_ok (forall_mem_cons_of cell0846_ok (forall_mem_cons_of cell0847_ok (forall_mem_cons_of cell0848_ok (forall_mem_cons_of cell0849_ok (forall_mem_cons_of cell0850_ok (forall_mem_cons_of cell0851_ok (forall_mem_cons_of cell0852_ok (forall_mem_cons_of cell0853_ok (forall_mem_cons_of cell0854_ok (forall_mem_cons_of cell0855_ok (forall_mem_cons_of cell0856_ok (forall_mem_cons_of cell0857_ok (forall_mem_cons_of cell0858_ok (forall_mem_cons_of cell0859_ok (forall_mem_cons_of cell0860_ok (forall_mem_cons_of cell0861_ok (forall_mem_cons_of cell0862_ok (forall_mem_cons_of cell0863_ok (forall_mem_cons_of cell0864_ok (forall_mem_cons_of cell0865_ok (forall_mem_cons_of cell0866_ok (forall_mem_cons_of cell0867_ok (forall_mem_cons_of cell0868_ok (forall_mem_cons_of cell0869_ok (forall_mem_cons_of cell0870_ok (forall_mem_cons_of cell0871_ok (forall_mem_cons_of cell0872_ok (forall_mem_cons_of cell0873_ok (forall_mem_cons_of cell0874_ok (forall_mem_cons_of cell0875_ok (forall_mem_cons_of cell0876_ok (forall_mem_cons_of cell0877_ok (forall_mem_cons_of cell0878_ok (forall_mem_cons_of cell0879_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


