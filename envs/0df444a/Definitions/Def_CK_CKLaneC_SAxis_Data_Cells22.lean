-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells22
-- name    : CK_CKLaneC_SAxis_Data_Cells22
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:23:28.837963+00:00
-- url     : https://prove2.me/theorems/d412d43f-b080-4bbe-b786-5f62def47e20
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells22` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells22` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells22` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells22 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells22.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells22 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 22 (cells 880..919). -/

def cell0880 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (125797 / 12800 : ℚ), (63097 / 6400 : ℚ), (.chain [(8, 12)]), (.chain [(8, 12)]), (.chain [(8, 12)]), (.chain [(8, 12), (8, 13)]), (.chain [(8, 12), (8, 13)]), (.chain [(8, 12), (8, 13)]), .one⟩
theorem cell0880_ok : cell0880.check T = true := by decide +kernel

def cell0881 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (125797 / 12800 : ℚ), (63097 / 6400 : ℚ), (.chain [(8, 12)]), (.chain [(8, 12)]), (.chain [(8, 12)]), (.chain [(8, 12), (8, 13)]), (.chain [(8, 12), (8, 13), (8, 14)]), (.chain [(8, 12), (8, 13)]), .one⟩
theorem cell0881_ok : cell0881.check T = true := by decide +kernel

def cell0882 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (63097 / 6400 : ℚ), (126591 / 12800 : ℚ), (.chain [(8, 13)]), (.chain [(8, 13)]), (.chain [(8, 13)]), (.chain [(8, 13)]), (.chain [(8, 13), (8, 14)]), (.chain [(8, 13), (8, 14)]), .one⟩
theorem cell0882_ok : cell0882.check T = true := by decide +kernel

def cell0883 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (63097 / 6400 : ℚ), (126591 / 12800 : ℚ), (.chain [(8, 13)]), (.chain [(8, 13)]), (.chain [(8, 13)]), (.chain [(8, 13)]), (.chain [(8, 13), (8, 14)]), (.chain [(8, 13), (8, 14)]), .one⟩
theorem cell0883_ok : cell0883.check T = true := by decide +kernel

def cell0884 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (126591 / 12800 : ℚ), (31747 / 3200 : ℚ), (.chain [(8, 13)]), (.chain [(8, 13)]), (.chain [(8, 13)]), (.chain [(8, 13), (8, 14)]), (.chain [(8, 13), (8, 14), (8, 15)]), (.chain [(8, 13), (8, 14)]), .one⟩
theorem cell0884_ok : cell0884.check T = true := by decide +kernel

def cell0885 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (126591 / 12800 : ℚ), (31747 / 3200 : ℚ), (.chain [(8, 13)]), (.chain [(8, 14)]), (.chain [(8, 14)]), (.chain [(8, 13), (8, 14)]), (.chain [(8, 14), (8, 15)]), (.chain [(8, 14), (8, 15)]), .one⟩
theorem cell0885_ok : cell0885.check T = true := by decide +kernel

def cell0886 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (31747 / 3200 : ℚ), (25477 / 2560 : ℚ), (.chain [(8, 14)]), (.chain [(8, 14)]), (.chain [(8, 14)]), (.chain [(8, 14), (8, 15)]), (.chain [(8, 14), (8, 15)]), (.chain [(8, 14), (8, 15)]), .one⟩
theorem cell0886_ok : cell0886.check T = true := by decide +kernel

def cell0887 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (31747 / 3200 : ℚ), (25477 / 2560 : ℚ), (.chain [(8, 14)]), (.chain [(8, 15)]), (.chain [(8, 14)]), (.chain [(8, 14), (8, 15)]), (.chain [(8, 15), (8, 16)]), (.chain [(8, 14), (8, 15)]), .one⟩
theorem cell0887_ok : cell0887.check T = true := by decide +kernel

def cell0888 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (25477 / 2560 : ℚ), (63891 / 6400 : ℚ), (.chain [(8, 15)]), (.chain [(8, 15)]), (.chain [(8, 15)]), (.chain [(8, 15), (8, 16)]), (.chain [(8, 15), (8, 16)]), (.chain [(8, 15), (8, 16)]), .one⟩
theorem cell0888_ok : cell0888.check T = true := by decide +kernel

def cell0889 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (25477 / 2560 : ℚ), (63891 / 6400 : ℚ), (.chain [(8, 15)]), (.chain [(8, 15)]), (.chain [(8, 15)]), (.chain [(8, 15), (8, 16)]), (.chain [(8, 15), (8, 16), (8, 17)]), (.chain [(8, 15), (8, 16)]), .one⟩
theorem cell0889_ok : cell0889.check T = true := by decide +kernel

def cell0890 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (63891 / 6400 : ℚ), (128179 / 12800 : ℚ), (.chain [(8, 16)]), (.chain [(8, 16)]), (.chain [(8, 16)]), (.chain [(8, 16)]), (.chain [(8, 16), (8, 17)]), (.chain [(8, 16), (8, 17)]), .one⟩
theorem cell0890_ok : cell0890.check T = true := by decide +kernel

def cell0891 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (63891 / 6400 : ℚ), (128179 / 12800 : ℚ), (.chain [(8, 16)]), (.chain [(8, 16)]), (.chain [(8, 16)]), (.chain [(8, 16)]), (.chain [(8, 16), (8, 17)]), (.chain [(8, 16), (8, 17)]), .one⟩
theorem cell0891_ok : cell0891.check T = true := by decide +kernel

def cell0892 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (128179 / 12800 : ℚ), (2009 / 200 : ℚ), (.chain [(8, 16)]), (.chain [(8, 16)]), (.chain [(8, 16)]), (.chain [(8, 16), (8, 17)]), (.chain [(8, 16), (8, 17), (8, 18)]), (.chain [(8, 16), (8, 17), (8, 18)]), .one⟩
theorem cell0892_ok : cell0892.check T = true := by decide +kernel

def cell0893 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (128179 / 12800 : ℚ), (2009 / 200 : ℚ), (.chain [(8, 16)]), (.chain [(8, 17)]), (.chain [(8, 17)]), (.chain [(8, 16), (8, 17)]), (.chain [(8, 17), (8, 18)]), (.chain [(8, 17), (8, 18)]), .one⟩
theorem cell0893_ok : cell0893.check T = true := by decide +kernel

def cell0894 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (2009 / 200 : ℚ), (128973 / 12800 : ℚ), (.chain [(8, 17)]), (.chain [(8, 17)]), (.chain [(8, 17)]), (.chain [(8, 17), (8, 18)]), (.chain [(8, 17), (8, 18), (8, 19)]), (.chain [(8, 17), (8, 18)]), .one⟩
theorem cell0894_ok : cell0894.check T = true := by decide +kernel

def cell0895 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (2009 / 200 : ℚ), (128973 / 12800 : ℚ), (.chain [(8, 17)]), (.chain [(8, 18)]), (.chain [(8, 18)]), (.chain [(8, 17), (8, 18)]), (.chain [(8, 18), (8, 19)]), (.chain [(8, 18), (8, 19)]), .one⟩
theorem cell0895_ok : cell0895.check T = true := by decide +kernel

def cell0896 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (128973 / 12800 : ℚ), (12937 / 1280 : ℚ), (.chain [(8, 18)]), (.chain [(8, 18)]), (.chain [(8, 18)]), (.chain [(8, 18), (8, 19)]), (.chain [(8, 18), (8, 19)]), (.chain [(8, 18), (8, 19)]), .one⟩
theorem cell0896_ok : cell0896.check T = true := by decide +kernel

def cell0897 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (128973 / 12800 : ℚ), (12937 / 1280 : ℚ), (.chain [(8, 18)]), (.chain [(8, 19)]), (.chain [(8, 18)]), (.chain [(8, 18), (8, 19)]), (.chain [(8, 19), (8, 20)]), (.chain [(8, 18), (8, 19)]), .one⟩
theorem cell0897_ok : cell0897.check T = true := by decide +kernel

def cell0898 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (12937 / 1280 : ℚ), (129767 / 12800 : ℚ), (.chain [(8, 19)]), (.chain [(8, 19)]), (.chain [(8, 19)]), (.chain [(8, 19), (8, 20)]), (.chain [(8, 19), (8, 20)]), (.chain [(8, 19), (8, 20)]), .one⟩
theorem cell0898_ok : cell0898.check T = true := by decide +kernel

def cell0899 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (12937 / 1280 : ℚ), (129767 / 12800 : ℚ), (.chain [(8, 19)]), (.chain [(8, 19)]), (.chain [(8, 19)]), (.chain [(8, 19), (8, 20)]), (.chain [(8, 19), (8, 20), (8, 21)]), (.chain [(8, 19), (8, 20)]), .one⟩
theorem cell0899_ok : cell0899.check T = true := by decide +kernel

def cell0900 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (129767 / 12800 : ℚ), (32541 / 3200 : ℚ), (.chain [(8, 20)]), (.chain [(8, 20)]), (.chain [(8, 20)]), (.chain [(8, 20)]), (.chain [(8, 20), (8, 21)]), (.chain [(8, 20), (8, 21)]), .one⟩
theorem cell0900_ok : cell0900.check T = true := by decide +kernel

def cell0901 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (129767 / 12800 : ℚ), (32541 / 3200 : ℚ), (.chain [(8, 20)]), (.chain [(8, 20)]), (.chain [(8, 20)]), (.chain [(8, 20)]), (.chain [(8, 20), (8, 21)]), (.chain [(8, 20), (8, 21)]), .one⟩
theorem cell0901_ok : cell0901.check T = true := by decide +kernel

def cell0902 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (32541 / 3200 : ℚ), (130561 / 12800 : ℚ), (.chain [(8, 20)]), (.chain [(8, 20)]), (.chain [(8, 20)]), (.chain [(8, 20), (8, 21)]), (.chain [(8, 20), (8, 21), (8, 22)]), (.chain [(8, 20), (8, 21)]), .one⟩
theorem cell0902_ok : cell0902.check T = true := by decide +kernel

def cell0903 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (32541 / 3200 : ℚ), (130561 / 12800 : ℚ), (.chain [(8, 20)]), (.chain [(8, 21)]), (.chain [(8, 21)]), (.chain [(8, 20), (8, 21)]), (.chain [(8, 21), (8, 22)]), (.chain [(8, 21), (8, 22)]), .one⟩
theorem cell0903_ok : cell0903.check T = true := by decide +kernel

def cell0904 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (130561 / 12800 : ℚ), (65479 / 6400 : ℚ), (.chain [(8, 21)]), (.chain [(8, 21)]), (.chain [(8, 21)]), (.chain [(8, 21), (8, 22)]), (.chain [(8, 21), (8, 22)]), (.chain [(8, 21), (8, 22)]), .one⟩
theorem cell0904_ok : cell0904.check T = true := by decide +kernel

def cell0905 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (130561 / 12800 : ℚ), (65479 / 6400 : ℚ), (.chain [(8, 21)]), (.chain [(8, 22)]), (.chain [(8, 21)]), (.chain [(8, 21), (8, 22)]), (.chain [(8, 22), (8, 23)]), (.chain [(8, 21), (8, 22)]), .one⟩
theorem cell0905_ok : cell0905.check T = true := by decide +kernel

def cell0906 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (65479 / 6400 : ℚ), (26271 / 2560 : ℚ), (.chain [(8, 22)]), (.chain [(8, 22)]), (.chain [(8, 22)]), (.chain [(8, 22), (8, 23)]), (.chain [(8, 22), (8, 23)]), (.chain [(8, 22), (8, 23)]), .one⟩
theorem cell0906_ok : cell0906.check T = true := by decide +kernel

def cell0907 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (65479 / 6400 : ℚ), (26271 / 2560 : ℚ), (.chain [(8, 22)]), (.chain [(8, 22)]), (.chain [(8, 22)]), (.chain [(8, 22), (8, 23)]), (.chain [(8, 22), (8, 23), (8, 24)]), (.chain [(8, 22), (8, 23)]), .one⟩
theorem cell0907_ok : cell0907.check T = true := by decide +kernel

def cell0908 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (26271 / 2560 : ℚ), (16469 / 1600 : ℚ), (.chain [(8, 23)]), (.chain [(8, 23)]), (.chain [(8, 23)]), (.chain [(8, 23)]), (.chain [(8, 23), (8, 24)]), (.chain [(8, 23), (8, 24)]), .one⟩
theorem cell0908_ok : cell0908.check T = true := by decide +kernel

def cell0909 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (26271 / 2560 : ℚ), (16469 / 1600 : ℚ), (.chain [(8, 23)]), (.chain [(8, 23)]), (.chain [(8, 23)]), (.chain [(8, 23)]), (.chain [(8, 23), (8, 24)]), (.chain [(8, 23), (8, 24)]), .one⟩
theorem cell0909_ok : cell0909.check T = true := by decide +kernel

def cell0910 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (16469 / 1600 : ℚ), (132149 / 12800 : ℚ), (.chain [(8, 23)]), (.chain [(8, 23)]), (.chain [(8, 23)]), (.chain [(8, 23), (8, 24)]), (.chain [(8, 23), (8, 24), (8, 25)]), (.chain [(8, 23), (8, 24)]), .one⟩
theorem cell0910_ok : cell0910.check T = true := by decide +kernel

def cell0911 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (16469 / 1600 : ℚ), (132149 / 12800 : ℚ), (.chain [(8, 23)]), (.chain [(8, 24)]), (.chain [(8, 24)]), (.chain [(8, 23), (8, 24)]), (.chain [(8, 24), (8, 25)]), (.chain [(8, 24), (8, 25)]), .one⟩
theorem cell0911_ok : cell0911.check T = true := by decide +kernel

def cell0912 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (132149 / 12800 : ℚ), (66273 / 6400 : ℚ), (.chain [(8, 24)]), (.chain [(8, 24)]), (.chain [(8, 24)]), (.chain [(8, 24), (8, 25)]), (.chain [(8, 24), (8, 25), (8, 26)]), (.chain [(8, 24), (8, 25)]), .one⟩
theorem cell0912_ok : cell0912.check T = true := by decide +kernel

def cell0913 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (132149 / 12800 : ℚ), (66273 / 6400 : ℚ), (.chain [(8, 24)]), (.chain [(8, 25)]), (.chain [(8, 24)]), (.chain [(8, 24), (8, 25)]), (.chain [(8, 25), (8, 26)]), (.chain [(8, 24), (8, 25), (8, 26)]), .one⟩
theorem cell0913_ok : cell0913.check T = true := by decide +kernel

def cell0914 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (66273 / 6400 : ℚ), (132943 / 12800 : ℚ), (.chain [(8, 25)]), (.chain [(8, 25)]), (.chain [(8, 25)]), (.chain [(8, 25), (8, 26)]), (.chain [(8, 25), (8, 26)]), (.chain [(8, 25), (8, 26)]), .one⟩
theorem cell0914_ok : cell0914.check T = true := by decide +kernel

def cell0915 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (66273 / 6400 : ℚ), (132943 / 12800 : ℚ), (.chain [(8, 25)]), (.chain [(8, 26)]), (.chain [(8, 25)]), (.chain [(8, 25), (8, 26)]), (.chain [(8, 26), (8, 27)]), (.chain [(8, 25), (8, 26)]), .one⟩
theorem cell0915_ok : cell0915.check T = true := by decide +kernel

def cell0916 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (132943 / 12800 : ℚ), (6667 / 640 : ℚ), (.chain [(8, 26)]), (.chain [(8, 26)]), (.chain [(8, 26)]), (.chain [(8, 26), (8, 27)]), (.chain [(8, 26), (8, 27)]), (.chain [(8, 26), (8, 27)]), .one⟩
theorem cell0916_ok : cell0916.check T = true := by decide +kernel

def cell0917 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (132943 / 12800 : ℚ), (6667 / 640 : ℚ), (.chain [(8, 26)]), (.chain [(8, 26)]), (.chain [(8, 26)]), (.chain [(8, 26), (8, 27)]), (.chain [(8, 26), (8, 27), (8, 28)]), (.chain [(8, 26), (8, 27)]), .one⟩
theorem cell0917_ok : cell0917.check T = true := by decide +kernel

def cell0918 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (6667 / 640 : ℚ), (133737 / 12800 : ℚ), (.chain [(8, 27)]), (.chain [(8, 27)]), (.chain [(8, 27)]), (.chain [(8, 27)]), (.chain [(8, 27), (8, 28)]), (.chain [(8, 27), (8, 28)]), .one⟩
theorem cell0918_ok : cell0918.check T = true := by decide +kernel

def cell0919 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (6667 / 640 : ℚ), (133737 / 12800 : ℚ), (.chain [(8, 27)]), (.chain [(8, 27)]), (.chain [(8, 27)]), (.chain [(8, 27)]), (.chain [(8, 27), (8, 28)]), (.chain [(8, 27), (8, 28)]), .one⟩
theorem cell0919_ok : cell0919.check T = true := by decide +kernel

def cells22 : List CellW := [cell0880, cell0881, cell0882, cell0883, cell0884, cell0885, cell0886, cell0887, cell0888, cell0889, cell0890, cell0891, cell0892, cell0893, cell0894, cell0895, cell0896, cell0897, cell0898, cell0899, cell0900, cell0901, cell0902, cell0903, cell0904, cell0905, cell0906, cell0907, cell0908, cell0909, cell0910, cell0911, cell0912, cell0913, cell0914, cell0915, cell0916, cell0917, cell0918, cell0919]

theorem cells22_valid : ∀ w ∈ cells22, w.check T = true :=
  (forall_mem_cons_of cell0880_ok (forall_mem_cons_of cell0881_ok (forall_mem_cons_of cell0882_ok (forall_mem_cons_of cell0883_ok (forall_mem_cons_of cell0884_ok (forall_mem_cons_of cell0885_ok (forall_mem_cons_of cell0886_ok (forall_mem_cons_of cell0887_ok (forall_mem_cons_of cell0888_ok (forall_mem_cons_of cell0889_ok (forall_mem_cons_of cell0890_ok (forall_mem_cons_of cell0891_ok (forall_mem_cons_of cell0892_ok (forall_mem_cons_of cell0893_ok (forall_mem_cons_of cell0894_ok (forall_mem_cons_of cell0895_ok (forall_mem_cons_of cell0896_ok (forall_mem_cons_of cell0897_ok (forall_mem_cons_of cell0898_ok (forall_mem_cons_of cell0899_ok (forall_mem_cons_of cell0900_ok (forall_mem_cons_of cell0901_ok (forall_mem_cons_of cell0902_ok (forall_mem_cons_of cell0903_ok (forall_mem_cons_of cell0904_ok (forall_mem_cons_of cell0905_ok (forall_mem_cons_of cell0906_ok (forall_mem_cons_of cell0907_ok (forall_mem_cons_of cell0908_ok (forall_mem_cons_of cell0909_ok (forall_mem_cons_of cell0910_ok (forall_mem_cons_of cell0911_ok (forall_mem_cons_of cell0912_ok (forall_mem_cons_of cell0913_ok (forall_mem_cons_of cell0914_ok (forall_mem_cons_of cell0915_ok (forall_mem_cons_of cell0916_ok (forall_mem_cons_of cell0917_ok (forall_mem_cons_of cell0918_ok (forall_mem_cons_of cell0919_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


