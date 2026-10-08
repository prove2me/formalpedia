-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells23
-- name    : CK_CKLaneC_SAxis_Data_Cells23
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T06:35:12.69992+00:00
-- url     : https://prove2.me/theorems/f7f45007-744e-40ef-8aaa-8d704ea1457e
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells23` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells23` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells23` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells23 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells23.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells23 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 23 (cells 920..959). -/

def cell0920 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (133737 / 12800 : ℚ), (67067 / 6400 : ℚ), (.chain [(8, 27)]), (.chain [(8, 27)]), (.chain [(8, 27)]), (.chain [(8, 27), (8, 28)]), (.chain [(8, 27), (8, 28), (8, 29)]), (.chain [(8, 27), (8, 28)]), .one⟩
theorem cell0920_ok : cell0920.check T = true := by decide +kernel

def cell0921 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (133737 / 12800 : ℚ), (67067 / 6400 : ℚ), (.chain [(8, 27)]), (.chain [(8, 28)]), (.chain [(8, 28)]), (.chain [(8, 27), (8, 28)]), (.chain [(8, 28), (8, 29)]), (.chain [(8, 28), (8, 29)]), .one⟩
theorem cell0921_ok : cell0921.check T = true := by decide +kernel

def cell0922 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (67067 / 6400 : ℚ), (134531 / 12800 : ℚ), (.chain [(8, 28)]), (.chain [(8, 28)]), (.chain [(8, 28)]), (.chain [(8, 28), (8, 29)]), (.chain [(8, 28), (8, 29)]), (.chain [(8, 28), (8, 29)]), .one⟩
theorem cell0922_ok : cell0922.check T = true := by decide +kernel

def cell0923 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (67067 / 6400 : ℚ), (134531 / 12800 : ℚ), (.chain [(8, 28)]), (.chain [(8, 29)]), (.chain [(8, 28)]), (.chain [(8, 28), (8, 29)]), (.chain [(8, 29), (8, 30)]), (.chain [(8, 28), (8, 29)]), .one⟩
theorem cell0923_ok : cell0923.check T = true := by decide +kernel

def cell0924 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (134531 / 12800 : ℚ), (8433 / 800 : ℚ), (.chain [(8, 29)]), (.chain [(8, 29)]), (.chain [(8, 29)]), (.chain [(8, 29), (8, 30)]), (.chain [(8, 29), (8, 30)]), (.chain [(8, 29), (8, 30)]), .one⟩
theorem cell0924_ok : cell0924.check T = true := by decide +kernel

def cell0925 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (134531 / 12800 : ℚ), (8433 / 800 : ℚ), (.chain [(8, 29)]), (.chain [(8, 29)]), (.chain [(8, 29)]), (.chain [(8, 29), (8, 30)]), (.chain [(8, 29), (8, 30), (8, 31)]), (.chain [(8, 29), (8, 30)]), .one⟩
theorem cell0925_ok : cell0925.check T = true := by decide +kernel

def cell0926 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (8433 / 800 : ℚ), (5413 / 512 : ℚ), (.chain [(8, 30)]), (.chain [(8, 30)]), (.chain [(8, 30)]), (.chain [(8, 30)]), (.chain [(8, 30), (8, 31)]), (.chain [(8, 30), (8, 31)]), .one⟩
theorem cell0926_ok : cell0926.check T = true := by decide +kernel

def cell0927 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (8433 / 800 : ℚ), (5413 / 512 : ℚ), (.chain [(8, 30)]), (.chain [(8, 30)]), (.chain [(8, 30)]), (.chain [(8, 30)]), (.chain [(8, 30), (8, 31)]), (.chain [(8, 30), (8, 31)]), .one⟩
theorem cell0927_ok : cell0927.check T = true := by decide +kernel

def cell0928 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (5413 / 512 : ℚ), (67861 / 6400 : ℚ), (.chain [(8, 30)]), (.chain [(8, 30)]), (.chain [(8, 30)]), (.chain [(8, 30), (8, 31)]), (.chain [(8, 30), (8, 31), (9, 0)]), (.chain [(8, 30), (8, 31)]), .one⟩
theorem cell0928_ok : cell0928.check T = true := by decide +kernel

def cell0929 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (5413 / 512 : ℚ), (67861 / 6400 : ℚ), (.chain [(8, 30)]), (.chain [(8, 31)]), (.chain [(8, 31)]), (.chain [(8, 30), (8, 31)]), (.chain [(8, 31), (9, 0)]), (.chain [(8, 31), (9, 0)]), .one⟩
theorem cell0929_ok : cell0929.check T = true := by decide +kernel

def cell0930 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (67861 / 6400 : ℚ), (136119 / 12800 : ℚ), (.chain [(8, 31)]), (.chain [(8, 31)]), (.chain [(8, 31)]), (.chain [(8, 31), (9, 0)]), (.chain [(8, 31), (9, 0)]), (.chain [(8, 31), (9, 0)]), .one⟩
theorem cell0930_ok : cell0930.check T = true := by decide +kernel

def cell0931 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (67861 / 6400 : ℚ), (136119 / 12800 : ℚ), (.chain [(8, 31)]), (.chain [(9, 0)]), (.chain [(8, 31)]), (.chain [(8, 31), (9, 0)]), (.chain [(9, 0), (9, 1)]), (.chain [(8, 31), (9, 0)]), .one⟩
theorem cell0931_ok : cell0931.check T = true := by decide +kernel

def cell0932 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (136119 / 12800 : ℚ), (34129 / 3200 : ℚ), (.chain [(9, 0)]), (.chain [(9, 0)]), (.chain [(9, 0)]), (.chain [(9, 0), (9, 1)]), (.chain [(9, 0), (9, 1), (9, 2)]), (.chain [(9, 0), (9, 1)]), .one⟩
theorem cell0932_ok : cell0932.check T = true := by decide +kernel

def cell0933 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (34129 / 3200 : ℚ), (136913 / 12800 : ℚ), (.chain [(9, 1)]), (.chain [(9, 1)]), (.chain [(9, 1)]), (.chain [(9, 1), (9, 2)]), (.chain [(9, 1), (9, 2)]), (.chain [(9, 1), (9, 2)]), .one⟩
theorem cell0933_ok : cell0933.check T = true := by decide +kernel

def cell0934 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (34129 / 3200 : ℚ), (136913 / 12800 : ℚ), (.chain [(9, 1)]), (.chain [(9, 1)]), (.chain [(9, 1)]), (.chain [(9, 1), (9, 2)]), (.chain [(9, 1), (9, 2), (9, 3)]), (.chain [(9, 1), (9, 2)]), .one⟩
theorem cell0934_ok : cell0934.check T = true := by decide +kernel

def cell0935 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (136913 / 12800 : ℚ), (13731 / 1280 : ℚ), (.chain [(9, 2)]), (.chain [(9, 2)]), (.chain [(9, 2)]), (.chain [(9, 2)]), (.chain [(9, 2), (9, 3)]), (.chain [(9, 2), (9, 3)]), .one⟩
theorem cell0935_ok : cell0935.check T = true := by decide +kernel

def cell0936 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (136913 / 12800 : ℚ), (13731 / 1280 : ℚ), (.chain [(9, 2)]), (.chain [(9, 2)]), (.chain [(9, 2)]), (.chain [(9, 2)]), (.chain [(9, 2), (9, 3)]), (.chain [(9, 2), (9, 3)]), .one⟩
theorem cell0936_ok : cell0936.check T = true := by decide +kernel

def cell0937 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (13731 / 1280 : ℚ), (137707 / 12800 : ℚ), (.chain [(9, 2)]), (.chain [(9, 2)]), (.chain [(9, 2)]), (.chain [(9, 2), (9, 3)]), (.chain [(9, 2), (9, 3), (9, 4)]), (.chain [(9, 2), (9, 3)]), .one⟩
theorem cell0937_ok : cell0937.check T = true := by decide +kernel

def cell0938 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (13731 / 1280 : ℚ), (137707 / 12800 : ℚ), (.chain [(9, 2)]), (.chain [(9, 3)]), (.chain [(9, 3)]), (.chain [(9, 2), (9, 3)]), (.chain [(9, 3), (9, 4)]), (.chain [(9, 3), (9, 4)]), .one⟩
theorem cell0938_ok : cell0938.check T = true := by decide +kernel

def cell0939 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (137707 / 12800 : ℚ), (17263 / 1600 : ℚ), (.chain [(9, 3)]), (.chain [(9, 3)]), (.chain [(9, 3)]), (.chain [(9, 3), (9, 4)]), (.chain [(9, 3), (9, 4), (9, 5)]), (.chain [(9, 3), (9, 4)]), .one⟩
theorem cell0939_ok : cell0939.check T = true := by decide +kernel

def cell0940 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (17263 / 1600 : ℚ), (138501 / 12800 : ℚ), (.chain [(9, 4)]), (.chain [(9, 4)]), (.chain [(9, 4)]), (.chain [(9, 4), (9, 5)]), (.chain [(9, 4), (9, 5), (9, 6)]), (.chain [(9, 4), (9, 5)]), .one⟩
theorem cell0940_ok : cell0940.check T = true := by decide +kernel

def cell0941 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (138501 / 12800 : ℚ), (69449 / 6400 : ℚ), (.chain [(9, 5)]), (.chain [(9, 5)]), (.chain [(9, 5)]), (.chain [(9, 5)]), (.chain [(9, 5), (9, 6)]), (.chain [(9, 5), (9, 6)]), .one⟩
theorem cell0941_ok : cell0941.check T = true := by decide +kernel

def cell0942 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (69449 / 6400 : ℚ), (27859 / 2560 : ℚ), (.chain [(9, 5)]), (.chain [(9, 5)]), (.chain [(9, 5)]), (.chain [(9, 5), (9, 6)]), (.chain [(9, 5), (9, 6), (9, 7)]), (.chain [(9, 5), (9, 6)]), .one⟩
theorem cell0942_ok : cell0942.check T = true := by decide +kernel

def cell0943 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (69449 / 6400 : ℚ), (27859 / 2560 : ℚ), (.chain [(9, 5)]), (.chain [(9, 6)]), (.chain [(9, 6)]), (.chain [(9, 5), (9, 6)]), (.chain [(9, 6), (9, 7)]), (.chain [(9, 6), (9, 7)]), .one⟩
theorem cell0943_ok : cell0943.check T = true := by decide +kernel

def cell0944 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (27859 / 2560 : ℚ), (34923 / 3200 : ℚ), (.chain [(9, 6)]), (.chain [(9, 6)]), (.chain [(9, 6)]), (.chain [(9, 6), (9, 7)]), (.chain [(9, 6), (9, 7), (9, 8)]), (.chain [(9, 6), (9, 7)]), .one⟩
theorem cell0944_ok : cell0944.check T = true := by decide +kernel

def cell0945 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (34923 / 3200 : ℚ), (140089 / 12800 : ℚ), (.chain [(9, 7)]), (.chain [(9, 7)]), (.chain [(9, 7)]), (.chain [(9, 7), (9, 8)]), (.chain [(9, 7), (9, 8), (9, 9)]), (.chain [(9, 7), (9, 8)]), .one⟩
theorem cell0945_ok : cell0945.check T = true := by decide +kernel

def cell0946 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (140089 / 12800 : ℚ), (70243 / 6400 : ℚ), (.chain [(9, 8)]), (.chain [(9, 8)]), (.chain [(9, 8)]), (.chain [(9, 8), (9, 9)]), (.chain [(9, 8), (9, 9), (9, 10)]), (.chain [(9, 8), (9, 9)]), .one⟩
theorem cell0946_ok : cell0946.check T = true := by decide +kernel

def cell0947 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (70243 / 6400 : ℚ), (140883 / 12800 : ℚ), (.chain [(9, 9)]), (.chain [(9, 9)]), (.chain [(9, 9)]), (.chain [(9, 9)]), (.chain [(9, 9), (9, 10)]), (.chain [(9, 9), (9, 10)]), .one⟩
theorem cell0947_ok : cell0947.check T = true := by decide +kernel

def cell0948 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (70243 / 6400 : ℚ), (140883 / 12800 : ℚ), (.chain [(9, 9)]), (.chain [(9, 9)]), (.chain [(9, 9)]), (.chain [(9, 9)]), (.chain [(9, 9), (9, 10)]), (.chain [(9, 9), (9, 10)]), .one⟩
theorem cell0948_ok : cell0948.check T = true := by decide +kernel

def cell0949 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (140883 / 12800 : ℚ), (883 / 80 : ℚ), (.chain [(9, 9)]), (.chain [(9, 9)]), (.chain [(9, 9)]), (.chain [(9, 9), (9, 10)]), (.chain [(9, 9), (9, 10), (9, 11)]), (.chain [(9, 9), (9, 10), (9, 11)]), .one⟩
theorem cell0949_ok : cell0949.check T = true := by decide +kernel

def cell0950 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (883 / 80 : ℚ), (141677 / 12800 : ℚ), (.chain [(9, 10)]), (.chain [(9, 10)]), (.chain [(9, 10)]), (.chain [(9, 10), (9, 11)]), (.chain [(9, 10), (9, 11), (9, 12)]), (.chain [(9, 10), (9, 11)]), .one⟩
theorem cell0950_ok : cell0950.check T = true := by decide +kernel

def cell0951 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (141677 / 12800 : ℚ), (71037 / 6400 : ℚ), (.chain [(9, 11)]), (.chain [(9, 11)]), (.chain [(9, 11)]), (.chain [(9, 11), (9, 12)]), (.chain [(9, 11), (9, 12), (9, 13)]), (.chain [(9, 11), (9, 12)]), .one⟩
theorem cell0951_ok : cell0951.check T = true := by decide +kernel

def cell0952 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (71037 / 6400 : ℚ), (142471 / 12800 : ℚ), (.chain [(9, 12)]), (.chain [(9, 12)]), (.chain [(9, 12)]), (.chain [(9, 12)]), (.chain [(9, 12), (9, 13)]), (.chain [(9, 12), (9, 13)]), .one⟩
theorem cell0952_ok : cell0952.check T = true := by decide +kernel

def cell0953 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (142471 / 12800 : ℚ), (35717 / 3200 : ℚ), (.chain [(9, 12)]), (.chain [(9, 12)]), (.chain [(9, 12)]), (.chain [(9, 12), (9, 13)]), (.chain [(9, 12), (9, 13), (9, 14)]), (.chain [(9, 12), (9, 13), (9, 14)]), .one⟩
theorem cell0953_ok : cell0953.check T = true := by decide +kernel

def cell0954 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (35717 / 3200 : ℚ), (28653 / 2560 : ℚ), (.chain [(9, 13)]), (.chain [(9, 13)]), (.chain [(9, 13)]), (.chain [(9, 13), (9, 14)]), (.chain [(9, 13), (9, 14), (9, 15)]), (.chain [(9, 13), (9, 14)]), .one⟩
theorem cell0954_ok : cell0954.check T = true := by decide +kernel

def cell0955 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (28653 / 2560 : ℚ), (71831 / 6400 : ℚ), (.chain [(9, 14)]), (.chain [(9, 14)]), (.chain [(9, 14)]), (.chain [(9, 14), (9, 15)]), (.chain [(9, 14), (9, 15), (9, 16)]), (.chain [(9, 14), (9, 15)]), .one⟩
theorem cell0955_ok : cell0955.check T = true := by decide +kernel

def cell0956 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (71831 / 6400 : ℚ), (144059 / 12800 : ℚ), (.chain [(9, 15)]), (.chain [(9, 15)]), (.chain [(9, 15)]), (.chain [(9, 15)]), (.chain [(9, 15), (9, 16)]), (.chain [(9, 15), (9, 16)]), .one⟩
theorem cell0956_ok : cell0956.check T = true := by decide +kernel

def cell0957 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (144059 / 12800 : ℚ), (18057 / 1600 : ℚ), (.chain [(9, 15)]), (.chain [(9, 15)]), (.chain [(9, 15)]), (.chain [(9, 15), (9, 16)]), (.chain [(9, 15), (9, 16), (9, 17)]), (.chain [(9, 15), (9, 16), (9, 17)]), .one⟩
theorem cell0957_ok : cell0957.check T = true := by decide +kernel

def cell0958 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (144059 / 12800 : ℚ), (18057 / 1600 : ℚ), (.chain [(9, 15)]), (.chain [(9, 16)]), (.chain [(9, 16)]), (.chain [(9, 15), (9, 16)]), (.chain [(9, 16), (9, 17)]), (.chain [(9, 16), (9, 17)]), .one⟩
theorem cell0958_ok : cell0958.check T = true := by decide +kernel

def cell0959 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (18057 / 1600 : ℚ), (144853 / 12800 : ℚ), (.chain [(9, 16)]), (.chain [(9, 16)]), (.chain [(9, 16)]), (.chain [(9, 16), (9, 17)]), (.chain [(9, 16), (9, 17), (9, 18)]), (.chain [(9, 16), (9, 17), (9, 18)]), .one⟩
theorem cell0959_ok : cell0959.check T = true := by decide +kernel

def cells23 : List CellW := [cell0920, cell0921, cell0922, cell0923, cell0924, cell0925, cell0926, cell0927, cell0928, cell0929, cell0930, cell0931, cell0932, cell0933, cell0934, cell0935, cell0936, cell0937, cell0938, cell0939, cell0940, cell0941, cell0942, cell0943, cell0944, cell0945, cell0946, cell0947, cell0948, cell0949, cell0950, cell0951, cell0952, cell0953, cell0954, cell0955, cell0956, cell0957, cell0958, cell0959]

theorem cells23_valid : ∀ w ∈ cells23, w.check T = true :=
  (forall_mem_cons_of cell0920_ok (forall_mem_cons_of cell0921_ok (forall_mem_cons_of cell0922_ok (forall_mem_cons_of cell0923_ok (forall_mem_cons_of cell0924_ok (forall_mem_cons_of cell0925_ok (forall_mem_cons_of cell0926_ok (forall_mem_cons_of cell0927_ok (forall_mem_cons_of cell0928_ok (forall_mem_cons_of cell0929_ok (forall_mem_cons_of cell0930_ok (forall_mem_cons_of cell0931_ok (forall_mem_cons_of cell0932_ok (forall_mem_cons_of cell0933_ok (forall_mem_cons_of cell0934_ok (forall_mem_cons_of cell0935_ok (forall_mem_cons_of cell0936_ok (forall_mem_cons_of cell0937_ok (forall_mem_cons_of cell0938_ok (forall_mem_cons_of cell0939_ok (forall_mem_cons_of cell0940_ok (forall_mem_cons_of cell0941_ok (forall_mem_cons_of cell0942_ok (forall_mem_cons_of cell0943_ok (forall_mem_cons_of cell0944_ok (forall_mem_cons_of cell0945_ok (forall_mem_cons_of cell0946_ok (forall_mem_cons_of cell0947_ok (forall_mem_cons_of cell0948_ok (forall_mem_cons_of cell0949_ok (forall_mem_cons_of cell0950_ok (forall_mem_cons_of cell0951_ok (forall_mem_cons_of cell0952_ok (forall_mem_cons_of cell0953_ok (forall_mem_cons_of cell0954_ok (forall_mem_cons_of cell0955_ok (forall_mem_cons_of cell0956_ok (forall_mem_cons_of cell0957_ok (forall_mem_cons_of cell0958_ok (forall_mem_cons_of cell0959_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


