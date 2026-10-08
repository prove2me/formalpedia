-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells24
-- name    : CK_CKLaneC_SAxis_Data_Cells24
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T06:40:52.452988+00:00
-- url     : https://prove2.me/theorems/dc29a0cf-20d1-47e9-87d0-5d8225322a1f
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells24` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells24` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells24` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells24 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells24.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells24 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 24 (cells 960..999). -/

def cell0960 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (144853 / 12800 : ℚ), (2905 / 256 : ℚ), (.chain [(9, 17)]), (.chain [(9, 17)]), (.chain [(9, 17)]), (.chain [(9, 17), (9, 18)]), (.chain [(9, 17), (9, 18), (9, 19)]), (.chain [(9, 17), (9, 18)]), .one⟩
theorem cell0960_ok : cell0960.check T = true := by decide +kernel

def cell0961 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (2905 / 256 : ℚ), (145647 / 12800 : ℚ), (.chain [(9, 18)]), (.chain [(9, 18)]), (.chain [(9, 18)]), (.chain [(9, 18), (9, 19)]), (.chain [(9, 18), (9, 19), (9, 20)]), (.chain [(9, 18), (9, 19)]), .one⟩
theorem cell0961_ok : cell0961.check T = true := by decide +kernel

def cell0962 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (145647 / 12800 : ℚ), (36511 / 3200 : ℚ), (.chain [(9, 19)]), (.chain [(9, 19)]), (.chain [(9, 19)]), (.chain [(9, 19)]), (.chain [(9, 19), (9, 20)]), (.chain [(9, 19), (9, 20)]), .one⟩
theorem cell0962_ok : cell0962.check T = true := by decide +kernel

def cell0963 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (36511 / 3200 : ℚ), (146441 / 12800 : ℚ), (.chain [(9, 19)]), (.chain [(9, 19)]), (.chain [(9, 19)]), (.chain [(9, 19), (9, 20)]), (.chain [(9, 19), (9, 20), (9, 21)]), (.chain [(9, 19), (9, 20), (9, 21)]), .one⟩
theorem cell0963_ok : cell0963.check T = true := by decide +kernel

def cell0964 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (146441 / 12800 : ℚ), (73419 / 6400 : ℚ), (.chain [(9, 20)]), (.chain [(9, 20)]), (.chain [(9, 20)]), (.chain [(9, 20), (9, 21)]), (.chain [(9, 20), (9, 21), (9, 22)]), (.chain [(9, 20), (9, 21)]), .one⟩
theorem cell0964_ok : cell0964.check T = true := by decide +kernel

def cell0965 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (73419 / 6400 : ℚ), (29447 / 2560 : ℚ), (.chain [(9, 21)]), (.chain [(9, 21)]), (.chain [(9, 21)]), (.chain [(9, 21), (9, 22)]), (.chain [(9, 21), (9, 22), (9, 23)]), (.chain [(9, 21), (9, 22)]), .one⟩
theorem cell0965_ok : cell0965.check T = true := by decide +kernel

def cell0966 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (29447 / 2560 : ℚ), (9227 / 800 : ℚ), (.chain [(9, 22)]), (.chain [(9, 22)]), (.chain [(9, 22)]), (.chain [(9, 22)]), (.chain [(9, 22), (9, 23)]), (.chain [(9, 22), (9, 23)]), .one⟩
theorem cell0966_ok : cell0966.check T = true := by decide +kernel

def cell0967 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (9227 / 800 : ℚ), (148029 / 12800 : ℚ), (.chain [(9, 22)]), (.chain [(9, 22)]), (.chain [(9, 22)]), (.chain [(9, 22), (9, 23)]), (.chain [(9, 22), (9, 23), (9, 24)]), (.chain [(9, 22), (9, 23), (9, 24)]), .one⟩
theorem cell0967_ok : cell0967.check T = true := by decide +kernel

def cell0968 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (148029 / 12800 : ℚ), (74213 / 6400 : ℚ), (.chain [(9, 23)]), (.chain [(9, 23)]), (.chain [(9, 23)]), (.chain [(9, 23), (9, 24)]), (.chain [(9, 23), (9, 24), (9, 25)]), (.chain [(9, 23), (9, 24), (9, 25)]), .one⟩
theorem cell0968_ok : cell0968.check T = true := by decide +kernel

def cell0969 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (74213 / 6400 : ℚ), (148823 / 12800 : ℚ), (.chain [(9, 24)]), (.chain [(9, 24)]), (.chain [(9, 24)]), (.chain [(9, 24), (9, 25)]), (.chain [(9, 24), (9, 25), (9, 26)]), (.chain [(9, 24), (9, 25)]), .one⟩
theorem cell0969_ok : cell0969.check T = true := by decide +kernel

def cell0970 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (148823 / 12800 : ℚ), (7461 / 640 : ℚ), (.chain [(9, 25)]), (.chain [(9, 25)]), (.chain [(9, 25)]), (.chain [(9, 25), (9, 26)]), (.chain [(9, 25), (9, 26), (9, 27)]), (.chain [(9, 25), (9, 26)]), .one⟩
theorem cell0970_ok : cell0970.check T = true := by decide +kernel

def cell0971 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (7461 / 640 : ℚ), (149617 / 12800 : ℚ), (.chain [(9, 26)]), (.chain [(9, 26)]), (.chain [(9, 26)]), (.chain [(9, 26)]), (.chain [(9, 26), (9, 27)]), (.chain [(9, 26), (9, 27)]), .one⟩
theorem cell0971_ok : cell0971.check T = true := by decide +kernel

def cell0972 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (149617 / 12800 : ℚ), (75007 / 6400 : ℚ), (.chain [(9, 26)]), (.chain [(9, 26)]), (.chain [(9, 26)]), (.chain [(9, 26), (9, 27)]), (.chain [(9, 26), (9, 27), (9, 28)]), (.chain [(9, 26), (9, 27), (9, 28)]), .one⟩
theorem cell0972_ok : cell0972.check T = true := by decide +kernel

def cell0973 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (75007 / 6400 : ℚ), (150411 / 12800 : ℚ), (.chain [(9, 27)]), (.chain [(9, 27)]), (.chain [(9, 27)]), (.chain [(9, 27), (9, 28)]), (.chain [(9, 27), (9, 28), (9, 29)]), (.chain [(9, 27), (9, 28)]), .one⟩
theorem cell0973_ok : cell0973.check T = true := by decide +kernel

def cell0974 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (150411 / 12800 : ℚ), (18851 / 1600 : ℚ), (.chain [(9, 28)]), (.chain [(9, 28)]), (.chain [(9, 28)]), (.chain [(9, 28), (9, 29)]), (.chain [(9, 28), (9, 29), (9, 30)]), (.chain [(9, 28), (9, 29)]), .one⟩
theorem cell0974_ok : cell0974.check T = true := by decide +kernel

def cell0975 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (18851 / 1600 : ℚ), (30241 / 2560 : ℚ), (.chain [(9, 29)]), (.chain [(9, 29)]), (.chain [(9, 29)]), (.chain [(9, 29)]), (.chain [(9, 29), (9, 30)]), (.chain [(9, 29), (9, 30)]), .one⟩
theorem cell0975_ok : cell0975.check T = true := by decide +kernel

def cell0976 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (30241 / 2560 : ℚ), (75801 / 6400 : ℚ), (.chain [(9, 29)]), (.chain [(9, 29)]), (.chain [(9, 29)]), (.chain [(9, 29), (9, 30)]), (.chain [(9, 29), (9, 30), (9, 31)]), (.chain [(9, 29), (9, 30), (9, 31)]), .one⟩
theorem cell0976_ok : cell0976.check T = true := by decide +kernel

def cell0977 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (75801 / 6400 : ℚ), (151999 / 12800 : ℚ), (.chain [(9, 30)]), (.chain [(9, 30)]), (.chain [(9, 30)]), (.chain [(9, 30), (9, 31)]), (.chain [(9, 30), (9, 31), (10, 0)]), (.chain [(9, 30), (9, 31)]), .one⟩
theorem cell0977_ok : cell0977.check T = true := by decide +kernel

def cell0978 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (151999 / 12800 : ℚ), (38099 / 3200 : ℚ), (.chain [(9, 31)]), (.chain [(9, 31)]), (.chain [(9, 31)]), (.chain [(9, 31), (10, 0)]), (.chain [(9, 31), (10, 0), (10, 1)]), (.chain [(9, 31), (10, 0)]), .one⟩
theorem cell0978_ok : cell0978.check T = true := by decide +kernel

def cell0979 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (38099 / 3200 : ℚ), (152793 / 12800 : ℚ), (.chain [(10, 0)]), (.chain [(10, 0)]), (.chain [(10, 0)]), (.chain [(10, 0), (10, 1)]), (.chain [(10, 0), (10, 1), (10, 2)]), (.chain [(10, 0), (10, 1)]), .one⟩
theorem cell0979_ok : cell0979.check T = true := by decide +kernel

def cell0980 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (152793 / 12800 : ℚ), (15319 / 1280 : ℚ), (.chain [(10, 1)]), (.chain [(10, 1)]), (.chain [(10, 1)]), (.chain [(10, 1)]), (.chain [(10, 1), (10, 2)]), (.chain [(10, 1), (10, 2)]), .one⟩
theorem cell0980_ok : cell0980.check T = true := by decide +kernel

def cell0981 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (15319 / 1280 : ℚ), (153587 / 12800 : ℚ), (.chain [(10, 1)]), (.chain [(10, 1)]), (.chain [(10, 1)]), (.chain [(10, 1), (10, 2)]), (.chain [(10, 1), (10, 2), (10, 3)]), (.chain [(10, 1), (10, 2), (10, 3)]), .one⟩
theorem cell0981_ok : cell0981.check T = true := by decide +kernel

def cell0982 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (153587 / 12800 : ℚ), (1203 / 100 : ℚ), (.chain [(10, 2)]), (.chain [(10, 2)]), (.chain [(10, 2)]), (.chain [(10, 2), (10, 3)]), (.chain [(10, 2), (10, 3), (10, 4)]), (.chain [(10, 2), (10, 3)]), .one⟩
theorem cell0982_ok : cell0982.check T = true := by decide +kernel

def cell0983 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (1203 / 100 : ℚ), (154381 / 12800 : ℚ), (.chain [(10, 3)]), (.chain [(10, 3)]), (.chain [(10, 3)]), (.chain [(10, 3), (10, 4)]), (.chain [(10, 3), (10, 4), (10, 5)]), (.chain [(10, 3), (10, 4)]), .one⟩
theorem cell0983_ok : cell0983.check T = true := by decide +kernel

def cell0984 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (154381 / 12800 : ℚ), (77389 / 6400 : ℚ), (.chain [(10, 4)]), (.chain [(10, 4)]), (.chain [(10, 4)]), (.chain [(10, 4)]), (.chain [(10, 4), (10, 5)]), (.chain [(10, 4), (10, 5)]), .one⟩
theorem cell0984_ok : cell0984.check T = true := by decide +kernel

def cell0985 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (77389 / 6400 : ℚ), (6207 / 512 : ℚ), (.chain [(10, 4)]), (.chain [(10, 4)]), (.chain [(10, 4)]), (.chain [(10, 4), (10, 5)]), (.chain [(10, 4), (10, 5), (10, 6)]), (.chain [(10, 4), (10, 5), (10, 6)]), .one⟩
theorem cell0985_ok : cell0985.check T = true := by decide +kernel

def cell0986 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (6207 / 512 : ℚ), (38893 / 3200 : ℚ), (.chain [(10, 5)]), (.chain [(10, 5)]), (.chain [(10, 5)]), (.chain [(10, 5), (10, 6)]), (.chain [(10, 5), (10, 6), (10, 7)]), (.chain [(10, 5), (10, 6)]), .one⟩
theorem cell0986_ok : cell0986.check T = true := by decide +kernel

def cell0987 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (38893 / 3200 : ℚ), (155969 / 12800 : ℚ), (.chain [(10, 6)]), (.chain [(10, 6)]), (.chain [(10, 6)]), (.chain [(10, 6), (10, 7)]), (.chain [(10, 6), (10, 7), (10, 8)]), (.chain [(10, 6), (10, 7)]), .one⟩
theorem cell0987_ok : cell0987.check T = true := by decide +kernel

def cell0988 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (155969 / 12800 : ℚ), (78183 / 6400 : ℚ), (.chain [(10, 7)]), (.chain [(10, 7)]), (.chain [(10, 7)]), (.chain [(10, 7), (10, 8)]), (.chain [(10, 7), (10, 8), (10, 9)]), (.chain [(10, 7), (10, 8)]), .one⟩
theorem cell0988_ok : cell0988.check T = true := by decide +kernel

def cell0989 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (78183 / 6400 : ℚ), (156763 / 12800 : ℚ), (.chain [(10, 8)]), (.chain [(10, 8)]), (.chain [(10, 8)]), (.chain [(10, 8)]), (.chain [(10, 8), (10, 9)]), (.chain [(10, 8), (10, 9)]), .one⟩
theorem cell0989_ok : cell0989.check T = true := by decide +kernel

def cell0990 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (156763 / 12800 : ℚ), (3929 / 320 : ℚ), (.chain [(10, 8)]), (.chain [(10, 8)]), (.chain [(10, 8)]), (.chain [(10, 8), (10, 9)]), (.chain [(10, 8), (10, 9), (10, 10)]), (.chain [(10, 8), (10, 9), (10, 10)]), .one⟩
theorem cell0990_ok : cell0990.check T = true := by decide +kernel

def cell0991 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (3929 / 320 : ℚ), (157557 / 12800 : ℚ), (.chain [(10, 9)]), (.chain [(10, 9)]), (.chain [(10, 9)]), (.chain [(10, 9), (10, 10)]), (.chain [(10, 9), (10, 10), (10, 11)]), (.chain [(10, 9), (10, 10)]), .one⟩
theorem cell0991_ok : cell0991.check T = true := by decide +kernel

def cell0992 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (157557 / 12800 : ℚ), (78977 / 6400 : ℚ), (.chain [(10, 10)]), (.chain [(10, 10)]), (.chain [(10, 10)]), (.chain [(10, 10), (10, 11)]), (.chain [(10, 10), (10, 11), (10, 12)]), (.chain [(10, 10), (10, 11)]), .one⟩
theorem cell0992_ok : cell0992.check T = true := by decide +kernel

def cell0993 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (78977 / 6400 : ℚ), (158351 / 12800 : ℚ), (.chain [(10, 11)]), (.chain [(10, 11)]), (.chain [(10, 11)]), (.chain [(10, 11)]), (.chain [(10, 11), (10, 12)]), (.chain [(10, 11), (10, 12)]), .one⟩
theorem cell0993_ok : cell0993.check T = true := by decide +kernel

def cell0994 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (158351 / 12800 : ℚ), (39687 / 3200 : ℚ), (.chain [(10, 11)]), (.chain [(10, 11)]), (.chain [(10, 11)]), (.chain [(10, 11), (10, 12)]), (.chain [(10, 11), (10, 12), (10, 13)]), (.chain [(10, 11), (10, 12), (10, 13)]), .one⟩
theorem cell0994_ok : cell0994.check T = true := by decide +kernel

def cell0995 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (39687 / 3200 : ℚ), (31829 / 2560 : ℚ), (.chain [(10, 12)]), (.chain [(10, 12)]), (.chain [(10, 12)]), (.chain [(10, 12), (10, 13)]), (.chain [(10, 12), (10, 13), (10, 14)]), (.chain [(10, 12), (10, 13)]), .one⟩
theorem cell0995_ok : cell0995.check T = true := by decide +kernel

def cell0996 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (31829 / 2560 : ℚ), (79771 / 6400 : ℚ), (.chain [(10, 13)]), (.chain [(10, 13)]), (.chain [(10, 13)]), (.chain [(10, 13), (10, 14)]), (.chain [(10, 13), (10, 14), (10, 15)]), (.chain [(10, 13), (10, 14)]), .one⟩
theorem cell0996_ok : cell0996.check T = true := by decide +kernel

def cell0997 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (79771 / 6400 : ℚ), (159939 / 12800 : ℚ), (.chain [(10, 14)]), (.chain [(10, 14)]), (.chain [(10, 14)]), (.chain [(10, 14), (10, 15)]), (.chain [(10, 14), (10, 15), (10, 16)]), (.chain [(10, 14), (10, 15)]), .one⟩
theorem cell0997_ok : cell0997.check T = true := by decide +kernel

def cell0998 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (159939 / 12800 : ℚ), (10021 / 800 : ℚ), (.chain [(10, 15)]), (.chain [(10, 15)]), (.chain [(10, 15)]), (.chain [(10, 15)]), (.chain [(10, 15), (10, 16)]), (.chain [(10, 15), (10, 16)]), .one⟩
theorem cell0998_ok : cell0998.check T = true := by decide +kernel

def cell0999 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (10021 / 800 : ℚ), (160733 / 12800 : ℚ), (.chain [(10, 15)]), (.chain [(10, 15)]), (.chain [(10, 15)]), (.chain [(10, 15), (10, 16)]), (.chain [(10, 15), (10, 16), (10, 17)]), (.chain [(10, 15), (10, 16), (10, 17)]), .one⟩
theorem cell0999_ok : cell0999.check T = true := by decide +kernel

def cells24 : List CellW := [cell0960, cell0961, cell0962, cell0963, cell0964, cell0965, cell0966, cell0967, cell0968, cell0969, cell0970, cell0971, cell0972, cell0973, cell0974, cell0975, cell0976, cell0977, cell0978, cell0979, cell0980, cell0981, cell0982, cell0983, cell0984, cell0985, cell0986, cell0987, cell0988, cell0989, cell0990, cell0991, cell0992, cell0993, cell0994, cell0995, cell0996, cell0997, cell0998, cell0999]

theorem cells24_valid : ∀ w ∈ cells24, w.check T = true :=
  (forall_mem_cons_of cell0960_ok (forall_mem_cons_of cell0961_ok (forall_mem_cons_of cell0962_ok (forall_mem_cons_of cell0963_ok (forall_mem_cons_of cell0964_ok (forall_mem_cons_of cell0965_ok (forall_mem_cons_of cell0966_ok (forall_mem_cons_of cell0967_ok (forall_mem_cons_of cell0968_ok (forall_mem_cons_of cell0969_ok (forall_mem_cons_of cell0970_ok (forall_mem_cons_of cell0971_ok (forall_mem_cons_of cell0972_ok (forall_mem_cons_of cell0973_ok (forall_mem_cons_of cell0974_ok (forall_mem_cons_of cell0975_ok (forall_mem_cons_of cell0976_ok (forall_mem_cons_of cell0977_ok (forall_mem_cons_of cell0978_ok (forall_mem_cons_of cell0979_ok (forall_mem_cons_of cell0980_ok (forall_mem_cons_of cell0981_ok (forall_mem_cons_of cell0982_ok (forall_mem_cons_of cell0983_ok (forall_mem_cons_of cell0984_ok (forall_mem_cons_of cell0985_ok (forall_mem_cons_of cell0986_ok (forall_mem_cons_of cell0987_ok (forall_mem_cons_of cell0988_ok (forall_mem_cons_of cell0989_ok (forall_mem_cons_of cell0990_ok (forall_mem_cons_of cell0991_ok (forall_mem_cons_of cell0992_ok (forall_mem_cons_of cell0993_ok (forall_mem_cons_of cell0994_ok (forall_mem_cons_of cell0995_ok (forall_mem_cons_of cell0996_ok (forall_mem_cons_of cell0997_ok (forall_mem_cons_of cell0998_ok (forall_mem_cons_of cell0999_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


