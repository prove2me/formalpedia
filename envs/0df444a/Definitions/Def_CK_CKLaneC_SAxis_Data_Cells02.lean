-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells02
-- name    : CK_CKLaneC_SAxis_Data_Cells02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T07:26:25.507266+00:00
-- url     : https://prove2.me/theorems/60762cb5-7fe8-4aa4-bfac-662e9a52157e
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells02` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells02` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells02` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells02 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells02.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells02 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 2 (cells 80..119). -/

def cell0080 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (13687 / 51200 : ℚ), (3521 / 12800 : ℚ), (.chain [(0, 20)]), (.chain [(0, 20)]), (.chain [(0, 20)]), (.chain [(0, 20)]), (.chain [(0, 20), (0, 21)]), (.chain [(0, 20), (0, 21)]), .three⟩
theorem cell0080_ok : cell0080.check T = true := by decide +kernel

def cell0081 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (1329 / 5120 : ℚ), (13687 / 51200 : ℚ), (.chain [(0, 19)]), (.chain [(0, 20)]), (.chain [(0, 19)]), (.chain [(0, 19), (0, 20)]), (.chain [(0, 20), (0, 21)]), (.chain [(0, 19), (0, 20)]), .three⟩
theorem cell0081_ok : cell0081.check T = true := by decide +kernel

def cell0082 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (13687 / 51200 : ℚ), (3521 / 12800 : ℚ), (.chain [(0, 20)]), (.chain [(0, 20)]), (.chain [(0, 20)]), (.chain [(0, 20)]), (.chain [(0, 20), (0, 21), (0, 22)]), (.chain [(0, 20), (0, 21)]), .three⟩
theorem cell0082_ok : cell0082.check T = true := by decide +kernel

def cell0083 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (781 / 3200 : ℚ), (1329 / 5120 : ℚ), (.chain [(0, 18)]), (.chain [(0, 19)]), (.chain [(0, 19)]), (.chain [(0, 18), (0, 19)]), (.chain [(0, 19), (0, 20), (0, 21)]), (.chain [(0, 19), (0, 20)]), .two⟩
theorem cell0083_ok : cell0083.check T = true := by decide +kernel

def cell0084 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (781 / 3200 : ℚ), (1329 / 5120 : ℚ), (.chain [(0, 18)]), (.chain [(0, 20)]), (.chain [(0, 19)]), (.chain [(0, 18), (0, 19)]), (.chain [(0, 20), (0, 21), (0, 22)]), (.chain [(0, 19), (0, 20), (0, 21)]), .three⟩
theorem cell0084_ok : cell0084.check T = true := by decide +kernel

def cell0085 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (1329 / 5120 : ℚ), (3521 / 12800 : ℚ), (.chain [(0, 19)]), (.chain [(0, 21)]), (.chain [(0, 20)]), (.chain [(0, 19), (0, 20)]), (.chain [(0, 21), (0, 22)]), (.chain [(0, 20), (0, 21)]), .two⟩
theorem cell0085_ok : cell0085.check T = true := by decide +kernel

def cell0086 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (1329 / 5120 : ℚ), (3521 / 12800 : ℚ), (.chain [(0, 19)]), (.chain [(0, 21)]), (.chain [(0, 20)]), (.chain [(0, 19), (0, 20)]), (.chain [(0, 21), (0, 22), (0, 23)]), (.chain [(0, 20), (0, 21), (0, 22)]), .two⟩
theorem cell0086_ok : cell0086.check T = true := by decide +kernel

def cell0087 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (3521 / 12800 : ℚ), (14481 / 51200 : ℚ), (.chain [(0, 20)]), (.chain [(0, 20)]), (.chain [(0, 20)]), (.chain [(0, 20), (0, 21)]), (.chain [(0, 20), (0, 21), (0, 22)]), (.chain [(0, 20), (0, 21)]), .three⟩
theorem cell0087_ok : cell0087.check T = true := by decide +kernel

def cell0088 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (14481 / 51200 : ℚ), (7439 / 25600 : ℚ), (.chain [(0, 21)]), (.chain [(0, 21)]), (.chain [(0, 21)]), (.chain [(0, 21)]), (.chain [(0, 21), (0, 22)]), (.chain [(0, 21), (0, 22)]), .three⟩
theorem cell0088_ok : cell0088.check T = true := by decide +kernel

def cell0089 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (3521 / 12800 : ℚ), (7439 / 25600 : ℚ), (.chain [(0, 20)]), (.chain [(0, 21)]), (.chain [(0, 21)]), (.chain [(0, 20), (0, 21)]), (.chain [(0, 21), (0, 22), (0, 23)]), (.chain [(0, 21), (0, 22)]), .three⟩
theorem cell0089_ok : cell0089.check T = true := by decide +kernel

def cell0090 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (7439 / 25600 : ℚ), (611 / 2048 : ℚ), (.chain [(0, 21)]), (.chain [(0, 21)]), (.chain [(0, 21)]), (.chain [(0, 21), (0, 22)]), (.chain [(0, 21), (0, 22), (0, 23)]), (.chain [(0, 21), (0, 22)]), .three⟩
theorem cell0090_ok : cell0090.check T = true := by decide +kernel

def cell0091 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (611 / 2048 : ℚ), (1959 / 6400 : ℚ), (.chain [(0, 22)]), (.chain [(0, 22)]), (.chain [(0, 22)]), (.chain [(0, 22)]), (.chain [(0, 22), (0, 23)]), (.chain [(0, 22), (0, 23)]), .three⟩
theorem cell0091_ok : cell0091.check T = true := by decide +kernel

def cell0092 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (7439 / 25600 : ℚ), (1959 / 6400 : ℚ), (.chain [(0, 21)]), (.chain [(0, 22)]), (.chain [(0, 22)]), (.chain [(0, 21), (0, 22)]), (.chain [(0, 22), (0, 23), (0, 24)]), (.chain [(0, 22), (0, 23)]), .three⟩
theorem cell0092_ok : cell0092.check T = true := by decide +kernel

def cell0093 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (3521 / 12800 : ℚ), (7439 / 25600 : ℚ), (.chain [(0, 20)]), (.chain [(0, 22)]), (.chain [(0, 21)]), (.chain [(0, 20), (0, 21)]), (.chain [(0, 22), (0, 23)]), (.chain [(0, 21), (0, 22)]), .two⟩
theorem cell0093_ok : cell0093.check T = true := by decide +kernel

def cell0094 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (3521 / 12800 : ℚ), (7439 / 25600 : ℚ), (.chain [(0, 20)]), (.chain [(0, 22)]), (.chain [(0, 21)]), (.chain [(0, 20), (0, 21)]), (.chain [(0, 22), (0, 23), (0, 24)]), (.chain [(0, 21), (0, 22), (0, 23)]), .two⟩
theorem cell0094_ok : cell0094.check T = true := by decide +kernel

def cell0095 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (7439 / 25600 : ℚ), (611 / 2048 : ℚ), (.chain [(0, 21)]), (.chain [(0, 23)]), (.chain [(0, 22)]), (.chain [(0, 21), (0, 22)]), (.chain [(0, 23), (0, 24)]), (.chain [(0, 22), (0, 23)]), .two⟩
theorem cell0095_ok : cell0095.check T = true := by decide +kernel

def cell0096 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (611 / 2048 : ℚ), (1959 / 6400 : ℚ), (.chain [(0, 22)]), (.chain [(0, 23)]), (.chain [(0, 23)]), (.chain [(0, 22)]), (.chain [(0, 23), (0, 24), (0, 25)]), (.chain [(0, 23), (0, 24)]), .two⟩
theorem cell0096_ok : cell0096.check T = true := by decide +kernel

def cell0097 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (1959 / 6400 : ℚ), (16069 / 51200 : ℚ), (.chain [(0, 22)]), (.chain [(0, 22)]), (.chain [(0, 22)]), (.chain [(0, 22), (0, 23)]), (.chain [(0, 22), (0, 23), (0, 24)]), (.chain [(0, 22), (0, 23)]), .three⟩
theorem cell0097_ok : cell0097.check T = true := by decide +kernel

def cell0098 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (16069 / 51200 : ℚ), (8233 / 25600 : ℚ), (.chain [(0, 23)]), (.chain [(0, 23)]), (.chain [(0, 23)]), (.chain [(0, 23)]), (.chain [(0, 23), (0, 24)]), (.chain [(0, 23), (0, 24)]), .three⟩
theorem cell0098_ok : cell0098.check T = true := by decide +kernel

def cell0099 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (1959 / 6400 : ℚ), (8233 / 25600 : ℚ), (.chain [(0, 22)]), (.chain [(0, 23)]), (.chain [(0, 23)]), (.chain [(0, 22), (0, 23)]), (.chain [(0, 23), (0, 24), (0, 25)]), (.chain [(0, 23), (0, 24)]), .three⟩
theorem cell0099_ok : cell0099.check T = true := by decide +kernel

def cell0100 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (8233 / 25600 : ℚ), (863 / 2560 : ℚ), (.chain [(0, 23)]), (.chain [(0, 23)]), (.chain [(0, 23)]), (.chain [(0, 23), (0, 24)]), (.chain [(0, 23), (0, 24), (0, 25)]), (.chain [(0, 23), (0, 24), (0, 25)]), .two⟩
theorem cell0100_ok : cell0100.check T = true := by decide +kernel

def cell0101 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (8233 / 25600 : ℚ), (863 / 2560 : ℚ), (.chain [(0, 23)]), (.chain [(0, 24)]), (.chain [(0, 24)]), (.chain [(0, 23), (0, 24)]), (.chain [(0, 24), (0, 25), (0, 26)]), (.chain [(0, 24), (0, 25)]), .three⟩
theorem cell0101_ok : cell0101.check T = true := by decide +kernel

def cell0102 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (1959 / 6400 : ℚ), (16069 / 51200 : ℚ), (.chain [(0, 22)]), (.chain [(0, 24)]), (.chain [(0, 23)]), (.chain [(0, 22), (0, 23)]), (.chain [(0, 24), (0, 25)]), (.chain [(0, 23), (0, 24)]), .two⟩
theorem cell0102_ok : cell0102.check T = true := by decide +kernel

def cell0103 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (16069 / 51200 : ℚ), (8233 / 25600 : ℚ), (.chain [(0, 23)]), (.chain [(0, 24)]), (.chain [(0, 24)]), (.chain [(0, 23)]), (.chain [(0, 24), (0, 25), (0, 26)]), (.chain [(0, 24), (0, 25)]), .two⟩
theorem cell0103_ok : cell0103.check T = true := by decide +kernel

def cell0104 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (8233 / 25600 : ℚ), (863 / 2560 : ℚ), (.chain [(0, 23)]), (.chain [(0, 25)]), (.chain [(0, 24)]), (.chain [(0, 23), (0, 24)]), (.chain [(0, 25), (0, 26)]), (.chain [(0, 24), (0, 25)]), .three⟩
theorem cell0104_ok : cell0104.check T = true := by decide +kernel

def cell0105 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (8233 / 25600 : ℚ), (863 / 2560 : ℚ), (.chain [(0, 23)]), (.chain [(0, 25)]), (.chain [(0, 24)]), (.chain [(0, 23), (0, 24)]), (.chain [(0, 25), (0, 26), (0, 27)]), (.chain [(0, 24), (0, 25), (0, 26)]), .three⟩
theorem cell0105_ok : cell0105.check T = true := by decide +kernel

def cell0106 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (863 / 2560 : ℚ), (9027 / 25600 : ℚ), (.chain [(0, 24)]), (.chain [(0, 24)]), (.chain [(0, 24)]), (.chain [(0, 24), (0, 25)]), (.chain [(0, 24), (0, 25), (0, 26)]), (.chain [(0, 24), (0, 25), (0, 26)]), .two⟩
theorem cell0106_ok : cell0106.check T = true := by decide +kernel

def cell0107 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (863 / 2560 : ℚ), (9027 / 25600 : ℚ), (.chain [(0, 24)]), (.chain [(0, 25)]), (.chain [(0, 25)]), (.chain [(0, 24), (0, 25)]), (.chain [(0, 25), (0, 26)]), (.chain [(0, 25), (0, 26)]), .three⟩
theorem cell0107_ok : cell0107.check T = true := by decide +kernel

def cell0108 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (9027 / 25600 : ℚ), (589 / 1600 : ℚ), (.chain [(0, 25)]), (.chain [(0, 25)]), (.chain [(0, 25)]), (.chain [(0, 25), (0, 26)]), (.chain [(0, 25), (0, 26), (0, 27)]), (.chain [(0, 25), (0, 26)]), .two⟩
theorem cell0108_ok : cell0108.check T = true := by decide +kernel

def cell0109 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (9027 / 25600 : ℚ), (589 / 1600 : ℚ), (.chain [(0, 25)]), (.chain [(0, 26)]), (.chain [(0, 26)]), (.chain [(0, 25), (0, 26)]), (.chain [(0, 26), (0, 27)]), (.chain [(0, 26), (0, 27)]), .three⟩
theorem cell0109_ok : cell0109.check T = true := by decide +kernel

def cell0110 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (863 / 2560 : ℚ), (9027 / 25600 : ℚ), (.chain [(0, 24)]), (.chain [(0, 26)]), (.chain [(0, 25)]), (.chain [(0, 24), (0, 25)]), (.chain [(0, 26), (0, 27)]), (.chain [(0, 25), (0, 26)]), .two⟩
theorem cell0110_ok : cell0110.check T = true := by decide +kernel

def cell0111 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (863 / 2560 : ℚ), (9027 / 25600 : ℚ), (.chain [(0, 24)]), (.chain [(0, 26)]), (.chain [(0, 25)]), (.chain [(0, 24), (0, 25)]), (.chain [(0, 26), (0, 27), (0, 28)]), (.chain [(0, 25), (0, 26)]), .three⟩
theorem cell0111_ok : cell0111.check T = true := by decide +kernel

def cell0112 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (9027 / 25600 : ℚ), (589 / 1600 : ℚ), (.chain [(0, 25)]), (.chain [(0, 26)]), (.chain [(0, 26)]), (.chain [(0, 25), (0, 26)]), (.chain [(0, 26), (0, 27), (0, 28)]), (.chain [(0, 26), (0, 27)]), .two⟩
theorem cell0112_ok : cell0112.check T = true := by decide +kernel

def cell0113 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (9027 / 25600 : ℚ), (589 / 1600 : ℚ), (.chain [(0, 25)]), (.chain [(0, 27)]), (.chain [(0, 26)]), (.chain [(0, 25), (0, 26)]), (.chain [(0, 27), (0, 28)]), (.chain [(0, 26), (0, 27)]), .three⟩
theorem cell0113_ok : cell0113.check T = true := by decide +kernel

def cell0114 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (589 / 1600 : ℚ), (9821 / 25600 : ℚ), (.chain [(0, 26)]), (.chain [(0, 26)]), (.chain [(0, 26)]), (.chain [(0, 26), (0, 27)]), (.chain [(0, 26), (0, 27), (0, 28)]), (.chain [(0, 26), (0, 27)]), .three⟩
theorem cell0114_ok : cell0114.check T = true := by decide +kernel

def cell0115 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (589 / 1600 : ℚ), (9821 / 25600 : ℚ), (.chain [(0, 26)]), (.chain [(0, 27)]), (.chain [(0, 26)]), (.chain [(0, 26), (0, 27)]), (.chain [(0, 27), (0, 28)]), (.chain [(0, 26), (0, 27), (0, 28)]), .three⟩
theorem cell0115_ok : cell0115.check T = true := by decide +kernel

def cell0116 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (9821 / 25600 : ℚ), (5109 / 12800 : ℚ), (.chain [(0, 27)]), (.chain [(0, 27)]), (.chain [(0, 27)]), (.chain [(0, 27), (0, 28)]), (.chain [(0, 27), (0, 28)]), (.chain [(0, 27), (0, 28)]), .three⟩
theorem cell0116_ok : cell0116.check T = true := by decide +kernel

def cell0117 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (9821 / 25600 : ℚ), (5109 / 12800 : ℚ), (.chain [(0, 27)]), (.chain [(0, 28)]), (.chain [(0, 27)]), (.chain [(0, 27), (0, 28)]), (.chain [(0, 28), (0, 29)]), (.chain [(0, 27), (0, 28)]), .two⟩
theorem cell0117_ok : cell0117.check T = true := by decide +kernel

def cell0118 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (589 / 1600 : ℚ), (3849 / 10240 : ℚ), (.chain [(0, 26)]), (.chain [(0, 27)]), (.chain [(0, 27)]), (.chain [(0, 26), (0, 27)]), (.chain [(0, 27), (0, 28), (0, 29)]), (.chain [(0, 27), (0, 28)]), .two⟩
theorem cell0118_ok : cell0118.check T = true := by decide +kernel

def cell0119 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (3849 / 10240 : ℚ), (9821 / 25600 : ℚ), (.chain [(0, 27)]), (.chain [(0, 28)]), (.chain [(0, 27)]), (.chain [(0, 27)]), (.chain [(0, 28), (0, 29)]), (.chain [(0, 27), (0, 28)]), .two⟩
theorem cell0119_ok : cell0119.check T = true := by decide +kernel

def cells02 : List CellW := [cell0080, cell0081, cell0082, cell0083, cell0084, cell0085, cell0086, cell0087, cell0088, cell0089, cell0090, cell0091, cell0092, cell0093, cell0094, cell0095, cell0096, cell0097, cell0098, cell0099, cell0100, cell0101, cell0102, cell0103, cell0104, cell0105, cell0106, cell0107, cell0108, cell0109, cell0110, cell0111, cell0112, cell0113, cell0114, cell0115, cell0116, cell0117, cell0118, cell0119]

theorem cells02_valid : ∀ w ∈ cells02, w.check T = true :=
  (forall_mem_cons_of cell0080_ok (forall_mem_cons_of cell0081_ok (forall_mem_cons_of cell0082_ok (forall_mem_cons_of cell0083_ok (forall_mem_cons_of cell0084_ok (forall_mem_cons_of cell0085_ok (forall_mem_cons_of cell0086_ok (forall_mem_cons_of cell0087_ok (forall_mem_cons_of cell0088_ok (forall_mem_cons_of cell0089_ok (forall_mem_cons_of cell0090_ok (forall_mem_cons_of cell0091_ok (forall_mem_cons_of cell0092_ok (forall_mem_cons_of cell0093_ok (forall_mem_cons_of cell0094_ok (forall_mem_cons_of cell0095_ok (forall_mem_cons_of cell0096_ok (forall_mem_cons_of cell0097_ok (forall_mem_cons_of cell0098_ok (forall_mem_cons_of cell0099_ok (forall_mem_cons_of cell0100_ok (forall_mem_cons_of cell0101_ok (forall_mem_cons_of cell0102_ok (forall_mem_cons_of cell0103_ok (forall_mem_cons_of cell0104_ok (forall_mem_cons_of cell0105_ok (forall_mem_cons_of cell0106_ok (forall_mem_cons_of cell0107_ok (forall_mem_cons_of cell0108_ok (forall_mem_cons_of cell0109_ok (forall_mem_cons_of cell0110_ok (forall_mem_cons_of cell0111_ok (forall_mem_cons_of cell0112_ok (forall_mem_cons_of cell0113_ok (forall_mem_cons_of cell0114_ok (forall_mem_cons_of cell0115_ok (forall_mem_cons_of cell0116_ok (forall_mem_cons_of cell0117_ok (forall_mem_cons_of cell0118_ok (forall_mem_cons_of cell0119_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


