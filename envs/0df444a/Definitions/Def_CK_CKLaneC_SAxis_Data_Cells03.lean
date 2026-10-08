-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells03
-- name    : CK_CKLaneC_SAxis_Data_Cells03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T05:43:08.931583+00:00
-- url     : https://prove2.me/theorems/9f27c7a2-4cfe-47b8-aa49-a9d527465c3f
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells03` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells03` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells03` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells03 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells03.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells03 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 3 (cells 120..159). -/

def cell0120 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (9821 / 25600 : ℚ), (20039 / 51200 : ℚ), (.chain [(0, 27)]), (.chain [(0, 28)]), (.chain [(0, 28)]), (.chain [(0, 27)]), (.chain [(0, 28), (0, 29)]), (.chain [(0, 28)]), .three⟩
theorem cell0120_ok : cell0120.check T = true := by decide +kernel

def cell0121 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (20039 / 51200 : ℚ), (5109 / 12800 : ℚ), (.chain [(0, 27)]), (.chain [(0, 28)]), (.chain [(0, 28)]), (.chain [(0, 27), (0, 28)]), (.chain [(0, 28), (0, 29), (0, 30)]), (.chain [(0, 28), (0, 29)]), .two⟩
theorem cell0121_ok : cell0121.check T = true := by decide +kernel

def cell0122 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (5109 / 12800 : ℚ), (20833 / 51200 : ℚ), (.chain [(0, 28)]), (.chain [(0, 28)]), (.chain [(0, 28)]), (.chain [(0, 28)]), (.chain [(0, 28), (0, 29)]), (.chain [(0, 28), (0, 29)]), .three⟩
theorem cell0122_ok : cell0122.check T = true := by decide +kernel

def cell0123 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (20833 / 51200 : ℚ), (2123 / 5120 : ℚ), (.chain [(0, 28)]), (.chain [(0, 28)]), (.chain [(0, 28)]), (.chain [(0, 28), (0, 29)]), (.chain [(0, 28), (0, 29), (0, 30)]), (.chain [(0, 28), (0, 29)]), .two⟩
theorem cell0123_ok : cell0123.check T = true := by decide +kernel

def cell0124 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (2123 / 5120 : ℚ), (2753 / 6400 : ℚ), (.chain [(0, 29)]), (.chain [(0, 29)]), (.chain [(0, 29)]), (.chain [(0, 29)]), (.chain [(0, 29), (0, 30)]), (.chain [(0, 29), (0, 30)]), .two⟩
theorem cell0124_ok : cell0124.check T = true := by decide +kernel

def cell0125 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (2123 / 5120 : ℚ), (2753 / 6400 : ℚ), (.chain [(0, 29)]), (.chain [(0, 29)]), (.chain [(0, 29)]), (.chain [(0, 29)]), (.chain [(0, 29), (0, 30)]), (.chain [(0, 29), (0, 30)]), .three⟩
theorem cell0125_ok : cell0125.check T = true := by decide +kernel

def cell0126 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (5109 / 12800 : ℚ), (2123 / 5120 : ℚ), (.chain [(0, 28)]), (.chain [(0, 29)]), (.chain [(0, 28)]), (.chain [(0, 28), (0, 29)]), (.chain [(0, 29), (0, 30)]), (.chain [(0, 28), (0, 29)]), .three⟩
theorem cell0126_ok : cell0126.check T = true := by decide +kernel

def cell0127 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (5109 / 12800 : ℚ), (2123 / 5120 : ℚ), (.chain [(0, 28)]), (.chain [(0, 29)]), (.chain [(0, 29)]), (.chain [(0, 28), (0, 29)]), (.chain [(0, 29), (0, 30), (0, 31)]), (.chain [(0, 29), (0, 30)]), .three⟩
theorem cell0127_ok : cell0127.check T = true := by decide +kernel

def cell0128 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (2123 / 5120 : ℚ), (21627 / 51200 : ℚ), (.chain [(0, 29)]), (.chain [(0, 30)]), (.chain [(0, 29)]), (.chain [(0, 29)]), (.chain [(0, 30), (0, 31)]), (.chain [(0, 29), (0, 30)]), .two⟩
theorem cell0128_ok : cell0128.check T = true := by decide +kernel

def cell0129 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (21627 / 51200 : ℚ), (2753 / 6400 : ℚ), (.chain [(0, 29)]), (.chain [(0, 30)]), (.chain [(0, 30)]), (.chain [(0, 29)]), (.chain [(0, 30), (0, 31)]), (.chain [(0, 30)]), .three⟩
theorem cell0129_ok : cell0129.check T = true := by decide +kernel

def cell0130 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (2753 / 6400 : ℚ), (11409 / 25600 : ℚ), (.chain [(0, 29)]), (.chain [(0, 29)]), (.chain [(0, 29)]), (.chain [(0, 29), (0, 30)]), (.chain [(0, 29), (0, 30), (0, 31)]), (.chain [(0, 29), (0, 30)]), .two⟩
theorem cell0130_ok : cell0130.check T = true := by decide +kernel

def cell0131 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (2753 / 6400 : ℚ), (11409 / 25600 : ℚ), (.chain [(0, 29)]), (.chain [(0, 30)]), (.chain [(0, 30)]), (.chain [(0, 29), (0, 30)]), (.chain [(0, 30), (0, 31)]), (.chain [(0, 30), (0, 31)]), .three⟩
theorem cell0131_ok : cell0131.check T = true := by decide +kernel

def cell0132 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (11409 / 25600 : ℚ), (5903 / 12800 : ℚ), (.chain [(0, 30)]), (.chain [(0, 30)]), (.chain [(0, 30)]), (.chain [(0, 30), (0, 31)]), (.chain [(0, 30), (0, 31)]), (.chain [(0, 30), (0, 31)]), .three⟩
theorem cell0132_ok : cell0132.check T = true := by decide +kernel

def cell0133 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (11409 / 25600 : ℚ), (5903 / 12800 : ℚ), (.chain [(0, 30)]), (.chain [(0, 31)]), (.chain [(0, 30)]), (.chain [(0, 30), (0, 31)]), (.chain [(0, 31), (1, 0)]), (.chain [(0, 30), (0, 31)]), .two⟩
theorem cell0133_ok : cell0133.check T = true := by decide +kernel

def cell0134 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (2753 / 6400 : ℚ), (11409 / 25600 : ℚ), (.chain [(0, 29)]), (.chain [(0, 30)]), (.chain [(0, 30)]), (.chain [(0, 29), (0, 30)]), (.chain [(0, 30), (0, 31)]), (.chain [(0, 30), (0, 31)]), .three⟩
theorem cell0134_ok : cell0134.check T = true := by decide +kernel

def cell0135 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (2753 / 6400 : ℚ), (11409 / 25600 : ℚ), (.chain [(0, 29)]), (.chain [(0, 31)]), (.chain [(0, 30)]), (.chain [(0, 29), (0, 30)]), (.chain [(0, 31), (1, 0)]), (.chain [(0, 30), (0, 31)]), .three⟩
theorem cell0135_ok : cell0135.check T = true := by decide +kernel

def cell0136 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (11409 / 25600 : ℚ), (4643 / 10240 : ℚ), (.chain [(0, 30)]), (.chain [(0, 31)]), (.chain [(0, 31)]), (.chain [(0, 30)]), (.chain [(0, 31), (1, 0)]), (.chain [(0, 31)]), .three⟩
theorem cell0136_ok : cell0136.check T = true := by decide +kernel

def cell0137 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (4643 / 10240 : ℚ), (5903 / 12800 : ℚ), (.chain [(0, 30)]), (.chain [(0, 31)]), (.chain [(0, 31)]), (.chain [(0, 30), (0, 31)]), (.chain [(0, 31), (1, 0), (1, 1)]), (.chain [(0, 31), (1, 0)]), .two⟩
theorem cell0137_ok : cell0137.check T = true := by decide +kernel

def cell0138 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (5903 / 12800 : ℚ), (12203 / 25600 : ℚ), (.chain [(0, 31)]), (.chain [(0, 31)]), (.chain [(0, 31)]), (.chain [(0, 31), (1, 0)]), (.chain [(0, 31), (1, 0)]), (.chain [(0, 31), (1, 0)]), .three⟩
theorem cell0138_ok : cell0138.check T = true := by decide +kernel

def cell0139 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (5903 / 12800 : ℚ), (12203 / 25600 : ℚ), (.chain [(0, 31)]), (.chain [(0, 31)]), (.chain [(0, 31)]), (.chain [(0, 31), (1, 0)]), (.chain [(0, 31), (1, 0)]), (.chain [(0, 31), (1, 0)]), .three⟩
theorem cell0139_ok : cell0139.check T = true := by decide +kernel

def cell0140 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (12203 / 25600 : ℚ), (63 / 128 : ℚ), (.chain [(1, 0)]), (.chain [(1, 0)]), (.chain [(1, 0)]), (.chain [(1, 0)]), (.chain [(1, 0), (1, 1)]), (.chain [(1, 0)]), .two⟩
theorem cell0140_ok : cell0140.check T = true := by decide +kernel

def cell0141 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (12203 / 25600 : ℚ), (63 / 128 : ℚ), (.chain [(1, 0)]), (.chain [(1, 0)]), (.chain [(1, 0)]), (.chain [(1, 0)]), (.chain [(1, 0), (1, 1)]), (.chain [(1, 0), (1, 1)]), .three⟩
theorem cell0141_ok : cell0141.check T = true := by decide +kernel

def cell0142 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (5903 / 12800 : ℚ), (12203 / 25600 : ℚ), (.chain [(0, 31)]), (.chain [(1, 0)]), (.chain [(0, 31)]), (.chain [(0, 31), (1, 0)]), (.chain [(1, 0), (1, 1)]), (.chain [(0, 31), (1, 0)]), .three⟩
theorem cell0142_ok : cell0142.check T = true := by decide +kernel

def cell0143 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (5903 / 12800 : ℚ), (12203 / 25600 : ℚ), (.chain [(0, 31)]), (.chain [(1, 0)]), (.chain [(0, 31)]), (.chain [(0, 31), (1, 0)]), (.chain [(1, 0), (1, 1)]), (.chain [(0, 31), (1, 0)]), .three⟩
theorem cell0143_ok : cell0143.check T = true := by decide +kernel

def cell0144 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (12203 / 25600 : ℚ), (63 / 128 : ℚ), (.chain [(1, 0)]), (.chain [(1, 0)]), (.chain [(1, 0)]), (.chain [(1, 0)]), (.chain [(1, 0), (1, 1)]), (.chain [(1, 0), (1, 1)]), .three⟩
theorem cell0144_ok : cell0144.check T = true := by decide +kernel

def cell0145 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (12203 / 25600 : ℚ), (63 / 128 : ℚ), (.chain [(1, 0)]), (.chain [(1, 1)]), (.chain [(1, 0)]), (.chain [(1, 0)]), (.chain [(1, 1), (1, 2)]), (.chain [(1, 0), (1, 1)]), .three⟩
theorem cell0145_ok : cell0145.check T = true := by decide +kernel

def cell0146 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (63 / 128 : ℚ), (12997 / 25600 : ℚ), (.chain [(1, 0)]), (.chain [(1, 0)]), (.chain [(1, 0)]), (.chain [(1, 0), (1, 1)]), (.chain [(1, 0), (1, 1)]), (.chain [(1, 0), (1, 1)]), .three⟩
theorem cell0146_ok : cell0146.check T = true := by decide +kernel

def cell0147 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (63 / 128 : ℚ), (12997 / 25600 : ℚ), (.chain [(1, 0)]), (.chain [(1, 1)]), (.chain [(1, 0)]), (.chain [(1, 0), (1, 1)]), (.chain [(1, 1), (1, 2)]), (.chain [(1, 0), (1, 1)]), .two⟩
theorem cell0147_ok : cell0147.check T = true := by decide +kernel

def cell0148 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (12997 / 25600 : ℚ), (6697 / 12800 : ℚ), (.chain [(1, 1)]), (.chain [(1, 1)]), (.chain [(1, 1)]), (.chain [(1, 1)]), (.chain [(1, 1), (1, 2)]), (.chain [(1, 1), (1, 2)]), .three⟩
theorem cell0148_ok : cell0148.check T = true := by decide +kernel

def cell0149 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (12997 / 25600 : ℚ), (6697 / 12800 : ℚ), (.chain [(1, 1)]), (.chain [(1, 1)]), (.chain [(1, 1)]), (.chain [(1, 1)]), (.chain [(1, 1), (1, 2)]), (.chain [(1, 1), (1, 2)]), .three⟩
theorem cell0149_ok : cell0149.check T = true := by decide +kernel

def cell0150 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (63 / 128 : ℚ), (12997 / 25600 : ℚ), (.chain [(1, 0)]), (.chain [(1, 1)]), (.chain [(1, 1)]), (.chain [(1, 0), (1, 1)]), (.chain [(1, 1), (1, 2)]), (.chain [(1, 1)]), .three⟩
theorem cell0150_ok : cell0150.check T = true := by decide +kernel

def cell0151 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (63 / 128 : ℚ), (12997 / 25600 : ℚ), (.chain [(1, 0)]), (.chain [(1, 1)]), (.chain [(1, 1)]), (.chain [(1, 0), (1, 1)]), (.chain [(1, 1), (1, 2)]), (.chain [(1, 1), (1, 2)]), .three⟩
theorem cell0151_ok : cell0151.check T = true := by decide +kernel

def cell0152 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (12997 / 25600 : ℚ), (26391 / 51200 : ℚ), (.chain [(1, 1)]), (.chain [(1, 2)]), (.chain [(1, 1)]), (.chain [(1, 1)]), (.chain [(1, 2), (1, 3)]), (.chain [(1, 1), (1, 2)]), .two⟩
theorem cell0152_ok : cell0152.check T = true := by decide +kernel

def cell0153 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (26391 / 51200 : ℚ), (6697 / 12800 : ℚ), (.chain [(1, 1)]), (.chain [(1, 2)]), (.chain [(1, 2)]), (.chain [(1, 1)]), (.chain [(1, 2), (1, 3)]), (.chain [(1, 2)]), .three⟩
theorem cell0153_ok : cell0153.check T = true := by decide +kernel

def cell0154 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (6697 / 12800 : ℚ), (5437 / 10240 : ℚ), (.chain [(1, 1)]), (.chain [(1, 1)]), (.chain [(1, 1)]), (.chain [(1, 1), (1, 2)]), (.chain [(1, 1), (1, 2)]), (.chain [(1, 1), (1, 2)]), .two⟩
theorem cell0154_ok : cell0154.check T = true := by decide +kernel

def cell0155 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (5437 / 10240 : ℚ), (13791 / 25600 : ℚ), (.chain [(1, 2)]), (.chain [(1, 2)]), (.chain [(1, 2)]), (.chain [(1, 2)]), (.chain [(1, 2), (1, 3)]), (.chain [(1, 2)]), .two⟩
theorem cell0155_ok : cell0155.check T = true := by decide +kernel

def cell0156 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (13791 / 25600 : ℚ), (3547 / 6400 : ℚ), (.chain [(1, 2)]), (.chain [(1, 2)]), (.chain [(1, 2)]), (.chain [(1, 2), (1, 3)]), (.chain [(1, 2), (1, 3)]), (.chain [(1, 2), (1, 3)]), .three⟩
theorem cell0156_ok : cell0156.check T = true := by decide +kernel

def cell0157 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (13791 / 25600 : ℚ), (3547 / 6400 : ℚ), (.chain [(1, 2)]), (.chain [(1, 2)]), (.chain [(1, 2)]), (.chain [(1, 2), (1, 3)]), (.chain [(1, 2), (1, 3)]), (.chain [(1, 2), (1, 3)]), .three⟩
theorem cell0157_ok : cell0157.check T = true := by decide +kernel

def cell0158 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (6697 / 12800 : ℚ), (5437 / 10240 : ℚ), (.chain [(1, 1)]), (.chain [(1, 2)]), (.chain [(1, 2)]), (.chain [(1, 1), (1, 2)]), (.chain [(1, 2), (1, 3)]), (.chain [(1, 2)]), .three⟩
theorem cell0158_ok : cell0158.check T = true := by decide +kernel

def cell0159 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (5437 / 10240 : ℚ), (13791 / 25600 : ℚ), (.chain [(1, 2)]), (.chain [(1, 2)]), (.chain [(1, 2)]), (.chain [(1, 2)]), (.chain [(1, 2), (1, 3)]), (.chain [(1, 2), (1, 3)]), .two⟩
theorem cell0159_ok : cell0159.check T = true := by decide +kernel

def cells03 : List CellW := [cell0120, cell0121, cell0122, cell0123, cell0124, cell0125, cell0126, cell0127, cell0128, cell0129, cell0130, cell0131, cell0132, cell0133, cell0134, cell0135, cell0136, cell0137, cell0138, cell0139, cell0140, cell0141, cell0142, cell0143, cell0144, cell0145, cell0146, cell0147, cell0148, cell0149, cell0150, cell0151, cell0152, cell0153, cell0154, cell0155, cell0156, cell0157, cell0158, cell0159]

theorem cells03_valid : ∀ w ∈ cells03, w.check T = true :=
  (forall_mem_cons_of cell0120_ok (forall_mem_cons_of cell0121_ok (forall_mem_cons_of cell0122_ok (forall_mem_cons_of cell0123_ok (forall_mem_cons_of cell0124_ok (forall_mem_cons_of cell0125_ok (forall_mem_cons_of cell0126_ok (forall_mem_cons_of cell0127_ok (forall_mem_cons_of cell0128_ok (forall_mem_cons_of cell0129_ok (forall_mem_cons_of cell0130_ok (forall_mem_cons_of cell0131_ok (forall_mem_cons_of cell0132_ok (forall_mem_cons_of cell0133_ok (forall_mem_cons_of cell0134_ok (forall_mem_cons_of cell0135_ok (forall_mem_cons_of cell0136_ok (forall_mem_cons_of cell0137_ok (forall_mem_cons_of cell0138_ok (forall_mem_cons_of cell0139_ok (forall_mem_cons_of cell0140_ok (forall_mem_cons_of cell0141_ok (forall_mem_cons_of cell0142_ok (forall_mem_cons_of cell0143_ok (forall_mem_cons_of cell0144_ok (forall_mem_cons_of cell0145_ok (forall_mem_cons_of cell0146_ok (forall_mem_cons_of cell0147_ok (forall_mem_cons_of cell0148_ok (forall_mem_cons_of cell0149_ok (forall_mem_cons_of cell0150_ok (forall_mem_cons_of cell0151_ok (forall_mem_cons_of cell0152_ok (forall_mem_cons_of cell0153_ok (forall_mem_cons_of cell0154_ok (forall_mem_cons_of cell0155_ok (forall_mem_cons_of cell0156_ok (forall_mem_cons_of cell0157_ok (forall_mem_cons_of cell0158_ok (forall_mem_cons_of cell0159_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


