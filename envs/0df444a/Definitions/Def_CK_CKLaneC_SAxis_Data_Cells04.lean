-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells04
-- name    : CK_CKLaneC_SAxis_Data_Cells04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:32:53.727461+00:00
-- url     : https://prove2.me/theorems/c61acf36-7737-46e4-8110-c715881dfed3
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells04` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells04` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells04` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells04 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells04.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells04 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 4 (cells 160..199). -/

def cell0160 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (13791 / 25600 : ℚ), (3547 / 6400 : ℚ), (.chain [(1, 2)]), (.chain [(1, 3)]), (.chain [(1, 2)]), (.chain [(1, 2), (1, 3)]), (.chain [(1, 3), (1, 4)]), (.chain [(1, 2), (1, 3)]), .three⟩
theorem cell0160_ok : cell0160.check T = true := by decide +kernel

def cell0161 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (13791 / 25600 : ℚ), (3547 / 6400 : ℚ), (.chain [(1, 2)]), (.chain [(1, 3)]), (.chain [(1, 3)]), (.chain [(1, 2), (1, 3)]), (.chain [(1, 3), (1, 4)]), (.chain [(1, 3)]), .three⟩
theorem cell0161_ok : cell0161.check T = true := by decide +kernel

def cell0162 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (3547 / 6400 : ℚ), (2917 / 5120 : ℚ), (.chain [(1, 3)]), (.chain [(1, 3)]), (.chain [(1, 3)]), (.chain [(1, 3)]), (.chain [(1, 3), (1, 4)]), (.chain [(1, 3)]), .two⟩
theorem cell0162_ok : cell0162.check T = true := by decide +kernel

def cell0163 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (3547 / 6400 : ℚ), (2917 / 5120 : ℚ), (.chain [(1, 3)]), (.chain [(1, 3)]), (.chain [(1, 3)]), (.chain [(1, 3)]), (.chain [(1, 3), (1, 4)]), (.chain [(1, 3), (1, 4)]), .three⟩
theorem cell0163_ok : cell0163.check T = true := by decide +kernel

def cell0164 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (2917 / 5120 : ℚ), (7491 / 12800 : ℚ), (.chain [(1, 3)]), (.chain [(1, 3)]), (.chain [(1, 3)]), (.chain [(1, 3), (1, 4)]), (.chain [(1, 3), (1, 4)]), (.chain [(1, 3), (1, 4)]), .three⟩
theorem cell0164_ok : cell0164.check T = true := by decide +kernel

def cell0165 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (2917 / 5120 : ℚ), (7491 / 12800 : ℚ), (.chain [(1, 3)]), (.chain [(1, 4)]), (.chain [(1, 3)]), (.chain [(1, 3), (1, 4)]), (.chain [(1, 4)]), (.chain [(1, 3), (1, 4)]), .two⟩
theorem cell0165_ok : cell0165.check T = true := by decide +kernel

def cell0166 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (3547 / 6400 : ℚ), (2917 / 5120 : ℚ), (.chain [(1, 3)]), (.chain [(1, 3)]), (.chain [(1, 3)]), (.chain [(1, 3)]), (.chain [(1, 3), (1, 4)]), (.chain [(1, 3), (1, 4)]), .three⟩
theorem cell0166_ok : cell0166.check T = true := by decide +kernel

def cell0167 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (3547 / 6400 : ℚ), (2917 / 5120 : ℚ), (.chain [(1, 3)]), (.chain [(1, 4)]), (.chain [(1, 3)]), (.chain [(1, 3)]), (.chain [(1, 4), (1, 5)]), (.chain [(1, 3), (1, 4)]), .three⟩
theorem cell0167_ok : cell0167.check T = true := by decide +kernel

def cell0168 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (2917 / 5120 : ℚ), (7491 / 12800 : ℚ), (.chain [(1, 3)]), (.chain [(1, 4)]), (.chain [(1, 4)]), (.chain [(1, 3), (1, 4)]), (.chain [(1, 4), (1, 5)]), (.chain [(1, 4)]), .three⟩
theorem cell0168_ok : cell0168.check T = true := by decide +kernel

def cell0169 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (2917 / 5120 : ℚ), (7491 / 12800 : ℚ), (.chain [(1, 3)]), (.chain [(1, 4)]), (.chain [(1, 4)]), (.chain [(1, 3), (1, 4)]), (.chain [(1, 4), (1, 5)]), (.chain [(1, 4)]), .three⟩
theorem cell0169_ok : cell0169.check T = true := by decide +kernel

def cell0170 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (7491 / 12800 : ℚ), (15379 / 25600 : ℚ), (.chain [(1, 4)]), (.chain [(1, 4)]), (.chain [(1, 4)]), (.chain [(1, 4)]), (.chain [(1, 4), (1, 5)]), (.chain [(1, 4)]), .three⟩
theorem cell0170_ok : cell0170.check T = true := by decide +kernel

def cell0171 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (7491 / 12800 : ℚ), (15379 / 25600 : ℚ), (.chain [(1, 4)]), (.chain [(1, 4)]), (.chain [(1, 4)]), (.chain [(1, 4)]), (.chain [(1, 4), (1, 5)]), (.chain [(1, 4), (1, 5)]), .three⟩
theorem cell0171_ok : cell0171.check T = true := by decide +kernel

def cell0172 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (15379 / 25600 : ℚ), (493 / 800 : ℚ), (.chain [(1, 4)]), (.chain [(1, 4)]), (.chain [(1, 4)]), (.chain [(1, 4), (1, 5)]), (.chain [(1, 4), (1, 5)]), (.chain [(1, 4), (1, 5)]), .three⟩
theorem cell0172_ok : cell0172.check T = true := by decide +kernel

def cell0173 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (15379 / 25600 : ℚ), (493 / 800 : ℚ), (.chain [(1, 4)]), (.chain [(1, 5)]), (.chain [(1, 4)]), (.chain [(1, 4), (1, 5)]), (.chain [(1, 5)]), (.chain [(1, 4), (1, 5)]), .two⟩
theorem cell0173_ok : cell0173.check T = true := by decide +kernel

def cell0174 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (7491 / 12800 : ℚ), (15379 / 25600 : ℚ), (.chain [(1, 4)]), (.chain [(1, 4)]), (.chain [(1, 4)]), (.chain [(1, 4)]), (.chain [(1, 4), (1, 5)]), (.chain [(1, 4), (1, 5)]), .three⟩
theorem cell0174_ok : cell0174.check T = true := by decide +kernel

def cell0175 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (7491 / 12800 : ℚ), (15379 / 25600 : ℚ), (.chain [(1, 4)]), (.chain [(1, 5)]), (.chain [(1, 4)]), (.chain [(1, 4)]), (.chain [(1, 5), (1, 6)]), (.chain [(1, 4), (1, 5)]), .three⟩
theorem cell0175_ok : cell0175.check T = true := by decide +kernel

def cell0176 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (15379 / 25600 : ℚ), (493 / 800 : ℚ), (.chain [(1, 4)]), (.chain [(1, 5)]), (.chain [(1, 5)]), (.chain [(1, 4), (1, 5)]), (.chain [(1, 5), (1, 6)]), (.chain [(1, 5)]), .three⟩
theorem cell0176_ok : cell0176.check T = true := by decide +kernel

def cell0177 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (15379 / 25600 : ℚ), (493 / 800 : ℚ), (.chain [(1, 4)]), (.chain [(1, 5)]), (.chain [(1, 5)]), (.chain [(1, 4), (1, 5)]), (.chain [(1, 5), (1, 6)]), (.chain [(1, 5)]), .three⟩
theorem cell0177_ok : cell0177.check T = true := by decide +kernel

def cell0178 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (493 / 800 : ℚ), (16173 / 25600 : ℚ), (.chain [(1, 5)]), (.chain [(1, 5)]), (.chain [(1, 5)]), (.chain [(1, 5)]), (.chain [(1, 5), (1, 6)]), (.chain [(1, 5)]), .three⟩
theorem cell0178_ok : cell0178.check T = true := by decide +kernel

def cell0179 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (493 / 800 : ℚ), (16173 / 25600 : ℚ), (.chain [(1, 5)]), (.chain [(1, 5)]), (.chain [(1, 5)]), (.chain [(1, 5)]), (.chain [(1, 5), (1, 6)]), (.chain [(1, 5), (1, 6)]), .three⟩
theorem cell0179_ok : cell0179.check T = true := by decide +kernel

def cell0180 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (16173 / 25600 : ℚ), (1657 / 2560 : ℚ), (.chain [(1, 5)]), (.chain [(1, 5)]), (.chain [(1, 5)]), (.chain [(1, 5), (1, 6)]), (.chain [(1, 5), (1, 6)]), (.chain [(1, 5), (1, 6)]), .three⟩
theorem cell0180_ok : cell0180.check T = true := by decide +kernel

def cell0181 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (16173 / 25600 : ℚ), (1657 / 2560 : ℚ), (.chain [(1, 5)]), (.chain [(1, 6)]), (.chain [(1, 5)]), (.chain [(1, 5), (1, 6)]), (.chain [(1, 6)]), (.chain [(1, 5), (1, 6)]), .two⟩
theorem cell0181_ok : cell0181.check T = true := by decide +kernel

def cell0182 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (493 / 800 : ℚ), (16173 / 25600 : ℚ), (.chain [(1, 5)]), (.chain [(1, 5)]), (.chain [(1, 5)]), (.chain [(1, 5)]), (.chain [(1, 5), (1, 6)]), (.chain [(1, 5), (1, 6)]), .three⟩
theorem cell0182_ok : cell0182.check T = true := by decide +kernel

def cell0183 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (493 / 800 : ℚ), (16173 / 25600 : ℚ), (.chain [(1, 5)]), (.chain [(1, 6)]), (.chain [(1, 5)]), (.chain [(1, 5)]), (.chain [(1, 6), (1, 7)]), (.chain [(1, 5), (1, 6)]), .three⟩
theorem cell0183_ok : cell0183.check T = true := by decide +kernel

def cell0184 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (16173 / 25600 : ℚ), (1657 / 2560 : ℚ), (.chain [(1, 5)]), (.chain [(1, 6)]), (.chain [(1, 6)]), (.chain [(1, 5), (1, 6)]), (.chain [(1, 6), (1, 7)]), (.chain [(1, 6)]), .three⟩
theorem cell0184_ok : cell0184.check T = true := by decide +kernel

def cell0185 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (16173 / 25600 : ℚ), (1657 / 2560 : ℚ), (.chain [(1, 5)]), (.chain [(1, 6)]), (.chain [(1, 6)]), (.chain [(1, 5), (1, 6)]), (.chain [(1, 6), (1, 7)]), (.chain [(1, 6)]), .three⟩
theorem cell0185_ok : cell0185.check T = true := by decide +kernel

def cell0186 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (1657 / 2560 : ℚ), (16967 / 25600 : ℚ), (.chain [(1, 6)]), (.chain [(1, 6)]), (.chain [(1, 6)]), (.chain [(1, 6)]), (.chain [(1, 6), (1, 7)]), (.chain [(1, 6)]), .three⟩
theorem cell0186_ok : cell0186.check T = true := by decide +kernel

def cell0187 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (1657 / 2560 : ℚ), (16967 / 25600 : ℚ), (.chain [(1, 6)]), (.chain [(1, 6)]), (.chain [(1, 6)]), (.chain [(1, 6)]), (.chain [(1, 6), (1, 7)]), (.chain [(1, 6), (1, 7)]), .three⟩
theorem cell0187_ok : cell0187.check T = true := by decide +kernel

def cell0188 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (16967 / 25600 : ℚ), (4341 / 6400 : ℚ), (.chain [(1, 6)]), (.chain [(1, 6)]), (.chain [(1, 6)]), (.chain [(1, 6), (1, 7)]), (.chain [(1, 6), (1, 7)]), (.chain [(1, 6), (1, 7)]), .three⟩
theorem cell0188_ok : cell0188.check T = true := by decide +kernel

def cell0189 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (16967 / 25600 : ℚ), (4341 / 6400 : ℚ), (.chain [(1, 6)]), (.chain [(1, 7)]), (.chain [(1, 6)]), (.chain [(1, 6), (1, 7)]), (.chain [(1, 7)]), (.chain [(1, 6), (1, 7)]), .two⟩
theorem cell0189_ok : cell0189.check T = true := by decide +kernel

def cell0190 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (1657 / 2560 : ℚ), (33537 / 51200 : ℚ), (.chain [(1, 6)]), (.chain [(1, 6)]), (.chain [(1, 6)]), (.chain [(1, 6)]), (.chain [(1, 6), (1, 7)]), (.chain [(1, 6), (1, 7)]), .two⟩
theorem cell0190_ok : cell0190.check T = true := by decide +kernel

def cell0191 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (33537 / 51200 : ℚ), (16967 / 25600 : ℚ), (.chain [(1, 6)]), (.chain [(1, 7)]), (.chain [(1, 6)]), (.chain [(1, 6)]), (.chain [(1, 7)]), (.chain [(1, 6), (1, 7)]), .two⟩
theorem cell0191_ok : cell0191.check T = true := by decide +kernel

def cell0192 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (16967 / 25600 : ℚ), (4341 / 6400 : ℚ), (.chain [(1, 6)]), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 6), (1, 7)]), (.chain [(1, 7), (1, 8)]), (.chain [(1, 7)]), .three⟩
theorem cell0192_ok : cell0192.check T = true := by decide +kernel

def cell0193 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (16967 / 25600 : ℚ), (4341 / 6400 : ℚ), (.chain [(1, 6)]), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 6), (1, 7)]), (.chain [(1, 7), (1, 8)]), (.chain [(1, 7)]), .three⟩
theorem cell0193_ok : cell0193.check T = true := by decide +kernel

def cell0194 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (4341 / 6400 : ℚ), (17761 / 25600 : ℚ), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 7)]), .three⟩
theorem cell0194_ok : cell0194.check T = true := by decide +kernel

def cell0195 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (4341 / 6400 : ℚ), (17761 / 25600 : ℚ), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 7), (1, 8)]), (.chain [(1, 7)]), .three⟩
theorem cell0195_ok : cell0195.check T = true := by decide +kernel

def cell0196 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (17761 / 25600 : ℚ), (9079 / 12800 : ℚ), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 7), (1, 8)]), (.chain [(1, 7), (1, 8)]), (.chain [(1, 7), (1, 8)]), .three⟩
theorem cell0196_ok : cell0196.check T = true := by decide +kernel

def cell0197 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (17761 / 25600 : ℚ), (35919 / 51200 : ℚ), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 7), (1, 8)]), (.chain [(1, 7), (1, 8)]), .three⟩
theorem cell0197_ok : cell0197.check T = true := by decide +kernel

def cell0198 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (35919 / 51200 : ℚ), (9079 / 12800 : ℚ), (.chain [(1, 7)]), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 7), (1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8)]), .three⟩
theorem cell0198_ok : cell0198.check T = true := by decide +kernel

def cell0199 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (4341 / 6400 : ℚ), (17761 / 25600 : ℚ), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 7), (1, 8)]), (.chain [(1, 7), (1, 8)]), .three⟩
theorem cell0199_ok : cell0199.check T = true := by decide +kernel

def cells04 : List CellW := [cell0160, cell0161, cell0162, cell0163, cell0164, cell0165, cell0166, cell0167, cell0168, cell0169, cell0170, cell0171, cell0172, cell0173, cell0174, cell0175, cell0176, cell0177, cell0178, cell0179, cell0180, cell0181, cell0182, cell0183, cell0184, cell0185, cell0186, cell0187, cell0188, cell0189, cell0190, cell0191, cell0192, cell0193, cell0194, cell0195, cell0196, cell0197, cell0198, cell0199]

theorem cells04_valid : ∀ w ∈ cells04, w.check T = true :=
  (forall_mem_cons_of cell0160_ok (forall_mem_cons_of cell0161_ok (forall_mem_cons_of cell0162_ok (forall_mem_cons_of cell0163_ok (forall_mem_cons_of cell0164_ok (forall_mem_cons_of cell0165_ok (forall_mem_cons_of cell0166_ok (forall_mem_cons_of cell0167_ok (forall_mem_cons_of cell0168_ok (forall_mem_cons_of cell0169_ok (forall_mem_cons_of cell0170_ok (forall_mem_cons_of cell0171_ok (forall_mem_cons_of cell0172_ok (forall_mem_cons_of cell0173_ok (forall_mem_cons_of cell0174_ok (forall_mem_cons_of cell0175_ok (forall_mem_cons_of cell0176_ok (forall_mem_cons_of cell0177_ok (forall_mem_cons_of cell0178_ok (forall_mem_cons_of cell0179_ok (forall_mem_cons_of cell0180_ok (forall_mem_cons_of cell0181_ok (forall_mem_cons_of cell0182_ok (forall_mem_cons_of cell0183_ok (forall_mem_cons_of cell0184_ok (forall_mem_cons_of cell0185_ok (forall_mem_cons_of cell0186_ok (forall_mem_cons_of cell0187_ok (forall_mem_cons_of cell0188_ok (forall_mem_cons_of cell0189_ok (forall_mem_cons_of cell0190_ok (forall_mem_cons_of cell0191_ok (forall_mem_cons_of cell0192_ok (forall_mem_cons_of cell0193_ok (forall_mem_cons_of cell0194_ok (forall_mem_cons_of cell0195_ok (forall_mem_cons_of cell0196_ok (forall_mem_cons_of cell0197_ok (forall_mem_cons_of cell0198_ok (forall_mem_cons_of cell0199_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


