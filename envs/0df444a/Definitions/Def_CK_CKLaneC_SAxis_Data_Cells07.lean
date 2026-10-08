-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells07
-- name    : CK_CKLaneC_SAxis_Data_Cells07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T05:58:46.501981+00:00
-- url     : https://prove2.me/theorems/4cb905d1-f0a6-4203-a9c3-91ba0caf59bc
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells07` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells07` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells07` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells07 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells07.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells07 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 7 (cells 280..319). -/

def cell0280 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (24907 / 25600 : ℚ), (3163 / 3200 : ℚ), (.chain [(1, 14)]), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 14), (1, 15)]), (.chain [(1, 15)]), (.chain [(1, 15)]), .three⟩
theorem cell0280_ok : cell0280.check T = true := by decide +kernel

def cell0281 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (2451 / 2560 : ℚ), (49417 / 51200 : ℚ), (.chain [(1, 14)]), (.chain [(1, 15)]), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 15)]), (.chain [(1, 14), (1, 15)]), .two⟩
theorem cell0281_ok : cell0281.check T = true := by decide +kernel

def cell0282 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (49417 / 51200 : ℚ), (24907 / 25600 : ℚ), (.chain [(1, 14)]), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 14)]), (.chain [(1, 15)]), (.chain [(1, 15)]), .three⟩
theorem cell0282_ok : cell0282.check T = true := by decide +kernel

def cell0283 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (24907 / 25600 : ℚ), (3163 / 3200 : ℚ), (.chain [(1, 14)]), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 14), (1, 15)]), (.chain [(1, 15), (1, 16)]), (.chain [(1, 15)]), .three⟩
theorem cell0283_ok : cell0283.check T = true := by decide +kernel

def cell0284 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (3163 / 3200 : ℚ), (25701 / 25600 : ℚ), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 15)]), .three⟩
theorem cell0284_ok : cell0284.check T = true := by decide +kernel

def cell0285 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (3163 / 3200 : ℚ), (25701 / 25600 : ℚ), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 15), (1, 16)]), (.chain [(1, 15)]), .three⟩
theorem cell0285_ok : cell0285.check T = true := by decide +kernel

def cell0286 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (25701 / 25600 : ℚ), (13049 / 12800 : ℚ), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 15), (1, 16)]), (.chain [(1, 15), (1, 16)]), (.chain [(1, 15), (1, 16)]), .three⟩
theorem cell0286_ok : cell0286.check T = true := by decide +kernel

def cell0287 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (25701 / 25600 : ℚ), (13049 / 12800 : ℚ), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 15), (1, 16)]), (.chain [(1, 15), (1, 16)]), (.chain [(1, 15), (1, 16)]), .two⟩
theorem cell0287_ok : cell0287.check T = true := by decide +kernel

def cell0288 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (3163 / 3200 : ℚ), (25701 / 25600 : ℚ), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 15), (1, 16)]), (.chain [(1, 15), (1, 16)]), .three⟩
theorem cell0288_ok : cell0288.check T = true := by decide +kernel

def cell0289 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (3163 / 3200 : ℚ), (25701 / 25600 : ℚ), (.chain [(1, 15)]), (.chain [(1, 16)]), (.chain [(1, 15)]), (.chain [(1, 15)]), (.chain [(1, 16)]), (.chain [(1, 15), (1, 16)]), .three⟩
theorem cell0289_ok : cell0289.check T = true := by decide +kernel

def cell0290 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (25701 / 25600 : ℚ), (13049 / 12800 : ℚ), (.chain [(1, 15)]), (.chain [(1, 16)]), (.chain [(1, 15)]), (.chain [(1, 15), (1, 16)]), (.chain [(1, 16)]), (.chain [(1, 15), (1, 16)]), .three⟩
theorem cell0290_ok : cell0290.check T = true := by decide +kernel

def cell0291 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (25701 / 25600 : ℚ), (13049 / 12800 : ℚ), (.chain [(1, 15)]), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 15), (1, 16)]), (.chain [(1, 16), (1, 17)]), (.chain [(1, 16)]), .three⟩
theorem cell0291_ok : cell0291.check T = true := by decide +kernel

def cell0292 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (13049 / 12800 : ℚ), (5299 / 5120 : ℚ), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16)]), .three⟩
theorem cell0292_ok : cell0292.check T = true := by decide +kernel

def cell0293 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (13049 / 12800 : ℚ), (5299 / 5120 : ℚ), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16)]), .three⟩
theorem cell0293_ok : cell0293.check T = true := by decide +kernel

def cell0294 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (5299 / 5120 : ℚ), (6723 / 6400 : ℚ), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16), (1, 17)]), (.chain [(1, 16), (1, 17)]), .three⟩
theorem cell0294_ok : cell0294.check T = true := by decide +kernel

def cell0295 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (13049 / 12800 : ℚ), (5299 / 5120 : ℚ), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16), (1, 17)]), (.chain [(1, 16)]), .three⟩
theorem cell0295_ok : cell0295.check T = true := by decide +kernel

def cell0296 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (5299 / 5120 : ℚ), (53387 / 51200 : ℚ), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16), (1, 17)]), (.chain [(1, 16), (1, 17)]), .two⟩
theorem cell0296_ok : cell0296.check T = true := by decide +kernel

def cell0297 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (53387 / 51200 : ℚ), (6723 / 6400 : ℚ), (.chain [(1, 16)]), (.chain [(1, 17)]), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 17)]), (.chain [(1, 16), (1, 17)]), .three⟩
theorem cell0297_ok : cell0297.check T = true := by decide +kernel

def cell0298 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (6723 / 6400 : ℚ), (27289 / 25600 : ℚ), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16)]), (.chain [(1, 16), (1, 17)]), (.chain [(1, 16), (1, 17)]), (.chain [(1, 16), (1, 17)]), .three⟩
theorem cell0298_ok : cell0298.check T = true := by decide +kernel

def cell0299 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (6723 / 6400 : ℚ), (27289 / 25600 : ℚ), (.chain [(1, 16)]), (.chain [(1, 17)]), (.chain [(1, 17)]), (.chain [(1, 16), (1, 17)]), (.chain [(1, 17)]), (.chain [(1, 17)]), .three⟩
theorem cell0299_ok : cell0299.check T = true := by decide +kernel

def cell0300 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (27289 / 25600 : ℚ), (13843 / 12800 : ℚ), (.chain [(1, 17)]), (.chain [(1, 17)]), (.chain [(1, 17)]), (.chain [(1, 17)]), (.chain [(1, 17), (1, 18)]), (.chain [(1, 17)]), .three⟩
theorem cell0300_ok : cell0300.check T = true := by decide +kernel

def cell0301 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (6723 / 6400 : ℚ), (27289 / 25600 : ℚ), (.chain [(1, 16)]), (.chain [(1, 17)]), (.chain [(1, 17)]), (.chain [(1, 16), (1, 17)]), (.chain [(1, 17), (1, 18)]), (.chain [(1, 17)]), .three⟩
theorem cell0301_ok : cell0301.check T = true := by decide +kernel

def cell0302 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (27289 / 25600 : ℚ), (13843 / 12800 : ℚ), (.chain [(1, 17)]), (.chain [(1, 17)]), (.chain [(1, 17)]), (.chain [(1, 17)]), (.chain [(1, 17), (1, 18)]), (.chain [(1, 17), (1, 18)]), .three⟩
theorem cell0302_ok : cell0302.check T = true := by decide +kernel

def cell0303 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (13843 / 12800 : ℚ), (28083 / 25600 : ℚ), (.chain [(1, 17)]), (.chain [(1, 17)]), (.chain [(1, 17)]), (.chain [(1, 17), (1, 18)]), (.chain [(1, 17), (1, 18)]), (.chain [(1, 17), (1, 18)]), .three⟩
theorem cell0303_ok : cell0303.check T = true := by decide +kernel

def cell0304 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (28083 / 25600 : ℚ), (89 / 80 : ℚ), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18)]), .three⟩
theorem cell0304_ok : cell0304.check T = true := by decide +kernel

def cell0305 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (28083 / 25600 : ℚ), (89 / 80 : ℚ), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18)]), .three⟩
theorem cell0305_ok : cell0305.check T = true := by decide +kernel

def cell0306 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (13843 / 12800 : ℚ), (28083 / 25600 : ℚ), (.chain [(1, 17)]), (.chain [(1, 18)]), (.chain [(1, 17)]), (.chain [(1, 17), (1, 18)]), (.chain [(1, 18), (1, 19)]), (.chain [(1, 17), (1, 18)]), .two⟩
theorem cell0306_ok : cell0306.check T = true := by decide +kernel

def cell0307 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (28083 / 25600 : ℚ), (89 / 80 : ℚ), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18), (1, 19)]), (.chain [(1, 18)]), .three⟩
theorem cell0307_ok : cell0307.check T = true := by decide +kernel

def cell0308 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (89 / 80 : ℚ), (28877 / 25600 : ℚ), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18), (1, 19)]), (.chain [(1, 18), (1, 19)]), .three⟩
theorem cell0308_ok : cell0308.check T = true := by decide +kernel

def cell0309 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (28877 / 25600 : ℚ), (14637 / 12800 : ℚ), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18), (1, 19)]), (.chain [(1, 18), (1, 19)]), (.chain [(1, 18), (1, 19)]), .two⟩
theorem cell0309_ok : cell0309.check T = true := by decide +kernel

def cell0310 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (89 / 80 : ℚ), (28877 / 25600 : ℚ), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18)]), (.chain [(1, 18), (1, 19)]), (.chain [(1, 18), (1, 19)]), .two⟩
theorem cell0310_ok : cell0310.check T = true := by decide +kernel

def cell0311 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (28877 / 25600 : ℚ), (14637 / 12800 : ℚ), (.chain [(1, 18)]), (.chain [(1, 19)]), (.chain [(1, 19)]), (.chain [(1, 18), (1, 19)]), (.chain [(1, 19), (1, 20)]), (.chain [(1, 19)]), .three⟩
theorem cell0311_ok : cell0311.check T = true := by decide +kernel

def cell0312 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (14637 / 12800 : ℚ), (29671 / 25600 : ℚ), (.chain [(1, 19)]), (.chain [(1, 19)]), (.chain [(1, 19)]), (.chain [(1, 19)]), (.chain [(1, 19), (1, 20)]), (.chain [(1, 19)]), .three⟩
theorem cell0312_ok : cell0312.check T = true := by decide +kernel

def cell0313 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (29671 / 25600 : ℚ), (7517 / 6400 : ℚ), (.chain [(1, 19)]), (.chain [(1, 19)]), (.chain [(1, 19)]), (.chain [(1, 19)]), (.chain [(1, 19), (1, 20)]), (.chain [(1, 19), (1, 20)]), .three⟩
theorem cell0313_ok : cell0313.check T = true := by decide +kernel

def cell0314 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (14637 / 12800 : ℚ), (29671 / 25600 : ℚ), (.chain [(1, 19)]), (.chain [(1, 19)]), (.chain [(1, 19)]), (.chain [(1, 19)]), (.chain [(1, 19), (1, 20)]), (.chain [(1, 19), (1, 20)]), .three⟩
theorem cell0314_ok : cell0314.check T = true := by decide +kernel

def cell0315 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (29671 / 25600 : ℚ), (7517 / 6400 : ℚ), (.chain [(1, 19)]), (.chain [(1, 20)]), (.chain [(1, 19)]), (.chain [(1, 19)]), (.chain [(1, 20)]), (.chain [(1, 19), (1, 20)]), .two⟩
theorem cell0315_ok : cell0315.check T = true := by decide +kernel

def cell0316 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (7517 / 6400 : ℚ), (6093 / 5120 : ℚ), (.chain [(1, 19)]), (.chain [(1, 19)]), (.chain [(1, 19)]), (.chain [(1, 19), (1, 20)]), (.chain [(1, 19), (1, 20)]), (.chain [(1, 19), (1, 20)]), .three⟩
theorem cell0316_ok : cell0316.check T = true := by decide +kernel

def cell0317 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (7517 / 6400 : ℚ), (6093 / 5120 : ℚ), (.chain [(1, 19)]), (.chain [(1, 20)]), (.chain [(1, 20)]), (.chain [(1, 19), (1, 20)]), (.chain [(1, 20)]), (.chain [(1, 20)]), .three⟩
theorem cell0317_ok : cell0317.check T = true := by decide +kernel

def cell0318 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (6093 / 5120 : ℚ), (15431 / 12800 : ℚ), (.chain [(1, 20)]), (.chain [(1, 20)]), (.chain [(1, 20)]), (.chain [(1, 20)]), (.chain [(1, 20), (1, 21)]), (.chain [(1, 20), (1, 21)]), .three⟩
theorem cell0318_ok : cell0318.check T = true := by decide +kernel

def cell0319 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (7517 / 6400 : ℚ), (6093 / 5120 : ℚ), (.chain [(1, 19)]), (.chain [(1, 20)]), (.chain [(1, 20)]), (.chain [(1, 19), (1, 20)]), (.chain [(1, 20), (1, 21)]), (.chain [(1, 20)]), .three⟩
theorem cell0319_ok : cell0319.check T = true := by decide +kernel

def cells07 : List CellW := [cell0280, cell0281, cell0282, cell0283, cell0284, cell0285, cell0286, cell0287, cell0288, cell0289, cell0290, cell0291, cell0292, cell0293, cell0294, cell0295, cell0296, cell0297, cell0298, cell0299, cell0300, cell0301, cell0302, cell0303, cell0304, cell0305, cell0306, cell0307, cell0308, cell0309, cell0310, cell0311, cell0312, cell0313, cell0314, cell0315, cell0316, cell0317, cell0318, cell0319]

theorem cells07_valid : ∀ w ∈ cells07, w.check T = true :=
  (forall_mem_cons_of cell0280_ok (forall_mem_cons_of cell0281_ok (forall_mem_cons_of cell0282_ok (forall_mem_cons_of cell0283_ok (forall_mem_cons_of cell0284_ok (forall_mem_cons_of cell0285_ok (forall_mem_cons_of cell0286_ok (forall_mem_cons_of cell0287_ok (forall_mem_cons_of cell0288_ok (forall_mem_cons_of cell0289_ok (forall_mem_cons_of cell0290_ok (forall_mem_cons_of cell0291_ok (forall_mem_cons_of cell0292_ok (forall_mem_cons_of cell0293_ok (forall_mem_cons_of cell0294_ok (forall_mem_cons_of cell0295_ok (forall_mem_cons_of cell0296_ok (forall_mem_cons_of cell0297_ok (forall_mem_cons_of cell0298_ok (forall_mem_cons_of cell0299_ok (forall_mem_cons_of cell0300_ok (forall_mem_cons_of cell0301_ok (forall_mem_cons_of cell0302_ok (forall_mem_cons_of cell0303_ok (forall_mem_cons_of cell0304_ok (forall_mem_cons_of cell0305_ok (forall_mem_cons_of cell0306_ok (forall_mem_cons_of cell0307_ok (forall_mem_cons_of cell0308_ok (forall_mem_cons_of cell0309_ok (forall_mem_cons_of cell0310_ok (forall_mem_cons_of cell0311_ok (forall_mem_cons_of cell0312_ok (forall_mem_cons_of cell0313_ok (forall_mem_cons_of cell0314_ok (forall_mem_cons_of cell0315_ok (forall_mem_cons_of cell0316_ok (forall_mem_cons_of cell0317_ok (forall_mem_cons_of cell0318_ok (forall_mem_cons_of cell0319_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


