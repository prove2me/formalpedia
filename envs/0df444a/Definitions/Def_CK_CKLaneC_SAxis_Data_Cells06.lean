-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells06
-- name    : CK_CKLaneC_SAxis_Data_Cells06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T06:20:31.129113+00:00
-- url     : https://prove2.me/theorems/d961856e-a33a-466c-8e91-4a75d0dc405e
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells06` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells06` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells06` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells06 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells06.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells06 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 6 (cells 240..279). -/

def cell0240 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (20937 / 25600 : ℚ), (10667 / 12800 : ℚ), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11), (1, 12)]), (.chain [(1, 11)]), .three⟩
theorem cell0240_ok : cell0240.check T = true := by decide +kernel

def cell0241 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (20937 / 25600 : ℚ), (10667 / 12800 : ℚ), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11), (1, 12)]), (.chain [(1, 11)]), .three⟩
theorem cell0241_ok : cell0241.check T = true := by decide +kernel

def cell0242 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (10667 / 12800 : ℚ), (21731 / 25600 : ℚ), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11), (1, 12)]), (.chain [(1, 11)]), .three⟩
theorem cell0242_ok : cell0242.check T = true := by decide +kernel

def cell0243 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (10667 / 12800 : ℚ), (21731 / 25600 : ℚ), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11), (1, 12)]), (.chain [(1, 11), (1, 12)]), .three⟩
theorem cell0243_ok : cell0243.check T = true := by decide +kernel

def cell0244 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (21731 / 25600 : ℚ), (43859 / 51200 : ℚ), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11), (1, 12)]), (.chain [(1, 11), (1, 12)]), (.chain [(1, 11), (1, 12)]), .three⟩
theorem cell0244_ok : cell0244.check T = true := by decide +kernel

def cell0245 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (43859 / 51200 : ℚ), (1383 / 1600 : ℚ), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), .three⟩
theorem cell0245_ok : cell0245.check T = true := by decide +kernel

def cell0246 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (21731 / 25600 : ℚ), (43859 / 51200 : ℚ), (.chain [(1, 11)]), (.chain [(1, 12)]), (.chain [(1, 11)]), (.chain [(1, 11), (1, 12)]), (.chain [(1, 12)]), (.chain [(1, 11), (1, 12)]), .three⟩
theorem cell0246_ok : cell0246.check T = true := by decide +kernel

def cell0247 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (43859 / 51200 : ℚ), (1383 / 1600 : ℚ), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), .three⟩
theorem cell0247_ok : cell0247.check T = true := by decide +kernel

def cell0248 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (10667 / 12800 : ℚ), (8613 / 10240 : ℚ), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11), (1, 12)]), (.chain [(1, 11), (1, 12)]), .three⟩
theorem cell0248_ok : cell0248.check T = true := by decide +kernel

def cell0249 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (8613 / 10240 : ℚ), (21731 / 25600 : ℚ), (.chain [(1, 11)]), (.chain [(1, 12)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 12)]), (.chain [(1, 11), (1, 12)]), .three⟩
theorem cell0249_ok : cell0249.check T = true := by decide +kernel

def cell0250 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (10667 / 12800 : ℚ), (21731 / 25600 : ℚ), (.chain [(1, 11)]), (.chain [(1, 12)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 12)]), (.chain [(1, 11), (1, 12)]), .three⟩
theorem cell0250_ok : cell0250.check T = true := by decide +kernel

def cell0251 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (21731 / 25600 : ℚ), (1383 / 1600 : ℚ), (.chain [(1, 11)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 11), (1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), .three⟩
theorem cell0251_ok : cell0251.check T = true := by decide +kernel

def cell0252 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (21731 / 25600 : ℚ), (1383 / 1600 : ℚ), (.chain [(1, 11)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 11), (1, 12)]), (.chain [(1, 12), (1, 13)]), (.chain [(1, 12)]), .three⟩
theorem cell0252_ok : cell0252.check T = true := by decide +kernel

def cell0253 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (1383 / 1600 : ℚ), (901 / 1024 : ℚ), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), .three⟩
theorem cell0253_ok : cell0253.check T = true := by decide +kernel

def cell0254 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (1383 / 1600 : ℚ), (901 / 1024 : ℚ), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12), (1, 13)]), (.chain [(1, 12)]), .three⟩
theorem cell0254_ok : cell0254.check T = true := by decide +kernel

def cell0255 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (901 / 1024 : ℚ), (11461 / 12800 : ℚ), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12), (1, 13)]), (.chain [(1, 12), (1, 13)]), (.chain [(1, 12), (1, 13)]), .three⟩
theorem cell0255_ok : cell0255.check T = true := by decide +kernel

def cell0256 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (901 / 1024 : ℚ), (11461 / 12800 : ℚ), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12), (1, 13)]), (.chain [(1, 12), (1, 13)]), (.chain [(1, 12), (1, 13)]), .two⟩
theorem cell0256_ok : cell0256.check T = true := by decide +kernel

def cell0257 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (1383 / 1600 : ℚ), (901 / 1024 : ℚ), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12), (1, 13)]), (.chain [(1, 12)]), .three⟩
theorem cell0257_ok : cell0257.check T = true := by decide +kernel

def cell0258 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (1383 / 1600 : ℚ), (44653 / 51200 : ℚ), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 12), (1, 13)]), (.chain [(1, 12)]), .three⟩
theorem cell0258_ok : cell0258.check T = true := by decide +kernel

def cell0259 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (44653 / 51200 : ℚ), (901 / 1024 : ℚ), (.chain [(1, 12)]), (.chain [(1, 13)]), (.chain [(1, 12)]), (.chain [(1, 12)]), (.chain [(1, 13)]), (.chain [(1, 12), (1, 13)]), .three⟩
theorem cell0259_ok : cell0259.check T = true := by decide +kernel

def cell0260 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (901 / 1024 : ℚ), (11461 / 12800 : ℚ), (.chain [(1, 12)]), (.chain [(1, 13)]), (.chain [(1, 12)]), (.chain [(1, 12), (1, 13)]), (.chain [(1, 13)]), (.chain [(1, 12), (1, 13)]), .two⟩
theorem cell0260_ok : cell0260.check T = true := by decide +kernel

def cell0261 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (901 / 1024 : ℚ), (11461 / 12800 : ℚ), (.chain [(1, 12)]), (.chain [(1, 13)]), (.chain [(1, 12)]), (.chain [(1, 12), (1, 13)]), (.chain [(1, 13), (1, 14)]), (.chain [(1, 12), (1, 13)]), .three⟩
theorem cell0261_ok : cell0261.check T = true := by decide +kernel

def cell0262 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (11461 / 12800 : ℚ), (46241 / 51200 : ℚ), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), .three⟩
theorem cell0262_ok : cell0262.check T = true := by decide +kernel

def cell0263 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (46241 / 51200 : ℚ), (23319 / 25600 : ℚ), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), .three⟩
theorem cell0263_ok : cell0263.check T = true := by decide +kernel

def cell0264 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (11461 / 12800 : ℚ), (23319 / 25600 : ℚ), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), .three⟩
theorem cell0264_ok : cell0264.check T = true := by decide +kernel

def cell0265 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (23319 / 25600 : ℚ), (5929 / 6400 : ℚ), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13), (1, 14)]), (.chain [(1, 13)]), .three⟩
theorem cell0265_ok : cell0265.check T = true := by decide +kernel

def cell0266 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (23319 / 25600 : ℚ), (5929 / 6400 : ℚ), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13), (1, 14)]), (.chain [(1, 13), (1, 14)]), .three⟩
theorem cell0266_ok : cell0266.check T = true := by decide +kernel

def cell0267 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (11461 / 12800 : ℚ), (23319 / 25600 : ℚ), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13), (1, 14)]), (.chain [(1, 13)]), .three⟩
theorem cell0267_ok : cell0267.check T = true := by decide +kernel

def cell0268 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (23319 / 25600 : ℚ), (5929 / 6400 : ℚ), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13), (1, 14)]), (.chain [(1, 13), (1, 14)]), .three⟩
theorem cell0268_ok : cell0268.check T = true := by decide +kernel

def cell0269 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (23319 / 25600 : ℚ), (5929 / 6400 : ℚ), (.chain [(1, 13)]), (.chain [(1, 14)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 14)]), (.chain [(1, 13), (1, 14)]), .three⟩
theorem cell0269_ok : cell0269.check T = true := by decide +kernel

def cell0270 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (5929 / 6400 : ℚ), (24113 / 25600 : ℚ), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13)]), (.chain [(1, 13), (1, 14)]), (.chain [(1, 13), (1, 14)]), (.chain [(1, 13), (1, 14)]), .three⟩
theorem cell0270_ok : cell0270.check T = true := by decide +kernel

def cell0271 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (5929 / 6400 : ℚ), (24113 / 25600 : ℚ), (.chain [(1, 13)]), (.chain [(1, 14)]), (.chain [(1, 13)]), (.chain [(1, 13), (1, 14)]), (.chain [(1, 14)]), (.chain [(1, 13), (1, 14)]), .two⟩
theorem cell0271_ok : cell0271.check T = true := by decide +kernel

def cell0272 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (24113 / 25600 : ℚ), (2451 / 2560 : ℚ), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14)]), .three⟩
theorem cell0272_ok : cell0272.check T = true := by decide +kernel

def cell0273 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (24113 / 25600 : ℚ), (2451 / 2560 : ℚ), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14), (1, 15)]), (.chain [(1, 14)]), .three⟩
theorem cell0273_ok : cell0273.check T = true := by decide +kernel

def cell0274 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (5929 / 6400 : ℚ), (24113 / 25600 : ℚ), (.chain [(1, 13)]), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 13), (1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14)]), .three⟩
theorem cell0274_ok : cell0274.check T = true := by decide +kernel

def cell0275 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (5929 / 6400 : ℚ), (24113 / 25600 : ℚ), (.chain [(1, 13)]), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 13), (1, 14)]), (.chain [(1, 14), (1, 15)]), (.chain [(1, 14)]), .three⟩
theorem cell0275_ok : cell0275.check T = true := by decide +kernel

def cell0276 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (24113 / 25600 : ℚ), (2451 / 2560 : ℚ), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14), (1, 15)]), (.chain [(1, 14)]), .three⟩
theorem cell0276_ok : cell0276.check T = true := by decide +kernel

def cell0277 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (24113 / 25600 : ℚ), (2451 / 2560 : ℚ), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14), (1, 15)]), (.chain [(1, 14), (1, 15)]), .three⟩
theorem cell0277_ok : cell0277.check T = true := by decide +kernel

def cell0278 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (2451 / 2560 : ℚ), (24907 / 25600 : ℚ), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14), (1, 15)]), (.chain [(1, 14), (1, 15)]), .three⟩
theorem cell0278_ok : cell0278.check T = true := by decide +kernel

def cell0279 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (24907 / 25600 : ℚ), (3163 / 3200 : ℚ), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14)]), (.chain [(1, 14), (1, 15)]), (.chain [(1, 14), (1, 15)]), (.chain [(1, 14), (1, 15)]), .two⟩
theorem cell0279_ok : cell0279.check T = true := by decide +kernel

def cells06 : List CellW := [cell0240, cell0241, cell0242, cell0243, cell0244, cell0245, cell0246, cell0247, cell0248, cell0249, cell0250, cell0251, cell0252, cell0253, cell0254, cell0255, cell0256, cell0257, cell0258, cell0259, cell0260, cell0261, cell0262, cell0263, cell0264, cell0265, cell0266, cell0267, cell0268, cell0269, cell0270, cell0271, cell0272, cell0273, cell0274, cell0275, cell0276, cell0277, cell0278, cell0279]

theorem cells06_valid : ∀ w ∈ cells06, w.check T = true :=
  (forall_mem_cons_of cell0240_ok (forall_mem_cons_of cell0241_ok (forall_mem_cons_of cell0242_ok (forall_mem_cons_of cell0243_ok (forall_mem_cons_of cell0244_ok (forall_mem_cons_of cell0245_ok (forall_mem_cons_of cell0246_ok (forall_mem_cons_of cell0247_ok (forall_mem_cons_of cell0248_ok (forall_mem_cons_of cell0249_ok (forall_mem_cons_of cell0250_ok (forall_mem_cons_of cell0251_ok (forall_mem_cons_of cell0252_ok (forall_mem_cons_of cell0253_ok (forall_mem_cons_of cell0254_ok (forall_mem_cons_of cell0255_ok (forall_mem_cons_of cell0256_ok (forall_mem_cons_of cell0257_ok (forall_mem_cons_of cell0258_ok (forall_mem_cons_of cell0259_ok (forall_mem_cons_of cell0260_ok (forall_mem_cons_of cell0261_ok (forall_mem_cons_of cell0262_ok (forall_mem_cons_of cell0263_ok (forall_mem_cons_of cell0264_ok (forall_mem_cons_of cell0265_ok (forall_mem_cons_of cell0266_ok (forall_mem_cons_of cell0267_ok (forall_mem_cons_of cell0268_ok (forall_mem_cons_of cell0269_ok (forall_mem_cons_of cell0270_ok (forall_mem_cons_of cell0271_ok (forall_mem_cons_of cell0272_ok (forall_mem_cons_of cell0273_ok (forall_mem_cons_of cell0274_ok (forall_mem_cons_of cell0275_ok (forall_mem_cons_of cell0276_ok (forall_mem_cons_of cell0277_ok (forall_mem_cons_of cell0278_ok (forall_mem_cons_of cell0279_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


