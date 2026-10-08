-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells05
-- name    : CK_CKLaneC_SAxis_Data_Cells05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T04:05:10.449982+00:00
-- url     : https://prove2.me/theorems/ab5865f2-5b34-4872-b33a-41fe550bc5be
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells05` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells05` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells05` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells05 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells05.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells05 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 5 (cells 200..239). -/

def cell0200 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (4341 / 6400 : ℚ), (17761 / 25600 : ℚ), (.chain [(1, 7)]), (.chain [(1, 8)]), (.chain [(1, 7)]), (.chain [(1, 7)]), (.chain [(1, 8)]), (.chain [(1, 7), (1, 8)]), .two⟩
theorem cell0200_ok : cell0200.check T = true := by decide +kernel

def cell0201 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (17761 / 25600 : ℚ), (9079 / 12800 : ℚ), (.chain [(1, 7)]), (.chain [(1, 8)]), (.chain [(1, 7)]), (.chain [(1, 7), (1, 8)]), (.chain [(1, 8), (1, 9)]), (.chain [(1, 7), (1, 8)]), .three⟩
theorem cell0201_ok : cell0201.check T = true := by decide +kernel

def cell0202 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (17761 / 25600 : ℚ), (9079 / 12800 : ℚ), (.chain [(1, 7)]), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 7), (1, 8)]), (.chain [(1, 8), (1, 9)]), (.chain [(1, 8)]), .three⟩
theorem cell0202_ok : cell0202.check T = true := by decide +kernel

def cell0203 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (9079 / 12800 : ℚ), (3711 / 5120 : ℚ), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8)]), .two⟩
theorem cell0203_ok : cell0203.check T = true := by decide +kernel

def cell0204 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (9079 / 12800 : ℚ), (3711 / 5120 : ℚ), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8), (1, 9)]), (.chain [(1, 8)]), .three⟩
theorem cell0204_ok : cell0204.check T = true := by decide +kernel

def cell0205 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (3711 / 5120 : ℚ), (2369 / 3200 : ℚ), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8), (1, 9)]), (.chain [(1, 8), (1, 9)]), (.chain [(1, 8), (1, 9)]), .three⟩
theorem cell0205_ok : cell0205.check T = true := by decide +kernel

def cell0206 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (3711 / 5120 : ℚ), (2369 / 3200 : ℚ), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8), (1, 9)]), (.chain [(1, 8), (1, 9)]), (.chain [(1, 8), (1, 9)]), .two⟩
theorem cell0206_ok : cell0206.check T = true := by decide +kernel

def cell0207 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (9079 / 12800 : ℚ), (36713 / 51200 : ℚ), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8), (1, 9)]), (.chain [(1, 8)]), .three⟩
theorem cell0207_ok : cell0207.check T = true := by decide +kernel

def cell0208 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (36713 / 51200 : ℚ), (3711 / 5120 : ℚ), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 8), (1, 9)]), (.chain [(1, 8), (1, 9)]), .three⟩
theorem cell0208_ok : cell0208.check T = true := by decide +kernel

def cell0209 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (36713 / 51200 : ℚ), (3711 / 5120 : ℚ), (.chain [(1, 8)]), (.chain [(1, 9)]), (.chain [(1, 8)]), (.chain [(1, 8)]), (.chain [(1, 9)]), (.chain [(1, 8), (1, 9)]), .three⟩
theorem cell0209_ok : cell0209.check T = true := by decide +kernel

def cell0210 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (3711 / 5120 : ℚ), (2369 / 3200 : ℚ), (.chain [(1, 8)]), (.chain [(1, 9)]), (.chain [(1, 8)]), (.chain [(1, 8), (1, 9)]), (.chain [(1, 9)]), (.chain [(1, 8), (1, 9)]), .two⟩
theorem cell0210_ok : cell0210.check T = true := by decide +kernel

def cell0211 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (3711 / 5120 : ℚ), (2369 / 3200 : ℚ), (.chain [(1, 8)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 8), (1, 9)]), (.chain [(1, 9), (1, 10)]), (.chain [(1, 9)]), .three⟩
theorem cell0211_ok : cell0211.check T = true := by decide +kernel

def cell0212 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (2369 / 3200 : ℚ), (38301 / 51200 : ℚ), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), .three⟩
theorem cell0212_ok : cell0212.check T = true := by decide +kernel

def cell0213 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (38301 / 51200 : ℚ), (19349 / 25600 : ℚ), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), .three⟩
theorem cell0213_ok : cell0213.check T = true := by decide +kernel

def cell0214 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (2369 / 3200 : ℚ), (19349 / 25600 : ℚ), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), .three⟩
theorem cell0214_ok : cell0214.check T = true := by decide +kernel

def cell0215 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (19349 / 25600 : ℚ), (9873 / 12800 : ℚ), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9), (1, 10)]), (.chain [(1, 9), (1, 10)]), .three⟩
theorem cell0215_ok : cell0215.check T = true := by decide +kernel

def cell0216 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (19349 / 25600 : ℚ), (9873 / 12800 : ℚ), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9), (1, 10)]), (.chain [(1, 9), (1, 10)]), .three⟩
theorem cell0216_ok : cell0216.check T = true := by decide +kernel

def cell0217 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (2369 / 3200 : ℚ), (19349 / 25600 : ℚ), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9), (1, 10)]), (.chain [(1, 9)]), .three⟩
theorem cell0217_ok : cell0217.check T = true := by decide +kernel

def cell0218 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (2369 / 3200 : ℚ), (19349 / 25600 : ℚ), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9), (1, 10)]), (.chain [(1, 9)]), .three⟩
theorem cell0218_ok : cell0218.check T = true := by decide +kernel

def cell0219 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (19349 / 25600 : ℚ), (7819 / 10240 : ℚ), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9), (1, 10)]), (.chain [(1, 9), (1, 10)]), .three⟩
theorem cell0219_ok : cell0219.check T = true := by decide +kernel

def cell0220 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (7819 / 10240 : ℚ), (9873 / 12800 : ℚ), (.chain [(1, 9)]), (.chain [(1, 10)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 10)]), (.chain [(1, 9), (1, 10)]), .three⟩
theorem cell0220_ok : cell0220.check T = true := by decide +kernel

def cell0221 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (19349 / 25600 : ℚ), (9873 / 12800 : ℚ), (.chain [(1, 9)]), (.chain [(1, 10)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 10)]), (.chain [(1, 9), (1, 10)]), .three⟩
theorem cell0221_ok : cell0221.check T = true := by decide +kernel

def cell0222 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (9873 / 12800 : ℚ), (39889 / 51200 : ℚ), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9)]), (.chain [(1, 9), (1, 10)]), (.chain [(1, 9), (1, 10)]), (.chain [(1, 9), (1, 10)]), .three⟩
theorem cell0222_ok : cell0222.check T = true := by decide +kernel

def cell0223 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (39889 / 51200 : ℚ), (20143 / 25600 : ℚ), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), .three⟩
theorem cell0223_ok : cell0223.check T = true := by decide +kernel

def cell0224 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (9873 / 12800 : ℚ), (20143 / 25600 : ℚ), (.chain [(1, 9)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 9), (1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), .two⟩
theorem cell0224_ok : cell0224.check T = true := by decide +kernel

def cell0225 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (20143 / 25600 : ℚ), (1027 / 1280 : ℚ), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), .three⟩
theorem cell0225_ok : cell0225.check T = true := by decide +kernel

def cell0226 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (20143 / 25600 : ℚ), (1027 / 1280 : ℚ), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10), (1, 11)]), (.chain [(1, 10)]), .three⟩
theorem cell0226_ok : cell0226.check T = true := by decide +kernel

def cell0227 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (9873 / 12800 : ℚ), (20143 / 25600 : ℚ), (.chain [(1, 9)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 9), (1, 10)]), (.chain [(1, 10), (1, 11)]), (.chain [(1, 10)]), .three⟩
theorem cell0227_ok : cell0227.check T = true := by decide +kernel

def cell0228 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (9873 / 12800 : ℚ), (20143 / 25600 : ℚ), (.chain [(1, 9)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 9), (1, 10)]), (.chain [(1, 10), (1, 11)]), (.chain [(1, 10)]), .three⟩
theorem cell0228_ok : cell0228.check T = true := by decide +kernel

def cell0229 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (20143 / 25600 : ℚ), (1027 / 1280 : ℚ), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10), (1, 11)]), (.chain [(1, 10), (1, 11)]), .three⟩
theorem cell0229_ok : cell0229.check T = true := by decide +kernel

def cell0230 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (20143 / 25600 : ℚ), (40683 / 51200 : ℚ), (.chain [(1, 10)]), (.chain [(1, 11)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 11)]), (.chain [(1, 10)]), .three⟩
theorem cell0230_ok : cell0230.check T = true := by decide +kernel

def cell0231 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (40683 / 51200 : ℚ), (1027 / 1280 : ℚ), (.chain [(1, 10)]), (.chain [(1, 11)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 11)]), (.chain [(1, 10), (1, 11)]), .three⟩
theorem cell0231_ok : cell0231.check T = true := by decide +kernel

def cell0232 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (1027 / 1280 : ℚ), (20937 / 25600 : ℚ), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10), (1, 11)]), (.chain [(1, 10), (1, 11)]), (.chain [(1, 10), (1, 11)]), .three⟩
theorem cell0232_ok : cell0232.check T = true := by decide +kernel

def cell0233 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (1027 / 1280 : ℚ), (41477 / 51200 : ℚ), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10)]), (.chain [(1, 10), (1, 11)]), (.chain [(1, 10), (1, 11)]), .three⟩
theorem cell0233_ok : cell0233.check T = true := by decide +kernel

def cell0234 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (41477 / 51200 : ℚ), (20937 / 25600 : ℚ), (.chain [(1, 10)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 10), (1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), .three⟩
theorem cell0234_ok : cell0234.check T = true := by decide +kernel

def cell0235 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (20937 / 25600 : ℚ), (42271 / 51200 : ℚ), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), .three⟩
theorem cell0235_ok : cell0235.check T = true := by decide +kernel

def cell0236 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (42271 / 51200 : ℚ), (10667 / 12800 : ℚ), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), .three⟩
theorem cell0236_ok : cell0236.check T = true := by decide +kernel

def cell0237 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (20937 / 25600 : ℚ), (10667 / 12800 : ℚ), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 11)]), .three⟩
theorem cell0237_ok : cell0237.check T = true := by decide +kernel

def cell0238 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (1027 / 1280 : ℚ), (20937 / 25600 : ℚ), (.chain [(1, 10)]), (.chain [(1, 11)]), (.chain [(1, 10)]), (.chain [(1, 10), (1, 11)]), (.chain [(1, 11)]), (.chain [(1, 10), (1, 11)]), .two⟩
theorem cell0238_ok : cell0238.check T = true := by decide +kernel

def cell0239 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (1027 / 1280 : ℚ), (20937 / 25600 : ℚ), (.chain [(1, 10)]), (.chain [(1, 11)]), (.chain [(1, 11)]), (.chain [(1, 10), (1, 11)]), (.chain [(1, 11), (1, 12)]), (.chain [(1, 11)]), .three⟩
theorem cell0239_ok : cell0239.check T = true := by decide +kernel

def cells05 : List CellW := [cell0200, cell0201, cell0202, cell0203, cell0204, cell0205, cell0206, cell0207, cell0208, cell0209, cell0210, cell0211, cell0212, cell0213, cell0214, cell0215, cell0216, cell0217, cell0218, cell0219, cell0220, cell0221, cell0222, cell0223, cell0224, cell0225, cell0226, cell0227, cell0228, cell0229, cell0230, cell0231, cell0232, cell0233, cell0234, cell0235, cell0236, cell0237, cell0238, cell0239]

theorem cells05_valid : ∀ w ∈ cells05, w.check T = true :=
  (forall_mem_cons_of cell0200_ok (forall_mem_cons_of cell0201_ok (forall_mem_cons_of cell0202_ok (forall_mem_cons_of cell0203_ok (forall_mem_cons_of cell0204_ok (forall_mem_cons_of cell0205_ok (forall_mem_cons_of cell0206_ok (forall_mem_cons_of cell0207_ok (forall_mem_cons_of cell0208_ok (forall_mem_cons_of cell0209_ok (forall_mem_cons_of cell0210_ok (forall_mem_cons_of cell0211_ok (forall_mem_cons_of cell0212_ok (forall_mem_cons_of cell0213_ok (forall_mem_cons_of cell0214_ok (forall_mem_cons_of cell0215_ok (forall_mem_cons_of cell0216_ok (forall_mem_cons_of cell0217_ok (forall_mem_cons_of cell0218_ok (forall_mem_cons_of cell0219_ok (forall_mem_cons_of cell0220_ok (forall_mem_cons_of cell0221_ok (forall_mem_cons_of cell0222_ok (forall_mem_cons_of cell0223_ok (forall_mem_cons_of cell0224_ok (forall_mem_cons_of cell0225_ok (forall_mem_cons_of cell0226_ok (forall_mem_cons_of cell0227_ok (forall_mem_cons_of cell0228_ok (forall_mem_cons_of cell0229_ok (forall_mem_cons_of cell0230_ok (forall_mem_cons_of cell0231_ok (forall_mem_cons_of cell0232_ok (forall_mem_cons_of cell0233_ok (forall_mem_cons_of cell0234_ok (forall_mem_cons_of cell0235_ok (forall_mem_cons_of cell0236_ok (forall_mem_cons_of cell0237_ok (forall_mem_cons_of cell0238_ok (forall_mem_cons_of cell0239_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


