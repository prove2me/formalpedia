-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells13
-- name    : CK_CKLaneC_SAxis_Data_Cells13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T04:17:23.251068+00:00
-- url     : https://prove2.me/theorems/2419d577-b88a-4622-9d1d-afa56bab5c7b
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells13` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells13` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells13` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells13 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells13.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells13 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 13 (cells 520..559). -/

def cell0520 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (40071 / 6400 : ℚ), (160681 / 25600 : ℚ), (.chain [(5, 19)]), (.chain [(5, 19)]), (.chain [(5, 19)]), (.chain [(5, 19)]), (.chain [(5, 19), (5, 20)]), (.chain [(5, 19)]), .one⟩
theorem cell0520_ok : cell0520.check T = true := by decide +kernel

def cell0521 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (160681 / 25600 : ℚ), (80539 / 12800 : ℚ), (.chain [(5, 19)]), (.chain [(5, 19)]), (.chain [(5, 19)]), (.chain [(5, 19)]), (.chain [(5, 19), (5, 20)]), (.chain [(5, 19), (5, 20)]), .three⟩
theorem cell0521_ok : cell0521.check T = true := by decide +kernel

def cell0522 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (40071 / 6400 : ℚ), (80539 / 12800 : ℚ), (.chain [(5, 19)]), (.chain [(5, 19)]), (.chain [(5, 19)]), (.chain [(5, 19)]), (.chain [(5, 19), (5, 20)]), (.chain [(5, 19), (5, 20)]), .one⟩
theorem cell0522_ok : cell0522.check T = true := by decide +kernel

def cell0523 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (80539 / 12800 : ℚ), (6459 / 1024 : ℚ), (.chain [(5, 19)]), (.chain [(5, 19)]), (.chain [(5, 19)]), (.chain [(5, 19), (5, 20)]), (.chain [(5, 19), (5, 20)]), (.chain [(5, 19), (5, 20)]), .one⟩
theorem cell0523_ok : cell0523.check T = true := by decide +kernel

def cell0524 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (6459 / 1024 : ℚ), (10117 / 1600 : ℚ), (.chain [(5, 20)]), (.chain [(5, 20)]), (.chain [(5, 20)]), (.chain [(5, 20)]), (.chain [(5, 20), (5, 21)]), (.chain [(5, 20)]), .one⟩
theorem cell0524_ok : cell0524.check T = true := by decide +kernel

def cell0525 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (80539 / 12800 : ℚ), (10117 / 1600 : ℚ), (.chain [(5, 19)]), (.chain [(5, 20)]), (.chain [(5, 20)]), (.chain [(5, 19), (5, 20)]), (.chain [(5, 20), (5, 21)]), (.chain [(5, 20), (5, 21)]), .one⟩
theorem cell0525_ok : cell0525.check T = true := by decide +kernel

def cell0526 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (10117 / 1600 : ℚ), (81333 / 12800 : ℚ), (.chain [(5, 20)]), (.chain [(5, 20)]), (.chain [(5, 20)]), (.chain [(5, 20), (5, 21)]), (.chain [(5, 20), (5, 21)]), (.chain [(5, 20), (5, 21)]), .one⟩
theorem cell0526_ok : cell0526.check T = true := by decide +kernel

def cell0527 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (10117 / 1600 : ℚ), (81333 / 12800 : ℚ), (.chain [(5, 20)]), (.chain [(5, 21)]), (.chain [(5, 20)]), (.chain [(5, 20), (5, 21)]), (.chain [(5, 21), (5, 22)]), (.chain [(5, 20), (5, 21)]), .one⟩
theorem cell0527_ok : cell0527.check T = true := by decide +kernel

def cell0528 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (10117 / 1600 : ℚ), (81333 / 12800 : ℚ), (.chain [(5, 20)]), (.chain [(5, 21)]), (.chain [(5, 21)]), (.chain [(5, 20), (5, 21)]), (.chain [(5, 21), (5, 22)]), (.chain [(5, 21)]), .one⟩
theorem cell0528_ok : cell0528.check T = true := by decide +kernel

def cell0529 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (81333 / 12800 : ℚ), (8173 / 1280 : ℚ), (.chain [(5, 21)]), (.chain [(5, 21)]), (.chain [(5, 21)]), (.chain [(5, 21), (5, 22)]), (.chain [(5, 21), (5, 22)]), (.chain [(5, 21), (5, 22)]), .one⟩
theorem cell0529_ok : cell0529.check T = true := by decide +kernel

def cell0530 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (81333 / 12800 : ℚ), (163063 / 25600 : ℚ), (.chain [(5, 21)]), (.chain [(5, 21)]), (.chain [(5, 21)]), (.chain [(5, 21)]), (.chain [(5, 21), (5, 22)]), (.chain [(5, 21), (5, 22)]), .one⟩
theorem cell0530_ok : cell0530.check T = true := by decide +kernel

def cell0531 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (163063 / 25600 : ℚ), (8173 / 1280 : ℚ), (.chain [(5, 21)]), (.chain [(5, 22)]), (.chain [(5, 22)]), (.chain [(5, 21), (5, 22)]), (.chain [(5, 22), (5, 23)]), (.chain [(5, 22)]), .one⟩
theorem cell0531_ok : cell0531.check T = true := by decide +kernel

def cell0532 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (8173 / 1280 : ℚ), (163857 / 25600 : ℚ), (.chain [(5, 22)]), (.chain [(5, 22)]), (.chain [(5, 22)]), (.chain [(5, 22)]), (.chain [(5, 22), (5, 23)]), (.chain [(5, 22)]), .one⟩
theorem cell0532_ok : cell0532.check T = true := by decide +kernel

def cell0533 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (163857 / 25600 : ℚ), (82127 / 12800 : ℚ), (.chain [(5, 22)]), (.chain [(5, 22)]), (.chain [(5, 22)]), (.chain [(5, 22), (5, 23)]), (.chain [(5, 22), (5, 23)]), (.chain [(5, 22), (5, 23)]), .one⟩
theorem cell0533_ok : cell0533.check T = true := by decide +kernel

def cell0534 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (8173 / 1280 : ℚ), (163857 / 25600 : ℚ), (.chain [(5, 22)]), (.chain [(5, 22)]), (.chain [(5, 22)]), (.chain [(5, 22)]), (.chain [(5, 22), (5, 23)]), (.chain [(5, 22), (5, 23)]), .one⟩
theorem cell0534_ok : cell0534.check T = true := by decide +kernel

def cell0535 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (163857 / 25600 : ℚ), (82127 / 12800 : ℚ), (.chain [(5, 22)]), (.chain [(5, 23)]), (.chain [(5, 22)]), (.chain [(5, 22), (5, 23)]), (.chain [(5, 23), (5, 24)]), (.chain [(5, 22), (5, 23)]), .one⟩
theorem cell0535_ok : cell0535.check T = true := by decide +kernel

def cell0536 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (82127 / 12800 : ℚ), (20631 / 3200 : ℚ), (.chain [(5, 23)]), (.chain [(5, 23)]), (.chain [(5, 23)]), (.chain [(5, 23)]), (.chain [(5, 23), (5, 24)]), (.chain [(5, 23)]), .one⟩
theorem cell0536_ok : cell0536.check T = true := by decide +kernel

def cell0537 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (82127 / 12800 : ℚ), (20631 / 3200 : ℚ), (.chain [(5, 23)]), (.chain [(5, 23)]), (.chain [(5, 23)]), (.chain [(5, 23)]), (.chain [(5, 23), (5, 24)]), (.chain [(5, 23), (5, 24)]), .one⟩
theorem cell0537_ok : cell0537.check T = true := by decide +kernel

def cell0538 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (82127 / 12800 : ℚ), (20631 / 3200 : ℚ), (.chain [(5, 23)]), (.chain [(5, 23)]), (.chain [(5, 23)]), (.chain [(5, 23)]), (.chain [(5, 23), (5, 24)]), (.chain [(5, 23), (5, 24)]), .one⟩
theorem cell0538_ok : cell0538.check T = true := by decide +kernel

def cell0539 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (20631 / 3200 : ℚ), (33089 / 5120 : ℚ), (.chain [(5, 23)]), (.chain [(5, 23)]), (.chain [(5, 23)]), (.chain [(5, 23), (5, 24)]), (.chain [(5, 23), (5, 24)]), (.chain [(5, 23), (5, 24)]), .one⟩
theorem cell0539_ok : cell0539.check T = true := by decide +kernel

def cell0540 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (33089 / 5120 : ℚ), (82921 / 12800 : ℚ), (.chain [(5, 24)]), (.chain [(5, 24)]), (.chain [(5, 24)]), (.chain [(5, 24)]), (.chain [(5, 24), (5, 25)]), (.chain [(5, 24)]), .one⟩
theorem cell0540_ok : cell0540.check T = true := by decide +kernel

def cell0541 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (20631 / 3200 : ℚ), (33089 / 5120 : ℚ), (.chain [(5, 23)]), (.chain [(5, 24)]), (.chain [(5, 24)]), (.chain [(5, 23), (5, 24)]), (.chain [(5, 24), (5, 25)]), (.chain [(5, 24)]), .one⟩
theorem cell0541_ok : cell0541.check T = true := by decide +kernel

def cell0542 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (33089 / 5120 : ℚ), (82921 / 12800 : ℚ), (.chain [(5, 24)]), (.chain [(5, 24)]), (.chain [(5, 24)]), (.chain [(5, 24)]), (.chain [(5, 24), (5, 25)]), (.chain [(5, 24), (5, 25)]), .one⟩
theorem cell0542_ok : cell0542.check T = true := by decide +kernel

def cell0543 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (82921 / 12800 : ℚ), (41659 / 6400 : ℚ), (.chain [(5, 24)]), (.chain [(5, 24)]), (.chain [(5, 24)]), (.chain [(5, 24), (5, 25)]), (.chain [(5, 24), (5, 25)]), (.chain [(5, 24), (5, 25)]), .one⟩
theorem cell0543_ok : cell0543.check T = true := by decide +kernel

def cell0544 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (82921 / 12800 : ℚ), (41659 / 6400 : ℚ), (.chain [(5, 24)]), (.chain [(5, 24)]), (.chain [(5, 24)]), (.chain [(5, 24), (5, 25)]), (.chain [(5, 24), (5, 25)]), (.chain [(5, 24), (5, 25)]), .one⟩
theorem cell0544_ok : cell0544.check T = true := by decide +kernel

def cell0545 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (82921 / 12800 : ℚ), (166239 / 25600 : ℚ), (.chain [(5, 24)]), (.chain [(5, 25)]), (.chain [(5, 24)]), (.chain [(5, 24)]), (.chain [(5, 25)]), (.chain [(5, 24), (5, 25)]), .one⟩
theorem cell0545_ok : cell0545.check T = true := by decide +kernel

def cell0546 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (166239 / 25600 : ℚ), (41659 / 6400 : ℚ), (.chain [(5, 24)]), (.chain [(5, 25)]), (.chain [(5, 25)]), (.chain [(5, 24), (5, 25)]), (.chain [(5, 25), (5, 26)]), (.chain [(5, 25)]), .three⟩
theorem cell0546_ok : cell0546.check T = true := by decide +kernel

def cell0547 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (41659 / 6400 : ℚ), (167033 / 25600 : ℚ), (.chain [(5, 25)]), (.chain [(5, 25)]), (.chain [(5, 25)]), (.chain [(5, 25)]), (.chain [(5, 25), (5, 26)]), (.chain [(5, 25)]), .one⟩
theorem cell0547_ok : cell0547.check T = true := by decide +kernel

def cell0548 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (167033 / 25600 : ℚ), (16743 / 2560 : ℚ), (.chain [(5, 25)]), (.chain [(5, 25)]), (.chain [(5, 25)]), (.chain [(5, 25), (5, 26)]), (.chain [(5, 25), (5, 26)]), (.chain [(5, 25), (5, 26)]), .one⟩
theorem cell0548_ok : cell0548.check T = true := by decide +kernel

def cell0549 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (41659 / 6400 : ℚ), (167033 / 25600 : ℚ), (.chain [(5, 25)]), (.chain [(5, 25)]), (.chain [(5, 25)]), (.chain [(5, 25)]), (.chain [(5, 25), (5, 26)]), (.chain [(5, 25), (5, 26)]), .one⟩
theorem cell0549_ok : cell0549.check T = true := by decide +kernel

def cell0550 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (167033 / 25600 : ℚ), (16743 / 2560 : ℚ), (.chain [(5, 25)]), (.chain [(5, 26)]), (.chain [(5, 25)]), (.chain [(5, 25), (5, 26)]), (.chain [(5, 26), (5, 27)]), (.chain [(5, 25), (5, 26)]), .one⟩
theorem cell0550_ok : cell0550.check T = true := by decide +kernel

def cell0551 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (16743 / 2560 : ℚ), (167827 / 25600 : ℚ), (.chain [(5, 26)]), (.chain [(5, 26)]), (.chain [(5, 26)]), (.chain [(5, 26)]), (.chain [(5, 26), (5, 27)]), (.chain [(5, 26)]), .one⟩
theorem cell0551_ok : cell0551.check T = true := by decide +kernel

def cell0552 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (167827 / 25600 : ℚ), (5257 / 800 : ℚ), (.chain [(5, 26)]), (.chain [(5, 26)]), (.chain [(5, 26)]), (.chain [(5, 26)]), (.chain [(5, 26), (5, 27)]), (.chain [(5, 26), (5, 27)]), .three⟩
theorem cell0552_ok : cell0552.check T = true := by decide +kernel

def cell0553 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (16743 / 2560 : ℚ), (5257 / 800 : ℚ), (.chain [(5, 26)]), (.chain [(5, 26)]), (.chain [(5, 26)]), (.chain [(5, 26)]), (.chain [(5, 26), (5, 27)]), (.chain [(5, 26), (5, 27)]), .one⟩
theorem cell0553_ok : cell0553.check T = true := by decide +kernel

def cell0554 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (5257 / 800 : ℚ), (168621 / 25600 : ℚ), (.chain [(5, 26)]), (.chain [(5, 26)]), (.chain [(5, 26)]), (.chain [(5, 26), (5, 27)]), (.chain [(5, 26), (5, 27)]), (.chain [(5, 26), (5, 27)]), .one⟩
theorem cell0554_ok : cell0554.check T = true := by decide +kernel

def cell0555 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (168621 / 25600 : ℚ), (84509 / 12800 : ℚ), (.chain [(5, 27)]), (.chain [(5, 27)]), (.chain [(5, 27)]), (.chain [(5, 27)]), (.chain [(5, 27), (5, 28)]), (.chain [(5, 27)]), .one⟩
theorem cell0555_ok : cell0555.check T = true := by decide +kernel

def cell0556 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (5257 / 800 : ℚ), (168621 / 25600 : ℚ), (.chain [(5, 26)]), (.chain [(5, 27)]), (.chain [(5, 27)]), (.chain [(5, 26), (5, 27)]), (.chain [(5, 27), (5, 28)]), (.chain [(5, 27)]), .one⟩
theorem cell0556_ok : cell0556.check T = true := by decide +kernel

def cell0557 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (168621 / 25600 : ℚ), (84509 / 12800 : ℚ), (.chain [(5, 27)]), (.chain [(5, 27)]), (.chain [(5, 27)]), (.chain [(5, 27)]), (.chain [(5, 27), (5, 28)]), (.chain [(5, 27), (5, 28)]), .one⟩
theorem cell0557_ok : cell0557.check T = true := by decide +kernel

def cell0558 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (84509 / 12800 : ℚ), (33883 / 5120 : ℚ), (.chain [(5, 27)]), (.chain [(5, 27)]), (.chain [(5, 27)]), (.chain [(5, 27), (5, 28)]), (.chain [(5, 27), (5, 28)]), (.chain [(5, 27), (5, 28)]), .one⟩
theorem cell0558_ok : cell0558.check T = true := by decide +kernel

def cell0559 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (33883 / 5120 : ℚ), (42453 / 6400 : ℚ), (.chain [(5, 28)]), (.chain [(5, 28)]), (.chain [(5, 28)]), (.chain [(5, 28)]), (.chain [(5, 28)]), (.chain [(5, 28)]), .one⟩
theorem cell0559_ok : cell0559.check T = true := by decide +kernel

def cells13 : List CellW := [cell0520, cell0521, cell0522, cell0523, cell0524, cell0525, cell0526, cell0527, cell0528, cell0529, cell0530, cell0531, cell0532, cell0533, cell0534, cell0535, cell0536, cell0537, cell0538, cell0539, cell0540, cell0541, cell0542, cell0543, cell0544, cell0545, cell0546, cell0547, cell0548, cell0549, cell0550, cell0551, cell0552, cell0553, cell0554, cell0555, cell0556, cell0557, cell0558, cell0559]

theorem cells13_valid : ∀ w ∈ cells13, w.check T = true :=
  (forall_mem_cons_of cell0520_ok (forall_mem_cons_of cell0521_ok (forall_mem_cons_of cell0522_ok (forall_mem_cons_of cell0523_ok (forall_mem_cons_of cell0524_ok (forall_mem_cons_of cell0525_ok (forall_mem_cons_of cell0526_ok (forall_mem_cons_of cell0527_ok (forall_mem_cons_of cell0528_ok (forall_mem_cons_of cell0529_ok (forall_mem_cons_of cell0530_ok (forall_mem_cons_of cell0531_ok (forall_mem_cons_of cell0532_ok (forall_mem_cons_of cell0533_ok (forall_mem_cons_of cell0534_ok (forall_mem_cons_of cell0535_ok (forall_mem_cons_of cell0536_ok (forall_mem_cons_of cell0537_ok (forall_mem_cons_of cell0538_ok (forall_mem_cons_of cell0539_ok (forall_mem_cons_of cell0540_ok (forall_mem_cons_of cell0541_ok (forall_mem_cons_of cell0542_ok (forall_mem_cons_of cell0543_ok (forall_mem_cons_of cell0544_ok (forall_mem_cons_of cell0545_ok (forall_mem_cons_of cell0546_ok (forall_mem_cons_of cell0547_ok (forall_mem_cons_of cell0548_ok (forall_mem_cons_of cell0549_ok (forall_mem_cons_of cell0550_ok (forall_mem_cons_of cell0551_ok (forall_mem_cons_of cell0552_ok (forall_mem_cons_of cell0553_ok (forall_mem_cons_of cell0554_ok (forall_mem_cons_of cell0555_ok (forall_mem_cons_of cell0556_ok (forall_mem_cons_of cell0557_ok (forall_mem_cons_of cell0558_ok (forall_mem_cons_of cell0559_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


