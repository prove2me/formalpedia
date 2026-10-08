-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells09
-- name    : CK_CKLaneC_SAxis_Data_Cells09
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:12:47.680301+00:00
-- url     : https://prove2.me/theorems/74d09d84-21b1-4e8a-865f-28189b3fee50
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells09` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells09` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells09` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells09 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells09.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells09 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 9 (cells 360..399). -/

def cell0360 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (19401 / 12800 : ℚ), (39199 / 25600 : ℚ), (.chain [(1, 28)]), (.chain [(1, 29)]), (.chain [(1, 28)]), (.chain [(1, 28)]), (.chain [(1, 29)]), (.chain [(1, 28), (1, 29)]), .three⟩
theorem cell0360_ok : cell0360.check T = true := by decide +kernel

def cell0361 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (39199 / 25600 : ℚ), (9899 / 6400 : ℚ), (.chain [(1, 28)]), (.chain [(1, 29)]), (.chain [(1, 29)]), (.chain [(1, 28), (1, 29)]), (.chain [(1, 29), (1, 30)]), (.chain [(1, 29)]), .three⟩
theorem cell0361_ok : cell0361.check T = true := by decide +kernel

def cell0362 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (9899 / 6400 : ℚ), (4039 / 2560 : ℚ), (.chain [(1, 29)]), (.chain [(1, 29)]), (.chain [(1, 29)]), (.chain [(1, 29), (1, 30)]), (.chain [(1, 29), (1, 30)]), (.chain [(1, 29), (1, 30)]), .two⟩
theorem cell0362_ok : cell0362.check T = true := by decide +kernel

def cell0363 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (9899 / 6400 : ℚ), (4039 / 2560 : ℚ), (.chain [(1, 29)]), (.chain [(1, 29)]), (.chain [(1, 29)]), (.chain [(1, 29), (1, 30)]), (.chain [(1, 29), (1, 30), (1, 31)]), (.chain [(1, 29), (1, 30)]), .two⟩
theorem cell0363_ok : cell0363.check T = true := by decide +kernel

def cell0364 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (4039 / 2560 : ℚ), (40787 / 25600 : ℚ), (.chain [(1, 30)]), (.chain [(1, 30)]), (.chain [(1, 30)]), (.chain [(1, 30)]), (.chain [(1, 30), (1, 31)]), (.chain [(1, 30)]), .one⟩
theorem cell0364_ok : cell0364.check T = true := by decide +kernel

def cell0365 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (40787 / 25600 : ℚ), (1287 / 800 : ℚ), (.chain [(1, 30)]), (.chain [(1, 30)]), (.chain [(1, 30)]), (.chain [(1, 30)]), (.chain [(1, 30), (1, 31)]), (.chain [(1, 30), (1, 31)]), .three⟩
theorem cell0365_ok : cell0365.check T = true := by decide +kernel

def cell0366 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (1287 / 800 : ℚ), (20989 / 12800 : ℚ), (.chain [(1, 30)]), (.chain [(1, 30)]), (.chain [(1, 30)]), (.chain [(1, 30), (1, 31)]), (.chain [(1, 30), (1, 31), (2, 0)]), (.chain [(1, 30), (1, 31)]), .two⟩
theorem cell0366_ok : cell0366.check T = true := by decide +kernel

def cell0367 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (1287 / 800 : ℚ), (20989 / 12800 : ℚ), (.chain [(1, 30)]), (.chain [(1, 31)]), (.chain [(1, 31)]), (.chain [(1, 30), (1, 31)]), (.chain [(1, 31), (2, 0)]), (.chain [(1, 31), (2, 0)]), .three⟩
theorem cell0367_ok : cell0367.check T = true := by decide +kernel

def cell0368 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (20989 / 12800 : ℚ), (10693 / 6400 : ℚ), (.chain [(1, 31)]), (.chain [(1, 31)]), (.chain [(1, 31)]), (.chain [(1, 31), (2, 0)]), (.chain [(1, 31), (2, 0)]), (.chain [(1, 31), (2, 0)]), .three⟩
theorem cell0368_ok : cell0368.check T = true := by decide +kernel

def cell0369 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (20989 / 12800 : ℚ), (10693 / 6400 : ℚ), (.chain [(1, 31)]), (.chain [(2, 0)]), (.chain [(1, 31)]), (.chain [(1, 31), (2, 0)]), (.chain [(2, 0), (2, 1)]), (.chain [(1, 31), (2, 0)]), .two⟩
theorem cell0369_ok : cell0369.check T = true := by decide +kernel

def cell0370 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (10693 / 6400 : ℚ), (21783 / 12800 : ℚ), (.chain [(2, 0)]), (.chain [(2, 0)]), (.chain [(2, 0)]), (.chain [(2, 0), (2, 1)]), (.chain [(2, 0), (2, 1)]), (.chain [(2, 0), (2, 1)]), .three⟩
theorem cell0370_ok : cell0370.check T = true := by decide +kernel

def cell0371 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (10693 / 6400 : ℚ), (21783 / 12800 : ℚ), (.chain [(2, 0)]), (.chain [(2, 0)]), (.chain [(2, 0)]), (.chain [(2, 0), (2, 1)]), (.chain [(2, 0), (2, 1), (2, 2)]), (.chain [(2, 0), (2, 1)]), .two⟩
theorem cell0371_ok : cell0371.check T = true := by decide +kernel

def cell0372 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (21783 / 12800 : ℚ), (1109 / 640 : ℚ), (.chain [(2, 1)]), (.chain [(2, 1)]), (.chain [(2, 1)]), (.chain [(2, 1)]), (.chain [(2, 1), (2, 2)]), (.chain [(2, 1), (2, 2)]), .two⟩
theorem cell0372_ok : cell0372.check T = true := by decide +kernel

def cell0373 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (21783 / 12800 : ℚ), (1109 / 640 : ℚ), (.chain [(2, 1)]), (.chain [(2, 1)]), (.chain [(2, 1)]), (.chain [(2, 1)]), (.chain [(2, 1), (2, 2)]), (.chain [(2, 1), (2, 2)]), .three⟩
theorem cell0373_ok : cell0373.check T = true := by decide +kernel

def cell0374 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (1109 / 640 : ℚ), (22577 / 12800 : ℚ), (.chain [(2, 1)]), (.chain [(2, 1)]), (.chain [(2, 1)]), (.chain [(2, 1), (2, 2)]), (.chain [(2, 1), (2, 2), (2, 3)]), (.chain [(2, 1), (2, 2)]), .two⟩
theorem cell0374_ok : cell0374.check T = true := by decide +kernel

def cell0375 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (1109 / 640 : ℚ), (22577 / 12800 : ℚ), (.chain [(2, 1)]), (.chain [(2, 2)]), (.chain [(2, 2)]), (.chain [(2, 1), (2, 2)]), (.chain [(2, 2), (2, 3)]), (.chain [(2, 2), (2, 3)]), .three⟩
theorem cell0375_ok : cell0375.check T = true := by decide +kernel

def cell0376 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (22577 / 12800 : ℚ), (45551 / 25600 : ℚ), (.chain [(2, 2)]), (.chain [(2, 2)]), (.chain [(2, 2)]), (.chain [(2, 2), (2, 3)]), (.chain [(2, 2), (2, 3), (2, 4)]), (.chain [(2, 2), (2, 3)]), .two⟩
theorem cell0376_ok : cell0376.check T = true := by decide +kernel

def cell0377 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (45551 / 25600 : ℚ), (11487 / 6400 : ℚ), (.chain [(2, 3)]), (.chain [(2, 3)]), (.chain [(2, 3)]), (.chain [(2, 3)]), (.chain [(2, 3), (2, 4)]), (.chain [(2, 3)]), .two⟩
theorem cell0377_ok : cell0377.check T = true := by decide +kernel

def cell0378 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (11487 / 6400 : ℚ), (23371 / 12800 : ℚ), (.chain [(2, 3)]), (.chain [(2, 3)]), (.chain [(2, 3)]), (.chain [(2, 3), (2, 4)]), (.chain [(2, 3), (2, 4)]), (.chain [(2, 3), (2, 4)]), .three⟩
theorem cell0378_ok : cell0378.check T = true := by decide +kernel

def cell0379 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (11487 / 6400 : ℚ), (23371 / 12800 : ℚ), (.chain [(2, 3)]), (.chain [(2, 3)]), (.chain [(2, 3)]), (.chain [(2, 3), (2, 4)]), (.chain [(2, 3), (2, 4), (2, 5)]), (.chain [(2, 3), (2, 4)]), .two⟩
theorem cell0379_ok : cell0379.check T = true := by decide +kernel

def cell0380 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (23371 / 12800 : ℚ), (2971 / 1600 : ℚ), (.chain [(2, 4)]), (.chain [(2, 4)]), (.chain [(2, 4)]), (.chain [(2, 4), (2, 5)]), (.chain [(2, 4), (2, 5)]), (.chain [(2, 4), (2, 5)]), .three⟩
theorem cell0380_ok : cell0380.check T = true := by decide +kernel

def cell0381 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (23371 / 12800 : ℚ), (2971 / 1600 : ℚ), (.chain [(2, 4)]), (.chain [(2, 4)]), (.chain [(2, 4)]), (.chain [(2, 4), (2, 5)]), (.chain [(2, 4), (2, 5), (2, 6)]), (.chain [(2, 4), (2, 5)]), .three⟩
theorem cell0381_ok : cell0381.check T = true := by decide +kernel

def cell0382 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (2971 / 1600 : ℚ), (4833 / 2560 : ℚ), (.chain [(2, 5)]), (.chain [(2, 5)]), (.chain [(2, 5)]), (.chain [(2, 5)]), (.chain [(2, 5), (2, 6)]), (.chain [(2, 5), (2, 6)]), .two⟩
theorem cell0382_ok : cell0382.check T = true := by decide +kernel

def cell0383 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (2971 / 1600 : ℚ), (4833 / 2560 : ℚ), (.chain [(2, 5)]), (.chain [(2, 5)]), (.chain [(2, 5)]), (.chain [(2, 5)]), (.chain [(2, 5), (2, 6)]), (.chain [(2, 5), (2, 6)]), .three⟩
theorem cell0383_ok : cell0383.check T = true := by decide +kernel

def cell0384 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (4833 / 2560 : ℚ), (12281 / 6400 : ℚ), (.chain [(2, 5)]), (.chain [(2, 5)]), (.chain [(2, 5)]), (.chain [(2, 5), (2, 6)]), (.chain [(2, 5), (2, 6), (2, 7)]), (.chain [(2, 5), (2, 6), (2, 7)]), .one⟩
theorem cell0384_ok : cell0384.check T = true := by decide +kernel

def cell0385 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (12281 / 6400 : ℚ), (24959 / 12800 : ℚ), (.chain [(2, 6)]), (.chain [(2, 6)]), (.chain [(2, 6)]), (.chain [(2, 6), (2, 7)]), (.chain [(2, 6), (2, 7), (2, 8)]), (.chain [(2, 6), (2, 7)]), .one⟩
theorem cell0385_ok : cell0385.check T = true := by decide +kernel

def cell0386 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (24959 / 12800 : ℚ), (6339 / 3200 : ℚ), (.chain [(2, 7)]), (.chain [(2, 7)]), (.chain [(2, 7)]), (.chain [(2, 7), (2, 8)]), (.chain [(2, 7), (2, 8), (2, 9)]), (.chain [(2, 7), (2, 8)]), .one⟩
theorem cell0386_ok : cell0386.check T = true := by decide +kernel

def cell0387 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (6339 / 3200 : ℚ), (25753 / 12800 : ℚ), (.chain [(2, 8)]), (.chain [(2, 8)]), (.chain [(2, 8)]), (.chain [(2, 8)]), (.chain [(2, 8), (2, 9)]), (.chain [(2, 8), (2, 9)]), .one⟩
theorem cell0387_ok : cell0387.check T = true := by decide +kernel

def cell0388 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (25753 / 12800 : ℚ), (523 / 256 : ℚ), (.chain [(2, 8)]), (.chain [(2, 8)]), (.chain [(2, 8)]), (.chain [(2, 8), (2, 9)]), (.chain [(2, 8), (2, 9), (2, 10)]), (.chain [(2, 8), (2, 9), (2, 10)]), .one⟩
theorem cell0388_ok : cell0388.check T = true := by decide +kernel

def cell0389 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (523 / 256 : ℚ), (26547 / 12800 : ℚ), (.chain [(2, 9)]), (.chain [(2, 9)]), (.chain [(2, 9)]), (.chain [(2, 9), (2, 10)]), (.chain [(2, 9), (2, 10), (2, 11)]), (.chain [(2, 9), (2, 10)]), .one⟩
theorem cell0389_ok : cell0389.check T = true := by decide +kernel

def cell0390 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (26547 / 12800 : ℚ), (421 / 200 : ℚ), (.chain [(2, 10)]), (.chain [(2, 10)]), (.chain [(2, 10)]), (.chain [(2, 10), (2, 11)]), (.chain [(2, 10), (2, 11), (2, 12)]), (.chain [(2, 10), (2, 11)]), .one⟩
theorem cell0390_ok : cell0390.check T = true := by decide +kernel

def cell0391 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (421 / 200 : ℚ), (27341 / 12800 : ℚ), (.chain [(2, 11)]), (.chain [(2, 11)]), (.chain [(2, 11)]), (.chain [(2, 11), (2, 12)]), (.chain [(2, 11), (2, 12), (2, 13)]), (.chain [(2, 11), (2, 12)]), .one⟩
theorem cell0391_ok : cell0391.check T = true := by decide +kernel

def cell0392 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (27341 / 12800 : ℚ), (13869 / 6400 : ℚ), (.chain [(2, 12)]), (.chain [(2, 12)]), (.chain [(2, 12)]), (.chain [(2, 12)]), (.chain [(2, 12), (2, 13)]), (.chain [(2, 12), (2, 13)]), .one⟩
theorem cell0392_ok : cell0392.check T = true := by decide +kernel

def cell0393 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (13869 / 6400 : ℚ), (5627 / 2560 : ℚ), (.chain [(2, 12)]), (.chain [(2, 12)]), (.chain [(2, 12)]), (.chain [(2, 12), (2, 13)]), (.chain [(2, 12), (2, 13), (2, 14)]), (.chain [(2, 12), (2, 13), (2, 14)]), .one⟩
theorem cell0393_ok : cell0393.check T = true := by decide +kernel

def cell0394 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (5627 / 2560 : ℚ), (7133 / 3200 : ℚ), (.chain [(2, 13)]), (.chain [(2, 13)]), (.chain [(2, 13)]), (.chain [(2, 13), (2, 14)]), (.chain [(2, 13), (2, 14), (2, 15)]), (.chain [(2, 13), (2, 14)]), .one⟩
theorem cell0394_ok : cell0394.check T = true := by decide +kernel

def cell0395 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (7133 / 3200 : ℚ), (28929 / 12800 : ℚ), (.chain [(2, 14)]), (.chain [(2, 14)]), (.chain [(2, 14)]), (.chain [(2, 14), (2, 15)]), (.chain [(2, 14), (2, 15), (2, 16)]), (.chain [(2, 14), (2, 15)]), .one⟩
theorem cell0395_ok : cell0395.check T = true := by decide +kernel

def cell0396 : CellW := ⟨(0 : ℚ), (1 / 50 : ℚ), (28929 / 12800 : ℚ), (14663 / 6400 : ℚ), (.chain [(2, 15)]), (.chain [(2, 15)]), (.chain [(2, 15)]), (.chain [(2, 15)]), (.chain [(2, 15), (2, 16)]), (.chain [(2, 15), (2, 16)]), .one⟩
theorem cell0396_ok : cell0396.check T = true := by decide +kernel

def cell0397 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (14663 / 6400 : ℚ), (753 / 320 : ℚ), (.chain [(2, 15)]), (.chain [(2, 15)]), (.chain [(2, 15)]), (.chain [(2, 15), (2, 16), (2, 17)]), (.chain [(2, 15), (2, 16), (2, 17)]), (.chain [(2, 15), (2, 16), (2, 17)]), .one⟩
theorem cell0397_ok : cell0397.check T = true := by decide +kernel

def cell0398 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (14663 / 6400 : ℚ), (753 / 320 : ℚ), (.chain [(2, 15)]), (.chain [(2, 16)]), (.chain [(2, 16)]), (.chain [(2, 15), (2, 16), (2, 17)]), (.chain [(2, 16), (2, 17), (2, 18)]), (.chain [(2, 16), (2, 17)]), .one⟩
theorem cell0398_ok : cell0398.check T = true := by decide +kernel

def cell0399 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (753 / 320 : ℚ), (15457 / 6400 : ℚ), (.chain [(2, 17)]), (.chain [(2, 17)]), (.chain [(2, 17)]), (.chain [(2, 17), (2, 18), (2, 19)]), (.chain [(2, 17), (2, 18), (2, 19)]), (.chain [(2, 17), (2, 18), (2, 19)]), .one⟩
theorem cell0399_ok : cell0399.check T = true := by decide +kernel

def cells09 : List CellW := [cell0360, cell0361, cell0362, cell0363, cell0364, cell0365, cell0366, cell0367, cell0368, cell0369, cell0370, cell0371, cell0372, cell0373, cell0374, cell0375, cell0376, cell0377, cell0378, cell0379, cell0380, cell0381, cell0382, cell0383, cell0384, cell0385, cell0386, cell0387, cell0388, cell0389, cell0390, cell0391, cell0392, cell0393, cell0394, cell0395, cell0396, cell0397, cell0398, cell0399]

theorem cells09_valid : ∀ w ∈ cells09, w.check T = true :=
  (forall_mem_cons_of cell0360_ok (forall_mem_cons_of cell0361_ok (forall_mem_cons_of cell0362_ok (forall_mem_cons_of cell0363_ok (forall_mem_cons_of cell0364_ok (forall_mem_cons_of cell0365_ok (forall_mem_cons_of cell0366_ok (forall_mem_cons_of cell0367_ok (forall_mem_cons_of cell0368_ok (forall_mem_cons_of cell0369_ok (forall_mem_cons_of cell0370_ok (forall_mem_cons_of cell0371_ok (forall_mem_cons_of cell0372_ok (forall_mem_cons_of cell0373_ok (forall_mem_cons_of cell0374_ok (forall_mem_cons_of cell0375_ok (forall_mem_cons_of cell0376_ok (forall_mem_cons_of cell0377_ok (forall_mem_cons_of cell0378_ok (forall_mem_cons_of cell0379_ok (forall_mem_cons_of cell0380_ok (forall_mem_cons_of cell0381_ok (forall_mem_cons_of cell0382_ok (forall_mem_cons_of cell0383_ok (forall_mem_cons_of cell0384_ok (forall_mem_cons_of cell0385_ok (forall_mem_cons_of cell0386_ok (forall_mem_cons_of cell0387_ok (forall_mem_cons_of cell0388_ok (forall_mem_cons_of cell0389_ok (forall_mem_cons_of cell0390_ok (forall_mem_cons_of cell0391_ok (forall_mem_cons_of cell0392_ok (forall_mem_cons_of cell0393_ok (forall_mem_cons_of cell0394_ok (forall_mem_cons_of cell0395_ok (forall_mem_cons_of cell0396_ok (forall_mem_cons_of cell0397_ok (forall_mem_cons_of cell0398_ok (forall_mem_cons_of cell0399_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


