-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Data_Cells14
-- name    : CK_CKLaneC_SAxis_Data_Cells14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T06:40:11.796839+00:00
-- url     : https://prove2.me/theorems/6bfe444e-08a4-4e66-a6e3-be165a860c6e
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Data.Cells14` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Data.Cells14` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Data.Cells14` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Data.Cells14 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Data/Cells14.lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Table
import Definitions.Def_CK_CKLaneC_SAxis_Cell

-- ===== source module CKLaneC.SAxis.Data.Cells14 =====
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell

namespace CKLaneC.SAxis.Data

/-! Cell batch 14 (cells 560..599). -/

def cell0560 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (84509 / 12800 : ℚ), (42453 / 6400 : ℚ), (.chain [(5, 27)]), (.chain [(5, 28)]), (.chain [(5, 27)]), (.chain [(5, 27), (5, 28)]), (.chain [(5, 28), (5, 29)]), (.chain [(5, 27), (5, 28)]), .one⟩
theorem cell0560_ok : cell0560.check T = true := by decide +kernel

def cell0561 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (84509 / 12800 : ℚ), (42453 / 6400 : ℚ), (.chain [(5, 27)]), (.chain [(5, 28)]), (.chain [(5, 28)]), (.chain [(5, 27), (5, 28)]), (.chain [(5, 28), (5, 29)]), (.chain [(5, 28)]), .one⟩
theorem cell0561_ok : cell0561.check T = true := by decide +kernel

def cell0562 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (42453 / 6400 : ℚ), (85303 / 12800 : ℚ), (.chain [(5, 28)]), (.chain [(5, 28)]), (.chain [(5, 28)]), (.chain [(5, 28), (5, 29)]), (.chain [(5, 28), (5, 29)]), (.chain [(5, 28), (5, 29)]), .one⟩
theorem cell0562_ok : cell0562.check T = true := by decide +kernel

def cell0563 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (42453 / 6400 : ℚ), (85303 / 12800 : ℚ), (.chain [(5, 28)]), (.chain [(5, 28)]), (.chain [(5, 28)]), (.chain [(5, 28), (5, 29)]), (.chain [(5, 28), (5, 29)]), (.chain [(5, 28), (5, 29)]), .one⟩
theorem cell0563_ok : cell0563.check T = true := by decide +kernel

def cell0564 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (42453 / 6400 : ℚ), (170209 / 25600 : ℚ), (.chain [(5, 28)]), (.chain [(5, 28)]), (.chain [(5, 28)]), (.chain [(5, 28)]), (.chain [(5, 28), (5, 29)]), (.chain [(5, 28), (5, 29)]), .one⟩
theorem cell0564_ok : cell0564.check T = true := by decide +kernel

def cell0565 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (170209 / 25600 : ℚ), (85303 / 12800 : ℚ), (.chain [(5, 28)]), (.chain [(5, 29)]), (.chain [(5, 29)]), (.chain [(5, 28), (5, 29)]), (.chain [(5, 29), (5, 30)]), (.chain [(5, 29)]), .one⟩
theorem cell0565_ok : cell0565.check T = true := by decide +kernel

def cell0566 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (85303 / 12800 : ℚ), (171003 / 25600 : ℚ), (.chain [(5, 29)]), (.chain [(5, 29)]), (.chain [(5, 29)]), (.chain [(5, 29)]), (.chain [(5, 29), (5, 30)]), (.chain [(5, 29)]), .one⟩
theorem cell0566_ok : cell0566.check T = true := by decide +kernel

def cell0567 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (171003 / 25600 : ℚ), (857 / 128 : ℚ), (.chain [(5, 29)]), (.chain [(5, 29)]), (.chain [(5, 29)]), (.chain [(5, 29), (5, 30)]), (.chain [(5, 29), (5, 30)]), (.chain [(5, 29), (5, 30)]), .one⟩
theorem cell0567_ok : cell0567.check T = true := by decide +kernel

def cell0568 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (85303 / 12800 : ℚ), (171003 / 25600 : ℚ), (.chain [(5, 29)]), (.chain [(5, 29)]), (.chain [(5, 29)]), (.chain [(5, 29)]), (.chain [(5, 29), (5, 30)]), (.chain [(5, 29), (5, 30)]), .one⟩
theorem cell0568_ok : cell0568.check T = true := by decide +kernel

def cell0569 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (171003 / 25600 : ℚ), (857 / 128 : ℚ), (.chain [(5, 29)]), (.chain [(5, 30)]), (.chain [(5, 29)]), (.chain [(5, 29), (5, 30)]), (.chain [(5, 30), (5, 31)]), (.chain [(5, 29), (5, 30)]), .one⟩
theorem cell0569_ok : cell0569.check T = true := by decide +kernel

def cell0570 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (857 / 128 : ℚ), (171797 / 25600 : ℚ), (.chain [(5, 30)]), (.chain [(5, 30)]), (.chain [(5, 30)]), (.chain [(5, 30)]), (.chain [(5, 30)]), (.chain [(5, 30)]), .one⟩
theorem cell0570_ok : cell0570.check T = true := by decide +kernel

def cell0571 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (171797 / 25600 : ℚ), (86097 / 12800 : ℚ), (.chain [(5, 30)]), (.chain [(5, 30)]), (.chain [(5, 30)]), (.chain [(5, 30)]), (.chain [(5, 30), (5, 31)]), (.chain [(5, 30), (5, 31)]), .one⟩
theorem cell0571_ok : cell0571.check T = true := by decide +kernel

def cell0572 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (857 / 128 : ℚ), (171797 / 25600 : ℚ), (.chain [(5, 30)]), (.chain [(5, 30)]), (.chain [(5, 30)]), (.chain [(5, 30)]), (.chain [(5, 30), (5, 31)]), (.chain [(5, 30)]), .three⟩
theorem cell0572_ok : cell0572.check T = true := by decide +kernel

def cell0573 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (171797 / 25600 : ℚ), (86097 / 12800 : ℚ), (.chain [(5, 30)]), (.chain [(5, 30)]), (.chain [(5, 30)]), (.chain [(5, 30)]), (.chain [(5, 30), (5, 31)]), (.chain [(5, 30), (5, 31)]), .one⟩
theorem cell0573_ok : cell0573.check T = true := by decide +kernel

def cell0574 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (86097 / 12800 : ℚ), (172591 / 25600 : ℚ), (.chain [(5, 30)]), (.chain [(5, 30)]), (.chain [(5, 30)]), (.chain [(5, 30), (5, 31)]), (.chain [(5, 30), (5, 31)]), (.chain [(5, 30), (5, 31)]), .one⟩
theorem cell0574_ok : cell0574.check T = true := by decide +kernel

def cell0575 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (172591 / 25600 : ℚ), (43247 / 6400 : ℚ), (.chain [(5, 31)]), (.chain [(5, 31)]), (.chain [(5, 31)]), (.chain [(5, 31)]), (.chain [(5, 31), (6, 0)]), (.chain [(5, 31)]), .one⟩
theorem cell0575_ok : cell0575.check T = true := by decide +kernel

def cell0576 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (86097 / 12800 : ℚ), (172591 / 25600 : ℚ), (.chain [(5, 30)]), (.chain [(5, 31)]), (.chain [(5, 31)]), (.chain [(5, 30), (5, 31)]), (.chain [(5, 31), (6, 0)]), (.chain [(5, 31)]), .one⟩
theorem cell0576_ok : cell0576.check T = true := by decide +kernel

def cell0577 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (172591 / 25600 : ℚ), (43247 / 6400 : ℚ), (.chain [(5, 31)]), (.chain [(5, 31)]), (.chain [(5, 31)]), (.chain [(5, 31)]), (.chain [(5, 31), (6, 0)]), (.chain [(5, 31), (6, 0)]), .one⟩
theorem cell0577_ok : cell0577.check T = true := by decide +kernel

def cell0578 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (43247 / 6400 : ℚ), (86891 / 12800 : ℚ), (.chain [(5, 31)]), (.chain [(5, 31)]), (.chain [(5, 31)]), (.chain [(5, 31), (6, 0)]), (.chain [(5, 31), (6, 0)]), (.chain [(5, 31), (6, 0)]), .one⟩
theorem cell0578_ok : cell0578.check T = true := by decide +kernel

def cell0579 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (43247 / 6400 : ℚ), (86891 / 12800 : ℚ), (.chain [(5, 31)]), (.chain [(5, 31)]), (.chain [(5, 31)]), (.chain [(5, 31), (6, 0)]), (.chain [(5, 31), (6, 0)]), (.chain [(5, 31), (6, 0)]), .one⟩
theorem cell0579_ok : cell0579.check T = true := by decide +kernel

def cell0580 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (43247 / 6400 : ℚ), (86891 / 12800 : ℚ), (.chain [(5, 31)]), (.chain [(6, 0)]), (.chain [(5, 31)]), (.chain [(5, 31), (6, 0)]), (.chain [(6, 0), (6, 1)]), (.chain [(5, 31), (6, 0)]), .one⟩
theorem cell0580_ok : cell0580.check T = true := by decide +kernel

def cell0581 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (43247 / 6400 : ℚ), (86891 / 12800 : ℚ), (.chain [(5, 31)]), (.chain [(6, 0)]), (.chain [(5, 31)]), (.chain [(5, 31), (6, 0)]), (.chain [(6, 0), (6, 1)]), (.chain [(5, 31), (6, 0)]), .one⟩
theorem cell0581_ok : cell0581.check T = true := by decide +kernel

def cell0582 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (86891 / 12800 : ℚ), (174179 / 25600 : ℚ), (.chain [(6, 0)]), (.chain [(6, 0)]), (.chain [(6, 0)]), (.chain [(6, 0)]), (.chain [(6, 0), (6, 1)]), (.chain [(6, 0)]), .one⟩
theorem cell0582_ok : cell0582.check T = true := by decide +kernel

def cell0583 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (174179 / 25600 : ℚ), (10911 / 1600 : ℚ), (.chain [(6, 0)]), (.chain [(6, 0)]), (.chain [(6, 0)]), (.chain [(6, 0), (6, 1)]), (.chain [(6, 0), (6, 1)]), (.chain [(6, 0), (6, 1)]), .one⟩
theorem cell0583_ok : cell0583.check T = true := by decide +kernel

def cell0584 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (86891 / 12800 : ℚ), (174179 / 25600 : ℚ), (.chain [(6, 0)]), (.chain [(6, 0)]), (.chain [(6, 0)]), (.chain [(6, 0)]), (.chain [(6, 0), (6, 1)]), (.chain [(6, 0), (6, 1)]), .one⟩
theorem cell0584_ok : cell0584.check T = true := by decide +kernel

def cell0585 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (174179 / 25600 : ℚ), (10911 / 1600 : ℚ), (.chain [(6, 0)]), (.chain [(6, 1)]), (.chain [(6, 0)]), (.chain [(6, 0), (6, 1)]), (.chain [(6, 1), (6, 2)]), (.chain [(6, 0), (6, 1)]), .one⟩
theorem cell0585_ok : cell0585.check T = true := by decide +kernel

def cell0586 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (10911 / 1600 : ℚ), (174973 / 25600 : ℚ), (.chain [(6, 1)]), (.chain [(6, 1)]), (.chain [(6, 1)]), (.chain [(6, 1)]), (.chain [(6, 1)]), (.chain [(6, 1)]), .one⟩
theorem cell0586_ok : cell0586.check T = true := by decide +kernel

def cell0587 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (174973 / 25600 : ℚ), (17537 / 2560 : ℚ), (.chain [(6, 1)]), (.chain [(6, 1)]), (.chain [(6, 1)]), (.chain [(6, 1)]), (.chain [(6, 1), (6, 2)]), (.chain [(6, 1), (6, 2)]), .three⟩
theorem cell0587_ok : cell0587.check T = true := by decide +kernel

def cell0588 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (10911 / 1600 : ℚ), (174973 / 25600 : ℚ), (.chain [(6, 1)]), (.chain [(6, 1)]), (.chain [(6, 1)]), (.chain [(6, 1)]), (.chain [(6, 1), (6, 2)]), (.chain [(6, 1)]), .one⟩
theorem cell0588_ok : cell0588.check T = true := by decide +kernel

def cell0589 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (174973 / 25600 : ℚ), (17537 / 2560 : ℚ), (.chain [(6, 1)]), (.chain [(6, 1)]), (.chain [(6, 1)]), (.chain [(6, 1)]), (.chain [(6, 1), (6, 2)]), (.chain [(6, 1), (6, 2)]), .one⟩
theorem cell0589_ok : cell0589.check T = true := by decide +kernel

def cell0590 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (17537 / 2560 : ℚ), (175767 / 25600 : ℚ), (.chain [(6, 1)]), (.chain [(6, 1)]), (.chain [(6, 1)]), (.chain [(6, 1), (6, 2)]), (.chain [(6, 1), (6, 2)]), (.chain [(6, 1), (6, 2)]), .one⟩
theorem cell0590_ok : cell0590.check T = true := by decide +kernel

def cell0591 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (175767 / 25600 : ℚ), (44041 / 6400 : ℚ), (.chain [(6, 2)]), (.chain [(6, 2)]), (.chain [(6, 2)]), (.chain [(6, 2)]), (.chain [(6, 2), (6, 3)]), (.chain [(6, 2)]), .one⟩
theorem cell0591_ok : cell0591.check T = true := by decide +kernel

def cell0592 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (17537 / 2560 : ℚ), (175767 / 25600 : ℚ), (.chain [(6, 1)]), (.chain [(6, 2)]), (.chain [(6, 2)]), (.chain [(6, 1), (6, 2)]), (.chain [(6, 2), (6, 3)]), (.chain [(6, 2)]), .one⟩
theorem cell0592_ok : cell0592.check T = true := by decide +kernel

def cell0593 : CellW := ⟨(1 / 100 : ℚ), (1 / 50 : ℚ), (175767 / 25600 : ℚ), (44041 / 6400 : ℚ), (.chain [(6, 2)]), (.chain [(6, 2)]), (.chain [(6, 2)]), (.chain [(6, 2)]), (.chain [(6, 2), (6, 3)]), (.chain [(6, 2), (6, 3)]), .one⟩
theorem cell0593_ok : cell0593.check T = true := by decide +kernel

def cell0594 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (44041 / 6400 : ℚ), (176561 / 25600 : ℚ), (.chain [(6, 2)]), (.chain [(6, 2)]), (.chain [(6, 2)]), (.chain [(6, 2), (6, 3)]), (.chain [(6, 2), (6, 3)]), (.chain [(6, 2), (6, 3)]), .one⟩
theorem cell0594_ok : cell0594.check T = true := by decide +kernel

def cell0595 : CellW := ⟨(0 : ℚ), (1 / 100 : ℚ), (176561 / 25600 : ℚ), (88479 / 12800 : ℚ), (.chain [(6, 3)]), (.chain [(6, 3)]), (.chain [(6, 3)]), (.chain [(6, 3)]), (.chain [(6, 3)]), (.chain [(6, 3)]), .one⟩
theorem cell0595_ok : cell0595.check T = true := by decide +kernel

def cell0596 : CellW := ⟨(1 / 100 : ℚ), (3 / 200 : ℚ), (44041 / 6400 : ℚ), (88479 / 12800 : ℚ), (.chain [(6, 2)]), (.chain [(6, 3)]), (.chain [(6, 2)]), (.chain [(6, 2), (6, 3)]), (.chain [(6, 3), (6, 4)]), (.chain [(6, 2), (6, 3)]), .one⟩
theorem cell0596_ok : cell0596.check T = true := by decide +kernel

def cell0597 : CellW := ⟨(3 / 200 : ℚ), (1 / 50 : ℚ), (44041 / 6400 : ℚ), (88479 / 12800 : ℚ), (.chain [(6, 2)]), (.chain [(6, 3)]), (.chain [(6, 3)]), (.chain [(6, 2), (6, 3)]), (.chain [(6, 3), (6, 4)]), (.chain [(6, 3)]), .one⟩
theorem cell0597_ok : cell0597.check T = true := by decide +kernel

def cell0598 : CellW := ⟨(0 : ℚ), (1 / 200 : ℚ), (88479 / 12800 : ℚ), (22219 / 3200 : ℚ), (.chain [(6, 3)]), (.chain [(6, 3)]), (.chain [(6, 3)]), (.chain [(6, 3), (6, 4)]), (.chain [(6, 3), (6, 4)]), (.chain [(6, 3), (6, 4)]), .one⟩
theorem cell0598_ok : cell0598.check T = true := by decide +kernel

def cell0599 : CellW := ⟨(1 / 200 : ℚ), (1 / 100 : ℚ), (88479 / 12800 : ℚ), (22219 / 3200 : ℚ), (.chain [(6, 3)]), (.chain [(6, 3)]), (.chain [(6, 3)]), (.chain [(6, 3), (6, 4)]), (.chain [(6, 3), (6, 4)]), (.chain [(6, 3), (6, 4)]), .one⟩
theorem cell0599_ok : cell0599.check T = true := by decide +kernel

def cells14 : List CellW := [cell0560, cell0561, cell0562, cell0563, cell0564, cell0565, cell0566, cell0567, cell0568, cell0569, cell0570, cell0571, cell0572, cell0573, cell0574, cell0575, cell0576, cell0577, cell0578, cell0579, cell0580, cell0581, cell0582, cell0583, cell0584, cell0585, cell0586, cell0587, cell0588, cell0589, cell0590, cell0591, cell0592, cell0593, cell0594, cell0595, cell0596, cell0597, cell0598, cell0599]

theorem cells14_valid : ∀ w ∈ cells14, w.check T = true :=
  (forall_mem_cons_of cell0560_ok (forall_mem_cons_of cell0561_ok (forall_mem_cons_of cell0562_ok (forall_mem_cons_of cell0563_ok (forall_mem_cons_of cell0564_ok (forall_mem_cons_of cell0565_ok (forall_mem_cons_of cell0566_ok (forall_mem_cons_of cell0567_ok (forall_mem_cons_of cell0568_ok (forall_mem_cons_of cell0569_ok (forall_mem_cons_of cell0570_ok (forall_mem_cons_of cell0571_ok (forall_mem_cons_of cell0572_ok (forall_mem_cons_of cell0573_ok (forall_mem_cons_of cell0574_ok (forall_mem_cons_of cell0575_ok (forall_mem_cons_of cell0576_ok (forall_mem_cons_of cell0577_ok (forall_mem_cons_of cell0578_ok (forall_mem_cons_of cell0579_ok (forall_mem_cons_of cell0580_ok (forall_mem_cons_of cell0581_ok (forall_mem_cons_of cell0582_ok (forall_mem_cons_of cell0583_ok (forall_mem_cons_of cell0584_ok (forall_mem_cons_of cell0585_ok (forall_mem_cons_of cell0586_ok (forall_mem_cons_of cell0587_ok (forall_mem_cons_of cell0588_ok (forall_mem_cons_of cell0589_ok (forall_mem_cons_of cell0590_ok (forall_mem_cons_of cell0591_ok (forall_mem_cons_of cell0592_ok (forall_mem_cons_of cell0593_ok (forall_mem_cons_of cell0594_ok (forall_mem_cons_of cell0595_ok (forall_mem_cons_of cell0596_ok (forall_mem_cons_of cell0597_ok (forall_mem_cons_of cell0598_ok (forall_mem_cons_of cell0599_ok forall_mem_nil_of))))))))))))))))))))))))))))))))))))))))

end CKLaneC.SAxis.Data

end


