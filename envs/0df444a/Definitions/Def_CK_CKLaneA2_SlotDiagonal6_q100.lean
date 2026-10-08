-- Prove2me | Definitions.Def_CK_CKLaneA2_SlotDiagonal6_q100
-- name    : CK_CKLaneA2_SlotDiagonal6_q100
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T04:09:47.16809+00:00
-- url     : https://prove2.me/theorems/67613fb7-1e21-4d09-8014-d8cceba800e7
-- title:
--   Courtade–Kumar proof module `CKLaneA2.SlotDiagonal6 (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA2.SlotDiagonal6 (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA2.SlotDiagonal6 (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA2.SlotDiagonal6 (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA2/SlotDiagonal6 (piece 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_CorrectionComplementCharts
import Definitions.Def_CK_CKLaneA2_SlotDiagonal6_q02


namespace CKLaneA2.Slots
open GeneralCK GeneralCK.Correction GeneralCK.Correction.Complement CKLaneA.Cell
/-- strict owner on `[37/100, 19/50] × (0, 3/10]` -/
theorem diagonal6_actual : ∀ ⦃u rho : ℝ⦄, u ∈ Set.Icc (37 / 100 : ℝ) (19 / 50) →
    rho ∈ Set.Ioc (0 : ℝ) (3 / 10) → ActualRatioMinorsPositive u rho := by
  intro u rho hu hr
  exact actual_of_tree Diag6.slotTree_ok (by push_cast; linarith [hu.1])
    (by push_cast; linarith [hu.2]) (by push_cast; linarith [hr.1]) (by push_cast; linarith [hr.2])
    (by linarith [hu.1]) (by linarith [hu.2]) hr.1 (by linarith [hr.2])

end CKLaneA2.Slots


