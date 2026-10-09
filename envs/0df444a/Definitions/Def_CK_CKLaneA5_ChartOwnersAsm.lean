-- Prove2me | Definitions.Def_CK_CKLaneA5_ChartOwnersAsm
-- name    : CK_CKLaneA5_ChartOwnersAsm
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T11:19:45.079263+00:00
-- url     : https://prove2.me/theorems/ed1de310-501f-4b09-a761-e785913aafa1
-- title:
--   Courtade–Kumar proof module `CKLaneA5.ChartOwnersAsm` (transplant, CKFast certificate inputs)
-- statement:
--   Transplant of the Lean module `CKLaneA5.ChartOwnersAsm` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), with one substantive change: the certificate inputs it consumes are replaced by the platform theorems `GeneralCK.CKFast.hC1_actual`, `GeneralCK.CKFast.hC2_actual` (correction bands R-B1, R-B2) and `GeneralCK.CKFast.directC3_actual` (chart owner `directC3`). These are proved on this platform by the computing interval checker `GeneralCK.CKFast.tree_sound` instead of the source's stored certificates, and they state exactly the source's `ActualRatioFamilyOn` inputs in unfolded form. Everything else is the original source, with project imports redirected to their transplanted bundles `Definitions.Def_CK_*`.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA5.ChartOwnersAsm` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA5.ChartOwnersAsm (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA5/ChartOwnersAsm.lean)

import Definitions.Def_CK_GeneralCK_CorrectionComplementCharts
import Definitions.Def_CK_CKLaneA1_BSFinal
import Definitions.Def_CK_CKLaneA1_FEFinal
import Definitions.Def_CK_CKLaneA5_SlotDiagonal1
import Definitions.Def_CK_CKLaneA4_D2Slot
import Definitions.Def_CK_CKLaneA2_SlotDiagonal3
import Definitions.Def_CK_CKLaneA2_SlotDiagonal4
import Definitions.Def_CK_CKLaneA2_SlotDiagonal5
import Definitions.Def_CK_CKLaneA2_SlotDiagonal6
import Definitions.Def_CK_CKLaneA3W_Owners
import Theorems.Thm_GeneralCK_CKFast_directC3_actual
import Definitions.Def_CK_CKLaneA3V_Owners

/-!
# Lane A5: the `ChartOwners` inhabitant, every field taken from the lane that closed it

| field | owner declaration | lane |
|---|---|---|
| bothSmall | `CKLaneA1.bothSmall_field` | A1 |
| fixedEdge | `CKLaneA1.fixedEdge_field` | A1 |
| diagonal1 | `CKLaneA5.Slots.diagonal1_signs` | A5 |
| diagonal2 | `CKLaneA4.D2.diagonal2_signs` | A4 |
| diagonal3..6 | `CKLaneA2.Slots.diagonal{3,4,5,6}_signs` | A2 |
| diagonal7..9, corner0..5, directC5, directC6 | `CKLaneA3W.*` (u ≥ 9/25 high-u owner) | A3 |
| directC3 | `GeneralCK.CKFast.directC3_actual` (computing checker; replaces the A3X Taylor-model owner) | CKFast |
| directC4 | `CKLaneA3V.directC4` | A3 |

All modules compiled over the F-C provider (`~/gck_lanes/F-C/work/root`); the single `CKLaneA` checker root is
`A2/checkerFC` (byte-identical to `A4/deproot`).
-/

namespace CKLaneA5.Assembly

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Complement

/-- The complete chart-owner record. -/
theorem chartOwners : ChartOwners where
  bothSmall := CKLaneA1.bothSmall_field
  fixedEdge := CKLaneA1.fixedEdge_field
  diagonal1 := CKLaneA5.Slots.diagonal1_signs
  diagonal2 := CKLaneA4.D2.diagonal2_signs
  diagonal3 := CKLaneA2.Slots.diagonal3_signs
  diagonal4 := CKLaneA2.Slots.diagonal4_signs
  diagonal5 := CKLaneA2.Slots.diagonal5_signs
  diagonal6 := CKLaneA2.Slots.diagonal6_signs
  diagonal7 := CKLaneA3W.diagonal7
  diagonal8 := CKLaneA3W.diagonal8
  diagonal9 := CKLaneA3W.diagonal9
  directC3 := fun _ _ _ _ _ hr1 hu hr =>
    ratioSigns_of_positive (GeneralCK.CKFast.directC3_actual hu hr hr1)
  directC4 := CKLaneA3V.directC4
  directC5 := CKLaneA3W.directC5
  directC6 := CKLaneA3W.directC6
  corner0 := CKLaneA3W.corner0
  corner1 := CKLaneA3W.corner1
  corner2 := CKLaneA3W.corner2
  corner3 := CKLaneA3W.corner3
  corner4 := CKLaneA3W.corner4
  corner5 := CKLaneA3W.corner5

end CKLaneA5.Assembly


