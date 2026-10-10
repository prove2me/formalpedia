-- Prove2me | Definitions.Def_CK_CKLaneA5_Correction
-- name    : CK_CKLaneA5_Correction
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-10T10:04:37.361265+00:00
-- url     : https://prove2.me/theorems/395134ac-4cec-4877-bd2b-bb5295fc4fef
-- title:
--   Courtade–Kumar proof module `CKLaneA5.Correction` (transplant, CKFast certificate inputs)
-- statement:
--   Transplant of the Lean module `CKLaneA5.Correction` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), with one substantive change: the certificate inputs it consumes are replaced by the platform theorems `GeneralCK.CKFast.hC1_actual`, `GeneralCK.CKFast.hC2_actual` (correction bands R-B1, R-B2) and `GeneralCK.CKFast.directC3_actual` (chart owner `directC3`). These are proved on this platform by the computing interval checker `GeneralCK.CKFast.tree_sound` instead of the source's stored certificates, and they state exactly the source's `ActualRatioFamilyOn` inputs in unfolded form. Everything else is the original source, with project imports redirected to their transplanted bundles `Definitions.Def_CK_*`.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA5.Correction` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA5.Correction (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA5/Correction.lean)

import Definitions.Def_CK_CKLaneA5_Correction_q01

namespace CKLaneA5.Assembly
open GeneralCK GeneralCK.Correction GeneralCK.Correction.Complement
/-- `Theorem71Components.correctionDet` -/
theorem correctionDet :
    ∀ p ∈ GeneralCK.Correction.orderedTriangle, 0 ≤ GeneralCK.Correction.Mdet p.1 p.2 :=
  correction_signs.2

end CKLaneA5.Assembly


