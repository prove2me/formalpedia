-- Prove2me | Definitions.Def_CK_CKLaneA5_Correction_q01
-- name    : CK_CKLaneA5_Correction_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-10T02:44:08.225039+00:00
-- url     : https://prove2.me/theorems/6131f760-0433-4763-b3ec-63a861230448
-- title:
--   Courtade–Kumar proof module `CKLaneA5.Correction (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA5.Correction (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA5.Correction (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA5.Correction (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA5/Correction (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneA5_Correction_q00

namespace CKLaneA5.Assembly
open GeneralCK GeneralCK.Correction GeneralCK.Correction.Complement
/-- `Theorem71Components.correctionLeft` -/
theorem correctionLeft :
    ∀ p ∈ GeneralCK.Correction.orderedTriangle, 0 < GeneralCK.Correction.Mleft p.1 p.2 :=
  correction_signs.1

end CKLaneA5.Assembly


