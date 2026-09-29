-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_Cells_C0230
-- name    : CK_CKLaneM07_CE_Cells_C0230
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:38:56.362012+00:00
-- url     : https://prove2.me/theorems/b1024c51-23a9-4577-9083-6d9d2920f646
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.Cells.C0230` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.Cells.C0230` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.Cells.C0230` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.Cells.C0230 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/Cells/C0230.lean)

import Definitions.Def_CK_CKLaneM07_CE_Cells_C0230_part00

set_option autoImplicit false

namespace CKLaneM07.CE.Cells.C0230

open CKLaneM07.CE CKLaneM07.CE.V2 CKLaneD

theorem h_chkUE : chkUE 8 w = true := by decide +kernel

theorem h_finG : finG 8 cl w = true := by decide +kernel

end CKLaneM07.CE.Cells.C0230


