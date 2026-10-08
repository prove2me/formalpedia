-- Prove2me | Definitions.Def_CK_CKLaneN23_PosCell_C4_13
-- name    : CK_CKLaneN23_PosCell_C4_13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T13:15:46.131472+00:00
-- url     : https://prove2.me/theorems/79cb42dd-4f5b-4aa9-af54-bb498814b030
-- title:
--   Courtade–Kumar proof module `CKLaneN23.PosCell.C4_13` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.PosCell.C4_13` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.PosCell.C4_13` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.PosCell.C4_13 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/PosCell/C4_13.lean)

import Definitions.Def_CK_CKLaneN23_CPosSplit

-- ===== source module CKLaneN23.PosCell.C4_13 =====
section

/-! Corner positivity grid cell `(4, 13)`: kernel evaluation of `boxCell 4 13` (Lane N23b). -/

namespace CKLaneN23.CT

theorem cell_4_13 : boxCell 4 13 = true := by decide +kernel

end CKLaneN23.CT

end


