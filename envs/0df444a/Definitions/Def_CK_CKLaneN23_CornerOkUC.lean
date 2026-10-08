-- Prove2me | Definitions.Def_CK_CKLaneN23_CornerOkUC
-- name    : CK_CKLaneN23_CornerOkUC
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T09:01:35.455028+00:00
-- url     : https://prove2.me/theorems/4ed4fdf4-3707-4bb9-82ae-c60d81d8df4d
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CornerOkUC` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CornerOkUC` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CornerOkUC` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CornerOkUC (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CornerOkUC.lean)

import Definitions.Def_CK_CKLaneN23_UCon

-- ===== source module CKLaneN23.CornerOkUC =====
section

/-! Kernel evaluation of one part of the corner checker (Lane N23b): `ucCheck = true` by `decide +kernel`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CKLaneN23.CT

theorem uc_ok : ucCheck = true := by decide +kernel

end CKLaneN23.CT

end


