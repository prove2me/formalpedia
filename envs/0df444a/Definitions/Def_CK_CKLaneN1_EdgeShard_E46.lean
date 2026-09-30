-- Prove2me | Definitions.Def_CK_CKLaneN1_EdgeShard_E46
-- name    : CK_CKLaneN1_EdgeShard_E46
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:01:49.866984+00:00
-- url     : https://prove2.me/theorems/b3d220d5-83f1-4ecc-b055-be3b22b87ac8
-- title:
--   Courtade–Kumar proof module `CKLaneN1.EdgeShard.E46` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.EdgeShard.E46` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.EdgeShard.E46` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.EdgeShard.E46 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/EdgeShard/E46.lean)

import Definitions.Def_CK_CKLaneN1_EdgeTree

-- ===== source module CKLaneN1.EdgeShard.E46 =====
section

/-! Kernel check of generated edgeTree leaves [2300, 2350). -/

namespace CKLaneN1.EdgeShard

open CKLaneN1.Edge

theorem E46 : ((edgeTree.leaves.drop 2300).take 50).all
    (fun q => edgeLeafOK (edgeRoot.ofPath q.1) q.2) = true := by decide +kernel

end CKLaneN1.EdgeShard

end


