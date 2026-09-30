-- Prove2me | Definitions.Def_CK_CKLaneD_ArchTree_part01_q00
-- name    : CK_CKLaneD_ArchTree_part01_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T06:04:30.932951+00:00
-- url     : https://prove2.me/theorems/91b1ffc4-159a-4242-b62b-45ed59f70615
-- title:
--   Courtade–Kumar proof module `CKLaneD.ArchTree (part 2 of 3) (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneD.ArchTree (part 2 of 3) (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneD.ArchTree (part 2 of 3) (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneD.ArchTree (part 2 of 3) (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneD/ArchTree (part 2 of 3) (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneD_ArchTree_part01_q00_t06

namespace CKLaneD
namespace ArchTree
local notation "L" => PTree.leaf
local notation "N" => PTree.node
set_option maxRecDepth 100000 in
/-- The archived partition tree (root box `[3,28] × [1,28] × [0,1]` in `(u, v, t)`). -/
def archTree : PTree :=
  N 0 (N 1 (N 2 (N 0 (N 1 (N 2 archTree_sub_000 archTree_sub_001) archTree_sub_002) (N 1 (N 2 (N 0 archTree_sub_003 archTree_sub_004) archTree_sub_005) archTree_sub_006)) (N 0 (N 1 (N 2 (N 0 archTree_sub_007 archTree_sub_008) (N 0 (N 1 (N 2 (N 0 archTree_sub_009 archTree_sub_010) (N 0 (N 1 (N 2 archTree_sub_011 archTree_sub_012) archTree_sub_013) archTree_sub_014)) (N 2 archTree_sub_015 (N 0 archTree_sub_016 (N 1 (N 2 archTree_sub_017 (N 0 archTree_sub_018 archTree_sub_019)) archTree_sub_020)))) (N 1 archTree_sub_021 (N 2 archTree_sub_022 (N 0 (N 1 archTree_sub_023 (N 2 archTree_sub_024 (N 0 archTree_sub_025 (N 1 archTree_sub_026 archTree_sub_027)))) archTree_sub_028))))) archTree_sub_029) archTree_sub_030)) archTree_sub_031) archTree_sub_032

end ArchTree
end CKLaneD


