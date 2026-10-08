-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch47_q00
-- name    : CK_CKLaneC3_CompactBatch47_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T10:52:37.457278+00:00
-- url     : https://prove2.me/theorems/0d4be83c-b833-44ab-9d98-114aebb3ccf0
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch47 (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch47 (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch47 (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch47 (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch47 (piece 1 of 4).lean)

import Definitions.Def_CK_CKLaneC3_CompactBatch47_q00_q02

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace CKLaneC3.CompactBatch47
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF
theorem g108_ok : tagOKF CompactData.T CompactData.F g108 = true := by decide +kernel

def g109 : Tag := .inr ⟨(9 / 25 : ℚ), (19 / 50 : ℚ), (1157 / 100 : ℚ), (12 : ℚ), (37 / 100 : ℚ), (2357 / 200 : ℚ), (26, 6), (27, 19), (27, 1), (2, 11), [(25, 19), (25, 20), (25, 21), (25, 22), (25, 23), (26, 0), (26, 1), (26, 2), (26, 3), (26, 4), (26, 5), (26, 6), (26, 7), (26, 8), (26, 9), (26, 10), (26, 11), (26, 12), (26, 13), (26, 14), (26, 15), (26, 16), (26, 17)], [(27, 7), (27, 8), (27, 9), (27, 10), (27, 11), (27, 12), (27, 13), (27, 14), (27, 15), (27, 16), (27, 17), (27, 18), (27, 19), (27, 20), (27, 21), (27, 22), (27, 23), (28, 0), (28, 1), (28, 2), (28, 3), (28, 4), (28, 5), (28, 6), (28, 7)], [(26, 13), (26, 14), (26, 15), (26, 16), (26, 17), (26, 18), (26, 19), (26, 20), (26, 21), (26, 22), (26, 23), (27, 0), (27, 1), (27, 2), (27, 3), (27, 4), (27, 5), (27, 6), (27, 7), (27, 8), (27, 9), (27, 10), (27, 11), (27, 12)], [(2, 11), (2, 12)]⟩

end CKLaneC3.CompactBatch47


