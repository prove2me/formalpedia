-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch47_q00_q02
-- name    : CK_CKLaneC3_CompactBatch47_q00_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T10:26:17.748995+00:00
-- url     : https://prove2.me/theorems/11ad4265-8fa9-4d47-b492-b074c7e64b9d
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch47 (piece 1 of 4) (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch47 (piece 1 of 4) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch47 (piece 1 of 4) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch47 (piece 1 of 4) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch47 (piece 1 of 4) (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneC3_CompactBatch47_q00_q01

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace CKLaneC3.CompactBatch47
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF
def g107 : Tag := .inr ⟨(19 / 50 : ℚ), (2 / 5 : ℚ), (1071 / 100 : ℚ), (557 / 50 : ℚ), (39 / 100 : ℚ), (437 / 40 : ℚ), (24, 11), (26, 2), (25, 7), (2, 12), [(24, 0), (24, 1), (24, 2), (24, 3), (24, 4), (24, 5), (24, 6), (24, 7), (24, 8), (24, 9), (24, 10), (24, 11), (24, 12), (24, 13), (24, 14), (24, 15), (24, 16), (24, 17), (24, 18), (24, 19), (24, 20), (24, 21), (24, 22)], [(25, 14), (25, 15), (25, 16), (25, 17), (25, 18), (25, 19), (25, 20), (25, 21), (25, 22), (25, 23), (26, 0), (26, 1), (26, 2), (26, 3), (26, 4), (26, 5), (26, 6), (26, 7), (26, 8), (26, 9), (26, 10), (26, 11), (26, 12), (26, 13), (26, 14)], [(24, 19), (24, 20), (24, 21), (24, 22), (24, 23), (25, 0), (25, 1), (25, 2), (25, 3), (25, 4), (25, 5), (25, 6), (25, 7), (25, 8), (25, 9), (25, 10), (25, 11), (25, 12), (25, 13), (25, 14), (25, 15), (25, 16), (25, 17), (25, 18)], [(2, 12), (2, 13)]⟩

theorem g107_ok : tagOKF CompactData.T CompactData.F g107 = true := by decide +kernel

def g108 : Tag := .inr ⟨(9 / 25 : ℚ), (19 / 50 : ℚ), (557 / 50 : ℚ), (1157 / 100 : ℚ), (37 / 100 : ℚ), (2271 / 200 : ℚ), (25, 9), (26, 22), (26, 3), (2, 11), [(24, 22), (24, 23), (25, 0), (25, 1), (25, 2), (25, 3), (25, 4), (25, 5), (25, 6), (25, 7), (25, 8), (25, 9), (25, 10), (25, 11), (25, 12), (25, 13), (25, 14), (25, 15), (25, 16), (25, 17), (25, 18), (25, 19)], [(26, 10), (26, 11), (26, 12), (26, 13), (26, 14), (26, 15), (26, 16), (26, 17), (26, 18), (26, 19), (26, 20), (26, 21), (26, 22), (26, 23), (27, 0), (27, 1), (27, 2), (27, 3), (27, 4), (27, 5), (27, 6), (27, 7), (27, 8), (27, 9)], [(25, 16), (25, 17), (25, 18), (25, 19), (25, 20), (25, 21), (25, 22), (25, 23), (26, 0), (26, 1), (26, 2), (26, 3), (26, 4), (26, 5), (26, 6), (26, 7), (26, 8), (26, 9), (26, 10), (26, 11), (26, 12), (26, 13), (26, 14)], [(2, 11), (2, 12)]⟩

end CKLaneC3.CompactBatch47


