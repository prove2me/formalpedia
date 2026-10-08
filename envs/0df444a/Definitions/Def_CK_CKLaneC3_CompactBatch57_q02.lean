-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch57_q02
-- name    : CK_CKLaneC3_CompactBatch57_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T08:23:08.126271+00:00
-- url     : https://prove2.me/theorems/db3e97c6-ffd4-4bb3-97a7-2f8a6c07da9a
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch57 (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch57 (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch57 (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch57 (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch57 (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneC3_CompactBatch57_q01

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace CKLaneC3.CompactBatch57
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF
def g086 : Tag := .inr ⟨(1201 / 400 : ℚ), (63 / 20 : ℚ), (557 / 50 : ℚ), (1157 / 100 : ℚ), (2461 / 800 : ℚ), (2271 / 200 : ℚ), (25, 9), (38, 4), (31, 18), (8, 3), [(24, 22), (24, 23), (25, 0), (25, 1), (25, 2), (25, 3), (25, 4), (25, 5), (25, 6), (25, 7), (25, 8), (25, 9), (25, 10), (25, 11), (25, 12), (25, 13), (25, 14), (25, 15), (25, 16), (25, 17), (25, 18), (25, 19)], [(37, 10), (37, 11), (37, 12), (37, 13), (37, 14), (37, 15), (37, 16), (37, 17), (37, 18), (37, 19), (37, 20), (37, 21), (37, 22), (37, 23), (38, 0), (38, 1), (38, 2), (38, 3), (38, 4), (38, 5), (38, 6), (38, 7), (38, 8), (38, 9), (38, 10), (38, 11), (38, 12), (38, 13), (38, 14), (38, 15), (38, 16), (38, 17), (38, 18), (38, 19), (38, 20), (38, 21), (38, 22)], [(31, 4), (31, 5), (31, 6), (31, 7), (31, 8), (31, 9), (31, 10), (31, 11), (31, 12), (31, 13), (31, 14), (31, 15), (31, 16), (31, 17), (31, 18), (31, 19), (31, 20), (31, 21), (31, 22), (31, 23), (32, 0), (32, 1), (32, 2), (32, 3), (32, 4), (32, 5), (32, 6), (32, 7), (32, 8), (32, 9)], [(7, 23), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6)]⟩

theorem g086_ok : tagOKF CompactData.T CompactData.F g086 = true := by decide +kernel

def g087 : Tag := .inr ⟨(1201 / 400 : ℚ), (63 / 20 : ℚ), (1157 / 100 : ℚ), (12 : ℚ), (2461 / 800 : ℚ), (2357 / 200 : ℚ), (26, 6), (39, 2), (32, 16), (8, 3), [(25, 19), (25, 20), (25, 21), (25, 22), (25, 23), (26, 0), (26, 1), (26, 2), (26, 3), (26, 4), (26, 5), (26, 6), (26, 7), (26, 8), (26, 9), (26, 10), (26, 11), (26, 12), (26, 13), (26, 14), (26, 15), (26, 16), (26, 17)], [(38, 8), (38, 9), (38, 10), (38, 11), (38, 12), (38, 13), (38, 14), (38, 15), (38, 16), (38, 17), (38, 18), (38, 19), (38, 20), (38, 21), (38, 22), (38, 23), (39, 0), (39, 1), (39, 2), (39, 3), (39, 4), (39, 5), (39, 6), (39, 7), (39, 8), (39, 9), (39, 10), (39, 11), (39, 12), (39, 13), (39, 14), (39, 15), (39, 16), (39, 17), (39, 18), (39, 19), (39, 20)], [(32, 2), (32, 3), (32, 4), (32, 5), (32, 6), (32, 7), (32, 8), (32, 9), (32, 10), (32, 11), (32, 12), (32, 13), (32, 14), (32, 15), (32, 16), (32, 17), (32, 18), (32, 19), (32, 20), (32, 21), (32, 22), (32, 23), (33, 0), (33, 1), (33, 2), (33, 3), (33, 4), (33, 5), (33, 6)], [(7, 23), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6)]⟩

theorem g087_ok : tagOKF CompactData.T CompactData.F g087 = true := by decide +kernel

end CKLaneC3.CompactBatch57


