-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch57_q00
-- name    : CK_CKLaneC3_CompactBatch57_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T05:22:05.722394+00:00
-- url     : https://prove2.me/theorems/613fc6cf-ad8e-48f3-8687-67dd15a1dc6d
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch57 (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch57 (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch57 (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch57 (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch57 (piece 1 of 4).lean)

import Definitions.Def_CK_CKLaneC3_CompactBatch57_part03


/-! Lane C3 compact cell batch (generated; memoised chains over the data tables). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactBatch57
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF

def g082 : Tag := .inr ⟨(1201 / 400 : ℚ), (63 / 20 : ℚ), (257 / 25 : ℚ), (1071 / 100 : ℚ), (2461 / 800 : ℚ), (2099 / 200 : ℚ), (23, 14), (36, 9), (29, 23), (8, 3), [(23, 3), (23, 4), (23, 5), (23, 6), (23, 7), (23, 8), (23, 9), (23, 10), (23, 11), (23, 12), (23, 13), (23, 14), (23, 15), (23, 16), (23, 17), (23, 18), (23, 19), (23, 20), (23, 21), (23, 22), (23, 23), (24, 0)], [(35, 15), (35, 16), (35, 17), (35, 18), (35, 19), (35, 20), (35, 21), (35, 22), (35, 23), (36, 0), (36, 1), (36, 2), (36, 3), (36, 4), (36, 5), (36, 6), (36, 7), (36, 8), (36, 9), (36, 10), (36, 11), (36, 12), (36, 13), (36, 14), (36, 15), (36, 16), (36, 17), (36, 18), (36, 19), (36, 20), (36, 21), (36, 22), (36, 23), (37, 0), (37, 1), (37, 2), (37, 3)], [(29, 9), (29, 10), (29, 11), (29, 12), (29, 13), (29, 14), (29, 15), (29, 16), (29, 17), (29, 18), (29, 19), (29, 20), (29, 21), (29, 22), (29, 23), (30, 0), (30, 1), (30, 2), (30, 3), (30, 4), (30, 5), (30, 6), (30, 7), (30, 8), (30, 9), (30, 10), (30, 11), (30, 12), (30, 13), (30, 14)], [(7, 23), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6)]⟩

theorem g082_ok : tagOKF CompactData.T CompactData.F g082 = true := by decide +kernel

def g083 : Tag := .inr ⟨(1201 / 400 : ℚ), (63 / 20 : ℚ), (1071 / 100 : ℚ), (557 / 50 : ℚ), (2461 / 800 : ℚ), (437 / 40 : ℚ), (24, 11), (37, 7), (30, 21), (8, 3), [(24, 0), (24, 1), (24, 2), (24, 3), (24, 4), (24, 5), (24, 6), (24, 7), (24, 8), (24, 9), (24, 10), (24, 11), (24, 12), (24, 13), (24, 14), (24, 15), (24, 16), (24, 17), (24, 18), (24, 19), (24, 20), (24, 21), (24, 22)], [(36, 13), (36, 14), (36, 15), (36, 16), (36, 17), (36, 18), (36, 19), (36, 20), (36, 21), (36, 22), (36, 23), (37, 0), (37, 1), (37, 2), (37, 3), (37, 4), (37, 5), (37, 6), (37, 7), (37, 8), (37, 9), (37, 10), (37, 11), (37, 12), (37, 13), (37, 14), (37, 15), (37, 16), (37, 17), (37, 18), (37, 19), (37, 20), (37, 21), (37, 22), (37, 23), (38, 0), (38, 1)], [(30, 7), (30, 8), (30, 9), (30, 10), (30, 11), (30, 12), (30, 13), (30, 14), (30, 15), (30, 16), (30, 17), (30, 18), (30, 19), (30, 20), (30, 21), (30, 22), (30, 23), (31, 0), (31, 1), (31, 2), (31, 3), (31, 4), (31, 5), (31, 6), (31, 7), (31, 8), (31, 9), (31, 10), (31, 11)], [(7, 23), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6)]⟩

theorem g083_ok : tagOKF CompactData.T CompactData.F g083 = true := by decide +kernel

end CKLaneC3.CompactBatch57


