-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch23
-- name    : CK_CKLaneC3_CompactBatch23
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:29:17.170301+00:00
-- url     : https://prove2.me/theorems/4fc74347-ac7d-4311-876e-87493c37dfac
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch23` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch23` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch23` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch23 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch23.lean)

import Definitions.Def_CK_CKLaneC3_CompactBatch23_part00

/-! Lane C3 compact cell batch (generated; memoised chains over the data tables). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactBatch23
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF

def g087 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (38 / 25 : ℚ), (8 / 5 : ℚ), (37 / 800 : ℚ), (39 / 25 : ℚ), (4, 23), (5, 4), (5, 1), (0, 17), [(4, 21), (4, 22), (4, 23), (5, 0), (5, 1)], [(5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6)], [(4, 23), (5, 0), (5, 1), (5, 2), (5, 3)], [(0, 16), (0, 17)]⟩

theorem g087_ok : tagOKF CompactData.T CompactData.F g087 = true := by decide +kernel

def g088 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (36 / 25 : ℚ), (38 / 25 : ℚ), (39 / 800 : ℚ), (37 / 25 : ℚ), (4, 19), (5, 0), (4, 21), (0, 18), [(4, 17), (4, 18), (4, 19), (4, 20), (4, 21)], [(4, 22), (4, 23), (5, 0), (5, 1), (5, 2)], [(4, 19), (4, 20), (4, 21), (4, 22), (4, 23)], [(0, 17), (0, 18)]⟩

theorem g088_ok : tagOKF CompactData.T CompactData.F g088 = true := by decide +kernel

def g089 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (38 / 25 : ℚ), (8 / 5 : ℚ), (39 / 800 : ℚ), (39 / 25 : ℚ), (4, 23), (5, 4), (5, 1), (0, 18), [(4, 21), (4, 22), (4, 23), (5, 0), (5, 1)], [(5, 2), (5, 3), (5, 4), (5, 5), (5, 6)], [(4, 23), (5, 0), (5, 1), (5, 2), (5, 3)], [(0, 17), (0, 18)]⟩

theorem g089_ok : tagOKF CompactData.T CompactData.F g089 = true := by decide +kernel

def g090 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (8 / 5 : ℚ), (42 / 25 : ℚ), (33 / 800 : ℚ), (41 / 25 : ℚ), (5, 3), (5, 7), (5, 5), (0, 14), [(5, 1), (5, 2), (5, 3), (5, 4), (5, 5)], [(5, 5), (5, 6), (5, 7), (5, 8), (5, 9)], [(5, 3), (5, 4), (5, 5), (5, 6), (5, 7)], [(0, 14), (0, 15)]⟩

theorem g090_ok : tagOKF CompactData.T CompactData.F g090 = true := by decide +kernel

def g091 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (42 / 25 : ℚ), (44 / 25 : ℚ), (33 / 800 : ℚ), (43 / 25 : ℚ), (5, 7), (5, 11), (5, 9), (0, 14), [(5, 5), (5, 6), (5, 7), (5, 8), (5, 9)], [(5, 9), (5, 10), (5, 11), (5, 12), (5, 13)], [(5, 7), (5, 8), (5, 9), (5, 10), (5, 11)], [(0, 14), (0, 15)]⟩

theorem g091_ok : tagOKF CompactData.T CompactData.F g091 = true := by decide +kernel

def g092 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (8 / 5 : ℚ), (42 / 25 : ℚ), (7 / 160 : ℚ), (41 / 25 : ℚ), (5, 3), (5, 7), (5, 5), (0, 16), [(5, 1), (5, 2), (5, 3), (5, 4), (5, 5)], [(5, 5), (5, 6), (5, 7), (5, 8), (5, 9)], [(5, 3), (5, 4), (5, 5), (5, 6), (5, 7)], [(0, 15), (0, 16)]⟩

theorem g092_ok : tagOKF CompactData.T CompactData.F g092 = true := by decide +kernel

def g093 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (42 / 25 : ℚ), (44 / 25 : ℚ), (7 / 160 : ℚ), (43 / 25 : ℚ), (5, 7), (5, 11), (5, 9), (0, 16), [(5, 5), (5, 6), (5, 7), (5, 8), (5, 9)], [(5, 9), (5, 10), (5, 11), (5, 12), (5, 13)], [(5, 7), (5, 8), (5, 9), (5, 10), (5, 11)], [(0, 15), (0, 16)]⟩

theorem g093_ok : tagOKF CompactData.T CompactData.F g093 = true := by decide +kernel

def g094 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (44 / 25 : ℚ), (46 / 25 : ℚ), (33 / 800 : ℚ), (9 / 5 : ℚ), (5, 11), (5, 15), (5, 13), (0, 14), [(5, 9), (5, 10), (5, 11), (5, 12), (5, 13)], [(5, 13), (5, 14), (5, 15), (5, 16), (5, 17)], [(5, 11), (5, 12), (5, 13), (5, 14), (5, 15)], [(0, 14), (0, 15)]⟩

theorem g094_ok : tagOKF CompactData.T CompactData.F g094 = true := by decide +kernel

def g095 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (46 / 25 : ℚ), (48 / 25 : ℚ), (33 / 800 : ℚ), (47 / 25 : ℚ), (5, 15), (5, 19), (5, 17), (0, 14), [(5, 13), (5, 14), (5, 15), (5, 16), (5, 17)], [(5, 17), (5, 18), (5, 19), (5, 20), (5, 21)], [(5, 15), (5, 16), (5, 17), (5, 18), (5, 19)], [(0, 14), (0, 15)]⟩

theorem g095_ok : tagOKF CompactData.T CompactData.F g095 = true := by decide +kernel

def g096 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (44 / 25 : ℚ), (46 / 25 : ℚ), (7 / 160 : ℚ), (9 / 5 : ℚ), (5, 11), (5, 15), (5, 13), (0, 16), [(5, 9), (5, 10), (5, 11), (5, 12), (5, 13)], [(5, 13), (5, 14), (5, 15), (5, 16), (5, 17)], [(5, 11), (5, 12), (5, 13), (5, 14), (5, 15)], [(0, 15), (0, 16)]⟩

theorem g096_ok : tagOKF CompactData.T CompactData.F g096 = true := by decide +kernel

def g097 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (46 / 25 : ℚ), (48 / 25 : ℚ), (7 / 160 : ℚ), (47 / 25 : ℚ), (5, 15), (5, 19), (5, 17), (0, 16), [(5, 13), (5, 14), (5, 15), (5, 16), (5, 17)], [(5, 17), (5, 18), (5, 19), (5, 20), (5, 21)], [(5, 15), (5, 16), (5, 17), (5, 18), (5, 19)], [(0, 15), (0, 16)]⟩

theorem g097_ok : tagOKF CompactData.T CompactData.F g097 = true := by decide +kernel

def g098 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (8 / 5 : ℚ), (42 / 25 : ℚ), (37 / 800 : ℚ), (41 / 25 : ℚ), (5, 3), (5, 8), (5, 5), (0, 17), [(5, 1), (5, 2), (5, 3), (5, 4), (5, 5)], [(5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10)], [(5, 3), (5, 4), (5, 5), (5, 6), (5, 7)], [(0, 16), (0, 17)]⟩

theorem g098_ok : tagOKF CompactData.T CompactData.F g098 = true := by decide +kernel

def g099 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (42 / 25 : ℚ), (44 / 25 : ℚ), (37 / 800 : ℚ), (43 / 25 : ℚ), (5, 7), (5, 12), (5, 9), (0, 17), [(5, 5), (5, 6), (5, 7), (5, 8), (5, 9)], [(5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14)], [(5, 7), (5, 8), (5, 9), (5, 10), (5, 11)], [(0, 16), (0, 17)]⟩

theorem g099_ok : tagOKF CompactData.T CompactData.F g099 = true := by decide +kernel

def g100 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (8 / 5 : ℚ), (42 / 25 : ℚ), (39 / 800 : ℚ), (41 / 25 : ℚ), (5, 3), (5, 8), (5, 5), (0, 18), [(5, 1), (5, 2), (5, 3), (5, 4), (5, 5)], [(5, 6), (5, 7), (5, 8), (5, 9), (5, 10)], [(5, 3), (5, 4), (5, 5), (5, 6), (5, 7)], [(0, 17), (0, 18)]⟩

theorem g100_ok : tagOKF CompactData.T CompactData.F g100 = true := by decide +kernel

def g101 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (42 / 25 : ℚ), (44 / 25 : ℚ), (39 / 800 : ℚ), (43 / 25 : ℚ), (5, 7), (5, 12), (5, 9), (0, 18), [(5, 5), (5, 6), (5, 7), (5, 8), (5, 9)], [(5, 10), (5, 11), (5, 12), (5, 13), (5, 14)], [(5, 7), (5, 8), (5, 9), (5, 10), (5, 11)], [(0, 17), (0, 18)]⟩

theorem g101_ok : tagOKF CompactData.T CompactData.F g101 = true := by decide +kernel

def g102 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (44 / 25 : ℚ), (46 / 25 : ℚ), (37 / 800 : ℚ), (9 / 5 : ℚ), (5, 11), (5, 16), (5, 13), (0, 17), [(5, 9), (5, 10), (5, 11), (5, 12), (5, 13)], [(5, 13), (5, 14), (5, 15), (5, 16), (5, 17), (5, 18)], [(5, 11), (5, 12), (5, 13), (5, 14), (5, 15)], [(0, 16), (0, 17)]⟩

theorem g102_ok : tagOKF CompactData.T CompactData.F g102 = true := by decide +kernel

def g103 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (46 / 25 : ℚ), (48 / 25 : ℚ), (37 / 800 : ℚ), (47 / 25 : ℚ), (5, 15), (5, 20), (5, 17), (0, 17), [(5, 13), (5, 14), (5, 15), (5, 16), (5, 17)], [(5, 17), (5, 18), (5, 19), (5, 20), (5, 21), (5, 22)], [(5, 15), (5, 16), (5, 17), (5, 18), (5, 19)], [(0, 16), (0, 17)]⟩

theorem g103_ok : tagOKF CompactData.T CompactData.F g103 = true := by decide +kernel

def g104 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (44 / 25 : ℚ), (46 / 25 : ℚ), (39 / 800 : ℚ), (9 / 5 : ℚ), (5, 11), (5, 16), (5, 13), (0, 18), [(5, 9), (5, 10), (5, 11), (5, 12), (5, 13)], [(5, 14), (5, 15), (5, 16), (5, 17), (5, 18)], [(5, 11), (5, 12), (5, 13), (5, 14), (5, 15)], [(0, 17), (0, 18)]⟩

theorem g104_ok : tagOKF CompactData.T CompactData.F g104 = true := by decide +kernel

def g105 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (46 / 25 : ℚ), (48 / 25 : ℚ), (39 / 800 : ℚ), (47 / 25 : ℚ), (5, 15), (5, 20), (5, 17), (0, 18), [(5, 13), (5, 14), (5, 15), (5, 16), (5, 17)], [(5, 18), (5, 19), (5, 20), (5, 21), (5, 22)], [(5, 15), (5, 16), (5, 17), (5, 18), (5, 19)], [(0, 17), (0, 18)]⟩

theorem g105_ok : tagOKF CompactData.T CompactData.F g105 = true := by decide +kernel

def g106 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (32 / 25 : ℚ), (34 / 25 : ℚ), (21 / 400 : ℚ), (33 / 25 : ℚ), (4, 11), (4, 16), (4, 14), (0, 19), [(4, 9), (4, 10), (4, 11), (4, 12), (4, 13)], [(4, 14), (4, 15), (4, 16), (4, 17), (4, 18)], [(4, 11), (4, 12), (4, 13), (4, 14), (4, 15), (4, 16)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g106_ok : tagOKF CompactData.T CompactData.F g106 = true := by decide +kernel

def g107 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (34 / 25 : ℚ), (36 / 25 : ℚ), (21 / 400 : ℚ), (7 / 5 : ℚ), (4, 15), (4, 20), (4, 18), (0, 19), [(4, 13), (4, 14), (4, 15), (4, 16), (4, 17)], [(4, 18), (4, 19), (4, 20), (4, 21), (4, 22)], [(4, 15), (4, 16), (4, 17), (4, 18), (4, 19), (4, 20)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g107_ok : tagOKF CompactData.T CompactData.F g107 = true := by decide +kernel

def g108 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (32 / 25 : ℚ), (34 / 25 : ℚ), (23 / 400 : ℚ), (33 / 25 : ℚ), (4, 11), (4, 17), (4, 14), (0, 21), [(4, 9), (4, 10), (4, 11), (4, 12), (4, 13)], [(4, 14), (4, 15), (4, 16), (4, 17), (4, 18), (4, 19)], [(4, 12), (4, 13), (4, 14), (4, 15), (4, 16)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g108_ok : tagOKF CompactData.T CompactData.F g108 = true := by decide +kernel

def g109 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (34 / 25 : ℚ), (36 / 25 : ℚ), (23 / 400 : ℚ), (7 / 5 : ℚ), (4, 15), (4, 21), (4, 18), (0, 21), [(4, 13), (4, 14), (4, 15), (4, 16), (4, 17)], [(4, 18), (4, 19), (4, 20), (4, 21), (4, 22), (4, 23)], [(4, 16), (4, 17), (4, 18), (4, 19), (4, 20)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g109_ok : tagOKF CompactData.T CompactData.F g109 = true := by decide +kernel

def g110 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (36 / 25 : ℚ), (38 / 25 : ℚ), (21 / 400 : ℚ), (37 / 25 : ℚ), (4, 19), (5, 0), (4, 22), (0, 19), [(4, 17), (4, 18), (4, 19), (4, 20), (4, 21)], [(4, 22), (4, 23), (5, 0), (5, 1), (5, 2)], [(4, 19), (4, 20), (4, 21), (4, 22), (4, 23), (5, 0)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g110_ok : tagOKF CompactData.T CompactData.F g110 = true := by decide +kernel

def g111 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (38 / 25 : ℚ), (8 / 5 : ℚ), (21 / 400 : ℚ), (39 / 25 : ℚ), (4, 23), (5, 4), (5, 2), (0, 19), [(4, 21), (4, 22), (4, 23), (5, 0), (5, 1)], [(5, 2), (5, 3), (5, 4), (5, 5), (5, 6)], [(4, 23), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g111_ok : tagOKF CompactData.T CompactData.F g111 = true := by decide +kernel

def g112 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (36 / 25 : ℚ), (38 / 25 : ℚ), (23 / 400 : ℚ), (37 / 25 : ℚ), (4, 19), (5, 1), (4, 22), (0, 21), [(4, 17), (4, 18), (4, 19), (4, 20), (4, 21)], [(4, 22), (4, 23), (5, 0), (5, 1), (5, 2), (5, 3)], [(4, 20), (4, 21), (4, 22), (4, 23), (5, 0)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g112_ok : tagOKF CompactData.T CompactData.F g112 = true := by decide +kernel

def g113 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (38 / 25 : ℚ), (8 / 5 : ℚ), (23 / 400 : ℚ), (39 / 25 : ℚ), (4, 23), (5, 5), (5, 2), (0, 21), [(4, 21), (4, 22), (4, 23), (5, 0), (5, 1)], [(5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7)], [(5, 0), (5, 1), (5, 2), (5, 3), (5, 4)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g113_ok : tagOKF CompactData.T CompactData.F g113 = true := by decide +kernel

def g114 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (8 / 5 : ℚ), (42 / 25 : ℚ), (41 / 800 : ℚ), (41 / 25 : ℚ), (5, 3), (5, 8), (5, 5), (0, 19), [(5, 1), (5, 2), (5, 3), (5, 4), (5, 5)], [(5, 6), (5, 7), (5, 8), (5, 9), (5, 10)], [(5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8)], [(0, 18), (0, 19)]⟩

theorem g114_ok : tagOKF CompactData.T CompactData.F g114 = true := by decide +kernel

def g115 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (42 / 25 : ℚ), (44 / 25 : ℚ), (41 / 800 : ℚ), (43 / 25 : ℚ), (5, 7), (5, 12), (5, 9), (0, 19), [(5, 5), (5, 6), (5, 7), (5, 8), (5, 9)], [(5, 10), (5, 11), (5, 12), (5, 13), (5, 14)], [(5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12)], [(0, 18), (0, 19)]⟩

theorem g115_ok : tagOKF CompactData.T CompactData.F g115 = true := by decide +kernel

def g116 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (8 / 5 : ℚ), (42 / 25 : ℚ), (43 / 800 : ℚ), (41 / 25 : ℚ), (5, 3), (5, 8), (5, 6), (0, 20), [(5, 1), (5, 2), (5, 3), (5, 4), (5, 5)], [(5, 6), (5, 7), (5, 8), (5, 9), (5, 10)], [(5, 4), (5, 5), (5, 6), (5, 7), (5, 8)], [(0, 19), (0, 20)]⟩

theorem g116_ok : tagOKF CompactData.T CompactData.F g116 = true := by decide +kernel

def g117 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (42 / 25 : ℚ), (44 / 25 : ℚ), (43 / 800 : ℚ), (43 / 25 : ℚ), (5, 7), (5, 12), (5, 10), (0, 20), [(5, 5), (5, 6), (5, 7), (5, 8), (5, 9)], [(5, 10), (5, 11), (5, 12), (5, 13), (5, 14)], [(5, 8), (5, 9), (5, 10), (5, 11), (5, 12)], [(0, 19), (0, 20)]⟩

theorem g117_ok : tagOKF CompactData.T CompactData.F g117 = true := by decide +kernel

def g118 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (44 / 25 : ℚ), (46 / 25 : ℚ), (41 / 800 : ℚ), (9 / 5 : ℚ), (5, 11), (5, 16), (5, 13), (0, 19), [(5, 9), (5, 10), (5, 11), (5, 12), (5, 13)], [(5, 14), (5, 15), (5, 16), (5, 17), (5, 18)], [(5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (5, 16)], [(0, 18), (0, 19)]⟩

theorem g118_ok : tagOKF CompactData.T CompactData.F g118 = true := by decide +kernel

def g119 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (46 / 25 : ℚ), (48 / 25 : ℚ), (41 / 800 : ℚ), (47 / 25 : ℚ), (5, 15), (5, 20), (5, 17), (0, 19), [(5, 13), (5, 14), (5, 15), (5, 16), (5, 17)], [(5, 18), (5, 19), (5, 20), (5, 21), (5, 22)], [(5, 15), (5, 16), (5, 17), (5, 18), (5, 19), (5, 20)], [(0, 18), (0, 19)]⟩

theorem g119_ok : tagOKF CompactData.T CompactData.F g119 = true := by decide +kernel

def tags : List Tag := [g000, g001, g002, g003, g004, g005, g006, g007, g008, g009, g010, g011, g012, g013, g014, g015, g016, g017, g018, g019, g020, g021, g022, g023, g024, g025, g026, g027, g028, g029, g030, g031, g032, g033, g034, g035, g036, g037, g038, g039, g040, g041, g042, g043, g044, g045, g046, g047, g048, g049, g050, g051, g052, g053, g054, g055, g056, g057, g058, g059, g060, g061, g062, g063, g064, g065, g066, g067, g068, g069, g070, g071, g072, g073, g074, g075, g076, g077, g078, g079, g080, g081, g082, g083, g084, g085, g086, g087, g088, g089, g090, g091, g092, g093, g094, g095, g096, g097, g098, g099, g100, g101, g102, g103, g104, g105, g106, g107, g108, g109, g110, g111, g112, g113, g114, g115, g116, g117, g118, g119]

theorem tags_ok : tags.all (tagOKF CompactData.T CompactData.F) = true := by
  simp only [tags, List.all_cons, List.all_nil, g000_ok, g001_ok, g002_ok, g003_ok, g004_ok, g005_ok, g006_ok, g007_ok, g008_ok, g009_ok, g010_ok, g011_ok, g012_ok, g013_ok, g014_ok, g015_ok, g016_ok, g017_ok, g018_ok, g019_ok, g020_ok, g021_ok, g022_ok, g023_ok, g024_ok, g025_ok, g026_ok, g027_ok, g028_ok, g029_ok, g030_ok, g031_ok, g032_ok, g033_ok, g034_ok, g035_ok, g036_ok, g037_ok, g038_ok, g039_ok, g040_ok, g041_ok, g042_ok, g043_ok, g044_ok, g045_ok, g046_ok, g047_ok, g048_ok, g049_ok, g050_ok, g051_ok, g052_ok, g053_ok, g054_ok, g055_ok, g056_ok, g057_ok, g058_ok, g059_ok, g060_ok, g061_ok, g062_ok, g063_ok, g064_ok, g065_ok, g066_ok, g067_ok, g068_ok, g069_ok, g070_ok, g071_ok, g072_ok, g073_ok, g074_ok, g075_ok, g076_ok, g077_ok, g078_ok, g079_ok, g080_ok, g081_ok, g082_ok, g083_ok, g084_ok, g085_ok, g086_ok, g087_ok, g088_ok, g089_ok, g090_ok, g091_ok, g092_ok, g093_ok, g094_ok, g095_ok, g096_ok, g097_ok, g098_ok, g099_ok, g100_ok, g101_ok, g102_ok, g103_ok, g104_ok, g105_ok, g106_ok, g107_ok, g108_ok, g109_ok, g110_ok, g111_ok, g112_ok, g113_ok, g114_ok, g115_ok, g116_ok, g117_ok, g118_ok, g119_ok, Bool.and_self]

end CKLaneC3.CompactBatch23


