-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch22_q02
-- name    : CK_CKLaneC3_CompactBatch22_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T04:07:53.374372+00:00
-- url     : https://prove2.me/theorems/2779f8a5-74e8-410b-b345-744227ca9d21
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch22 (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch22 (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch22 (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch22 (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch22 (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneC3_CompactBatch22_q01

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace CKLaneC3.CompactBatch22
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF
def g080 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (12 / 25 : ℚ), (13 / 25 : ℚ), (27 / 400 : ℚ), (1 / 2 : ℚ), (2, 18), (3, 1), (2, 21), (1, 0), [(2, 17), (2, 18), (2, 19)], [(2, 23), (3, 0), (3, 1), (3, 2)], [(2, 20), (2, 21), (2, 22)], [(1, 0), (1, 1)]⟩

theorem g080_ok : tagOKF CompactData.T CompactData.F g080 = true := by decide +kernel

def g081 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (13 / 25 : ℚ), (14 / 25 : ℚ), (27 / 400 : ℚ), (27 / 50 : ℚ), (2, 20), (3, 3), (2, 23), (1, 0), [(2, 19), (2, 20), (2, 21)], [(3, 1), (3, 2), (3, 3), (3, 4)], [(2, 22), (2, 23), (3, 0)], [(1, 0), (1, 1)]⟩

theorem g081_ok : tagOKF CompactData.T CompactData.F g081 = true := by decide +kernel

def g082 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (14 / 25 : ℚ), (3 / 5 : ℚ), (1 / 16 : ℚ), (29 / 50 : ℚ), (2, 22), (3, 4), (3, 1), (0, 23), [(2, 21), (2, 22), (2, 23)], [(3, 3), (3, 4), (3, 5)], [(3, 0), (3, 1), (3, 2)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g082_ok : tagOKF CompactData.T CompactData.F g082 = true := by decide +kernel

def g083 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (3 / 5 : ℚ), (16 / 25 : ℚ), (1 / 16 : ℚ), (31 / 50 : ℚ), (3, 0), (3, 6), (3, 3), (0, 23), [(2, 23), (3, 0), (3, 1)], [(3, 5), (3, 6), (3, 7)], [(3, 2), (3, 3), (3, 4)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g083_ok : tagOKF CompactData.T CompactData.F g083 = true := by decide +kernel

def g084 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (14 / 25 : ℚ), (3 / 5 : ℚ), (27 / 400 : ℚ), (29 / 50 : ℚ), (2, 22), (3, 5), (3, 1), (1, 0), [(2, 21), (2, 22), (2, 23)], [(3, 3), (3, 4), (3, 5), (3, 6)], [(3, 0), (3, 1), (3, 2)], [(1, 0), (1, 1)]⟩

theorem g084_ok : tagOKF CompactData.T CompactData.F g084 = true := by decide +kernel

def g085 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (3 / 5 : ℚ), (16 / 25 : ℚ), (27 / 400 : ℚ), (31 / 50 : ℚ), (3, 0), (3, 7), (3, 3), (1, 0), [(2, 23), (3, 0), (3, 1)], [(3, 5), (3, 6), (3, 7), (3, 8)], [(3, 2), (3, 3), (3, 4)], [(1, 0), (1, 1)]⟩

theorem g085_ok : tagOKF CompactData.T CompactData.F g085 = true := by decide +kernel

def g086 : Tag := .inr ⟨(7 / 100 : ℚ), (2 / 25 : ℚ), (12 / 25 : ℚ), (13 / 25 : ℚ), (3 / 40 : ℚ), (1 / 2 : ℚ), (2, 18), (3, 1), (2, 22), (1, 3), [(2, 17), (2, 18), (2, 19)], [(3, 0), (3, 1), (3, 2), (3, 3)], [(2, 20), (2, 21), (2, 22), (2, 23)], [(1, 1), (1, 2), (1, 3), (1, 4)]⟩

theorem g086_ok : tagOKF CompactData.T CompactData.F g086 = true := by decide +kernel

def g087 : Tag := .inr ⟨(7 / 100 : ℚ), (2 / 25 : ℚ), (13 / 25 : ℚ), (14 / 25 : ℚ), (3 / 40 : ℚ), (27 / 50 : ℚ), (2, 20), (3, 3), (3, 0), (1, 3), [(2, 19), (2, 20), (2, 21)], [(3, 2), (3, 3), (3, 4), (3, 5)], [(2, 22), (2, 23), (3, 0), (3, 1)], [(1, 1), (1, 2), (1, 3), (1, 4)]⟩

theorem g087_ok : tagOKF CompactData.T CompactData.F g087 = true := by decide +kernel

def g088 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (14 / 25 : ℚ), (3 / 5 : ℚ), (29 / 400 : ℚ), (29 / 50 : ℚ), (2, 22), (3, 5), (3, 2), (1, 2), [(2, 21), (2, 22), (2, 23)], [(3, 4), (3, 5), (3, 6)], [(3, 0), (3, 1), (3, 2), (3, 3)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g088_ok : tagOKF CompactData.T CompactData.F g088 = true := by decide +kernel

def g089 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (3 / 5 : ℚ), (16 / 25 : ℚ), (29 / 400 : ℚ), (31 / 50 : ℚ), (3, 0), (3, 7), (3, 4), (1, 2), [(2, 23), (3, 0), (3, 1)], [(3, 6), (3, 7), (3, 8)], [(3, 2), (3, 3), (3, 4), (3, 5)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g089_ok : tagOKF CompactData.T CompactData.F g089 = true := by decide +kernel

def g090 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (14 / 25 : ℚ), (3 / 5 : ℚ), (31 / 400 : ℚ), (29 / 50 : ℚ), (2, 22), (3, 6), (3, 2), (1, 3), [(2, 21), (2, 22), (2, 23)], [(3, 4), (3, 5), (3, 6), (3, 7)], [(3, 1), (3, 2), (3, 3)], [(1, 3), (1, 4)]⟩

theorem g090_ok : tagOKF CompactData.T CompactData.F g090 = true := by decide +kernel

def g091 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (3 / 5 : ℚ), (16 / 25 : ℚ), (31 / 400 : ℚ), (31 / 50 : ℚ), (3, 0), (3, 8), (3, 4), (1, 3), [(2, 23), (3, 0), (3, 1)], [(3, 6), (3, 7), (3, 8), (3, 9)], [(3, 3), (3, 4), (3, 5)], [(1, 3), (1, 4)]⟩

theorem g091_ok : tagOKF CompactData.T CompactData.F g091 = true := by decide +kernel

def g092 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (16 / 25 : ℚ), (17 / 25 : ℚ), (33 / 800 : ℚ), (33 / 50 : ℚ), (3, 2), (3, 6), (3, 4), (0, 14), [(3, 1), (3, 2), (3, 3)], [(3, 5), (3, 6), (3, 7)], [(3, 3), (3, 4), (3, 5)], [(0, 14), (0, 15)]⟩

theorem g092_ok : tagOKF CompactData.T CompactData.F g092 = true := by decide +kernel

def g093 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (17 / 25 : ℚ), (18 / 25 : ℚ), (33 / 800 : ℚ), (7 / 10 : ℚ), (3, 4), (3, 8), (3, 6), (0, 14), [(3, 3), (3, 4), (3, 5)], [(3, 7), (3, 8), (3, 9)], [(3, 5), (3, 6), (3, 7)], [(0, 14), (0, 15)]⟩

theorem g093_ok : tagOKF CompactData.T CompactData.F g093 = true := by decide +kernel

def g094 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (16 / 25 : ℚ), (17 / 25 : ℚ), (7 / 160 : ℚ), (33 / 50 : ℚ), (3, 2), (3, 6), (3, 4), (0, 16), [(3, 1), (3, 2), (3, 3)], [(3, 5), (3, 6), (3, 7)], [(3, 3), (3, 4), (3, 5)], [(0, 15), (0, 16)]⟩

theorem g094_ok : tagOKF CompactData.T CompactData.F g094 = true := by decide +kernel

def g095 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (17 / 25 : ℚ), (18 / 25 : ℚ), (7 / 160 : ℚ), (7 / 10 : ℚ), (3, 4), (3, 8), (3, 6), (0, 16), [(3, 3), (3, 4), (3, 5)], [(3, 7), (3, 8), (3, 9)], [(3, 5), (3, 6), (3, 7)], [(0, 15), (0, 16)]⟩

theorem g095_ok : tagOKF CompactData.T CompactData.F g095 = true := by decide +kernel

def g096 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (18 / 25 : ℚ), (19 / 25 : ℚ), (33 / 800 : ℚ), (37 / 50 : ℚ), (3, 6), (3, 10), (3, 8), (0, 14), [(3, 5), (3, 6), (3, 7)], [(3, 9), (3, 10), (3, 11)], [(3, 7), (3, 8), (3, 9)], [(0, 14), (0, 15)]⟩

theorem g096_ok : tagOKF CompactData.T CompactData.F g096 = true := by decide +kernel

def g097 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (19 / 25 : ℚ), (4 / 5 : ℚ), (33 / 800 : ℚ), (39 / 50 : ℚ), (3, 8), (3, 12), (3, 10), (0, 14), [(3, 7), (3, 8), (3, 9)], [(3, 11), (3, 12), (3, 13)], [(3, 9), (3, 10), (3, 11)], [(0, 14), (0, 15)]⟩

theorem g097_ok : tagOKF CompactData.T CompactData.F g097 = true := by decide +kernel

def g098 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (18 / 25 : ℚ), (19 / 25 : ℚ), (7 / 160 : ℚ), (37 / 50 : ℚ), (3, 6), (3, 10), (3, 8), (0, 16), [(3, 5), (3, 6), (3, 7)], [(3, 9), (3, 10), (3, 11)], [(3, 7), (3, 8), (3, 9)], [(0, 15), (0, 16)]⟩

theorem g098_ok : tagOKF CompactData.T CompactData.F g098 = true := by decide +kernel

def g099 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (19 / 25 : ℚ), (4 / 5 : ℚ), (7 / 160 : ℚ), (39 / 50 : ℚ), (3, 8), (3, 12), (3, 10), (0, 16), [(3, 7), (3, 8), (3, 9)], [(3, 11), (3, 12), (3, 13)], [(3, 9), (3, 10), (3, 11)], [(0, 15), (0, 16)]⟩

theorem g099_ok : tagOKF CompactData.T CompactData.F g099 = true := by decide +kernel

def g100 : Tag := .inr ⟨(9 / 200 : ℚ), (1 / 20 : ℚ), (16 / 25 : ℚ), (17 / 25 : ℚ), (19 / 400 : ℚ), (33 / 50 : ℚ), (3, 2), (3, 7), (3, 4), (0, 17), [(3, 1), (3, 2), (3, 3)], [(3, 5), (3, 6), (3, 7), (3, 8)], [(3, 3), (3, 4), (3, 5)], [(0, 16), (0, 17), (0, 18)]⟩

theorem g100_ok : tagOKF CompactData.T CompactData.F g100 = true := by decide +kernel

def g101 : Tag := .inr ⟨(9 / 200 : ℚ), (1 / 20 : ℚ), (17 / 25 : ℚ), (18 / 25 : ℚ), (19 / 400 : ℚ), (7 / 10 : ℚ), (3, 4), (3, 9), (3, 6), (0, 17), [(3, 3), (3, 4), (3, 5)], [(3, 7), (3, 8), (3, 9), (3, 10)], [(3, 5), (3, 6), (3, 7)], [(0, 16), (0, 17), (0, 18)]⟩

theorem g101_ok : tagOKF CompactData.T CompactData.F g101 = true := by decide +kernel

def g102 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (18 / 25 : ℚ), (19 / 25 : ℚ), (37 / 800 : ℚ), (37 / 50 : ℚ), (3, 6), (3, 11), (3, 8), (0, 17), [(3, 5), (3, 6), (3, 7)], [(3, 9), (3, 10), (3, 11), (3, 12)], [(3, 7), (3, 8), (3, 9)], [(0, 16), (0, 17)]⟩

theorem g102_ok : tagOKF CompactData.T CompactData.F g102 = true := by decide +kernel

def g103 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (19 / 25 : ℚ), (4 / 5 : ℚ), (37 / 800 : ℚ), (39 / 50 : ℚ), (3, 8), (3, 13), (3, 10), (0, 17), [(3, 7), (3, 8), (3, 9)], [(3, 11), (3, 12), (3, 13), (3, 14)], [(3, 9), (3, 10), (3, 11)], [(0, 16), (0, 17)]⟩

theorem g103_ok : tagOKF CompactData.T CompactData.F g103 = true := by decide +kernel

def g104 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (18 / 25 : ℚ), (19 / 25 : ℚ), (39 / 800 : ℚ), (37 / 50 : ℚ), (3, 6), (3, 11), (3, 8), (0, 18), [(3, 5), (3, 6), (3, 7)], [(3, 10), (3, 11), (3, 12)], [(3, 7), (3, 8), (3, 9)], [(0, 17), (0, 18)]⟩

theorem g104_ok : tagOKF CompactData.T CompactData.F g104 = true := by decide +kernel

def g105 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (19 / 25 : ℚ), (4 / 5 : ℚ), (39 / 800 : ℚ), (39 / 50 : ℚ), (3, 8), (3, 13), (3, 10), (0, 18), [(3, 7), (3, 8), (3, 9)], [(3, 12), (3, 13), (3, 14)], [(3, 9), (3, 10), (3, 11)], [(0, 17), (0, 18)]⟩

theorem g105_ok : tagOKF CompactData.T CompactData.F g105 = true := by decide +kernel

def g106 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (4 / 5 : ℚ), (21 / 25 : ℚ), (33 / 800 : ℚ), (41 / 50 : ℚ), (3, 10), (3, 14), (3, 12), (0, 14), [(3, 9), (3, 10), (3, 11)], [(3, 13), (3, 14), (3, 15)], [(3, 11), (3, 12), (3, 13)], [(0, 14), (0, 15)]⟩

theorem g106_ok : tagOKF CompactData.T CompactData.F g106 = true := by decide +kernel

def g107 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (21 / 25 : ℚ), (22 / 25 : ℚ), (33 / 800 : ℚ), (43 / 50 : ℚ), (3, 12), (3, 16), (3, 14), (0, 14), [(3, 11), (3, 12), (3, 13)], [(3, 15), (3, 16), (3, 17)], [(3, 13), (3, 14), (3, 15)], [(0, 14), (0, 15)]⟩

theorem g107_ok : tagOKF CompactData.T CompactData.F g107 = true := by decide +kernel

def g108 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (4 / 5 : ℚ), (21 / 25 : ℚ), (7 / 160 : ℚ), (41 / 50 : ℚ), (3, 10), (3, 14), (3, 12), (0, 16), [(3, 9), (3, 10), (3, 11)], [(3, 13), (3, 14), (3, 15)], [(3, 11), (3, 12), (3, 13)], [(0, 15), (0, 16)]⟩

theorem g108_ok : tagOKF CompactData.T CompactData.F g108 = true := by decide +kernel

def g109 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (21 / 25 : ℚ), (22 / 25 : ℚ), (7 / 160 : ℚ), (43 / 50 : ℚ), (3, 12), (3, 16), (3, 14), (0, 16), [(3, 11), (3, 12), (3, 13)], [(3, 15), (3, 16), (3, 17)], [(3, 13), (3, 14), (3, 15)], [(0, 15), (0, 16)]⟩

theorem g109_ok : tagOKF CompactData.T CompactData.F g109 = true := by decide +kernel

def g110 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (22 / 25 : ℚ), (23 / 25 : ℚ), (33 / 800 : ℚ), (9 / 10 : ℚ), (3, 14), (3, 18), (3, 16), (0, 14), [(3, 13), (3, 14), (3, 15)], [(3, 17), (3, 18), (3, 19)], [(3, 15), (3, 16), (3, 17)], [(0, 14), (0, 15)]⟩

theorem g110_ok : tagOKF CompactData.T CompactData.F g110 = true := by decide +kernel

def g111 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (23 / 25 : ℚ), (24 / 25 : ℚ), (33 / 800 : ℚ), (47 / 50 : ℚ), (3, 16), (3, 20), (3, 18), (0, 14), [(3, 15), (3, 16), (3, 17)], [(3, 19), (3, 20), (3, 21)], [(3, 17), (3, 18), (3, 19)], [(0, 14), (0, 15)]⟩

theorem g111_ok : tagOKF CompactData.T CompactData.F g111 = true := by decide +kernel

def g112 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (22 / 25 : ℚ), (23 / 25 : ℚ), (7 / 160 : ℚ), (9 / 10 : ℚ), (3, 14), (3, 18), (3, 16), (0, 16), [(3, 13), (3, 14), (3, 15)], [(3, 17), (3, 18), (3, 19)], [(3, 15), (3, 16), (3, 17)], [(0, 15), (0, 16)]⟩

theorem g112_ok : tagOKF CompactData.T CompactData.F g112 = true := by decide +kernel

def g113 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (23 / 25 : ℚ), (24 / 25 : ℚ), (7 / 160 : ℚ), (47 / 50 : ℚ), (3, 16), (3, 20), (3, 18), (0, 16), [(3, 15), (3, 16), (3, 17)], [(3, 19), (3, 20), (3, 21)], [(3, 17), (3, 18), (3, 19)], [(0, 15), (0, 16)]⟩

theorem g113_ok : tagOKF CompactData.T CompactData.F g113 = true := by decide +kernel

def g114 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (4 / 5 : ℚ), (21 / 25 : ℚ), (37 / 800 : ℚ), (41 / 50 : ℚ), (3, 10), (3, 15), (3, 12), (0, 17), [(3, 9), (3, 10), (3, 11)], [(3, 13), (3, 14), (3, 15), (3, 16)], [(3, 11), (3, 12), (3, 13)], [(0, 16), (0, 17)]⟩

theorem g114_ok : tagOKF CompactData.T CompactData.F g114 = true := by decide +kernel

def g115 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (21 / 25 : ℚ), (22 / 25 : ℚ), (37 / 800 : ℚ), (43 / 50 : ℚ), (3, 12), (3, 17), (3, 14), (0, 17), [(3, 11), (3, 12), (3, 13)], [(3, 15), (3, 16), (3, 17), (3, 18)], [(3, 13), (3, 14), (3, 15)], [(0, 16), (0, 17)]⟩

theorem g115_ok : tagOKF CompactData.T CompactData.F g115 = true := by decide +kernel

def g116 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (4 / 5 : ℚ), (21 / 25 : ℚ), (39 / 800 : ℚ), (41 / 50 : ℚ), (3, 10), (3, 15), (3, 12), (0, 18), [(3, 9), (3, 10), (3, 11)], [(3, 14), (3, 15), (3, 16)], [(3, 11), (3, 12), (3, 13)], [(0, 17), (0, 18)]⟩

theorem g116_ok : tagOKF CompactData.T CompactData.F g116 = true := by decide +kernel

def g117 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (21 / 25 : ℚ), (22 / 25 : ℚ), (39 / 800 : ℚ), (43 / 50 : ℚ), (3, 12), (3, 17), (3, 14), (0, 18), [(3, 11), (3, 12), (3, 13)], [(3, 16), (3, 17), (3, 18)], [(3, 13), (3, 14), (3, 15)], [(0, 17), (0, 18)]⟩

theorem g117_ok : tagOKF CompactData.T CompactData.F g117 = true := by decide +kernel

def g118 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (22 / 25 : ℚ), (23 / 25 : ℚ), (37 / 800 : ℚ), (9 / 10 : ℚ), (3, 14), (3, 19), (3, 16), (0, 17), [(3, 13), (3, 14), (3, 15)], [(3, 17), (3, 18), (3, 19), (3, 20)], [(3, 15), (3, 16), (3, 17)], [(0, 16), (0, 17)]⟩

theorem g118_ok : tagOKF CompactData.T CompactData.F g118 = true := by decide +kernel

def g119 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (23 / 25 : ℚ), (24 / 25 : ℚ), (37 / 800 : ℚ), (47 / 50 : ℚ), (3, 16), (3, 21), (3, 18), (0, 17), [(3, 15), (3, 16), (3, 17)], [(3, 19), (3, 20), (3, 21), (3, 22)], [(3, 17), (3, 18), (3, 19)], [(0, 16), (0, 17)]⟩

theorem g119_ok : tagOKF CompactData.T CompactData.F g119 = true := by decide +kernel

end CKLaneC3.CompactBatch22


