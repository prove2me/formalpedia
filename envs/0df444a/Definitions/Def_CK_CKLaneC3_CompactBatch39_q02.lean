-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch39_q02
-- name    : CK_CKLaneC3_CompactBatch39_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T02:35:44.19046+00:00
-- url     : https://prove2.me/theorems/be472d7e-5233-46f1-925e-c70d4547e336
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch39 (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch39 (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch39 (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch39 (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch39 (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneC3_CompactBatch39_q01

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace CKLaneC3.CompactBatch39
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF
def g080 : Tag := .inr ⟨(1 / 5 : ℚ), (21 / 100 : ℚ), (9 / 400 : ℚ), (19 / 800 : ℚ), (41 / 200 : ℚ), (37 / 1600 : ℚ), (0, 2), (2, 15), (2, 1), (1, 23), [(0, 2), (0, 3)], [(2, 14), (2, 15)], [(2, 1), (2, 2)], [(1, 23), (2, 0)]⟩

theorem g080_ok : tagOKF CompactData.T CompactData.F g080 = true := by decide +kernel

def g081 : Tag := .inr ⟨(21 / 100 : ℚ), (11 / 50 : ℚ), (9 / 400 : ℚ), (19 / 800 : ℚ), (43 / 200 : ℚ), (37 / 1600 : ℚ), (0, 2), (2, 16), (2, 2), (2, 0), [(0, 2), (0, 3)], [(2, 15), (2, 16)], [(2, 2), (2, 3)], [(2, 0), (2, 1)]⟩

theorem g081_ok : tagOKF CompactData.T CompactData.F g081 = true := by decide +kernel

def g082 : Tag := .inr ⟨(1 / 5 : ℚ), (21 / 100 : ℚ), (19 / 800 : ℚ), (1 / 40 : ℚ), (41 / 200 : ℚ), (39 / 1600 : ℚ), (0, 4), (2, 15), (2, 2), (1, 23), [(0, 3), (0, 4)], [(2, 14), (2, 15)], [(2, 1), (2, 2)], [(1, 23), (2, 0)]⟩

theorem g082_ok : tagOKF CompactData.T CompactData.F g082 = true := by decide +kernel

def g083 : Tag := .inr ⟨(21 / 100 : ℚ), (11 / 50 : ℚ), (19 / 800 : ℚ), (1 / 40 : ℚ), (43 / 200 : ℚ), (39 / 1600 : ℚ), (0, 4), (2, 16), (2, 2), (2, 0), [(0, 3), (0, 4)], [(2, 15), (2, 16)], [(2, 2), (2, 3)], [(2, 0), (2, 1)]⟩

theorem g083_ok : tagOKF CompactData.T CompactData.F g083 = true := by decide +kernel

def g084 : Tag := .inr ⟨(11 / 50 : ℚ), (6 / 25 : ℚ), (9 / 400 : ℚ), (19 / 800 : ℚ), (23 / 100 : ℚ), (37 / 1600 : ℚ), (0, 2), (2, 17), (2, 4), (2, 2), [(0, 2), (0, 3)], [(2, 16), (2, 17), (2, 18)], [(2, 3), (2, 4)], [(2, 1), (2, 2)]⟩

theorem g084_ok : tagOKF CompactData.T CompactData.F g084 = true := by decide +kernel

def g085 : Tag := .inr ⟨(11 / 50 : ℚ), (6 / 25 : ℚ), (19 / 800 : ℚ), (1 / 40 : ℚ), (23 / 100 : ℚ), (39 / 1600 : ℚ), (0, 4), (2, 17), (2, 4), (2, 2), [(0, 3), (0, 4)], [(2, 16), (2, 17), (2, 18)], [(2, 3), (2, 4)], [(2, 1), (2, 2)]⟩

theorem g085_ok : tagOKF CompactData.T CompactData.F g085 = true := by decide +kernel

def g086 : Tag := .inr ⟨(1 / 5 : ℚ), (21 / 100 : ℚ), (1 / 40 : ℚ), (11 / 400 : ℚ), (41 / 200 : ℚ), (21 / 800 : ℚ), (0, 5), (2, 15), (2, 2), (1, 23), [(0, 4), (0, 5), (0, 6)], [(2, 14), (2, 15)], [(2, 1), (2, 2)], [(1, 23), (2, 0)]⟩

theorem g086_ok : tagOKF CompactData.T CompactData.F g086 = true := by decide +kernel

def g087 : Tag := .inr ⟨(21 / 100 : ℚ), (11 / 50 : ℚ), (1 / 40 : ℚ), (11 / 400 : ℚ), (43 / 200 : ℚ), (21 / 800 : ℚ), (0, 5), (2, 16), (2, 3), (2, 0), [(0, 4), (0, 5), (0, 6)], [(2, 15), (2, 16)], [(2, 2), (2, 3)], [(2, 0), (2, 1)]⟩

theorem g087_ok : tagOKF CompactData.T CompactData.F g087 = true := by decide +kernel

def g088 : Tag := .inr ⟨(1 / 5 : ℚ), (21 / 100 : ℚ), (11 / 400 : ℚ), (3 / 100 : ℚ), (41 / 200 : ℚ), (23 / 800 : ℚ), (0, 7), (2, 15), (2, 2), (1, 23), [(0, 6), (0, 7), (0, 8)], [(2, 14), (2, 15)], [(2, 1), (2, 2)], [(1, 23), (2, 0)]⟩

theorem g088_ok : tagOKF CompactData.T CompactData.F g088 = true := by decide +kernel

def g089 : Tag := .inr ⟨(21 / 100 : ℚ), (11 / 50 : ℚ), (11 / 400 : ℚ), (3 / 100 : ℚ), (43 / 200 : ℚ), (23 / 800 : ℚ), (0, 7), (2, 16), (2, 3), (2, 0), [(0, 6), (0, 7), (0, 8)], [(2, 15), (2, 16)], [(2, 2), (2, 3)], [(2, 0), (2, 1)]⟩

theorem g089_ok : tagOKF CompactData.T CompactData.F g089 = true := by decide +kernel

def g090 : Tag := .inr ⟨(11 / 50 : ℚ), (6 / 25 : ℚ), (1 / 40 : ℚ), (11 / 400 : ℚ), (23 / 100 : ℚ), (21 / 800 : ℚ), (0, 5), (2, 17), (2, 4), (2, 2), [(0, 4), (0, 5), (0, 6)], [(2, 16), (2, 17), (2, 18)], [(2, 3), (2, 4), (2, 5)], [(2, 1), (2, 2)]⟩

theorem g090_ok : tagOKF CompactData.T CompactData.F g090 = true := by decide +kernel

def g091 : Tag := .inr ⟨(11 / 50 : ℚ), (6 / 25 : ℚ), (11 / 400 : ℚ), (3 / 100 : ℚ), (23 / 100 : ℚ), (23 / 800 : ℚ), (0, 7), (2, 17), (2, 4), (2, 2), [(0, 6), (0, 7), (0, 8)], [(2, 16), (2, 17), (2, 18)], [(2, 3), (2, 4), (2, 5)], [(2, 1), (2, 2)]⟩

theorem g091_ok : tagOKF CompactData.T CompactData.F g091 = true := by decide +kernel

def g092 : Tag := .inr ⟨(4 / 25 : ℚ), (17 / 100 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (33 / 200 : ℚ), (1 / 32 : ℚ), (0, 9), (2, 11), (1, 22), (1, 19), [(0, 8), (0, 9)], [(2, 10), (2, 11)], [(1, 22), (1, 23)], [(1, 18), (1, 19)]⟩

theorem g092_ok : tagOKF CompactData.T CompactData.F g092 = true := by decide +kernel

def g093 : Tag := .inr ⟨(17 / 100 : ℚ), (9 / 50 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (7 / 40 : ℚ), (1 / 32 : ℚ), (0, 9), (2, 12), (1, 23), (1, 20), [(0, 8), (0, 9)], [(2, 11), (2, 12), (2, 13)], [(1, 23), (2, 0)], [(1, 19), (1, 20), (1, 21)]⟩

theorem g093_ok : tagOKF CompactData.T CompactData.F g093 = true := by decide +kernel

def g094 : Tag := .inr ⟨(4 / 25 : ℚ), (17 / 100 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (33 / 200 : ℚ), (27 / 800 : ℚ), (0, 10), (2, 11), (1, 23), (1, 19), [(0, 9), (0, 10), (0, 11)], [(2, 10), (2, 11), (2, 12)], [(1, 22), (1, 23)], [(1, 18), (1, 19)]⟩

theorem g094_ok : tagOKF CompactData.T CompactData.F g094 = true := by decide +kernel

def g095 : Tag := .inr ⟨(17 / 100 : ℚ), (9 / 50 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (7 / 40 : ℚ), (27 / 800 : ℚ), (0, 10), (2, 12), (2, 0), (1, 20), [(0, 9), (0, 10), (0, 11)], [(2, 11), (2, 12), (2, 13)], [(1, 23), (2, 0)], [(1, 19), (1, 20), (1, 21)]⟩

theorem g095_ok : tagOKF CompactData.T CompactData.F g095 = true := by decide +kernel

def g096 : Tag := .inr ⟨(9 / 50 : ℚ), (19 / 100 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (37 / 200 : ℚ), (1 / 32 : ℚ), (0, 9), (2, 13), (2, 0), (1, 21), [(0, 8), (0, 9)], [(2, 12), (2, 13), (2, 14)], [(2, 0), (2, 1)], [(1, 21), (1, 22)]⟩

theorem g096_ok : tagOKF CompactData.T CompactData.F g096 = true := by decide +kernel

def g097 : Tag := .inr ⟨(19 / 100 : ℚ), (1 / 5 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (39 / 200 : ℚ), (1 / 32 : ℚ), (0, 9), (2, 14), (2, 1), (1, 22), [(0, 8), (0, 9)], [(2, 13), (2, 14), (2, 15)], [(2, 1), (2, 2)], [(1, 22), (1, 23)]⟩

theorem g097_ok : tagOKF CompactData.T CompactData.F g097 = true := by decide +kernel

def g098 : Tag := .inr ⟨(9 / 50 : ℚ), (19 / 100 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (37 / 200 : ℚ), (27 / 800 : ℚ), (0, 10), (2, 13), (2, 1), (1, 21), [(0, 9), (0, 10), (0, 11)], [(2, 13), (2, 14)], [(2, 0), (2, 1)], [(1, 21), (1, 22)]⟩

theorem g098_ok : tagOKF CompactData.T CompactData.F g098 = true := by decide +kernel

def g099 : Tag := .inr ⟨(19 / 100 : ℚ), (1 / 5 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (39 / 200 : ℚ), (27 / 800 : ℚ), (0, 10), (2, 14), (2, 1), (1, 22), [(0, 9), (0, 10), (0, 11)], [(2, 14), (2, 15)], [(2, 1), (2, 2)], [(1, 22), (1, 23)]⟩

theorem g099_ok : tagOKF CompactData.T CompactData.F g099 = true := by decide +kernel

def g100 : Tag := .inr ⟨(4 / 25 : ℚ), (17 / 100 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (33 / 200 : ℚ), (29 / 800 : ℚ), (0, 12), (2, 11), (1, 23), (1, 19), [(0, 11), (0, 12)], [(2, 10), (2, 11), (2, 12)], [(1, 22), (1, 23)], [(1, 18), (1, 19)]⟩

theorem g100_ok : tagOKF CompactData.T CompactData.F g100 = true := by decide +kernel

def g101 : Tag := .inr ⟨(17 / 100 : ℚ), (9 / 50 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (7 / 40 : ℚ), (29 / 800 : ℚ), (0, 12), (2, 12), (2, 0), (1, 20), [(0, 11), (0, 12)], [(2, 12), (2, 13)], [(1, 23), (2, 0)], [(1, 19), (1, 20), (1, 21)]⟩

theorem g101_ok : tagOKF CompactData.T CompactData.F g101 = true := by decide +kernel

def g102 : Tag := .inr ⟨(4 / 25 : ℚ), (17 / 100 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (33 / 200 : ℚ), (31 / 800 : ℚ), (0, 13), (2, 11), (1, 23), (1, 19), [(0, 12), (0, 13), (0, 14)], [(2, 11), (2, 12)], [(1, 22), (1, 23), (2, 0)], [(1, 18), (1, 19)]⟩

theorem g102_ok : tagOKF CompactData.T CompactData.F g102 = true := by decide +kernel

def g103 : Tag := .inr ⟨(17 / 100 : ℚ), (9 / 50 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (7 / 40 : ℚ), (31 / 800 : ℚ), (0, 13), (2, 12), (2, 0), (1, 20), [(0, 12), (0, 13), (0, 14)], [(2, 12), (2, 13)], [(1, 23), (2, 0), (2, 1)], [(1, 19), (1, 20), (1, 21)]⟩

theorem g103_ok : tagOKF CompactData.T CompactData.F g103 = true := by decide +kernel

def g104 : Tag := .inr ⟨(9 / 50 : ℚ), (19 / 100 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (37 / 200 : ℚ), (29 / 800 : ℚ), (0, 12), (2, 13), (2, 1), (1, 21), [(0, 11), (0, 12)], [(2, 13), (2, 14)], [(2, 0), (2, 1)], [(1, 21), (1, 22)]⟩

theorem g104_ok : tagOKF CompactData.T CompactData.F g104 = true := by decide +kernel

def g105 : Tag := .inr ⟨(19 / 100 : ℚ), (1 / 5 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (39 / 200 : ℚ), (29 / 800 : ℚ), (0, 12), (2, 14), (2, 2), (1, 22), [(0, 11), (0, 12)], [(2, 14), (2, 15)], [(2, 1), (2, 2)], [(1, 22), (1, 23)]⟩

theorem g105_ok : tagOKF CompactData.T CompactData.F g105 = true := by decide +kernel

def g106 : Tag := .inr ⟨(9 / 50 : ℚ), (19 / 100 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (37 / 200 : ℚ), (31 / 800 : ℚ), (0, 13), (2, 13), (2, 1), (1, 21), [(0, 12), (0, 13), (0, 14)], [(2, 13), (2, 14)], [(2, 0), (2, 1), (2, 2)], [(1, 21), (1, 22)]⟩

theorem g106_ok : tagOKF CompactData.T CompactData.F g106 = true := by decide +kernel

def g107 : Tag := .inr ⟨(19 / 100 : ℚ), (1 / 5 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (39 / 200 : ℚ), (31 / 800 : ℚ), (0, 13), (2, 14), (2, 2), (1, 22), [(0, 12), (0, 13), (0, 14)], [(2, 14), (2, 15)], [(2, 1), (2, 2)], [(1, 22), (1, 23)]⟩

theorem g107_ok : tagOKF CompactData.T CompactData.F g107 = true := by decide +kernel

def g108 : Tag := .inr ⟨(1 / 5 : ℚ), (21 / 100 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (41 / 200 : ℚ), (1 / 32 : ℚ), (0, 9), (2, 15), (2, 2), (1, 23), [(0, 8), (0, 9)], [(2, 14), (2, 15), (2, 16)], [(2, 2), (2, 3)], [(1, 23), (2, 0)]⟩

theorem g108_ok : tagOKF CompactData.T CompactData.F g108 = true := by decide +kernel

def g109 : Tag := .inr ⟨(21 / 100 : ℚ), (11 / 50 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (43 / 200 : ℚ), (1 / 32 : ℚ), (0, 9), (2, 16), (2, 3), (2, 0), [(0, 8), (0, 9)], [(2, 15), (2, 16), (2, 17)], [(2, 2), (2, 3)], [(2, 0), (2, 1)]⟩

theorem g109_ok : tagOKF CompactData.T CompactData.F g109 = true := by decide +kernel

def g110 : Tag := .inr ⟨(1 / 5 : ℚ), (11 / 50 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (21 / 100 : ℚ), (27 / 800 : ℚ), (0, 10), (2, 16), (2, 3), (2, 0), [(0, 9), (0, 10), (0, 11)], [(2, 15), (2, 16), (2, 17)], [(2, 2), (2, 3), (2, 4)], [(1, 23), (2, 0), (2, 1)]⟩

theorem g110_ok : tagOKF CompactData.T CompactData.F g110 = true := by decide +kernel

def g111 : Tag := .inr ⟨(11 / 50 : ℚ), (6 / 25 : ℚ), (3 / 100 : ℚ), (7 / 200 : ℚ), (23 / 100 : ℚ), (13 / 400 : ℚ), (0, 9), (2, 18), (2, 4), (2, 2), [(0, 8), (0, 9), (0, 10), (0, 11)], [(2, 16), (2, 17), (2, 18), (2, 19)], [(2, 3), (2, 4), (2, 5)], [(2, 1), (2, 2)]⟩

theorem g111_ok : tagOKF CompactData.T CompactData.F g111 = true := by decide +kernel

def g112 : Tag := .inr ⟨(1 / 5 : ℚ), (11 / 50 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (21 / 100 : ℚ), (29 / 800 : ℚ), (0, 12), (2, 16), (2, 3), (2, 0), [(0, 11), (0, 12)], [(2, 15), (2, 16), (2, 17)], [(2, 2), (2, 3), (2, 4)], [(1, 23), (2, 0), (2, 1)]⟩

theorem g112_ok : tagOKF CompactData.T CompactData.F g112 = true := by decide +kernel

def g113 : Tag := .inr ⟨(1 / 5 : ℚ), (11 / 50 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (21 / 100 : ℚ), (31 / 800 : ℚ), (0, 13), (2, 16), (2, 3), (2, 0), [(0, 12), (0, 13), (0, 14)], [(2, 15), (2, 16), (2, 17)], [(2, 2), (2, 3), (2, 4)], [(1, 23), (2, 0), (2, 1)]⟩

theorem g113_ok : tagOKF CompactData.T CompactData.F g113 = true := by decide +kernel

def g114 : Tag := .inr ⟨(11 / 50 : ℚ), (6 / 25 : ℚ), (7 / 200 : ℚ), (1 / 25 : ℚ), (23 / 100 : ℚ), (3 / 80 : ℚ), (0, 12), (2, 18), (2, 5), (2, 2), [(0, 11), (0, 12), (0, 13), (0, 14)], [(2, 17), (2, 18), (2, 19)], [(2, 4), (2, 5), (2, 6)], [(2, 1), (2, 2)]⟩

theorem g114_ok : tagOKF CompactData.T CompactData.F g114 = true := by decide +kernel

def g115 : Tag := .inr ⟨(6 / 25 : ℚ), (13 / 50 : ℚ), (1 / 50 : ℚ), (9 / 400 : ℚ), (1 / 4 : ℚ), (17 / 800 : ℚ), (0, 1), (2, 19), (2, 5), (2, 3), [(0, 0), (0, 1), (0, 2)], [(2, 18), (2, 19), (2, 20)], [(2, 4), (2, 5), (2, 6)], [(2, 2), (2, 3), (2, 4)]⟩

theorem g115_ok : tagOKF CompactData.T CompactData.F g115 = true := by decide +kernel

def g116 : Tag := .inr ⟨(13 / 50 : ℚ), (7 / 25 : ℚ), (1 / 50 : ℚ), (9 / 400 : ℚ), (27 / 100 : ℚ), (17 / 800 : ℚ), (0, 1), (2, 21), (2, 6), (2, 5), [(0, 0), (0, 1), (0, 2)], [(2, 20), (2, 21), (2, 22)], [(2, 6), (2, 7)], [(2, 4), (2, 5), (2, 6)]⟩

theorem g116_ok : tagOKF CompactData.T CompactData.F g116 = true := by decide +kernel

def g117 : Tag := .inr ⟨(6 / 25 : ℚ), (13 / 50 : ℚ), (9 / 400 : ℚ), (1 / 40 : ℚ), (1 / 4 : ℚ), (19 / 800 : ℚ), (0, 3), (2, 19), (2, 5), (2, 3), [(0, 2), (0, 3), (0, 4)], [(2, 18), (2, 19), (2, 20)], [(2, 4), (2, 5), (2, 6)], [(2, 2), (2, 3), (2, 4)]⟩

theorem g117_ok : tagOKF CompactData.T CompactData.F g117 = true := by decide +kernel

def g118 : Tag := .inr ⟨(13 / 50 : ℚ), (7 / 25 : ℚ), (9 / 400 : ℚ), (1 / 40 : ℚ), (27 / 100 : ℚ), (19 / 800 : ℚ), (0, 3), (2, 21), (2, 7), (2, 5), [(0, 2), (0, 3), (0, 4)], [(2, 20), (2, 21), (2, 22)], [(2, 6), (2, 7)], [(2, 4), (2, 5), (2, 6)]⟩

theorem g118_ok : tagOKF CompactData.T CompactData.F g118 = true := by decide +kernel

def g119 : Tag := .inr ⟨(7 / 25 : ℚ), (3 / 10 : ℚ), (1 / 50 : ℚ), (9 / 400 : ℚ), (29 / 100 : ℚ), (17 / 800 : ℚ), (0, 1), (2, 23), (2, 8), (2, 6), [(0, 0), (0, 1), (0, 2)], [(2, 22), (2, 23), (3, 0)], [(2, 7), (2, 8)], [(2, 6), (2, 7)]⟩

theorem g119_ok : tagOKF CompactData.T CompactData.F g119 = true := by decide +kernel

end CKLaneC3.CompactBatch39


