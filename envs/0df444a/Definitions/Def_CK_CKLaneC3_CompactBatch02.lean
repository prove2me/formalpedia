-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch02
-- name    : CK_CKLaneC3_CompactBatch02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T06:34:41.81915+00:00
-- url     : https://prove2.me/theorems/3b74f611-b789-4874-b00b-63406056112b
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch02` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch02` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch02` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch02 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch02.lean)

import Definitions.Def_CK_CKLaneC3_CompactBatch02_part00

/-! Lane C3 compact cell batch (generated; memoised chains over the data tables). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactBatch02
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF

def g069 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (21 / 200 : ℚ), (11 / 100 : ℚ), (31 / 800 : ℚ), (43 / 400 : ℚ), (1, 10), (1, 21), (1, 16), (0, 13), [(1, 9), (1, 10)], [(1, 21), (1, 22)], [(1, 16), (1, 17)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g069_ok : tagOKF CompactData.T CompactData.F g069 = true := by decide +kernel

def g070 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (11 / 100 : ℚ), (23 / 200 : ℚ), (29 / 800 : ℚ), (9 / 80 : ℚ), (1, 11), (1, 21), (1, 17), (0, 12), [(1, 10), (1, 11)], [(1, 21), (1, 22)], [(1, 16), (1, 17)], [(0, 11), (0, 12)]⟩

theorem g070_ok : tagOKF CompactData.T CompactData.F g070 = true := by decide +kernel

def g071 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (23 / 200 : ℚ), (3 / 25 : ℚ), (29 / 800 : ℚ), (47 / 400 : ℚ), (1, 12), (1, 22), (1, 17), (0, 12), [(1, 11), (1, 12)], [(1, 21), (1, 22)], [(1, 17), (1, 18)], [(0, 11), (0, 12)]⟩

theorem g071_ok : tagOKF CompactData.T CompactData.F g071 = true := by decide +kernel

def g072 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (11 / 100 : ℚ), (23 / 200 : ℚ), (31 / 800 : ℚ), (9 / 80 : ℚ), (1, 11), (1, 22), (1, 17), (0, 13), [(1, 10), (1, 11)], [(1, 21), (1, 22)], [(1, 16), (1, 17)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g072_ok : tagOKF CompactData.T CompactData.F g072 = true := by decide +kernel

def g073 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (23 / 200 : ℚ), (3 / 25 : ℚ), (31 / 800 : ℚ), (47 / 400 : ℚ), (1, 12), (1, 22), (1, 18), (0, 13), [(1, 11), (1, 12)], [(1, 22), (1, 23)], [(1, 17), (1, 18)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g073_ok : tagOKF CompactData.T CompactData.F g073 = true := by decide +kernel

def g074 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (3 / 25 : ℚ), (1 / 8 : ℚ), (49 / 1600 : ℚ), (49 / 400 : ℚ), (1, 13), (1, 21), (1, 17), (0, 8), [(1, 12), (1, 13)], [(1, 21)], [(1, 17), (1, 18)], [(0, 8), (0, 9)]⟩

theorem g074_ok : tagOKF CompactData.T CompactData.F g074 = true := by decide +kernel

def g075 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (1 / 8 : ℚ), (13 / 100 : ℚ), (49 / 1600 : ℚ), (51 / 400 : ℚ), (1, 13), (1, 22), (1, 18), (0, 8), [(1, 13), (1, 14)], [(1, 21), (1, 22)], [(1, 17), (1, 18)], [(0, 8), (0, 9)]⟩

theorem g075_ok : tagOKF CompactData.T CompactData.F g075 = true := by decide +kernel

def g076 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (3 / 25 : ℚ), (1 / 8 : ℚ), (51 / 1600 : ℚ), (49 / 400 : ℚ), (1, 13), (1, 21), (1, 17), (0, 9), [(1, 12), (1, 13)], [(1, 21), (1, 22)], [(1, 17), (1, 18)], [(0, 9)]⟩

theorem g076_ok : tagOKF CompactData.T CompactData.F g076 = true := by decide +kernel

def g077 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (1 / 8 : ℚ), (13 / 100 : ℚ), (51 / 1600 : ℚ), (51 / 400 : ℚ), (1, 13), (1, 22), (1, 18), (0, 9), [(1, 13), (1, 14)], [(1, 21), (1, 22)], [(1, 18)], [(0, 9)]⟩

theorem g077_ok : tagOKF CompactData.T CompactData.F g077 = true := by decide +kernel

def g078 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (13 / 100 : ℚ), (7 / 50 : ℚ), (49 / 1600 : ℚ), (27 / 200 : ℚ), (1, 15), (1, 22), (1, 19), (0, 8), [(1, 14), (1, 15)], [(1, 22), (1, 23)], [(1, 18), (1, 19), (1, 20)], [(0, 8), (0, 9)]⟩

theorem g078_ok : tagOKF CompactData.T CompactData.F g078 = true := by decide +kernel

def g079 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (13 / 100 : ℚ), (7 / 50 : ℚ), (51 / 1600 : ℚ), (27 / 200 : ℚ), (1, 15), (1, 23), (1, 19), (0, 9), [(1, 14), (1, 15)], [(1, 22), (1, 23)], [(1, 18), (1, 19), (1, 20)], [(0, 9)]⟩

theorem g079_ok : tagOKF CompactData.T CompactData.F g079 = true := by decide +kernel

def g080 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (3 / 25 : ℚ), (1 / 8 : ℚ), (27 / 800 : ℚ), (49 / 400 : ℚ), (1, 13), (1, 22), (1, 18), (0, 10), [(1, 12), (1, 13)], [(1, 21), (1, 22)], [(1, 17), (1, 18)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g080_ok : tagOKF CompactData.T CompactData.F g080 = true := by decide +kernel

def g081 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (1 / 8 : ℚ), (13 / 100 : ℚ), (27 / 800 : ℚ), (51 / 400 : ℚ), (1, 13), (1, 22), (1, 18), (0, 10), [(1, 13), (1, 14)], [(1, 22), (1, 23)], [(1, 18), (1, 19)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g081_ok : tagOKF CompactData.T CompactData.F g081 = true := by decide +kernel

def g082 : Tag := .inr ⟨(13 / 400 : ℚ), (27 / 800 : ℚ), (13 / 100 : ℚ), (7 / 50 : ℚ), (53 / 1600 : ℚ), (27 / 200 : ℚ), (1, 15), (1, 23), (1, 19), (0, 10), [(1, 14), (1, 15)], [(1, 22), (1, 23)], [(1, 18), (1, 19), (1, 20)], [(0, 9), (0, 10)]⟩

theorem g082_ok : tagOKF CompactData.T CompactData.F g082 = true := by decide +kernel

def g083 : Tag := .inr ⟨(27 / 800 : ℚ), (7 / 200 : ℚ), (13 / 100 : ℚ), (7 / 50 : ℚ), (11 / 320 : ℚ), (27 / 200 : ℚ), (1, 15), (1, 23), (1, 19), (0, 11), [(1, 14), (1, 15)], [(1, 22), (1, 23), (2, 0)], [(1, 19), (1, 20)], [(0, 10), (0, 11)]⟩

theorem g083_ok : tagOKF CompactData.T CompactData.F g083 = true := by decide +kernel

def g084 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (7 / 50 : ℚ), (3 / 20 : ℚ), (49 / 1600 : ℚ), (29 / 200 : ℚ), (1, 16), (1, 23), (1, 20), (0, 8), [(1, 15), (1, 16), (1, 17)], [(1, 23), (2, 0)], [(1, 19), (1, 20), (1, 21)], [(0, 8), (0, 9)]⟩

theorem g084_ok : tagOKF CompactData.T CompactData.F g084 = true := by decide +kernel

def g085 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (7 / 50 : ℚ), (3 / 20 : ℚ), (51 / 1600 : ℚ), (29 / 200 : ℚ), (1, 16), (2, 0), (1, 20), (0, 9), [(1, 15), (1, 16), (1, 17)], [(1, 23), (2, 0)], [(1, 20), (1, 21)], [(0, 9)]⟩

theorem g085_ok : tagOKF CompactData.T CompactData.F g085 = true := by decide +kernel

def g086 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (3 / 20 : ℚ), (4 / 25 : ℚ), (49 / 1600 : ℚ), (31 / 200 : ℚ), (1, 17), (2, 0), (1, 21), (0, 8), [(1, 17), (1, 18)], [(2, 0), (2, 1)], [(1, 21), (1, 22)], [(0, 8), (0, 9)]⟩

theorem g086_ok : tagOKF CompactData.T CompactData.F g086 = true := by decide +kernel

def g087 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (3 / 20 : ℚ), (4 / 25 : ℚ), (51 / 1600 : ℚ), (31 / 200 : ℚ), (1, 17), (2, 1), (1, 21), (0, 9), [(1, 17), (1, 18)], [(2, 0), (2, 1)], [(1, 21), (1, 22)], [(0, 9)]⟩

theorem g087_ok : tagOKF CompactData.T CompactData.F g087 = true := by decide +kernel

def g088 : Tag := .inr ⟨(13 / 400 : ℚ), (27 / 800 : ℚ), (7 / 50 : ℚ), (3 / 20 : ℚ), (53 / 1600 : ℚ), (29 / 200 : ℚ), (1, 16), (2, 0), (1, 20), (0, 10), [(1, 15), (1, 16), (1, 17)], [(1, 23), (2, 0)], [(1, 20), (1, 21)], [(0, 9), (0, 10)]⟩

theorem g088_ok : tagOKF CompactData.T CompactData.F g088 = true := by decide +kernel

def g089 : Tag := .inr ⟨(27 / 800 : ℚ), (7 / 200 : ℚ), (7 / 50 : ℚ), (3 / 20 : ℚ), (11 / 320 : ℚ), (29 / 200 : ℚ), (1, 16), (2, 0), (1, 20), (0, 11), [(1, 15), (1, 16), (1, 17)], [(1, 23), (2, 0), (2, 1)], [(1, 20), (1, 21)], [(0, 10), (0, 11)]⟩

theorem g089_ok : tagOKF CompactData.T CompactData.F g089 = true := by decide +kernel

def g090 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (3 / 20 : ℚ), (4 / 25 : ℚ), (27 / 800 : ℚ), (31 / 200 : ℚ), (1, 17), (2, 1), (1, 22), (0, 10), [(1, 17), (1, 18)], [(2, 0), (2, 1), (2, 2)], [(1, 21), (1, 22)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g090_ok : tagOKF CompactData.T CompactData.F g090 = true := by decide +kernel

def g091 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (3 / 25 : ℚ), (1 / 8 : ℚ), (29 / 800 : ℚ), (49 / 400 : ℚ), (1, 13), (1, 22), (1, 18), (0, 12), [(1, 12), (1, 13)], [(1, 22), (1, 23)], [(1, 17), (1, 18)], [(0, 11), (0, 12)]⟩

theorem g091_ok : tagOKF CompactData.T CompactData.F g091 = true := by decide +kernel

def g092 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (1 / 8 : ℚ), (13 / 100 : ℚ), (29 / 800 : ℚ), (51 / 400 : ℚ), (1, 13), (1, 23), (1, 19), (0, 12), [(1, 13), (1, 14)], [(1, 22), (1, 23)], [(1, 18), (1, 19)], [(0, 11), (0, 12)]⟩

theorem g092_ok : tagOKF CompactData.T CompactData.F g092 = true := by decide +kernel

def g093 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (3 / 25 : ℚ), (1 / 8 : ℚ), (31 / 800 : ℚ), (49 / 400 : ℚ), (1, 13), (1, 23), (1, 18), (0, 13), [(1, 12), (1, 13)], [(1, 22), (1, 23)], [(1, 18), (1, 19)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g093_ok : tagOKF CompactData.T CompactData.F g093 = true := by decide +kernel

def g094 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (1 / 8 : ℚ), (13 / 100 : ℚ), (31 / 800 : ℚ), (51 / 400 : ℚ), (1, 13), (1, 23), (1, 19), (0, 13), [(1, 13), (1, 14)], [(1, 23), (2, 0)], [(1, 18), (1, 19)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g094_ok : tagOKF CompactData.T CompactData.F g094 = true := by decide +kernel

def g095 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (13 / 100 : ℚ), (27 / 200 : ℚ), (29 / 800 : ℚ), (53 / 400 : ℚ), (1, 14), (1, 23), (1, 19), (0, 12), [(1, 14), (1, 15)], [(1, 23), (2, 0)], [(1, 19), (1, 20)], [(0, 11), (0, 12)]⟩

theorem g095_ok : tagOKF CompactData.T CompactData.F g095 = true := by decide +kernel

def g096 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (27 / 200 : ℚ), (7 / 50 : ℚ), (29 / 800 : ℚ), (11 / 80 : ℚ), (1, 15), (2, 0), (1, 20), (0, 12), [(1, 15)], [(1, 23), (2, 0)], [(1, 19), (1, 20)], [(0, 11), (0, 12)]⟩

theorem g096_ok : tagOKF CompactData.T CompactData.F g096 = true := by decide +kernel

def g097 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (13 / 100 : ℚ), (7 / 50 : ℚ), (31 / 800 : ℚ), (27 / 200 : ℚ), (1, 15), (2, 0), (1, 20), (0, 13), [(1, 14), (1, 15)], [(1, 23), (2, 0), (2, 1)], [(1, 19), (1, 20), (1, 21)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g097_ok : tagOKF CompactData.T CompactData.F g097 = true := by decide +kernel

def g098 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (7 / 50 : ℚ), (3 / 20 : ℚ), (29 / 800 : ℚ), (29 / 200 : ℚ), (1, 16), (2, 0), (1, 21), (0, 12), [(1, 15), (1, 16), (1, 17)], [(2, 0), (2, 1)], [(1, 20), (1, 21)], [(0, 11), (0, 12)]⟩

theorem g098_ok : tagOKF CompactData.T CompactData.F g098 = true := by decide +kernel

def g099 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (3 / 20 : ℚ), (4 / 25 : ℚ), (29 / 800 : ℚ), (31 / 200 : ℚ), (1, 17), (2, 1), (1, 22), (0, 12), [(1, 17), (1, 18)], [(2, 1), (2, 2)], [(1, 21), (1, 22)], [(0, 11), (0, 12)]⟩

theorem g099_ok : tagOKF CompactData.T CompactData.F g099 = true := by decide +kernel

def g100 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (7 / 50 : ℚ), (3 / 20 : ℚ), (31 / 800 : ℚ), (29 / 200 : ℚ), (1, 16), (2, 1), (1, 21), (0, 13), [(1, 15), (1, 16), (1, 17)], [(2, 0), (2, 1), (2, 2)], [(1, 20), (1, 21), (1, 22)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g100_ok : tagOKF CompactData.T CompactData.F g100 = true := by decide +kernel

def g101 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (3 / 20 : ℚ), (4 / 25 : ℚ), (31 / 800 : ℚ), (31 / 200 : ℚ), (1, 17), (2, 2), (1, 22), (0, 13), [(1, 17), (1, 18)], [(2, 1), (2, 2)], [(1, 21), (1, 22), (1, 23)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g101_ok : tagOKF CompactData.T CompactData.F g101 = true := by decide +kernel

def g102 : Tag := .inr ⟨(1 / 50 : ℚ), (33 / 1600 : ℚ), (4 / 25 : ℚ), (17 / 100 : ℚ), (13 / 640 : ℚ), (33 / 200 : ℚ), (1, 19), (1, 23), (1, 21), (0, 0), [(1, 18), (1, 19)], [(1, 23), (2, 0)], [(1, 21), (1, 22)], [(0, 0)]⟩

theorem g102_ok : tagOKF CompactData.T CompactData.F g102 = true := by decide +kernel

def g103 : Tag := .inr ⟨(33 / 1600 : ℚ), (17 / 800 : ℚ), (4 / 25 : ℚ), (17 / 100 : ℚ), (67 / 3200 : ℚ), (33 / 200 : ℚ), (1, 19), (1, 23), (1, 21), (0, 0), [(1, 18), (1, 19)], [(1, 23), (2, 0)], [(1, 21), (1, 22)], [(0, 0), (0, 1)]⟩

theorem g103_ok : tagOKF CompactData.T CompactData.F g103 = true := by decide +kernel

def g104 : Tag := .inr ⟨(1 / 50 : ℚ), (33 / 1600 : ℚ), (17 / 100 : ℚ), (9 / 50 : ℚ), (13 / 640 : ℚ), (7 / 40 : ℚ), (1, 20), (2, 0), (1, 22), (0, 0), [(1, 19), (1, 20), (1, 21)], [(2, 0), (2, 1)], [(1, 22), (1, 23)], [(0, 0)]⟩

theorem g104_ok : tagOKF CompactData.T CompactData.F g104 = true := by decide +kernel

def g105 : Tag := .inr ⟨(33 / 1600 : ℚ), (17 / 800 : ℚ), (17 / 100 : ℚ), (9 / 50 : ℚ), (67 / 3200 : ℚ), (7 / 40 : ℚ), (1, 20), (2, 0), (1, 22), (0, 0), [(1, 19), (1, 20), (1, 21)], [(2, 0), (2, 1)], [(1, 22), (1, 23)], [(0, 0), (0, 1)]⟩

theorem g105_ok : tagOKF CompactData.T CompactData.F g105 = true := by decide +kernel

def g106 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (4 / 25 : ℚ), (33 / 200 : ℚ), (7 / 320 : ℚ), (13 / 80 : ℚ), (1, 18), (1, 23), (1, 21), (0, 1), [(1, 18), (1, 19)], [(1, 23), (2, 0)], [(1, 21)], [(0, 1), (0, 2)]⟩

theorem g106_ok : tagOKF CompactData.T CompactData.F g106 = true := by decide +kernel

def g107 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (33 / 200 : ℚ), (17 / 100 : ℚ), (7 / 320 : ℚ), (67 / 400 : ℚ), (1, 19), (2, 0), (1, 22), (0, 1), [(1, 19)], [(1, 23), (2, 0)], [(1, 21), (1, 22)], [(0, 1), (0, 2)]⟩

theorem g107_ok : tagOKF CompactData.T CompactData.F g107 = true := by decide +kernel

def g108 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (17 / 100 : ℚ), (9 / 50 : ℚ), (7 / 320 : ℚ), (7 / 40 : ℚ), (1, 20), (2, 1), (1, 22), (0, 1), [(1, 19), (1, 20), (1, 21)], [(2, 0), (2, 1)], [(1, 22), (1, 23)], [(0, 1), (0, 2)]⟩

theorem g108_ok : tagOKF CompactData.T CompactData.F g108 = true := by decide +kernel

def g109 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (9 / 50 : ℚ), (19 / 100 : ℚ), (33 / 1600 : ℚ), (37 / 200 : ℚ), (1, 21), (2, 1), (1, 23), (0, 0), [(1, 21), (1, 22)], [(2, 1), (2, 2)], [(1, 23), (2, 0)], [(0, 0), (0, 1)]⟩

theorem g109_ok : tagOKF CompactData.T CompactData.F g109 = true := by decide +kernel

def g110 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (19 / 100 : ℚ), (1 / 5 : ℚ), (33 / 1600 : ℚ), (39 / 200 : ℚ), (1, 22), (2, 2), (2, 0), (0, 0), [(1, 22), (1, 23)], [(2, 2), (2, 3)], [(2, 0), (2, 1)], [(0, 0), (0, 1)]⟩

theorem g110_ok : tagOKF CompactData.T CompactData.F g110 = true := by decide +kernel

def g111 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (9 / 50 : ℚ), (19 / 100 : ℚ), (7 / 320 : ℚ), (37 / 200 : ℚ), (1, 21), (2, 1), (1, 23), (0, 1), [(1, 21), (1, 22)], [(2, 1), (2, 2)], [(1, 23), (2, 0)], [(0, 1), (0, 2)]⟩

theorem g111_ok : tagOKF CompactData.T CompactData.F g111 = true := by decide +kernel

def g112 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (19 / 100 : ℚ), (1 / 5 : ℚ), (7 / 320 : ℚ), (39 / 200 : ℚ), (1, 22), (2, 2), (2, 0), (0, 1), [(1, 22), (1, 23)], [(2, 2), (2, 3)], [(2, 0), (2, 1)], [(0, 1), (0, 2)]⟩

theorem g112_ok : tagOKF CompactData.T CompactData.F g112 = true := by decide +kernel

def g113 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (4 / 25 : ℚ), (17 / 100 : ℚ), (37 / 1600 : ℚ), (33 / 200 : ℚ), (1, 19), (2, 0), (1, 21), (0, 2), [(1, 18), (1, 19)], [(1, 23), (2, 0)], [(1, 21), (1, 22)], [(0, 2), (0, 3)]⟩

theorem g113_ok : tagOKF CompactData.T CompactData.F g113 = true := by decide +kernel

def g114 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (4 / 25 : ℚ), (17 / 100 : ℚ), (39 / 1600 : ℚ), (33 / 200 : ℚ), (1, 19), (2, 0), (1, 22), (0, 4), [(1, 18), (1, 19)], [(1, 23), (2, 0), (2, 1)], [(1, 21), (1, 22)], [(0, 3), (0, 4)]⟩

theorem g114_ok : tagOKF CompactData.T CompactData.F g114 = true := by decide +kernel

def g115 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (17 / 100 : ℚ), (9 / 50 : ℚ), (37 / 1600 : ℚ), (7 / 40 : ℚ), (1, 20), (2, 1), (1, 23), (0, 2), [(1, 19), (1, 20), (1, 21)], [(2, 0), (2, 1)], [(1, 22), (1, 23)], [(0, 2), (0, 3)]⟩

theorem g115_ok : tagOKF CompactData.T CompactData.F g115 = true := by decide +kernel

def g116 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (17 / 100 : ℚ), (9 / 50 : ℚ), (39 / 1600 : ℚ), (7 / 40 : ℚ), (1, 20), (2, 1), (1, 23), (0, 4), [(1, 19), (1, 20), (1, 21)], [(2, 0), (2, 1), (2, 2)], [(1, 22), (1, 23)], [(0, 3), (0, 4)]⟩

theorem g116_ok : tagOKF CompactData.T CompactData.F g116 = true := by decide +kernel

def g117 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (9 / 50 : ℚ), (19 / 100 : ℚ), (37 / 1600 : ℚ), (37 / 200 : ℚ), (1, 21), (2, 2), (2, 0), (0, 2), [(1, 21), (1, 22)], [(2, 1), (2, 2)], [(1, 23), (2, 0)], [(0, 2), (0, 3)]⟩

theorem g117_ok : tagOKF CompactData.T CompactData.F g117 = true := by decide +kernel

def g118 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (19 / 100 : ℚ), (1 / 5 : ℚ), (37 / 1600 : ℚ), (39 / 200 : ℚ), (1, 22), (2, 3), (2, 0), (0, 2), [(1, 22), (1, 23)], [(2, 2), (2, 3)], [(2, 0), (2, 1)], [(0, 2), (0, 3)]⟩

theorem g118_ok : tagOKF CompactData.T CompactData.F g118 = true := by decide +kernel

def g119 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (9 / 50 : ℚ), (19 / 100 : ℚ), (39 / 1600 : ℚ), (37 / 200 : ℚ), (1, 21), (2, 2), (2, 0), (0, 4), [(1, 21), (1, 22)], [(2, 1), (2, 2)], [(1, 23), (2, 0)], [(0, 3), (0, 4)]⟩

theorem g119_ok : tagOKF CompactData.T CompactData.F g119 = true := by decide +kernel

def tags : List Tag := [g000, g001, g002, g003, g004, g005, g006, g007, g008, g009, g010, g011, g012, g013, g014, g015, g016, g017, g018, g019, g020, g021, g022, g023, g024, g025, g026, g027, g028, g029, g030, g031, g032, g033, g034, g035, g036, g037, g038, g039, g040, g041, g042, g043, g044, g045, g046, g047, g048, g049, g050, g051, g052, g053, g054, g055, g056, g057, g058, g059, g060, g061, g062, g063, g064, g065, g066, g067, g068, g069, g070, g071, g072, g073, g074, g075, g076, g077, g078, g079, g080, g081, g082, g083, g084, g085, g086, g087, g088, g089, g090, g091, g092, g093, g094, g095, g096, g097, g098, g099, g100, g101, g102, g103, g104, g105, g106, g107, g108, g109, g110, g111, g112, g113, g114, g115, g116, g117, g118, g119]

theorem tags_ok : tags.all (tagOKF CompactData.T CompactData.F) = true := by
  simp only [tags, List.all_cons, List.all_nil, g000_ok, g001_ok, g002_ok, g003_ok, g004_ok, g005_ok, g006_ok, g007_ok, g008_ok, g009_ok, g010_ok, g011_ok, g012_ok, g013_ok, g014_ok, g015_ok, g016_ok, g017_ok, g018_ok, g019_ok, g020_ok, g021_ok, g022_ok, g023_ok, g024_ok, g025_ok, g026_ok, g027_ok, g028_ok, g029_ok, g030_ok, g031_ok, g032_ok, g033_ok, g034_ok, g035_ok, g036_ok, g037_ok, g038_ok, g039_ok, g040_ok, g041_ok, g042_ok, g043_ok, g044_ok, g045_ok, g046_ok, g047_ok, g048_ok, g049_ok, g050_ok, g051_ok, g052_ok, g053_ok, g054_ok, g055_ok, g056_ok, g057_ok, g058_ok, g059_ok, g060_ok, g061_ok, g062_ok, g063_ok, g064_ok, g065_ok, g066_ok, g067_ok, g068_ok, g069_ok, g070_ok, g071_ok, g072_ok, g073_ok, g074_ok, g075_ok, g076_ok, g077_ok, g078_ok, g079_ok, g080_ok, g081_ok, g082_ok, g083_ok, g084_ok, g085_ok, g086_ok, g087_ok, g088_ok, g089_ok, g090_ok, g091_ok, g092_ok, g093_ok, g094_ok, g095_ok, g096_ok, g097_ok, g098_ok, g099_ok, g100_ok, g101_ok, g102_ok, g103_ok, g104_ok, g105_ok, g106_ok, g107_ok, g108_ok, g109_ok, g110_ok, g111_ok, g112_ok, g113_ok, g114_ok, g115_ok, g116_ok, g117_ok, g118_ok, g119_ok, Bool.and_self]

end CKLaneC3.CompactBatch02


