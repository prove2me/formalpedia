-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch22_q01
-- name    : CK_CKLaneC3_CompactBatch22_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T03:49:50.160171+00:00
-- url     : https://prove2.me/theorems/f47c2266-7009-4984-af69-7762667760bf
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch22 (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch22 (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch22 (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch22 (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch22 (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneC3_CompactBatch22_q00

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace CKLaneC3.CompactBatch22
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF
def g040 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (13 / 25 : ℚ), (14 / 25 : ℚ), (33 / 800 : ℚ), (27 / 50 : ℚ), (2, 20), (3, 0), (2, 22), (0, 14), [(2, 19), (2, 20), (2, 21)], [(2, 23), (3, 0), (3, 1)], [(2, 21), (2, 22), (2, 23)], [(0, 14), (0, 15)]⟩

theorem g040_ok : tagOKF CompactData.T CompactData.F g040 = true := by decide +kernel

def g041 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (13 / 25 : ℚ), (14 / 25 : ℚ), (7 / 160 : ℚ), (27 / 50 : ℚ), (2, 20), (3, 0), (2, 22), (0, 16), [(2, 19), (2, 20), (2, 21)], [(2, 23), (3, 0), (3, 1)], [(2, 21), (2, 22), (2, 23)], [(0, 15), (0, 16)]⟩

theorem g041_ok : tagOKF CompactData.T CompactData.F g041 = true := by decide +kernel

def g042 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (12 / 25 : ℚ), (13 / 25 : ℚ), (37 / 800 : ℚ), (1 / 2 : ℚ), (2, 18), (2, 23), (2, 20), (0, 17), [(2, 17), (2, 18), (2, 19)], [(2, 21), (2, 22), (2, 23), (3, 0)], [(2, 19), (2, 20), (2, 21)], [(0, 16), (0, 17)]⟩

theorem g042_ok : tagOKF CompactData.T CompactData.F g042 = true := by decide +kernel

def g043 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (12 / 25 : ℚ), (13 / 25 : ℚ), (39 / 800 : ℚ), (1 / 2 : ℚ), (2, 18), (2, 23), (2, 20), (0, 18), [(2, 17), (2, 18), (2, 19)], [(2, 22), (2, 23), (3, 0)], [(2, 19), (2, 20), (2, 21)], [(0, 17), (0, 18)]⟩

theorem g043_ok : tagOKF CompactData.T CompactData.F g043 = true := by decide +kernel

def g044 : Tag := .inr ⟨(9 / 200 : ℚ), (1 / 20 : ℚ), (13 / 25 : ℚ), (14 / 25 : ℚ), (19 / 400 : ℚ), (27 / 50 : ℚ), (2, 20), (3, 1), (2, 22), (0, 17), [(2, 19), (2, 20), (2, 21)], [(2, 23), (3, 0), (3, 1), (3, 2)], [(2, 21), (2, 22), (2, 23)], [(0, 16), (0, 17), (0, 18)]⟩

theorem g044_ok : tagOKF CompactData.T CompactData.F g044 = true := by decide +kernel

def g045 : Tag := .inr ⟨(1 / 25 : ℚ), (9 / 200 : ℚ), (14 / 25 : ℚ), (3 / 5 : ℚ), (17 / 400 : ℚ), (29 / 50 : ℚ), (2, 22), (3, 2), (3, 0), (0, 15), [(2, 21), (2, 22), (2, 23)], [(3, 1), (3, 2), (3, 3)], [(2, 23), (3, 0), (3, 1)], [(0, 14), (0, 15), (0, 16)]⟩

theorem g045_ok : tagOKF CompactData.T CompactData.F g045 = true := by decide +kernel

def g046 : Tag := .inr ⟨(1 / 25 : ℚ), (9 / 200 : ℚ), (3 / 5 : ℚ), (16 / 25 : ℚ), (17 / 400 : ℚ), (31 / 50 : ℚ), (3, 0), (3, 4), (3, 2), (0, 15), [(2, 23), (3, 0), (3, 1)], [(3, 3), (3, 4), (3, 5)], [(3, 1), (3, 2), (3, 3)], [(0, 14), (0, 15), (0, 16)]⟩

theorem g046_ok : tagOKF CompactData.T CompactData.F g046 = true := by decide +kernel

def g047 : Tag := .inr ⟨(9 / 200 : ℚ), (1 / 20 : ℚ), (14 / 25 : ℚ), (3 / 5 : ℚ), (19 / 400 : ℚ), (29 / 50 : ℚ), (2, 22), (3, 3), (3, 0), (0, 17), [(2, 21), (2, 22), (2, 23)], [(3, 1), (3, 2), (3, 3), (3, 4)], [(2, 23), (3, 0), (3, 1)], [(0, 16), (0, 17), (0, 18)]⟩

theorem g047_ok : tagOKF CompactData.T CompactData.F g047 = true := by decide +kernel

def g048 : Tag := .inr ⟨(9 / 200 : ℚ), (1 / 20 : ℚ), (3 / 5 : ℚ), (16 / 25 : ℚ), (19 / 400 : ℚ), (31 / 50 : ℚ), (3, 0), (3, 5), (3, 2), (0, 17), [(2, 23), (3, 0), (3, 1)], [(3, 3), (3, 4), (3, 5), (3, 6)], [(3, 1), (3, 2), (3, 3)], [(0, 16), (0, 17), (0, 18)]⟩

theorem g048_ok : tagOKF CompactData.T CompactData.F g048 = true := by decide +kernel

def g049 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (12 / 25 : ℚ), (13 / 25 : ℚ), (21 / 400 : ℚ), (1 / 2 : ℚ), (2, 18), (2, 23), (2, 21), (0, 19), [(2, 17), (2, 18), (2, 19)], [(2, 22), (2, 23), (3, 0)], [(2, 19), (2, 20), (2, 21), (2, 22)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g049_ok : tagOKF CompactData.T CompactData.F g049 = true := by decide +kernel

def g050 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (13 / 25 : ℚ), (14 / 25 : ℚ), (21 / 400 : ℚ), (27 / 50 : ℚ), (2, 20), (3, 1), (2, 23), (0, 19), [(2, 19), (2, 20), (2, 21)], [(3, 0), (3, 1), (3, 2)], [(2, 21), (2, 22), (2, 23), (3, 0)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g050_ok : tagOKF CompactData.T CompactData.F g050 = true := by decide +kernel

def g051 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (12 / 25 : ℚ), (13 / 25 : ℚ), (23 / 400 : ℚ), (1 / 2 : ℚ), (2, 18), (3, 0), (2, 21), (0, 21), [(2, 17), (2, 18), (2, 19)], [(2, 22), (2, 23), (3, 0), (3, 1)], [(2, 20), (2, 21), (2, 22)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g051_ok : tagOKF CompactData.T CompactData.F g051 = true := by decide +kernel

def g052 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (13 / 25 : ℚ), (14 / 25 : ℚ), (23 / 400 : ℚ), (27 / 50 : ℚ), (2, 20), (3, 2), (2, 23), (0, 21), [(2, 19), (2, 20), (2, 21)], [(3, 0), (3, 1), (3, 2), (3, 3)], [(2, 22), (2, 23), (3, 0)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g052_ok : tagOKF CompactData.T CompactData.F g052 = true := by decide +kernel

def g053 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (14 / 25 : ℚ), (3 / 5 : ℚ), (21 / 400 : ℚ), (29 / 50 : ℚ), (2, 22), (3, 3), (3, 1), (0, 19), [(2, 21), (2, 22), (2, 23)], [(3, 2), (3, 3), (3, 4)], [(2, 23), (3, 0), (3, 1), (3, 2)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g053_ok : tagOKF CompactData.T CompactData.F g053 = true := by decide +kernel

def g054 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (3 / 5 : ℚ), (16 / 25 : ℚ), (21 / 400 : ℚ), (31 / 50 : ℚ), (3, 0), (3, 5), (3, 3), (0, 19), [(2, 23), (3, 0), (3, 1)], [(3, 4), (3, 5), (3, 6)], [(3, 1), (3, 2), (3, 3), (3, 4)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g054_ok : tagOKF CompactData.T CompactData.F g054 = true := by decide +kernel

def g055 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (14 / 25 : ℚ), (3 / 5 : ℚ), (23 / 400 : ℚ), (29 / 50 : ℚ), (2, 22), (3, 4), (3, 1), (0, 21), [(2, 21), (2, 22), (2, 23)], [(3, 2), (3, 3), (3, 4), (3, 5)], [(3, 0), (3, 1), (3, 2)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g055_ok : tagOKF CompactData.T CompactData.F g055 = true := by decide +kernel

def g056 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (3 / 5 : ℚ), (16 / 25 : ℚ), (23 / 400 : ℚ), (31 / 50 : ℚ), (3, 0), (3, 6), (3, 3), (0, 21), [(2, 23), (3, 0), (3, 1)], [(3, 4), (3, 5), (3, 6), (3, 7)], [(3, 2), (3, 3), (3, 4)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g056_ok : tagOKF CompactData.T CompactData.F g056 = true := by decide +kernel

def g057 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (8 / 25 : ℚ), (17 / 50 : ℚ), (1 / 16 : ℚ), (33 / 100 : ℚ), (2, 9), (2, 16), (2, 13), (0, 23), [(2, 8), (2, 9), (2, 10)], [(2, 15), (2, 16)], [(2, 12), (2, 13)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g057_ok : tagOKF CompactData.T CompactData.F g057 = true := by decide +kernel

def g058 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (17 / 50 : ℚ), (9 / 25 : ℚ), (1 / 16 : ℚ), (7 / 20 : ℚ), (2, 10), (2, 17), (2, 14), (0, 23), [(2, 10), (2, 11)], [(2, 16), (2, 17)], [(2, 13), (2, 14)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g058_ok : tagOKF CompactData.T CompactData.F g058 = true := by decide +kernel

def g059 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (8 / 25 : ℚ), (17 / 50 : ℚ), (27 / 400 : ℚ), (33 / 100 : ℚ), (2, 9), (2, 16), (2, 13), (1, 0), [(2, 8), (2, 9), (2, 10)], [(2, 15), (2, 16), (2, 17)], [(2, 12), (2, 13)], [(1, 0), (1, 1)]⟩

theorem g059_ok : tagOKF CompactData.T CompactData.F g059 = true := by decide +kernel

def g060 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (17 / 50 : ℚ), (9 / 25 : ℚ), (27 / 400 : ℚ), (7 / 20 : ℚ), (2, 10), (2, 17), (2, 14), (1, 0), [(2, 10), (2, 11)], [(2, 16), (2, 17), (2, 18)], [(2, 13), (2, 14)], [(1, 0), (1, 1)]⟩

theorem g060_ok : tagOKF CompactData.T CompactData.F g060 = true := by decide +kernel

def g061 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (9 / 25 : ℚ), (19 / 50 : ℚ), (1 / 16 : ℚ), (37 / 100 : ℚ), (2, 11), (2, 18), (2, 15), (0, 23), [(2, 11), (2, 12)], [(2, 17), (2, 18)], [(2, 14), (2, 15)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g061_ok : tagOKF CompactData.T CompactData.F g061 = true := by decide +kernel

def g062 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (19 / 50 : ℚ), (2 / 5 : ℚ), (1 / 16 : ℚ), (39 / 100 : ℚ), (2, 12), (2, 19), (2, 16), (0, 23), [(2, 12), (2, 13)], [(2, 18), (2, 19)], [(2, 15), (2, 16)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g062_ok : tagOKF CompactData.T CompactData.F g062 = true := by decide +kernel

def g063 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (9 / 25 : ℚ), (19 / 50 : ℚ), (27 / 400 : ℚ), (37 / 100 : ℚ), (2, 11), (2, 18), (2, 15), (1, 0), [(2, 11), (2, 12)], [(2, 17), (2, 18), (2, 19)], [(2, 14), (2, 15)], [(1, 0), (1, 1)]⟩

theorem g063_ok : tagOKF CompactData.T CompactData.F g063 = true := by decide +kernel

def g064 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (19 / 50 : ℚ), (2 / 5 : ℚ), (27 / 400 : ℚ), (39 / 100 : ℚ), (2, 12), (2, 19), (2, 16), (1, 0), [(2, 12), (2, 13)], [(2, 18), (2, 19), (2, 20)], [(2, 15), (2, 16)], [(1, 0), (1, 1)]⟩

theorem g064_ok : tagOKF CompactData.T CompactData.F g064 = true := by decide +kernel

def g065 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (8 / 25 : ℚ), (17 / 50 : ℚ), (29 / 400 : ℚ), (33 / 100 : ℚ), (2, 9), (2, 17), (2, 13), (1, 2), [(2, 8), (2, 9), (2, 10)], [(2, 16), (2, 17)], [(2, 12), (2, 13), (2, 14)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g065_ok : tagOKF CompactData.T CompactData.F g065 = true := by decide +kernel

def g066 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (17 / 50 : ℚ), (9 / 25 : ℚ), (29 / 400 : ℚ), (7 / 20 : ℚ), (2, 10), (2, 18), (2, 14), (1, 2), [(2, 10), (2, 11)], [(2, 17), (2, 18)], [(2, 13), (2, 14), (2, 15)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g066_ok : tagOKF CompactData.T CompactData.F g066 = true := by decide +kernel

def g067 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (8 / 25 : ℚ), (17 / 50 : ℚ), (31 / 400 : ℚ), (33 / 100 : ℚ), (2, 9), (2, 17), (2, 13), (1, 3), [(2, 8), (2, 9), (2, 10)], [(2, 16), (2, 17), (2, 18)], [(2, 13), (2, 14)], [(1, 3), (1, 4)]⟩

theorem g067_ok : tagOKF CompactData.T CompactData.F g067 = true := by decide +kernel

def g068 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (17 / 50 : ℚ), (9 / 25 : ℚ), (31 / 400 : ℚ), (7 / 20 : ℚ), (2, 10), (2, 18), (2, 14), (1, 3), [(2, 10), (2, 11)], [(2, 17), (2, 18), (2, 19)], [(2, 14), (2, 15)], [(1, 3), (1, 4)]⟩

theorem g068_ok : tagOKF CompactData.T CompactData.F g068 = true := by decide +kernel

def g069 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (9 / 25 : ℚ), (2 / 5 : ℚ), (29 / 400 : ℚ), (19 / 50 : ℚ), (2, 12), (2, 19), (2, 16), (1, 2), [(2, 11), (2, 12), (2, 13)], [(2, 18), (2, 19), (2, 20)], [(2, 14), (2, 15), (2, 16), (2, 17)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g069_ok : tagOKF CompactData.T CompactData.F g069 = true := by decide +kernel

def g070 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (9 / 25 : ℚ), (2 / 5 : ℚ), (31 / 400 : ℚ), (19 / 50 : ℚ), (2, 12), (2, 20), (2, 16), (1, 3), [(2, 11), (2, 12), (2, 13)], [(2, 18), (2, 19), (2, 20), (2, 21)], [(2, 15), (2, 16), (2, 17)], [(1, 3), (1, 4)]⟩

theorem g070_ok : tagOKF CompactData.T CompactData.F g070 = true := by decide +kernel

def g071 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (2 / 5 : ℚ), (11 / 25 : ℚ), (1 / 16 : ℚ), (21 / 50 : ℚ), (2, 14), (2, 20), (2, 17), (0, 23), [(2, 13), (2, 14), (2, 15)], [(2, 19), (2, 20), (2, 21)], [(2, 16), (2, 17), (2, 18)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g071_ok : tagOKF CompactData.T CompactData.F g071 = true := by decide +kernel

def g072 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (2 / 5 : ℚ), (11 / 25 : ℚ), (27 / 400 : ℚ), (21 / 50 : ℚ), (2, 14), (2, 21), (2, 17), (1, 0), [(2, 13), (2, 14), (2, 15)], [(2, 19), (2, 20), (2, 21), (2, 22)], [(2, 16), (2, 17), (2, 18)], [(1, 0), (1, 1)]⟩

theorem g072_ok : tagOKF CompactData.T CompactData.F g072 = true := by decide +kernel

def g073 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (11 / 25 : ℚ), (12 / 25 : ℚ), (1 / 16 : ℚ), (23 / 50 : ℚ), (2, 16), (2, 22), (2, 19), (0, 23), [(2, 15), (2, 16), (2, 17)], [(2, 21), (2, 22), (2, 23)], [(2, 18), (2, 19), (2, 20)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g073_ok : tagOKF CompactData.T CompactData.F g073 = true := by decide +kernel

def g074 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (11 / 25 : ℚ), (12 / 25 : ℚ), (27 / 400 : ℚ), (23 / 50 : ℚ), (2, 16), (2, 23), (2, 19), (1, 0), [(2, 15), (2, 16), (2, 17)], [(2, 21), (2, 22), (2, 23), (3, 0)], [(2, 18), (2, 19), (2, 20)], [(1, 0), (1, 1)]⟩

theorem g074_ok : tagOKF CompactData.T CompactData.F g074 = true := by decide +kernel

def g075 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (2 / 5 : ℚ), (11 / 25 : ℚ), (29 / 400 : ℚ), (21 / 50 : ℚ), (2, 14), (2, 21), (2, 18), (1, 2), [(2, 13), (2, 14), (2, 15)], [(2, 20), (2, 21), (2, 22)], [(2, 16), (2, 17), (2, 18), (2, 19)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g075_ok : tagOKF CompactData.T CompactData.F g075 = true := by decide +kernel

def g076 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (2 / 5 : ℚ), (11 / 25 : ℚ), (31 / 400 : ℚ), (21 / 50 : ℚ), (2, 14), (2, 22), (2, 18), (1, 3), [(2, 13), (2, 14), (2, 15)], [(2, 20), (2, 21), (2, 22), (2, 23)], [(2, 17), (2, 18), (2, 19)], [(1, 3), (1, 4)]⟩

theorem g076_ok : tagOKF CompactData.T CompactData.F g076 = true := by decide +kernel

def g077 : Tag := .inr ⟨(7 / 100 : ℚ), (2 / 25 : ℚ), (11 / 25 : ℚ), (12 / 25 : ℚ), (3 / 40 : ℚ), (23 / 50 : ℚ), (2, 16), (2, 23), (2, 20), (1, 3), [(2, 15), (2, 16), (2, 17)], [(2, 22), (2, 23), (3, 0), (3, 1)], [(2, 18), (2, 19), (2, 20), (2, 21)], [(1, 1), (1, 2), (1, 3), (1, 4)]⟩

theorem g077_ok : tagOKF CompactData.T CompactData.F g077 = true := by decide +kernel

def g078 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (12 / 25 : ℚ), (13 / 25 : ℚ), (1 / 16 : ℚ), (1 / 2 : ℚ), (2, 18), (3, 0), (2, 21), (0, 23), [(2, 17), (2, 18), (2, 19)], [(2, 23), (3, 0), (3, 1)], [(2, 20), (2, 21), (2, 22)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g078_ok : tagOKF CompactData.T CompactData.F g078 = true := by decide +kernel

def g079 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (13 / 25 : ℚ), (14 / 25 : ℚ), (1 / 16 : ℚ), (27 / 50 : ℚ), (2, 20), (3, 2), (2, 23), (0, 23), [(2, 19), (2, 20), (2, 21)], [(3, 1), (3, 2), (3, 3)], [(2, 22), (2, 23), (3, 0)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g079_ok : tagOKF CompactData.T CompactData.F g079 = true := by decide +kernel

end CKLaneC3.CompactBatch22


