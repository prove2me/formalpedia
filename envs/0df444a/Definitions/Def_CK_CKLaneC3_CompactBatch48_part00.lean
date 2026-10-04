-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch48_part00
-- name    : CK_CKLaneC3_CompactBatch48_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T05:34:12.028303+00:00
-- url     : https://prove2.me/theorems/77631993-d9ec-41a2-88fc-d542c952a301
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch48 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch48 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch48 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch48 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch48 (part 1 of 2).lean)

import Definitions.Def_CK_CKLaneC3_CompactBatch48_part00_q01

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace CKLaneC3.CompactBatch48
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF
def g063 : Tag := .inr ⟨(17 / 25 : ℚ), (18 / 25 : ℚ), (1 / 40 : ℚ), (11 / 400 : ℚ), (7 / 10 : ℚ), (21 / 800 : ℚ), (0, 5), (4, 16), (3, 5), (3, 4), [(0, 4), (0, 5), (0, 6)], [(4, 14), (4, 15), (4, 16), (4, 17), (4, 18)], [(3, 4), (3, 5), (3, 6)], [(3, 3), (3, 4), (3, 5)]⟩

theorem g063_ok : tagOKF CompactData.T CompactData.F g063 = true := by decide +kernel

def g064 : Tag := .inr ⟨(16 / 25 : ℚ), (17 / 25 : ℚ), (11 / 400 : ℚ), (3 / 100 : ℚ), (33 / 50 : ℚ), (23 / 800 : ℚ), (0, 7), (4, 12), (3, 3), (3, 2), [(0, 6), (0, 7), (0, 8)], [(4, 10), (4, 11), (4, 12), (4, 13), (4, 14)], [(3, 2), (3, 3), (3, 4)], [(3, 1), (3, 2), (3, 3)]⟩

theorem g064_ok : tagOKF CompactData.T CompactData.F g064 = true := by decide +kernel

def g065 : Tag := .inr ⟨(17 / 25 : ℚ), (18 / 25 : ℚ), (11 / 400 : ℚ), (3 / 100 : ℚ), (7 / 10 : ℚ), (23 / 800 : ℚ), (0, 7), (4, 16), (3, 5), (3, 4), [(0, 6), (0, 7), (0, 8)], [(4, 14), (4, 15), (4, 16), (4, 17), (4, 18)], [(3, 4), (3, 5), (3, 6)], [(3, 3), (3, 4), (3, 5)]⟩

theorem g065_ok : tagOKF CompactData.T CompactData.F g065 = true := by decide +kernel

def g066 : Tag := .inr ⟨(18 / 25 : ℚ), (4 / 5 : ℚ), (1 / 40 : ℚ), (11 / 400 : ℚ), (19 / 25 : ℚ), (21 / 800 : ℚ), (0, 5), (4, 22), (3, 8), (3, 7), [(0, 4), (0, 5), (0, 6)], [(4, 18), (4, 19), (4, 20), (4, 21), (4, 22), (4, 23), (5, 0), (5, 1), (5, 2)], [(3, 6), (3, 7), (3, 8), (3, 9), (3, 10)], [(3, 5), (3, 6), (3, 7), (3, 8), (3, 9)]⟩

theorem g066_ok : tagOKF CompactData.T CompactData.F g066 = true := by decide +kernel

def g067 : Tag := .inr ⟨(18 / 25 : ℚ), (4 / 5 : ℚ), (11 / 400 : ℚ), (3 / 100 : ℚ), (19 / 25 : ℚ), (23 / 800 : ℚ), (0, 7), (4, 22), (3, 8), (3, 7), [(0, 6), (0, 7), (0, 8)], [(4, 18), (4, 19), (4, 20), (4, 21), (4, 22), (4, 23), (5, 0), (5, 1), (5, 2)], [(3, 6), (3, 7), (3, 8), (3, 9), (3, 10)], [(3, 5), (3, 6), (3, 7), (3, 8), (3, 9)]⟩

theorem g067_ok : tagOKF CompactData.T CompactData.F g067 = true := by decide +kernel

def g068 : Tag := .inr ⟨(4 / 5 : ℚ), (22 / 25 : ℚ), (1 / 50 : ℚ), (9 / 400 : ℚ), (21 / 25 : ℚ), (17 / 800 : ℚ), (0, 1), (5, 6), (3, 12), (3, 11), [(0, 0), (0, 1), (0, 2)], [(5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10)], [(3, 10), (3, 11), (3, 12), (3, 13), (3, 14)], [(3, 9), (3, 10), (3, 11), (3, 12), (3, 13)]⟩

theorem g068_ok : tagOKF CompactData.T CompactData.F g068 = true := by decide +kernel

def g069 : Tag := .inr ⟨(22 / 25 : ℚ), (24 / 25 : ℚ), (1 / 50 : ℚ), (9 / 400 : ℚ), (23 / 25 : ℚ), (17 / 800 : ℚ), (0, 1), (5, 14), (3, 16), (3, 15), [(0, 0), (0, 1), (0, 2)], [(5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (5, 16), (5, 17), (5, 18)], [(3, 14), (3, 15), (3, 16), (3, 17), (3, 18)], [(3, 13), (3, 14), (3, 15), (3, 16), (3, 17)]⟩

theorem g069_ok : tagOKF CompactData.T CompactData.F g069 = true := by decide +kernel

def g070 : Tag := .inr ⟨(4 / 5 : ℚ), (22 / 25 : ℚ), (9 / 400 : ℚ), (1 / 40 : ℚ), (21 / 25 : ℚ), (19 / 800 : ℚ), (0, 3), (5, 6), (3, 12), (3, 11), [(0, 2), (0, 3), (0, 4)], [(5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10)], [(3, 10), (3, 11), (3, 12), (3, 13), (3, 14)], [(3, 9), (3, 10), (3, 11), (3, 12), (3, 13)]⟩

theorem g070_ok : tagOKF CompactData.T CompactData.F g070 = true := by decide +kernel

def g071 : Tag := .inr ⟨(22 / 25 : ℚ), (24 / 25 : ℚ), (9 / 400 : ℚ), (1 / 40 : ℚ), (23 / 25 : ℚ), (19 / 800 : ℚ), (0, 3), (5, 14), (3, 16), (3, 15), [(0, 2), (0, 3), (0, 4)], [(5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (5, 16), (5, 17), (5, 18)], [(3, 14), (3, 15), (3, 16), (3, 17), (3, 18)], [(3, 13), (3, 14), (3, 15), (3, 16), (3, 17)]⟩

theorem g071_ok : tagOKF CompactData.T CompactData.F g071 = true := by decide +kernel

def g072 : Tag := .inr ⟨(4 / 5 : ℚ), (22 / 25 : ℚ), (1 / 40 : ℚ), (3 / 100 : ℚ), (21 / 25 : ℚ), (11 / 400 : ℚ), (0, 6), (5, 6), (3, 12), (3, 11), [(0, 4), (0, 5), (0, 6), (0, 7), (0, 8)], [(5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10)], [(3, 10), (3, 11), (3, 12), (3, 13), (3, 14)], [(3, 9), (3, 10), (3, 11), (3, 12), (3, 13)]⟩

theorem g072_ok : tagOKF CompactData.T CompactData.F g072 = true := by decide +kernel

def g073 : Tag := .inr ⟨(22 / 25 : ℚ), (24 / 25 : ℚ), (1 / 40 : ℚ), (3 / 100 : ℚ), (23 / 25 : ℚ), (11 / 400 : ℚ), (0, 6), (5, 14), (3, 16), (3, 15), [(0, 4), (0, 5), (0, 6), (0, 7), (0, 8)], [(5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (5, 16), (5, 17), (5, 18)], [(3, 14), (3, 15), (3, 16), (3, 17), (3, 18)], [(3, 13), (3, 14), (3, 15), (3, 16), (3, 17)]⟩

theorem g073_ok : tagOKF CompactData.T CompactData.F g073 = true := by decide +kernel

def g074 : Tag := .inr ⟨(16 / 25 : ℚ), (17 / 25 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (33 / 50 : ℚ), (1 / 32 : ℚ), (0, 9), (4, 12), (3, 3), (3, 2), [(0, 8), (0, 9)], [(4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 15)], [(3, 2), (3, 3), (3, 4), (3, 5)], [(3, 1), (3, 2), (3, 3)]⟩

theorem g074_ok : tagOKF CompactData.T CompactData.F g074 = true := by decide +kernel

def g075 : Tag := .inr ⟨(17 / 25 : ℚ), (18 / 25 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (7 / 10 : ℚ), (1 / 32 : ℚ), (0, 9), (4, 16), (3, 5), (3, 4), [(0, 8), (0, 9)], [(4, 14), (4, 15), (4, 16), (4, 17), (4, 18), (4, 19)], [(3, 4), (3, 5), (3, 6), (3, 7)], [(3, 3), (3, 4), (3, 5)]⟩

theorem g075_ok : tagOKF CompactData.T CompactData.F g075 = true := by decide +kernel

def g076 : Tag := .inr ⟨(16 / 25 : ℚ), (17 / 25 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (33 / 50 : ℚ), (27 / 800 : ℚ), (0, 10), (4, 13), (3, 4), (3, 2), [(0, 9), (0, 10), (0, 11)], [(4, 11), (4, 12), (4, 13), (4, 14), (4, 15)], [(3, 3), (3, 4), (3, 5)], [(3, 1), (3, 2), (3, 3)]⟩

theorem g076_ok : tagOKF CompactData.T CompactData.F g076 = true := by decide +kernel

def g077 : Tag := .inr ⟨(17 / 25 : ℚ), (18 / 25 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (7 / 10 : ℚ), (27 / 800 : ℚ), (0, 10), (4, 17), (3, 6), (3, 4), [(0, 9), (0, 10), (0, 11)], [(4, 15), (4, 16), (4, 17), (4, 18), (4, 19)], [(3, 5), (3, 6), (3, 7)], [(3, 3), (3, 4), (3, 5)]⟩

theorem g077_ok : tagOKF CompactData.T CompactData.F g077 = true := by decide +kernel

def g078 : Tag := .inr ⟨(18 / 25 : ℚ), (4 / 5 : ℚ), (3 / 100 : ℚ), (7 / 200 : ℚ), (19 / 25 : ℚ), (13 / 400 : ℚ), (0, 9), (4, 23), (3, 9), (3, 7), [(0, 8), (0, 9), (0, 10), (0, 11)], [(4, 18), (4, 19), (4, 20), (4, 21), (4, 22), (4, 23), (5, 0), (5, 1), (5, 2), (5, 3)], [(3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11)], [(3, 5), (3, 6), (3, 7), (3, 8), (3, 9)]⟩

theorem g078_ok : tagOKF CompactData.T CompactData.F g078 = true := by decide +kernel

def g079 : Tag := .inr ⟨(16 / 25 : ℚ), (17 / 25 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (33 / 50 : ℚ), (29 / 800 : ℚ), (0, 12), (4, 13), (3, 4), (3, 2), [(0, 11), (0, 12)], [(4, 11), (4, 12), (4, 13), (4, 14), (4, 15)], [(3, 3), (3, 4), (3, 5)], [(3, 1), (3, 2), (3, 3)]⟩

theorem g079_ok : tagOKF CompactData.T CompactData.F g079 = true := by decide +kernel

def g080 : Tag := .inr ⟨(17 / 25 : ℚ), (18 / 25 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (7 / 10 : ℚ), (29 / 800 : ℚ), (0, 12), (4, 17), (3, 6), (3, 4), [(0, 11), (0, 12)], [(4, 15), (4, 16), (4, 17), (4, 18), (4, 19)], [(3, 5), (3, 6), (3, 7)], [(3, 3), (3, 4), (3, 5)]⟩

theorem g080_ok : tagOKF CompactData.T CompactData.F g080 = true := by decide +kernel

def g081 : Tag := .inr ⟨(16 / 25 : ℚ), (17 / 25 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (33 / 50 : ℚ), (31 / 800 : ℚ), (0, 13), (4, 13), (3, 4), (3, 2), [(0, 12), (0, 13), (0, 14)], [(4, 11), (4, 12), (4, 13), (4, 14), (4, 15)], [(3, 3), (3, 4), (3, 5)], [(3, 1), (3, 2), (3, 3)]⟩

theorem g081_ok : tagOKF CompactData.T CompactData.F g081 = true := by decide +kernel

def g082 : Tag := .inr ⟨(17 / 25 : ℚ), (18 / 25 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (7 / 10 : ℚ), (31 / 800 : ℚ), (0, 13), (4, 17), (3, 6), (3, 4), [(0, 12), (0, 13), (0, 14)], [(4, 15), (4, 16), (4, 17), (4, 18), (4, 19)], [(3, 5), (3, 6), (3, 7)], [(3, 3), (3, 4), (3, 5)]⟩

theorem g082_ok : tagOKF CompactData.T CompactData.F g082 = true := by decide +kernel

def g083 : Tag := .inr ⟨(18 / 25 : ℚ), (4 / 5 : ℚ), (7 / 200 : ℚ), (1 / 25 : ℚ), (19 / 25 : ℚ), (3 / 80 : ℚ), (0, 12), (4, 23), (3, 9), (3, 7), [(0, 11), (0, 12), (0, 13), (0, 14)], [(4, 19), (4, 20), (4, 21), (4, 22), (4, 23), (5, 0), (5, 1), (5, 2), (5, 3)], [(3, 7), (3, 8), (3, 9), (3, 10), (3, 11)], [(3, 5), (3, 6), (3, 7), (3, 8), (3, 9)]⟩

theorem g083_ok : tagOKF CompactData.T CompactData.F g083 = true := by decide +kernel

def g084 : Tag := .inr ⟨(4 / 5 : ℚ), (22 / 25 : ℚ), (3 / 100 : ℚ), (7 / 200 : ℚ), (21 / 25 : ℚ), (13 / 400 : ℚ), (0, 9), (5, 7), (3, 13), (3, 11), [(0, 8), (0, 9), (0, 10), (0, 11)], [(5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11)], [(3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15)], [(3, 9), (3, 10), (3, 11), (3, 12), (3, 13)]⟩

theorem g084_ok : tagOKF CompactData.T CompactData.F g084 = true := by decide +kernel

def g085 : Tag := .inr ⟨(22 / 25 : ℚ), (24 / 25 : ℚ), (3 / 100 : ℚ), (7 / 200 : ℚ), (23 / 25 : ℚ), (13 / 400 : ℚ), (0, 9), (5, 15), (3, 17), (3, 15), [(0, 8), (0, 9), (0, 10), (0, 11)], [(5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (5, 16), (5, 17), (5, 18), (5, 19)], [(3, 14), (3, 15), (3, 16), (3, 17), (3, 18), (3, 19)], [(3, 13), (3, 14), (3, 15), (3, 16), (3, 17)]⟩

theorem g085_ok : tagOKF CompactData.T CompactData.F g085 = true := by decide +kernel

def g086 : Tag := .inr ⟨(4 / 5 : ℚ), (22 / 25 : ℚ), (7 / 200 : ℚ), (1 / 25 : ℚ), (21 / 25 : ℚ), (3 / 80 : ℚ), (0, 12), (5, 7), (3, 13), (3, 11), [(0, 11), (0, 12), (0, 13), (0, 14)], [(5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11)], [(3, 11), (3, 12), (3, 13), (3, 14), (3, 15)], [(3, 9), (3, 10), (3, 11), (3, 12), (3, 13)]⟩

theorem g086_ok : tagOKF CompactData.T CompactData.F g086 = true := by decide +kernel

def g087 : Tag := .inr ⟨(22 / 25 : ℚ), (24 / 25 : ℚ), (7 / 200 : ℚ), (1 / 25 : ℚ), (23 / 25 : ℚ), (3 / 80 : ℚ), (0, 12), (5, 15), (3, 17), (3, 15), [(0, 11), (0, 12), (0, 13), (0, 14)], [(5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (5, 16), (5, 17), (5, 18), (5, 19)], [(3, 15), (3, 16), (3, 17), (3, 18), (3, 19)], [(3, 13), (3, 14), (3, 15), (3, 16), (3, 17)]⟩

theorem g087_ok : tagOKF CompactData.T CompactData.F g087 = true := by decide +kernel

def g088 : Tag := .inr ⟨(24 / 25 : ℚ), (26 / 25 : ℚ), (1 / 50 : ℚ), (9 / 400 : ℚ), (1 : ℚ), (17 / 800 : ℚ), (0, 1), (5, 22), (3, 20), (3, 19), [(0, 0), (0, 1), (0, 2)], [(5, 18), (5, 19), (5, 20), (5, 21), (5, 22), (5, 23), (6, 0), (6, 1), (6, 2)], [(3, 18), (3, 19), (3, 20), (3, 21), (3, 22)], [(3, 17), (3, 18), (3, 19), (3, 20), (3, 21)]⟩

theorem g088_ok : tagOKF CompactData.T CompactData.F g088 = true := by decide +kernel

def g089 : Tag := .inr ⟨(26 / 25 : ℚ), (28 / 25 : ℚ), (1 / 50 : ℚ), (9 / 400 : ℚ), (27 / 25 : ℚ), (17 / 800 : ℚ), (0, 1), (6, 6), (4, 0), (3, 23), [(0, 0), (0, 1), (0, 2)], [(6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10)], [(3, 22), (3, 23), (4, 0), (4, 1), (4, 2)], [(3, 21), (3, 22), (3, 23), (4, 0), (4, 1)]⟩

theorem g089_ok : tagOKF CompactData.T CompactData.F g089 = true := by decide +kernel

def g090 : Tag := .inr ⟨(24 / 25 : ℚ), (26 / 25 : ℚ), (9 / 400 : ℚ), (1 / 40 : ℚ), (1 : ℚ), (19 / 800 : ℚ), (0, 3), (5, 22), (3, 20), (3, 19), [(0, 2), (0, 3), (0, 4)], [(5, 18), (5, 19), (5, 20), (5, 21), (5, 22), (5, 23), (6, 0), (6, 1), (6, 2)], [(3, 18), (3, 19), (3, 20), (3, 21), (3, 22)], [(3, 17), (3, 18), (3, 19), (3, 20), (3, 21)]⟩

theorem g090_ok : tagOKF CompactData.T CompactData.F g090 = true := by decide +kernel

def g091 : Tag := .inr ⟨(26 / 25 : ℚ), (28 / 25 : ℚ), (9 / 400 : ℚ), (1 / 40 : ℚ), (27 / 25 : ℚ), (19 / 800 : ℚ), (0, 3), (6, 6), (4, 0), (3, 23), [(0, 2), (0, 3), (0, 4)], [(6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10)], [(3, 22), (3, 23), (4, 0), (4, 1), (4, 2)], [(3, 21), (3, 22), (3, 23), (4, 0), (4, 1)]⟩

theorem g091_ok : tagOKF CompactData.T CompactData.F g091 = true := by decide +kernel

def g092 : Tag := .inr ⟨(28 / 25 : ℚ), (6 / 5 : ℚ), (1 / 50 : ℚ), (9 / 400 : ℚ), (29 / 25 : ℚ), (17 / 800 : ℚ), (0, 1), (6, 14), (4, 4), (4, 3), [(0, 0), (0, 1), (0, 2)], [(6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (6, 16), (6, 17), (6, 18)], [(4, 2), (4, 3), (4, 4), (4, 5), (4, 6)], [(4, 1), (4, 2), (4, 3), (4, 4), (4, 5)]⟩

theorem g092_ok : tagOKF CompactData.T CompactData.F g092 = true := by decide +kernel

def g093 : Tag := .inr ⟨(6 / 5 : ℚ), (32 / 25 : ℚ), (1 / 50 : ℚ), (9 / 400 : ℚ), (31 / 25 : ℚ), (17 / 800 : ℚ), (0, 1), (6, 22), (4, 8), (4, 7), [(0, 0), (0, 1), (0, 2)], [(6, 18), (6, 19), (6, 20), (6, 21), (6, 22), (6, 23), (7, 0), (7, 1), (7, 2)], [(4, 6), (4, 7), (4, 8), (4, 9), (4, 10)], [(4, 5), (4, 6), (4, 7), (4, 8), (4, 9)]⟩

theorem g093_ok : tagOKF CompactData.T CompactData.F g093 = true := by decide +kernel

def g094 : Tag := .inr ⟨(28 / 25 : ℚ), (6 / 5 : ℚ), (9 / 400 : ℚ), (1 / 40 : ℚ), (29 / 25 : ℚ), (19 / 800 : ℚ), (0, 3), (6, 14), (4, 4), (4, 3), [(0, 2), (0, 3), (0, 4)], [(6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (6, 16), (6, 17), (6, 18)], [(4, 2), (4, 3), (4, 4), (4, 5), (4, 6)], [(4, 1), (4, 2), (4, 3), (4, 4), (4, 5)]⟩


end CKLaneC3.CompactBatch48


