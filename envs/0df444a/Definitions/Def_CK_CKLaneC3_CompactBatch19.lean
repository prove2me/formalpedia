-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch19
-- name    : CK_CKLaneC3_CompactBatch19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:50:32.316223+00:00
-- url     : https://prove2.me/theorems/ba306307-b341-43ba-a16e-e865a2a1c51c
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch19` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch19` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch19` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch19 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch19.lean)

import Definitions.Def_CK_CKLaneC3_CompactBatch19_part00

/-! Lane C3 compact cell batch (generated; memoised chains over the data tables). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactBatch19
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF

def g062 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (11 / 200 : ℚ), (3 / 50 : ℚ), (47 / 800 : ℚ), (23 / 400 : ℚ), (0, 21), (1, 20), (1, 12), (0, 22), [(0, 20), (0, 21), (0, 22)], [(1, 19), (1, 20), (1, 21)], [(1, 11), (1, 12)], [(0, 21), (0, 22)]⟩

theorem g062_ok : tagOKF CompactData.T CompactData.F g062 = true := by decide +kernel

def g063 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (3 / 50 : ℚ), (1 / 16 : ℚ), (33 / 800 : ℚ), (49 / 800 : ℚ), (0, 22), (1, 16), (1, 9), (0, 14), [(0, 22), (0, 23)], [(1, 15), (1, 16)], [(1, 8), (1, 9)], [(0, 14), (0, 15)]⟩

theorem g063_ok : tagOKF CompactData.T CompactData.F g063 = true := by decide +kernel

def g064 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (1 / 16 : ℚ), (13 / 200 : ℚ), (33 / 800 : ℚ), (51 / 800 : ℚ), (0, 23), (1, 16), (1, 9), (0, 14), [(0, 23), (1, 0)], [(1, 16), (1, 17)], [(1, 9), (1, 10)], [(0, 14), (0, 15)]⟩

theorem g064_ok : tagOKF CompactData.T CompactData.F g064 = true := by decide +kernel

def g065 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (3 / 50 : ℚ), (13 / 200 : ℚ), (7 / 160 : ℚ), (1 / 16 : ℚ), (0, 23), (1, 17), (1, 10), (0, 16), [(0, 22), (0, 23), (1, 0)], [(1, 16), (1, 17)], [(1, 9), (1, 10)], [(0, 15), (0, 16)]⟩

theorem g065_ok : tagOKF CompactData.T CompactData.F g065 = true := by decide +kernel

def g066 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (13 / 200 : ℚ), (7 / 100 : ℚ), (33 / 800 : ℚ), (27 / 400 : ℚ), (1, 0), (1, 17), (1, 10), (0, 14), [(1, 0), (1, 1)], [(1, 16), (1, 17)], [(1, 9), (1, 10), (1, 11)], [(0, 14), (0, 15)]⟩

theorem g066_ok : tagOKF CompactData.T CompactData.F g066 = true := by decide +kernel

def g067 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (13 / 200 : ℚ), (7 / 100 : ℚ), (7 / 160 : ℚ), (27 / 400 : ℚ), (1, 0), (1, 17), (1, 11), (0, 16), [(1, 0), (1, 1)], [(1, 17), (1, 18)], [(1, 10), (1, 11)], [(0, 15), (0, 16)]⟩

theorem g067_ok : tagOKF CompactData.T CompactData.F g067 = true := by decide +kernel

def g068 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (3 / 50 : ℚ), (13 / 200 : ℚ), (37 / 800 : ℚ), (1 / 16 : ℚ), (0, 23), (1, 17), (1, 10), (0, 17), [(0, 22), (0, 23), (1, 0)], [(1, 17), (1, 18)], [(1, 9), (1, 10), (1, 11)], [(0, 16), (0, 17)]⟩

theorem g068_ok : tagOKF CompactData.T CompactData.F g068 = true := by decide +kernel

def g069 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (3 / 50 : ℚ), (13 / 200 : ℚ), (39 / 800 : ℚ), (1 / 16 : ℚ), (0, 23), (1, 18), (1, 11), (0, 18), [(0, 22), (0, 23), (1, 0)], [(1, 17), (1, 18), (1, 19)], [(1, 10), (1, 11)], [(0, 17), (0, 18)]⟩

theorem g069_ok : tagOKF CompactData.T CompactData.F g069 = true := by decide +kernel

def g070 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (13 / 200 : ℚ), (7 / 100 : ℚ), (37 / 800 : ℚ), (27 / 400 : ℚ), (1, 0), (1, 18), (1, 11), (0, 17), [(1, 0), (1, 1)], [(1, 17), (1, 18), (1, 19)], [(1, 10), (1, 11), (1, 12)], [(0, 16), (0, 17)]⟩

theorem g070_ok : tagOKF CompactData.T CompactData.F g070 = true := by decide +kernel

def g071 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (13 / 200 : ℚ), (7 / 100 : ℚ), (39 / 800 : ℚ), (27 / 400 : ℚ), (1, 0), (1, 19), (1, 12), (0, 18), [(1, 0), (1, 1)], [(1, 18), (1, 19)], [(1, 11), (1, 12)], [(0, 17), (0, 18)]⟩

theorem g071_ok : tagOKF CompactData.T CompactData.F g071 = true := by decide +kernel

def g072 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (7 / 100 : ℚ), (3 / 40 : ℚ), (33 / 800 : ℚ), (29 / 400 : ℚ), (1, 2), (1, 17), (1, 11), (0, 14), [(1, 1), (1, 2), (1, 3)], [(1, 17), (1, 18)], [(1, 10), (1, 11), (1, 12)], [(0, 14), (0, 15)]⟩

theorem g072_ok : tagOKF CompactData.T CompactData.F g072 = true := by decide +kernel

def g073 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (7 / 100 : ℚ), (3 / 40 : ℚ), (7 / 160 : ℚ), (29 / 400 : ℚ), (1, 2), (1, 18), (1, 12), (0, 16), [(1, 1), (1, 2), (1, 3)], [(1, 17), (1, 18), (1, 19)], [(1, 11), (1, 12)], [(0, 15), (0, 16)]⟩

theorem g073_ok : tagOKF CompactData.T CompactData.F g073 = true := by decide +kernel

def g074 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (3 / 40 : ℚ), (2 / 25 : ℚ), (33 / 800 : ℚ), (31 / 400 : ℚ), (1, 3), (1, 18), (1, 12), (0, 14), [(1, 3), (1, 4)], [(1, 17), (1, 18), (1, 19)], [(1, 11), (1, 12), (1, 13)], [(0, 14), (0, 15)]⟩

theorem g074_ok : tagOKF CompactData.T CompactData.F g074 = true := by decide +kernel

def g075 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (3 / 40 : ℚ), (2 / 25 : ℚ), (7 / 160 : ℚ), (31 / 400 : ℚ), (1, 3), (1, 19), (1, 12), (0, 16), [(1, 3), (1, 4)], [(1, 18), (1, 19)], [(1, 12), (1, 13)], [(0, 15), (0, 16)]⟩

theorem g075_ok : tagOKF CompactData.T CompactData.F g075 = true := by decide +kernel

def g076 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (7 / 100 : ℚ), (3 / 40 : ℚ), (37 / 800 : ℚ), (29 / 400 : ℚ), (1, 2), (1, 19), (1, 12), (0, 17), [(1, 1), (1, 2), (1, 3)], [(1, 18), (1, 19)], [(1, 11), (1, 12), (1, 13)], [(0, 16), (0, 17)]⟩

theorem g076_ok : tagOKF CompactData.T CompactData.F g076 = true := by decide +kernel

def g077 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (7 / 100 : ℚ), (3 / 40 : ℚ), (39 / 800 : ℚ), (29 / 400 : ℚ), (1, 2), (1, 19), (1, 12), (0, 18), [(1, 1), (1, 2), (1, 3)], [(1, 19), (1, 20)], [(1, 12), (1, 13)], [(0, 17), (0, 18)]⟩

theorem g077_ok : tagOKF CompactData.T CompactData.F g077 = true := by decide +kernel

def g078 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (3 / 40 : ℚ), (2 / 25 : ℚ), (37 / 800 : ℚ), (31 / 400 : ℚ), (1, 3), (1, 19), (1, 13), (0, 17), [(1, 3), (1, 4)], [(1, 19), (1, 20)], [(1, 12), (1, 13)], [(0, 16), (0, 17)]⟩

theorem g078_ok : tagOKF CompactData.T CompactData.F g078 = true := by decide +kernel

def g079 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (3 / 40 : ℚ), (2 / 25 : ℚ), (39 / 800 : ℚ), (31 / 400 : ℚ), (1, 3), (1, 20), (1, 13), (0, 18), [(1, 3), (1, 4)], [(1, 19), (1, 20), (1, 21)], [(1, 13), (1, 14)], [(0, 17), (0, 18)]⟩

theorem g079_ok : tagOKF CompactData.T CompactData.F g079 = true := by decide +kernel

def g080 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (3 / 50 : ℚ), (13 / 200 : ℚ), (41 / 800 : ℚ), (1 / 16 : ℚ), (0, 23), (1, 19), (1, 11), (0, 19), [(0, 22), (0, 23), (1, 0)], [(1, 18), (1, 19)], [(1, 10), (1, 11), (1, 12)], [(0, 18), (0, 19)]⟩

theorem g080_ok : tagOKF CompactData.T CompactData.F g080 = true := by decide +kernel

def g081 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (3 / 50 : ℚ), (13 / 200 : ℚ), (43 / 800 : ℚ), (1 / 16 : ℚ), (0, 23), (1, 19), (1, 12), (0, 20), [(0, 22), (0, 23), (1, 0)], [(1, 19), (1, 20)], [(1, 11), (1, 12)], [(0, 19), (0, 20)]⟩

theorem g081_ok : tagOKF CompactData.T CompactData.F g081 = true := by decide +kernel

def g082 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (13 / 200 : ℚ), (7 / 100 : ℚ), (41 / 800 : ℚ), (27 / 400 : ℚ), (1, 0), (1, 19), (1, 12), (0, 19), [(1, 0), (1, 1)], [(1, 19), (1, 20)], [(1, 11), (1, 12), (1, 13)], [(0, 18), (0, 19)]⟩

theorem g082_ok : tagOKF CompactData.T CompactData.F g082 = true := by decide +kernel

def g083 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (13 / 200 : ℚ), (7 / 100 : ℚ), (43 / 800 : ℚ), (27 / 400 : ℚ), (1, 0), (1, 20), (1, 12), (0, 20), [(1, 0), (1, 1)], [(1, 19), (1, 20), (1, 21)], [(1, 12), (1, 13)], [(0, 19), (0, 20)]⟩

theorem g083_ok : tagOKF CompactData.T CompactData.F g083 = true := by decide +kernel

def g084 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (3 / 50 : ℚ), (13 / 200 : ℚ), (9 / 160 : ℚ), (1 / 16 : ℚ), (0, 23), (1, 20), (1, 12), (0, 21), [(0, 22), (0, 23), (1, 0)], [(1, 19), (1, 20), (1, 21)], [(1, 11), (1, 12), (1, 13)], [(0, 20), (0, 21)]⟩

theorem g084_ok : tagOKF CompactData.T CompactData.F g084 = true := by decide +kernel

def g085 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (3 / 50 : ℚ), (13 / 200 : ℚ), (47 / 800 : ℚ), (1 / 16 : ℚ), (0, 23), (1, 21), (1, 12), (0, 22), [(0, 22), (0, 23), (1, 0)], [(1, 20), (1, 21)], [(1, 12), (1, 13)], [(0, 21), (0, 22)]⟩

theorem g085_ok : tagOKF CompactData.T CompactData.F g085 = true := by decide +kernel

def g086 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (13 / 200 : ℚ), (7 / 100 : ℚ), (9 / 160 : ℚ), (27 / 400 : ℚ), (1, 0), (1, 21), (1, 13), (0, 21), [(1, 0), (1, 1)], [(1, 20), (1, 21)], [(1, 12), (1, 13)], [(0, 20), (0, 21)]⟩

theorem g086_ok : tagOKF CompactData.T CompactData.F g086 = true := by decide +kernel

def g087 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (13 / 200 : ℚ), (7 / 100 : ℚ), (47 / 800 : ℚ), (27 / 400 : ℚ), (1, 0), (1, 21), (1, 13), (0, 22), [(1, 0), (1, 1)], [(1, 21), (1, 22)], [(1, 13), (1, 14)], [(0, 21), (0, 22)]⟩

theorem g087_ok : tagOKF CompactData.T CompactData.F g087 = true := by decide +kernel

def g088 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (7 / 100 : ℚ), (3 / 40 : ℚ), (41 / 800 : ℚ), (29 / 400 : ℚ), (1, 2), (1, 20), (1, 13), (0, 19), [(1, 1), (1, 2), (1, 3)], [(1, 19), (1, 20), (1, 21)], [(1, 12), (1, 13)], [(0, 18), (0, 19)]⟩

theorem g088_ok : tagOKF CompactData.T CompactData.F g088 = true := by decide +kernel

def g089 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (7 / 100 : ℚ), (3 / 40 : ℚ), (43 / 800 : ℚ), (29 / 400 : ℚ), (1, 2), (1, 21), (1, 13), (0, 20), [(1, 1), (1, 2), (1, 3)], [(1, 20), (1, 21)], [(1, 13), (1, 14)], [(0, 19), (0, 20)]⟩

theorem g089_ok : tagOKF CompactData.T CompactData.F g089 = true := by decide +kernel

def g090 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (3 / 40 : ℚ), (2 / 25 : ℚ), (41 / 800 : ℚ), (31 / 400 : ℚ), (1, 3), (1, 21), (1, 14), (0, 19), [(1, 3), (1, 4)], [(1, 20), (1, 21)], [(1, 13), (1, 14)], [(0, 18), (0, 19)]⟩

theorem g090_ok : tagOKF CompactData.T CompactData.F g090 = true := by decide +kernel

def g091 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (3 / 40 : ℚ), (2 / 25 : ℚ), (43 / 800 : ℚ), (31 / 400 : ℚ), (1, 3), (1, 21), (1, 14), (0, 20), [(1, 3), (1, 4)], [(1, 21), (1, 22)], [(1, 13), (1, 14), (1, 15)], [(0, 19), (0, 20)]⟩

theorem g091_ok : tagOKF CompactData.T CompactData.F g091 = true := by decide +kernel

def g092 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (7 / 100 : ℚ), (3 / 40 : ℚ), (9 / 160 : ℚ), (29 / 400 : ℚ), (1, 2), (1, 21), (1, 14), (0, 21), [(1, 1), (1, 2), (1, 3)], [(1, 21), (1, 22)], [(1, 13), (1, 14)], [(0, 20), (0, 21)]⟩

theorem g092_ok : tagOKF CompactData.T CompactData.F g092 = true := by decide +kernel

def g093 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (7 / 100 : ℚ), (3 / 40 : ℚ), (47 / 800 : ℚ), (29 / 400 : ℚ), (1, 2), (1, 22), (1, 14), (0, 22), [(1, 1), (1, 2), (1, 3)], [(1, 21), (1, 22)], [(1, 13), (1, 14), (1, 15)], [(0, 21), (0, 22)]⟩

theorem g093_ok : tagOKF CompactData.T CompactData.F g093 = true := by decide +kernel

def g094 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (3 / 40 : ℚ), (2 / 25 : ℚ), (23 / 400 : ℚ), (31 / 400 : ℚ), (1, 3), (1, 22), (1, 15), (0, 21), [(1, 3), (1, 4)], [(1, 21), (1, 22), (1, 23)], [(1, 14), (1, 15)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g094_ok : tagOKF CompactData.T CompactData.F g094 = true := by decide +kernel

def g095 : Tag := .inr ⟨(3 / 50 : ℚ), (1 / 16 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (49 / 800 : ℚ), (33 / 800 : ℚ), (0, 14), (1, 19), (1, 9), (0, 22), [(0, 14), (0, 15)], [(1, 18), (1, 19)], [(1, 8), (1, 9)], [(0, 22), (0, 23)]⟩

theorem g095_ok : tagOKF CompactData.T CompactData.F g095 = true := by decide +kernel

def g096 : Tag := .inr ⟨(1 / 16 : ℚ), (13 / 200 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (51 / 800 : ℚ), (33 / 800 : ℚ), (0, 14), (1, 19), (1, 9), (0, 23), [(0, 14), (0, 15)], [(1, 19), (1, 20)], [(1, 9), (1, 10)], [(0, 23), (1, 0)]⟩

theorem g096_ok : tagOKF CompactData.T CompactData.F g096 = true := by decide +kernel

def g097 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (1 / 16 : ℚ), (7 / 160 : ℚ), (0, 16), (1, 19), (1, 10), (0, 23), [(0, 15), (0, 16)], [(1, 18), (1, 19), (1, 20)], [(1, 9), (1, 10)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g097_ok : tagOKF CompactData.T CompactData.F g097 = true := by decide +kernel

def g098 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (27 / 400 : ℚ), (33 / 800 : ℚ), (0, 14), (1, 20), (1, 10), (1, 0), [(0, 14), (0, 15)], [(1, 19), (1, 20), (1, 21)], [(1, 9), (1, 10), (1, 11)], [(1, 0), (1, 1)]⟩

theorem g098_ok : tagOKF CompactData.T CompactData.F g098 = true := by decide +kernel

def g099 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (27 / 400 : ℚ), (7 / 160 : ℚ), (0, 16), (1, 20), (1, 11), (1, 0), [(0, 15), (0, 16)], [(1, 20), (1, 21)], [(1, 10), (1, 11)], [(1, 0), (1, 1)]⟩

theorem g099_ok : tagOKF CompactData.T CompactData.F g099 = true := by decide +kernel

def g100 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (9 / 200 : ℚ), (19 / 400 : ℚ), (1 / 16 : ℚ), (37 / 800 : ℚ), (0, 17), (1, 20), (1, 10), (0, 23), [(0, 16), (0, 17)], [(1, 19), (1, 20)], [(1, 9), (1, 10), (1, 11)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g100_ok : tagOKF CompactData.T CompactData.F g100 = true := by decide +kernel

def g101 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (19 / 400 : ℚ), (1 / 20 : ℚ), (1 / 16 : ℚ), (39 / 800 : ℚ), (0, 18), (1, 20), (1, 11), (0, 23), [(0, 17), (0, 18)], [(1, 19), (1, 20), (1, 21)], [(1, 10), (1, 11)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g101_ok : tagOKF CompactData.T CompactData.F g101 = true := by decide +kernel

def g102 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (9 / 200 : ℚ), (19 / 400 : ℚ), (27 / 400 : ℚ), (37 / 800 : ℚ), (0, 17), (1, 21), (1, 11), (1, 0), [(0, 16), (0, 17)], [(1, 20), (1, 21)], [(1, 10), (1, 11), (1, 12)], [(1, 0), (1, 1)]⟩

theorem g102_ok : tagOKF CompactData.T CompactData.F g102 = true := by decide +kernel

def g103 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (19 / 400 : ℚ), (1 / 20 : ℚ), (27 / 400 : ℚ), (39 / 800 : ℚ), (0, 18), (1, 21), (1, 12), (1, 0), [(0, 17), (0, 18)], [(1, 20), (1, 21), (1, 22)], [(1, 11), (1, 12)], [(1, 0), (1, 1)]⟩

theorem g103_ok : tagOKF CompactData.T CompactData.F g103 = true := by decide +kernel

def g104 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (29 / 400 : ℚ), (33 / 800 : ℚ), (0, 14), (1, 21), (1, 11), (1, 2), [(0, 14), (0, 15)], [(1, 21), (1, 22)], [(1, 10), (1, 11), (1, 12)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g104_ok : tagOKF CompactData.T CompactData.F g104 = true := by decide +kernel

def g105 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (29 / 400 : ℚ), (7 / 160 : ℚ), (0, 16), (1, 22), (1, 12), (1, 2), [(0, 15), (0, 16)], [(1, 21), (1, 22)], [(1, 11), (1, 12)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g105_ok : tagOKF CompactData.T CompactData.F g105 = true := by decide +kernel

def g106 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (31 / 400 : ℚ), (33 / 800 : ℚ), (0, 14), (1, 22), (1, 12), (1, 3), [(0, 14), (0, 15)], [(1, 22), (1, 23)], [(1, 11), (1, 12), (1, 13)], [(1, 3), (1, 4)]⟩

theorem g106_ok : tagOKF CompactData.T CompactData.F g106 = true := by decide +kernel

def g107 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (31 / 400 : ℚ), (7 / 160 : ℚ), (0, 16), (1, 23), (1, 12), (1, 3), [(0, 15), (0, 16)], [(1, 22), (1, 23)], [(1, 12), (1, 13)], [(1, 3), (1, 4)]⟩

theorem g107_ok : tagOKF CompactData.T CompactData.F g107 = true := by decide +kernel

def g108 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (9 / 200 : ℚ), (19 / 400 : ℚ), (29 / 400 : ℚ), (37 / 800 : ℚ), (0, 17), (1, 22), (1, 12), (1, 2), [(0, 16), (0, 17)], [(1, 21), (1, 22)], [(1, 11), (1, 12), (1, 13)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g108_ok : tagOKF CompactData.T CompactData.F g108 = true := by decide +kernel

def g109 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (19 / 400 : ℚ), (1 / 20 : ℚ), (29 / 400 : ℚ), (39 / 800 : ℚ), (0, 18), (1, 22), (1, 12), (1, 2), [(0, 17), (0, 18)], [(1, 21), (1, 22), (1, 23)], [(1, 12), (1, 13)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g109_ok : tagOKF CompactData.T CompactData.F g109 = true := by decide +kernel

def g110 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (9 / 200 : ℚ), (1 / 20 : ℚ), (31 / 400 : ℚ), (19 / 400 : ℚ), (0, 17), (1, 23), (1, 13), (1, 3), [(0, 16), (0, 17), (0, 18)], [(1, 22), (1, 23), (2, 0)], [(1, 12), (1, 13), (1, 14)], [(1, 3), (1, 4)]⟩

theorem g110_ok : tagOKF CompactData.T CompactData.F g110 = true := by decide +kernel

def g111 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (1 / 20 : ℚ), (21 / 400 : ℚ), (1 / 16 : ℚ), (41 / 800 : ℚ), (0, 19), (1, 20), (1, 11), (0, 23), [(0, 18), (0, 19)], [(1, 19), (1, 20), (1, 21)], [(1, 10), (1, 11), (1, 12)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g111_ok : tagOKF CompactData.T CompactData.F g111 = true := by decide +kernel

def g112 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (21 / 400 : ℚ), (11 / 200 : ℚ), (1 / 16 : ℚ), (43 / 800 : ℚ), (0, 20), (1, 20), (1, 12), (0, 23), [(0, 19), (0, 20)], [(1, 20), (1, 21)], [(1, 11), (1, 12)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g112_ok : tagOKF CompactData.T CompactData.F g112 = true := by decide +kernel

def g113 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (1 / 20 : ℚ), (21 / 400 : ℚ), (27 / 400 : ℚ), (41 / 800 : ℚ), (0, 19), (1, 21), (1, 12), (1, 0), [(0, 18), (0, 19)], [(1, 21), (1, 22)], [(1, 11), (1, 12), (1, 13)], [(1, 0), (1, 1)]⟩

theorem g113_ok : tagOKF CompactData.T CompactData.F g113 = true := by decide +kernel

def g114 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (21 / 400 : ℚ), (11 / 200 : ℚ), (27 / 400 : ℚ), (43 / 800 : ℚ), (0, 20), (1, 22), (1, 12), (1, 0), [(0, 19), (0, 20)], [(1, 21), (1, 22)], [(1, 12), (1, 13)], [(1, 0), (1, 1)]⟩

theorem g114_ok : tagOKF CompactData.T CompactData.F g114 = true := by decide +kernel

def g115 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (11 / 200 : ℚ), (23 / 400 : ℚ), (1 / 16 : ℚ), (9 / 160 : ℚ), (0, 21), (1, 21), (1, 12), (0, 23), [(0, 20), (0, 21)], [(1, 20), (1, 21)], [(1, 11), (1, 12), (1, 13)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g115_ok : tagOKF CompactData.T CompactData.F g115 = true := by decide +kernel

def g116 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (23 / 400 : ℚ), (3 / 50 : ℚ), (1 / 16 : ℚ), (47 / 800 : ℚ), (0, 22), (1, 21), (1, 12), (0, 23), [(0, 21), (0, 22)], [(1, 20), (1, 21), (1, 22)], [(1, 12), (1, 13)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g116_ok : tagOKF CompactData.T CompactData.F g116 = true := by decide +kernel

def g117 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (11 / 200 : ℚ), (23 / 400 : ℚ), (27 / 400 : ℚ), (9 / 160 : ℚ), (0, 21), (1, 22), (1, 13), (1, 0), [(0, 20), (0, 21)], [(1, 21), (1, 22)], [(1, 12), (1, 13)], [(1, 0), (1, 1)]⟩

theorem g117_ok : tagOKF CompactData.T CompactData.F g117 = true := by decide +kernel

def g118 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (23 / 400 : ℚ), (3 / 50 : ℚ), (27 / 400 : ℚ), (47 / 800 : ℚ), (0, 22), (1, 22), (1, 13), (1, 0), [(0, 21), (0, 22)], [(1, 21), (1, 22), (1, 23)], [(1, 13), (1, 14)], [(1, 0), (1, 1)]⟩

theorem g118_ok : tagOKF CompactData.T CompactData.F g118 = true := by decide +kernel

def g119 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (1 / 20 : ℚ), (11 / 200 : ℚ), (29 / 400 : ℚ), (21 / 400 : ℚ), (0, 19), (1, 22), (1, 13), (1, 2), [(0, 18), (0, 19), (0, 20)], [(1, 22), (1, 23)], [(1, 12), (1, 13), (1, 14)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g119_ok : tagOKF CompactData.T CompactData.F g119 = true := by decide +kernel

def tags : List Tag := [g000, g001, g002, g003, g004, g005, g006, g007, g008, g009, g010, g011, g012, g013, g014, g015, g016, g017, g018, g019, g020, g021, g022, g023, g024, g025, g026, g027, g028, g029, g030, g031, g032, g033, g034, g035, g036, g037, g038, g039, g040, g041, g042, g043, g044, g045, g046, g047, g048, g049, g050, g051, g052, g053, g054, g055, g056, g057, g058, g059, g060, g061, g062, g063, g064, g065, g066, g067, g068, g069, g070, g071, g072, g073, g074, g075, g076, g077, g078, g079, g080, g081, g082, g083, g084, g085, g086, g087, g088, g089, g090, g091, g092, g093, g094, g095, g096, g097, g098, g099, g100, g101, g102, g103, g104, g105, g106, g107, g108, g109, g110, g111, g112, g113, g114, g115, g116, g117, g118, g119]

theorem tags_ok : tags.all (tagOKF CompactData.T CompactData.F) = true := by
  simp only [tags, List.all_cons, List.all_nil, g000_ok, g001_ok, g002_ok, g003_ok, g004_ok, g005_ok, g006_ok, g007_ok, g008_ok, g009_ok, g010_ok, g011_ok, g012_ok, g013_ok, g014_ok, g015_ok, g016_ok, g017_ok, g018_ok, g019_ok, g020_ok, g021_ok, g022_ok, g023_ok, g024_ok, g025_ok, g026_ok, g027_ok, g028_ok, g029_ok, g030_ok, g031_ok, g032_ok, g033_ok, g034_ok, g035_ok, g036_ok, g037_ok, g038_ok, g039_ok, g040_ok, g041_ok, g042_ok, g043_ok, g044_ok, g045_ok, g046_ok, g047_ok, g048_ok, g049_ok, g050_ok, g051_ok, g052_ok, g053_ok, g054_ok, g055_ok, g056_ok, g057_ok, g058_ok, g059_ok, g060_ok, g061_ok, g062_ok, g063_ok, g064_ok, g065_ok, g066_ok, g067_ok, g068_ok, g069_ok, g070_ok, g071_ok, g072_ok, g073_ok, g074_ok, g075_ok, g076_ok, g077_ok, g078_ok, g079_ok, g080_ok, g081_ok, g082_ok, g083_ok, g084_ok, g085_ok, g086_ok, g087_ok, g088_ok, g089_ok, g090_ok, g091_ok, g092_ok, g093_ok, g094_ok, g095_ok, g096_ok, g097_ok, g098_ok, g099_ok, g100_ok, g101_ok, g102_ok, g103_ok, g104_ok, g105_ok, g106_ok, g107_ok, g108_ok, g109_ok, g110_ok, g111_ok, g112_ok, g113_ok, g114_ok, g115_ok, g116_ok, g117_ok, g118_ok, g119_ok, Bool.and_self]

end CKLaneC3.CompactBatch19


