-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch06
-- name    : CK_CKLaneC3_CompactBatch06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T02:28:08.244655+00:00
-- url     : https://prove2.me/theorems/45bb9d57-cf9a-4af2-87c7-060cdaa88878
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch06` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch06` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch06` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch06 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch06.lean)

import Definitions.Def_CK_CKLaneC3_CompactData
import Definitions.Def_CK_CKLaneC3_CompactCoverF

-- ===== source module CKLaneC3.CompactBatch06 =====
section

/-! Lane C3 compact cell batch (generated; memoised chains over the data tables). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactBatch06
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF

def g000 : Tag := .inr ⟨(1 / 40 : ℚ), (11 / 400 : ℚ), (17 / 25 : ℚ), (18 / 25 : ℚ), (21 / 800 : ℚ), (7 / 10 : ℚ), (3, 4), (3, 7), (3, 5), (0, 5), [(3, 3), (3, 4), (3, 5)], [(3, 5), (3, 6), (3, 7), (3, 8)], [(3, 4), (3, 5), (3, 6)], [(0, 4), (0, 5), (0, 6)]⟩

theorem g000_ok : tagOKF CompactData.T CompactData.F g000 = true := by decide +kernel

def g001 : Tag := .inr ⟨(11 / 400 : ℚ), (3 / 100 : ℚ), (16 / 25 : ℚ), (17 / 25 : ℚ), (23 / 800 : ℚ), (33 / 50 : ℚ), (3, 2), (3, 5), (3, 3), (0, 7), [(3, 1), (3, 2), (3, 3)], [(3, 4), (3, 5), (3, 6)], [(3, 2), (3, 3), (3, 4)], [(0, 6), (0, 7), (0, 8)]⟩

theorem g001_ok : tagOKF CompactData.T CompactData.F g001 = true := by decide +kernel

def g002 : Tag := .inr ⟨(11 / 400 : ℚ), (3 / 100 : ℚ), (17 / 25 : ℚ), (18 / 25 : ℚ), (23 / 800 : ℚ), (7 / 10 : ℚ), (3, 4), (3, 7), (3, 5), (0, 7), [(3, 3), (3, 4), (3, 5)], [(3, 6), (3, 7), (3, 8)], [(3, 4), (3, 5), (3, 6)], [(0, 6), (0, 7), (0, 8)]⟩

theorem g002_ok : tagOKF CompactData.T CompactData.F g002 = true := by decide +kernel

def g003 : Tag := .inr ⟨(1 / 40 : ℚ), (11 / 400 : ℚ), (18 / 25 : ℚ), (19 / 25 : ℚ), (21 / 800 : ℚ), (37 / 50 : ℚ), (3, 6), (3, 9), (3, 7), (0, 5), [(3, 5), (3, 6), (3, 7)], [(3, 7), (3, 8), (3, 9), (3, 10)], [(3, 6), (3, 7), (3, 8)], [(0, 4), (0, 5), (0, 6)]⟩

theorem g003_ok : tagOKF CompactData.T CompactData.F g003 = true := by decide +kernel

def g004 : Tag := .inr ⟨(1 / 40 : ℚ), (11 / 400 : ℚ), (19 / 25 : ℚ), (4 / 5 : ℚ), (21 / 800 : ℚ), (39 / 50 : ℚ), (3, 8), (3, 11), (3, 9), (0, 5), [(3, 7), (3, 8), (3, 9)], [(3, 9), (3, 10), (3, 11), (3, 12)], [(3, 8), (3, 9), (3, 10)], [(0, 4), (0, 5), (0, 6)]⟩

theorem g004_ok : tagOKF CompactData.T CompactData.F g004 = true := by decide +kernel

def g005 : Tag := .inr ⟨(11 / 400 : ℚ), (3 / 100 : ℚ), (18 / 25 : ℚ), (19 / 25 : ℚ), (23 / 800 : ℚ), (37 / 50 : ℚ), (3, 6), (3, 9), (3, 7), (0, 7), [(3, 5), (3, 6), (3, 7)], [(3, 8), (3, 9), (3, 10)], [(3, 6), (3, 7), (3, 8)], [(0, 6), (0, 7), (0, 8)]⟩

theorem g005_ok : tagOKF CompactData.T CompactData.F g005 = true := by decide +kernel

def g006 : Tag := .inr ⟨(11 / 400 : ℚ), (3 / 100 : ℚ), (19 / 25 : ℚ), (4 / 5 : ℚ), (23 / 800 : ℚ), (39 / 50 : ℚ), (3, 8), (3, 11), (3, 9), (0, 7), [(3, 7), (3, 8), (3, 9)], [(3, 10), (3, 11), (3, 12)], [(3, 8), (3, 9), (3, 10)], [(0, 6), (0, 7), (0, 8)]⟩

theorem g006_ok : tagOKF CompactData.T CompactData.F g006 = true := by decide +kernel

def g007 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (4 / 5 : ℚ), (21 / 25 : ℚ), (41 / 1600 : ℚ), (41 / 50 : ℚ), (3, 10), (3, 12), (3, 11), (0, 5), [(3, 9), (3, 10), (3, 11)], [(3, 11), (3, 12), (3, 13), (3, 14)], [(3, 10), (3, 11), (3, 12)], [(0, 4), (0, 5)]⟩

theorem g007_ok : tagOKF CompactData.T CompactData.F g007 = true := by decide +kernel

def g008 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (21 / 25 : ℚ), (22 / 25 : ℚ), (41 / 1600 : ℚ), (43 / 50 : ℚ), (3, 12), (3, 14), (3, 13), (0, 5), [(3, 11), (3, 12), (3, 13)], [(3, 13), (3, 14), (3, 15), (3, 16)], [(3, 12), (3, 13), (3, 14)], [(0, 4), (0, 5)]⟩

theorem g008_ok : tagOKF CompactData.T CompactData.F g008 = true := by decide +kernel

def g009 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (4 / 5 : ℚ), (21 / 25 : ℚ), (43 / 1600 : ℚ), (41 / 50 : ℚ), (3, 10), (3, 13), (3, 11), (0, 6), [(3, 9), (3, 10), (3, 11)], [(3, 12), (3, 13), (3, 14)], [(3, 10), (3, 11), (3, 12)], [(0, 5), (0, 6)]⟩

theorem g009_ok : tagOKF CompactData.T CompactData.F g009 = true := by decide +kernel

def g010 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (21 / 25 : ℚ), (22 / 25 : ℚ), (43 / 1600 : ℚ), (43 / 50 : ℚ), (3, 12), (3, 15), (3, 13), (0, 6), [(3, 11), (3, 12), (3, 13)], [(3, 14), (3, 15), (3, 16)], [(3, 12), (3, 13), (3, 14)], [(0, 5), (0, 6)]⟩

theorem g010_ok : tagOKF CompactData.T CompactData.F g010 = true := by decide +kernel

def g011 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (22 / 25 : ℚ), (23 / 25 : ℚ), (41 / 1600 : ℚ), (9 / 10 : ℚ), (3, 14), (3, 16), (3, 15), (0, 5), [(3, 13), (3, 14), (3, 15)], [(3, 15), (3, 16), (3, 17), (3, 18)], [(3, 14), (3, 15), (3, 16)], [(0, 4), (0, 5)]⟩

theorem g011_ok : tagOKF CompactData.T CompactData.F g011 = true := by decide +kernel

def g012 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (23 / 25 : ℚ), (24 / 25 : ℚ), (41 / 1600 : ℚ), (47 / 50 : ℚ), (3, 16), (3, 18), (3, 17), (0, 5), [(3, 15), (3, 16), (3, 17)], [(3, 17), (3, 18), (3, 19), (3, 20)], [(3, 16), (3, 17), (3, 18)], [(0, 4), (0, 5)]⟩

theorem g012_ok : tagOKF CompactData.T CompactData.F g012 = true := by decide +kernel

def g013 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (22 / 25 : ℚ), (23 / 25 : ℚ), (43 / 1600 : ℚ), (9 / 10 : ℚ), (3, 14), (3, 17), (3, 15), (0, 6), [(3, 13), (3, 14), (3, 15)], [(3, 16), (3, 17), (3, 18)], [(3, 14), (3, 15), (3, 16)], [(0, 5), (0, 6)]⟩

theorem g013_ok : tagOKF CompactData.T CompactData.F g013 = true := by decide +kernel

def g014 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (23 / 25 : ℚ), (24 / 25 : ℚ), (43 / 1600 : ℚ), (47 / 50 : ℚ), (3, 16), (3, 19), (3, 17), (0, 6), [(3, 15), (3, 16), (3, 17)], [(3, 18), (3, 19), (3, 20)], [(3, 16), (3, 17), (3, 18)], [(0, 5), (0, 6)]⟩

theorem g014_ok : tagOKF CompactData.T CompactData.F g014 = true := by decide +kernel

def g015 : Tag := .inr ⟨(11 / 400 : ℚ), (3 / 100 : ℚ), (4 / 5 : ℚ), (21 / 25 : ℚ), (23 / 800 : ℚ), (41 / 50 : ℚ), (3, 10), (3, 13), (3, 11), (0, 7), [(3, 9), (3, 10), (3, 11)], [(3, 12), (3, 13), (3, 14)], [(3, 10), (3, 11), (3, 12)], [(0, 6), (0, 7), (0, 8)]⟩

theorem g015_ok : tagOKF CompactData.T CompactData.F g015 = true := by decide +kernel

def g016 : Tag := .inr ⟨(11 / 400 : ℚ), (3 / 100 : ℚ), (21 / 25 : ℚ), (22 / 25 : ℚ), (23 / 800 : ℚ), (43 / 50 : ℚ), (3, 12), (3, 15), (3, 13), (0, 7), [(3, 11), (3, 12), (3, 13)], [(3, 14), (3, 15), (3, 16)], [(3, 12), (3, 13), (3, 14)], [(0, 6), (0, 7), (0, 8)]⟩

theorem g016_ok : tagOKF CompactData.T CompactData.F g016 = true := by decide +kernel

def g017 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (22 / 25 : ℚ), (23 / 25 : ℚ), (9 / 320 : ℚ), (9 / 10 : ℚ), (3, 14), (3, 17), (3, 15), (0, 6), [(3, 13), (3, 14), (3, 15)], [(3, 16), (3, 17), (3, 18)], [(3, 14), (3, 15), (3, 16)], [(0, 6), (0, 7)]⟩

theorem g017_ok : tagOKF CompactData.T CompactData.F g017 = true := by decide +kernel

def g018 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (23 / 25 : ℚ), (24 / 25 : ℚ), (9 / 320 : ℚ), (47 / 50 : ℚ), (3, 16), (3, 19), (3, 17), (0, 6), [(3, 15), (3, 16), (3, 17)], [(3, 18), (3, 19), (3, 20)], [(3, 16), (3, 17), (3, 18)], [(0, 6), (0, 7)]⟩

theorem g018_ok : tagOKF CompactData.T CompactData.F g018 = true := by decide +kernel

def g019 : Tag := .inr ⟨(23 / 800 : ℚ), (3 / 100 : ℚ), (22 / 25 : ℚ), (23 / 25 : ℚ), (47 / 1600 : ℚ), (9 / 10 : ℚ), (3, 14), (3, 17), (3, 15), (0, 7), [(3, 13), (3, 14), (3, 15)], [(3, 16), (3, 17), (3, 18)], [(3, 14), (3, 15), (3, 16)], [(0, 7), (0, 8)]⟩

theorem g019_ok : tagOKF CompactData.T CompactData.F g019 = true := by decide +kernel

def g020 : Tag := .inr ⟨(23 / 800 : ℚ), (3 / 100 : ℚ), (23 / 25 : ℚ), (24 / 25 : ℚ), (47 / 1600 : ℚ), (47 / 50 : ℚ), (3, 16), (3, 19), (3, 17), (0, 7), [(3, 15), (3, 16), (3, 17)], [(3, 18), (3, 19), (3, 20)], [(3, 16), (3, 17), (3, 18)], [(0, 7), (0, 8)]⟩

theorem g020_ok : tagOKF CompactData.T CompactData.F g020 = true := by decide +kernel

def g021 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (24 / 25 : ℚ), (1 : ℚ), (33 / 1600 : ℚ), (49 / 50 : ℚ), (3, 18), (3, 20), (3, 19), (0, 0), [(3, 17), (3, 18), (3, 19)], [(3, 19), (3, 20), (3, 21)], [(3, 18), (3, 19), (3, 20)], [(0, 0), (0, 1)]⟩

theorem g021_ok : tagOKF CompactData.T CompactData.F g021 = true := by decide +kernel

def g022 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (1 : ℚ), (26 / 25 : ℚ), (33 / 1600 : ℚ), (51 / 50 : ℚ), (3, 20), (3, 22), (3, 21), (0, 0), [(3, 19), (3, 20), (3, 21)], [(3, 21), (3, 22), (3, 23)], [(3, 20), (3, 21), (3, 22)], [(0, 0), (0, 1)]⟩

theorem g022_ok : tagOKF CompactData.T CompactData.F g022 = true := by decide +kernel

def g023 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (24 / 25 : ℚ), (1 : ℚ), (7 / 320 : ℚ), (49 / 50 : ℚ), (3, 18), (3, 20), (3, 19), (0, 1), [(3, 17), (3, 18), (3, 19)], [(3, 19), (3, 20), (3, 21)], [(3, 18), (3, 19), (3, 20)], [(0, 1), (0, 2)]⟩

theorem g023_ok : tagOKF CompactData.T CompactData.F g023 = true := by decide +kernel

def g024 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (1 : ℚ), (26 / 25 : ℚ), (7 / 320 : ℚ), (51 / 50 : ℚ), (3, 20), (3, 22), (3, 21), (0, 1), [(3, 19), (3, 20), (3, 21)], [(3, 21), (3, 22), (3, 23)], [(3, 20), (3, 21), (3, 22)], [(0, 1), (0, 2)]⟩

theorem g024_ok : tagOKF CompactData.T CompactData.F g024 = true := by decide +kernel

def g025 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (26 / 25 : ℚ), (27 / 25 : ℚ), (33 / 1600 : ℚ), (53 / 50 : ℚ), (3, 22), (4, 0), (3, 23), (0, 0), [(3, 21), (3, 22), (3, 23)], [(3, 23), (4, 0), (4, 1)], [(3, 22), (3, 23), (4, 0)], [(0, 0), (0, 1)]⟩

theorem g025_ok : tagOKF CompactData.T CompactData.F g025 = true := by decide +kernel

def g026 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (27 / 25 : ℚ), (28 / 25 : ℚ), (33 / 1600 : ℚ), (11 / 10 : ℚ), (4, 0), (4, 2), (4, 1), (0, 0), [(3, 23), (4, 0), (4, 1)], [(4, 1), (4, 2), (4, 3)], [(4, 0), (4, 1), (4, 2)], [(0, 0), (0, 1)]⟩

theorem g026_ok : tagOKF CompactData.T CompactData.F g026 = true := by decide +kernel

def g027 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (26 / 25 : ℚ), (27 / 25 : ℚ), (7 / 320 : ℚ), (53 / 50 : ℚ), (3, 22), (4, 0), (3, 23), (0, 1), [(3, 21), (3, 22), (3, 23)], [(3, 23), (4, 0), (4, 1)], [(3, 22), (3, 23), (4, 0)], [(0, 1), (0, 2)]⟩

theorem g027_ok : tagOKF CompactData.T CompactData.F g027 = true := by decide +kernel

def g028 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (27 / 25 : ℚ), (28 / 25 : ℚ), (7 / 320 : ℚ), (11 / 10 : ℚ), (4, 0), (4, 2), (4, 1), (0, 1), [(3, 23), (4, 0), (4, 1)], [(4, 1), (4, 2), (4, 3)], [(4, 0), (4, 1), (4, 2)], [(0, 1), (0, 2)]⟩

theorem g028_ok : tagOKF CompactData.T CompactData.F g028 = true := by decide +kernel

def g029 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (24 / 25 : ℚ), (1 : ℚ), (37 / 1600 : ℚ), (49 / 50 : ℚ), (3, 18), (3, 20), (3, 19), (0, 2), [(3, 17), (3, 18), (3, 19)], [(3, 19), (3, 20), (3, 21)], [(3, 18), (3, 19), (3, 20)], [(0, 2), (0, 3)]⟩

theorem g029_ok : tagOKF CompactData.T CompactData.F g029 = true := by decide +kernel

def g030 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (1 : ℚ), (26 / 25 : ℚ), (37 / 1600 : ℚ), (51 / 50 : ℚ), (3, 20), (3, 22), (3, 21), (0, 2), [(3, 19), (3, 20), (3, 21)], [(3, 21), (3, 22), (3, 23)], [(3, 20), (3, 21), (3, 22)], [(0, 2), (0, 3)]⟩

theorem g030_ok : tagOKF CompactData.T CompactData.F g030 = true := by decide +kernel

def g031 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (24 / 25 : ℚ), (1 : ℚ), (39 / 1600 : ℚ), (49 / 50 : ℚ), (3, 18), (3, 20), (3, 19), (0, 4), [(3, 17), (3, 18), (3, 19)], [(3, 19), (3, 20), (3, 21)], [(3, 18), (3, 19), (3, 20)], [(0, 3), (0, 4)]⟩

theorem g031_ok : tagOKF CompactData.T CompactData.F g031 = true := by decide +kernel

def g032 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (1 : ℚ), (26 / 25 : ℚ), (39 / 1600 : ℚ), (51 / 50 : ℚ), (3, 20), (3, 22), (3, 21), (0, 4), [(3, 19), (3, 20), (3, 21)], [(3, 21), (3, 22), (3, 23)], [(3, 20), (3, 21), (3, 22)], [(0, 3), (0, 4)]⟩

theorem g032_ok : tagOKF CompactData.T CompactData.F g032 = true := by decide +kernel

def g033 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (26 / 25 : ℚ), (27 / 25 : ℚ), (37 / 1600 : ℚ), (53 / 50 : ℚ), (3, 22), (4, 0), (3, 23), (0, 2), [(3, 21), (3, 22), (3, 23)], [(3, 23), (4, 0), (4, 1)], [(3, 22), (3, 23), (4, 0)], [(0, 2), (0, 3)]⟩

theorem g033_ok : tagOKF CompactData.T CompactData.F g033 = true := by decide +kernel

def g034 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (27 / 25 : ℚ), (28 / 25 : ℚ), (37 / 1600 : ℚ), (11 / 10 : ℚ), (4, 0), (4, 2), (4, 1), (0, 2), [(3, 23), (4, 0), (4, 1)], [(4, 1), (4, 2), (4, 3)], [(4, 0), (4, 1), (4, 2)], [(0, 2), (0, 3)]⟩

theorem g034_ok : tagOKF CompactData.T CompactData.F g034 = true := by decide +kernel

def g035 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (26 / 25 : ℚ), (27 / 25 : ℚ), (39 / 1600 : ℚ), (53 / 50 : ℚ), (3, 22), (4, 0), (3, 23), (0, 4), [(3, 21), (3, 22), (3, 23)], [(3, 23), (4, 0), (4, 1)], [(3, 22), (3, 23), (4, 0)], [(0, 3), (0, 4)]⟩

theorem g035_ok : tagOKF CompactData.T CompactData.F g035 = true := by decide +kernel

def g036 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (27 / 25 : ℚ), (28 / 25 : ℚ), (39 / 1600 : ℚ), (11 / 10 : ℚ), (4, 0), (4, 2), (4, 1), (0, 4), [(3, 23), (4, 0), (4, 1)], [(4, 1), (4, 2), (4, 3)], [(4, 0), (4, 1), (4, 2)], [(0, 3), (0, 4)]⟩

theorem g036_ok : tagOKF CompactData.T CompactData.F g036 = true := by decide +kernel

def g037 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (28 / 25 : ℚ), (29 / 25 : ℚ), (33 / 1600 : ℚ), (57 / 50 : ℚ), (4, 2), (4, 4), (4, 3), (0, 0), [(4, 1), (4, 2), (4, 3)], [(4, 3), (4, 4), (4, 5)], [(4, 2), (4, 3), (4, 4)], [(0, 0), (0, 1)]⟩

theorem g037_ok : tagOKF CompactData.T CompactData.F g037 = true := by decide +kernel

def g038 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (29 / 25 : ℚ), (6 / 5 : ℚ), (33 / 1600 : ℚ), (59 / 50 : ℚ), (4, 4), (4, 6), (4, 5), (0, 0), [(4, 3), (4, 4), (4, 5)], [(4, 5), (4, 6), (4, 7)], [(4, 4), (4, 5), (4, 6)], [(0, 0), (0, 1)]⟩

theorem g038_ok : tagOKF CompactData.T CompactData.F g038 = true := by decide +kernel

def g039 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (28 / 25 : ℚ), (29 / 25 : ℚ), (7 / 320 : ℚ), (57 / 50 : ℚ), (4, 2), (4, 4), (4, 3), (0, 1), [(4, 1), (4, 2), (4, 3)], [(4, 3), (4, 4), (4, 5)], [(4, 2), (4, 3), (4, 4)], [(0, 1), (0, 2)]⟩

theorem g039_ok : tagOKF CompactData.T CompactData.F g039 = true := by decide +kernel

def g040 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (29 / 25 : ℚ), (6 / 5 : ℚ), (7 / 320 : ℚ), (59 / 50 : ℚ), (4, 4), (4, 6), (4, 5), (0, 1), [(4, 3), (4, 4), (4, 5)], [(4, 5), (4, 6), (4, 7)], [(4, 4), (4, 5), (4, 6)], [(0, 1), (0, 2)]⟩

theorem g040_ok : tagOKF CompactData.T CompactData.F g040 = true := by decide +kernel

def g041 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (6 / 5 : ℚ), (31 / 25 : ℚ), (33 / 1600 : ℚ), (61 / 50 : ℚ), (4, 6), (4, 8), (4, 7), (0, 0), [(4, 5), (4, 6), (4, 7)], [(4, 7), (4, 8), (4, 9)], [(4, 6), (4, 7), (4, 8)], [(0, 0), (0, 1)]⟩

theorem g041_ok : tagOKF CompactData.T CompactData.F g041 = true := by decide +kernel

def g042 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (31 / 25 : ℚ), (32 / 25 : ℚ), (33 / 1600 : ℚ), (63 / 50 : ℚ), (4, 8), (4, 10), (4, 9), (0, 0), [(4, 7), (4, 8), (4, 9)], [(4, 9), (4, 10), (4, 11)], [(4, 8), (4, 9), (4, 10)], [(0, 0), (0, 1)]⟩

theorem g042_ok : tagOKF CompactData.T CompactData.F g042 = true := by decide +kernel

def g043 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (6 / 5 : ℚ), (31 / 25 : ℚ), (7 / 320 : ℚ), (61 / 50 : ℚ), (4, 6), (4, 8), (4, 7), (0, 1), [(4, 5), (4, 6), (4, 7)], [(4, 7), (4, 8), (4, 9)], [(4, 6), (4, 7), (4, 8)], [(0, 1), (0, 2)]⟩

theorem g043_ok : tagOKF CompactData.T CompactData.F g043 = true := by decide +kernel

def g044 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (31 / 25 : ℚ), (32 / 25 : ℚ), (7 / 320 : ℚ), (63 / 50 : ℚ), (4, 8), (4, 10), (4, 9), (0, 1), [(4, 7), (4, 8), (4, 9)], [(4, 9), (4, 10), (4, 11)], [(4, 8), (4, 9), (4, 10)], [(0, 1), (0, 2)]⟩

theorem g044_ok : tagOKF CompactData.T CompactData.F g044 = true := by decide +kernel

def g045 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (28 / 25 : ℚ), (29 / 25 : ℚ), (37 / 1600 : ℚ), (57 / 50 : ℚ), (4, 2), (4, 4), (4, 3), (0, 2), [(4, 1), (4, 2), (4, 3)], [(4, 3), (4, 4), (4, 5)], [(4, 2), (4, 3), (4, 4)], [(0, 2), (0, 3)]⟩

theorem g045_ok : tagOKF CompactData.T CompactData.F g045 = true := by decide +kernel

def g046 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (29 / 25 : ℚ), (6 / 5 : ℚ), (37 / 1600 : ℚ), (59 / 50 : ℚ), (4, 4), (4, 6), (4, 5), (0, 2), [(4, 3), (4, 4), (4, 5)], [(4, 5), (4, 6), (4, 7)], [(4, 4), (4, 5), (4, 6)], [(0, 2), (0, 3)]⟩

theorem g046_ok : tagOKF CompactData.T CompactData.F g046 = true := by decide +kernel

def g047 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (28 / 25 : ℚ), (29 / 25 : ℚ), (39 / 1600 : ℚ), (57 / 50 : ℚ), (4, 2), (4, 4), (4, 3), (0, 4), [(4, 1), (4, 2), (4, 3)], [(4, 3), (4, 4), (4, 5)], [(4, 2), (4, 3), (4, 4)], [(0, 3), (0, 4)]⟩

theorem g047_ok : tagOKF CompactData.T CompactData.F g047 = true := by decide +kernel

def g048 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (29 / 25 : ℚ), (6 / 5 : ℚ), (39 / 1600 : ℚ), (59 / 50 : ℚ), (4, 4), (4, 6), (4, 5), (0, 4), [(4, 3), (4, 4), (4, 5)], [(4, 5), (4, 6), (4, 7)], [(4, 4), (4, 5), (4, 6)], [(0, 3), (0, 4)]⟩

theorem g048_ok : tagOKF CompactData.T CompactData.F g048 = true := by decide +kernel

def g049 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (6 / 5 : ℚ), (31 / 25 : ℚ), (37 / 1600 : ℚ), (61 / 50 : ℚ), (4, 6), (4, 8), (4, 7), (0, 2), [(4, 5), (4, 6), (4, 7)], [(4, 7), (4, 8), (4, 9)], [(4, 6), (4, 7), (4, 8)], [(0, 2), (0, 3)]⟩

theorem g049_ok : tagOKF CompactData.T CompactData.F g049 = true := by decide +kernel

def g050 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (31 / 25 : ℚ), (32 / 25 : ℚ), (37 / 1600 : ℚ), (63 / 50 : ℚ), (4, 8), (4, 10), (4, 9), (0, 2), [(4, 7), (4, 8), (4, 9)], [(4, 9), (4, 10), (4, 11)], [(4, 8), (4, 9), (4, 10)], [(0, 2), (0, 3)]⟩

theorem g050_ok : tagOKF CompactData.T CompactData.F g050 = true := by decide +kernel

def g051 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (6 / 5 : ℚ), (31 / 25 : ℚ), (39 / 1600 : ℚ), (61 / 50 : ℚ), (4, 6), (4, 8), (4, 7), (0, 4), [(4, 5), (4, 6), (4, 7)], [(4, 7), (4, 8), (4, 9)], [(4, 6), (4, 7), (4, 8)], [(0, 3), (0, 4)]⟩

theorem g051_ok : tagOKF CompactData.T CompactData.F g051 = true := by decide +kernel

def g052 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (31 / 25 : ℚ), (32 / 25 : ℚ), (39 / 1600 : ℚ), (63 / 50 : ℚ), (4, 8), (4, 10), (4, 9), (0, 4), [(4, 7), (4, 8), (4, 9)], [(4, 9), (4, 10), (4, 11)], [(4, 8), (4, 9), (4, 10)], [(0, 3), (0, 4)]⟩

theorem g052_ok : tagOKF CompactData.T CompactData.F g052 = true := by decide +kernel

def g053 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (24 / 25 : ℚ), (1 : ℚ), (41 / 1600 : ℚ), (49 / 50 : ℚ), (3, 18), (3, 20), (3, 19), (0, 5), [(3, 17), (3, 18), (3, 19)], [(3, 19), (3, 20), (3, 21), (3, 22)], [(3, 18), (3, 19), (3, 20)], [(0, 4), (0, 5)]⟩

theorem g053_ok : tagOKF CompactData.T CompactData.F g053 = true := by decide +kernel

def g054 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (1 : ℚ), (26 / 25 : ℚ), (41 / 1600 : ℚ), (51 / 50 : ℚ), (3, 20), (3, 22), (3, 21), (0, 5), [(3, 19), (3, 20), (3, 21)], [(3, 21), (3, 22), (3, 23), (4, 0)], [(3, 20), (3, 21), (3, 22)], [(0, 4), (0, 5)]⟩

theorem g054_ok : tagOKF CompactData.T CompactData.F g054 = true := by decide +kernel

def g055 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (24 / 25 : ℚ), (1 : ℚ), (43 / 1600 : ℚ), (49 / 50 : ℚ), (3, 18), (3, 21), (3, 19), (0, 6), [(3, 17), (3, 18), (3, 19)], [(3, 20), (3, 21), (3, 22)], [(3, 18), (3, 19), (3, 20)], [(0, 5), (0, 6)]⟩

theorem g055_ok : tagOKF CompactData.T CompactData.F g055 = true := by decide +kernel

def g056 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (1 : ℚ), (26 / 25 : ℚ), (43 / 1600 : ℚ), (51 / 50 : ℚ), (3, 20), (3, 23), (3, 21), (0, 6), [(3, 19), (3, 20), (3, 21)], [(3, 22), (3, 23), (4, 0)], [(3, 20), (3, 21), (3, 22)], [(0, 5), (0, 6)]⟩

theorem g056_ok : tagOKF CompactData.T CompactData.F g056 = true := by decide +kernel

def g057 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (26 / 25 : ℚ), (27 / 25 : ℚ), (41 / 1600 : ℚ), (53 / 50 : ℚ), (3, 22), (4, 0), (3, 23), (0, 5), [(3, 21), (3, 22), (3, 23)], [(3, 23), (4, 0), (4, 1), (4, 2)], [(3, 22), (3, 23), (4, 0)], [(0, 4), (0, 5)]⟩

theorem g057_ok : tagOKF CompactData.T CompactData.F g057 = true := by decide +kernel

def g058 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (27 / 25 : ℚ), (28 / 25 : ℚ), (41 / 1600 : ℚ), (11 / 10 : ℚ), (4, 0), (4, 2), (4, 1), (0, 5), [(3, 23), (4, 0), (4, 1)], [(4, 1), (4, 2), (4, 3), (4, 4)], [(4, 0), (4, 1), (4, 2)], [(0, 4), (0, 5)]⟩

theorem g058_ok : tagOKF CompactData.T CompactData.F g058 = true := by decide +kernel

def g059 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (26 / 25 : ℚ), (27 / 25 : ℚ), (43 / 1600 : ℚ), (53 / 50 : ℚ), (3, 22), (4, 1), (3, 23), (0, 6), [(3, 21), (3, 22), (3, 23)], [(4, 0), (4, 1), (4, 2)], [(3, 22), (3, 23), (4, 0)], [(0, 5), (0, 6)]⟩

theorem g059_ok : tagOKF CompactData.T CompactData.F g059 = true := by decide +kernel

def g060 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (27 / 25 : ℚ), (28 / 25 : ℚ), (43 / 1600 : ℚ), (11 / 10 : ℚ), (4, 0), (4, 3), (4, 1), (0, 6), [(3, 23), (4, 0), (4, 1)], [(4, 2), (4, 3), (4, 4)], [(4, 0), (4, 1), (4, 2)], [(0, 5), (0, 6)]⟩

theorem g060_ok : tagOKF CompactData.T CompactData.F g060 = true := by decide +kernel

def g061 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (24 / 25 : ℚ), (1 : ℚ), (9 / 320 : ℚ), (49 / 50 : ℚ), (3, 18), (3, 21), (3, 19), (0, 6), [(3, 17), (3, 18), (3, 19)], [(3, 20), (3, 21), (3, 22)], [(3, 18), (3, 19), (3, 20)], [(0, 6), (0, 7)]⟩

theorem g061_ok : tagOKF CompactData.T CompactData.F g061 = true := by decide +kernel

def g062 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (1 : ℚ), (26 / 25 : ℚ), (9 / 320 : ℚ), (51 / 50 : ℚ), (3, 20), (3, 23), (3, 21), (0, 6), [(3, 19), (3, 20), (3, 21)], [(3, 22), (3, 23), (4, 0)], [(3, 20), (3, 21), (3, 22)], [(0, 6), (0, 7)]⟩

theorem g062_ok : tagOKF CompactData.T CompactData.F g062 = true := by decide +kernel

def g063 : Tag := .inr ⟨(23 / 800 : ℚ), (3 / 100 : ℚ), (24 / 25 : ℚ), (1 : ℚ), (47 / 1600 : ℚ), (49 / 50 : ℚ), (3, 18), (3, 21), (3, 19), (0, 7), [(3, 17), (3, 18), (3, 19)], [(3, 20), (3, 21), (3, 22)], [(3, 18), (3, 19), (3, 20)], [(0, 7), (0, 8)]⟩

theorem g063_ok : tagOKF CompactData.T CompactData.F g063 = true := by decide +kernel

def g064 : Tag := .inr ⟨(23 / 800 : ℚ), (3 / 100 : ℚ), (1 : ℚ), (26 / 25 : ℚ), (47 / 1600 : ℚ), (51 / 50 : ℚ), (3, 20), (3, 23), (3, 21), (0, 7), [(3, 19), (3, 20), (3, 21)], [(3, 22), (3, 23), (4, 0)], [(3, 20), (3, 21), (3, 22)], [(0, 7), (0, 8)]⟩

theorem g064_ok : tagOKF CompactData.T CompactData.F g064 = true := by decide +kernel

def g065 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (26 / 25 : ℚ), (27 / 25 : ℚ), (9 / 320 : ℚ), (53 / 50 : ℚ), (3, 22), (4, 1), (3, 23), (0, 6), [(3, 21), (3, 22), (3, 23)], [(4, 0), (4, 1), (4, 2)], [(3, 22), (3, 23), (4, 0)], [(0, 6), (0, 7)]⟩

theorem g065_ok : tagOKF CompactData.T CompactData.F g065 = true := by decide +kernel

def g066 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (27 / 25 : ℚ), (28 / 25 : ℚ), (9 / 320 : ℚ), (11 / 10 : ℚ), (4, 0), (4, 3), (4, 1), (0, 6), [(3, 23), (4, 0), (4, 1)], [(4, 2), (4, 3), (4, 4)], [(4, 0), (4, 1), (4, 2)], [(0, 6), (0, 7)]⟩

theorem g066_ok : tagOKF CompactData.T CompactData.F g066 = true := by decide +kernel

def g067 : Tag := .inr ⟨(23 / 800 : ℚ), (3 / 100 : ℚ), (26 / 25 : ℚ), (27 / 25 : ℚ), (47 / 1600 : ℚ), (53 / 50 : ℚ), (3, 22), (4, 1), (3, 23), (0, 7), [(3, 21), (3, 22), (3, 23)], [(4, 0), (4, 1), (4, 2)], [(3, 22), (3, 23), (4, 0)], [(0, 7), (0, 8)]⟩

theorem g067_ok : tagOKF CompactData.T CompactData.F g067 = true := by decide +kernel

def g068 : Tag := .inr ⟨(23 / 800 : ℚ), (3 / 100 : ℚ), (27 / 25 : ℚ), (28 / 25 : ℚ), (47 / 1600 : ℚ), (11 / 10 : ℚ), (4, 0), (4, 3), (4, 1), (0, 7), [(3, 23), (4, 0), (4, 1)], [(4, 2), (4, 3), (4, 4)], [(4, 0), (4, 1), (4, 2)], [(0, 7), (0, 8)]⟩

theorem g068_ok : tagOKF CompactData.T CompactData.F g068 = true := by decide +kernel

def g069 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (28 / 25 : ℚ), (29 / 25 : ℚ), (41 / 1600 : ℚ), (57 / 50 : ℚ), (4, 2), (4, 4), (4, 3), (0, 5), [(4, 1), (4, 2), (4, 3)], [(4, 3), (4, 4), (4, 5), (4, 6)], [(4, 2), (4, 3), (4, 4)], [(0, 4), (0, 5)]⟩

theorem g069_ok : tagOKF CompactData.T CompactData.F g069 = true := by decide +kernel

def g070 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (29 / 25 : ℚ), (6 / 5 : ℚ), (41 / 1600 : ℚ), (59 / 50 : ℚ), (4, 4), (4, 6), (4, 5), (0, 5), [(4, 3), (4, 4), (4, 5)], [(4, 5), (4, 6), (4, 7), (4, 8)], [(4, 4), (4, 5), (4, 6)], [(0, 4), (0, 5)]⟩

theorem g070_ok : tagOKF CompactData.T CompactData.F g070 = true := by decide +kernel

def g071 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (28 / 25 : ℚ), (29 / 25 : ℚ), (43 / 1600 : ℚ), (57 / 50 : ℚ), (4, 2), (4, 5), (4, 3), (0, 6), [(4, 1), (4, 2), (4, 3)], [(4, 4), (4, 5), (4, 6)], [(4, 2), (4, 3), (4, 4)], [(0, 5), (0, 6)]⟩

theorem g071_ok : tagOKF CompactData.T CompactData.F g071 = true := by decide +kernel

def g072 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (29 / 25 : ℚ), (6 / 5 : ℚ), (43 / 1600 : ℚ), (59 / 50 : ℚ), (4, 4), (4, 7), (4, 5), (0, 6), [(4, 3), (4, 4), (4, 5)], [(4, 6), (4, 7), (4, 8)], [(4, 4), (4, 5), (4, 6)], [(0, 5), (0, 6)]⟩

theorem g072_ok : tagOKF CompactData.T CompactData.F g072 = true := by decide +kernel

def g073 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (6 / 5 : ℚ), (31 / 25 : ℚ), (41 / 1600 : ℚ), (61 / 50 : ℚ), (4, 6), (4, 8), (4, 7), (0, 5), [(4, 5), (4, 6), (4, 7)], [(4, 7), (4, 8), (4, 9), (4, 10)], [(4, 6), (4, 7), (4, 8)], [(0, 4), (0, 5)]⟩

theorem g073_ok : tagOKF CompactData.T CompactData.F g073 = true := by decide +kernel

def g074 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (31 / 25 : ℚ), (32 / 25 : ℚ), (41 / 1600 : ℚ), (63 / 50 : ℚ), (4, 8), (4, 10), (4, 9), (0, 5), [(4, 7), (4, 8), (4, 9)], [(4, 9), (4, 10), (4, 11), (4, 12)], [(4, 8), (4, 9), (4, 10)], [(0, 4), (0, 5)]⟩

theorem g074_ok : tagOKF CompactData.T CompactData.F g074 = true := by decide +kernel

def g075 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (6 / 5 : ℚ), (31 / 25 : ℚ), (43 / 1600 : ℚ), (61 / 50 : ℚ), (4, 6), (4, 9), (4, 7), (0, 6), [(4, 5), (4, 6), (4, 7)], [(4, 8), (4, 9), (4, 10)], [(4, 6), (4, 7), (4, 8)], [(0, 5), (0, 6)]⟩

theorem g075_ok : tagOKF CompactData.T CompactData.F g075 = true := by decide +kernel

def g076 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (31 / 25 : ℚ), (32 / 25 : ℚ), (43 / 1600 : ℚ), (63 / 50 : ℚ), (4, 8), (4, 11), (4, 9), (0, 6), [(4, 7), (4, 8), (4, 9)], [(4, 10), (4, 11), (4, 12)], [(4, 8), (4, 9), (4, 10)], [(0, 5), (0, 6)]⟩

theorem g076_ok : tagOKF CompactData.T CompactData.F g076 = true := by decide +kernel

def g077 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (28 / 25 : ℚ), (29 / 25 : ℚ), (9 / 320 : ℚ), (57 / 50 : ℚ), (4, 2), (4, 5), (4, 3), (0, 6), [(4, 1), (4, 2), (4, 3)], [(4, 4), (4, 5), (4, 6)], [(4, 2), (4, 3), (4, 4)], [(0, 6), (0, 7)]⟩

theorem g077_ok : tagOKF CompactData.T CompactData.F g077 = true := by decide +kernel

def g078 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (29 / 25 : ℚ), (6 / 5 : ℚ), (9 / 320 : ℚ), (59 / 50 : ℚ), (4, 4), (4, 7), (4, 5), (0, 6), [(4, 3), (4, 4), (4, 5)], [(4, 6), (4, 7), (4, 8)], [(4, 4), (4, 5), (4, 6)], [(0, 6), (0, 7)]⟩

theorem g078_ok : tagOKF CompactData.T CompactData.F g078 = true := by decide +kernel

def g079 : Tag := .inr ⟨(23 / 800 : ℚ), (3 / 100 : ℚ), (28 / 25 : ℚ), (29 / 25 : ℚ), (47 / 1600 : ℚ), (57 / 50 : ℚ), (4, 2), (4, 5), (4, 3), (0, 7), [(4, 1), (4, 2), (4, 3)], [(4, 4), (4, 5), (4, 6)], [(4, 2), (4, 3), (4, 4)], [(0, 7), (0, 8)]⟩

theorem g079_ok : tagOKF CompactData.T CompactData.F g079 = true := by decide +kernel

def g080 : Tag := .inr ⟨(23 / 800 : ℚ), (3 / 100 : ℚ), (29 / 25 : ℚ), (6 / 5 : ℚ), (47 / 1600 : ℚ), (59 / 50 : ℚ), (4, 4), (4, 7), (4, 5), (0, 7), [(4, 3), (4, 4), (4, 5)], [(4, 6), (4, 7), (4, 8)], [(4, 4), (4, 5), (4, 6)], [(0, 7), (0, 8)]⟩

theorem g080_ok : tagOKF CompactData.T CompactData.F g080 = true := by decide +kernel

def g081 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (6 / 5 : ℚ), (31 / 25 : ℚ), (9 / 320 : ℚ), (61 / 50 : ℚ), (4, 6), (4, 9), (4, 7), (0, 6), [(4, 5), (4, 6), (4, 7)], [(4, 8), (4, 9), (4, 10)], [(4, 6), (4, 7), (4, 8)], [(0, 6), (0, 7)]⟩

theorem g081_ok : tagOKF CompactData.T CompactData.F g081 = true := by decide +kernel

def g082 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (31 / 25 : ℚ), (32 / 25 : ℚ), (9 / 320 : ℚ), (63 / 50 : ℚ), (4, 8), (4, 11), (4, 9), (0, 6), [(4, 7), (4, 8), (4, 9)], [(4, 10), (4, 11), (4, 12)], [(4, 8), (4, 9), (4, 10)], [(0, 6), (0, 7)]⟩

theorem g082_ok : tagOKF CompactData.T CompactData.F g082 = true := by decide +kernel

def g083 : Tag := .inr ⟨(23 / 800 : ℚ), (3 / 100 : ℚ), (6 / 5 : ℚ), (32 / 25 : ℚ), (47 / 1600 : ℚ), (31 / 25 : ℚ), (4, 7), (4, 10), (4, 8), (0, 7), [(4, 5), (4, 6), (4, 7), (4, 8), (4, 9)], [(4, 8), (4, 9), (4, 10), (4, 11), (4, 12)], [(4, 6), (4, 7), (4, 8), (4, 9), (4, 10)], [(0, 7), (0, 8)]⟩

theorem g083_ok : tagOKF CompactData.T CompactData.F g083 = true := by decide +kernel

def g084 : Tag := .inr ⟨(3 / 100 : ℚ), (13 / 400 : ℚ), (16 / 25 : ℚ), (17 / 25 : ℚ), (1 / 32 : ℚ), (33 / 50 : ℚ), (3, 2), (3, 5), (3, 3), (0, 9), [(3, 1), (3, 2), (3, 3)], [(3, 4), (3, 5), (3, 6)], [(3, 2), (3, 3), (3, 4), (3, 5)], [(0, 8), (0, 9)]⟩

theorem g084_ok : tagOKF CompactData.T CompactData.F g084 = true := by decide +kernel

def g085 : Tag := .inr ⟨(3 / 100 : ℚ), (13 / 400 : ℚ), (17 / 25 : ℚ), (18 / 25 : ℚ), (1 / 32 : ℚ), (7 / 10 : ℚ), (3, 4), (3, 7), (3, 5), (0, 9), [(3, 3), (3, 4), (3, 5)], [(3, 6), (3, 7), (3, 8)], [(3, 4), (3, 5), (3, 6), (3, 7)], [(0, 8), (0, 9)]⟩

theorem g085_ok : tagOKF CompactData.T CompactData.F g085 = true := by decide +kernel

def g086 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (16 / 25 : ℚ), (17 / 25 : ℚ), (27 / 800 : ℚ), (33 / 50 : ℚ), (3, 2), (3, 5), (3, 4), (0, 10), [(3, 1), (3, 2), (3, 3)], [(3, 4), (3, 5), (3, 6)], [(3, 3), (3, 4), (3, 5)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g086_ok : tagOKF CompactData.T CompactData.F g086 = true := by decide +kernel

def g087 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (17 / 25 : ℚ), (18 / 25 : ℚ), (27 / 800 : ℚ), (7 / 10 : ℚ), (3, 4), (3, 7), (3, 6), (0, 10), [(3, 3), (3, 4), (3, 5)], [(3, 6), (3, 7), (3, 8)], [(3, 5), (3, 6), (3, 7)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g087_ok : tagOKF CompactData.T CompactData.F g087 = true := by decide +kernel

def g088 : Tag := .inr ⟨(3 / 100 : ℚ), (13 / 400 : ℚ), (18 / 25 : ℚ), (19 / 25 : ℚ), (1 / 32 : ℚ), (37 / 50 : ℚ), (3, 6), (3, 9), (3, 7), (0, 9), [(3, 5), (3, 6), (3, 7)], [(3, 8), (3, 9), (3, 10)], [(3, 6), (3, 7), (3, 8), (3, 9)], [(0, 8), (0, 9)]⟩

theorem g088_ok : tagOKF CompactData.T CompactData.F g088 = true := by decide +kernel

def g089 : Tag := .inr ⟨(3 / 100 : ℚ), (13 / 400 : ℚ), (19 / 25 : ℚ), (4 / 5 : ℚ), (1 / 32 : ℚ), (39 / 50 : ℚ), (3, 8), (3, 11), (3, 9), (0, 9), [(3, 7), (3, 8), (3, 9)], [(3, 10), (3, 11), (3, 12)], [(3, 8), (3, 9), (3, 10), (3, 11)], [(0, 8), (0, 9)]⟩

theorem g089_ok : tagOKF CompactData.T CompactData.F g089 = true := by decide +kernel

def g090 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (18 / 25 : ℚ), (19 / 25 : ℚ), (27 / 800 : ℚ), (37 / 50 : ℚ), (3, 6), (3, 9), (3, 8), (0, 10), [(3, 5), (3, 6), (3, 7)], [(3, 8), (3, 9), (3, 10)], [(3, 7), (3, 8), (3, 9)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g090_ok : tagOKF CompactData.T CompactData.F g090 = true := by decide +kernel

def g091 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (19 / 25 : ℚ), (4 / 5 : ℚ), (27 / 800 : ℚ), (39 / 50 : ℚ), (3, 8), (3, 11), (3, 10), (0, 10), [(3, 7), (3, 8), (3, 9)], [(3, 10), (3, 11), (3, 12)], [(3, 9), (3, 10), (3, 11)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g091_ok : tagOKF CompactData.T CompactData.F g091 = true := by decide +kernel

def g092 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (16 / 25 : ℚ), (17 / 25 : ℚ), (29 / 800 : ℚ), (33 / 50 : ℚ), (3, 2), (3, 6), (3, 4), (0, 12), [(3, 1), (3, 2), (3, 3)], [(3, 4), (3, 5), (3, 6), (3, 7)], [(3, 3), (3, 4), (3, 5)], [(0, 11), (0, 12)]⟩

theorem g092_ok : tagOKF CompactData.T CompactData.F g092 = true := by decide +kernel

def g093 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (17 / 25 : ℚ), (18 / 25 : ℚ), (29 / 800 : ℚ), (7 / 10 : ℚ), (3, 4), (3, 8), (3, 6), (0, 12), [(3, 3), (3, 4), (3, 5)], [(3, 6), (3, 7), (3, 8), (3, 9)], [(3, 5), (3, 6), (3, 7)], [(0, 11), (0, 12)]⟩

theorem g093_ok : tagOKF CompactData.T CompactData.F g093 = true := by decide +kernel

def g094 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (16 / 25 : ℚ), (17 / 25 : ℚ), (31 / 800 : ℚ), (33 / 50 : ℚ), (3, 2), (3, 6), (3, 4), (0, 13), [(3, 1), (3, 2), (3, 3)], [(3, 5), (3, 6), (3, 7)], [(3, 3), (3, 4), (3, 5)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g094_ok : tagOKF CompactData.T CompactData.F g094 = true := by decide +kernel

def g095 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (17 / 25 : ℚ), (18 / 25 : ℚ), (31 / 800 : ℚ), (7 / 10 : ℚ), (3, 4), (3, 8), (3, 6), (0, 13), [(3, 3), (3, 4), (3, 5)], [(3, 7), (3, 8), (3, 9)], [(3, 5), (3, 6), (3, 7)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g095_ok : tagOKF CompactData.T CompactData.F g095 = true := by decide +kernel

def g096 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (18 / 25 : ℚ), (19 / 25 : ℚ), (29 / 800 : ℚ), (37 / 50 : ℚ), (3, 6), (3, 10), (3, 8), (0, 12), [(3, 5), (3, 6), (3, 7)], [(3, 8), (3, 9), (3, 10), (3, 11)], [(3, 7), (3, 8), (3, 9)], [(0, 11), (0, 12)]⟩

theorem g096_ok : tagOKF CompactData.T CompactData.F g096 = true := by decide +kernel

def g097 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (19 / 25 : ℚ), (4 / 5 : ℚ), (29 / 800 : ℚ), (39 / 50 : ℚ), (3, 8), (3, 12), (3, 10), (0, 12), [(3, 7), (3, 8), (3, 9)], [(3, 10), (3, 11), (3, 12), (3, 13)], [(3, 9), (3, 10), (3, 11)], [(0, 11), (0, 12)]⟩

theorem g097_ok : tagOKF CompactData.T CompactData.F g097 = true := by decide +kernel

def g098 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (18 / 25 : ℚ), (19 / 25 : ℚ), (31 / 800 : ℚ), (37 / 50 : ℚ), (3, 6), (3, 10), (3, 8), (0, 13), [(3, 5), (3, 6), (3, 7)], [(3, 9), (3, 10), (3, 11)], [(3, 7), (3, 8), (3, 9)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g098_ok : tagOKF CompactData.T CompactData.F g098 = true := by decide +kernel

def g099 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (19 / 25 : ℚ), (4 / 5 : ℚ), (31 / 800 : ℚ), (39 / 50 : ℚ), (3, 8), (3, 12), (3, 10), (0, 13), [(3, 7), (3, 8), (3, 9)], [(3, 11), (3, 12), (3, 13)], [(3, 9), (3, 10), (3, 11)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g099_ok : tagOKF CompactData.T CompactData.F g099 = true := by decide +kernel

def g100 : Tag := .inr ⟨(3 / 100 : ℚ), (13 / 400 : ℚ), (4 / 5 : ℚ), (21 / 25 : ℚ), (1 / 32 : ℚ), (41 / 50 : ℚ), (3, 10), (3, 13), (3, 11), (0, 9), [(3, 9), (3, 10), (3, 11)], [(3, 12), (3, 13), (3, 14)], [(3, 10), (3, 11), (3, 12), (3, 13)], [(0, 8), (0, 9)]⟩

theorem g100_ok : tagOKF CompactData.T CompactData.F g100 = true := by decide +kernel

def g101 : Tag := .inr ⟨(3 / 100 : ℚ), (13 / 400 : ℚ), (21 / 25 : ℚ), (22 / 25 : ℚ), (1 / 32 : ℚ), (43 / 50 : ℚ), (3, 12), (3, 15), (3, 13), (0, 9), [(3, 11), (3, 12), (3, 13)], [(3, 14), (3, 15), (3, 16)], [(3, 12), (3, 13), (3, 14), (3, 15)], [(0, 8), (0, 9)]⟩

theorem g101_ok : tagOKF CompactData.T CompactData.F g101 = true := by decide +kernel

def g102 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (4 / 5 : ℚ), (21 / 25 : ℚ), (27 / 800 : ℚ), (41 / 50 : ℚ), (3, 10), (3, 13), (3, 12), (0, 10), [(3, 9), (3, 10), (3, 11)], [(3, 12), (3, 13), (3, 14)], [(3, 11), (3, 12), (3, 13)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g102_ok : tagOKF CompactData.T CompactData.F g102 = true := by decide +kernel

def g103 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (21 / 25 : ℚ), (22 / 25 : ℚ), (27 / 800 : ℚ), (43 / 50 : ℚ), (3, 12), (3, 15), (3, 14), (0, 10), [(3, 11), (3, 12), (3, 13)], [(3, 14), (3, 15), (3, 16)], [(3, 13), (3, 14), (3, 15)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g103_ok : tagOKF CompactData.T CompactData.F g103 = true := by decide +kernel

def g104 : Tag := .inr ⟨(3 / 100 : ℚ), (13 / 400 : ℚ), (22 / 25 : ℚ), (23 / 25 : ℚ), (1 / 32 : ℚ), (9 / 10 : ℚ), (3, 14), (3, 17), (3, 15), (0, 9), [(3, 13), (3, 14), (3, 15)], [(3, 16), (3, 17), (3, 18)], [(3, 14), (3, 15), (3, 16), (3, 17)], [(0, 8), (0, 9)]⟩

theorem g104_ok : tagOKF CompactData.T CompactData.F g104 = true := by decide +kernel

def g105 : Tag := .inr ⟨(3 / 100 : ℚ), (13 / 400 : ℚ), (23 / 25 : ℚ), (24 / 25 : ℚ), (1 / 32 : ℚ), (47 / 50 : ℚ), (3, 16), (3, 19), (3, 17), (0, 9), [(3, 15), (3, 16), (3, 17)], [(3, 18), (3, 19), (3, 20)], [(3, 16), (3, 17), (3, 18), (3, 19)], [(0, 8), (0, 9)]⟩

theorem g105_ok : tagOKF CompactData.T CompactData.F g105 = true := by decide +kernel

def g106 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (22 / 25 : ℚ), (23 / 25 : ℚ), (27 / 800 : ℚ), (9 / 10 : ℚ), (3, 14), (3, 17), (3, 16), (0, 10), [(3, 13), (3, 14), (3, 15)], [(3, 16), (3, 17), (3, 18)], [(3, 15), (3, 16), (3, 17)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g106_ok : tagOKF CompactData.T CompactData.F g106 = true := by decide +kernel

def g107 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (23 / 25 : ℚ), (24 / 25 : ℚ), (27 / 800 : ℚ), (47 / 50 : ℚ), (3, 16), (3, 19), (3, 18), (0, 10), [(3, 15), (3, 16), (3, 17)], [(3, 18), (3, 19), (3, 20)], [(3, 17), (3, 18), (3, 19)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g107_ok : tagOKF CompactData.T CompactData.F g107 = true := by decide +kernel

def g108 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (4 / 5 : ℚ), (21 / 25 : ℚ), (29 / 800 : ℚ), (41 / 50 : ℚ), (3, 10), (3, 14), (3, 12), (0, 12), [(3, 9), (3, 10), (3, 11)], [(3, 12), (3, 13), (3, 14), (3, 15)], [(3, 11), (3, 12), (3, 13)], [(0, 11), (0, 12)]⟩

theorem g108_ok : tagOKF CompactData.T CompactData.F g108 = true := by decide +kernel

def g109 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (21 / 25 : ℚ), (22 / 25 : ℚ), (29 / 800 : ℚ), (43 / 50 : ℚ), (3, 12), (3, 16), (3, 14), (0, 12), [(3, 11), (3, 12), (3, 13)], [(3, 14), (3, 15), (3, 16), (3, 17)], [(3, 13), (3, 14), (3, 15)], [(0, 11), (0, 12)]⟩

theorem g109_ok : tagOKF CompactData.T CompactData.F g109 = true := by decide +kernel

def g110 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (4 / 5 : ℚ), (21 / 25 : ℚ), (31 / 800 : ℚ), (41 / 50 : ℚ), (3, 10), (3, 14), (3, 12), (0, 13), [(3, 9), (3, 10), (3, 11)], [(3, 13), (3, 14), (3, 15)], [(3, 11), (3, 12), (3, 13)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g110_ok : tagOKF CompactData.T CompactData.F g110 = true := by decide +kernel

def g111 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (21 / 25 : ℚ), (22 / 25 : ℚ), (31 / 800 : ℚ), (43 / 50 : ℚ), (3, 12), (3, 16), (3, 14), (0, 13), [(3, 11), (3, 12), (3, 13)], [(3, 15), (3, 16), (3, 17)], [(3, 13), (3, 14), (3, 15)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g111_ok : tagOKF CompactData.T CompactData.F g111 = true := by decide +kernel

def g112 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (22 / 25 : ℚ), (23 / 25 : ℚ), (29 / 800 : ℚ), (9 / 10 : ℚ), (3, 14), (3, 18), (3, 16), (0, 12), [(3, 13), (3, 14), (3, 15)], [(3, 16), (3, 17), (3, 18), (3, 19)], [(3, 15), (3, 16), (3, 17)], [(0, 11), (0, 12)]⟩

theorem g112_ok : tagOKF CompactData.T CompactData.F g112 = true := by decide +kernel

def g113 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (23 / 25 : ℚ), (24 / 25 : ℚ), (29 / 800 : ℚ), (47 / 50 : ℚ), (3, 16), (3, 20), (3, 18), (0, 12), [(3, 15), (3, 16), (3, 17)], [(3, 18), (3, 19), (3, 20), (3, 21)], [(3, 17), (3, 18), (3, 19)], [(0, 11), (0, 12)]⟩

theorem g113_ok : tagOKF CompactData.T CompactData.F g113 = true := by decide +kernel

def g114 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (22 / 25 : ℚ), (23 / 25 : ℚ), (31 / 800 : ℚ), (9 / 10 : ℚ), (3, 14), (3, 18), (3, 16), (0, 13), [(3, 13), (3, 14), (3, 15)], [(3, 17), (3, 18), (3, 19)], [(3, 15), (3, 16), (3, 17)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g114_ok : tagOKF CompactData.T CompactData.F g114 = true := by decide +kernel

def g115 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (23 / 25 : ℚ), (24 / 25 : ℚ), (31 / 800 : ℚ), (47 / 50 : ℚ), (3, 16), (3, 20), (3, 18), (0, 13), [(3, 15), (3, 16), (3, 17)], [(3, 19), (3, 20), (3, 21)], [(3, 17), (3, 18), (3, 19)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g115_ok : tagOKF CompactData.T CompactData.F g115 = true := by decide +kernel

def g116 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (24 / 25 : ℚ), (1 : ℚ), (49 / 1600 : ℚ), (49 / 50 : ℚ), (3, 18), (3, 21), (3, 19), (0, 8), [(3, 17), (3, 18), (3, 19)], [(3, 20), (3, 21), (3, 22)], [(3, 18), (3, 19), (3, 20)], [(0, 8), (0, 9)]⟩

theorem g116_ok : tagOKF CompactData.T CompactData.F g116 = true := by decide +kernel

def g117 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (1 : ℚ), (26 / 25 : ℚ), (49 / 1600 : ℚ), (51 / 50 : ℚ), (3, 20), (3, 23), (3, 21), (0, 8), [(3, 19), (3, 20), (3, 21)], [(3, 22), (3, 23), (4, 0)], [(3, 20), (3, 21), (3, 22)], [(0, 8), (0, 9)]⟩

theorem g117_ok : tagOKF CompactData.T CompactData.F g117 = true := by decide +kernel

def g118 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (24 / 25 : ℚ), (1 : ℚ), (51 / 1600 : ℚ), (49 / 50 : ℚ), (3, 18), (3, 21), (3, 19), (0, 9), [(3, 17), (3, 18), (3, 19)], [(3, 20), (3, 21), (3, 22)], [(3, 18), (3, 19), (3, 20), (3, 21)], [(0, 9)]⟩

theorem g118_ok : tagOKF CompactData.T CompactData.F g118 = true := by decide +kernel

def g119 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (1 : ℚ), (26 / 25 : ℚ), (51 / 1600 : ℚ), (51 / 50 : ℚ), (3, 20), (3, 23), (3, 21), (0, 9), [(3, 19), (3, 20), (3, 21)], [(3, 22), (3, 23), (4, 0)], [(3, 20), (3, 21), (3, 22), (3, 23)], [(0, 9)]⟩

theorem g119_ok : tagOKF CompactData.T CompactData.F g119 = true := by decide +kernel

def tags : List Tag := [g000, g001, g002, g003, g004, g005, g006, g007, g008, g009, g010, g011, g012, g013, g014, g015, g016, g017, g018, g019, g020, g021, g022, g023, g024, g025, g026, g027, g028, g029, g030, g031, g032, g033, g034, g035, g036, g037, g038, g039, g040, g041, g042, g043, g044, g045, g046, g047, g048, g049, g050, g051, g052, g053, g054, g055, g056, g057, g058, g059, g060, g061, g062, g063, g064, g065, g066, g067, g068, g069, g070, g071, g072, g073, g074, g075, g076, g077, g078, g079, g080, g081, g082, g083, g084, g085, g086, g087, g088, g089, g090, g091, g092, g093, g094, g095, g096, g097, g098, g099, g100, g101, g102, g103, g104, g105, g106, g107, g108, g109, g110, g111, g112, g113, g114, g115, g116, g117, g118, g119]

theorem tags_ok : tags.all (tagOKF CompactData.T CompactData.F) = true := by
  simp only [tags, List.all_cons, List.all_nil, g000_ok, g001_ok, g002_ok, g003_ok, g004_ok, g005_ok, g006_ok, g007_ok, g008_ok, g009_ok, g010_ok, g011_ok, g012_ok, g013_ok, g014_ok, g015_ok, g016_ok, g017_ok, g018_ok, g019_ok, g020_ok, g021_ok, g022_ok, g023_ok, g024_ok, g025_ok, g026_ok, g027_ok, g028_ok, g029_ok, g030_ok, g031_ok, g032_ok, g033_ok, g034_ok, g035_ok, g036_ok, g037_ok, g038_ok, g039_ok, g040_ok, g041_ok, g042_ok, g043_ok, g044_ok, g045_ok, g046_ok, g047_ok, g048_ok, g049_ok, g050_ok, g051_ok, g052_ok, g053_ok, g054_ok, g055_ok, g056_ok, g057_ok, g058_ok, g059_ok, g060_ok, g061_ok, g062_ok, g063_ok, g064_ok, g065_ok, g066_ok, g067_ok, g068_ok, g069_ok, g070_ok, g071_ok, g072_ok, g073_ok, g074_ok, g075_ok, g076_ok, g077_ok, g078_ok, g079_ok, g080_ok, g081_ok, g082_ok, g083_ok, g084_ok, g085_ok, g086_ok, g087_ok, g088_ok, g089_ok, g090_ok, g091_ok, g092_ok, g093_ok, g094_ok, g095_ok, g096_ok, g097_ok, g098_ok, g099_ok, g100_ok, g101_ok, g102_ok, g103_ok, g104_ok, g105_ok, g106_ok, g107_ok, g108_ok, g109_ok, g110_ok, g111_ok, g112_ok, g113_ok, g114_ok, g115_ok, g116_ok, g117_ok, g118_ok, g119_ok, Bool.and_self]

end CKLaneC3.CompactBatch06

end


