-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch32_part00
-- name    : CK_CKLaneC3_CompactBatch32_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T20:07:43.268471+00:00
-- url     : https://prove2.me/theorems/51bb47ee-c338-4a98-97dc-ba1ac25f3dca
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch32 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch32 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch32 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch32 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch32 (part 1 of 2).lean)

import Definitions.Def_CK_CKLaneC3_CompactData
import Definitions.Def_CK_CKLaneC3_CompactCoverF

/-! Lane C3 compact cell batch (generated; memoised chains over the data tables). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactBatch32
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF

def g000 : Tag := .inr ⟨(2 / 25 : ℚ), (17 / 200 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (33 / 400 : ℚ), (29 / 800 : ℚ), (0, 12), (1, 23), (1, 12), (1, 5), [(0, 11), (0, 12)], [(1, 22), (1, 23)], [(1, 11), (1, 12), (1, 13)], [(1, 4), (1, 5)]⟩

theorem g000_ok : tagOKF CompactData.T CompactData.F g000 = true := by decide +kernel

def g001 : Tag := .inr ⟨(17 / 200 : ℚ), (9 / 100 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (7 / 80 : ℚ), (29 / 800 : ℚ), (0, 12), (2, 0), (1, 13), (1, 6), [(0, 11), (0, 12)], [(1, 23), (2, 0)], [(1, 12), (1, 13)], [(1, 5), (1, 6)]⟩

theorem g001_ok : tagOKF CompactData.T CompactData.F g001 = true := by decide +kernel

def g002 : Tag := .inr ⟨(2 / 25 : ℚ), (17 / 200 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (33 / 400 : ℚ), (31 / 800 : ℚ), (0, 13), (1, 23), (1, 12), (1, 5), [(0, 12), (0, 13), (0, 14)], [(1, 22), (1, 23), (2, 0)], [(1, 12), (1, 13)], [(1, 4), (1, 5)]⟩

theorem g002_ok : tagOKF CompactData.T CompactData.F g002 = true := by decide +kernel

def g003 : Tag := .inr ⟨(17 / 200 : ℚ), (9 / 100 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (7 / 80 : ℚ), (31 / 800 : ℚ), (0, 13), (2, 0), (1, 13), (1, 6), [(0, 12), (0, 13), (0, 14)], [(1, 23), (2, 0), (2, 1)], [(1, 13), (1, 14)], [(1, 5), (1, 6)]⟩

theorem g003_ok : tagOKF CompactData.T CompactData.F g003 = true := by decide +kernel

def g004 : Tag := .inr ⟨(9 / 100 : ℚ), (19 / 200 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (37 / 400 : ℚ), (29 / 800 : ℚ), (0, 12), (2, 1), (1, 14), (1, 7), [(0, 11), (0, 12)], [(2, 0), (2, 1)], [(1, 13), (1, 14)], [(1, 6), (1, 7)]⟩

theorem g004_ok : tagOKF CompactData.T CompactData.F g004 = true := by decide +kernel

def g005 : Tag := .inr ⟨(19 / 200 : ℚ), (1 / 10 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (39 / 400 : ℚ), (29 / 800 : ℚ), (0, 12), (2, 2), (1, 14), (1, 8), [(0, 11), (0, 12)], [(2, 1), (2, 2)], [(1, 14), (1, 15)], [(1, 7), (1, 8)]⟩

theorem g005_ok : tagOKF CompactData.T CompactData.F g005 = true := by decide +kernel

def g006 : Tag := .inr ⟨(9 / 100 : ℚ), (19 / 200 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (37 / 400 : ℚ), (31 / 800 : ℚ), (0, 13), (2, 1), (1, 14), (1, 7), [(0, 12), (0, 13), (0, 14)], [(2, 0), (2, 1), (2, 2)], [(1, 13), (1, 14), (1, 15)], [(1, 6), (1, 7)]⟩

theorem g006_ok : tagOKF CompactData.T CompactData.F g006 = true := by decide +kernel

def g007 : Tag := .inr ⟨(19 / 200 : ℚ), (1 / 10 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (39 / 400 : ℚ), (31 / 800 : ℚ), (0, 13), (2, 2), (1, 15), (1, 8), [(0, 12), (0, 13), (0, 14)], [(2, 1), (2, 2)], [(1, 14), (1, 15)], [(1, 7), (1, 8)]⟩

theorem g007_ok : tagOKF CompactData.T CompactData.F g007 = true := by decide +kernel

def g008 : Tag := .inr ⟨(1 / 10 : ℚ), (21 / 200 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (41 / 400 : ℚ), (1 / 32 : ℚ), (0, 9), (2, 2), (1, 14), (1, 9), [(0, 8), (0, 9)], [(2, 2), (2, 3)], [(1, 14), (1, 15)], [(1, 8), (1, 9)]⟩

theorem g008_ok : tagOKF CompactData.T CompactData.F g008 = true := by decide +kernel

def g009 : Tag := .inr ⟨(21 / 200 : ℚ), (11 / 100 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (43 / 400 : ℚ), (1 / 32 : ℚ), (0, 9), (2, 3), (1, 15), (1, 10), [(0, 8), (0, 9)], [(2, 2), (2, 3)], [(1, 15), (1, 16)], [(1, 9), (1, 10)]⟩

theorem g009_ok : tagOKF CompactData.T CompactData.F g009 = true := by decide +kernel

def g010 : Tag := .inr ⟨(1 / 10 : ℚ), (21 / 200 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (41 / 400 : ℚ), (27 / 800 : ℚ), (0, 10), (2, 2), (1, 15), (1, 9), [(0, 9), (0, 10), (0, 11)], [(2, 2), (2, 3)], [(1, 14), (1, 15)], [(1, 8), (1, 9)]⟩

theorem g010_ok : tagOKF CompactData.T CompactData.F g010 = true := by decide +kernel

def g011 : Tag := .inr ⟨(21 / 200 : ℚ), (11 / 100 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (43 / 400 : ℚ), (27 / 800 : ℚ), (0, 10), (2, 3), (1, 16), (1, 10), [(0, 9), (0, 10), (0, 11)], [(2, 3), (2, 4)], [(1, 15), (1, 16)], [(1, 9), (1, 10)]⟩

theorem g011_ok : tagOKF CompactData.T CompactData.F g011 = true := by decide +kernel

def g012 : Tag := .inr ⟨(11 / 100 : ℚ), (23 / 200 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (9 / 80 : ℚ), (1 / 32 : ℚ), (0, 9), (2, 4), (1, 16), (1, 11), [(0, 8), (0, 9)], [(2, 3), (2, 4)], [(1, 15), (1, 16)], [(1, 10), (1, 11)]⟩

theorem g012_ok : tagOKF CompactData.T CompactData.F g012 = true := by decide +kernel

def g013 : Tag := .inr ⟨(23 / 200 : ℚ), (3 / 25 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (47 / 400 : ℚ), (1 / 32 : ℚ), (0, 9), (2, 5), (1, 17), (1, 12), [(0, 8), (0, 9)], [(2, 4), (2, 5)], [(1, 16), (1, 17)], [(1, 11), (1, 12)]⟩

theorem g013_ok : tagOKF CompactData.T CompactData.F g013 = true := by decide +kernel

def g014 : Tag := .inr ⟨(11 / 100 : ℚ), (23 / 200 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (9 / 80 : ℚ), (27 / 800 : ℚ), (0, 10), (2, 4), (1, 16), (1, 11), [(0, 9), (0, 10), (0, 11)], [(2, 3), (2, 4)], [(1, 16), (1, 17)], [(1, 10), (1, 11)]⟩

theorem g014_ok : tagOKF CompactData.T CompactData.F g014 = true := by decide +kernel

def g015 : Tag := .inr ⟨(23 / 200 : ℚ), (3 / 25 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (47 / 400 : ℚ), (27 / 800 : ℚ), (0, 10), (2, 5), (1, 17), (1, 12), [(0, 9), (0, 10), (0, 11)], [(2, 4), (2, 5)], [(1, 16), (1, 17)], [(1, 11), (1, 12)]⟩

theorem g015_ok : tagOKF CompactData.T CompactData.F g015 = true := by decide +kernel

def g016 : Tag := .inr ⟨(1 / 10 : ℚ), (21 / 200 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (41 / 400 : ℚ), (29 / 800 : ℚ), (0, 12), (2, 3), (1, 15), (1, 9), [(0, 11), (0, 12)], [(2, 2), (2, 3)], [(1, 15), (1, 16)], [(1, 8), (1, 9)]⟩

theorem g016_ok : tagOKF CompactData.T CompactData.F g016 = true := by decide +kernel

def g017 : Tag := .inr ⟨(21 / 200 : ℚ), (11 / 100 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (43 / 400 : ℚ), (29 / 800 : ℚ), (0, 12), (2, 3), (1, 16), (1, 10), [(0, 11), (0, 12)], [(2, 3), (2, 4)], [(1, 15), (1, 16)], [(1, 9), (1, 10)]⟩

theorem g017_ok : tagOKF CompactData.T CompactData.F g017 = true := by decide +kernel

def g018 : Tag := .inr ⟨(1 / 10 : ℚ), (21 / 200 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (41 / 400 : ℚ), (31 / 800 : ℚ), (0, 13), (2, 3), (1, 16), (1, 9), [(0, 12), (0, 13), (0, 14)], [(2, 2), (2, 3)], [(1, 15), (1, 16)], [(1, 8), (1, 9)]⟩

theorem g018_ok : tagOKF CompactData.T CompactData.F g018 = true := by decide +kernel

def g019 : Tag := .inr ⟨(21 / 200 : ℚ), (11 / 100 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (43 / 400 : ℚ), (31 / 800 : ℚ), (0, 13), (2, 4), (1, 16), (1, 10), [(0, 12), (0, 13), (0, 14)], [(2, 3), (2, 4)], [(1, 16), (1, 17)], [(1, 9), (1, 10)]⟩

theorem g019_ok : tagOKF CompactData.T CompactData.F g019 = true := by decide +kernel

def g020 : Tag := .inr ⟨(11 / 100 : ℚ), (23 / 200 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (9 / 80 : ℚ), (29 / 800 : ℚ), (0, 12), (2, 4), (1, 17), (1, 11), [(0, 11), (0, 12)], [(2, 4), (2, 5)], [(1, 16), (1, 17)], [(1, 10), (1, 11)]⟩

theorem g020_ok : tagOKF CompactData.T CompactData.F g020 = true := by decide +kernel

def g021 : Tag := .inr ⟨(23 / 200 : ℚ), (3 / 25 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (47 / 400 : ℚ), (29 / 800 : ℚ), (0, 12), (2, 5), (1, 17), (1, 12), [(0, 11), (0, 12)], [(2, 4), (2, 5)], [(1, 17), (1, 18)], [(1, 11), (1, 12)]⟩

theorem g021_ok : tagOKF CompactData.T CompactData.F g021 = true := by decide +kernel

def g022 : Tag := .inr ⟨(11 / 100 : ℚ), (3 / 25 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (23 / 200 : ℚ), (31 / 800 : ℚ), (0, 13), (2, 5), (1, 17), (1, 11), [(0, 12), (0, 13), (0, 14)], [(2, 4), (2, 5), (2, 6)], [(1, 16), (1, 17), (1, 18)], [(1, 10), (1, 11), (1, 12)]⟩

theorem g022_ok : tagOKF CompactData.T CompactData.F g022 = true := by decide +kernel

def g023 : Tag := .inr ⟨(3 / 25 : ℚ), (1 / 8 : ℚ), (1 / 50 : ℚ), (17 / 800 : ℚ), (49 / 400 : ℚ), (33 / 1600 : ℚ), (0, 0), (2, 5), (1, 16), (1, 13), [(0, 0), (0, 1)], [(2, 4), (2, 5)], [(1, 15), (1, 16)], [(1, 12), (1, 13)]⟩

theorem g023_ok : tagOKF CompactData.T CompactData.F g023 = true := by decide +kernel

def g024 : Tag := .inr ⟨(1 / 8 : ℚ), (13 / 100 : ℚ), (1 / 50 : ℚ), (17 / 800 : ℚ), (51 / 400 : ℚ), (33 / 1600 : ℚ), (0, 0), (2, 5), (1, 17), (1, 13), [(0, 0), (0, 1)], [(2, 5), (2, 6)], [(1, 16), (1, 17)], [(1, 13), (1, 14)]⟩

theorem g024_ok : tagOKF CompactData.T CompactData.F g024 = true := by decide +kernel

def g025 : Tag := .inr ⟨(3 / 25 : ℚ), (1 / 8 : ℚ), (17 / 800 : ℚ), (9 / 400 : ℚ), (49 / 400 : ℚ), (7 / 320 : ℚ), (0, 1), (2, 5), (1, 16), (1, 13), [(0, 1), (0, 2)], [(2, 4), (2, 5)], [(1, 16)], [(1, 12), (1, 13)]⟩

theorem g025_ok : tagOKF CompactData.T CompactData.F g025 = true := by decide +kernel

def g026 : Tag := .inr ⟨(1 / 8 : ℚ), (13 / 100 : ℚ), (17 / 800 : ℚ), (9 / 400 : ℚ), (51 / 400 : ℚ), (7 / 320 : ℚ), (0, 1), (2, 5), (1, 17), (1, 13), [(0, 1), (0, 2)], [(2, 5), (2, 6)], [(1, 16), (1, 17)], [(1, 13), (1, 14)]⟩

theorem g026_ok : tagOKF CompactData.T CompactData.F g026 = true := by decide +kernel

def g027 : Tag := .inr ⟨(13 / 100 : ℚ), (7 / 50 : ℚ), (1 / 50 : ℚ), (17 / 800 : ℚ), (27 / 200 : ℚ), (33 / 1600 : ℚ), (0, 0), (2, 6), (1, 18), (1, 15), [(0, 0), (0, 1)], [(2, 6), (2, 7)], [(1, 17), (1, 18)], [(1, 14), (1, 15)]⟩

theorem g027_ok : tagOKF CompactData.T CompactData.F g027 = true := by decide +kernel

def g028 : Tag := .inr ⟨(13 / 100 : ℚ), (7 / 50 : ℚ), (17 / 800 : ℚ), (9 / 400 : ℚ), (27 / 200 : ℚ), (7 / 320 : ℚ), (0, 1), (2, 6), (1, 18), (1, 15), [(0, 1), (0, 2)], [(2, 6), (2, 7)], [(1, 17), (1, 18)], [(1, 14), (1, 15)]⟩

theorem g028_ok : tagOKF CompactData.T CompactData.F g028 = true := by decide +kernel

def g029 : Tag := .inr ⟨(3 / 25 : ℚ), (1 / 8 : ℚ), (9 / 400 : ℚ), (19 / 800 : ℚ), (49 / 400 : ℚ), (37 / 1600 : ℚ), (0, 2), (2, 5), (1, 16), (1, 13), [(0, 2), (0, 3)], [(2, 4), (2, 5)], [(1, 16), (1, 17)], [(1, 12), (1, 13)]⟩

theorem g029_ok : tagOKF CompactData.T CompactData.F g029 = true := by decide +kernel

def g030 : Tag := .inr ⟨(1 / 8 : ℚ), (13 / 100 : ℚ), (9 / 400 : ℚ), (19 / 800 : ℚ), (51 / 400 : ℚ), (37 / 1600 : ℚ), (0, 2), (2, 5), (1, 17), (1, 13), [(0, 2), (0, 3)], [(2, 5), (2, 6)], [(1, 16), (1, 17)], [(1, 13), (1, 14)]⟩

theorem g030_ok : tagOKF CompactData.T CompactData.F g030 = true := by decide +kernel

def g031 : Tag := .inr ⟨(3 / 25 : ℚ), (13 / 100 : ℚ), (19 / 800 : ℚ), (1 / 40 : ℚ), (1 / 8 : ℚ), (39 / 1600 : ℚ), (0, 4), (2, 5), (1, 17), (1, 13), [(0, 3), (0, 4)], [(2, 4), (2, 5), (2, 6)], [(1, 16), (1, 17)], [(1, 12), (1, 13), (1, 14)]⟩

theorem g031_ok : tagOKF CompactData.T CompactData.F g031 = true := by decide +kernel

def g032 : Tag := .inr ⟨(13 / 100 : ℚ), (7 / 50 : ℚ), (9 / 400 : ℚ), (1 / 40 : ℚ), (27 / 200 : ℚ), (19 / 800 : ℚ), (0, 3), (2, 7), (1, 18), (1, 15), [(0, 2), (0, 3), (0, 4)], [(2, 6), (2, 7)], [(1, 17), (1, 18), (1, 19)], [(1, 14), (1, 15)]⟩

theorem g032_ok : tagOKF CompactData.T CompactData.F g032 = true := by decide +kernel

def g033 : Tag := .inr ⟨(7 / 50 : ℚ), (3 / 20 : ℚ), (1 / 50 : ℚ), (9 / 400 : ℚ), (29 / 200 : ℚ), (17 / 800 : ℚ), (0, 1), (2, 8), (1, 19), (1, 16), [(0, 0), (0, 1), (0, 2)], [(2, 7), (2, 8)], [(1, 18), (1, 19), (1, 20)], [(1, 15), (1, 16), (1, 17)]⟩

theorem g033_ok : tagOKF CompactData.T CompactData.F g033 = true := by decide +kernel

def g034 : Tag := .inr ⟨(3 / 20 : ℚ), (4 / 25 : ℚ), (1 / 50 : ℚ), (9 / 400 : ℚ), (31 / 200 : ℚ), (17 / 800 : ℚ), (0, 1), (2, 9), (1, 20), (1, 17), [(0, 0), (0, 1), (0, 2)], [(2, 8), (2, 9), (2, 10)], [(1, 19), (1, 20), (1, 21)], [(1, 17), (1, 18)]⟩

theorem g034_ok : tagOKF CompactData.T CompactData.F g034 = true := by decide +kernel

def g035 : Tag := .inr ⟨(7 / 50 : ℚ), (3 / 20 : ℚ), (9 / 400 : ℚ), (1 / 40 : ℚ), (29 / 200 : ℚ), (19 / 800 : ℚ), (0, 3), (2, 8), (1, 19), (1, 16), [(0, 2), (0, 3), (0, 4)], [(2, 7), (2, 8), (2, 9)], [(1, 18), (1, 19), (1, 20)], [(1, 15), (1, 16), (1, 17)]⟩

theorem g035_ok : tagOKF CompactData.T CompactData.F g035 = true := by decide +kernel

def g036 : Tag := .inr ⟨(3 / 20 : ℚ), (4 / 25 : ℚ), (9 / 400 : ℚ), (1 / 40 : ℚ), (31 / 200 : ℚ), (19 / 800 : ℚ), (0, 3), (2, 9), (1, 20), (1, 17), [(0, 2), (0, 3), (0, 4)], [(2, 8), (2, 9), (2, 10)], [(1, 20), (1, 21)], [(1, 17), (1, 18)]⟩

theorem g036_ok : tagOKF CompactData.T CompactData.F g036 = true := by decide +kernel

def g037 : Tag := .inr ⟨(3 / 25 : ℚ), (13 / 100 : ℚ), (1 / 40 : ℚ), (21 / 800 : ℚ), (1 / 8 : ℚ), (41 / 1600 : ℚ), (0, 5), (2, 5), (1, 17), (1, 13), [(0, 4), (0, 5)], [(2, 4), (2, 5), (2, 6)], [(1, 16), (1, 17), (1, 18)], [(1, 12), (1, 13), (1, 14)]⟩

theorem g037_ok : tagOKF CompactData.T CompactData.F g037 = true := by decide +kernel

def g038 : Tag := .inr ⟨(3 / 25 : ℚ), (13 / 100 : ℚ), (21 / 800 : ℚ), (11 / 400 : ℚ), (1 / 8 : ℚ), (43 / 1600 : ℚ), (0, 6), (2, 5), (1, 17), (1, 13), [(0, 5), (0, 6)], [(2, 5), (2, 6)], [(1, 16), (1, 17), (1, 18)], [(1, 12), (1, 13), (1, 14)]⟩

theorem g038_ok : tagOKF CompactData.T CompactData.F g038 = true := by decide +kernel

def g039 : Tag := .inr ⟨(13 / 100 : ℚ), (7 / 50 : ℚ), (1 / 40 : ℚ), (11 / 400 : ℚ), (27 / 200 : ℚ), (21 / 800 : ℚ), (0, 5), (2, 7), (1, 18), (1, 15), [(0, 4), (0, 5), (0, 6)], [(2, 6), (2, 7), (2, 8)], [(1, 17), (1, 18), (1, 19)], [(1, 14), (1, 15)]⟩

theorem g039_ok : tagOKF CompactData.T CompactData.F g039 = true := by decide +kernel

def g040 : Tag := .inr ⟨(3 / 25 : ℚ), (13 / 100 : ℚ), (11 / 400 : ℚ), (23 / 800 : ℚ), (1 / 8 : ℚ), (9 / 320 : ℚ), (0, 6), (2, 5), (1, 17), (1, 13), [(0, 6), (0, 7)], [(2, 5), (2, 6)], [(1, 16), (1, 17), (1, 18)], [(1, 12), (1, 13), (1, 14)]⟩

theorem g040_ok : tagOKF CompactData.T CompactData.F g040 = true := by decide +kernel

def g041 : Tag := .inr ⟨(3 / 25 : ℚ), (13 / 100 : ℚ), (23 / 800 : ℚ), (3 / 100 : ℚ), (1 / 8 : ℚ), (47 / 1600 : ℚ), (0, 7), (2, 6), (1, 17), (1, 13), [(0, 7), (0, 8)], [(2, 5), (2, 6)], [(1, 17), (1, 18)], [(1, 12), (1, 13), (1, 14)]⟩

theorem g041_ok : tagOKF CompactData.T CompactData.F g041 = true := by decide +kernel

def g042 : Tag := .inr ⟨(13 / 100 : ℚ), (7 / 50 : ℚ), (11 / 400 : ℚ), (3 / 100 : ℚ), (27 / 200 : ℚ), (23 / 800 : ℚ), (0, 7), (2, 7), (1, 19), (1, 15), [(0, 6), (0, 7), (0, 8)], [(2, 6), (2, 7), (2, 8)], [(1, 18), (1, 19)], [(1, 14), (1, 15)]⟩

theorem g042_ok : tagOKF CompactData.T CompactData.F g042 = true := by decide +kernel

def g043 : Tag := .inr ⟨(7 / 50 : ℚ), (3 / 20 : ℚ), (1 / 40 : ℚ), (11 / 400 : ℚ), (29 / 200 : ℚ), (21 / 800 : ℚ), (0, 5), (2, 8), (1, 20), (1, 16), [(0, 4), (0, 5), (0, 6)], [(2, 7), (2, 8), (2, 9)], [(1, 19), (1, 20)], [(1, 15), (1, 16), (1, 17)]⟩

theorem g043_ok : tagOKF CompactData.T CompactData.F g043 = true := by decide +kernel

def g044 : Tag := .inr ⟨(3 / 20 : ℚ), (4 / 25 : ℚ), (1 / 40 : ℚ), (11 / 400 : ℚ), (31 / 200 : ℚ), (21 / 800 : ℚ), (0, 5), (2, 9), (1, 21), (1, 17), [(0, 4), (0, 5), (0, 6)], [(2, 9), (2, 10)], [(1, 20), (1, 21)], [(1, 17), (1, 18)]⟩

theorem g044_ok : tagOKF CompactData.T CompactData.F g044 = true := by decide +kernel

def g045 : Tag := .inr ⟨(7 / 50 : ℚ), (3 / 20 : ℚ), (11 / 400 : ℚ), (3 / 100 : ℚ), (29 / 200 : ℚ), (23 / 800 : ℚ), (0, 7), (2, 8), (1, 20), (1, 16), [(0, 6), (0, 7), (0, 8)], [(2, 8), (2, 9)], [(1, 19), (1, 20), (1, 21)], [(1, 15), (1, 16), (1, 17)]⟩

theorem g045_ok : tagOKF CompactData.T CompactData.F g045 = true := by decide +kernel

def g046 : Tag := .inr ⟨(3 / 20 : ℚ), (4 / 25 : ℚ), (11 / 400 : ℚ), (3 / 100 : ℚ), (31 / 200 : ℚ), (23 / 800 : ℚ), (0, 7), (2, 9), (1, 21), (1, 17), [(0, 6), (0, 7), (0, 8)], [(2, 9), (2, 10)], [(1, 20), (1, 21), (1, 22)], [(1, 17), (1, 18)]⟩

theorem g046_ok : tagOKF CompactData.T CompactData.F g046 = true := by decide +kernel

def g047 : Tag := .inr ⟨(3 / 25 : ℚ), (13 / 100 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (1 / 8 : ℚ), (1 / 32 : ℚ), (0, 9), (2, 6), (1, 18), (1, 13), [(0, 8), (0, 9)], [(2, 5), (2, 6)], [(1, 17), (1, 18)], [(1, 12), (1, 13), (1, 14)]⟩

theorem g047_ok : tagOKF CompactData.T CompactData.F g047 = true := by decide +kernel

def g048 : Tag := .inr ⟨(3 / 25 : ℚ), (13 / 100 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (1 / 8 : ℚ), (27 / 800 : ℚ), (0, 10), (2, 6), (1, 18), (1, 13), [(0, 9), (0, 10), (0, 11)], [(2, 5), (2, 6), (2, 7)], [(1, 17), (1, 18), (1, 19)], [(1, 12), (1, 13), (1, 14)]⟩

theorem g048_ok : tagOKF CompactData.T CompactData.F g048 = true := by decide +kernel

def g049 : Tag := .inr ⟨(13 / 100 : ℚ), (7 / 50 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (27 / 200 : ℚ), (1 / 32 : ℚ), (0, 9), (2, 7), (1, 19), (1, 15), [(0, 8), (0, 9)], [(2, 6), (2, 7), (2, 8)], [(1, 18), (1, 19), (1, 20)], [(1, 14), (1, 15)]⟩

theorem g049_ok : tagOKF CompactData.T CompactData.F g049 = true := by decide +kernel

def g050 : Tag := .inr ⟨(13 / 100 : ℚ), (7 / 50 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (27 / 200 : ℚ), (27 / 800 : ℚ), (0, 10), (2, 7), (1, 19), (1, 15), [(0, 9), (0, 10), (0, 11)], [(2, 6), (2, 7), (2, 8)], [(1, 18), (1, 19), (1, 20)], [(1, 14), (1, 15)]⟩

theorem g050_ok : tagOKF CompactData.T CompactData.F g050 = true := by decide +kernel

def g051 : Tag := .inr ⟨(3 / 25 : ℚ), (13 / 100 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (1 / 8 : ℚ), (29 / 800 : ℚ), (0, 12), (2, 6), (1, 18), (1, 13), [(0, 11), (0, 12)], [(2, 5), (2, 6), (2, 7)], [(1, 17), (1, 18), (1, 19)], [(1, 12), (1, 13), (1, 14)]⟩

theorem g051_ok : tagOKF CompactData.T CompactData.F g051 = true := by decide +kernel

def g052 : Tag := .inr ⟨(3 / 25 : ℚ), (13 / 100 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (1 / 8 : ℚ), (31 / 800 : ℚ), (0, 13), (2, 6), (1, 19), (1, 13), [(0, 12), (0, 13), (0, 14)], [(2, 5), (2, 6), (2, 7)], [(1, 18), (1, 19)], [(1, 12), (1, 13), (1, 14)]⟩

theorem g052_ok : tagOKF CompactData.T CompactData.F g052 = true := by decide +kernel

def g053 : Tag := .inr ⟨(13 / 100 : ℚ), (7 / 50 : ℚ), (7 / 200 : ℚ), (1 / 25 : ℚ), (27 / 200 : ℚ), (3 / 80 : ℚ), (0, 12), (2, 8), (1, 20), (1, 15), [(0, 11), (0, 12), (0, 13), (0, 14)], [(2, 7), (2, 8)], [(1, 19), (1, 20), (1, 21)], [(1, 14), (1, 15)]⟩

theorem g053_ok : tagOKF CompactData.T CompactData.F g053 = true := by decide +kernel

def g054 : Tag := .inr ⟨(7 / 50 : ℚ), (3 / 20 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (29 / 200 : ℚ), (1 / 32 : ℚ), (0, 9), (2, 8), (1, 20), (1, 16), [(0, 8), (0, 9)], [(2, 8), (2, 9)], [(1, 19), (1, 20), (1, 21)], [(1, 15), (1, 16), (1, 17)]⟩

theorem g054_ok : tagOKF CompactData.T CompactData.F g054 = true := by decide +kernel

def g055 : Tag := .inr ⟨(3 / 20 : ℚ), (4 / 25 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (31 / 200 : ℚ), (1 / 32 : ℚ), (0, 9), (2, 10), (1, 21), (1, 17), [(0, 8), (0, 9)], [(2, 9), (2, 10)], [(1, 21), (1, 22)], [(1, 17), (1, 18)]⟩

theorem g055_ok : tagOKF CompactData.T CompactData.F g055 = true := by decide +kernel

def g056 : Tag := .inr ⟨(7 / 50 : ℚ), (3 / 20 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (29 / 200 : ℚ), (27 / 800 : ℚ), (0, 10), (2, 9), (1, 20), (1, 16), [(0, 9), (0, 10), (0, 11)], [(2, 8), (2, 9)], [(1, 20), (1, 21)], [(1, 15), (1, 16), (1, 17)]⟩

theorem g056_ok : tagOKF CompactData.T CompactData.F g056 = true := by decide +kernel

def g057 : Tag := .inr ⟨(3 / 20 : ℚ), (4 / 25 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (31 / 200 : ℚ), (27 / 800 : ℚ), (0, 10), (2, 10), (1, 22), (1, 17), [(0, 9), (0, 10), (0, 11)], [(2, 9), (2, 10)], [(1, 21), (1, 22)], [(1, 17), (1, 18)]⟩

theorem g057_ok : tagOKF CompactData.T CompactData.F g057 = true := by decide +kernel

def g058 : Tag := .inr ⟨(7 / 50 : ℚ), (3 / 20 : ℚ), (7 / 200 : ℚ), (1 / 25 : ℚ), (29 / 200 : ℚ), (3 / 80 : ℚ), (0, 12), (2, 9), (1, 21), (1, 16), [(0, 11), (0, 12), (0, 13), (0, 14)], [(2, 8), (2, 9), (2, 10)], [(1, 20), (1, 21), (1, 22)], [(1, 15), (1, 16), (1, 17)]⟩

theorem g058_ok : tagOKF CompactData.T CompactData.F g058 = true := by decide +kernel

def g059 : Tag := .inr ⟨(3 / 20 : ℚ), (4 / 25 : ℚ), (7 / 200 : ℚ), (1 / 25 : ℚ), (31 / 200 : ℚ), (3 / 80 : ℚ), (0, 12), (2, 10), (1, 22), (1, 17), [(0, 11), (0, 12), (0, 13), (0, 14)], [(2, 9), (2, 10), (2, 11)], [(1, 21), (1, 22), (1, 23)], [(1, 17), (1, 18)]⟩

theorem g059_ok : tagOKF CompactData.T CompactData.F g059 = true := by decide +kernel

def g060 : Tag := .inr ⟨(2 / 25 : ℚ), (17 / 200 : ℚ), (1 / 25 : ℚ), (9 / 200 : ℚ), (33 / 400 : ℚ), (17 / 400 : ℚ), (0, 15), (1, 23), (1, 13), (1, 5), [(0, 14), (0, 15), (0, 16)], [(1, 23), (2, 0)], [(1, 12), (1, 13), (1, 14)], [(1, 4), (1, 5)]⟩

theorem g060_ok : tagOKF CompactData.T CompactData.F g060 = true := by decide +kernel

def g061 : Tag := .inr ⟨(17 / 200 : ℚ), (9 / 100 : ℚ), (1 / 25 : ℚ), (9 / 200 : ℚ), (7 / 80 : ℚ), (17 / 400 : ℚ), (0, 15), (2, 0), (1, 14), (1, 6), [(0, 14), (0, 15), (0, 16)], [(2, 0), (2, 1)], [(1, 13), (1, 14), (1, 15)], [(1, 5), (1, 6)]⟩

theorem g061_ok : tagOKF CompactData.T CompactData.F g061 = true := by decide +kernel

def g062 : Tag := .inr ⟨(2 / 25 : ℚ), (17 / 200 : ℚ), (9 / 200 : ℚ), (1 / 20 : ℚ), (33 / 400 : ℚ), (19 / 400 : ℚ), (0, 17), (2, 0), (1, 14), (1, 5), [(0, 16), (0, 17), (0, 18)], [(1, 23), (2, 0), (2, 1)], [(1, 13), (1, 14), (1, 15)], [(1, 4), (1, 5)]⟩

theorem g062_ok : tagOKF CompactData.T CompactData.F g062 = true := by decide +kernel

def g063 : Tag := .inr ⟨(17 / 200 : ℚ), (9 / 100 : ℚ), (9 / 200 : ℚ), (1 / 20 : ℚ), (7 / 80 : ℚ), (19 / 400 : ℚ), (0, 17), (2, 1), (1, 15), (1, 6), [(0, 16), (0, 17), (0, 18)], [(2, 0), (2, 1), (2, 2)], [(1, 14), (1, 15)], [(1, 5), (1, 6)]⟩

theorem g063_ok : tagOKF CompactData.T CompactData.F g063 = true := by decide +kernel

def g064 : Tag := .inr ⟨(9 / 100 : ℚ), (19 / 200 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (37 / 400 : ℚ), (33 / 800 : ℚ), (0, 14), (2, 1), (1, 14), (1, 7), [(0, 14), (0, 15)], [(2, 1), (2, 2)], [(1, 14), (1, 15)], [(1, 6), (1, 7)]⟩

theorem g064_ok : tagOKF CompactData.T CompactData.F g064 = true := by decide +kernel

def g065 : Tag := .inr ⟨(19 / 200 : ℚ), (1 / 10 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (39 / 400 : ℚ), (33 / 800 : ℚ), (0, 14), (2, 2), (1, 15), (1, 8), [(0, 14), (0, 15)], [(2, 2), (2, 3)], [(1, 15), (1, 16)], [(1, 7), (1, 8)]⟩

theorem g065_ok : tagOKF CompactData.T CompactData.F g065 = true := by decide +kernel

def g066 : Tag := .inr ⟨(9 / 100 : ℚ), (19 / 200 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (37 / 400 : ℚ), (7 / 160 : ℚ), (0, 16), (2, 1), (1, 15), (1, 7), [(0, 15), (0, 16)], [(2, 1), (2, 2)], [(1, 14), (1, 15)], [(1, 6), (1, 7)]⟩

theorem g066_ok : tagOKF CompactData.T CompactData.F g066 = true := by decide +kernel

def g067 : Tag := .inr ⟨(19 / 200 : ℚ), (1 / 10 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (39 / 400 : ℚ), (7 / 160 : ℚ), (0, 16), (2, 2), (1, 16), (1, 8), [(0, 15), (0, 16)], [(2, 2), (2, 3)], [(1, 15), (1, 16)], [(1, 7), (1, 8)]⟩

theorem g067_ok : tagOKF CompactData.T CompactData.F g067 = true := by decide +kernel

def g068 : Tag := .inr ⟨(9 / 100 : ℚ), (19 / 200 : ℚ), (9 / 200 : ℚ), (1 / 20 : ℚ), (37 / 400 : ℚ), (19 / 400 : ℚ), (0, 17), (2, 2), (1, 15), (1, 7), [(0, 16), (0, 17), (0, 18)], [(2, 1), (2, 2)], [(1, 15), (1, 16)], [(1, 6), (1, 7)]⟩

theorem g068_ok : tagOKF CompactData.T CompactData.F g068 = true := by decide +kernel

def g069 : Tag := .inr ⟨(19 / 200 : ℚ), (1 / 10 : ℚ), (9 / 200 : ℚ), (1 / 20 : ℚ), (39 / 400 : ℚ), (19 / 400 : ℚ), (0, 17), (2, 3), (1, 16), (1, 8), [(0, 16), (0, 17), (0, 18)], [(2, 2), (2, 3)], [(1, 15), (1, 16), (1, 17)], [(1, 7), (1, 8)]⟩

theorem g069_ok : tagOKF CompactData.T CompactData.F g069 = true := by decide +kernel

def g070 : Tag := .inr ⟨(2 / 25 : ℚ), (17 / 200 : ℚ), (1 / 20 : ℚ), (11 / 200 : ℚ), (33 / 400 : ℚ), (21 / 400 : ℚ), (0, 19), (2, 0), (1, 15), (1, 5), [(0, 18), (0, 19), (0, 20)], [(2, 0), (2, 1)], [(1, 14), (1, 15)], [(1, 4), (1, 5)]⟩

theorem g070_ok : tagOKF CompactData.T CompactData.F g070 = true := by decide +kernel

def g071 : Tag := .inr ⟨(17 / 200 : ℚ), (9 / 100 : ℚ), (1 / 20 : ℚ), (11 / 200 : ℚ), (7 / 80 : ℚ), (21 / 400 : ℚ), (0, 19), (2, 1), (1, 15), (1, 6), [(0, 18), (0, 19), (0, 20)], [(2, 1), (2, 2)], [(1, 15), (1, 16)], [(1, 5), (1, 6)]⟩

theorem g071_ok : tagOKF CompactData.T CompactData.F g071 = true := by decide +kernel

def g072 : Tag := .inr ⟨(2 / 25 : ℚ), (17 / 200 : ℚ), (11 / 200 : ℚ), (3 / 50 : ℚ), (33 / 400 : ℚ), (23 / 400 : ℚ), (0, 21), (2, 1), (1, 15), (1, 5), [(0, 20), (0, 21), (0, 22)], [(2, 0), (2, 1), (2, 2)], [(1, 15), (1, 16)], [(1, 4), (1, 5)]⟩

theorem g072_ok : tagOKF CompactData.T CompactData.F g072 = true := by decide +kernel

def g073 : Tag := .inr ⟨(17 / 200 : ℚ), (9 / 100 : ℚ), (11 / 200 : ℚ), (3 / 50 : ℚ), (7 / 80 : ℚ), (23 / 400 : ℚ), (0, 21), (2, 2), (1, 16), (1, 6), [(0, 20), (0, 21), (0, 22)], [(2, 1), (2, 2)], [(1, 15), (1, 16), (1, 17)], [(1, 5), (1, 6)]⟩

theorem g073_ok : tagOKF CompactData.T CompactData.F g073 = true := by decide +kernel

def g074 : Tag := .inr ⟨(9 / 100 : ℚ), (19 / 200 : ℚ), (1 / 20 : ℚ), (11 / 200 : ℚ), (37 / 400 : ℚ), (21 / 400 : ℚ), (0, 19), (2, 2), (1, 16), (1, 7), [(0, 18), (0, 19), (0, 20)], [(2, 2), (2, 3)], [(1, 15), (1, 16), (1, 17)], [(1, 6), (1, 7)]⟩

theorem g074_ok : tagOKF CompactData.T CompactData.F g074 = true := by decide +kernel

def g075 : Tag := .inr ⟨(19 / 200 : ℚ), (1 / 10 : ℚ), (1 / 20 : ℚ), (11 / 200 : ℚ), (39 / 400 : ℚ), (21 / 400 : ℚ), (0, 19), (2, 3), (1, 17), (1, 8), [(0, 18), (0, 19), (0, 20)], [(2, 2), (2, 3), (2, 4)], [(1, 16), (1, 17)], [(1, 7), (1, 8)]⟩

theorem g075_ok : tagOKF CompactData.T CompactData.F g075 = true := by decide +kernel

def g076 : Tag := .inr ⟨(9 / 100 : ℚ), (19 / 200 : ℚ), (11 / 200 : ℚ), (3 / 50 : ℚ), (37 / 400 : ℚ), (23 / 400 : ℚ), (0, 21), (2, 3), (1, 17), (1, 7), [(0, 20), (0, 21), (0, 22)], [(2, 2), (2, 3)], [(1, 16), (1, 17)], [(1, 6), (1, 7)]⟩

theorem g076_ok : tagOKF CompactData.T CompactData.F g076 = true := by decide +kernel

def g077 : Tag := .inr ⟨(19 / 200 : ℚ), (1 / 10 : ℚ), (11 / 200 : ℚ), (3 / 50 : ℚ), (39 / 400 : ℚ), (23 / 400 : ℚ), (0, 21), (2, 3), (1, 17), (1, 8), [(0, 20), (0, 21), (0, 22)], [(2, 3), (2, 4)], [(1, 17), (1, 18)], [(1, 7), (1, 8)]⟩

theorem g077_ok : tagOKF CompactData.T CompactData.F g077 = true := by decide +kernel

def g078 : Tag := .inr ⟨(1 / 10 : ℚ), (21 / 200 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (41 / 400 : ℚ), (33 / 800 : ℚ), (0, 14), (2, 3), (1, 16), (1, 9), [(0, 14), (0, 15)], [(2, 2), (2, 3)], [(1, 15), (1, 16)], [(1, 8), (1, 9)]⟩

theorem g078_ok : tagOKF CompactData.T CompactData.F g078 = true := by decide +kernel

def g079 : Tag := .inr ⟨(21 / 200 : ℚ), (11 / 100 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (43 / 400 : ℚ), (33 / 800 : ℚ), (0, 14), (2, 4), (1, 17), (1, 10), [(0, 14), (0, 15)], [(2, 3), (2, 4)], [(1, 16), (1, 17)], [(1, 9), (1, 10)]⟩

theorem g079_ok : tagOKF CompactData.T CompactData.F g079 = true := by decide +kernel

def g080 : Tag := .inr ⟨(1 / 10 : ℚ), (21 / 200 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (41 / 400 : ℚ), (7 / 160 : ℚ), (0, 16), (2, 3), (1, 16), (1, 9), [(0, 15), (0, 16)], [(2, 3), (2, 4)], [(1, 16), (1, 17)], [(1, 8), (1, 9)]⟩

theorem g080_ok : tagOKF CompactData.T CompactData.F g080 = true := by decide +kernel

def g081 : Tag := .inr ⟨(21 / 200 : ℚ), (11 / 100 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (43 / 400 : ℚ), (7 / 160 : ℚ), (0, 16), (2, 4), (1, 17), (1, 10), [(0, 15), (0, 16)], [(2, 3), (2, 4)], [(1, 16), (1, 17)], [(1, 9), (1, 10)]⟩

theorem g081_ok : tagOKF CompactData.T CompactData.F g081 = true := by decide +kernel

def g082 : Tag := .inr ⟨(11 / 100 : ℚ), (3 / 25 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (23 / 200 : ℚ), (33 / 800 : ℚ), (0, 14), (2, 5), (1, 18), (1, 11), [(0, 14), (0, 15)], [(2, 4), (2, 5), (2, 6)], [(1, 17), (1, 18)], [(1, 10), (1, 11), (1, 12)]⟩

theorem g082_ok : tagOKF CompactData.T CompactData.F g082 = true := by decide +kernel

def g083 : Tag := .inr ⟨(11 / 100 : ℚ), (3 / 25 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (23 / 200 : ℚ), (7 / 160 : ℚ), (0, 16), (2, 5), (1, 18), (1, 11), [(0, 15), (0, 16)], [(2, 4), (2, 5), (2, 6)], [(1, 17), (1, 18), (1, 19)], [(1, 10), (1, 11), (1, 12)]⟩

theorem g083_ok : tagOKF CompactData.T CompactData.F g083 = true := by decide +kernel

def g084 : Tag := .inr ⟨(1 / 10 : ℚ), (21 / 200 : ℚ), (9 / 200 : ℚ), (19 / 400 : ℚ), (41 / 400 : ℚ), (37 / 800 : ℚ), (0, 17), (2, 3), (1, 17), (1, 9), [(0, 16), (0, 17)], [(2, 3), (2, 4)], [(1, 16), (1, 17)], [(1, 8), (1, 9)]⟩

theorem g084_ok : tagOKF CompactData.T CompactData.F g084 = true := by decide +kernel

def g085 : Tag := .inr ⟨(21 / 200 : ℚ), (11 / 100 : ℚ), (9 / 200 : ℚ), (19 / 400 : ℚ), (43 / 400 : ℚ), (37 / 800 : ℚ), (0, 17), (2, 4), (1, 17), (1, 10), [(0, 16), (0, 17)], [(2, 4), (2, 5)], [(1, 17), (1, 18)], [(1, 9), (1, 10)]⟩

theorem g085_ok : tagOKF CompactData.T CompactData.F g085 = true := by decide +kernel

def g086 : Tag := .inr ⟨(1 / 10 : ℚ), (11 / 100 : ℚ), (19 / 400 : ℚ), (1 / 20 : ℚ), (21 / 200 : ℚ), (39 / 800 : ℚ), (0, 18), (2, 4), (1, 17), (1, 9), [(0, 17), (0, 18)], [(2, 3), (2, 4), (2, 5)], [(1, 16), (1, 17), (1, 18)], [(1, 8), (1, 9), (1, 10)]⟩

theorem g086_ok : tagOKF CompactData.T CompactData.F g086 = true := by decide +kernel

def g087 : Tag := .inr ⟨(11 / 100 : ℚ), (3 / 25 : ℚ), (9 / 200 : ℚ), (19 / 400 : ℚ), (23 / 200 : ℚ), (37 / 800 : ℚ), (0, 17), (2, 5), (1, 18), (1, 11), [(0, 16), (0, 17)], [(2, 4), (2, 5), (2, 6)], [(1, 17), (1, 18), (1, 19)], [(1, 10), (1, 11), (1, 12)]⟩

theorem g087_ok : tagOKF CompactData.T CompactData.F g087 = true := by decide +kernel

def g088 : Tag := .inr ⟨(11 / 100 : ℚ), (3 / 25 : ℚ), (19 / 400 : ℚ), (1 / 20 : ℚ), (23 / 200 : ℚ), (39 / 800 : ℚ), (0, 18), (2, 5), (1, 19), (1, 11), [(0, 17), (0, 18)], [(2, 5), (2, 6)], [(1, 18), (1, 19)], [(1, 10), (1, 11), (1, 12)]⟩

theorem g088_ok : tagOKF CompactData.T CompactData.F g088 = true := by decide +kernel

def g089 : Tag := .inr ⟨(1 / 10 : ℚ), (21 / 200 : ℚ), (1 / 20 : ℚ), (11 / 200 : ℚ), (41 / 400 : ℚ), (21 / 400 : ℚ), (0, 19), (2, 4), (1, 17), (1, 9), [(0, 18), (0, 19), (0, 20)], [(2, 3), (2, 4)], [(1, 17), (1, 18)], [(1, 8), (1, 9)]⟩

theorem g089_ok : tagOKF CompactData.T CompactData.F g089 = true := by decide +kernel

def g090 : Tag := .inr ⟨(21 / 200 : ℚ), (11 / 100 : ℚ), (1 / 20 : ℚ), (11 / 200 : ℚ), (43 / 400 : ℚ), (21 / 400 : ℚ), (0, 19), (2, 5), (1, 18), (1, 10), [(0, 18), (0, 19), (0, 20)], [(2, 4), (2, 5)], [(1, 17), (1, 18), (1, 19)], [(1, 9), (1, 10)]⟩

theorem g090_ok : tagOKF CompactData.T CompactData.F g090 = true := by decide +kernel

def g091 : Tag := .inr ⟨(1 / 10 : ℚ), (21 / 200 : ℚ), (11 / 200 : ℚ), (3 / 50 : ℚ), (41 / 400 : ℚ), (23 / 400 : ℚ), (0, 21), (2, 4), (1, 18), (1, 9), [(0, 20), (0, 21), (0, 22)], [(2, 4), (2, 5)], [(1, 17), (1, 18), (1, 19)], [(1, 8), (1, 9)]⟩

theorem g091_ok : tagOKF CompactData.T CompactData.F g091 = true := by decide +kernel

def g092 : Tag := .inr ⟨(21 / 200 : ℚ), (11 / 100 : ℚ), (11 / 200 : ℚ), (3 / 50 : ℚ), (43 / 400 : ℚ), (23 / 400 : ℚ), (0, 21), (2, 5), (1, 19), (1, 10), [(0, 20), (0, 21), (0, 22)], [(2, 4), (2, 5), (2, 6)], [(1, 18), (1, 19)], [(1, 9), (1, 10)]⟩

theorem g092_ok : tagOKF CompactData.T CompactData.F g092 = true := by decide +kernel

def g093 : Tag := .inr ⟨(11 / 100 : ℚ), (3 / 25 : ℚ), (1 / 20 : ℚ), (21 / 400 : ℚ), (23 / 200 : ℚ), (41 / 800 : ℚ), (0, 19), (2, 6), (1, 19), (1, 11), [(0, 18), (0, 19)], [(2, 5), (2, 6)], [(1, 18), (1, 19), (1, 20)], [(1, 10), (1, 11), (1, 12)]⟩

theorem g093_ok : tagOKF CompactData.T CompactData.F g093 = true := by decide +kernel

def g094 : Tag := .inr ⟨(11 / 100 : ℚ), (3 / 25 : ℚ), (21 / 400 : ℚ), (11 / 200 : ℚ), (23 / 200 : ℚ), (43 / 800 : ℚ), (0, 20), (2, 6), (1, 19), (1, 11), [(0, 19), (0, 20)], [(2, 5), (2, 6), (2, 7)], [(1, 18), (1, 19), (1, 20)], [(1, 10), (1, 11), (1, 12)]⟩

theorem g094_ok : tagOKF CompactData.T CompactData.F g094 = true := by decide +kernel

def g095 : Tag := .inr ⟨(11 / 100 : ℚ), (3 / 25 : ℚ), (11 / 200 : ℚ), (3 / 50 : ℚ), (23 / 200 : ℚ), (23 / 400 : ℚ), (0, 21), (2, 6), (1, 20), (1, 11), [(0, 20), (0, 21), (0, 22)], [(2, 5), (2, 6), (2, 7)], [(1, 19), (1, 20), (1, 21)], [(1, 10), (1, 11), (1, 12)]⟩

theorem g095_ok : tagOKF CompactData.T CompactData.F g095 = true := by decide +kernel

def g096 : Tag := .inr ⟨(2 / 25 : ℚ), (17 / 200 : ℚ), (3 / 50 : ℚ), (13 / 200 : ℚ), (33 / 400 : ℚ), (1 / 16 : ℚ), (0, 23), (2, 1), (1, 16), (1, 5), [(0, 22), (0, 23), (1, 0)], [(2, 1), (2, 2)], [(1, 15), (1, 16), (1, 17)], [(1, 4), (1, 5)]⟩

theorem g096_ok : tagOKF CompactData.T CompactData.F g096 = true := by decide +kernel

def g097 : Tag := .inr ⟨(17 / 200 : ℚ), (9 / 100 : ℚ), (3 / 50 : ℚ), (13 / 200 : ℚ), (7 / 80 : ℚ), (1 / 16 : ℚ), (0, 23), (2, 2), (1, 17), (1, 6), [(0, 22), (0, 23), (1, 0)], [(2, 2), (2, 3)], [(1, 16), (1, 17)], [(1, 5), (1, 6)]⟩

theorem g097_ok : tagOKF CompactData.T CompactData.F g097 = true := by decide +kernel

def g098 : Tag := .inr ⟨(2 / 25 : ℚ), (17 / 200 : ℚ), (13 / 200 : ℚ), (7 / 100 : ℚ), (33 / 400 : ℚ), (27 / 400 : ℚ), (1, 0), (2, 2), (1, 17), (1, 5), [(1, 0), (1, 1)], [(2, 1), (2, 2)], [(1, 16), (1, 17)], [(1, 4), (1, 5)]⟩

theorem g098_ok : tagOKF CompactData.T CompactData.F g098 = true := by decide +kernel

def g099 : Tag := .inr ⟨(17 / 200 : ℚ), (9 / 100 : ℚ), (13 / 200 : ℚ), (7 / 100 : ℚ), (7 / 80 : ℚ), (27 / 400 : ℚ), (1, 0), (2, 3), (1, 17), (1, 6), [(1, 0), (1, 1)], [(2, 2), (2, 3)], [(1, 17), (1, 18)], [(1, 5), (1, 6)]⟩

theorem g099_ok : tagOKF CompactData.T CompactData.F g099 = true := by decide +kernel

def g100 : Tag := .inr ⟨(9 / 100 : ℚ), (19 / 200 : ℚ), (3 / 50 : ℚ), (13 / 200 : ℚ), (37 / 400 : ℚ), (1 / 16 : ℚ), (0, 23), (2, 3), (1, 17), (1, 7), [(0, 22), (0, 23), (1, 0)], [(2, 2), (2, 3), (2, 4)], [(1, 17), (1, 18)], [(1, 6), (1, 7)]⟩

theorem g100_ok : tagOKF CompactData.T CompactData.F g100 = true := by decide +kernel

def g101 : Tag := .inr ⟨(19 / 200 : ℚ), (1 / 10 : ℚ), (3 / 50 : ℚ), (13 / 200 : ℚ), (39 / 400 : ℚ), (1 / 16 : ℚ), (0, 23), (2, 4), (1, 18), (1, 8), [(0, 22), (0, 23), (1, 0)], [(2, 3), (2, 4)], [(1, 17), (1, 18), (1, 19)], [(1, 7), (1, 8)]⟩

theorem g101_ok : tagOKF CompactData.T CompactData.F g101 = true := by decide +kernel

def g102 : Tag := .inr ⟨(9 / 100 : ℚ), (19 / 200 : ℚ), (13 / 200 : ℚ), (7 / 100 : ℚ), (37 / 400 : ℚ), (27 / 400 : ℚ), (1, 0), (2, 3), (1, 18), (1, 7), [(1, 0), (1, 1)], [(2, 3), (2, 4)], [(1, 17), (1, 18), (1, 19)], [(1, 6), (1, 7)]⟩

theorem g102_ok : tagOKF CompactData.T CompactData.F g102 = true := by decide +kernel

def g103 : Tag := .inr ⟨(19 / 200 : ℚ), (1 / 10 : ℚ), (13 / 200 : ℚ), (7 / 100 : ℚ), (39 / 400 : ℚ), (27 / 400 : ℚ), (1, 0), (2, 4), (1, 19), (1, 8), [(1, 0), (1, 1)], [(2, 4), (2, 5)], [(1, 18), (1, 19)], [(1, 7), (1, 8)]⟩

theorem g103_ok : tagOKF CompactData.T CompactData.F g103 = true := by decide +kernel

def g104 : Tag := .inr ⟨(2 / 25 : ℚ), (17 / 200 : ℚ), (7 / 100 : ℚ), (3 / 40 : ℚ), (33 / 400 : ℚ), (29 / 400 : ℚ), (1, 2), (2, 2), (1, 17), (1, 5), [(1, 1), (1, 2), (1, 3)], [(2, 2), (2, 3)], [(1, 17), (1, 18)], [(1, 4), (1, 5)]⟩

theorem g104_ok : tagOKF CompactData.T CompactData.F g104 = true := by decide +kernel

def g105 : Tag := .inr ⟨(17 / 200 : ℚ), (9 / 100 : ℚ), (7 / 100 : ℚ), (3 / 40 : ℚ), (7 / 80 : ℚ), (29 / 400 : ℚ), (1, 2), (2, 3), (1, 18), (1, 6), [(1, 1), (1, 2), (1, 3)], [(2, 2), (2, 3), (2, 4)], [(1, 17), (1, 18), (1, 19)], [(1, 5), (1, 6)]⟩

theorem g105_ok : tagOKF CompactData.T CompactData.F g105 = true := by decide +kernel


end CKLaneC3.CompactBatch32


