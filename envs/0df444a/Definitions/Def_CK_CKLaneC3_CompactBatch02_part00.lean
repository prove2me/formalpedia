-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch02_part00
-- name    : CK_CKLaneC3_CompactBatch02_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T20:22:21.566829+00:00
-- url     : https://prove2.me/theorems/d5a78a6f-4864-42d2-b5ed-1439c612ee3b
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch02 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch02 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch02 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch02 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch02 (part 1 of 2).lean)

import Definitions.Def_CK_CKLaneC3_CompactData
import Definitions.Def_CK_CKLaneC3_CompactCoverF

/-! Lane C3 compact cell batch (generated; memoised chains over the data tables). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactBatch02
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF

def g000 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (29 / 200 : ℚ), (3 / 20 : ℚ), (7 / 320 : ℚ), (59 / 400 : ℚ), (1, 16), (1, 22), (1, 19), (0, 1), [(1, 16), (1, 17)], [(1, 21), (1, 22)], [(1, 19), (1, 20)], [(0, 1), (0, 2)]⟩

theorem g000_ok : tagOKF CompactData.T CompactData.F g000 = true := by decide +kernel

def g001 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (3 / 20 : ℚ), (31 / 200 : ℚ), (33 / 1600 : ℚ), (61 / 400 : ℚ), (1, 17), (1, 22), (1, 20), (0, 0), [(1, 17)], [(1, 22)], [(1, 19), (1, 20)], [(0, 0), (0, 1)]⟩

theorem g001_ok : tagOKF CompactData.T CompactData.F g001 = true := by decide +kernel

def g002 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (31 / 200 : ℚ), (4 / 25 : ℚ), (33 / 1600 : ℚ), (63 / 400 : ℚ), (1, 18), (1, 23), (1, 20), (0, 0), [(1, 17), (1, 18)], [(1, 22), (1, 23)], [(1, 20), (1, 21)], [(0, 0), (0, 1)]⟩

theorem g002_ok : tagOKF CompactData.T CompactData.F g002 = true := by decide +kernel

def g003 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (3 / 20 : ℚ), (31 / 200 : ℚ), (7 / 320 : ℚ), (61 / 400 : ℚ), (1, 17), (1, 22), (1, 20), (0, 1), [(1, 17)], [(1, 22), (1, 23)], [(1, 20)], [(0, 1), (0, 2)]⟩

theorem g003_ok : tagOKF CompactData.T CompactData.F g003 = true := by decide +kernel

def g004 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (31 / 200 : ℚ), (4 / 25 : ℚ), (7 / 320 : ℚ), (63 / 400 : ℚ), (1, 18), (1, 23), (1, 20), (0, 1), [(1, 17), (1, 18)], [(1, 22), (1, 23)], [(1, 20), (1, 21)], [(0, 1), (0, 2)]⟩

theorem g004_ok : tagOKF CompactData.T CompactData.F g004 = true := by decide +kernel

def g005 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (7 / 50 : ℚ), (29 / 200 : ℚ), (37 / 1600 : ℚ), (57 / 400 : ℚ), (1, 16), (1, 22), (1, 19), (0, 2), [(1, 15), (1, 16)], [(1, 21), (1, 22)], [(1, 18), (1, 19)], [(0, 2), (0, 3)]⟩

theorem g005_ok : tagOKF CompactData.T CompactData.F g005 = true := by decide +kernel

def g006 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (29 / 200 : ℚ), (3 / 20 : ℚ), (37 / 1600 : ℚ), (59 / 400 : ℚ), (1, 16), (1, 22), (1, 19), (0, 2), [(1, 16), (1, 17)], [(1, 22)], [(1, 19), (1, 20)], [(0, 2), (0, 3)]⟩

theorem g006_ok : tagOKF CompactData.T CompactData.F g006 = true := by decide +kernel

def g007 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (7 / 50 : ℚ), (29 / 200 : ℚ), (39 / 1600 : ℚ), (57 / 400 : ℚ), (1, 16), (1, 22), (1, 19), (0, 4), [(1, 15), (1, 16)], [(1, 21), (1, 22)], [(1, 19)], [(0, 3), (0, 4)]⟩

theorem g007_ok : tagOKF CompactData.T CompactData.F g007 = true := by decide +kernel

def g008 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (29 / 200 : ℚ), (3 / 20 : ℚ), (39 / 1600 : ℚ), (59 / 400 : ℚ), (1, 16), (1, 22), (1, 20), (0, 4), [(1, 16), (1, 17)], [(1, 22), (1, 23)], [(1, 19), (1, 20)], [(0, 3), (0, 4)]⟩

theorem g008_ok : tagOKF CompactData.T CompactData.F g008 = true := by decide +kernel

def g009 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (3 / 20 : ℚ), (31 / 200 : ℚ), (37 / 1600 : ℚ), (61 / 400 : ℚ), (1, 17), (1, 23), (1, 20), (0, 2), [(1, 17)], [(1, 22), (1, 23)], [(1, 20)], [(0, 2), (0, 3)]⟩

theorem g009_ok : tagOKF CompactData.T CompactData.F g009 = true := by decide +kernel

def g010 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (31 / 200 : ℚ), (4 / 25 : ℚ), (37 / 1600 : ℚ), (63 / 400 : ℚ), (1, 18), (1, 23), (1, 21), (0, 2), [(1, 17), (1, 18)], [(1, 23)], [(1, 20), (1, 21)], [(0, 2), (0, 3)]⟩

theorem g010_ok : tagOKF CompactData.T CompactData.F g010 = true := by decide +kernel

def g011 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (3 / 20 : ℚ), (31 / 200 : ℚ), (39 / 1600 : ℚ), (61 / 400 : ℚ), (1, 17), (1, 23), (1, 20), (0, 4), [(1, 17)], [(1, 22), (1, 23)], [(1, 20), (1, 21)], [(0, 3), (0, 4)]⟩

theorem g011_ok : tagOKF CompactData.T CompactData.F g011 = true := by decide +kernel

def g012 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (31 / 200 : ℚ), (4 / 25 : ℚ), (39 / 1600 : ℚ), (63 / 400 : ℚ), (1, 18), (1, 23), (1, 21), (0, 4), [(1, 17), (1, 18)], [(1, 23), (2, 0)], [(1, 20), (1, 21)], [(0, 3), (0, 4)]⟩

theorem g012_ok : tagOKF CompactData.T CompactData.F g012 = true := by decide +kernel

def g013 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (3 / 25 : ℚ), (1 / 8 : ℚ), (41 / 1600 : ℚ), (49 / 400 : ℚ), (1, 13), (1, 20), (1, 17), (0, 5), [(1, 12), (1, 13)], [(1, 19), (1, 20)], [(1, 16), (1, 17)], [(0, 4), (0, 5)]⟩

theorem g013_ok : tagOKF CompactData.T CompactData.F g013 = true := by decide +kernel

def g014 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (1 / 8 : ℚ), (13 / 100 : ℚ), (41 / 1600 : ℚ), (51 / 400 : ℚ), (1, 13), (1, 20), (1, 17), (0, 5), [(1, 13), (1, 14)], [(1, 20), (1, 21)], [(1, 17), (1, 18)], [(0, 4), (0, 5)]⟩

theorem g014_ok : tagOKF CompactData.T CompactData.F g014 = true := by decide +kernel

def g015 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (3 / 25 : ℚ), (1 / 8 : ℚ), (43 / 1600 : ℚ), (49 / 400 : ℚ), (1, 13), (1, 20), (1, 17), (0, 6), [(1, 12), (1, 13)], [(1, 20), (1, 21)], [(1, 16), (1, 17)], [(0, 5), (0, 6)]⟩

theorem g015_ok : tagOKF CompactData.T CompactData.F g015 = true := by decide +kernel

def g016 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (1 / 8 : ℚ), (13 / 100 : ℚ), (43 / 1600 : ℚ), (51 / 400 : ℚ), (1, 13), (1, 21), (1, 17), (0, 6), [(1, 13), (1, 14)], [(1, 20), (1, 21)], [(1, 17), (1, 18)], [(0, 5), (0, 6)]⟩

theorem g016_ok : tagOKF CompactData.T CompactData.F g016 = true := by decide +kernel

def g017 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (13 / 100 : ℚ), (27 / 200 : ℚ), (41 / 1600 : ℚ), (53 / 400 : ℚ), (1, 14), (1, 21), (1, 18), (0, 5), [(1, 14), (1, 15)], [(1, 21)], [(1, 17), (1, 18)], [(0, 4), (0, 5)]⟩

theorem g017_ok : tagOKF CompactData.T CompactData.F g017 = true := by decide +kernel

def g018 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (27 / 200 : ℚ), (7 / 50 : ℚ), (41 / 1600 : ℚ), (11 / 80 : ℚ), (1, 15), (1, 22), (1, 19), (0, 5), [(1, 15)], [(1, 21), (1, 22)], [(1, 18), (1, 19)], [(0, 4), (0, 5)]⟩

theorem g018_ok : tagOKF CompactData.T CompactData.F g018 = true := by decide +kernel

def g019 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (13 / 100 : ℚ), (27 / 200 : ℚ), (43 / 1600 : ℚ), (53 / 400 : ℚ), (1, 14), (1, 21), (1, 18), (0, 6), [(1, 14), (1, 15)], [(1, 21), (1, 22)], [(1, 18)], [(0, 5), (0, 6)]⟩

theorem g019_ok : tagOKF CompactData.T CompactData.F g019 = true := by decide +kernel

def g020 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (27 / 200 : ℚ), (7 / 50 : ℚ), (43 / 1600 : ℚ), (11 / 80 : ℚ), (1, 15), (1, 22), (1, 19), (0, 6), [(1, 15)], [(1, 21), (1, 22)], [(1, 18), (1, 19)], [(0, 5), (0, 6)]⟩

theorem g020_ok : tagOKF CompactData.T CompactData.F g020 = true := by decide +kernel

def g021 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (3 / 25 : ℚ), (1 / 8 : ℚ), (9 / 320 : ℚ), (49 / 400 : ℚ), (1, 13), (1, 20), (1, 17), (0, 6), [(1, 12), (1, 13)], [(1, 20), (1, 21)], [(1, 16), (1, 17)], [(0, 6), (0, 7)]⟩

theorem g021_ok : tagOKF CompactData.T CompactData.F g021 = true := by decide +kernel

def g022 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (1 / 8 : ℚ), (13 / 100 : ℚ), (9 / 320 : ℚ), (51 / 400 : ℚ), (1, 13), (1, 21), (1, 18), (0, 6), [(1, 13), (1, 14)], [(1, 21)], [(1, 17), (1, 18)], [(0, 6), (0, 7)]⟩

theorem g022_ok : tagOKF CompactData.T CompactData.F g022 = true := by decide +kernel

def g023 : Tag := .inr ⟨(23 / 800 : ℚ), (3 / 100 : ℚ), (3 / 25 : ℚ), (1 / 8 : ℚ), (47 / 1600 : ℚ), (49 / 400 : ℚ), (1, 13), (1, 21), (1, 17), (0, 7), [(1, 12), (1, 13)], [(1, 20), (1, 21)], [(1, 17)], [(0, 7), (0, 8)]⟩

theorem g023_ok : tagOKF CompactData.T CompactData.F g023 = true := by decide +kernel

def g024 : Tag := .inr ⟨(23 / 800 : ℚ), (3 / 100 : ℚ), (1 / 8 : ℚ), (13 / 100 : ℚ), (47 / 1600 : ℚ), (51 / 400 : ℚ), (1, 13), (1, 21), (1, 18), (0, 7), [(1, 13), (1, 14)], [(1, 21), (1, 22)], [(1, 17), (1, 18)], [(0, 7), (0, 8)]⟩

theorem g024_ok : tagOKF CompactData.T CompactData.F g024 = true := by decide +kernel

def g025 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (13 / 100 : ℚ), (27 / 200 : ℚ), (9 / 320 : ℚ), (53 / 400 : ℚ), (1, 14), (1, 22), (1, 18), (0, 6), [(1, 14), (1, 15)], [(1, 21), (1, 22)], [(1, 18), (1, 19)], [(0, 6), (0, 7)]⟩

theorem g025_ok : tagOKF CompactData.T CompactData.F g025 = true := by decide +kernel

def g026 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (27 / 200 : ℚ), (7 / 50 : ℚ), (9 / 320 : ℚ), (11 / 80 : ℚ), (1, 15), (1, 22), (1, 19), (0, 6), [(1, 15)], [(1, 22)], [(1, 18), (1, 19)], [(0, 6), (0, 7)]⟩

theorem g026_ok : tagOKF CompactData.T CompactData.F g026 = true := by decide +kernel

def g027 : Tag := .inr ⟨(23 / 800 : ℚ), (3 / 100 : ℚ), (13 / 100 : ℚ), (27 / 200 : ℚ), (47 / 1600 : ℚ), (53 / 400 : ℚ), (1, 14), (1, 22), (1, 18), (0, 7), [(1, 14), (1, 15)], [(1, 21), (1, 22)], [(1, 18), (1, 19)], [(0, 7), (0, 8)]⟩

theorem g027_ok : tagOKF CompactData.T CompactData.F g027 = true := by decide +kernel

def g028 : Tag := .inr ⟨(23 / 800 : ℚ), (3 / 100 : ℚ), (27 / 200 : ℚ), (7 / 50 : ℚ), (47 / 1600 : ℚ), (11 / 80 : ℚ), (1, 15), (1, 22), (1, 19), (0, 7), [(1, 15)], [(1, 22), (1, 23)], [(1, 19)], [(0, 7), (0, 8)]⟩

theorem g028_ok : tagOKF CompactData.T CompactData.F g028 = true := by decide +kernel

def g029 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (7 / 50 : ℚ), (29 / 200 : ℚ), (41 / 1600 : ℚ), (57 / 400 : ℚ), (1, 16), (1, 22), (1, 19), (0, 5), [(1, 15), (1, 16)], [(1, 22)], [(1, 19), (1, 20)], [(0, 4), (0, 5)]⟩

theorem g029_ok : tagOKF CompactData.T CompactData.F g029 = true := by decide +kernel

def g030 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (29 / 200 : ℚ), (3 / 20 : ℚ), (41 / 1600 : ℚ), (59 / 400 : ℚ), (1, 16), (1, 23), (1, 20), (0, 5), [(1, 16), (1, 17)], [(1, 22), (1, 23)], [(1, 19), (1, 20)], [(0, 4), (0, 5)]⟩

theorem g030_ok : tagOKF CompactData.T CompactData.F g030 = true := by decide +kernel

def g031 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (7 / 50 : ℚ), (29 / 200 : ℚ), (43 / 1600 : ℚ), (57 / 400 : ℚ), (1, 16), (1, 22), (1, 19), (0, 6), [(1, 15), (1, 16)], [(1, 22), (1, 23)], [(1, 19), (1, 20)], [(0, 5), (0, 6)]⟩

theorem g031_ok : tagOKF CompactData.T CompactData.F g031 = true := by decide +kernel

def g032 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (29 / 200 : ℚ), (3 / 20 : ℚ), (43 / 1600 : ℚ), (59 / 400 : ℚ), (1, 16), (1, 23), (1, 20), (0, 6), [(1, 16), (1, 17)], [(1, 22), (1, 23)], [(1, 20)], [(0, 5), (0, 6)]⟩

theorem g032_ok : tagOKF CompactData.T CompactData.F g032 = true := by decide +kernel

def g033 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (3 / 20 : ℚ), (4 / 25 : ℚ), (41 / 1600 : ℚ), (31 / 200 : ℚ), (1, 17), (1, 23), (1, 21), (0, 5), [(1, 17), (1, 18)], [(1, 23), (2, 0)], [(1, 20), (1, 21)], [(0, 4), (0, 5)]⟩

theorem g033_ok : tagOKF CompactData.T CompactData.F g033 = true := by decide +kernel

def g034 : Tag := .inr ⟨(21 / 800 : ℚ), (11 / 400 : ℚ), (3 / 20 : ℚ), (4 / 25 : ℚ), (43 / 1600 : ℚ), (31 / 200 : ℚ), (1, 17), (2, 0), (1, 21), (0, 6), [(1, 17), (1, 18)], [(1, 23), (2, 0)], [(1, 20), (1, 21)], [(0, 5), (0, 6)]⟩

theorem g034_ok : tagOKF CompactData.T CompactData.F g034 = true := by decide +kernel

def g035 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (7 / 50 : ℚ), (3 / 20 : ℚ), (9 / 320 : ℚ), (29 / 200 : ℚ), (1, 16), (1, 23), (1, 20), (0, 6), [(1, 15), (1, 16), (1, 17)], [(1, 22), (1, 23)], [(1, 19), (1, 20)], [(0, 6), (0, 7)]⟩

theorem g035_ok : tagOKF CompactData.T CompactData.F g035 = true := by decide +kernel

def g036 : Tag := .inr ⟨(23 / 800 : ℚ), (3 / 100 : ℚ), (7 / 50 : ℚ), (3 / 20 : ℚ), (47 / 1600 : ℚ), (29 / 200 : ℚ), (1, 16), (1, 23), (1, 20), (0, 7), [(1, 15), (1, 16), (1, 17)], [(1, 22), (1, 23), (2, 0)], [(1, 19), (1, 20), (1, 21)], [(0, 7), (0, 8)]⟩

theorem g036_ok : tagOKF CompactData.T CompactData.F g036 = true := by decide +kernel

def g037 : Tag := .inr ⟨(11 / 400 : ℚ), (23 / 800 : ℚ), (3 / 20 : ℚ), (4 / 25 : ℚ), (9 / 320 : ℚ), (31 / 200 : ℚ), (1, 17), (2, 0), (1, 21), (0, 6), [(1, 17), (1, 18)], [(1, 23), (2, 0)], [(1, 20), (1, 21), (1, 22)], [(0, 6), (0, 7)]⟩

theorem g037_ok : tagOKF CompactData.T CompactData.F g037 = true := by decide +kernel

def g038 : Tag := .inr ⟨(23 / 800 : ℚ), (3 / 100 : ℚ), (3 / 20 : ℚ), (4 / 25 : ℚ), (47 / 1600 : ℚ), (31 / 200 : ℚ), (1, 17), (2, 0), (1, 21), (0, 7), [(1, 17), (1, 18)], [(1, 23), (2, 0), (2, 1)], [(1, 20), (1, 21), (1, 22)], [(0, 7), (0, 8)]⟩

theorem g038_ok : tagOKF CompactData.T CompactData.F g038 = true := by decide +kernel

def g039 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (2 / 25 : ℚ), (17 / 200 : ℚ), (49 / 1600 : ℚ), (33 / 400 : ℚ), (1, 5), (1, 16), (1, 11), (0, 8), [(1, 4), (1, 5)], [(1, 15), (1, 16)], [(1, 10), (1, 11), (1, 12)], [(0, 8), (0, 9)]⟩

theorem g039_ok : tagOKF CompactData.T CompactData.F g039 = true := by decide +kernel

def g040 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (2 / 25 : ℚ), (17 / 200 : ℚ), (51 / 1600 : ℚ), (33 / 400 : ℚ), (1, 5), (1, 16), (1, 11), (0, 9), [(1, 4), (1, 5)], [(1, 16), (1, 17)], [(1, 11), (1, 12)], [(0, 9)]⟩

theorem g040_ok : tagOKF CompactData.T CompactData.F g040 = true := by decide +kernel

def g041 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (17 / 200 : ℚ), (9 / 100 : ℚ), (49 / 1600 : ℚ), (7 / 80 : ℚ), (1, 6), (1, 17), (1, 12), (0, 8), [(1, 5), (1, 6)], [(1, 16), (1, 17)], [(1, 11), (1, 12)], [(0, 8), (0, 9)]⟩

theorem g041_ok : tagOKF CompactData.T CompactData.F g041 = true := by decide +kernel

def g042 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (17 / 200 : ℚ), (9 / 100 : ℚ), (51 / 1600 : ℚ), (7 / 80 : ℚ), (1, 6), (1, 17), (1, 12), (0, 9), [(1, 5), (1, 6)], [(1, 16), (1, 17)], [(1, 12), (1, 13)], [(0, 9)]⟩

theorem g042_ok : tagOKF CompactData.T CompactData.F g042 = true := by decide +kernel

def g043 : Tag := .inr ⟨(13 / 400 : ℚ), (27 / 800 : ℚ), (2 / 25 : ℚ), (17 / 200 : ℚ), (53 / 1600 : ℚ), (33 / 400 : ℚ), (1, 5), (1, 17), (1, 11), (0, 10), [(1, 4), (1, 5)], [(1, 16), (1, 17)], [(1, 11), (1, 12)], [(0, 9), (0, 10)]⟩

theorem g043_ok : tagOKF CompactData.T CompactData.F g043 = true := by decide +kernel

def g044 : Tag := .inr ⟨(27 / 800 : ℚ), (7 / 200 : ℚ), (2 / 25 : ℚ), (17 / 200 : ℚ), (11 / 320 : ℚ), (33 / 400 : ℚ), (1, 5), (1, 17), (1, 12), (0, 11), [(1, 4), (1, 5)], [(1, 16), (1, 17)], [(1, 11), (1, 12)], [(0, 10), (0, 11)]⟩

theorem g044_ok : tagOKF CompactData.T CompactData.F g044 = true := by decide +kernel

def g045 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (17 / 200 : ℚ), (9 / 100 : ℚ), (27 / 800 : ℚ), (7 / 80 : ℚ), (1, 6), (1, 17), (1, 12), (0, 10), [(1, 5), (1, 6)], [(1, 17), (1, 18)], [(1, 12), (1, 13)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g045_ok : tagOKF CompactData.T CompactData.F g045 = true := by decide +kernel

def g046 : Tag := .inr ⟨(3 / 100 : ℚ), (13 / 400 : ℚ), (9 / 100 : ℚ), (19 / 200 : ℚ), (1 / 32 : ℚ), (37 / 400 : ℚ), (1, 7), (1, 17), (1, 13), (0, 9), [(1, 6), (1, 7)], [(1, 17), (1, 18)], [(1, 12), (1, 13)], [(0, 8), (0, 9)]⟩

theorem g046_ok : tagOKF CompactData.T CompactData.F g046 = true := by decide +kernel

def g047 : Tag := .inr ⟨(3 / 100 : ℚ), (13 / 400 : ℚ), (19 / 200 : ℚ), (1 / 10 : ℚ), (1 / 32 : ℚ), (39 / 400 : ℚ), (1, 8), (1, 18), (1, 14), (0, 9), [(1, 7), (1, 8)], [(1, 17), (1, 18), (1, 19)], [(1, 13), (1, 14)], [(0, 8), (0, 9)]⟩

theorem g047_ok : tagOKF CompactData.T CompactData.F g047 = true := by decide +kernel

def g048 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (9 / 100 : ℚ), (19 / 200 : ℚ), (27 / 800 : ℚ), (37 / 400 : ℚ), (1, 7), (1, 18), (1, 13), (0, 10), [(1, 6), (1, 7)], [(1, 17), (1, 18), (1, 19)], [(1, 13), (1, 14)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g048_ok : tagOKF CompactData.T CompactData.F g048 = true := by decide +kernel

def g049 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (19 / 200 : ℚ), (1 / 10 : ℚ), (27 / 800 : ℚ), (39 / 400 : ℚ), (1, 8), (1, 19), (1, 14), (0, 10), [(1, 7), (1, 8)], [(1, 18), (1, 19)], [(1, 13), (1, 14), (1, 15)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g049_ok : tagOKF CompactData.T CompactData.F g049 = true := by decide +kernel

def g050 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (2 / 25 : ℚ), (17 / 200 : ℚ), (29 / 800 : ℚ), (33 / 400 : ℚ), (1, 5), (1, 17), (1, 12), (0, 12), [(1, 4), (1, 5)], [(1, 17), (1, 18)], [(1, 11), (1, 12), (1, 13)], [(0, 11), (0, 12)]⟩

theorem g050_ok : tagOKF CompactData.T CompactData.F g050 = true := by decide +kernel

def g051 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (17 / 200 : ℚ), (9 / 100 : ℚ), (29 / 800 : ℚ), (7 / 80 : ℚ), (1, 6), (1, 18), (1, 13), (0, 12), [(1, 5), (1, 6)], [(1, 17), (1, 18), (1, 19)], [(1, 12), (1, 13)], [(0, 11), (0, 12)]⟩

theorem g051_ok : tagOKF CompactData.T CompactData.F g051 = true := by decide +kernel

def g052 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (2 / 25 : ℚ), (17 / 200 : ℚ), (31 / 800 : ℚ), (33 / 400 : ℚ), (1, 5), (1, 18), (1, 12), (0, 13), [(1, 4), (1, 5)], [(1, 17), (1, 18), (1, 19)], [(1, 12), (1, 13)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g052_ok : tagOKF CompactData.T CompactData.F g052 = true := by decide +kernel

def g053 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (17 / 200 : ℚ), (9 / 100 : ℚ), (31 / 800 : ℚ), (7 / 80 : ℚ), (1, 6), (1, 19), (1, 13), (0, 13), [(1, 5), (1, 6)], [(1, 18), (1, 19)], [(1, 13), (1, 14)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g053_ok : tagOKF CompactData.T CompactData.F g053 = true := by decide +kernel

def g054 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (9 / 100 : ℚ), (19 / 200 : ℚ), (29 / 800 : ℚ), (37 / 400 : ℚ), (1, 7), (1, 19), (1, 14), (0, 12), [(1, 6), (1, 7)], [(1, 18), (1, 19)], [(1, 13), (1, 14)], [(0, 11), (0, 12)]⟩

theorem g054_ok : tagOKF CompactData.T CompactData.F g054 = true := by decide +kernel

def g055 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (19 / 200 : ℚ), (1 / 10 : ℚ), (29 / 800 : ℚ), (39 / 400 : ℚ), (1, 8), (1, 19), (1, 14), (0, 12), [(1, 7), (1, 8)], [(1, 19), (1, 20)], [(1, 14), (1, 15)], [(0, 11), (0, 12)]⟩

theorem g055_ok : tagOKF CompactData.T CompactData.F g055 = true := by decide +kernel

def g056 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (9 / 100 : ℚ), (19 / 200 : ℚ), (31 / 800 : ℚ), (37 / 400 : ℚ), (1, 7), (1, 19), (1, 14), (0, 13), [(1, 6), (1, 7)], [(1, 19), (1, 20)], [(1, 13), (1, 14), (1, 15)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g056_ok : tagOKF CompactData.T CompactData.F g056 = true := by decide +kernel

def g057 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (19 / 200 : ℚ), (1 / 10 : ℚ), (31 / 800 : ℚ), (39 / 400 : ℚ), (1, 8), (1, 20), (1, 15), (0, 13), [(1, 7), (1, 8)], [(1, 19), (1, 20), (1, 21)], [(1, 14), (1, 15)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g057_ok : tagOKF CompactData.T CompactData.F g057 = true := by decide +kernel

def g058 : Tag := .inr ⟨(3 / 100 : ℚ), (13 / 400 : ℚ), (1 / 10 : ℚ), (21 / 200 : ℚ), (1 / 32 : ℚ), (41 / 400 : ℚ), (1, 9), (1, 19), (1, 14), (0, 9), [(1, 8), (1, 9)], [(1, 18), (1, 19)], [(1, 14), (1, 15)], [(0, 8), (0, 9)]⟩

theorem g058_ok : tagOKF CompactData.T CompactData.F g058 = true := by decide +kernel

def g059 : Tag := .inr ⟨(3 / 100 : ℚ), (13 / 400 : ℚ), (21 / 200 : ℚ), (11 / 100 : ℚ), (1 / 32 : ℚ), (43 / 400 : ℚ), (1, 10), (1, 19), (1, 15), (0, 9), [(1, 9), (1, 10)], [(1, 19), (1, 20)], [(1, 15), (1, 16)], [(0, 8), (0, 9)]⟩

theorem g059_ok : tagOKF CompactData.T CompactData.F g059 = true := by decide +kernel

def g060 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (1 / 10 : ℚ), (21 / 200 : ℚ), (27 / 800 : ℚ), (41 / 400 : ℚ), (1, 9), (1, 19), (1, 15), (0, 10), [(1, 8), (1, 9)], [(1, 19), (1, 20)], [(1, 14), (1, 15)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g060_ok : tagOKF CompactData.T CompactData.F g060 = true := by decide +kernel

def g061 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (21 / 200 : ℚ), (11 / 100 : ℚ), (27 / 800 : ℚ), (43 / 400 : ℚ), (1, 10), (1, 20), (1, 16), (0, 10), [(1, 9), (1, 10)], [(1, 19), (1, 20), (1, 21)], [(1, 15), (1, 16)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g061_ok : tagOKF CompactData.T CompactData.F g061 = true := by decide +kernel

def g062 : Tag := .inr ⟨(3 / 100 : ℚ), (13 / 400 : ℚ), (11 / 100 : ℚ), (23 / 200 : ℚ), (1 / 32 : ℚ), (9 / 80 : ℚ), (1, 11), (1, 20), (1, 16), (0, 9), [(1, 10), (1, 11)], [(1, 19), (1, 20), (1, 21)], [(1, 15), (1, 16)], [(0, 8), (0, 9)]⟩

theorem g062_ok : tagOKF CompactData.T CompactData.F g062 = true := by decide +kernel

def g063 : Tag := .inr ⟨(3 / 100 : ℚ), (13 / 400 : ℚ), (23 / 200 : ℚ), (3 / 25 : ℚ), (1 / 32 : ℚ), (47 / 400 : ℚ), (1, 12), (1, 21), (1, 17), (0, 9), [(1, 11), (1, 12)], [(1, 20), (1, 21)], [(1, 16), (1, 17)], [(0, 8), (0, 9)]⟩

theorem g063_ok : tagOKF CompactData.T CompactData.F g063 = true := by decide +kernel

def g064 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (11 / 100 : ℚ), (23 / 200 : ℚ), (27 / 800 : ℚ), (9 / 80 : ℚ), (1, 11), (1, 21), (1, 16), (0, 10), [(1, 10), (1, 11)], [(1, 20), (1, 21)], [(1, 16), (1, 17)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g064_ok : tagOKF CompactData.T CompactData.F g064 = true := by decide +kernel

def g065 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (23 / 200 : ℚ), (3 / 25 : ℚ), (27 / 800 : ℚ), (47 / 400 : ℚ), (1, 12), (1, 21), (1, 17), (0, 10), [(1, 11), (1, 12)], [(1, 21), (1, 22)], [(1, 16), (1, 17)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g065_ok : tagOKF CompactData.T CompactData.F g065 = true := by decide +kernel

def g066 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (1 / 10 : ℚ), (21 / 200 : ℚ), (29 / 800 : ℚ), (41 / 400 : ℚ), (1, 9), (1, 20), (1, 15), (0, 12), [(1, 8), (1, 9)], [(1, 19), (1, 20), (1, 21)], [(1, 15), (1, 16)], [(0, 11), (0, 12)]⟩

theorem g066_ok : tagOKF CompactData.T CompactData.F g066 = true := by decide +kernel

def g067 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (21 / 200 : ℚ), (11 / 100 : ℚ), (29 / 800 : ℚ), (43 / 400 : ℚ), (1, 10), (1, 21), (1, 16), (0, 12), [(1, 9), (1, 10)], [(1, 20), (1, 21)], [(1, 15), (1, 16)], [(0, 11), (0, 12)]⟩

theorem g067_ok : tagOKF CompactData.T CompactData.F g067 = true := by decide +kernel

def g068 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (1 / 10 : ℚ), (21 / 200 : ℚ), (31 / 800 : ℚ), (41 / 400 : ℚ), (1, 9), (1, 21), (1, 16), (0, 13), [(1, 8), (1, 9)], [(1, 20), (1, 21)], [(1, 15), (1, 16)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g068_ok : tagOKF CompactData.T CompactData.F g068 = true := by decide +kernel


end CKLaneC3.CompactBatch02


