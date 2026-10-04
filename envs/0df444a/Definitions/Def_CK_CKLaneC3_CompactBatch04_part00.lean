-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch04_part00
-- name    : CK_CKLaneC3_CompactBatch04_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T05:05:30.853984+00:00
-- url     : https://prove2.me/theorems/30e41d11-4e0e-4751-afd2-a2e0d1877caa
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch04 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch04 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch04 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch04 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch04 (part 1 of 2).lean)

import Definitions.Def_CK_CKLaneC3_CompactData
import Definitions.Def_CK_CKLaneC3_CompactCoverF

/-! Lane C3 compact cell batch (generated; memoised chains over the data tables). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactBatch04
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF

def g000 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (11 / 50 : ℚ), (23 / 100 : ℚ), (27 / 800 : ℚ), (9 / 40 : ℚ), (2, 1), (2, 6), (2, 4), (0, 10), [(2, 1), (2, 2)], [(2, 6), (2, 7)], [(2, 3), (2, 4)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g000_ok : tagOKF CompactData.T CompactData.F g000 = true := by decide +kernel

def g001 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (23 / 100 : ℚ), (6 / 25 : ℚ), (27 / 800 : ℚ), (47 / 200 : ℚ), (2, 2), (2, 7), (2, 5), (0, 10), [(2, 2)], [(2, 7), (2, 8)], [(2, 4), (2, 5)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g001_ok : tagOKF CompactData.T CompactData.F g001 = true := by decide +kernel

def g002 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (1 / 5 : ℚ), (21 / 100 : ℚ), (29 / 800 : ℚ), (41 / 200 : ℚ), (1, 23), (2, 5), (2, 3), (0, 12), [(1, 23), (2, 0)], [(2, 5), (2, 6)], [(2, 2), (2, 3)], [(0, 11), (0, 12)]⟩

theorem g002_ok : tagOKF CompactData.T CompactData.F g002 = true := by decide +kernel

def g003 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (21 / 100 : ℚ), (11 / 50 : ℚ), (29 / 800 : ℚ), (43 / 200 : ℚ), (2, 0), (2, 6), (2, 3), (0, 12), [(2, 0), (2, 1)], [(2, 6), (2, 7)], [(2, 3), (2, 4)], [(0, 11), (0, 12)]⟩

theorem g003_ok : tagOKF CompactData.T CompactData.F g003 = true := by decide +kernel

def g004 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (1 / 5 : ℚ), (21 / 100 : ℚ), (31 / 800 : ℚ), (41 / 200 : ℚ), (1, 23), (2, 6), (2, 3), (0, 13), [(1, 23), (2, 0)], [(2, 5), (2, 6)], [(2, 2), (2, 3)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g004_ok : tagOKF CompactData.T CompactData.F g004 = true := by decide +kernel

def g005 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (21 / 100 : ℚ), (11 / 50 : ℚ), (31 / 800 : ℚ), (43 / 200 : ℚ), (2, 0), (2, 6), (2, 4), (0, 13), [(2, 0), (2, 1)], [(2, 6), (2, 7)], [(2, 3), (2, 4)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g005_ok : tagOKF CompactData.T CompactData.F g005 = true := by decide +kernel

def g006 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (11 / 50 : ℚ), (23 / 100 : ℚ), (29 / 800 : ℚ), (9 / 40 : ℚ), (2, 1), (2, 7), (2, 4), (0, 12), [(2, 1), (2, 2)], [(2, 6), (2, 7)], [(2, 4), (2, 5)], [(0, 11), (0, 12)]⟩

theorem g006_ok : tagOKF CompactData.T CompactData.F g006 = true := by decide +kernel

def g007 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (23 / 100 : ℚ), (6 / 25 : ℚ), (29 / 800 : ℚ), (47 / 200 : ℚ), (2, 2), (2, 8), (2, 5), (0, 12), [(2, 2)], [(2, 7), (2, 8)], [(2, 4), (2, 5)], [(0, 11), (0, 12)]⟩

theorem g007_ok : tagOKF CompactData.T CompactData.F g007 = true := by decide +kernel

def g008 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (11 / 50 : ℚ), (23 / 100 : ℚ), (31 / 800 : ℚ), (9 / 40 : ℚ), (2, 1), (2, 7), (2, 4), (0, 13), [(2, 1), (2, 2)], [(2, 7), (2, 8)], [(2, 4), (2, 5)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g008_ok : tagOKF CompactData.T CompactData.F g008 = true := by decide +kernel

def g009 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (23 / 100 : ℚ), (6 / 25 : ℚ), (31 / 800 : ℚ), (47 / 200 : ℚ), (2, 2), (2, 8), (2, 5), (0, 13), [(2, 2)], [(2, 7), (2, 8)], [(2, 5), (2, 6)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g009_ok : tagOKF CompactData.T CompactData.F g009 = true := by decide +kernel

def g010 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (6 / 25 : ℚ), (1 / 4 : ℚ), (49 / 1600 : ℚ), (49 / 200 : ℚ), (2, 3), (2, 7), (2, 5), (0, 8), [(2, 2), (2, 3)], [(2, 7), (2, 8)], [(2, 5), (2, 6)], [(0, 8), (0, 9)]⟩

theorem g010_ok : tagOKF CompactData.T CompactData.F g010 = true := by decide +kernel

def g011 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (1 / 4 : ℚ), (13 / 50 : ℚ), (49 / 1600 : ℚ), (51 / 200 : ℚ), (2, 4), (2, 8), (2, 6), (0, 8), [(2, 3), (2, 4)], [(2, 8)], [(2, 6)], [(0, 8), (0, 9)]⟩

theorem g011_ok : tagOKF CompactData.T CompactData.F g011 = true := by decide +kernel

def g012 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (6 / 25 : ℚ), (1 / 4 : ℚ), (51 / 1600 : ℚ), (49 / 200 : ℚ), (2, 3), (2, 8), (2, 5), (0, 9), [(2, 2), (2, 3)], [(2, 7), (2, 8)], [(2, 5), (2, 6)], [(0, 9)]⟩

theorem g012_ok : tagOKF CompactData.T CompactData.F g012 = true := by decide +kernel

def g013 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (1 / 4 : ℚ), (13 / 50 : ℚ), (51 / 1600 : ℚ), (51 / 200 : ℚ), (2, 4), (2, 8), (2, 6), (0, 9), [(2, 3), (2, 4)], [(2, 8), (2, 9)], [(2, 6)], [(0, 9)]⟩

theorem g013_ok : tagOKF CompactData.T CompactData.F g013 = true := by decide +kernel

def g014 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (49 / 1600 : ℚ), (27 / 100 : ℚ), (2, 5), (2, 9), (2, 7), (0, 8), [(2, 4), (2, 5), (2, 6)], [(2, 8), (2, 9), (2, 10)], [(2, 6), (2, 7), (2, 8)], [(0, 8), (0, 9)]⟩

theorem g014_ok : tagOKF CompactData.T CompactData.F g014 = true := by decide +kernel

def g015 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (51 / 1600 : ℚ), (27 / 100 : ℚ), (2, 5), (2, 9), (2, 7), (0, 9), [(2, 4), (2, 5), (2, 6)], [(2, 8), (2, 9), (2, 10)], [(2, 6), (2, 7), (2, 8)], [(0, 9)]⟩

theorem g015_ok : tagOKF CompactData.T CompactData.F g015 = true := by decide +kernel

def g016 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (6 / 25 : ℚ), (1 / 4 : ℚ), (27 / 800 : ℚ), (49 / 200 : ℚ), (2, 3), (2, 8), (2, 5), (0, 10), [(2, 2), (2, 3)], [(2, 7), (2, 8)], [(2, 5), (2, 6)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g016_ok : tagOKF CompactData.T CompactData.F g016 = true := by decide +kernel

def g017 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (1 / 4 : ℚ), (13 / 50 : ℚ), (27 / 800 : ℚ), (51 / 200 : ℚ), (2, 4), (2, 8), (2, 6), (0, 10), [(2, 3), (2, 4)], [(2, 8), (2, 9)], [(2, 6), (2, 7)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g017_ok : tagOKF CompactData.T CompactData.F g017 = true := by decide +kernel

def g018 : Tag := .inr ⟨(13 / 400 : ℚ), (27 / 800 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (53 / 1600 : ℚ), (27 / 100 : ℚ), (2, 5), (2, 9), (2, 7), (0, 10), [(2, 4), (2, 5), (2, 6)], [(2, 9), (2, 10)], [(2, 6), (2, 7), (2, 8)], [(0, 9), (0, 10)]⟩

theorem g018_ok : tagOKF CompactData.T CompactData.F g018 = true := by decide +kernel

def g019 : Tag := .inr ⟨(27 / 800 : ℚ), (7 / 200 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (11 / 320 : ℚ), (27 / 100 : ℚ), (2, 5), (2, 9), (2, 7), (0, 11), [(2, 4), (2, 5), (2, 6)], [(2, 9), (2, 10)], [(2, 7), (2, 8)], [(0, 10), (0, 11)]⟩

theorem g019_ok : tagOKF CompactData.T CompactData.F g019 = true := by decide +kernel

def g020 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (7 / 25 : ℚ), (3 / 10 : ℚ), (49 / 1600 : ℚ), (29 / 100 : ℚ), (2, 6), (2, 10), (2, 8), (0, 8), [(2, 6), (2, 7)], [(2, 10), (2, 11)], [(2, 8), (2, 9)], [(0, 8), (0, 9)]⟩

theorem g020_ok : tagOKF CompactData.T CompactData.F g020 = true := by decide +kernel

def g021 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (7 / 25 : ℚ), (3 / 10 : ℚ), (51 / 1600 : ℚ), (29 / 100 : ℚ), (2, 6), (2, 10), (2, 8), (0, 9), [(2, 6), (2, 7)], [(2, 10), (2, 11)], [(2, 8), (2, 9)], [(0, 9)]⟩

theorem g021_ok : tagOKF CompactData.T CompactData.F g021 = true := by decide +kernel

def g022 : Tag := .inr ⟨(3 / 100 : ℚ), (13 / 400 : ℚ), (3 / 10 : ℚ), (8 / 25 : ℚ), (1 / 32 : ℚ), (31 / 100 : ℚ), (2, 8), (2, 11), (2, 10), (0, 9), [(2, 7), (2, 8)], [(2, 11), (2, 12)], [(2, 9), (2, 10)], [(0, 8), (0, 9)]⟩

theorem g022_ok : tagOKF CompactData.T CompactData.F g022 = true := by decide +kernel

def g023 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (7 / 25 : ℚ), (3 / 10 : ℚ), (27 / 800 : ℚ), (29 / 100 : ℚ), (2, 6), (2, 11), (2, 9), (0, 10), [(2, 6), (2, 7)], [(2, 10), (2, 11)], [(2, 8), (2, 9)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g023_ok : tagOKF CompactData.T CompactData.F g023 = true := by decide +kernel

def g024 : Tag := .inr ⟨(13 / 400 : ℚ), (7 / 200 : ℚ), (3 / 10 : ℚ), (8 / 25 : ℚ), (27 / 800 : ℚ), (31 / 100 : ℚ), (2, 8), (2, 12), (2, 10), (0, 10), [(2, 7), (2, 8)], [(2, 11), (2, 12)], [(2, 9), (2, 10)], [(0, 9), (0, 10), (0, 11)]⟩

theorem g024_ok : tagOKF CompactData.T CompactData.F g024 = true := by decide +kernel

def g025 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (6 / 25 : ℚ), (1 / 4 : ℚ), (29 / 800 : ℚ), (49 / 200 : ℚ), (2, 3), (2, 8), (2, 6), (0, 12), [(2, 2), (2, 3)], [(2, 8), (2, 9)], [(2, 5), (2, 6)], [(0, 11), (0, 12)]⟩

theorem g025_ok : tagOKF CompactData.T CompactData.F g025 = true := by decide +kernel

def g026 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (1 / 4 : ℚ), (13 / 50 : ℚ), (29 / 800 : ℚ), (51 / 200 : ℚ), (2, 4), (2, 9), (2, 6), (0, 12), [(2, 3), (2, 4)], [(2, 8), (2, 9)], [(2, 6), (2, 7)], [(0, 11), (0, 12)]⟩

theorem g026_ok : tagOKF CompactData.T CompactData.F g026 = true := by decide +kernel

def g027 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (6 / 25 : ℚ), (1 / 4 : ℚ), (31 / 800 : ℚ), (49 / 200 : ℚ), (2, 3), (2, 8), (2, 6), (0, 13), [(2, 2), (2, 3)], [(2, 8), (2, 9)], [(2, 5), (2, 6)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g027_ok : tagOKF CompactData.T CompactData.F g027 = true := by decide +kernel

def g028 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (1 / 4 : ℚ), (13 / 50 : ℚ), (31 / 800 : ℚ), (51 / 200 : ℚ), (2, 4), (2, 9), (2, 7), (0, 13), [(2, 3), (2, 4)], [(2, 9), (2, 10)], [(2, 6), (2, 7)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g028_ok : tagOKF CompactData.T CompactData.F g028 = true := by decide +kernel

def g029 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (29 / 800 : ℚ), (27 / 100 : ℚ), (2, 5), (2, 10), (2, 7), (0, 12), [(2, 4), (2, 5), (2, 6)], [(2, 9), (2, 10)], [(2, 7), (2, 8)], [(0, 11), (0, 12)]⟩

theorem g029_ok : tagOKF CompactData.T CompactData.F g029 = true := by decide +kernel

def g030 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (31 / 800 : ℚ), (27 / 100 : ℚ), (2, 5), (2, 10), (2, 8), (0, 13), [(2, 4), (2, 5), (2, 6)], [(2, 9), (2, 10), (2, 11)], [(2, 7), (2, 8)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g030_ok : tagOKF CompactData.T CompactData.F g030 = true := by decide +kernel

def g031 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (7 / 25 : ℚ), (3 / 10 : ℚ), (29 / 800 : ℚ), (29 / 100 : ℚ), (2, 6), (2, 11), (2, 9), (0, 12), [(2, 6), (2, 7)], [(2, 10), (2, 11), (2, 12)], [(2, 8), (2, 9)], [(0, 11), (0, 12)]⟩

theorem g031_ok : tagOKF CompactData.T CompactData.F g031 = true := by decide +kernel

def g032 : Tag := .inr ⟨(7 / 200 : ℚ), (3 / 80 : ℚ), (3 / 10 : ℚ), (8 / 25 : ℚ), (29 / 800 : ℚ), (31 / 100 : ℚ), (2, 8), (2, 12), (2, 10), (0, 12), [(2, 7), (2, 8)], [(2, 11), (2, 12), (2, 13)], [(2, 9), (2, 10), (2, 11)], [(0, 11), (0, 12)]⟩

theorem g032_ok : tagOKF CompactData.T CompactData.F g032 = true := by decide +kernel

def g033 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (7 / 25 : ℚ), (3 / 10 : ℚ), (31 / 800 : ℚ), (29 / 100 : ℚ), (2, 6), (2, 11), (2, 9), (0, 13), [(2, 6), (2, 7)], [(2, 10), (2, 11), (2, 12)], [(2, 8), (2, 9), (2, 10)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g033_ok : tagOKF CompactData.T CompactData.F g033 = true := by decide +kernel

def g034 : Tag := .inr ⟨(3 / 80 : ℚ), (1 / 25 : ℚ), (3 / 10 : ℚ), (8 / 25 : ℚ), (31 / 800 : ℚ), (31 / 100 : ℚ), (2, 8), (2, 12), (2, 10), (0, 13), [(2, 7), (2, 8)], [(2, 12), (2, 13)], [(2, 9), (2, 10), (2, 11)], [(0, 12), (0, 13), (0, 14)]⟩

theorem g034_ok : tagOKF CompactData.T CompactData.F g034 = true := by decide +kernel

def g035 : Tag := .inr ⟨(1 / 50 : ℚ), (33 / 1600 : ℚ), (8 / 25 : ℚ), (17 / 50 : ℚ), (13 / 640 : ℚ), (33 / 100 : ℚ), (2, 9), (2, 11), (2, 10), (0, 0), [(2, 8), (2, 9), (2, 10)], [(2, 11), (2, 12)], [(2, 10), (2, 11)], [(0, 0)]⟩

theorem g035_ok : tagOKF CompactData.T CompactData.F g035 = true := by decide +kernel

def g036 : Tag := .inr ⟨(33 / 1600 : ℚ), (17 / 800 : ℚ), (8 / 25 : ℚ), (17 / 50 : ℚ), (67 / 3200 : ℚ), (33 / 100 : ℚ), (2, 9), (2, 11), (2, 10), (0, 0), [(2, 8), (2, 9), (2, 10)], [(2, 11), (2, 12)], [(2, 10), (2, 11)], [(0, 0), (0, 1)]⟩

theorem g036_ok : tagOKF CompactData.T CompactData.F g036 = true := by decide +kernel

def g037 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (17 / 50 : ℚ), (9 / 25 : ℚ), (33 / 1600 : ℚ), (7 / 20 : ℚ), (2, 10), (2, 12), (2, 11), (0, 0), [(2, 10), (2, 11)], [(2, 12), (2, 13)], [(2, 11), (2, 12)], [(0, 0), (0, 1)]⟩

theorem g037_ok : tagOKF CompactData.T CompactData.F g037 = true := by decide +kernel

def g038 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (8 / 25 : ℚ), (17 / 50 : ℚ), (7 / 320 : ℚ), (33 / 100 : ℚ), (2, 9), (2, 12), (2, 10), (0, 1), [(2, 8), (2, 9), (2, 10)], [(2, 11), (2, 12)], [(2, 10), (2, 11)], [(0, 1), (0, 2)]⟩

theorem g038_ok : tagOKF CompactData.T CompactData.F g038 = true := by decide +kernel

def g039 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (17 / 50 : ℚ), (9 / 25 : ℚ), (7 / 320 : ℚ), (7 / 20 : ℚ), (2, 10), (2, 13), (2, 11), (0, 1), [(2, 10), (2, 11)], [(2, 12), (2, 13)], [(2, 11), (2, 12)], [(0, 1), (0, 2)]⟩

theorem g039_ok : tagOKF CompactData.T CompactData.F g039 = true := by decide +kernel

def g040 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (9 / 25 : ℚ), (19 / 50 : ℚ), (33 / 1600 : ℚ), (37 / 100 : ℚ), (2, 11), (2, 13), (2, 12), (0, 0), [(2, 11), (2, 12)], [(2, 13), (2, 14)], [(2, 12), (2, 13)], [(0, 0), (0, 1)]⟩

theorem g040_ok : tagOKF CompactData.T CompactData.F g040 = true := by decide +kernel

def g041 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (19 / 50 : ℚ), (2 / 5 : ℚ), (33 / 1600 : ℚ), (39 / 100 : ℚ), (2, 12), (2, 14), (2, 13), (0, 0), [(2, 12), (2, 13)], [(2, 14), (2, 15)], [(2, 13), (2, 14)], [(0, 0), (0, 1)]⟩

theorem g041_ok : tagOKF CompactData.T CompactData.F g041 = true := by decide +kernel

def g042 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (9 / 25 : ℚ), (19 / 50 : ℚ), (7 / 320 : ℚ), (37 / 100 : ℚ), (2, 11), (2, 14), (2, 12), (0, 1), [(2, 11), (2, 12)], [(2, 13), (2, 14)], [(2, 12), (2, 13)], [(0, 1), (0, 2)]⟩

theorem g042_ok : tagOKF CompactData.T CompactData.F g042 = true := by decide +kernel

def g043 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (19 / 50 : ℚ), (2 / 5 : ℚ), (7 / 320 : ℚ), (39 / 100 : ℚ), (2, 12), (2, 15), (2, 13), (0, 1), [(2, 12), (2, 13)], [(2, 14), (2, 15)], [(2, 13), (2, 14)], [(0, 1), (0, 2)]⟩

theorem g043_ok : tagOKF CompactData.T CompactData.F g043 = true := by decide +kernel

def g044 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (8 / 25 : ℚ), (17 / 50 : ℚ), (37 / 1600 : ℚ), (33 / 100 : ℚ), (2, 9), (2, 12), (2, 10), (0, 2), [(2, 8), (2, 9), (2, 10)], [(2, 11), (2, 12)], [(2, 10), (2, 11)], [(0, 2), (0, 3)]⟩

theorem g044_ok : tagOKF CompactData.T CompactData.F g044 = true := by decide +kernel

def g045 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (8 / 25 : ℚ), (17 / 50 : ℚ), (39 / 1600 : ℚ), (33 / 100 : ℚ), (2, 9), (2, 12), (2, 10), (0, 4), [(2, 8), (2, 9), (2, 10)], [(2, 11), (2, 12)], [(2, 10), (2, 11)], [(0, 3), (0, 4)]⟩

theorem g045_ok : tagOKF CompactData.T CompactData.F g045 = true := by decide +kernel

def g046 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (17 / 50 : ℚ), (9 / 25 : ℚ), (37 / 1600 : ℚ), (7 / 20 : ℚ), (2, 10), (2, 13), (2, 11), (0, 2), [(2, 10), (2, 11)], [(2, 12), (2, 13)], [(2, 11), (2, 12)], [(0, 2), (0, 3)]⟩

theorem g046_ok : tagOKF CompactData.T CompactData.F g046 = true := by decide +kernel

def g047 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (17 / 50 : ℚ), (9 / 25 : ℚ), (39 / 1600 : ℚ), (7 / 20 : ℚ), (2, 10), (2, 13), (2, 12), (0, 4), [(2, 10), (2, 11)], [(2, 12), (2, 13)], [(2, 11), (2, 12)], [(0, 3), (0, 4)]⟩

theorem g047_ok : tagOKF CompactData.T CompactData.F g047 = true := by decide +kernel

def g048 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (9 / 25 : ℚ), (19 / 50 : ℚ), (37 / 1600 : ℚ), (37 / 100 : ℚ), (2, 11), (2, 14), (2, 13), (0, 2), [(2, 11), (2, 12)], [(2, 13), (2, 14)], [(2, 12), (2, 13)], [(0, 2), (0, 3)]⟩

theorem g048_ok : tagOKF CompactData.T CompactData.F g048 = true := by decide +kernel

def g049 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (19 / 50 : ℚ), (2 / 5 : ℚ), (37 / 1600 : ℚ), (39 / 100 : ℚ), (2, 12), (2, 15), (2, 14), (0, 2), [(2, 12), (2, 13)], [(2, 14), (2, 15)], [(2, 13), (2, 14)], [(0, 2), (0, 3)]⟩

theorem g049_ok : tagOKF CompactData.T CompactData.F g049 = true := by decide +kernel

def g050 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (9 / 25 : ℚ), (19 / 50 : ℚ), (39 / 1600 : ℚ), (37 / 100 : ℚ), (2, 11), (2, 14), (2, 13), (0, 4), [(2, 11), (2, 12)], [(2, 13), (2, 14)], [(2, 12), (2, 13)], [(0, 3), (0, 4)]⟩

theorem g050_ok : tagOKF CompactData.T CompactData.F g050 = true := by decide +kernel

def g051 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (19 / 50 : ℚ), (2 / 5 : ℚ), (39 / 1600 : ℚ), (39 / 100 : ℚ), (2, 12), (2, 15), (2, 14), (0, 4), [(2, 12), (2, 13)], [(2, 14), (2, 15)], [(2, 13), (2, 14)], [(0, 3), (0, 4)]⟩

theorem g051_ok : tagOKF CompactData.T CompactData.F g051 = true := by decide +kernel

def g052 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (2 / 5 : ℚ), (21 / 50 : ℚ), (33 / 1600 : ℚ), (41 / 100 : ℚ), (2, 13), (2, 15), (2, 14), (0, 0), [(2, 13), (2, 14)], [(2, 15), (2, 16)], [(2, 14), (2, 15)], [(0, 0), (0, 1)]⟩

theorem g052_ok : tagOKF CompactData.T CompactData.F g052 = true := by decide +kernel

def g053 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (21 / 50 : ℚ), (11 / 25 : ℚ), (33 / 1600 : ℚ), (43 / 100 : ℚ), (2, 14), (2, 16), (2, 15), (0, 0), [(2, 14), (2, 15)], [(2, 16), (2, 17)], [(2, 15), (2, 16)], [(0, 0), (0, 1)]⟩

theorem g053_ok : tagOKF CompactData.T CompactData.F g053 = true := by decide +kernel

def g054 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (2 / 5 : ℚ), (21 / 50 : ℚ), (7 / 320 : ℚ), (41 / 100 : ℚ), (2, 13), (2, 16), (2, 14), (0, 1), [(2, 13), (2, 14)], [(2, 15), (2, 16)], [(2, 14), (2, 15)], [(0, 1), (0, 2)]⟩

theorem g054_ok : tagOKF CompactData.T CompactData.F g054 = true := by decide +kernel

def g055 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (21 / 50 : ℚ), (11 / 25 : ℚ), (7 / 320 : ℚ), (43 / 100 : ℚ), (2, 14), (2, 17), (2, 15), (0, 1), [(2, 14), (2, 15)], [(2, 16), (2, 17)], [(2, 15), (2, 16)], [(0, 1), (0, 2)]⟩

theorem g055_ok : tagOKF CompactData.T CompactData.F g055 = true := by decide +kernel

def g056 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (11 / 25 : ℚ), (23 / 50 : ℚ), (33 / 1600 : ℚ), (9 / 20 : ℚ), (2, 15), (2, 17), (2, 16), (0, 0), [(2, 15), (2, 16)], [(2, 17), (2, 18)], [(2, 16), (2, 17)], [(0, 0), (0, 1)]⟩

theorem g056_ok : tagOKF CompactData.T CompactData.F g056 = true := by decide +kernel

def g057 : Tag := .inr ⟨(1 / 50 : ℚ), (17 / 800 : ℚ), (23 / 50 : ℚ), (12 / 25 : ℚ), (33 / 1600 : ℚ), (47 / 100 : ℚ), (2, 16), (2, 18), (2, 17), (0, 0), [(2, 16), (2, 17)], [(2, 18), (2, 19)], [(2, 17), (2, 18)], [(0, 0), (0, 1)]⟩

theorem g057_ok : tagOKF CompactData.T CompactData.F g057 = true := by decide +kernel

def g058 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (11 / 25 : ℚ), (23 / 50 : ℚ), (7 / 320 : ℚ), (9 / 20 : ℚ), (2, 15), (2, 18), (2, 16), (0, 1), [(2, 15), (2, 16)], [(2, 17), (2, 18)], [(2, 16), (2, 17)], [(0, 1), (0, 2)]⟩

theorem g058_ok : tagOKF CompactData.T CompactData.F g058 = true := by decide +kernel

def g059 : Tag := .inr ⟨(17 / 800 : ℚ), (9 / 400 : ℚ), (23 / 50 : ℚ), (12 / 25 : ℚ), (7 / 320 : ℚ), (47 / 100 : ℚ), (2, 16), (2, 19), (2, 17), (0, 1), [(2, 16), (2, 17)], [(2, 18), (2, 19)], [(2, 17), (2, 18)], [(0, 1), (0, 2)]⟩

theorem g059_ok : tagOKF CompactData.T CompactData.F g059 = true := by decide +kernel

def g060 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (2 / 5 : ℚ), (21 / 50 : ℚ), (37 / 1600 : ℚ), (41 / 100 : ℚ), (2, 13), (2, 16), (2, 15), (0, 2), [(2, 13), (2, 14)], [(2, 15), (2, 16)], [(2, 14), (2, 15)], [(0, 2), (0, 3)]⟩

theorem g060_ok : tagOKF CompactData.T CompactData.F g060 = true := by decide +kernel

def g061 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (21 / 50 : ℚ), (11 / 25 : ℚ), (37 / 1600 : ℚ), (43 / 100 : ℚ), (2, 14), (2, 17), (2, 16), (0, 2), [(2, 14), (2, 15)], [(2, 16), (2, 17)], [(2, 15), (2, 16)], [(0, 2), (0, 3)]⟩

theorem g061_ok : tagOKF CompactData.T CompactData.F g061 = true := by decide +kernel

def g062 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (2 / 5 : ℚ), (21 / 50 : ℚ), (39 / 1600 : ℚ), (41 / 100 : ℚ), (2, 13), (2, 16), (2, 15), (0, 4), [(2, 13), (2, 14)], [(2, 15), (2, 16)], [(2, 14), (2, 15)], [(0, 3), (0, 4)]⟩

theorem g062_ok : tagOKF CompactData.T CompactData.F g062 = true := by decide +kernel

def g063 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (21 / 50 : ℚ), (11 / 25 : ℚ), (39 / 1600 : ℚ), (43 / 100 : ℚ), (2, 14), (2, 17), (2, 16), (0, 4), [(2, 14), (2, 15)], [(2, 16), (2, 17)], [(2, 15), (2, 16)], [(0, 3), (0, 4)]⟩

theorem g063_ok : tagOKF CompactData.T CompactData.F g063 = true := by decide +kernel

def g064 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (11 / 25 : ℚ), (23 / 50 : ℚ), (37 / 1600 : ℚ), (9 / 20 : ℚ), (2, 15), (2, 18), (2, 17), (0, 2), [(2, 15), (2, 16)], [(2, 17), (2, 18)], [(2, 16), (2, 17)], [(0, 2), (0, 3)]⟩

theorem g064_ok : tagOKF CompactData.T CompactData.F g064 = true := by decide +kernel

def g065 : Tag := .inr ⟨(9 / 400 : ℚ), (19 / 800 : ℚ), (23 / 50 : ℚ), (12 / 25 : ℚ), (37 / 1600 : ℚ), (47 / 100 : ℚ), (2, 16), (2, 19), (2, 18), (0, 2), [(2, 16), (2, 17)], [(2, 18), (2, 19)], [(2, 17), (2, 18)], [(0, 2), (0, 3)]⟩

theorem g065_ok : tagOKF CompactData.T CompactData.F g065 = true := by decide +kernel

def g066 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (11 / 25 : ℚ), (23 / 50 : ℚ), (39 / 1600 : ℚ), (9 / 20 : ℚ), (2, 15), (2, 18), (2, 17), (0, 4), [(2, 15), (2, 16)], [(2, 17), (2, 18)], [(2, 16), (2, 17)], [(0, 3), (0, 4)]⟩

theorem g066_ok : tagOKF CompactData.T CompactData.F g066 = true := by decide +kernel

def g067 : Tag := .inr ⟨(19 / 800 : ℚ), (1 / 40 : ℚ), (23 / 50 : ℚ), (12 / 25 : ℚ), (39 / 1600 : ℚ), (47 / 100 : ℚ), (2, 16), (2, 19), (2, 18), (0, 4), [(2, 16), (2, 17)], [(2, 18), (2, 19)], [(2, 17), (2, 18)], [(0, 3), (0, 4)]⟩

theorem g067_ok : tagOKF CompactData.T CompactData.F g067 = true := by decide +kernel

def g068 : Tag := .inr ⟨(1 / 40 : ℚ), (21 / 800 : ℚ), (8 / 25 : ℚ), (17 / 50 : ℚ), (41 / 1600 : ℚ), (33 / 100 : ℚ), (2, 9), (2, 12), (2, 10), (0, 5), [(2, 8), (2, 9), (2, 10)], [(2, 11), (2, 12), (2, 13)], [(2, 10), (2, 11)], [(0, 4), (0, 5)]⟩

theorem g068_ok : tagOKF CompactData.T CompactData.F g068 = true := by decide +kernel


end CKLaneC3.CompactBatch04


