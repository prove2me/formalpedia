-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch19_part00
-- name    : CK_CKLaneC3_CompactBatch19_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T21:44:54.974479+00:00
-- url     : https://prove2.me/theorems/99ca6fa9-512f-4ff3-802f-fdf6b4a4fbe2
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch19 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch19 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch19 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch19 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch19 (part 1 of 2).lean)

import Definitions.Def_CK_CKLaneC3_CompactData
import Definitions.Def_CK_CKLaneC3_CompactCoverF

/-! Lane C3 compact cell batch (generated; memoised chains over the data tables). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactBatch19
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF

def g000 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (3 / 100 : ℚ), (1 / 32 : ℚ), (29 / 400 : ℚ), (49 / 1600 : ℚ), (0, 8), (1, 20), (1, 9), (1, 2), [(0, 8), (0, 9)], [(1, 19), (1, 20), (1, 21)], [(1, 8), (1, 9), (1, 10)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g000_ok : tagOKF CompactData.T CompactData.F g000 = true := by decide +kernel

def g001 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (1 / 32 : ℚ), (13 / 400 : ℚ), (29 / 400 : ℚ), (51 / 1600 : ℚ), (0, 9), (1, 20), (1, 9), (1, 2), [(0, 9)], [(1, 20), (1, 21)], [(1, 9), (1, 10)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g001_ok : tagOKF CompactData.T CompactData.F g001 = true := by decide +kernel

def g002 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (31 / 400 : ℚ), (1 / 32 : ℚ), (0, 9), (1, 21), (1, 10), (1, 3), [(0, 8), (0, 9)], [(1, 21), (1, 22)], [(1, 9), (1, 10), (1, 11)], [(1, 3), (1, 4)]⟩

theorem g002_ok : tagOKF CompactData.T CompactData.F g002 = true := by decide +kernel

def g003 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (29 / 400 : ℚ), (27 / 800 : ℚ), (0, 10), (1, 20), (1, 10), (1, 2), [(0, 9), (0, 10), (0, 11)], [(1, 20), (1, 21)], [(1, 9), (1, 10)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g003_ok : tagOKF CompactData.T CompactData.F g003 = true := by decide +kernel

def g004 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (31 / 400 : ℚ), (27 / 800 : ℚ), (0, 10), (1, 22), (1, 11), (1, 3), [(0, 9), (0, 10), (0, 11)], [(1, 21), (1, 22)], [(1, 10), (1, 11)], [(1, 3), (1, 4)]⟩

theorem g004_ok : tagOKF CompactData.T CompactData.F g004 = true := by decide +kernel

def g005 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (29 / 400 : ℚ), (29 / 800 : ℚ), (0, 12), (1, 21), (1, 10), (1, 2), [(0, 11), (0, 12)], [(1, 20), (1, 21)], [(1, 9), (1, 10), (1, 11)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g005_ok : tagOKF CompactData.T CompactData.F g005 = true := by decide +kernel

def g006 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (29 / 400 : ℚ), (31 / 800 : ℚ), (0, 13), (1, 21), (1, 11), (1, 2), [(0, 12), (0, 13), (0, 14)], [(1, 20), (1, 21), (1, 22)], [(1, 10), (1, 11)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g006_ok : tagOKF CompactData.T CompactData.F g006 = true := by decide +kernel

def g007 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (31 / 400 : ℚ), (29 / 800 : ℚ), (0, 12), (1, 22), (1, 11), (1, 3), [(0, 11), (0, 12)], [(1, 21), (1, 22)], [(1, 10), (1, 11), (1, 12)], [(1, 3), (1, 4)]⟩

theorem g007_ok : tagOKF CompactData.T CompactData.F g007 = true := by decide +kernel

def g008 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (31 / 400 : ℚ), (31 / 800 : ℚ), (0, 13), (1, 22), (1, 12), (1, 3), [(0, 12), (0, 13), (0, 14)], [(1, 21), (1, 22), (1, 23)], [(1, 11), (1, 12)], [(1, 3), (1, 4)]⟩

theorem g008_ok : tagOKF CompactData.T CompactData.F g008 = true := by decide +kernel

def g009 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (33 / 800 : ℚ), (33 / 800 : ℚ), (0, 14), (1, 13), (1, 5), (0, 14), [(0, 14), (0, 15)], [(1, 12), (1, 13)], [(1, 4), (1, 5)], [(0, 14), (0, 15)]⟩

theorem g009_ok : tagOKF CompactData.T CompactData.F g009 = true := by decide +kernel

def g010 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (33 / 800 : ℚ), (7 / 160 : ℚ), (0, 16), (1, 13), (1, 5), (0, 14), [(0, 15), (0, 16)], [(1, 13), (1, 14)], [(1, 5), (1, 6)], [(0, 14), (0, 15)]⟩

theorem g010_ok : tagOKF CompactData.T CompactData.F g010 = true := by decide +kernel

def g011 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (7 / 160 : ℚ), (33 / 800 : ℚ), (0, 14), (1, 14), (1, 5), (0, 16), [(0, 14), (0, 15)], [(1, 13), (1, 14)], [(1, 5), (1, 6)], [(0, 15), (0, 16)]⟩

theorem g011_ok : tagOKF CompactData.T CompactData.F g011 = true := by decide +kernel

def g012 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (7 / 160 : ℚ), (7 / 160 : ℚ), (0, 16), (1, 14), (1, 6), (0, 16), [(0, 15), (0, 16)], [(1, 13), (1, 14), (1, 15)], [(1, 5), (1, 6)], [(0, 15), (0, 16)]⟩

theorem g012_ok : tagOKF CompactData.T CompactData.F g012 = true := by decide +kernel

def g013 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (19 / 400 : ℚ), (33 / 800 : ℚ), (37 / 800 : ℚ), (0, 17), (1, 14), (1, 6), (0, 14), [(0, 16), (0, 17)], [(1, 13), (1, 14)], [(1, 5), (1, 6)], [(0, 14), (0, 15)]⟩

theorem g013_ok : tagOKF CompactData.T CompactData.F g013 = true := by decide +kernel

def g014 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (19 / 400 : ℚ), (1 / 20 : ℚ), (33 / 800 : ℚ), (39 / 800 : ℚ), (0, 18), (1, 14), (1, 6), (0, 14), [(0, 17), (0, 18)], [(1, 13), (1, 14), (1, 15)], [(1, 6), (1, 7)], [(0, 14), (0, 15)]⟩

theorem g014_ok : tagOKF CompactData.T CompactData.F g014 = true := by decide +kernel

def g015 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (9 / 200 : ℚ), (19 / 400 : ℚ), (7 / 160 : ℚ), (37 / 800 : ℚ), (0, 17), (1, 14), (1, 6), (0, 16), [(0, 16), (0, 17)], [(1, 14), (1, 15)], [(1, 6), (1, 7)], [(0, 15), (0, 16)]⟩

theorem g015_ok : tagOKF CompactData.T CompactData.F g015 = true := by decide +kernel

def g016 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (19 / 400 : ℚ), (1 / 20 : ℚ), (7 / 160 : ℚ), (39 / 800 : ℚ), (0, 18), (1, 15), (1, 7), (0, 16), [(0, 17), (0, 18)], [(1, 14), (1, 15)], [(1, 6), (1, 7)], [(0, 15), (0, 16)]⟩

theorem g016_ok : tagOKF CompactData.T CompactData.F g016 = true := by decide +kernel

def g017 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (37 / 800 : ℚ), (33 / 800 : ℚ), (0, 14), (1, 14), (1, 6), (0, 17), [(0, 14), (0, 15)], [(1, 14), (1, 15)], [(1, 5), (1, 6)], [(0, 16), (0, 17)]⟩

theorem g017_ok : tagOKF CompactData.T CompactData.F g017 = true := by decide +kernel

def g018 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (39 / 800 : ℚ), (33 / 800 : ℚ), (0, 14), (1, 15), (1, 6), (0, 18), [(0, 14), (0, 15)], [(1, 15), (1, 16)], [(1, 6), (1, 7)], [(0, 17), (0, 18)]⟩

theorem g018_ok : tagOKF CompactData.T CompactData.F g018 = true := by decide +kernel

def g019 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (37 / 800 : ℚ), (7 / 160 : ℚ), (0, 16), (1, 15), (1, 6), (0, 17), [(0, 15), (0, 16)], [(1, 14), (1, 15)], [(1, 6), (1, 7)], [(0, 16), (0, 17)]⟩

theorem g019_ok : tagOKF CompactData.T CompactData.F g019 = true := by decide +kernel

def g020 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (39 / 800 : ℚ), (7 / 160 : ℚ), (0, 16), (1, 16), (1, 7), (0, 18), [(0, 15), (0, 16)], [(1, 15), (1, 16)], [(1, 6), (1, 7)], [(0, 17), (0, 18)]⟩

theorem g020_ok : tagOKF CompactData.T CompactData.F g020 = true := by decide +kernel

def g021 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (9 / 200 : ℚ), (19 / 400 : ℚ), (37 / 800 : ℚ), (37 / 800 : ℚ), (0, 17), (1, 15), (1, 7), (0, 17), [(0, 16), (0, 17)], [(1, 15), (1, 16)], [(1, 6), (1, 7)], [(0, 16), (0, 17)]⟩

theorem g021_ok : tagOKF CompactData.T CompactData.F g021 = true := by decide +kernel

def g022 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (19 / 400 : ℚ), (1 / 20 : ℚ), (37 / 800 : ℚ), (39 / 800 : ℚ), (0, 18), (1, 16), (1, 7), (0, 17), [(0, 17), (0, 18)], [(1, 15), (1, 16)], [(1, 7), (1, 8)], [(0, 16), (0, 17)]⟩

theorem g022_ok : tagOKF CompactData.T CompactData.F g022 = true := by decide +kernel

def g023 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (9 / 200 : ℚ), (19 / 400 : ℚ), (39 / 800 : ℚ), (37 / 800 : ℚ), (0, 17), (1, 16), (1, 7), (0, 18), [(0, 16), (0, 17)], [(1, 15), (1, 16)], [(1, 7), (1, 8)], [(0, 17), (0, 18)]⟩

theorem g023_ok : tagOKF CompactData.T CompactData.F g023 = true := by decide +kernel

def g024 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (19 / 400 : ℚ), (1 / 20 : ℚ), (39 / 800 : ℚ), (39 / 800 : ℚ), (0, 18), (1, 16), (1, 8), (0, 18), [(0, 17), (0, 18)], [(1, 16), (1, 17)], [(1, 7), (1, 8)], [(0, 17), (0, 18)]⟩

theorem g024_ok : tagOKF CompactData.T CompactData.F g024 = true := by decide +kernel

def g025 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (1 / 20 : ℚ), (21 / 400 : ℚ), (33 / 800 : ℚ), (41 / 800 : ℚ), (0, 19), (1, 14), (1, 7), (0, 14), [(0, 18), (0, 19)], [(1, 14), (1, 15)], [(1, 6), (1, 7)], [(0, 14), (0, 15)]⟩

theorem g025_ok : tagOKF CompactData.T CompactData.F g025 = true := by decide +kernel

def g026 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (21 / 400 : ℚ), (11 / 200 : ℚ), (33 / 800 : ℚ), (43 / 800 : ℚ), (0, 20), (1, 15), (1, 7), (0, 14), [(0, 19), (0, 20)], [(1, 14), (1, 15)], [(1, 7), (1, 8)], [(0, 14), (0, 15)]⟩

theorem g026_ok : tagOKF CompactData.T CompactData.F g026 = true := by decide +kernel

def g027 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (1 / 20 : ℚ), (21 / 400 : ℚ), (7 / 160 : ℚ), (41 / 800 : ℚ), (0, 19), (1, 15), (1, 7), (0, 16), [(0, 18), (0, 19)], [(1, 15), (1, 16)], [(1, 7), (1, 8)], [(0, 15), (0, 16)]⟩

theorem g027_ok : tagOKF CompactData.T CompactData.F g027 = true := by decide +kernel

def g028 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (21 / 400 : ℚ), (11 / 200 : ℚ), (7 / 160 : ℚ), (43 / 800 : ℚ), (0, 20), (1, 16), (1, 8), (0, 16), [(0, 19), (0, 20)], [(1, 15), (1, 16)], [(1, 7), (1, 8)], [(0, 15), (0, 16)]⟩

theorem g028_ok : tagOKF CompactData.T CompactData.F g028 = true := by decide +kernel

def g029 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (11 / 200 : ℚ), (23 / 400 : ℚ), (33 / 800 : ℚ), (9 / 160 : ℚ), (0, 21), (1, 15), (1, 8), (0, 14), [(0, 20), (0, 21)], [(1, 15), (1, 16)], [(1, 7), (1, 8)], [(0, 14), (0, 15)]⟩

theorem g029_ok : tagOKF CompactData.T CompactData.F g029 = true := by decide +kernel

def g030 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (23 / 400 : ℚ), (3 / 50 : ℚ), (33 / 800 : ℚ), (47 / 800 : ℚ), (0, 22), (1, 16), (1, 8), (0, 14), [(0, 21), (0, 22)], [(1, 15), (1, 16)], [(1, 8), (1, 9)], [(0, 14), (0, 15)]⟩

theorem g030_ok : tagOKF CompactData.T CompactData.F g030 = true := by decide +kernel

def g031 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (11 / 200 : ℚ), (23 / 400 : ℚ), (7 / 160 : ℚ), (9 / 160 : ℚ), (0, 21), (1, 16), (1, 8), (0, 16), [(0, 20), (0, 21)], [(1, 15), (1, 16)], [(1, 8), (1, 9)], [(0, 15), (0, 16)]⟩

theorem g031_ok : tagOKF CompactData.T CompactData.F g031 = true := by decide +kernel

def g032 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (23 / 400 : ℚ), (3 / 50 : ℚ), (7 / 160 : ℚ), (47 / 800 : ℚ), (0, 22), (1, 16), (1, 9), (0, 16), [(0, 21), (0, 22)], [(1, 16), (1, 17)], [(1, 8), (1, 9)], [(0, 15), (0, 16)]⟩

theorem g032_ok : tagOKF CompactData.T CompactData.F g032 = true := by decide +kernel

def g033 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (1 / 20 : ℚ), (21 / 400 : ℚ), (37 / 800 : ℚ), (41 / 800 : ℚ), (0, 19), (1, 16), (1, 8), (0, 17), [(0, 18), (0, 19)], [(1, 15), (1, 16)], [(1, 7), (1, 8)], [(0, 16), (0, 17)]⟩

theorem g033_ok : tagOKF CompactData.T CompactData.F g033 = true := by decide +kernel

def g034 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (21 / 400 : ℚ), (11 / 200 : ℚ), (37 / 800 : ℚ), (43 / 800 : ℚ), (0, 20), (1, 16), (1, 8), (0, 17), [(0, 19), (0, 20)], [(1, 16), (1, 17)], [(1, 8), (1, 9)], [(0, 16), (0, 17)]⟩

theorem g034_ok : tagOKF CompactData.T CompactData.F g034 = true := by decide +kernel

def g035 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (1 / 20 : ℚ), (21 / 400 : ℚ), (39 / 800 : ℚ), (41 / 800 : ℚ), (0, 19), (1, 17), (1, 8), (0, 18), [(0, 18), (0, 19)], [(1, 16), (1, 17)], [(1, 8), (1, 9)], [(0, 17), (0, 18)]⟩

theorem g035_ok : tagOKF CompactData.T CompactData.F g035 = true := by decide +kernel

def g036 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (21 / 400 : ℚ), (11 / 200 : ℚ), (39 / 800 : ℚ), (43 / 800 : ℚ), (0, 20), (1, 17), (1, 9), (0, 18), [(0, 19), (0, 20)], [(1, 16), (1, 17)], [(1, 8), (1, 9)], [(0, 17), (0, 18)]⟩

theorem g036_ok : tagOKF CompactData.T CompactData.F g036 = true := by decide +kernel

def g037 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (11 / 200 : ℚ), (3 / 50 : ℚ), (37 / 800 : ℚ), (23 / 400 : ℚ), (0, 21), (1, 17), (1, 9), (0, 17), [(0, 20), (0, 21), (0, 22)], [(1, 16), (1, 17)], [(1, 8), (1, 9), (1, 10)], [(0, 16), (0, 17)]⟩

theorem g037_ok : tagOKF CompactData.T CompactData.F g037 = true := by decide +kernel

def g038 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (11 / 200 : ℚ), (3 / 50 : ℚ), (39 / 800 : ℚ), (23 / 400 : ℚ), (0, 21), (1, 17), (1, 10), (0, 18), [(0, 20), (0, 21), (0, 22)], [(1, 17), (1, 18)], [(1, 9), (1, 10)], [(0, 17), (0, 18)]⟩

theorem g038_ok : tagOKF CompactData.T CompactData.F g038 = true := by decide +kernel

def g039 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (41 / 800 : ℚ), (33 / 800 : ℚ), (0, 14), (1, 16), (1, 7), (0, 19), [(0, 14), (0, 15)], [(1, 15), (1, 16)], [(1, 6), (1, 7)], [(0, 18), (0, 19)]⟩

theorem g039_ok : tagOKF CompactData.T CompactData.F g039 = true := by decide +kernel

def g040 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (43 / 800 : ℚ), (33 / 800 : ℚ), (0, 14), (1, 17), (1, 7), (0, 20), [(0, 14), (0, 15)], [(1, 16), (1, 17)], [(1, 7), (1, 8)], [(0, 19), (0, 20)]⟩

theorem g040_ok : tagOKF CompactData.T CompactData.F g040 = true := by decide +kernel

def g041 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (41 / 800 : ℚ), (7 / 160 : ℚ), (0, 16), (1, 16), (1, 7), (0, 19), [(0, 15), (0, 16)], [(1, 16), (1, 17)], [(1, 7), (1, 8)], [(0, 18), (0, 19)]⟩

theorem g041_ok : tagOKF CompactData.T CompactData.F g041 = true := by decide +kernel

def g042 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (43 / 800 : ℚ), (7 / 160 : ℚ), (0, 16), (1, 17), (1, 8), (0, 20), [(0, 15), (0, 16)], [(1, 16), (1, 17)], [(1, 7), (1, 8)], [(0, 19), (0, 20)]⟩

theorem g042_ok : tagOKF CompactData.T CompactData.F g042 = true := by decide +kernel

def g043 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (9 / 160 : ℚ), (33 / 800 : ℚ), (0, 14), (1, 17), (1, 8), (0, 21), [(0, 14), (0, 15)], [(1, 17), (1, 18)], [(1, 7), (1, 8)], [(0, 20), (0, 21)]⟩

theorem g043_ok : tagOKF CompactData.T CompactData.F g043 = true := by decide +kernel

def g044 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (1 / 25 : ℚ), (17 / 400 : ℚ), (47 / 800 : ℚ), (33 / 800 : ℚ), (0, 14), (1, 18), (1, 8), (0, 22), [(0, 14), (0, 15)], [(1, 17), (1, 18)], [(1, 8), (1, 9)], [(0, 21), (0, 22)]⟩

theorem g044_ok : tagOKF CompactData.T CompactData.F g044 = true := by decide +kernel

def g045 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (9 / 160 : ℚ), (7 / 160 : ℚ), (0, 16), (1, 18), (1, 8), (0, 21), [(0, 15), (0, 16)], [(1, 17), (1, 18)], [(1, 8), (1, 9)], [(0, 20), (0, 21)]⟩

theorem g045_ok : tagOKF CompactData.T CompactData.F g045 = true := by decide +kernel

def g046 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (17 / 400 : ℚ), (9 / 200 : ℚ), (47 / 800 : ℚ), (7 / 160 : ℚ), (0, 16), (1, 18), (1, 9), (0, 22), [(0, 15), (0, 16)], [(1, 18), (1, 19)], [(1, 8), (1, 9)], [(0, 21), (0, 22)]⟩

theorem g046_ok : tagOKF CompactData.T CompactData.F g046 = true := by decide +kernel

def g047 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (9 / 200 : ℚ), (19 / 400 : ℚ), (41 / 800 : ℚ), (37 / 800 : ℚ), (0, 17), (1, 17), (1, 8), (0, 19), [(0, 16), (0, 17)], [(1, 16), (1, 17)], [(1, 7), (1, 8)], [(0, 18), (0, 19)]⟩

theorem g047_ok : tagOKF CompactData.T CompactData.F g047 = true := by decide +kernel

def g048 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (9 / 200 : ℚ), (19 / 400 : ℚ), (43 / 800 : ℚ), (37 / 800 : ℚ), (0, 17), (1, 17), (1, 8), (0, 20), [(0, 16), (0, 17)], [(1, 17), (1, 18)], [(1, 8), (1, 9)], [(0, 19), (0, 20)]⟩

theorem g048_ok : tagOKF CompactData.T CompactData.F g048 = true := by decide +kernel

def g049 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (19 / 400 : ℚ), (1 / 20 : ℚ), (41 / 800 : ℚ), (39 / 800 : ℚ), (0, 18), (1, 17), (1, 8), (0, 19), [(0, 17), (0, 18)], [(1, 16), (1, 17)], [(1, 8), (1, 9)], [(0, 18), (0, 19)]⟩

theorem g049_ok : tagOKF CompactData.T CompactData.F g049 = true := by decide +kernel

def g050 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (19 / 400 : ℚ), (1 / 20 : ℚ), (43 / 800 : ℚ), (39 / 800 : ℚ), (0, 18), (1, 18), (1, 9), (0, 20), [(0, 17), (0, 18)], [(1, 17), (1, 18)], [(1, 8), (1, 9)], [(0, 19), (0, 20)]⟩

theorem g050_ok : tagOKF CompactData.T CompactData.F g050 = true := by decide +kernel

def g051 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (9 / 200 : ℚ), (19 / 400 : ℚ), (9 / 160 : ℚ), (37 / 800 : ℚ), (0, 17), (1, 18), (1, 9), (0, 21), [(0, 16), (0, 17)], [(1, 17), (1, 18)], [(1, 8), (1, 9)], [(0, 20), (0, 21)]⟩

theorem g051_ok : tagOKF CompactData.T CompactData.F g051 = true := by decide +kernel

def g052 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (9 / 200 : ℚ), (19 / 400 : ℚ), (47 / 800 : ℚ), (37 / 800 : ℚ), (0, 17), (1, 19), (1, 9), (0, 22), [(0, 16), (0, 17)], [(1, 18), (1, 19)], [(1, 9), (1, 10)], [(0, 21), (0, 22)]⟩

theorem g052_ok : tagOKF CompactData.T CompactData.F g052 = true := by decide +kernel

def g053 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (19 / 400 : ℚ), (1 / 20 : ℚ), (9 / 160 : ℚ), (39 / 800 : ℚ), (0, 18), (1, 18), (1, 9), (0, 21), [(0, 17), (0, 18)], [(1, 18), (1, 19)], [(1, 9), (1, 10)], [(0, 20), (0, 21)]⟩

theorem g053_ok : tagOKF CompactData.T CompactData.F g053 = true := by decide +kernel

def g054 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (19 / 400 : ℚ), (1 / 20 : ℚ), (47 / 800 : ℚ), (39 / 800 : ℚ), (0, 18), (1, 19), (1, 10), (0, 22), [(0, 17), (0, 18)], [(1, 18), (1, 19)], [(1, 9), (1, 10)], [(0, 21), (0, 22)]⟩

theorem g054_ok : tagOKF CompactData.T CompactData.F g054 = true := by decide +kernel

def g055 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (1 / 20 : ℚ), (11 / 200 : ℚ), (41 / 800 : ℚ), (21 / 400 : ℚ), (0, 19), (1, 17), (1, 9), (0, 19), [(0, 18), (0, 19), (0, 20)], [(1, 17), (1, 18)], [(1, 8), (1, 9), (1, 10)], [(0, 18), (0, 19)]⟩

theorem g055_ok : tagOKF CompactData.T CompactData.F g055 = true := by decide +kernel

def g056 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (1 / 20 : ℚ), (11 / 200 : ℚ), (43 / 800 : ℚ), (21 / 400 : ℚ), (0, 19), (1, 18), (1, 10), (0, 20), [(0, 18), (0, 19), (0, 20)], [(1, 17), (1, 18), (1, 19)], [(1, 9), (1, 10)], [(0, 19), (0, 20)]⟩

theorem g056_ok : tagOKF CompactData.T CompactData.F g056 = true := by decide +kernel

def g057 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (11 / 200 : ℚ), (3 / 50 : ℚ), (41 / 800 : ℚ), (23 / 400 : ℚ), (0, 21), (1, 18), (1, 10), (0, 19), [(0, 20), (0, 21), (0, 22)], [(1, 17), (1, 18), (1, 19)], [(1, 9), (1, 10), (1, 11)], [(0, 18), (0, 19)]⟩

theorem g057_ok : tagOKF CompactData.T CompactData.F g057 = true := by decide +kernel

def g058 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (11 / 200 : ℚ), (3 / 50 : ℚ), (43 / 800 : ℚ), (23 / 400 : ℚ), (0, 21), (1, 19), (1, 11), (0, 20), [(0, 20), (0, 21), (0, 22)], [(1, 18), (1, 19)], [(1, 10), (1, 11)], [(0, 19), (0, 20)]⟩

theorem g058_ok : tagOKF CompactData.T CompactData.F g058 = true := by decide +kernel

def g059 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (1 / 20 : ℚ), (21 / 400 : ℚ), (23 / 400 : ℚ), (41 / 800 : ℚ), (0, 19), (1, 19), (1, 10), (0, 21), [(0, 18), (0, 19)], [(1, 18), (1, 19), (1, 20)], [(1, 9), (1, 10), (1, 11)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g059_ok : tagOKF CompactData.T CompactData.F g059 = true := by decide +kernel

def g060 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (21 / 400 : ℚ), (11 / 200 : ℚ), (23 / 400 : ℚ), (43 / 800 : ℚ), (0, 20), (1, 19), (1, 11), (0, 21), [(0, 19), (0, 20)], [(1, 18), (1, 19), (1, 20)], [(1, 10), (1, 11)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g060_ok : tagOKF CompactData.T CompactData.F g060 = true := by decide +kernel

def g061 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (11 / 200 : ℚ), (3 / 50 : ℚ), (9 / 160 : ℚ), (23 / 400 : ℚ), (0, 21), (1, 19), (1, 11), (0, 21), [(0, 20), (0, 21), (0, 22)], [(1, 19), (1, 20)], [(1, 10), (1, 11), (1, 12)], [(0, 20), (0, 21)]⟩

theorem g061_ok : tagOKF CompactData.T CompactData.F g061 = true := by decide +kernel


end CKLaneC3.CompactBatch19


