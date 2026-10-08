-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch21
-- name    : CK_CKLaneC3_CompactBatch21
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T07:15:12.316173+00:00
-- url     : https://prove2.me/theorems/01a94877-9ece-4001-be70-2249a56051e2
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch21` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch21` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch21` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch21 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch21.lean)

import Definitions.Def_CK_CKLaneC3_CompactData
import Definitions.Def_CK_CKLaneC3_CompactCoverF

-- ===== source module CKLaneC3.CompactBatch21 =====
section

/-! Lane C3 compact cell batch (generated; memoised chains over the data tables). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactBatch21
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF

def g000 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (13 / 100 : ℚ), (7 / 50 : ℚ), (27 / 400 : ℚ), (27 / 200 : ℚ), (1, 15), (2, 5), (1, 23), (1, 0), [(1, 14), (1, 15)], [(2, 4), (2, 5), (2, 6)], [(1, 22), (1, 23), (2, 0)], [(1, 0), (1, 1)]⟩

theorem g000_ok : tagOKF CompactData.T CompactData.F g000 = true := by decide +kernel

def g001 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (7 / 50 : ℚ), (3 / 20 : ℚ), (1 / 16 : ℚ), (29 / 200 : ℚ), (1, 16), (2, 5), (1, 23), (0, 23), [(1, 15), (1, 16), (1, 17)], [(2, 4), (2, 5), (2, 6)], [(1, 23), (2, 0)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g001_ok : tagOKF CompactData.T CompactData.F g001 = true := by decide +kernel

def g002 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (3 / 20 : ℚ), (4 / 25 : ℚ), (1 / 16 : ℚ), (31 / 200 : ℚ), (1, 17), (2, 6), (2, 0), (0, 23), [(1, 17), (1, 18)], [(2, 5), (2, 6)], [(2, 0), (2, 1)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g002_ok : tagOKF CompactData.T CompactData.F g002 = true := by decide +kernel

def g003 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (7 / 50 : ℚ), (3 / 20 : ℚ), (27 / 400 : ℚ), (29 / 200 : ℚ), (1, 16), (2, 6), (2, 0), (1, 0), [(1, 15), (1, 16), (1, 17)], [(2, 5), (2, 6)], [(1, 23), (2, 0), (2, 1)], [(1, 0), (1, 1)]⟩

theorem g003_ok : tagOKF CompactData.T CompactData.F g003 = true := by decide +kernel

def g004 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (3 / 20 : ℚ), (4 / 25 : ℚ), (27 / 400 : ℚ), (31 / 200 : ℚ), (1, 17), (2, 6), (2, 1), (1, 0), [(1, 17), (1, 18)], [(2, 6), (2, 7)], [(2, 0), (2, 1), (2, 2)], [(1, 0), (1, 1)]⟩

theorem g004_ok : tagOKF CompactData.T CompactData.F g004 = true := by decide +kernel

def g005 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (3 / 25 : ℚ), (13 / 100 : ℚ), (29 / 400 : ℚ), (1 / 8 : ℚ), (1, 13), (2, 5), (1, 22), (1, 2), [(1, 12), (1, 13), (1, 14)], [(2, 4), (2, 5), (2, 6)], [(1, 22), (1, 23)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g005_ok : tagOKF CompactData.T CompactData.F g005 = true := by decide +kernel

def g006 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (3 / 25 : ℚ), (13 / 100 : ℚ), (31 / 400 : ℚ), (1 / 8 : ℚ), (1, 13), (2, 6), (1, 23), (1, 3), [(1, 12), (1, 13), (1, 14)], [(2, 5), (2, 6)], [(1, 22), (1, 23), (2, 0)], [(1, 3), (1, 4)]⟩

theorem g006_ok : tagOKF CompactData.T CompactData.F g006 = true := by decide +kernel

def g007 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (13 / 100 : ℚ), (7 / 50 : ℚ), (29 / 400 : ℚ), (27 / 200 : ℚ), (1, 15), (2, 6), (1, 23), (1, 2), [(1, 14), (1, 15)], [(2, 5), (2, 6)], [(1, 23), (2, 0)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g007_ok : tagOKF CompactData.T CompactData.F g007 = true := by decide +kernel

def g008 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (13 / 100 : ℚ), (7 / 50 : ℚ), (31 / 400 : ℚ), (27 / 200 : ℚ), (1, 15), (2, 6), (2, 0), (1, 3), [(1, 14), (1, 15)], [(2, 6), (2, 7)], [(1, 23), (2, 0), (2, 1)], [(1, 3), (1, 4)]⟩

theorem g008_ok : tagOKF CompactData.T CompactData.F g008 = true := by decide +kernel

def g009 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (7 / 50 : ℚ), (3 / 20 : ℚ), (29 / 400 : ℚ), (29 / 200 : ℚ), (1, 16), (2, 6), (2, 0), (1, 2), [(1, 15), (1, 16), (1, 17)], [(2, 6), (2, 7)], [(2, 0), (2, 1)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g009_ok : tagOKF CompactData.T CompactData.F g009 = true := by decide +kernel

def g010 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (3 / 20 : ℚ), (4 / 25 : ℚ), (29 / 400 : ℚ), (31 / 200 : ℚ), (1, 17), (2, 7), (2, 1), (1, 2), [(1, 17), (1, 18)], [(2, 6), (2, 7), (2, 8)], [(2, 1), (2, 2)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g010_ok : tagOKF CompactData.T CompactData.F g010 = true := by decide +kernel

def g011 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (7 / 50 : ℚ), (3 / 20 : ℚ), (31 / 400 : ℚ), (29 / 200 : ℚ), (1, 16), (2, 7), (2, 1), (1, 3), [(1, 15), (1, 16), (1, 17)], [(2, 6), (2, 7), (2, 8)], [(2, 0), (2, 1), (2, 2)], [(1, 3), (1, 4)]⟩

theorem g011_ok : tagOKF CompactData.T CompactData.F g011 = true := by decide +kernel

def g012 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (3 / 20 : ℚ), (4 / 25 : ℚ), (31 / 400 : ℚ), (31 / 200 : ℚ), (1, 17), (2, 8), (2, 2), (1, 3), [(1, 17), (1, 18)], [(2, 7), (2, 8)], [(2, 1), (2, 2)], [(1, 3), (1, 4)]⟩

theorem g012_ok : tagOKF CompactData.T CompactData.F g012 = true := by decide +kernel

def g013 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (4 / 25 : ℚ), (17 / 100 : ℚ), (33 / 800 : ℚ), (33 / 200 : ℚ), (1, 19), (2, 3), (1, 23), (0, 14), [(1, 18), (1, 19)], [(2, 2), (2, 3), (2, 4)], [(1, 23), (2, 0)], [(0, 14), (0, 15)]⟩

theorem g013_ok : tagOKF CompactData.T CompactData.F g013 = true := by decide +kernel

def g014 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (17 / 100 : ℚ), (9 / 50 : ℚ), (33 / 800 : ℚ), (7 / 40 : ℚ), (1, 20), (2, 4), (2, 0), (0, 14), [(1, 19), (1, 20), (1, 21)], [(2, 3), (2, 4)], [(2, 0), (2, 1)], [(0, 14), (0, 15)]⟩

theorem g014_ok : tagOKF CompactData.T CompactData.F g014 = true := by decide +kernel

def g015 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (4 / 25 : ℚ), (17 / 100 : ℚ), (7 / 160 : ℚ), (33 / 200 : ℚ), (1, 19), (2, 3), (2, 0), (0, 16), [(1, 18), (1, 19)], [(2, 3), (2, 4)], [(1, 23), (2, 0)], [(0, 15), (0, 16)]⟩

theorem g015_ok : tagOKF CompactData.T CompactData.F g015 = true := by decide +kernel

def g016 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (17 / 100 : ℚ), (9 / 50 : ℚ), (7 / 160 : ℚ), (7 / 40 : ℚ), (1, 20), (2, 4), (2, 1), (0, 16), [(1, 19), (1, 20), (1, 21)], [(2, 4), (2, 5)], [(2, 0), (2, 1)], [(0, 15), (0, 16)]⟩

theorem g016_ok : tagOKF CompactData.T CompactData.F g016 = true := by decide +kernel

def g017 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (9 / 50 : ℚ), (19 / 100 : ℚ), (33 / 800 : ℚ), (37 / 200 : ℚ), (1, 21), (2, 5), (2, 1), (0, 14), [(1, 21), (1, 22)], [(2, 4), (2, 5)], [(2, 1), (2, 2)], [(0, 14), (0, 15)]⟩

theorem g017_ok : tagOKF CompactData.T CompactData.F g017 = true := by decide +kernel

def g018 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (19 / 100 : ℚ), (1 / 5 : ℚ), (33 / 800 : ℚ), (39 / 200 : ℚ), (1, 22), (2, 5), (2, 2), (0, 14), [(1, 22), (1, 23)], [(2, 5), (2, 6)], [(2, 2), (2, 3)], [(0, 14), (0, 15)]⟩

theorem g018_ok : tagOKF CompactData.T CompactData.F g018 = true := by decide +kernel

def g019 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (9 / 50 : ℚ), (19 / 100 : ℚ), (7 / 160 : ℚ), (37 / 200 : ℚ), (1, 21), (2, 5), (2, 1), (0, 16), [(1, 21), (1, 22)], [(2, 4), (2, 5), (2, 6)], [(2, 1), (2, 2)], [(0, 15), (0, 16)]⟩

theorem g019_ok : tagOKF CompactData.T CompactData.F g019 = true := by decide +kernel

def g020 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (19 / 100 : ℚ), (1 / 5 : ℚ), (7 / 160 : ℚ), (39 / 200 : ℚ), (1, 22), (2, 6), (2, 2), (0, 16), [(1, 22), (1, 23)], [(2, 5), (2, 6)], [(2, 2), (2, 3)], [(0, 15), (0, 16)]⟩

theorem g020_ok : tagOKF CompactData.T CompactData.F g020 = true := by decide +kernel

def g021 : Tag := .inr ⟨(9 / 200 : ℚ), (1 / 20 : ℚ), (4 / 25 : ℚ), (17 / 100 : ℚ), (19 / 400 : ℚ), (33 / 200 : ℚ), (1, 19), (2, 4), (2, 0), (0, 17), [(1, 18), (1, 19)], [(2, 3), (2, 4), (2, 5)], [(1, 23), (2, 0), (2, 1)], [(0, 16), (0, 17), (0, 18)]⟩

theorem g021_ok : tagOKF CompactData.T CompactData.F g021 = true := by decide +kernel

def g022 : Tag := .inr ⟨(9 / 200 : ℚ), (1 / 20 : ℚ), (17 / 100 : ℚ), (9 / 50 : ℚ), (19 / 400 : ℚ), (7 / 40 : ℚ), (1, 20), (2, 5), (2, 1), (0, 17), [(1, 19), (1, 20), (1, 21)], [(2, 4), (2, 5), (2, 6)], [(2, 0), (2, 1), (2, 2)], [(0, 16), (0, 17), (0, 18)]⟩

theorem g022_ok : tagOKF CompactData.T CompactData.F g022 = true := by decide +kernel

def g023 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (9 / 50 : ℚ), (19 / 100 : ℚ), (37 / 800 : ℚ), (37 / 200 : ℚ), (1, 21), (2, 5), (2, 2), (0, 17), [(1, 21), (1, 22)], [(2, 5), (2, 6)], [(2, 1), (2, 2)], [(0, 16), (0, 17)]⟩

theorem g023_ok : tagOKF CompactData.T CompactData.F g023 = true := by decide +kernel

def g024 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (19 / 100 : ℚ), (1 / 5 : ℚ), (37 / 800 : ℚ), (39 / 200 : ℚ), (1, 22), (2, 6), (2, 3), (0, 17), [(1, 22), (1, 23)], [(2, 6), (2, 7)], [(2, 2), (2, 3)], [(0, 16), (0, 17)]⟩

theorem g024_ok : tagOKF CompactData.T CompactData.F g024 = true := by decide +kernel

def g025 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (9 / 50 : ℚ), (19 / 100 : ℚ), (39 / 800 : ℚ), (37 / 200 : ℚ), (1, 21), (2, 6), (2, 2), (0, 18), [(1, 21), (1, 22)], [(2, 5), (2, 6)], [(2, 1), (2, 2)], [(0, 17), (0, 18)]⟩

theorem g025_ok : tagOKF CompactData.T CompactData.F g025 = true := by decide +kernel

def g026 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (19 / 100 : ℚ), (1 / 5 : ℚ), (39 / 800 : ℚ), (39 / 200 : ℚ), (1, 22), (2, 6), (2, 3), (0, 18), [(1, 22), (1, 23)], [(2, 6), (2, 7)], [(2, 2), (2, 3)], [(0, 17), (0, 18)]⟩

theorem g026_ok : tagOKF CompactData.T CompactData.F g026 = true := by decide +kernel

def g027 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (1 / 5 : ℚ), (21 / 100 : ℚ), (33 / 800 : ℚ), (41 / 200 : ℚ), (1, 23), (2, 6), (2, 3), (0, 14), [(1, 23), (2, 0)], [(2, 6), (2, 7)], [(2, 2), (2, 3)], [(0, 14), (0, 15)]⟩

theorem g027_ok : tagOKF CompactData.T CompactData.F g027 = true := by decide +kernel

def g028 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (21 / 100 : ℚ), (11 / 50 : ℚ), (33 / 800 : ℚ), (43 / 200 : ℚ), (2, 0), (2, 7), (2, 4), (0, 14), [(2, 0), (2, 1)], [(2, 6), (2, 7)], [(2, 3), (2, 4)], [(0, 14), (0, 15)]⟩

theorem g028_ok : tagOKF CompactData.T CompactData.F g028 = true := by decide +kernel

def g029 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (1 / 5 : ℚ), (21 / 100 : ℚ), (7 / 160 : ℚ), (41 / 200 : ℚ), (1, 23), (2, 6), (2, 3), (0, 16), [(1, 23), (2, 0)], [(2, 6), (2, 7)], [(2, 3), (2, 4)], [(0, 15), (0, 16)]⟩

theorem g029_ok : tagOKF CompactData.T CompactData.F g029 = true := by decide +kernel

def g030 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (21 / 100 : ℚ), (11 / 50 : ℚ), (7 / 160 : ℚ), (43 / 200 : ℚ), (2, 0), (2, 7), (2, 4), (0, 16), [(2, 0), (2, 1)], [(2, 7), (2, 8)], [(2, 3), (2, 4)], [(0, 15), (0, 16)]⟩

theorem g030_ok : tagOKF CompactData.T CompactData.F g030 = true := by decide +kernel

def g031 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (11 / 50 : ℚ), (23 / 100 : ℚ), (33 / 800 : ℚ), (9 / 40 : ℚ), (2, 1), (2, 8), (2, 5), (0, 14), [(2, 1), (2, 2)], [(2, 7), (2, 8)], [(2, 4), (2, 5)], [(0, 14), (0, 15)]⟩

theorem g031_ok : tagOKF CompactData.T CompactData.F g031 = true := by decide +kernel

def g032 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (23 / 100 : ℚ), (6 / 25 : ℚ), (33 / 800 : ℚ), (47 / 200 : ℚ), (2, 2), (2, 8), (2, 5), (0, 14), [(2, 2)], [(2, 8), (2, 9)], [(2, 5), (2, 6)], [(0, 14), (0, 15)]⟩

theorem g032_ok : tagOKF CompactData.T CompactData.F g032 = true := by decide +kernel

def g033 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (11 / 50 : ℚ), (23 / 100 : ℚ), (7 / 160 : ℚ), (9 / 40 : ℚ), (2, 1), (2, 8), (2, 5), (0, 16), [(2, 1), (2, 2)], [(2, 7), (2, 8)], [(2, 4), (2, 5)], [(0, 15), (0, 16)]⟩

theorem g033_ok : tagOKF CompactData.T CompactData.F g033 = true := by decide +kernel

def g034 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (23 / 100 : ℚ), (6 / 25 : ℚ), (7 / 160 : ℚ), (47 / 200 : ℚ), (2, 2), (2, 8), (2, 5), (0, 16), [(2, 2)], [(2, 8), (2, 9)], [(2, 5), (2, 6)], [(0, 15), (0, 16)]⟩

theorem g034_ok : tagOKF CompactData.T CompactData.F g034 = true := by decide +kernel

def g035 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (1 / 5 : ℚ), (21 / 100 : ℚ), (37 / 800 : ℚ), (41 / 200 : ℚ), (1, 23), (2, 7), (2, 3), (0, 17), [(1, 23), (2, 0)], [(2, 6), (2, 7)], [(2, 3), (2, 4)], [(0, 16), (0, 17)]⟩

theorem g035_ok : tagOKF CompactData.T CompactData.F g035 = true := by decide +kernel

def g036 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (21 / 100 : ℚ), (11 / 50 : ℚ), (37 / 800 : ℚ), (43 / 200 : ℚ), (2, 0), (2, 8), (2, 4), (0, 17), [(2, 0), (2, 1)], [(2, 7), (2, 8)], [(2, 4), (2, 5)], [(0, 16), (0, 17)]⟩

theorem g036_ok : tagOKF CompactData.T CompactData.F g036 = true := by decide +kernel

def g037 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (1 / 5 : ℚ), (21 / 100 : ℚ), (39 / 800 : ℚ), (41 / 200 : ℚ), (1, 23), (2, 7), (2, 4), (0, 18), [(1, 23), (2, 0)], [(2, 7), (2, 8)], [(2, 3), (2, 4)], [(0, 17), (0, 18)]⟩

theorem g037_ok : tagOKF CompactData.T CompactData.F g037 = true := by decide +kernel

def g038 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (21 / 100 : ℚ), (11 / 50 : ℚ), (39 / 800 : ℚ), (43 / 200 : ℚ), (2, 0), (2, 8), (2, 4), (0, 18), [(2, 0), (2, 1)], [(2, 7), (2, 8)], [(2, 4), (2, 5)], [(0, 17), (0, 18)]⟩

theorem g038_ok : tagOKF CompactData.T CompactData.F g038 = true := by decide +kernel

def g039 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (11 / 50 : ℚ), (6 / 25 : ℚ), (37 / 800 : ℚ), (23 / 100 : ℚ), (2, 2), (2, 8), (2, 5), (0, 17), [(2, 1), (2, 2)], [(2, 8), (2, 9)], [(2, 4), (2, 5), (2, 6)], [(0, 16), (0, 17)]⟩

theorem g039_ok : tagOKF CompactData.T CompactData.F g039 = true := by decide +kernel

def g040 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (11 / 50 : ℚ), (6 / 25 : ℚ), (39 / 800 : ℚ), (23 / 100 : ℚ), (2, 2), (2, 9), (2, 5), (0, 18), [(2, 1), (2, 2)], [(2, 8), (2, 9), (2, 10)], [(2, 5), (2, 6)], [(0, 17), (0, 18)]⟩

theorem g040_ok : tagOKF CompactData.T CompactData.F g040 = true := by decide +kernel

def g041 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (4 / 25 : ℚ), (17 / 100 : ℚ), (21 / 400 : ℚ), (33 / 200 : ℚ), (1, 19), (2, 5), (2, 0), (0, 19), [(1, 18), (1, 19)], [(2, 4), (2, 5), (2, 6)], [(2, 0), (2, 1)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g041_ok : tagOKF CompactData.T CompactData.F g041 = true := by decide +kernel

def g042 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (17 / 100 : ℚ), (9 / 50 : ℚ), (21 / 400 : ℚ), (7 / 40 : ℚ), (1, 20), (2, 6), (2, 1), (0, 19), [(1, 19), (1, 20), (1, 21)], [(2, 5), (2, 6)], [(2, 1), (2, 2)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g042_ok : tagOKF CompactData.T CompactData.F g042 = true := by decide +kernel

def g043 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (4 / 25 : ℚ), (17 / 100 : ℚ), (23 / 400 : ℚ), (33 / 200 : ℚ), (1, 19), (2, 6), (2, 1), (0, 21), [(1, 18), (1, 19)], [(2, 5), (2, 6)], [(2, 0), (2, 1), (2, 2)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g043_ok : tagOKF CompactData.T CompactData.F g043 = true := by decide +kernel

def g044 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (17 / 100 : ℚ), (9 / 50 : ℚ), (23 / 400 : ℚ), (7 / 40 : ℚ), (1, 20), (2, 6), (2, 2), (0, 21), [(1, 19), (1, 20), (1, 21)], [(2, 6), (2, 7)], [(2, 1), (2, 2)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g044_ok : tagOKF CompactData.T CompactData.F g044 = true := by decide +kernel

def g045 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (9 / 50 : ℚ), (19 / 100 : ℚ), (21 / 400 : ℚ), (37 / 200 : ℚ), (1, 21), (2, 6), (2, 2), (0, 19), [(1, 21), (1, 22)], [(2, 6), (2, 7)], [(2, 2), (2, 3)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g045_ok : tagOKF CompactData.T CompactData.F g045 = true := by decide +kernel

def g046 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (19 / 100 : ℚ), (1 / 5 : ℚ), (21 / 400 : ℚ), (39 / 200 : ℚ), (1, 22), (2, 7), (2, 3), (0, 19), [(1, 22), (1, 23)], [(2, 6), (2, 7), (2, 8)], [(2, 2), (2, 3), (2, 4)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g046_ok : tagOKF CompactData.T CompactData.F g046 = true := by decide +kernel

def g047 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (9 / 50 : ℚ), (19 / 100 : ℚ), (23 / 400 : ℚ), (37 / 200 : ℚ), (1, 21), (2, 7), (2, 3), (0, 21), [(1, 21), (1, 22)], [(2, 6), (2, 7), (2, 8)], [(2, 2), (2, 3)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g047_ok : tagOKF CompactData.T CompactData.F g047 = true := by decide +kernel

def g048 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (19 / 100 : ℚ), (1 / 5 : ℚ), (23 / 400 : ℚ), (39 / 200 : ℚ), (1, 22), (2, 8), (2, 3), (0, 21), [(1, 22), (1, 23)], [(2, 7), (2, 8)], [(2, 3), (2, 4)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g048_ok : tagOKF CompactData.T CompactData.F g048 = true := by decide +kernel

def g049 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (1 / 5 : ℚ), (11 / 50 : ℚ), (41 / 800 : ℚ), (21 / 100 : ℚ), (2, 0), (2, 8), (2, 4), (0, 19), [(1, 23), (2, 0), (2, 1)], [(2, 7), (2, 8), (2, 9)], [(2, 3), (2, 4), (2, 5)], [(0, 18), (0, 19)]⟩

theorem g049_ok : tagOKF CompactData.T CompactData.F g049 = true := by decide +kernel

def g050 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (1 / 5 : ℚ), (11 / 50 : ℚ), (43 / 800 : ℚ), (21 / 100 : ℚ), (2, 0), (2, 8), (2, 4), (0, 20), [(1, 23), (2, 0), (2, 1)], [(2, 7), (2, 8), (2, 9)], [(2, 3), (2, 4), (2, 5)], [(0, 19), (0, 20)]⟩

theorem g050_ok : tagOKF CompactData.T CompactData.F g050 = true := by decide +kernel

def g051 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (11 / 50 : ℚ), (6 / 25 : ℚ), (41 / 800 : ℚ), (23 / 100 : ℚ), (2, 2), (2, 9), (2, 6), (0, 19), [(2, 1), (2, 2)], [(2, 8), (2, 9), (2, 10)], [(2, 5), (2, 6)], [(0, 18), (0, 19)]⟩

theorem g051_ok : tagOKF CompactData.T CompactData.F g051 = true := by decide +kernel

def g052 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (11 / 50 : ℚ), (6 / 25 : ℚ), (43 / 800 : ℚ), (23 / 100 : ℚ), (2, 2), (2, 9), (2, 6), (0, 20), [(2, 1), (2, 2)], [(2, 9), (2, 10)], [(2, 5), (2, 6), (2, 7)], [(0, 19), (0, 20)]⟩

theorem g052_ok : tagOKF CompactData.T CompactData.F g052 = true := by decide +kernel

def g053 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (1 / 5 : ℚ), (21 / 100 : ℚ), (23 / 400 : ℚ), (41 / 200 : ℚ), (1, 23), (2, 8), (2, 4), (0, 21), [(1, 23), (2, 0)], [(2, 8), (2, 9)], [(2, 4), (2, 5)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g053_ok : tagOKF CompactData.T CompactData.F g053 = true := by decide +kernel

def g054 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (21 / 100 : ℚ), (11 / 50 : ℚ), (23 / 400 : ℚ), (43 / 200 : ℚ), (2, 0), (2, 9), (2, 5), (0, 21), [(2, 0), (2, 1)], [(2, 8), (2, 9), (2, 10)], [(2, 4), (2, 5), (2, 6)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g054_ok : tagOKF CompactData.T CompactData.F g054 = true := by decide +kernel

def g055 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (11 / 50 : ℚ), (6 / 25 : ℚ), (23 / 400 : ℚ), (23 / 100 : ℚ), (2, 2), (2, 10), (2, 6), (0, 21), [(2, 1), (2, 2)], [(2, 9), (2, 10), (2, 11)], [(2, 5), (2, 6), (2, 7)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g055_ok : tagOKF CompactData.T CompactData.F g055 = true := by decide +kernel

def g056 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (6 / 25 : ℚ), (13 / 50 : ℚ), (33 / 800 : ℚ), (1 / 4 : ℚ), (2, 3), (2, 9), (2, 6), (0, 14), [(2, 2), (2, 3), (2, 4)], [(2, 8), (2, 9), (2, 10)], [(2, 6), (2, 7)], [(0, 14), (0, 15)]⟩

theorem g056_ok : tagOKF CompactData.T CompactData.F g056 = true := by decide +kernel

def g057 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (6 / 25 : ℚ), (13 / 50 : ℚ), (7 / 160 : ℚ), (1 / 4 : ℚ), (2, 3), (2, 9), (2, 7), (0, 16), [(2, 2), (2, 3), (2, 4)], [(2, 9), (2, 10)], [(2, 6), (2, 7)], [(0, 15), (0, 16)]⟩

theorem g057_ok : tagOKF CompactData.T CompactData.F g057 = true := by decide +kernel

def g058 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (33 / 800 : ℚ), (27 / 100 : ℚ), (2, 5), (2, 10), (2, 8), (0, 14), [(2, 4), (2, 5), (2, 6)], [(2, 10), (2, 11)], [(2, 7), (2, 8)], [(0, 14), (0, 15)]⟩

theorem g058_ok : tagOKF CompactData.T CompactData.F g058 = true := by decide +kernel

def g059 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (7 / 160 : ℚ), (27 / 100 : ℚ), (2, 5), (2, 11), (2, 8), (0, 16), [(2, 4), (2, 5), (2, 6)], [(2, 10), (2, 11)], [(2, 7), (2, 8), (2, 9)], [(0, 15), (0, 16)]⟩

theorem g059_ok : tagOKF CompactData.T CompactData.F g059 = true := by decide +kernel

def g060 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (6 / 25 : ℚ), (13 / 50 : ℚ), (37 / 800 : ℚ), (1 / 4 : ℚ), (2, 3), (2, 10), (2, 7), (0, 17), [(2, 2), (2, 3), (2, 4)], [(2, 9), (2, 10)], [(2, 6), (2, 7), (2, 8)], [(0, 16), (0, 17)]⟩

theorem g060_ok : tagOKF CompactData.T CompactData.F g060 = true := by decide +kernel

def g061 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (6 / 25 : ℚ), (13 / 50 : ℚ), (39 / 800 : ℚ), (1 / 4 : ℚ), (2, 3), (2, 10), (2, 7), (0, 18), [(2, 2), (2, 3), (2, 4)], [(2, 9), (2, 10), (2, 11)], [(2, 6), (2, 7), (2, 8)], [(0, 17), (0, 18)]⟩

theorem g061_ok : tagOKF CompactData.T CompactData.F g061 = true := by decide +kernel

def g062 : Tag := .inr ⟨(9 / 200 : ℚ), (1 / 20 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (19 / 400 : ℚ), (27 / 100 : ℚ), (2, 5), (2, 11), (2, 8), (0, 17), [(2, 4), (2, 5), (2, 6)], [(2, 10), (2, 11), (2, 12)], [(2, 7), (2, 8), (2, 9)], [(0, 16), (0, 17), (0, 18)]⟩

theorem g062_ok : tagOKF CompactData.T CompactData.F g062 = true := by decide +kernel

def g063 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (7 / 25 : ℚ), (3 / 10 : ℚ), (33 / 800 : ℚ), (29 / 100 : ℚ), (2, 6), (2, 11), (2, 9), (0, 14), [(2, 6), (2, 7)], [(2, 11), (2, 12)], [(2, 8), (2, 9), (2, 10)], [(0, 14), (0, 15)]⟩

theorem g063_ok : tagOKF CompactData.T CompactData.F g063 = true := by decide +kernel

def g064 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (7 / 25 : ℚ), (3 / 10 : ℚ), (7 / 160 : ℚ), (29 / 100 : ℚ), (2, 6), (2, 12), (2, 9), (0, 16), [(2, 6), (2, 7)], [(2, 11), (2, 12)], [(2, 8), (2, 9), (2, 10)], [(0, 15), (0, 16)]⟩

theorem g064_ok : tagOKF CompactData.T CompactData.F g064 = true := by decide +kernel

def g065 : Tag := .inr ⟨(1 / 25 : ℚ), (9 / 200 : ℚ), (3 / 10 : ℚ), (8 / 25 : ℚ), (17 / 400 : ℚ), (31 / 100 : ℚ), (2, 8), (2, 13), (2, 10), (0, 15), [(2, 7), (2, 8)], [(2, 12), (2, 13)], [(2, 10), (2, 11)], [(0, 14), (0, 15), (0, 16)]⟩

theorem g065_ok : tagOKF CompactData.T CompactData.F g065 = true := by decide +kernel

def g066 : Tag := .inr ⟨(9 / 200 : ℚ), (1 / 20 : ℚ), (7 / 25 : ℚ), (3 / 10 : ℚ), (19 / 400 : ℚ), (29 / 100 : ℚ), (2, 6), (2, 12), (2, 9), (0, 17), [(2, 6), (2, 7)], [(2, 11), (2, 12), (2, 13)], [(2, 9), (2, 10)], [(0, 16), (0, 17), (0, 18)]⟩

theorem g066_ok : tagOKF CompactData.T CompactData.F g066 = true := by decide +kernel

def g067 : Tag := .inr ⟨(9 / 200 : ℚ), (1 / 20 : ℚ), (3 / 10 : ℚ), (8 / 25 : ℚ), (19 / 400 : ℚ), (31 / 100 : ℚ), (2, 8), (2, 13), (2, 11), (0, 17), [(2, 7), (2, 8)], [(2, 12), (2, 13), (2, 14)], [(2, 10), (2, 11)], [(0, 16), (0, 17), (0, 18)]⟩

theorem g067_ok : tagOKF CompactData.T CompactData.F g067 = true := by decide +kernel

def g068 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (6 / 25 : ℚ), (13 / 50 : ℚ), (21 / 400 : ℚ), (1 / 4 : ℚ), (2, 3), (2, 10), (2, 7), (0, 19), [(2, 2), (2, 3), (2, 4)], [(2, 10), (2, 11)], [(2, 6), (2, 7), (2, 8)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g068_ok : tagOKF CompactData.T CompactData.F g068 = true := by decide +kernel

def g069 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (21 / 400 : ℚ), (27 / 100 : ℚ), (2, 5), (2, 12), (2, 8), (0, 19), [(2, 4), (2, 5), (2, 6)], [(2, 11), (2, 12)], [(2, 8), (2, 9)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g069_ok : tagOKF CompactData.T CompactData.F g069 = true := by decide +kernel

def g070 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (6 / 25 : ℚ), (13 / 50 : ℚ), (23 / 400 : ℚ), (1 / 4 : ℚ), (2, 3), (2, 11), (2, 8), (0, 21), [(2, 2), (2, 3), (2, 4)], [(2, 10), (2, 11), (2, 12)], [(2, 7), (2, 8)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g070_ok : tagOKF CompactData.T CompactData.F g070 = true := by decide +kernel

def g071 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (23 / 400 : ℚ), (27 / 100 : ℚ), (2, 5), (2, 12), (2, 9), (0, 21), [(2, 4), (2, 5), (2, 6)], [(2, 11), (2, 12), (2, 13)], [(2, 8), (2, 9), (2, 10)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g071_ok : tagOKF CompactData.T CompactData.F g071 = true := by decide +kernel

def g072 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (7 / 25 : ℚ), (3 / 10 : ℚ), (21 / 400 : ℚ), (29 / 100 : ℚ), (2, 6), (2, 13), (2, 10), (0, 19), [(2, 6), (2, 7)], [(2, 12), (2, 13)], [(2, 9), (2, 10)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g072_ok : tagOKF CompactData.T CompactData.F g072 = true := by decide +kernel

def g073 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (3 / 10 : ℚ), (8 / 25 : ℚ), (21 / 400 : ℚ), (31 / 100 : ℚ), (2, 8), (2, 14), (2, 11), (0, 19), [(2, 7), (2, 8)], [(2, 13), (2, 14)], [(2, 10), (2, 11), (2, 12)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g073_ok : tagOKF CompactData.T CompactData.F g073 = true := by decide +kernel

def g074 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (7 / 25 : ℚ), (3 / 10 : ℚ), (23 / 400 : ℚ), (29 / 100 : ℚ), (2, 6), (2, 13), (2, 10), (0, 21), [(2, 6), (2, 7)], [(2, 12), (2, 13), (2, 14)], [(2, 9), (2, 10), (2, 11)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g074_ok : tagOKF CompactData.T CompactData.F g074 = true := by decide +kernel

def g075 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (3 / 10 : ℚ), (8 / 25 : ℚ), (23 / 400 : ℚ), (31 / 100 : ℚ), (2, 8), (2, 14), (2, 11), (0, 21), [(2, 7), (2, 8)], [(2, 13), (2, 14), (2, 15)], [(2, 10), (2, 11), (2, 12)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g075_ok : tagOKF CompactData.T CompactData.F g075 = true := by decide +kernel

def g076 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (4 / 25 : ℚ), (17 / 100 : ℚ), (1 / 16 : ℚ), (33 / 200 : ℚ), (1, 19), (2, 6), (2, 1), (0, 23), [(1, 18), (1, 19)], [(2, 6), (2, 7)], [(2, 1), (2, 2)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g076_ok : tagOKF CompactData.T CompactData.F g076 = true := by decide +kernel

def g077 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (17 / 100 : ℚ), (9 / 50 : ℚ), (1 / 16 : ℚ), (7 / 40 : ℚ), (1, 20), (2, 7), (2, 2), (0, 23), [(1, 19), (1, 20), (1, 21)], [(2, 6), (2, 7), (2, 8)], [(2, 2), (2, 3)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g077_ok : tagOKF CompactData.T CompactData.F g077 = true := by decide +kernel

def g078 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (4 / 25 : ℚ), (17 / 100 : ℚ), (27 / 400 : ℚ), (33 / 200 : ℚ), (1, 19), (2, 7), (2, 2), (1, 0), [(1, 18), (1, 19)], [(2, 6), (2, 7), (2, 8)], [(2, 1), (2, 2)], [(1, 0), (1, 1)]⟩

theorem g078_ok : tagOKF CompactData.T CompactData.F g078 = true := by decide +kernel

def g079 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (17 / 100 : ℚ), (9 / 50 : ℚ), (27 / 400 : ℚ), (7 / 40 : ℚ), (1, 20), (2, 8), (2, 3), (1, 0), [(1, 19), (1, 20), (1, 21)], [(2, 7), (2, 8)], [(2, 2), (2, 3)], [(1, 0), (1, 1)]⟩

theorem g079_ok : tagOKF CompactData.T CompactData.F g079 = true := by decide +kernel

def g080 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (9 / 50 : ℚ), (19 / 100 : ℚ), (1 / 16 : ℚ), (37 / 200 : ℚ), (1, 21), (2, 8), (2, 3), (0, 23), [(1, 21), (1, 22)], [(2, 7), (2, 8)], [(2, 2), (2, 3), (2, 4)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g080_ok : tagOKF CompactData.T CompactData.F g080 = true := by decide +kernel

def g081 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (19 / 100 : ℚ), (1 / 5 : ℚ), (1 / 16 : ℚ), (39 / 200 : ℚ), (1, 22), (2, 8), (2, 4), (0, 23), [(1, 22), (1, 23)], [(2, 8), (2, 9)], [(2, 3), (2, 4)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g081_ok : tagOKF CompactData.T CompactData.F g081 = true := by decide +kernel

def g082 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (9 / 50 : ℚ), (19 / 100 : ℚ), (27 / 400 : ℚ), (37 / 200 : ℚ), (1, 21), (2, 8), (2, 3), (1, 0), [(1, 21), (1, 22)], [(2, 8), (2, 9)], [(2, 3), (2, 4)], [(1, 0), (1, 1)]⟩

theorem g082_ok : tagOKF CompactData.T CompactData.F g082 = true := by decide +kernel

def g083 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (19 / 100 : ℚ), (1 / 5 : ℚ), (27 / 400 : ℚ), (39 / 200 : ℚ), (1, 22), (2, 9), (2, 4), (1, 0), [(1, 22), (1, 23)], [(2, 8), (2, 9), (2, 10)], [(2, 4), (2, 5)], [(1, 0), (1, 1)]⟩

theorem g083_ok : tagOKF CompactData.T CompactData.F g083 = true := by decide +kernel

def g084 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (4 / 25 : ℚ), (17 / 100 : ℚ), (29 / 400 : ℚ), (33 / 200 : ℚ), (1, 19), (2, 8), (2, 2), (1, 2), [(1, 18), (1, 19)], [(2, 7), (2, 8)], [(2, 2), (2, 3)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g084_ok : tagOKF CompactData.T CompactData.F g084 = true := by decide +kernel

def g085 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (17 / 100 : ℚ), (9 / 50 : ℚ), (29 / 400 : ℚ), (7 / 40 : ℚ), (1, 20), (2, 8), (2, 3), (1, 2), [(1, 19), (1, 20), (1, 21)], [(2, 8), (2, 9)], [(2, 2), (2, 3), (2, 4)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g085_ok : tagOKF CompactData.T CompactData.F g085 = true := by decide +kernel

def g086 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (4 / 25 : ℚ), (17 / 100 : ℚ), (31 / 400 : ℚ), (33 / 200 : ℚ), (1, 19), (2, 8), (2, 3), (1, 3), [(1, 18), (1, 19)], [(2, 8), (2, 9)], [(2, 2), (2, 3)], [(1, 3), (1, 4)]⟩

theorem g086_ok : tagOKF CompactData.T CompactData.F g086 = true := by decide +kernel

def g087 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (17 / 100 : ℚ), (9 / 50 : ℚ), (31 / 400 : ℚ), (7 / 40 : ℚ), (1, 20), (2, 9), (2, 3), (1, 3), [(1, 19), (1, 20), (1, 21)], [(2, 8), (2, 9), (2, 10)], [(2, 3), (2, 4)], [(1, 3), (1, 4)]⟩

theorem g087_ok : tagOKF CompactData.T CompactData.F g087 = true := by decide +kernel

def g088 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (9 / 50 : ℚ), (1 / 5 : ℚ), (29 / 400 : ℚ), (19 / 100 : ℚ), (1, 22), (2, 9), (2, 4), (1, 2), [(1, 21), (1, 22), (1, 23)], [(2, 8), (2, 9), (2, 10)], [(2, 3), (2, 4), (2, 5)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g088_ok : tagOKF CompactData.T CompactData.F g088 = true := by decide +kernel

def g089 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (9 / 50 : ℚ), (1 / 5 : ℚ), (31 / 400 : ℚ), (19 / 100 : ℚ), (1, 22), (2, 10), (2, 5), (1, 3), [(1, 21), (1, 22), (1, 23)], [(2, 9), (2, 10), (2, 11)], [(2, 4), (2, 5), (2, 6)], [(1, 3), (1, 4)]⟩

theorem g089_ok : tagOKF CompactData.T CompactData.F g089 = true := by decide +kernel

def g090 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (1 / 5 : ℚ), (21 / 100 : ℚ), (1 / 16 : ℚ), (41 / 200 : ℚ), (1, 23), (2, 9), (2, 5), (0, 23), [(1, 23), (2, 0)], [(2, 8), (2, 9), (2, 10)], [(2, 4), (2, 5)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g090_ok : tagOKF CompactData.T CompactData.F g090 = true := by decide +kernel

def g091 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (21 / 100 : ℚ), (11 / 50 : ℚ), (1 / 16 : ℚ), (43 / 200 : ℚ), (2, 0), (2, 10), (2, 5), (0, 23), [(2, 0), (2, 1)], [(2, 9), (2, 10)], [(2, 5), (2, 6)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g091_ok : tagOKF CompactData.T CompactData.F g091 = true := by decide +kernel

def g092 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (1 / 5 : ℚ), (11 / 50 : ℚ), (27 / 400 : ℚ), (21 / 100 : ℚ), (2, 0), (2, 10), (2, 5), (1, 0), [(1, 23), (2, 0), (2, 1)], [(2, 9), (2, 10), (2, 11)], [(2, 4), (2, 5), (2, 6)], [(1, 0), (1, 1)]⟩

theorem g092_ok : tagOKF CompactData.T CompactData.F g092 = true := by decide +kernel

def g093 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (11 / 50 : ℚ), (6 / 25 : ℚ), (1 / 16 : ℚ), (23 / 100 : ℚ), (2, 2), (2, 10), (2, 6), (0, 23), [(2, 1), (2, 2)], [(2, 10), (2, 11)], [(2, 6), (2, 7)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g093_ok : tagOKF CompactData.T CompactData.F g093 = true := by decide +kernel

def g094 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (11 / 50 : ℚ), (6 / 25 : ℚ), (27 / 400 : ℚ), (23 / 100 : ℚ), (2, 2), (2, 11), (2, 7), (1, 0), [(2, 1), (2, 2)], [(2, 10), (2, 11), (2, 12)], [(2, 6), (2, 7), (2, 8)], [(1, 0), (1, 1)]⟩

theorem g094_ok : tagOKF CompactData.T CompactData.F g094 = true := by decide +kernel

def g095 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (1 / 5 : ℚ), (11 / 50 : ℚ), (29 / 400 : ℚ), (21 / 100 : ℚ), (2, 0), (2, 10), (2, 6), (1, 2), [(1, 23), (2, 0), (2, 1)], [(2, 10), (2, 11)], [(2, 5), (2, 6), (2, 7)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g095_ok : tagOKF CompactData.T CompactData.F g095 = true := by decide +kernel

def g096 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (1 / 5 : ℚ), (11 / 50 : ℚ), (31 / 400 : ℚ), (21 / 100 : ℚ), (2, 0), (2, 11), (2, 6), (1, 3), [(1, 23), (2, 0), (2, 1)], [(2, 10), (2, 11), (2, 12)], [(2, 5), (2, 6), (2, 7)], [(1, 3), (1, 4)]⟩

theorem g096_ok : tagOKF CompactData.T CompactData.F g096 = true := by decide +kernel

def g097 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (11 / 50 : ℚ), (6 / 25 : ℚ), (29 / 400 : ℚ), (23 / 100 : ℚ), (2, 2), (2, 12), (2, 7), (1, 2), [(2, 1), (2, 2)], [(2, 11), (2, 12)], [(2, 6), (2, 7), (2, 8)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g097_ok : tagOKF CompactData.T CompactData.F g097 = true := by decide +kernel

def g098 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (11 / 50 : ℚ), (6 / 25 : ℚ), (31 / 400 : ℚ), (23 / 100 : ℚ), (2, 2), (2, 12), (2, 8), (1, 3), [(2, 1), (2, 2)], [(2, 11), (2, 12), (2, 13)], [(2, 7), (2, 8)], [(1, 3), (1, 4)]⟩

theorem g098_ok : tagOKF CompactData.T CompactData.F g098 = true := by decide +kernel

def g099 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (6 / 25 : ℚ), (13 / 50 : ℚ), (1 / 16 : ℚ), (1 / 4 : ℚ), (2, 3), (2, 12), (2, 8), (0, 23), [(2, 2), (2, 3), (2, 4)], [(2, 11), (2, 12)], [(2, 7), (2, 8), (2, 9)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g099_ok : tagOKF CompactData.T CompactData.F g099 = true := by decide +kernel

def g100 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (1 / 16 : ℚ), (27 / 100 : ℚ), (2, 5), (2, 13), (2, 9), (0, 23), [(2, 4), (2, 5), (2, 6)], [(2, 12), (2, 13)], [(2, 8), (2, 9), (2, 10)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g100_ok : tagOKF CompactData.T CompactData.F g100 = true := by decide +kernel

def g101 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (6 / 25 : ℚ), (13 / 50 : ℚ), (27 / 400 : ℚ), (1 / 4 : ℚ), (2, 3), (2, 12), (2, 8), (1, 0), [(2, 2), (2, 3), (2, 4)], [(2, 11), (2, 12), (2, 13)], [(2, 7), (2, 8), (2, 9)], [(1, 0), (1, 1)]⟩

theorem g101_ok : tagOKF CompactData.T CompactData.F g101 = true := by decide +kernel

def g102 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (27 / 400 : ℚ), (27 / 100 : ℚ), (2, 5), (2, 13), (2, 9), (1, 0), [(2, 4), (2, 5), (2, 6)], [(2, 12), (2, 13), (2, 14)], [(2, 9), (2, 10)], [(1, 0), (1, 1)]⟩

theorem g102_ok : tagOKF CompactData.T CompactData.F g102 = true := by decide +kernel

def g103 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (7 / 25 : ℚ), (3 / 10 : ℚ), (1 / 16 : ℚ), (29 / 100 : ℚ), (2, 6), (2, 14), (2, 10), (0, 23), [(2, 6), (2, 7)], [(2, 13), (2, 14)], [(2, 10), (2, 11)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g103_ok : tagOKF CompactData.T CompactData.F g103 = true := by decide +kernel

def g104 : Tag := .inr ⟨(3 / 50 : ℚ), (13 / 200 : ℚ), (3 / 10 : ℚ), (8 / 25 : ℚ), (1 / 16 : ℚ), (31 / 100 : ℚ), (2, 8), (2, 15), (2, 11), (0, 23), [(2, 7), (2, 8)], [(2, 14), (2, 15)], [(2, 11), (2, 12)], [(0, 22), (0, 23), (1, 0)]⟩

theorem g104_ok : tagOKF CompactData.T CompactData.F g104 = true := by decide +kernel

def g105 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (7 / 25 : ℚ), (3 / 10 : ℚ), (27 / 400 : ℚ), (29 / 100 : ℚ), (2, 6), (2, 14), (2, 11), (1, 0), [(2, 6), (2, 7)], [(2, 13), (2, 14), (2, 15)], [(2, 10), (2, 11)], [(1, 0), (1, 1)]⟩

theorem g105_ok : tagOKF CompactData.T CompactData.F g105 = true := by decide +kernel

def g106 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (3 / 10 : ℚ), (8 / 25 : ℚ), (27 / 400 : ℚ), (31 / 100 : ℚ), (2, 8), (2, 15), (2, 12), (1, 0), [(2, 7), (2, 8)], [(2, 14), (2, 15), (2, 16)], [(2, 11), (2, 12)], [(1, 0), (1, 1)]⟩

theorem g106_ok : tagOKF CompactData.T CompactData.F g106 = true := by decide +kernel

def g107 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (6 / 25 : ℚ), (13 / 50 : ℚ), (29 / 400 : ℚ), (1 / 4 : ℚ), (2, 3), (2, 13), (2, 8), (1, 2), [(2, 2), (2, 3), (2, 4)], [(2, 12), (2, 13)], [(2, 8), (2, 9)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g107_ok : tagOKF CompactData.T CompactData.F g107 = true := by decide +kernel

def g108 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (6 / 25 : ℚ), (13 / 50 : ℚ), (31 / 400 : ℚ), (1 / 4 : ℚ), (2, 3), (2, 13), (2, 9), (1, 3), [(2, 2), (2, 3), (2, 4)], [(2, 12), (2, 13), (2, 14)], [(2, 8), (2, 9), (2, 10)], [(1, 3), (1, 4)]⟩

theorem g108_ok : tagOKF CompactData.T CompactData.F g108 = true := by decide +kernel

def g109 : Tag := .inr ⟨(7 / 100 : ℚ), (2 / 25 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (3 / 40 : ℚ), (27 / 100 : ℚ), (2, 5), (2, 14), (2, 10), (1, 3), [(2, 4), (2, 5), (2, 6)], [(2, 13), (2, 14), (2, 15)], [(2, 9), (2, 10), (2, 11)], [(1, 1), (1, 2), (1, 3), (1, 4)]⟩

theorem g109_ok : tagOKF CompactData.T CompactData.F g109 = true := by decide +kernel

def g110 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (7 / 25 : ℚ), (3 / 10 : ℚ), (29 / 400 : ℚ), (29 / 100 : ℚ), (2, 6), (2, 15), (2, 11), (1, 2), [(2, 6), (2, 7)], [(2, 14), (2, 15)], [(2, 10), (2, 11), (2, 12)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g110_ok : tagOKF CompactData.T CompactData.F g110 = true := by decide +kernel

def g111 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (3 / 10 : ℚ), (8 / 25 : ℚ), (29 / 400 : ℚ), (31 / 100 : ℚ), (2, 8), (2, 16), (2, 12), (1, 2), [(2, 7), (2, 8)], [(2, 15), (2, 16)], [(2, 11), (2, 12), (2, 13)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g111_ok : tagOKF CompactData.T CompactData.F g111 = true := by decide +kernel

def g112 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (7 / 25 : ℚ), (3 / 10 : ℚ), (31 / 400 : ℚ), (29 / 100 : ℚ), (2, 6), (2, 15), (2, 11), (1, 3), [(2, 6), (2, 7)], [(2, 14), (2, 15), (2, 16)], [(2, 10), (2, 11), (2, 12)], [(1, 3), (1, 4)]⟩

theorem g112_ok : tagOKF CompactData.T CompactData.F g112 = true := by decide +kernel

def g113 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (3 / 10 : ℚ), (8 / 25 : ℚ), (31 / 400 : ℚ), (31 / 100 : ℚ), (2, 8), (2, 16), (2, 12), (1, 3), [(2, 7), (2, 8)], [(2, 15), (2, 16), (2, 17)], [(2, 12), (2, 13)], [(1, 3), (1, 4)]⟩

theorem g113_ok : tagOKF CompactData.T CompactData.F g113 = true := by decide +kernel

def g114 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (8 / 25 : ℚ), (17 / 50 : ℚ), (33 / 800 : ℚ), (33 / 100 : ℚ), (2, 9), (2, 14), (2, 11), (0, 14), [(2, 8), (2, 9), (2, 10)], [(2, 13), (2, 14)], [(2, 11), (2, 12)], [(0, 14), (0, 15)]⟩

theorem g114_ok : tagOKF CompactData.T CompactData.F g114 = true := by decide +kernel

def g115 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (17 / 50 : ℚ), (9 / 25 : ℚ), (33 / 800 : ℚ), (7 / 20 : ℚ), (2, 10), (2, 15), (2, 12), (0, 14), [(2, 10), (2, 11)], [(2, 14), (2, 15)], [(2, 12), (2, 13)], [(0, 14), (0, 15)]⟩

theorem g115_ok : tagOKF CompactData.T CompactData.F g115 = true := by decide +kernel

def g116 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (8 / 25 : ℚ), (17 / 50 : ℚ), (7 / 160 : ℚ), (33 / 100 : ℚ), (2, 9), (2, 14), (2, 12), (0, 16), [(2, 8), (2, 9), (2, 10)], [(2, 13), (2, 14)], [(2, 11), (2, 12)], [(0, 15), (0, 16)]⟩

theorem g116_ok : tagOKF CompactData.T CompactData.F g116 = true := by decide +kernel

def g117 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (17 / 50 : ℚ), (9 / 25 : ℚ), (7 / 160 : ℚ), (7 / 20 : ℚ), (2, 10), (2, 15), (2, 13), (0, 16), [(2, 10), (2, 11)], [(2, 14), (2, 15)], [(2, 12), (2, 13)], [(0, 15), (0, 16)]⟩

theorem g117_ok : tagOKF CompactData.T CompactData.F g117 = true := by decide +kernel

def g118 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (9 / 25 : ℚ), (19 / 50 : ℚ), (33 / 800 : ℚ), (37 / 100 : ℚ), (2, 11), (2, 16), (2, 13), (0, 14), [(2, 11), (2, 12)], [(2, 15), (2, 16)], [(2, 13), (2, 14)], [(0, 14), (0, 15)]⟩

theorem g118_ok : tagOKF CompactData.T CompactData.F g118 = true := by decide +kernel

def g119 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (19 / 50 : ℚ), (2 / 5 : ℚ), (33 / 800 : ℚ), (39 / 100 : ℚ), (2, 12), (2, 17), (2, 14), (0, 14), [(2, 12), (2, 13)], [(2, 16), (2, 17)], [(2, 14), (2, 15)], [(0, 14), (0, 15)]⟩

theorem g119_ok : tagOKF CompactData.T CompactData.F g119 = true := by decide +kernel

def tags : List Tag := [g000, g001, g002, g003, g004, g005, g006, g007, g008, g009, g010, g011, g012, g013, g014, g015, g016, g017, g018, g019, g020, g021, g022, g023, g024, g025, g026, g027, g028, g029, g030, g031, g032, g033, g034, g035, g036, g037, g038, g039, g040, g041, g042, g043, g044, g045, g046, g047, g048, g049, g050, g051, g052, g053, g054, g055, g056, g057, g058, g059, g060, g061, g062, g063, g064, g065, g066, g067, g068, g069, g070, g071, g072, g073, g074, g075, g076, g077, g078, g079, g080, g081, g082, g083, g084, g085, g086, g087, g088, g089, g090, g091, g092, g093, g094, g095, g096, g097, g098, g099, g100, g101, g102, g103, g104, g105, g106, g107, g108, g109, g110, g111, g112, g113, g114, g115, g116, g117, g118, g119]

theorem tags_ok : tags.all (tagOKF CompactData.T CompactData.F) = true := by
  simp only [tags, List.all_cons, List.all_nil, g000_ok, g001_ok, g002_ok, g003_ok, g004_ok, g005_ok, g006_ok, g007_ok, g008_ok, g009_ok, g010_ok, g011_ok, g012_ok, g013_ok, g014_ok, g015_ok, g016_ok, g017_ok, g018_ok, g019_ok, g020_ok, g021_ok, g022_ok, g023_ok, g024_ok, g025_ok, g026_ok, g027_ok, g028_ok, g029_ok, g030_ok, g031_ok, g032_ok, g033_ok, g034_ok, g035_ok, g036_ok, g037_ok, g038_ok, g039_ok, g040_ok, g041_ok, g042_ok, g043_ok, g044_ok, g045_ok, g046_ok, g047_ok, g048_ok, g049_ok, g050_ok, g051_ok, g052_ok, g053_ok, g054_ok, g055_ok, g056_ok, g057_ok, g058_ok, g059_ok, g060_ok, g061_ok, g062_ok, g063_ok, g064_ok, g065_ok, g066_ok, g067_ok, g068_ok, g069_ok, g070_ok, g071_ok, g072_ok, g073_ok, g074_ok, g075_ok, g076_ok, g077_ok, g078_ok, g079_ok, g080_ok, g081_ok, g082_ok, g083_ok, g084_ok, g085_ok, g086_ok, g087_ok, g088_ok, g089_ok, g090_ok, g091_ok, g092_ok, g093_ok, g094_ok, g095_ok, g096_ok, g097_ok, g098_ok, g099_ok, g100_ok, g101_ok, g102_ok, g103_ok, g104_ok, g105_ok, g106_ok, g107_ok, g108_ok, g109_ok, g110_ok, g111_ok, g112_ok, g113_ok, g114_ok, g115_ok, g116_ok, g117_ok, g118_ok, g119_ok, Bool.and_self]

end CKLaneC3.CompactBatch21

end


