-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch41_part00
-- name    : CK_CKLaneC3_CompactBatch41_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T01:37:30.349091+00:00
-- url     : https://prove2.me/theorems/95a9c30b-751b-4dbc-957a-c00e6deff569
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch41 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch41 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch41 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch41 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch41 (part 1 of 3).lean)

import Definitions.Def_CK_CKLaneC3_CompactData
import Definitions.Def_CK_CKLaneC3_CompactCoverF

/-! Lane C3 compact cell batch (generated; memoised chains over the data tables). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactBatch41
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF

def g000 : Tag := .inr ⟨(6 / 25 : ℚ), (13 / 50 : ℚ), (9 / 100 : ℚ), (1 / 10 : ℚ), (1 / 4 : ℚ), (19 / 200 : ℚ), (1, 7), (2, 23), (2, 10), (2, 3), [(1, 6), (1, 7), (1, 8)], [(2, 21), (2, 22), (2, 23), (3, 0)], [(2, 9), (2, 10), (2, 11)], [(2, 2), (2, 3), (2, 4)]⟩

theorem g000_ok : tagOKF CompactData.T CompactData.F g000 = true := by decide +kernel

def g001 : Tag := .inr ⟨(13 / 50 : ℚ), (7 / 25 : ℚ), (9 / 100 : ℚ), (1 / 10 : ℚ), (27 / 100 : ℚ), (19 / 200 : ℚ), (1, 7), (3, 1), (2, 11), (2, 5), [(1, 6), (1, 7), (1, 8)], [(2, 23), (3, 0), (3, 1), (3, 2)], [(2, 10), (2, 11), (2, 12)], [(2, 4), (2, 5), (2, 6)]⟩

theorem g001_ok : tagOKF CompactData.T CompactData.F g001 = true := by decide +kernel

def g002 : Tag := .inr ⟨(7 / 25 : ℚ), (3 / 10 : ℚ), (2 / 25 : ℚ), (9 / 100 : ℚ), (29 / 100 : ℚ), (17 / 200 : ℚ), (1, 5), (3, 2), (2, 12), (2, 6), [(1, 4), (1, 5), (1, 6)], [(3, 1), (3, 2), (3, 3)], [(2, 11), (2, 12)], [(2, 6), (2, 7)]⟩

theorem g002_ok : tagOKF CompactData.T CompactData.F g002 = true := by decide +kernel

def g003 : Tag := .inr ⟨(3 / 10 : ℚ), (8 / 25 : ℚ), (2 / 25 : ℚ), (9 / 100 : ℚ), (31 / 100 : ℚ), (17 / 200 : ℚ), (1, 5), (3, 4), (2, 13), (2, 8), [(1, 4), (1, 5), (1, 6)], [(3, 3), (3, 4), (3, 5)], [(2, 12), (2, 13)], [(2, 7), (2, 8)]⟩

theorem g003_ok : tagOKF CompactData.T CompactData.F g003 = true := by decide +kernel

def g004 : Tag := .inr ⟨(7 / 25 : ℚ), (3 / 10 : ℚ), (9 / 100 : ℚ), (1 / 10 : ℚ), (29 / 100 : ℚ), (19 / 200 : ℚ), (1, 7), (3, 3), (2, 12), (2, 6), [(1, 6), (1, 7), (1, 8)], [(3, 1), (3, 2), (3, 3), (3, 4)], [(2, 11), (2, 12), (2, 13)], [(2, 6), (2, 7)]⟩

theorem g004_ok : tagOKF CompactData.T CompactData.F g004 = true := by decide +kernel

def g005 : Tag := .inr ⟨(3 / 10 : ℚ), (8 / 25 : ℚ), (9 / 100 : ℚ), (1 / 10 : ℚ), (31 / 100 : ℚ), (19 / 200 : ℚ), (1, 7), (3, 5), (2, 13), (2, 8), [(1, 6), (1, 7), (1, 8)], [(3, 3), (3, 4), (3, 5), (3, 6)], [(2, 12), (2, 13), (2, 14)], [(2, 7), (2, 8)]⟩

theorem g005_ok : tagOKF CompactData.T CompactData.F g005 = true := by decide +kernel

def g006 : Tag := .inr ⟨(6 / 25 : ℚ), (13 / 50 : ℚ), (1 / 10 : ℚ), (11 / 100 : ℚ), (1 / 4 : ℚ), (21 / 200 : ℚ), (1, 9), (2, 23), (2, 10), (2, 3), [(1, 8), (1, 9), (1, 10)], [(2, 22), (2, 23), (3, 0)], [(2, 10), (2, 11)], [(2, 2), (2, 3), (2, 4)]⟩

theorem g006_ok : tagOKF CompactData.T CompactData.F g006 = true := by decide +kernel

def g007 : Tag := .inr ⟨(13 / 50 : ℚ), (7 / 25 : ℚ), (1 / 10 : ℚ), (11 / 100 : ℚ), (27 / 100 : ℚ), (21 / 200 : ℚ), (1, 9), (3, 1), (2, 12), (2, 5), [(1, 8), (1, 9), (1, 10)], [(3, 0), (3, 1), (3, 2)], [(2, 11), (2, 12)], [(2, 4), (2, 5), (2, 6)]⟩

theorem g007_ok : tagOKF CompactData.T CompactData.F g007 = true := by decide +kernel

def g008 : Tag := .inr ⟨(6 / 25 : ℚ), (13 / 50 : ℚ), (11 / 100 : ℚ), (3 / 25 : ℚ), (1 / 4 : ℚ), (23 / 200 : ℚ), (1, 11), (3, 0), (2, 11), (2, 3), [(1, 10), (1, 11), (1, 12)], [(2, 22), (2, 23), (3, 0), (3, 1)], [(2, 10), (2, 11), (2, 12)], [(2, 2), (2, 3), (2, 4)]⟩

theorem g008_ok : tagOKF CompactData.T CompactData.F g008 = true := by decide +kernel

def g009 : Tag := .inr ⟨(13 / 50 : ℚ), (7 / 25 : ℚ), (11 / 100 : ℚ), (3 / 25 : ℚ), (27 / 100 : ℚ), (23 / 200 : ℚ), (1, 11), (3, 2), (2, 12), (2, 5), [(1, 10), (1, 11), (1, 12)], [(3, 0), (3, 1), (3, 2), (3, 3)], [(2, 11), (2, 12), (2, 13)], [(2, 4), (2, 5), (2, 6)]⟩

theorem g009_ok : tagOKF CompactData.T CompactData.F g009 = true := by decide +kernel

def g010 : Tag := .inr ⟨(7 / 25 : ℚ), (3 / 10 : ℚ), (1 / 10 : ℚ), (11 / 100 : ℚ), (29 / 100 : ℚ), (21 / 200 : ℚ), (1, 9), (3, 3), (2, 13), (2, 6), [(1, 8), (1, 9), (1, 10)], [(3, 2), (3, 3), (3, 4)], [(2, 12), (2, 13)], [(2, 6), (2, 7)]⟩

theorem g010_ok : tagOKF CompactData.T CompactData.F g010 = true := by decide +kernel

def g011 : Tag := .inr ⟨(3 / 10 : ℚ), (8 / 25 : ℚ), (1 / 10 : ℚ), (11 / 100 : ℚ), (31 / 100 : ℚ), (21 / 200 : ℚ), (1, 9), (3, 5), (2, 14), (2, 8), [(1, 8), (1, 9), (1, 10)], [(3, 4), (3, 5), (3, 6)], [(2, 13), (2, 14)], [(2, 7), (2, 8)]⟩

theorem g011_ok : tagOKF CompactData.T CompactData.F g011 = true := by decide +kernel

def g012 : Tag := .inr ⟨(7 / 25 : ℚ), (8 / 25 : ℚ), (11 / 100 : ℚ), (3 / 25 : ℚ), (3 / 10 : ℚ), (23 / 200 : ℚ), (1, 11), (3, 5), (2, 14), (2, 7), [(1, 10), (1, 11), (1, 12)], [(3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7)], [(2, 12), (2, 13), (2, 14), (2, 15)], [(2, 6), (2, 7), (2, 8)]⟩

theorem g012_ok : tagOKF CompactData.T CompactData.F g012 = true := by decide +kernel

def g013 : Tag := .inr ⟨(6 / 25 : ℚ), (13 / 50 : ℚ), (3 / 25 : ℚ), (7 / 50 : ℚ), (1 / 4 : ℚ), (13 / 100 : ℚ), (1, 14), (3, 0), (2, 12), (2, 3), [(1, 12), (1, 13), (1, 14), (1, 15)], [(2, 23), (3, 0), (3, 1), (3, 2)], [(2, 11), (2, 12), (2, 13)], [(2, 2), (2, 3), (2, 4)]⟩

theorem g013_ok : tagOKF CompactData.T CompactData.F g013 = true := by decide +kernel

def g014 : Tag := .inr ⟨(13 / 50 : ℚ), (7 / 25 : ℚ), (3 / 25 : ℚ), (7 / 50 : ℚ), (27 / 100 : ℚ), (13 / 100 : ℚ), (1, 14), (3, 2), (2, 13), (2, 5), [(1, 12), (1, 13), (1, 14), (1, 15)], [(3, 1), (3, 2), (3, 3), (3, 4)], [(2, 12), (2, 13), (2, 14)], [(2, 4), (2, 5), (2, 6)]⟩

theorem g014_ok : tagOKF CompactData.T CompactData.F g014 = true := by decide +kernel

def g015 : Tag := .inr ⟨(6 / 25 : ℚ), (13 / 50 : ℚ), (7 / 50 : ℚ), (4 / 25 : ℚ), (1 / 4 : ℚ), (3 / 20 : ℚ), (1, 17), (3, 1), (2, 13), (2, 3), [(1, 15), (1, 16), (1, 17), (1, 18)], [(3, 0), (3, 1), (3, 2), (3, 3)], [(2, 12), (2, 13), (2, 14)], [(2, 2), (2, 3), (2, 4)]⟩

theorem g015_ok : tagOKF CompactData.T CompactData.F g015 = true := by decide +kernel

def g016 : Tag := .inr ⟨(13 / 50 : ℚ), (7 / 25 : ℚ), (7 / 50 : ℚ), (4 / 25 : ℚ), (27 / 100 : ℚ), (3 / 20 : ℚ), (1, 17), (3, 3), (2, 14), (2, 5), [(1, 15), (1, 16), (1, 17), (1, 18)], [(3, 2), (3, 3), (3, 4), (3, 5)], [(2, 13), (2, 14), (2, 15)], [(2, 4), (2, 5), (2, 6)]⟩

theorem g016_ok : tagOKF CompactData.T CompactData.F g016 = true := by decide +kernel

def g017 : Tag := .inr ⟨(7 / 25 : ℚ), (8 / 25 : ℚ), (3 / 25 : ℚ), (13 / 100 : ℚ), (3 / 10 : ℚ), (1 / 8 : ℚ), (1, 13), (3, 5), (2, 14), (2, 7), [(1, 12), (1, 13), (1, 14)], [(3, 3), (3, 4), (3, 5), (3, 6), (3, 7)], [(2, 13), (2, 14), (2, 15)], [(2, 6), (2, 7), (2, 8)]⟩

theorem g017_ok : tagOKF CompactData.T CompactData.F g017 = true := by decide +kernel

def g018 : Tag := .inr ⟨(7 / 25 : ℚ), (8 / 25 : ℚ), (13 / 100 : ℚ), (7 / 50 : ℚ), (3 / 10 : ℚ), (27 / 200 : ℚ), (1, 15), (3, 6), (2, 15), (2, 7), [(1, 14), (1, 15)], [(3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8)], [(2, 13), (2, 14), (2, 15), (2, 16)], [(2, 6), (2, 7), (2, 8)]⟩

theorem g018_ok : tagOKF CompactData.T CompactData.F g018 = true := by decide +kernel

def g019 : Tag := .inr ⟨(7 / 25 : ℚ), (3 / 10 : ℚ), (7 / 50 : ℚ), (4 / 25 : ℚ), (29 / 100 : ℚ), (3 / 20 : ℚ), (1, 17), (3, 5), (2, 15), (2, 6), [(1, 15), (1, 16), (1, 17), (1, 18)], [(3, 4), (3, 5), (3, 6), (3, 7)], [(2, 14), (2, 15), (2, 16)], [(2, 6), (2, 7)]⟩

theorem g019_ok : tagOKF CompactData.T CompactData.F g019 = true := by decide +kernel

def g020 : Tag := .inr ⟨(3 / 10 : ℚ), (8 / 25 : ℚ), (7 / 50 : ℚ), (4 / 25 : ℚ), (31 / 100 : ℚ), (3 / 20 : ℚ), (1, 17), (3, 7), (2, 16), (2, 8), [(1, 15), (1, 16), (1, 17), (1, 18)], [(3, 6), (3, 7), (3, 8), (3, 9)], [(2, 15), (2, 16), (2, 17)], [(2, 7), (2, 8)]⟩

theorem g020_ok : tagOKF CompactData.T CompactData.F g020 = true := by decide +kernel

def g021 : Tag := .inr ⟨(4 / 25 : ℚ), (9 / 50 : ℚ), (4 / 25 : ℚ), (9 / 50 : ℚ), (17 / 100 : ℚ), (17 / 100 : ℚ), (1, 19), (2, 18), (2, 10), (1, 19), [(1, 18), (1, 19), (1, 20), (1, 21)], [(2, 17), (2, 18), (2, 19), (2, 20)], [(2, 8), (2, 9), (2, 10), (2, 11)], [(1, 18), (1, 19), (1, 20), (1, 21)]⟩

theorem g021_ok : tagOKF CompactData.T CompactData.F g021 = true := by decide +kernel

def g022 : Tag := .inr ⟨(4 / 25 : ℚ), (9 / 50 : ℚ), (9 / 50 : ℚ), (1 / 5 : ℚ), (17 / 100 : ℚ), (19 / 100 : ℚ), (1, 22), (2, 19), (2, 11), (1, 19), [(1, 21), (1, 22), (1, 23)], [(2, 18), (2, 19), (2, 20), (2, 21)], [(2, 10), (2, 11), (2, 12)], [(1, 18), (1, 19), (1, 20), (1, 21)]⟩

theorem g022_ok : tagOKF CompactData.T CompactData.F g022 = true := by decide +kernel

def g023 : Tag := .inr ⟨(9 / 50 : ℚ), (1 / 5 : ℚ), (4 / 25 : ℚ), (9 / 50 : ℚ), (19 / 100 : ℚ), (17 / 100 : ℚ), (1, 19), (2, 20), (2, 11), (1, 22), [(1, 18), (1, 19), (1, 20), (1, 21)], [(2, 19), (2, 20), (2, 21), (2, 22)], [(2, 10), (2, 11), (2, 12)], [(1, 21), (1, 22), (1, 23)]⟩

theorem g023_ok : tagOKF CompactData.T CompactData.F g023 = true := by decide +kernel

def g024 : Tag := .inr ⟨(9 / 50 : ℚ), (1 / 5 : ℚ), (9 / 50 : ℚ), (1 / 5 : ℚ), (19 / 100 : ℚ), (19 / 100 : ℚ), (1, 22), (2, 21), (2, 12), (1, 22), [(1, 21), (1, 22), (1, 23)], [(2, 20), (2, 21), (2, 22), (2, 23)], [(2, 11), (2, 12), (2, 13)], [(1, 21), (1, 22), (1, 23)]⟩

theorem g024_ok : tagOKF CompactData.T CompactData.F g024 = true := by decide +kernel

def g025 : Tag := .inr ⟨(4 / 25 : ℚ), (9 / 50 : ℚ), (1 / 5 : ℚ), (11 / 50 : ℚ), (17 / 100 : ℚ), (21 / 100 : ℚ), (2, 0), (2, 20), (2, 12), (1, 19), [(1, 23), (2, 0), (2, 1)], [(2, 19), (2, 20), (2, 21), (2, 22)], [(2, 11), (2, 12), (2, 13)], [(1, 18), (1, 19), (1, 20), (1, 21)]⟩

theorem g025_ok : tagOKF CompactData.T CompactData.F g025 = true := by decide +kernel

def g026 : Tag := .inr ⟨(4 / 25 : ℚ), (9 / 50 : ℚ), (11 / 50 : ℚ), (6 / 25 : ℚ), (17 / 100 : ℚ), (23 / 100 : ℚ), (2, 2), (2, 21), (2, 13), (1, 19), [(2, 1), (2, 2)], [(2, 20), (2, 21), (2, 22), (2, 23)], [(2, 12), (2, 13), (2, 14)], [(1, 18), (1, 19), (1, 20), (1, 21)]⟩

theorem g026_ok : tagOKF CompactData.T CompactData.F g026 = true := by decide +kernel

def g027 : Tag := .inr ⟨(9 / 50 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), (11 / 50 : ℚ), (19 / 100 : ℚ), (21 / 100 : ℚ), (2, 0), (2, 22), (2, 13), (1, 22), [(1, 23), (2, 0), (2, 1)], [(2, 21), (2, 22), (2, 23), (3, 0)], [(2, 12), (2, 13), (2, 14)], [(1, 21), (1, 22), (1, 23)]⟩

theorem g027_ok : tagOKF CompactData.T CompactData.F g027 = true := by decide +kernel

def g028 : Tag := .inr ⟨(9 / 50 : ℚ), (1 / 5 : ℚ), (11 / 50 : ℚ), (6 / 25 : ℚ), (19 / 100 : ℚ), (23 / 100 : ℚ), (2, 2), (2, 23), (2, 14), (1, 22), [(2, 1), (2, 2)], [(2, 22), (2, 23), (3, 0), (3, 1)], [(2, 13), (2, 14), (2, 15)], [(1, 21), (1, 22), (1, 23)]⟩

theorem g028_ok : tagOKF CompactData.T CompactData.F g028 = true := by decide +kernel

def g029 : Tag := .inr ⟨(1 / 5 : ℚ), (11 / 50 : ℚ), (4 / 25 : ℚ), (9 / 50 : ℚ), (21 / 100 : ℚ), (17 / 100 : ℚ), (1, 19), (2, 22), (2, 12), (2, 0), [(1, 18), (1, 19), (1, 20), (1, 21)], [(2, 21), (2, 22), (2, 23), (3, 0)], [(2, 11), (2, 12), (2, 13)], [(1, 23), (2, 0), (2, 1)]⟩

theorem g029_ok : tagOKF CompactData.T CompactData.F g029 = true := by decide +kernel

def g030 : Tag := .inr ⟨(11 / 50 : ℚ), (6 / 25 : ℚ), (4 / 25 : ℚ), (9 / 50 : ℚ), (23 / 100 : ℚ), (17 / 100 : ℚ), (1, 19), (3, 0), (2, 13), (2, 2), [(1, 18), (1, 19), (1, 20), (1, 21)], [(2, 23), (3, 0), (3, 1), (3, 2)], [(2, 12), (2, 13), (2, 14)], [(2, 1), (2, 2)]⟩

theorem g030_ok : tagOKF CompactData.T CompactData.F g030 = true := by decide +kernel

def g031 : Tag := .inr ⟨(1 / 5 : ℚ), (11 / 50 : ℚ), (9 / 50 : ℚ), (1 / 5 : ℚ), (21 / 100 : ℚ), (19 / 100 : ℚ), (1, 22), (2, 23), (2, 13), (2, 0), [(1, 21), (1, 22), (1, 23)], [(2, 22), (2, 23), (3, 0), (3, 1)], [(2, 12), (2, 13), (2, 14)], [(1, 23), (2, 0), (2, 1)]⟩

theorem g031_ok : tagOKF CompactData.T CompactData.F g031 = true := by decide +kernel

def g032 : Tag := .inr ⟨(11 / 50 : ℚ), (6 / 25 : ℚ), (9 / 50 : ℚ), (1 / 5 : ℚ), (23 / 100 : ℚ), (19 / 100 : ℚ), (1, 22), (3, 1), (2, 14), (2, 2), [(1, 21), (1, 22), (1, 23)], [(3, 0), (3, 1), (3, 2), (3, 3)], [(2, 13), (2, 14), (2, 15)], [(2, 1), (2, 2)]⟩

theorem g032_ok : tagOKF CompactData.T CompactData.F g032 = true := by decide +kernel

def g033 : Tag := .inr ⟨(1 / 5 : ℚ), (11 / 50 : ℚ), (1 / 5 : ℚ), (11 / 50 : ℚ), (21 / 100 : ℚ), (21 / 100 : ℚ), (2, 0), (3, 0), (2, 14), (2, 0), [(1, 23), (2, 0), (2, 1)], [(2, 23), (3, 0), (3, 1), (3, 2)], [(2, 13), (2, 14), (2, 15)], [(1, 23), (2, 0), (2, 1)]⟩

theorem g033_ok : tagOKF CompactData.T CompactData.F g033 = true := by decide +kernel

def g034 : Tag := .inr ⟨(1 / 5 : ℚ), (11 / 50 : ℚ), (11 / 50 : ℚ), (6 / 25 : ℚ), (21 / 100 : ℚ), (23 / 100 : ℚ), (2, 2), (3, 1), (2, 15), (2, 0), [(2, 1), (2, 2)], [(3, 0), (3, 1), (3, 2), (3, 3)], [(2, 14), (2, 15), (2, 16)], [(1, 23), (2, 0), (2, 1)]⟩

theorem g034_ok : tagOKF CompactData.T CompactData.F g034 = true := by decide +kernel

def g035 : Tag := .inr ⟨(11 / 50 : ℚ), (6 / 25 : ℚ), (1 / 5 : ℚ), (6 / 25 : ℚ), (23 / 100 : ℚ), (11 / 50 : ℚ), (2, 1), (3, 3), (2, 15), (2, 2), [(1, 23), (2, 0), (2, 1), (2, 2)], [(3, 1), (3, 2), (3, 3), (3, 4), (3, 5)], [(2, 14), (2, 15), (2, 16), (2, 17)], [(2, 1), (2, 2)]⟩

theorem g035_ok : tagOKF CompactData.T CompactData.F g035 = true := by decide +kernel

def g036 : Tag := .inr ⟨(4 / 25 : ℚ), (9 / 50 : ℚ), (6 / 25 : ℚ), (13 / 50 : ℚ), (17 / 100 : ℚ), (1 / 4 : ℚ), (2, 3), (2, 22), (2, 14), (1, 19), [(2, 2), (2, 3), (2, 4)], [(2, 21), (2, 22), (2, 23), (3, 0)], [(2, 13), (2, 14), (2, 15)], [(1, 18), (1, 19), (1, 20), (1, 21)]⟩

theorem g036_ok : tagOKF CompactData.T CompactData.F g036 = true := by decide +kernel

def g037 : Tag := .inr ⟨(4 / 25 : ℚ), (9 / 50 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (17 / 100 : ℚ), (27 / 100 : ℚ), (2, 5), (2, 23), (2, 15), (1, 19), [(2, 4), (2, 5), (2, 6)], [(2, 22), (2, 23), (3, 0), (3, 1)], [(2, 14), (2, 15), (2, 16)], [(1, 18), (1, 19), (1, 20), (1, 21)]⟩

theorem g037_ok : tagOKF CompactData.T CompactData.F g037 = true := by decide +kernel

def g038 : Tag := .inr ⟨(9 / 50 : ℚ), (1 / 5 : ℚ), (6 / 25 : ℚ), (13 / 50 : ℚ), (19 / 100 : ℚ), (1 / 4 : ℚ), (2, 3), (3, 0), (2, 15), (1, 22), [(2, 2), (2, 3), (2, 4)], [(2, 23), (3, 0), (3, 1), (3, 2)], [(2, 14), (2, 15), (2, 16)], [(1, 21), (1, 22), (1, 23)]⟩

theorem g038_ok : tagOKF CompactData.T CompactData.F g038 = true := by decide +kernel

def g039 : Tag := .inr ⟨(9 / 50 : ℚ), (1 / 5 : ℚ), (13 / 50 : ℚ), (7 / 25 : ℚ), (19 / 100 : ℚ), (27 / 100 : ℚ), (2, 5), (3, 1), (2, 16), (1, 22), [(2, 4), (2, 5), (2, 6)], [(3, 0), (3, 1), (3, 2), (3, 3)], [(2, 15), (2, 16), (2, 17)], [(1, 21), (1, 22), (1, 23)]⟩

theorem g039_ok : tagOKF CompactData.T CompactData.F g039 = true := by decide +kernel

def g040 : Tag := .inr ⟨(4 / 25 : ℚ), (9 / 50 : ℚ), (7 / 25 : ℚ), (3 / 10 : ℚ), (17 / 100 : ℚ), (29 / 100 : ℚ), (2, 6), (3, 0), (2, 16), (1, 19), [(2, 6), (2, 7)], [(2, 23), (3, 0), (3, 1), (3, 2)], [(2, 15), (2, 16), (2, 17)], [(1, 18), (1, 19), (1, 20), (1, 21)]⟩

theorem g040_ok : tagOKF CompactData.T CompactData.F g040 = true := by decide +kernel

def g041 : Tag := .inr ⟨(4 / 25 : ℚ), (9 / 50 : ℚ), (3 / 10 : ℚ), (8 / 25 : ℚ), (17 / 100 : ℚ), (31 / 100 : ℚ), (2, 8), (3, 1), (2, 17), (1, 19), [(2, 7), (2, 8)], [(3, 0), (3, 1), (3, 2), (3, 3)], [(2, 16), (2, 17), (2, 18)], [(1, 18), (1, 19), (1, 20), (1, 21)]⟩

theorem g041_ok : tagOKF CompactData.T CompactData.F g041 = true := by decide +kernel

def g042 : Tag := .inr ⟨(9 / 50 : ℚ), (1 / 5 : ℚ), (7 / 25 : ℚ), (8 / 25 : ℚ), (19 / 100 : ℚ), (3 / 10 : ℚ), (2, 7), (3, 3), (2, 17), (1, 22), [(2, 6), (2, 7), (2, 8)], [(3, 1), (3, 2), (3, 3), (3, 4), (3, 5)], [(2, 16), (2, 17), (2, 18), (2, 19)], [(1, 21), (1, 22), (1, 23)]⟩

theorem g042_ok : tagOKF CompactData.T CompactData.F g042 = true := by decide +kernel

def g043 : Tag := .inr ⟨(1 / 5 : ℚ), (11 / 50 : ℚ), (6 / 25 : ℚ), (7 / 25 : ℚ), (21 / 100 : ℚ), (13 / 50 : ℚ), (2, 4), (3, 3), (2, 16), (2, 0), [(2, 2), (2, 3), (2, 4), (2, 5), (2, 6)], [(3, 1), (3, 2), (3, 3), (3, 4), (3, 5)], [(2, 15), (2, 16), (2, 17), (2, 18)], [(1, 23), (2, 0), (2, 1)]⟩

theorem g043_ok : tagOKF CompactData.T CompactData.F g043 = true := by decide +kernel

def g044 : Tag := .inr ⟨(11 / 50 : ℚ), (6 / 25 : ℚ), (6 / 25 : ℚ), (7 / 25 : ℚ), (23 / 100 : ℚ), (13 / 50 : ℚ), (2, 4), (3, 5), (2, 17), (2, 2), [(2, 2), (2, 3), (2, 4), (2, 5), (2, 6)], [(3, 3), (3, 4), (3, 5), (3, 6), (3, 7)], [(2, 16), (2, 17), (2, 18), (2, 19)], [(2, 1), (2, 2)]⟩

theorem g044_ok : tagOKF CompactData.T CompactData.F g044 = true := by decide +kernel

def g045 : Tag := .inr ⟨(1 / 5 : ℚ), (11 / 50 : ℚ), (7 / 25 : ℚ), (8 / 25 : ℚ), (21 / 100 : ℚ), (3 / 10 : ℚ), (2, 7), (3, 5), (2, 18), (2, 0), [(2, 6), (2, 7), (2, 8)], [(3, 3), (3, 4), (3, 5), (3, 6), (3, 7)], [(2, 17), (2, 18), (2, 19), (2, 20)], [(1, 23), (2, 0), (2, 1)]⟩

theorem g045_ok : tagOKF CompactData.T CompactData.F g045 = true := by decide +kernel

def g046 : Tag := .inr ⟨(11 / 50 : ℚ), (6 / 25 : ℚ), (7 / 25 : ℚ), (8 / 25 : ℚ), (23 / 100 : ℚ), (3 / 10 : ℚ), (2, 7), (3, 7), (2, 19), (2, 2), [(2, 6), (2, 7), (2, 8)], [(3, 5), (3, 6), (3, 7), (3, 8), (3, 9)], [(2, 18), (2, 19), (2, 20), (2, 21)], [(2, 1), (2, 2)]⟩

theorem g046_ok : tagOKF CompactData.T CompactData.F g046 = true := by decide +kernel

def g047 : Tag := .inr ⟨(6 / 25 : ℚ), (13 / 50 : ℚ), (4 / 25 : ℚ), (9 / 50 : ℚ), (1 / 4 : ℚ), (17 / 100 : ℚ), (1, 19), (3, 2), (2, 14), (2, 3), [(1, 18), (1, 19), (1, 20), (1, 21)], [(3, 1), (3, 2), (3, 3), (3, 4)], [(2, 13), (2, 14), (2, 15)], [(2, 2), (2, 3), (2, 4)]⟩

theorem g047_ok : tagOKF CompactData.T CompactData.F g047 = true := by decide +kernel

def g048 : Tag := .inr ⟨(13 / 50 : ℚ), (7 / 25 : ℚ), (4 / 25 : ℚ), (9 / 50 : ℚ), (27 / 100 : ℚ), (17 / 100 : ℚ), (1, 19), (3, 4), (2, 15), (2, 5), [(1, 18), (1, 19), (1, 20), (1, 21)], [(3, 3), (3, 4), (3, 5), (3, 6)], [(2, 14), (2, 15), (2, 16)], [(2, 4), (2, 5), (2, 6)]⟩

theorem g048_ok : tagOKF CompactData.T CompactData.F g048 = true := by decide +kernel

def g049 : Tag := .inr ⟨(6 / 25 : ℚ), (13 / 50 : ℚ), (9 / 50 : ℚ), (1 / 5 : ℚ), (1 / 4 : ℚ), (19 / 100 : ℚ), (1, 22), (3, 3), (2, 15), (2, 3), [(1, 21), (1, 22), (1, 23)], [(3, 2), (3, 3), (3, 4), (3, 5)], [(2, 14), (2, 15), (2, 16)], [(2, 2), (2, 3), (2, 4)]⟩

theorem g049_ok : tagOKF CompactData.T CompactData.F g049 = true := by decide +kernel

def g050 : Tag := .inr ⟨(13 / 50 : ℚ), (7 / 25 : ℚ), (9 / 50 : ℚ), (1 / 5 : ℚ), (27 / 100 : ℚ), (19 / 100 : ℚ), (1, 22), (3, 5), (2, 16), (2, 5), [(1, 21), (1, 22), (1, 23)], [(3, 4), (3, 5), (3, 6), (3, 7)], [(2, 15), (2, 16), (2, 17)], [(2, 4), (2, 5), (2, 6)]⟩

theorem g050_ok : tagOKF CompactData.T CompactData.F g050 = true := by decide +kernel

def g051 : Tag := .inr ⟨(7 / 25 : ℚ), (8 / 25 : ℚ), (4 / 25 : ℚ), (9 / 50 : ℚ), (3 / 10 : ℚ), (17 / 100 : ℚ), (1, 19), (3, 7), (2, 16), (2, 7), [(1, 18), (1, 19), (1, 20), (1, 21)], [(3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10)], [(2, 15), (2, 16), (2, 17), (2, 18)], [(2, 6), (2, 7), (2, 8)]⟩

theorem g051_ok : tagOKF CompactData.T CompactData.F g051 = true := by decide +kernel

def g052 : Tag := .inr ⟨(7 / 25 : ℚ), (8 / 25 : ℚ), (9 / 50 : ℚ), (1 / 5 : ℚ), (3 / 10 : ℚ), (19 / 100 : ℚ), (1, 22), (3, 8), (2, 17), (2, 7), [(1, 21), (1, 22), (1, 23)], [(3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11)], [(2, 16), (2, 17), (2, 18), (2, 19)], [(2, 6), (2, 7), (2, 8)]⟩

theorem g052_ok : tagOKF CompactData.T CompactData.F g052 = true := by decide +kernel

def g053 : Tag := .inr ⟨(6 / 25 : ℚ), (7 / 25 : ℚ), (1 / 5 : ℚ), (11 / 50 : ℚ), (13 / 50 : ℚ), (21 / 100 : ℚ), (2, 0), (3, 5), (2, 16), (2, 4), [(1, 23), (2, 0), (2, 1)], [(3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8)], [(2, 15), (2, 16), (2, 17), (2, 18)], [(2, 2), (2, 3), (2, 4), (2, 5), (2, 6)]⟩

theorem g053_ok : tagOKF CompactData.T CompactData.F g053 = true := by decide +kernel

def g054 : Tag := .inr ⟨(6 / 25 : ℚ), (7 / 25 : ℚ), (11 / 50 : ℚ), (6 / 25 : ℚ), (13 / 50 : ℚ), (23 / 100 : ℚ), (2, 2), (3, 6), (2, 17), (2, 4), [(2, 1), (2, 2)], [(3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9)], [(2, 16), (2, 17), (2, 18), (2, 19)], [(2, 2), (2, 3), (2, 4), (2, 5), (2, 6)]⟩

theorem g054_ok : tagOKF CompactData.T CompactData.F g054 = true := by decide +kernel

def g055 : Tag := .inr ⟨(7 / 25 : ℚ), (8 / 25 : ℚ), (1 / 5 : ℚ), (11 / 50 : ℚ), (3 / 10 : ℚ), (21 / 100 : ℚ), (2, 0), (3, 9), (2, 18), (2, 7), [(1, 23), (2, 0), (2, 1)], [(3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12)], [(2, 17), (2, 18), (2, 19), (2, 20)], [(2, 6), (2, 7), (2, 8)]⟩

theorem g055_ok : tagOKF CompactData.T CompactData.F g055 = true := by decide +kernel

def g056 : Tag := .inr ⟨(7 / 25 : ℚ), (8 / 25 : ℚ), (11 / 50 : ℚ), (6 / 25 : ℚ), (3 / 10 : ℚ), (23 / 100 : ℚ), (2, 2), (3, 10), (2, 19), (2, 7), [(2, 1), (2, 2)], [(3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13)], [(2, 18), (2, 19), (2, 20), (2, 21)], [(2, 6), (2, 7), (2, 8)]⟩

theorem g056_ok : tagOKF CompactData.T CompactData.F g056 = true := by decide +kernel

def g057 : Tag := .inr ⟨(6 / 25 : ℚ), (13 / 50 : ℚ), (6 / 25 : ℚ), (7 / 25 : ℚ), (1 / 4 : ℚ), (13 / 50 : ℚ), (2, 4), (3, 7), (2, 18), (2, 3), [(2, 2), (2, 3), (2, 4), (2, 5), (2, 6)], [(3, 5), (3, 6), (3, 7), (3, 8), (3, 9)], [(2, 17), (2, 18), (2, 19), (2, 20)], [(2, 2), (2, 3), (2, 4)]⟩

theorem g057_ok : tagOKF CompactData.T CompactData.F g057 = true := by decide +kernel

def g058 : Tag := .inr ⟨(13 / 50 : ℚ), (7 / 25 : ℚ), (6 / 25 : ℚ), (7 / 25 : ℚ), (27 / 100 : ℚ), (13 / 50 : ℚ), (2, 4), (3, 9), (2, 19), (2, 5), [(2, 2), (2, 3), (2, 4), (2, 5), (2, 6)], [(3, 7), (3, 8), (3, 9), (3, 10), (3, 11)], [(2, 18), (2, 19), (2, 20), (2, 21)], [(2, 4), (2, 5), (2, 6)]⟩

theorem g058_ok : tagOKF CompactData.T CompactData.F g058 = true := by decide +kernel


end CKLaneC3.CompactBatch41


