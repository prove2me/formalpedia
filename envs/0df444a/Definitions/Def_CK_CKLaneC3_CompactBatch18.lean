-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch18
-- name    : CK_CKLaneC3_CompactBatch18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T02:25:45.706731+00:00
-- url     : https://prove2.me/theorems/0dff4031-0c27-4333-a42b-9c7528b0bc8d
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch18` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch18` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch18` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch18 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch18.lean)

import Definitions.Def_CK_CKLaneC3_CompactData
import Definitions.Def_CK_CKLaneC3_CompactCoverF

-- ===== source module CKLaneC3.CompactBatch18 =====
section

/-! Lane C3 compact cell batch (generated; memoised chains over the data tables). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactBatch18
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF

def g000 : Tag := .inr ⟨(29 / 800 : ℚ), (3 / 80 : ℚ), (2357 / 200 : ℚ), (12 : ℚ), (59 / 1600 : ℚ), (4757 / 400 : ℚ), (26, 12), (26, 15), (26, 13), (0, 12), [(26, 6), (26, 7), (26, 8), (26, 9), (26, 10), (26, 11), (26, 12), (26, 13), (26, 14), (26, 15), (26, 16), (26, 17)], [(26, 10), (26, 11), (26, 12), (26, 13), (26, 14), (26, 15), (26, 16), (26, 17), (26, 18), (26, 19), (26, 20), (26, 21)], [(26, 8), (26, 9), (26, 10), (26, 11), (26, 12), (26, 13), (26, 14), (26, 15), (26, 16), (26, 17), (26, 18), (26, 19)], [(0, 12)]⟩

theorem g000_ok : tagOKF CompactData.T CompactData.F g000 = true := by decide +kernel

def g001 : Tag := .inr ⟨(3 / 80 : ℚ), (31 / 800 : ℚ), (557 / 50 : ℚ), (2271 / 200 : ℚ), (61 / 1600 : ℚ), (4499 / 400 : ℚ), (25, 3), (25, 7), (25, 5), (0, 13), [(24, 22), (24, 23), (25, 0), (25, 1), (25, 2), (25, 3), (25, 4), (25, 5), (25, 6), (25, 7), (25, 8), (25, 9)], [(25, 2), (25, 3), (25, 4), (25, 5), (25, 6), (25, 7), (25, 8), (25, 9), (25, 10), (25, 11), (25, 12), (25, 13)], [(25, 0), (25, 1), (25, 2), (25, 3), (25, 4), (25, 5), (25, 6), (25, 7), (25, 8), (25, 9), (25, 10), (25, 11)], [(0, 12), (0, 13)]⟩

theorem g001_ok : tagOKF CompactData.T CompactData.F g001 = true := by decide +kernel

def g002 : Tag := .inr ⟨(3 / 80 : ℚ), (31 / 800 : ℚ), (2271 / 200 : ℚ), (1157 / 100 : ℚ), (61 / 1600 : ℚ), (917 / 80 : ℚ), (25, 14), (25, 18), (25, 16), (0, 13), [(25, 9), (25, 10), (25, 11), (25, 12), (25, 13), (25, 14), (25, 15), (25, 16), (25, 17), (25, 18), (25, 19)], [(25, 12), (25, 13), (25, 14), (25, 15), (25, 16), (25, 17), (25, 18), (25, 19), (25, 20), (25, 21), (25, 22), (25, 23)], [(25, 11), (25, 12), (25, 13), (25, 14), (25, 15), (25, 16), (25, 17), (25, 18), (25, 19), (25, 20), (25, 21)], [(0, 12), (0, 13)]⟩

theorem g002_ok : tagOKF CompactData.T CompactData.F g002 = true := by decide +kernel

def g003 : Tag := .inr ⟨(31 / 800 : ℚ), (1 / 25 : ℚ), (557 / 50 : ℚ), (2271 / 200 : ℚ), (63 / 1600 : ℚ), (4499 / 400 : ℚ), (25, 3), (25, 7), (25, 5), (0, 13), [(24, 22), (24, 23), (25, 0), (25, 1), (25, 2), (25, 3), (25, 4), (25, 5), (25, 6), (25, 7), (25, 8), (25, 9)], [(25, 2), (25, 3), (25, 4), (25, 5), (25, 6), (25, 7), (25, 8), (25, 9), (25, 10), (25, 11), (25, 12), (25, 13)], [(25, 0), (25, 1), (25, 2), (25, 3), (25, 4), (25, 5), (25, 6), (25, 7), (25, 8), (25, 9), (25, 10), (25, 11)], [(0, 13), (0, 14)]⟩

theorem g003_ok : tagOKF CompactData.T CompactData.F g003 = true := by decide +kernel

def g004 : Tag := .inr ⟨(31 / 800 : ℚ), (1 / 25 : ℚ), (2271 / 200 : ℚ), (1157 / 100 : ℚ), (63 / 1600 : ℚ), (917 / 80 : ℚ), (25, 14), (25, 18), (25, 16), (0, 13), [(25, 9), (25, 10), (25, 11), (25, 12), (25, 13), (25, 14), (25, 15), (25, 16), (25, 17), (25, 18), (25, 19)], [(25, 13), (25, 14), (25, 15), (25, 16), (25, 17), (25, 18), (25, 19), (25, 20), (25, 21), (25, 22), (25, 23)], [(25, 11), (25, 12), (25, 13), (25, 14), (25, 15), (25, 16), (25, 17), (25, 18), (25, 19), (25, 20), (25, 21)], [(0, 13), (0, 14)]⟩

theorem g004_ok : tagOKF CompactData.T CompactData.F g004 = true := by decide +kernel

def g005 : Tag := .inr ⟨(3 / 80 : ℚ), (31 / 800 : ℚ), (1157 / 100 : ℚ), (2357 / 200 : ℚ), (61 / 1600 : ℚ), (4671 / 400 : ℚ), (26, 1), (26, 5), (26, 3), (0, 13), [(25, 19), (25, 20), (25, 21), (25, 22), (25, 23), (26, 0), (26, 1), (26, 2), (26, 3), (26, 4), (26, 5), (26, 6)], [(25, 23), (26, 0), (26, 1), (26, 2), (26, 3), (26, 4), (26, 5), (26, 6), (26, 7), (26, 8), (26, 9), (26, 10)], [(25, 21), (25, 22), (25, 23), (26, 0), (26, 1), (26, 2), (26, 3), (26, 4), (26, 5), (26, 6), (26, 7), (26, 8)], [(0, 12), (0, 13)]⟩

theorem g005_ok : tagOKF CompactData.T CompactData.F g005 = true := by decide +kernel

def g006 : Tag := .inr ⟨(3 / 80 : ℚ), (31 / 800 : ℚ), (2357 / 200 : ℚ), (12 : ℚ), (61 / 1600 : ℚ), (4757 / 400 : ℚ), (26, 12), (26, 15), (26, 13), (0, 13), [(26, 6), (26, 7), (26, 8), (26, 9), (26, 10), (26, 11), (26, 12), (26, 13), (26, 14), (26, 15), (26, 16), (26, 17)], [(26, 10), (26, 11), (26, 12), (26, 13), (26, 14), (26, 15), (26, 16), (26, 17), (26, 18), (26, 19), (26, 20), (26, 21)], [(26, 8), (26, 9), (26, 10), (26, 11), (26, 12), (26, 13), (26, 14), (26, 15), (26, 16), (26, 17), (26, 18), (26, 19)], [(0, 12), (0, 13)]⟩

theorem g006_ok : tagOKF CompactData.T CompactData.F g006 = true := by decide +kernel

def g007 : Tag := .inr ⟨(31 / 800 : ℚ), (1 / 25 : ℚ), (1157 / 100 : ℚ), (2357 / 200 : ℚ), (63 / 1600 : ℚ), (4671 / 400 : ℚ), (26, 1), (26, 5), (26, 3), (0, 13), [(25, 19), (25, 20), (25, 21), (25, 22), (25, 23), (26, 0), (26, 1), (26, 2), (26, 3), (26, 4), (26, 5), (26, 6)], [(25, 23), (26, 0), (26, 1), (26, 2), (26, 3), (26, 4), (26, 5), (26, 6), (26, 7), (26, 8), (26, 9), (26, 10)], [(25, 21), (25, 22), (25, 23), (26, 0), (26, 1), (26, 2), (26, 3), (26, 4), (26, 5), (26, 6), (26, 7), (26, 8)], [(0, 13), (0, 14)]⟩

theorem g007_ok : tagOKF CompactData.T CompactData.F g007 = true := by decide +kernel

def g008 : Tag := .inr ⟨(31 / 800 : ℚ), (1 / 25 : ℚ), (2357 / 200 : ℚ), (12 : ℚ), (63 / 1600 : ℚ), (4757 / 400 : ℚ), (26, 12), (26, 15), (26, 13), (0, 13), [(26, 6), (26, 7), (26, 8), (26, 9), (26, 10), (26, 11), (26, 12), (26, 13), (26, 14), (26, 15), (26, 16), (26, 17)], [(26, 10), (26, 11), (26, 12), (26, 13), (26, 14), (26, 15), (26, 16), (26, 17), (26, 18), (26, 19), (26, 20), (26, 21)], [(26, 8), (26, 9), (26, 10), (26, 11), (26, 12), (26, 13), (26, 14), (26, 15), (26, 16), (26, 17), (26, 18), (26, 19)], [(0, 13), (0, 14)]⟩

theorem g008_ok : tagOKF CompactData.T CompactData.F g008 = true := by decide +kernel

def g009 : Tag := .inl ⟨(1 / 25 : ℚ), (1 / 20 : ℚ), (1 / 50 : ℚ), (3 / 100 : ℚ)⟩

theorem g009_ok : tagOKF CompactData.T CompactData.F g009 = true := by decide +kernel

def g010 : Tag := .inl ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (1 / 50 : ℚ), (9 / 400 : ℚ)⟩

theorem g010_ok : tagOKF CompactData.T CompactData.F g010 = true := by decide +kernel

def g011 : Tag := .inl ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (1 / 50 : ℚ), (17 / 800 : ℚ)⟩

theorem g011_ok : tagOKF CompactData.T CompactData.F g011 = true := by decide +kernel

def g012 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (1 / 50 : ℚ), (17 / 800 : ℚ), (47 / 800 : ℚ), (33 / 1600 : ℚ), (0, 0), (1, 15), (1, 4), (0, 22), [(0, 0), (0, 1)], [(1, 15), (1, 16)], [(1, 3), (1, 4)], [(0, 21), (0, 22)]⟩

theorem g012_ok : tagOKF CompactData.T CompactData.F g012 = true := by decide +kernel

def g013 : Tag := .inl ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (17 / 800 : ℚ), (9 / 400 : ℚ)⟩

theorem g013_ok : tagOKF CompactData.T CompactData.F g013 = true := by decide +kernel

def g014 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (17 / 800 : ℚ), (9 / 400 : ℚ), (47 / 800 : ℚ), (7 / 320 : ℚ), (0, 1), (1, 15), (1, 4), (0, 22), [(0, 1), (0, 2)], [(1, 15), (1, 16)], [(1, 4), (1, 5)], [(0, 21), (0, 22)]⟩

theorem g014_ok : tagOKF CompactData.T CompactData.F g014 = true := by decide +kernel

def g015 : Tag := .inl ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (9 / 400 : ℚ), (1 / 40 : ℚ)⟩

theorem g015_ok : tagOKF CompactData.T CompactData.F g015 = true := by decide +kernel

def g016 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (9 / 400 : ℚ), (19 / 800 : ℚ), (9 / 160 : ℚ), (37 / 1600 : ℚ), (0, 2), (1, 15), (1, 4), (0, 21), [(0, 2), (0, 3)], [(1, 14), (1, 15)], [(1, 3), (1, 4)], [(0, 20), (0, 21)]⟩

theorem g016_ok : tagOKF CompactData.T CompactData.F g016 = true := by decide +kernel

def g017 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (9 / 400 : ℚ), (19 / 800 : ℚ), (47 / 800 : ℚ), (37 / 1600 : ℚ), (0, 2), (1, 15), (1, 4), (0, 22), [(0, 2), (0, 3)], [(1, 15), (1, 16)], [(1, 4), (1, 5)], [(0, 21), (0, 22)]⟩

theorem g017_ok : tagOKF CompactData.T CompactData.F g017 = true := by decide +kernel

def g018 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (19 / 800 : ℚ), (1 / 40 : ℚ), (9 / 160 : ℚ), (39 / 1600 : ℚ), (0, 4), (1, 15), (1, 4), (0, 21), [(0, 3), (0, 4)], [(1, 14), (1, 15)], [(1, 4), (1, 5)], [(0, 20), (0, 21)]⟩

theorem g018_ok : tagOKF CompactData.T CompactData.F g018 = true := by decide +kernel

def g019 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (19 / 800 : ℚ), (1 / 40 : ℚ), (47 / 800 : ℚ), (39 / 1600 : ℚ), (0, 4), (1, 16), (1, 5), (0, 22), [(0, 3), (0, 4)], [(1, 15), (1, 16)], [(1, 4), (1, 5)], [(0, 21), (0, 22)]⟩

theorem g019_ok : tagOKF CompactData.T CompactData.F g019 = true := by decide +kernel

def g020 : Tag := .inl ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (1 / 40 : ℚ), (11 / 400 : ℚ)⟩

theorem g020_ok : tagOKF CompactData.T CompactData.F g020 = true := by decide +kernel

def g021 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (1 / 40 : ℚ), (11 / 400 : ℚ), (43 / 800 : ℚ), (21 / 800 : ℚ), (0, 5), (1, 14), (1, 4), (0, 20), [(0, 4), (0, 5), (0, 6)], [(1, 14), (1, 15)], [(1, 3), (1, 4), (1, 5)], [(0, 19), (0, 20)]⟩

theorem g021_ok : tagOKF CompactData.T CompactData.F g021 = true := by decide +kernel

def g022 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (11 / 400 : ℚ), (3 / 100 : ℚ), (41 / 800 : ℚ), (23 / 800 : ℚ), (0, 7), (1, 14), (1, 4), (0, 19), [(0, 6), (0, 7), (0, 8)], [(1, 13), (1, 14), (1, 15)], [(1, 3), (1, 4), (1, 5)], [(0, 18), (0, 19)]⟩

theorem g022_ok : tagOKF CompactData.T CompactData.F g022 = true := by decide +kernel

def g023 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (11 / 400 : ℚ), (3 / 100 : ℚ), (43 / 800 : ℚ), (23 / 800 : ℚ), (0, 7), (1, 15), (1, 5), (0, 20), [(0, 6), (0, 7), (0, 8)], [(1, 14), (1, 15)], [(1, 4), (1, 5)], [(0, 19), (0, 20)]⟩

theorem g023_ok : tagOKF CompactData.T CompactData.F g023 = true := by decide +kernel

def g024 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (1 / 40 : ℚ), (21 / 800 : ℚ), (9 / 160 : ℚ), (41 / 1600 : ℚ), (0, 5), (1, 15), (1, 4), (0, 21), [(0, 4), (0, 5)], [(1, 15), (1, 16)], [(1, 4), (1, 5)], [(0, 20), (0, 21)]⟩

theorem g024_ok : tagOKF CompactData.T CompactData.F g024 = true := by decide +kernel

def g025 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (1 / 40 : ℚ), (21 / 800 : ℚ), (47 / 800 : ℚ), (41 / 1600 : ℚ), (0, 5), (1, 16), (1, 5), (0, 22), [(0, 4), (0, 5)], [(1, 15), (1, 16)], [(1, 5)], [(0, 21), (0, 22)]⟩

theorem g025_ok : tagOKF CompactData.T CompactData.F g025 = true := by decide +kernel

def g026 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (21 / 800 : ℚ), (11 / 400 : ℚ), (9 / 160 : ℚ), (43 / 1600 : ℚ), (0, 6), (1, 15), (1, 5), (0, 21), [(0, 5), (0, 6)], [(1, 15), (1, 16)], [(1, 4), (1, 5)], [(0, 20), (0, 21)]⟩

theorem g026_ok : tagOKF CompactData.T CompactData.F g026 = true := by decide +kernel

def g027 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (21 / 800 : ℚ), (11 / 400 : ℚ), (47 / 800 : ℚ), (43 / 1600 : ℚ), (0, 6), (1, 16), (1, 5), (0, 22), [(0, 5), (0, 6)], [(1, 16)], [(1, 5), (1, 6)], [(0, 21), (0, 22)]⟩

theorem g027_ok : tagOKF CompactData.T CompactData.F g027 = true := by decide +kernel

def g028 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (11 / 400 : ℚ), (3 / 100 : ℚ), (9 / 160 : ℚ), (23 / 800 : ℚ), (0, 7), (1, 16), (1, 5), (0, 21), [(0, 6), (0, 7), (0, 8)], [(1, 15), (1, 16)], [(1, 5), (1, 6)], [(0, 20), (0, 21)]⟩

theorem g028_ok : tagOKF CompactData.T CompactData.F g028 = true := by decide +kernel

def g029 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (11 / 400 : ℚ), (3 / 100 : ℚ), (47 / 800 : ℚ), (23 / 800 : ℚ), (0, 7), (1, 16), (1, 6), (0, 22), [(0, 6), (0, 7), (0, 8)], [(1, 16), (1, 17)], [(1, 5), (1, 6)], [(0, 21), (0, 22)]⟩

theorem g029_ok : tagOKF CompactData.T CompactData.F g029 = true := by decide +kernel

def g030 : Tag := .inl ⟨(1 / 25 : ℚ), (9 / 200 : ℚ), (3 / 100 : ℚ), (7 / 200 : ℚ)⟩

theorem g030_ok : tagOKF CompactData.T CompactData.F g030 = true := by decide +kernel

def g031 : Tag := .inl ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ)⟩

theorem g031_ok : tagOKF CompactData.T CompactData.F g031 = true := by decide +kernel

def g032 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (39 / 800 : ℚ), (1 / 32 : ℚ), (0, 9), (1, 14), (1, 4), (0, 18), [(0, 8), (0, 9)], [(1, 13), (1, 14)], [(1, 3), (1, 4), (1, 5)], [(0, 17), (0, 18)]⟩

theorem g032_ok : tagOKF CompactData.T CompactData.F g032 = true := by decide +kernel

def g033 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (37 / 800 : ℚ), (27 / 800 : ℚ), (0, 10), (1, 13), (1, 4), (0, 17), [(0, 9), (0, 10), (0, 11)], [(1, 13), (1, 14)], [(1, 3), (1, 4), (1, 5)], [(0, 16), (0, 17)]⟩

theorem g033_ok : tagOKF CompactData.T CompactData.F g033 = true := by decide +kernel

def g034 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (39 / 800 : ℚ), (27 / 800 : ℚ), (0, 10), (1, 14), (1, 5), (0, 18), [(0, 9), (0, 10), (0, 11)], [(1, 13), (1, 14), (1, 15)], [(1, 4), (1, 5)], [(0, 17), (0, 18)]⟩

theorem g034_ok : tagOKF CompactData.T CompactData.F g034 = true := by decide +kernel

def g035 : Tag := .inl ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ)⟩

theorem g035_ok : tagOKF CompactData.T CompactData.F g035 = true := by decide +kernel

def g036 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (7 / 160 : ℚ), (29 / 800 : ℚ), (0, 12), (1, 13), (1, 4), (0, 16), [(0, 11), (0, 12)], [(1, 12), (1, 13)], [(1, 3), (1, 4), (1, 5)], [(0, 15), (0, 16)]⟩

theorem g036_ok : tagOKF CompactData.T CompactData.F g036 = true := by decide +kernel

def g037 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (33 / 800 : ℚ), (31 / 800 : ℚ), (0, 13), (1, 12), (1, 4), (0, 14), [(0, 12), (0, 13), (0, 14)], [(1, 12), (1, 13)], [(1, 3), (1, 4), (1, 5)], [(0, 14), (0, 15)]⟩

theorem g037_ok : tagOKF CompactData.T CompactData.F g037 = true := by decide +kernel

def g038 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (7 / 160 : ℚ), (31 / 800 : ℚ), (0, 13), (1, 13), (1, 5), (0, 16), [(0, 12), (0, 13), (0, 14)], [(1, 13), (1, 14)], [(1, 4), (1, 5)], [(0, 15), (0, 16)]⟩

theorem g038_ok : tagOKF CompactData.T CompactData.F g038 = true := by decide +kernel

def g039 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (37 / 800 : ℚ), (29 / 800 : ℚ), (0, 12), (1, 14), (1, 5), (0, 17), [(0, 11), (0, 12)], [(1, 13), (1, 14)], [(1, 4), (1, 5)], [(0, 16), (0, 17)]⟩

theorem g039_ok : tagOKF CompactData.T CompactData.F g039 = true := by decide +kernel

def g040 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (39 / 800 : ℚ), (29 / 800 : ℚ), (0, 12), (1, 14), (1, 5), (0, 18), [(0, 11), (0, 12)], [(1, 14), (1, 15)], [(1, 5), (1, 6)], [(0, 17), (0, 18)]⟩

theorem g040_ok : tagOKF CompactData.T CompactData.F g040 = true := by decide +kernel

def g041 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (37 / 800 : ℚ), (31 / 800 : ℚ), (0, 13), (1, 14), (1, 5), (0, 17), [(0, 12), (0, 13), (0, 14)], [(1, 13), (1, 14), (1, 15)], [(1, 5), (1, 6)], [(0, 16), (0, 17)]⟩

theorem g041_ok : tagOKF CompactData.T CompactData.F g041 = true := by decide +kernel

def g042 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (39 / 800 : ℚ), (31 / 800 : ℚ), (0, 13), (1, 15), (1, 6), (0, 18), [(0, 12), (0, 13), (0, 14)], [(1, 14), (1, 15)], [(1, 5), (1, 6)], [(0, 17), (0, 18)]⟩

theorem g042_ok : tagOKF CompactData.T CompactData.F g042 = true := by decide +kernel

def g043 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (41 / 800 : ℚ), (1 / 32 : ℚ), (0, 9), (1, 14), (1, 5), (0, 19), [(0, 8), (0, 9)], [(1, 14), (1, 15)], [(1, 4), (1, 5)], [(0, 18), (0, 19)]⟩

theorem g043_ok : tagOKF CompactData.T CompactData.F g043 = true := by decide +kernel

def g044 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (43 / 800 : ℚ), (1 / 32 : ℚ), (0, 9), (1, 15), (1, 5), (0, 20), [(0, 8), (0, 9)], [(1, 15), (1, 16)], [(1, 5), (1, 6)], [(0, 19), (0, 20)]⟩

theorem g044_ok : tagOKF CompactData.T CompactData.F g044 = true := by decide +kernel

def g045 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (41 / 800 : ℚ), (27 / 800 : ℚ), (0, 10), (1, 15), (1, 5), (0, 19), [(0, 9), (0, 10), (0, 11)], [(1, 14), (1, 15)], [(1, 5), (1, 6)], [(0, 18), (0, 19)]⟩

theorem g045_ok : tagOKF CompactData.T CompactData.F g045 = true := by decide +kernel

def g046 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (43 / 800 : ℚ), (27 / 800 : ℚ), (0, 10), (1, 16), (1, 6), (0, 20), [(0, 9), (0, 10), (0, 11)], [(1, 15), (1, 16)], [(1, 5), (1, 6)], [(0, 19), (0, 20)]⟩

theorem g046_ok : tagOKF CompactData.T CompactData.F g046 = true := by decide +kernel

def g047 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (9 / 160 : ℚ), (1 / 32 : ℚ), (0, 9), (1, 16), (1, 6), (0, 21), [(0, 8), (0, 9)], [(1, 15), (1, 16)], [(1, 5), (1, 6)], [(0, 20), (0, 21)]⟩

theorem g047_ok : tagOKF CompactData.T CompactData.F g047 = true := by decide +kernel

def g048 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (47 / 800 : ℚ), (1 / 32 : ℚ), (0, 9), (1, 17), (1, 6), (0, 22), [(0, 8), (0, 9)], [(1, 16), (1, 17)], [(1, 6), (1, 7)], [(0, 21), (0, 22)]⟩

theorem g048_ok : tagOKF CompactData.T CompactData.F g048 = true := by decide +kernel

def g049 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (9 / 160 : ℚ), (27 / 800 : ℚ), (0, 10), (1, 16), (1, 6), (0, 21), [(0, 9), (0, 10), (0, 11)], [(1, 16), (1, 17)], [(1, 6), (1, 7)], [(0, 20), (0, 21)]⟩

theorem g049_ok : tagOKF CompactData.T CompactData.F g049 = true := by decide +kernel

def g050 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (47 / 800 : ℚ), (27 / 800 : ℚ), (0, 10), (1, 17), (1, 7), (0, 22), [(0, 9), (0, 10), (0, 11)], [(1, 16), (1, 17)], [(1, 6), (1, 7)], [(0, 21), (0, 22)]⟩

theorem g050_ok : tagOKF CompactData.T CompactData.F g050 = true := by decide +kernel

def g051 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (41 / 800 : ℚ), (29 / 800 : ℚ), (0, 12), (1, 15), (1, 6), (0, 19), [(0, 11), (0, 12)], [(1, 15), (1, 16)], [(1, 5), (1, 6)], [(0, 18), (0, 19)]⟩

theorem g051_ok : tagOKF CompactData.T CompactData.F g051 = true := by decide +kernel

def g052 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (43 / 800 : ℚ), (29 / 800 : ℚ), (0, 12), (1, 16), (1, 6), (0, 20), [(0, 11), (0, 12)], [(1, 15), (1, 16)], [(1, 6), (1, 7)], [(0, 19), (0, 20)]⟩

theorem g052_ok : tagOKF CompactData.T CompactData.F g052 = true := by decide +kernel

def g053 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (41 / 800 : ℚ), (31 / 800 : ℚ), (0, 13), (1, 16), (1, 6), (0, 19), [(0, 12), (0, 13), (0, 14)], [(1, 15), (1, 16)], [(1, 6), (1, 7)], [(0, 18), (0, 19)]⟩

theorem g053_ok : tagOKF CompactData.T CompactData.F g053 = true := by decide +kernel

def g054 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (43 / 800 : ℚ), (31 / 800 : ℚ), (0, 13), (1, 16), (1, 7), (0, 20), [(0, 12), (0, 13), (0, 14)], [(1, 16), (1, 17)], [(1, 6), (1, 7)], [(0, 19), (0, 20)]⟩

theorem g054_ok : tagOKF CompactData.T CompactData.F g054 = true := by decide +kernel

def g055 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (9 / 160 : ℚ), (29 / 800 : ℚ), (0, 12), (1, 17), (1, 7), (0, 21), [(0, 11), (0, 12)], [(1, 16), (1, 17)], [(1, 6), (1, 7)], [(0, 20), (0, 21)]⟩

theorem g055_ok : tagOKF CompactData.T CompactData.F g055 = true := by decide +kernel

def g056 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (47 / 800 : ℚ), (29 / 800 : ℚ), (0, 12), (1, 17), (1, 7), (0, 22), [(0, 11), (0, 12)], [(1, 17), (1, 18)], [(1, 7), (1, 8)], [(0, 21), (0, 22)]⟩

theorem g056_ok : tagOKF CompactData.T CompactData.F g056 = true := by decide +kernel

def g057 : Tag := .inr ⟨(11 / 200 : ℚ), (23 / 400 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (9 / 160 : ℚ), (31 / 800 : ℚ), (0, 13), (1, 17), (1, 7), (0, 21), [(0, 12), (0, 13), (0, 14)], [(1, 16), (1, 17)], [(1, 7), (1, 8)], [(0, 20), (0, 21)]⟩

theorem g057_ok : tagOKF CompactData.T CompactData.F g057 = true := by decide +kernel

def g058 : Tag := .inr ⟨(23 / 400 : ℚ), (3 / 50 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (47 / 800 : ℚ), (31 / 800 : ℚ), (0, 13), (1, 18), (1, 8), (0, 22), [(0, 12), (0, 13), (0, 14)], [(1, 17), (1, 18)], [(1, 7), (1, 8)], [(0, 21), (0, 22)]⟩

theorem g058_ok : tagOKF CompactData.T CompactData.F g058 = true := by decide +kernel

def g059 : Tag := .inr ⟨(3 / 50 : ℚ), (1 / 16 : ℚ), (1 / 50 : ℚ), (17 / 800 : ℚ), (49 / 800 : ℚ), (33 / 1600 : ℚ), (0, 0), (1, 16), (1, 4), (0, 22), [(0, 0), (0, 1)], [(1, 15), (1, 16)], [(1, 4), (1, 5)], [(0, 22), (0, 23)]⟩

theorem g059_ok : tagOKF CompactData.T CompactData.F g059 = true := by decide +kernel

def g060 : Tag := .inr ⟨(1 / 16 : ℚ), (13 / 200 : ℚ), (1 / 50 : ℚ), (17 / 800 : ℚ), (51 / 800 : ℚ), (33 / 1600 : ℚ), (0, 0), (1, 17), (1, 5), (0, 23), [(0, 0), (0, 1)], [(1, 16), (1, 17)], [(1, 5)], [(0, 23), (1, 0)]⟩

theorem g060_ok : tagOKF CompactData.T CompactData.F g060 = true := by decide +kernel

def g061 : Tag := .inr ⟨(3 / 50 : ℚ), (1 / 16 : ℚ), (17 / 800 : ℚ), (9 / 400 : ℚ), (49 / 800 : ℚ), (7 / 320 : ℚ), (0, 1), (1, 16), (1, 5), (0, 22), [(0, 1), (0, 2)], [(1, 16)], [(1, 4), (1, 5)], [(0, 22), (0, 23)]⟩

theorem g061_ok : tagOKF CompactData.T CompactData.F g061 = true := by decide +kernel

def g062 : Tag := .inr ⟨(1 / 16 : ℚ), (13 / 200 : ℚ), (17 / 800 : ℚ), (9 / 400 : ℚ), (51 / 800 : ℚ), (7 / 320 : ℚ), (0, 1), (1, 17), (1, 5), (0, 23), [(0, 1), (0, 2)], [(1, 16), (1, 17)], [(1, 5), (1, 6)], [(0, 23), (1, 0)]⟩

theorem g062_ok : tagOKF CompactData.T CompactData.F g062 = true := by decide +kernel

def g063 : Tag := .inr ⟨(13 / 200 : ℚ), (27 / 400 : ℚ), (1 / 50 : ℚ), (17 / 800 : ℚ), (53 / 800 : ℚ), (33 / 1600 : ℚ), (0, 0), (1, 17), (1, 6), (1, 0), [(0, 0), (0, 1)], [(1, 17), (1, 18)], [(1, 5), (1, 6)], [(1, 0)]⟩

theorem g063_ok : tagOKF CompactData.T CompactData.F g063 = true := by decide +kernel

def g064 : Tag := .inr ⟨(27 / 400 : ℚ), (7 / 100 : ℚ), (1 / 50 : ℚ), (17 / 800 : ℚ), (11 / 160 : ℚ), (33 / 1600 : ℚ), (0, 0), (1, 18), (1, 6), (1, 1), [(0, 0), (0, 1)], [(1, 17), (1, 18)], [(1, 6), (1, 7)], [(1, 0), (1, 1)]⟩

theorem g064_ok : tagOKF CompactData.T CompactData.F g064 = true := by decide +kernel

def g065 : Tag := .inr ⟨(13 / 200 : ℚ), (27 / 400 : ℚ), (17 / 800 : ℚ), (9 / 400 : ℚ), (53 / 800 : ℚ), (7 / 320 : ℚ), (0, 1), (1, 17), (1, 6), (1, 0), [(0, 1), (0, 2)], [(1, 17), (1, 18)], [(1, 5), (1, 6)], [(1, 0)]⟩

theorem g065_ok : tagOKF CompactData.T CompactData.F g065 = true := by decide +kernel

def g066 : Tag := .inr ⟨(27 / 400 : ℚ), (7 / 100 : ℚ), (17 / 800 : ℚ), (9 / 400 : ℚ), (11 / 160 : ℚ), (7 / 320 : ℚ), (0, 1), (1, 18), (1, 6), (1, 1), [(0, 1), (0, 2)], [(1, 18)], [(1, 6), (1, 7)], [(1, 0), (1, 1)]⟩

theorem g066_ok : tagOKF CompactData.T CompactData.F g066 = true := by decide +kernel

def g067 : Tag := .inr ⟨(3 / 50 : ℚ), (1 / 16 : ℚ), (9 / 400 : ℚ), (19 / 800 : ℚ), (49 / 800 : ℚ), (37 / 1600 : ℚ), (0, 2), (1, 16), (1, 5), (0, 22), [(0, 2), (0, 3)], [(1, 16), (1, 17)], [(1, 5)], [(0, 22), (0, 23)]⟩

theorem g067_ok : tagOKF CompactData.T CompactData.F g067 = true := by decide +kernel

def g068 : Tag := .inr ⟨(1 / 16 : ℚ), (13 / 200 : ℚ), (9 / 400 : ℚ), (19 / 800 : ℚ), (51 / 800 : ℚ), (37 / 1600 : ℚ), (0, 2), (1, 17), (1, 6), (0, 23), [(0, 2), (0, 3)], [(1, 16), (1, 17)], [(1, 5), (1, 6)], [(0, 23), (1, 0)]⟩

theorem g068_ok : tagOKF CompactData.T CompactData.F g068 = true := by decide +kernel

def g069 : Tag := .inr ⟨(3 / 50 : ℚ), (1 / 16 : ℚ), (19 / 800 : ℚ), (1 / 40 : ℚ), (49 / 800 : ℚ), (39 / 1600 : ℚ), (0, 4), (1, 16), (1, 5), (0, 22), [(0, 3), (0, 4)], [(1, 16), (1, 17)], [(1, 5), (1, 6)], [(0, 22), (0, 23)]⟩

theorem g069_ok : tagOKF CompactData.T CompactData.F g069 = true := by decide +kernel

def g070 : Tag := .inr ⟨(1 / 16 : ℚ), (13 / 200 : ℚ), (19 / 800 : ℚ), (1 / 40 : ℚ), (51 / 800 : ℚ), (39 / 1600 : ℚ), (0, 4), (1, 17), (1, 6), (0, 23), [(0, 3), (0, 4)], [(1, 17)], [(1, 5), (1, 6)], [(0, 23), (1, 0)]⟩

theorem g070_ok : tagOKF CompactData.T CompactData.F g070 = true := by decide +kernel

def g071 : Tag := .inr ⟨(13 / 200 : ℚ), (27 / 400 : ℚ), (9 / 400 : ℚ), (19 / 800 : ℚ), (53 / 800 : ℚ), (37 / 1600 : ℚ), (0, 2), (1, 18), (1, 6), (1, 0), [(0, 2), (0, 3)], [(1, 17), (1, 18)], [(1, 6), (1, 7)], [(1, 0)]⟩

theorem g071_ok : tagOKF CompactData.T CompactData.F g071 = true := by decide +kernel

def g072 : Tag := .inr ⟨(27 / 400 : ℚ), (7 / 100 : ℚ), (9 / 400 : ℚ), (19 / 800 : ℚ), (11 / 160 : ℚ), (37 / 1600 : ℚ), (0, 2), (1, 18), (1, 7), (1, 1), [(0, 2), (0, 3)], [(1, 18), (1, 19)], [(1, 6), (1, 7)], [(1, 0), (1, 1)]⟩

theorem g072_ok : tagOKF CompactData.T CompactData.F g072 = true := by decide +kernel

def g073 : Tag := .inr ⟨(13 / 200 : ℚ), (27 / 400 : ℚ), (19 / 800 : ℚ), (1 / 40 : ℚ), (53 / 800 : ℚ), (39 / 1600 : ℚ), (0, 4), (1, 18), (1, 6), (1, 0), [(0, 3), (0, 4)], [(1, 17), (1, 18)], [(1, 6), (1, 7)], [(1, 0)]⟩

theorem g073_ok : tagOKF CompactData.T CompactData.F g073 = true := by decide +kernel

def g074 : Tag := .inr ⟨(27 / 400 : ℚ), (7 / 100 : ℚ), (19 / 800 : ℚ), (1 / 40 : ℚ), (11 / 160 : ℚ), (39 / 1600 : ℚ), (0, 4), (1, 18), (1, 7), (1, 1), [(0, 3), (0, 4)], [(1, 18), (1, 19)], [(1, 7)], [(1, 0), (1, 1)]⟩

theorem g074_ok : tagOKF CompactData.T CompactData.F g074 = true := by decide +kernel

def g075 : Tag := .inr ⟨(7 / 100 : ℚ), (29 / 400 : ℚ), (1 / 50 : ℚ), (17 / 800 : ℚ), (57 / 800 : ℚ), (33 / 1600 : ℚ), (0, 0), (1, 19), (1, 7), (1, 2), [(0, 0), (0, 1)], [(1, 18), (1, 19)], [(1, 6), (1, 7)], [(1, 1), (1, 2)]⟩

theorem g075_ok : tagOKF CompactData.T CompactData.F g075 = true := by decide +kernel

def g076 : Tag := .inr ⟨(29 / 400 : ℚ), (3 / 40 : ℚ), (1 / 50 : ℚ), (17 / 800 : ℚ), (59 / 800 : ℚ), (33 / 1600 : ℚ), (0, 0), (1, 19), (1, 7), (1, 2), [(0, 0), (0, 1)], [(1, 19), (1, 20)], [(1, 7), (1, 8)], [(1, 2), (1, 3)]⟩

theorem g076_ok : tagOKF CompactData.T CompactData.F g076 = true := by decide +kernel

def g077 : Tag := .inr ⟨(7 / 100 : ℚ), (29 / 400 : ℚ), (17 / 800 : ℚ), (9 / 400 : ℚ), (57 / 800 : ℚ), (7 / 320 : ℚ), (0, 1), (1, 19), (1, 7), (1, 2), [(0, 1), (0, 2)], [(1, 18), (1, 19)], [(1, 7)], [(1, 1), (1, 2)]⟩

theorem g077_ok : tagOKF CompactData.T CompactData.F g077 = true := by decide +kernel

def g078 : Tag := .inr ⟨(29 / 400 : ℚ), (3 / 40 : ℚ), (17 / 800 : ℚ), (9 / 400 : ℚ), (59 / 800 : ℚ), (7 / 320 : ℚ), (0, 1), (1, 19), (1, 8), (1, 2), [(0, 1), (0, 2)], [(1, 19), (1, 20)], [(1, 7), (1, 8)], [(1, 2), (1, 3)]⟩

theorem g078_ok : tagOKF CompactData.T CompactData.F g078 = true := by decide +kernel

def g079 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (1 / 50 : ℚ), (17 / 800 : ℚ), (31 / 400 : ℚ), (33 / 1600 : ℚ), (0, 0), (1, 20), (1, 8), (1, 3), [(0, 0), (0, 1)], [(1, 19), (1, 20), (1, 21)], [(1, 7), (1, 8), (1, 9)], [(1, 3), (1, 4)]⟩

theorem g079_ok : tagOKF CompactData.T CompactData.F g079 = true := by decide +kernel

def g080 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (17 / 800 : ℚ), (9 / 400 : ℚ), (31 / 400 : ℚ), (7 / 320 : ℚ), (0, 1), (1, 20), (1, 8), (1, 3), [(0, 1), (0, 2)], [(1, 20), (1, 21)], [(1, 8), (1, 9)], [(1, 3), (1, 4)]⟩

theorem g080_ok : tagOKF CompactData.T CompactData.F g080 = true := by decide +kernel

def g081 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (9 / 400 : ℚ), (19 / 800 : ℚ), (29 / 400 : ℚ), (37 / 1600 : ℚ), (0, 2), (1, 19), (1, 8), (1, 2), [(0, 2), (0, 3)], [(1, 18), (1, 19), (1, 20)], [(1, 7), (1, 8)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g081_ok : tagOKF CompactData.T CompactData.F g081 = true := by decide +kernel

def g082 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (19 / 800 : ℚ), (1 / 40 : ℚ), (29 / 400 : ℚ), (39 / 1600 : ℚ), (0, 4), (1, 19), (1, 8), (1, 2), [(0, 3), (0, 4)], [(1, 19), (1, 20)], [(1, 7), (1, 8)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g082_ok : tagOKF CompactData.T CompactData.F g082 = true := by decide +kernel

def g083 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (9 / 400 : ℚ), (19 / 800 : ℚ), (31 / 400 : ℚ), (37 / 1600 : ℚ), (0, 2), (1, 20), (1, 9), (1, 3), [(0, 2), (0, 3)], [(1, 20), (1, 21)], [(1, 8), (1, 9)], [(1, 3), (1, 4)]⟩

theorem g083_ok : tagOKF CompactData.T CompactData.F g083 = true := by decide +kernel

def g084 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (19 / 800 : ℚ), (1 / 40 : ℚ), (31 / 400 : ℚ), (39 / 1600 : ℚ), (0, 4), (1, 20), (1, 9), (1, 3), [(0, 3), (0, 4)], [(1, 20), (1, 21)], [(1, 8), (1, 9)], [(1, 3), (1, 4)]⟩

theorem g084_ok : tagOKF CompactData.T CompactData.F g084 = true := by decide +kernel

def g085 : Tag := .inr ⟨(3 / 50 : ℚ), (1 / 16 : ℚ), (1 / 40 : ℚ), (21 / 800 : ℚ), (49 / 800 : ℚ), (41 / 1600 : ℚ), (0, 5), (1, 17), (1, 6), (0, 22), [(0, 4), (0, 5)], [(1, 16), (1, 17)], [(1, 5), (1, 6)], [(0, 22), (0, 23)]⟩

theorem g085_ok : tagOKF CompactData.T CompactData.F g085 = true := by decide +kernel

def g086 : Tag := .inr ⟨(1 / 16 : ℚ), (13 / 200 : ℚ), (1 / 40 : ℚ), (21 / 800 : ℚ), (51 / 800 : ℚ), (41 / 1600 : ℚ), (0, 5), (1, 17), (1, 6), (0, 23), [(0, 4), (0, 5)], [(1, 17), (1, 18)], [(1, 6), (1, 7)], [(0, 23), (1, 0)]⟩

theorem g086_ok : tagOKF CompactData.T CompactData.F g086 = true := by decide +kernel

def g087 : Tag := .inr ⟨(3 / 50 : ℚ), (1 / 16 : ℚ), (21 / 800 : ℚ), (11 / 400 : ℚ), (49 / 800 : ℚ), (43 / 1600 : ℚ), (0, 6), (1, 17), (1, 6), (0, 22), [(0, 5), (0, 6)], [(1, 16), (1, 17)], [(1, 5), (1, 6)], [(0, 22), (0, 23)]⟩

theorem g087_ok : tagOKF CompactData.T CompactData.F g087 = true := by decide +kernel

def g088 : Tag := .inr ⟨(1 / 16 : ℚ), (13 / 200 : ℚ), (21 / 800 : ℚ), (11 / 400 : ℚ), (51 / 800 : ℚ), (43 / 1600 : ℚ), (0, 6), (1, 17), (1, 6), (0, 23), [(0, 5), (0, 6)], [(1, 17), (1, 18)], [(1, 6), (1, 7)], [(0, 23), (1, 0)]⟩

theorem g088_ok : tagOKF CompactData.T CompactData.F g088 = true := by decide +kernel

def g089 : Tag := .inr ⟨(13 / 200 : ℚ), (27 / 400 : ℚ), (1 / 40 : ℚ), (21 / 800 : ℚ), (53 / 800 : ℚ), (41 / 1600 : ℚ), (0, 5), (1, 18), (1, 7), (1, 0), [(0, 4), (0, 5)], [(1, 17), (1, 18)], [(1, 6), (1, 7)], [(1, 0)]⟩

theorem g089_ok : tagOKF CompactData.T CompactData.F g089 = true := by decide +kernel

def g090 : Tag := .inr ⟨(27 / 400 : ℚ), (7 / 100 : ℚ), (1 / 40 : ℚ), (21 / 800 : ℚ), (11 / 160 : ℚ), (41 / 1600 : ℚ), (0, 5), (1, 19), (1, 7), (1, 1), [(0, 4), (0, 5)], [(1, 18), (1, 19)], [(1, 7), (1, 8)], [(1, 0), (1, 1)]⟩

theorem g090_ok : tagOKF CompactData.T CompactData.F g090 = true := by decide +kernel

def g091 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (21 / 800 : ℚ), (11 / 400 : ℚ), (27 / 400 : ℚ), (43 / 1600 : ℚ), (0, 6), (1, 18), (1, 7), (1, 0), [(0, 5), (0, 6)], [(1, 18), (1, 19)], [(1, 7), (1, 8)], [(1, 0), (1, 1)]⟩

theorem g091_ok : tagOKF CompactData.T CompactData.F g091 = true := by decide +kernel

def g092 : Tag := .inr ⟨(3 / 50 : ℚ), (1 / 16 : ℚ), (11 / 400 : ℚ), (23 / 800 : ℚ), (49 / 800 : ℚ), (9 / 320 : ℚ), (0, 6), (1, 17), (1, 6), (0, 22), [(0, 6), (0, 7)], [(1, 16), (1, 17)], [(1, 6), (1, 7)], [(0, 22), (0, 23)]⟩

theorem g092_ok : tagOKF CompactData.T CompactData.F g092 = true := by decide +kernel

def g093 : Tag := .inr ⟨(1 / 16 : ℚ), (13 / 200 : ℚ), (11 / 400 : ℚ), (23 / 800 : ℚ), (51 / 800 : ℚ), (9 / 320 : ℚ), (0, 6), (1, 18), (1, 7), (0, 23), [(0, 6), (0, 7)], [(1, 17), (1, 18)], [(1, 6), (1, 7)], [(0, 23), (1, 0)]⟩

theorem g093_ok : tagOKF CompactData.T CompactData.F g093 = true := by decide +kernel

def g094 : Tag := .inr ⟨(3 / 50 : ℚ), (1 / 16 : ℚ), (23 / 800 : ℚ), (3 / 100 : ℚ), (49 / 800 : ℚ), (47 / 1600 : ℚ), (0, 7), (1, 17), (1, 6), (0, 22), [(0, 7), (0, 8)], [(1, 17)], [(1, 6), (1, 7)], [(0, 22), (0, 23)]⟩

theorem g094_ok : tagOKF CompactData.T CompactData.F g094 = true := by decide +kernel

def g095 : Tag := .inr ⟨(1 / 16 : ℚ), (13 / 200 : ℚ), (23 / 800 : ℚ), (3 / 100 : ℚ), (51 / 800 : ℚ), (47 / 1600 : ℚ), (0, 7), (1, 18), (1, 7), (0, 23), [(0, 7), (0, 8)], [(1, 17), (1, 18)], [(1, 7)], [(0, 23), (1, 0)]⟩

theorem g095_ok : tagOKF CompactData.T CompactData.F g095 = true := by decide +kernel

def g096 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (11 / 400 : ℚ), (23 / 800 : ℚ), (27 / 400 : ℚ), (9 / 320 : ℚ), (0, 6), (1, 19), (1, 8), (1, 0), [(0, 6), (0, 7)], [(1, 18), (1, 19)], [(1, 7), (1, 8)], [(1, 0), (1, 1)]⟩

theorem g096_ok : tagOKF CompactData.T CompactData.F g096 = true := by decide +kernel

def g097 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (23 / 800 : ℚ), (3 / 100 : ℚ), (27 / 400 : ℚ), (47 / 1600 : ℚ), (0, 7), (1, 19), (1, 8), (1, 0), [(0, 7), (0, 8)], [(1, 18), (1, 19)], [(1, 7), (1, 8)], [(1, 0), (1, 1)]⟩

theorem g097_ok : tagOKF CompactData.T CompactData.F g097 = true := by decide +kernel

def g098 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (1 / 40 : ℚ), (21 / 800 : ℚ), (29 / 400 : ℚ), (41 / 1600 : ℚ), (0, 5), (1, 19), (1, 8), (1, 2), [(0, 4), (0, 5)], [(1, 19), (1, 20)], [(1, 7), (1, 8), (1, 9)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g098_ok : tagOKF CompactData.T CompactData.F g098 = true := by decide +kernel

def g099 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (21 / 800 : ℚ), (11 / 400 : ℚ), (29 / 400 : ℚ), (43 / 1600 : ℚ), (0, 6), (1, 20), (1, 8), (1, 2), [(0, 5), (0, 6)], [(1, 19), (1, 20)], [(1, 8), (1, 9)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g099_ok : tagOKF CompactData.T CompactData.F g099 = true := by decide +kernel

def g100 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (1 / 40 : ℚ), (21 / 800 : ℚ), (31 / 400 : ℚ), (41 / 1600 : ℚ), (0, 5), (1, 21), (1, 9), (1, 3), [(0, 4), (0, 5)], [(1, 20), (1, 21)], [(1, 8), (1, 9), (1, 10)], [(1, 3), (1, 4)]⟩

theorem g100_ok : tagOKF CompactData.T CompactData.F g100 = true := by decide +kernel

def g101 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (21 / 800 : ℚ), (11 / 400 : ℚ), (31 / 400 : ℚ), (43 / 1600 : ℚ), (0, 6), (1, 21), (1, 9), (1, 3), [(0, 5), (0, 6)], [(1, 20), (1, 21)], [(1, 9), (1, 10)], [(1, 3), (1, 4)]⟩

theorem g101_ok : tagOKF CompactData.T CompactData.F g101 = true := by decide +kernel

def g102 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (11 / 400 : ℚ), (23 / 800 : ℚ), (29 / 400 : ℚ), (9 / 320 : ℚ), (0, 6), (1, 20), (1, 9), (1, 2), [(0, 6), (0, 7)], [(1, 19), (1, 20)], [(1, 8), (1, 9)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g102_ok : tagOKF CompactData.T CompactData.F g102 = true := by decide +kernel

def g103 : Tag := .inr ⟨(7 / 100 : ℚ), (3 / 40 : ℚ), (23 / 800 : ℚ), (3 / 100 : ℚ), (29 / 400 : ℚ), (47 / 1600 : ℚ), (0, 7), (1, 20), (1, 9), (1, 2), [(0, 7), (0, 8)], [(1, 19), (1, 20), (1, 21)], [(1, 8), (1, 9)], [(1, 1), (1, 2), (1, 3)]⟩

theorem g103_ok : tagOKF CompactData.T CompactData.F g103 = true := by decide +kernel

def g104 : Tag := .inr ⟨(3 / 40 : ℚ), (2 / 25 : ℚ), (11 / 400 : ℚ), (3 / 100 : ℚ), (31 / 400 : ℚ), (23 / 800 : ℚ), (0, 7), (1, 21), (1, 10), (1, 3), [(0, 6), (0, 7), (0, 8)], [(1, 20), (1, 21), (1, 22)], [(1, 9), (1, 10)], [(1, 3), (1, 4)]⟩

theorem g104_ok : tagOKF CompactData.T CompactData.F g104 = true := by decide +kernel

def g105 : Tag := .inr ⟨(3 / 50 : ℚ), (1 / 16 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (49 / 800 : ℚ), (1 / 32 : ℚ), (0, 9), (1, 17), (1, 7), (0, 22), [(0, 8), (0, 9)], [(1, 17), (1, 18)], [(1, 6), (1, 7)], [(0, 22), (0, 23)]⟩

theorem g105_ok : tagOKF CompactData.T CompactData.F g105 = true := by decide +kernel

def g106 : Tag := .inr ⟨(1 / 16 : ℚ), (13 / 200 : ℚ), (3 / 100 : ℚ), (13 / 400 : ℚ), (51 / 800 : ℚ), (1 / 32 : ℚ), (0, 9), (1, 18), (1, 7), (0, 23), [(0, 8), (0, 9)], [(1, 17), (1, 18)], [(1, 7), (1, 8)], [(0, 23), (1, 0)]⟩

theorem g106_ok : tagOKF CompactData.T CompactData.F g106 = true := by decide +kernel

def g107 : Tag := .inr ⟨(3 / 50 : ℚ), (1 / 16 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (49 / 800 : ℚ), (27 / 800 : ℚ), (0, 10), (1, 18), (1, 7), (0, 22), [(0, 9), (0, 10), (0, 11)], [(1, 17), (1, 18)], [(1, 7), (1, 8)], [(0, 22), (0, 23)]⟩

theorem g107_ok : tagOKF CompactData.T CompactData.F g107 = true := by decide +kernel

def g108 : Tag := .inr ⟨(1 / 16 : ℚ), (13 / 200 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (51 / 800 : ℚ), (27 / 800 : ℚ), (0, 10), (1, 18), (1, 8), (0, 23), [(0, 9), (0, 10), (0, 11)], [(1, 18), (1, 19)], [(1, 7), (1, 8)], [(0, 23), (1, 0)]⟩

theorem g108_ok : tagOKF CompactData.T CompactData.F g108 = true := by decide +kernel

def g109 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (3 / 100 : ℚ), (1 / 32 : ℚ), (27 / 400 : ℚ), (49 / 1600 : ℚ), (0, 8), (1, 19), (1, 8), (1, 0), [(0, 8), (0, 9)], [(1, 18), (1, 19), (1, 20)], [(1, 7), (1, 8), (1, 9)], [(1, 0), (1, 1)]⟩

theorem g109_ok : tagOKF CompactData.T CompactData.F g109 = true := by decide +kernel

def g110 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (1 / 32 : ℚ), (13 / 400 : ℚ), (27 / 400 : ℚ), (51 / 1600 : ℚ), (0, 9), (1, 19), (1, 8), (1, 0), [(0, 9)], [(1, 18), (1, 19), (1, 20)], [(1, 8), (1, 9)], [(1, 0), (1, 1)]⟩

theorem g110_ok : tagOKF CompactData.T CompactData.F g110 = true := by decide +kernel

def g111 : Tag := .inr ⟨(13 / 200 : ℚ), (27 / 400 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (53 / 800 : ℚ), (27 / 800 : ℚ), (0, 10), (1, 19), (1, 8), (1, 0), [(0, 9), (0, 10), (0, 11)], [(1, 18), (1, 19)], [(1, 8), (1, 9)], [(1, 0)]⟩

theorem g111_ok : tagOKF CompactData.T CompactData.F g111 = true := by decide +kernel

def g112 : Tag := .inr ⟨(27 / 400 : ℚ), (7 / 100 : ℚ), (13 / 400 : ℚ), (7 / 200 : ℚ), (11 / 160 : ℚ), (27 / 800 : ℚ), (0, 10), (1, 20), (1, 9), (1, 1), [(0, 9), (0, 10), (0, 11)], [(1, 19), (1, 20)], [(1, 8), (1, 9)], [(1, 0), (1, 1)]⟩

theorem g112_ok : tagOKF CompactData.T CompactData.F g112 = true := by decide +kernel

def g113 : Tag := .inr ⟨(3 / 50 : ℚ), (1 / 16 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (49 / 800 : ℚ), (29 / 800 : ℚ), (0, 12), (1, 18), (1, 8), (0, 22), [(0, 11), (0, 12)], [(1, 17), (1, 18)], [(1, 7), (1, 8)], [(0, 22), (0, 23)]⟩

theorem g113_ok : tagOKF CompactData.T CompactData.F g113 = true := by decide +kernel

def g114 : Tag := .inr ⟨(1 / 16 : ℚ), (13 / 200 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (51 / 800 : ℚ), (29 / 800 : ℚ), (0, 12), (1, 19), (1, 8), (0, 23), [(0, 11), (0, 12)], [(1, 18), (1, 19)], [(1, 8), (1, 9)], [(0, 23), (1, 0)]⟩

theorem g114_ok : tagOKF CompactData.T CompactData.F g114 = true := by decide +kernel

def g115 : Tag := .inr ⟨(3 / 50 : ℚ), (1 / 16 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (49 / 800 : ℚ), (31 / 800 : ℚ), (0, 13), (1, 18), (1, 8), (0, 22), [(0, 12), (0, 13), (0, 14)], [(1, 18), (1, 19)], [(1, 8), (1, 9)], [(0, 22), (0, 23)]⟩

theorem g115_ok : tagOKF CompactData.T CompactData.F g115 = true := by decide +kernel

def g116 : Tag := .inr ⟨(1 / 16 : ℚ), (13 / 200 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (51 / 800 : ℚ), (31 / 800 : ℚ), (0, 13), (1, 19), (1, 9), (0, 23), [(0, 12), (0, 13), (0, 14)], [(1, 18), (1, 19)], [(1, 8), (1, 9)], [(0, 23), (1, 0)]⟩

theorem g116_ok : tagOKF CompactData.T CompactData.F g116 = true := by decide +kernel

def g117 : Tag := .inr ⟨(13 / 200 : ℚ), (27 / 400 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (53 / 800 : ℚ), (29 / 800 : ℚ), (0, 12), (1, 19), (1, 9), (1, 0), [(0, 11), (0, 12)], [(1, 19), (1, 20)], [(1, 8), (1, 9)], [(1, 0)]⟩

theorem g117_ok : tagOKF CompactData.T CompactData.F g117 = true := by decide +kernel

def g118 : Tag := .inr ⟨(27 / 400 : ℚ), (7 / 100 : ℚ), (7 / 200 : ℚ), (3 / 80 : ℚ), (11 / 160 : ℚ), (29 / 800 : ℚ), (0, 12), (1, 20), (1, 9), (1, 1), [(0, 11), (0, 12)], [(1, 19), (1, 20)], [(1, 9), (1, 10)], [(1, 0), (1, 1)]⟩

theorem g118_ok : tagOKF CompactData.T CompactData.F g118 = true := by decide +kernel

def g119 : Tag := .inr ⟨(13 / 200 : ℚ), (7 / 100 : ℚ), (3 / 80 : ℚ), (1 / 25 : ℚ), (27 / 400 : ℚ), (31 / 800 : ℚ), (0, 13), (1, 20), (1, 10), (1, 0), [(0, 12), (0, 13), (0, 14)], [(1, 19), (1, 20), (1, 21)], [(1, 9), (1, 10)], [(1, 0), (1, 1)]⟩

theorem g119_ok : tagOKF CompactData.T CompactData.F g119 = true := by decide +kernel

def tags : List Tag := [g000, g001, g002, g003, g004, g005, g006, g007, g008, g009, g010, g011, g012, g013, g014, g015, g016, g017, g018, g019, g020, g021, g022, g023, g024, g025, g026, g027, g028, g029, g030, g031, g032, g033, g034, g035, g036, g037, g038, g039, g040, g041, g042, g043, g044, g045, g046, g047, g048, g049, g050, g051, g052, g053, g054, g055, g056, g057, g058, g059, g060, g061, g062, g063, g064, g065, g066, g067, g068, g069, g070, g071, g072, g073, g074, g075, g076, g077, g078, g079, g080, g081, g082, g083, g084, g085, g086, g087, g088, g089, g090, g091, g092, g093, g094, g095, g096, g097, g098, g099, g100, g101, g102, g103, g104, g105, g106, g107, g108, g109, g110, g111, g112, g113, g114, g115, g116, g117, g118, g119]

theorem tags_ok : tags.all (tagOKF CompactData.T CompactData.F) = true := by
  simp only [tags, List.all_cons, List.all_nil, g000_ok, g001_ok, g002_ok, g003_ok, g004_ok, g005_ok, g006_ok, g007_ok, g008_ok, g009_ok, g010_ok, g011_ok, g012_ok, g013_ok, g014_ok, g015_ok, g016_ok, g017_ok, g018_ok, g019_ok, g020_ok, g021_ok, g022_ok, g023_ok, g024_ok, g025_ok, g026_ok, g027_ok, g028_ok, g029_ok, g030_ok, g031_ok, g032_ok, g033_ok, g034_ok, g035_ok, g036_ok, g037_ok, g038_ok, g039_ok, g040_ok, g041_ok, g042_ok, g043_ok, g044_ok, g045_ok, g046_ok, g047_ok, g048_ok, g049_ok, g050_ok, g051_ok, g052_ok, g053_ok, g054_ok, g055_ok, g056_ok, g057_ok, g058_ok, g059_ok, g060_ok, g061_ok, g062_ok, g063_ok, g064_ok, g065_ok, g066_ok, g067_ok, g068_ok, g069_ok, g070_ok, g071_ok, g072_ok, g073_ok, g074_ok, g075_ok, g076_ok, g077_ok, g078_ok, g079_ok, g080_ok, g081_ok, g082_ok, g083_ok, g084_ok, g085_ok, g086_ok, g087_ok, g088_ok, g089_ok, g090_ok, g091_ok, g092_ok, g093_ok, g094_ok, g095_ok, g096_ok, g097_ok, g098_ok, g099_ok, g100_ok, g101_ok, g102_ok, g103_ok, g104_ok, g105_ok, g106_ok, g107_ok, g108_ok, g109_ok, g110_ok, g111_ok, g112_ok, g113_ok, g114_ok, g115_ok, g116_ok, g117_ok, g118_ok, g119_ok, Bool.and_self]

end CKLaneC3.CompactBatch18

end


