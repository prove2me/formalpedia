-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch22_q00
-- name    : CK_CKLaneC3_CompactBatch22_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T02:41:46.050916+00:00
-- url     : https://prove2.me/theorems/4675199a-df18-414a-a3f3-e240f89e2be0
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch22 (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch22 (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch22 (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch22 (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch22 (piece 1 of 4).lean)

import Definitions.Def_CK_CKLaneC3_CompactData
import Definitions.Def_CK_CKLaneC3_CompactCoverF



/-! Lane C3 compact cell batch (generated; memoised chains over the data tables). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactBatch22
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF

def g000 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (9 / 25 : ℚ), (19 / 50 : ℚ), (7 / 160 : ℚ), (37 / 100 : ℚ), (2, 11), (2, 16), (2, 14), (0, 16), [(2, 11), (2, 12)], [(2, 15), (2, 16)], [(2, 13), (2, 14)], [(0, 15), (0, 16)]⟩

theorem g000_ok : tagOKF CompactData.T CompactData.F g000 = true := by decide +kernel

def g001 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (19 / 50 : ℚ), (2 / 5 : ℚ), (7 / 160 : ℚ), (39 / 100 : ℚ), (2, 12), (2, 17), (2, 15), (0, 16), [(2, 12), (2, 13)], [(2, 16), (2, 17)], [(2, 14), (2, 15)], [(0, 15), (0, 16)]⟩

theorem g001_ok : tagOKF CompactData.T CompactData.F g001 = true := by decide +kernel

def g002 : Tag := .inr ⟨(9 / 200 : ℚ), (1 / 20 : ℚ), (8 / 25 : ℚ), (17 / 50 : ℚ), (19 / 400 : ℚ), (33 / 100 : ℚ), (2, 9), (2, 14), (2, 12), (0, 17), [(2, 8), (2, 9), (2, 10)], [(2, 13), (2, 14), (2, 15)], [(2, 11), (2, 12)], [(0, 16), (0, 17), (0, 18)]⟩

theorem g002_ok : tagOKF CompactData.T CompactData.F g002 = true := by decide +kernel

def g003 : Tag := .inr ⟨(9 / 200 : ℚ), (1 / 20 : ℚ), (17 / 50 : ℚ), (9 / 25 : ℚ), (19 / 400 : ℚ), (7 / 20 : ℚ), (2, 10), (2, 15), (2, 13), (0, 17), [(2, 10), (2, 11)], [(2, 14), (2, 15), (2, 16)], [(2, 12), (2, 13)], [(0, 16), (0, 17), (0, 18)]⟩

theorem g003_ok : tagOKF CompactData.T CompactData.F g003 = true := by decide +kernel

def g004 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (9 / 25 : ℚ), (19 / 50 : ℚ), (37 / 800 : ℚ), (37 / 100 : ℚ), (2, 11), (2, 16), (2, 14), (0, 17), [(2, 11), (2, 12)], [(2, 15), (2, 16), (2, 17)], [(2, 13), (2, 14)], [(0, 16), (0, 17)]⟩

theorem g004_ok : tagOKF CompactData.T CompactData.F g004 = true := by decide +kernel

def g005 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (19 / 50 : ℚ), (2 / 5 : ℚ), (37 / 800 : ℚ), (39 / 100 : ℚ), (2, 12), (2, 17), (2, 15), (0, 17), [(2, 12), (2, 13)], [(2, 16), (2, 17), (2, 18)], [(2, 14), (2, 15)], [(0, 16), (0, 17)]⟩

theorem g005_ok : tagOKF CompactData.T CompactData.F g005 = true := by decide +kernel

def g006 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (9 / 25 : ℚ), (19 / 50 : ℚ), (39 / 800 : ℚ), (37 / 100 : ℚ), (2, 11), (2, 16), (2, 14), (0, 18), [(2, 11), (2, 12)], [(2, 16), (2, 17)], [(2, 13), (2, 14)], [(0, 17), (0, 18)]⟩

theorem g006_ok : tagOKF CompactData.T CompactData.F g006 = true := by decide +kernel

def g007 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (19 / 50 : ℚ), (2 / 5 : ℚ), (39 / 800 : ℚ), (39 / 100 : ℚ), (2, 12), (2, 17), (2, 15), (0, 18), [(2, 12), (2, 13)], [(2, 17), (2, 18)], [(2, 14), (2, 15)], [(0, 17), (0, 18)]⟩

theorem g007_ok : tagOKF CompactData.T CompactData.F g007 = true := by decide +kernel

def g008 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (2 / 5 : ℚ), (21 / 50 : ℚ), (33 / 800 : ℚ), (41 / 100 : ℚ), (2, 13), (2, 18), (2, 15), (0, 14), [(2, 13), (2, 14)], [(2, 17), (2, 18)], [(2, 15), (2, 16)], [(0, 14), (0, 15)]⟩

theorem g008_ok : tagOKF CompactData.T CompactData.F g008 = true := by decide +kernel

def g009 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (21 / 50 : ℚ), (11 / 25 : ℚ), (33 / 800 : ℚ), (43 / 100 : ℚ), (2, 14), (2, 19), (2, 16), (0, 14), [(2, 14), (2, 15)], [(2, 18), (2, 19)], [(2, 16), (2, 17)], [(0, 14), (0, 15)]⟩

theorem g009_ok : tagOKF CompactData.T CompactData.F g009 = true := by decide +kernel

def g010 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (2 / 5 : ℚ), (21 / 50 : ℚ), (7 / 160 : ℚ), (41 / 100 : ℚ), (2, 13), (2, 18), (2, 16), (0, 16), [(2, 13), (2, 14)], [(2, 17), (2, 18)], [(2, 15), (2, 16)], [(0, 15), (0, 16)]⟩

theorem g010_ok : tagOKF CompactData.T CompactData.F g010 = true := by decide +kernel

def g011 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (21 / 50 : ℚ), (11 / 25 : ℚ), (7 / 160 : ℚ), (43 / 100 : ℚ), (2, 14), (2, 19), (2, 17), (0, 16), [(2, 14), (2, 15)], [(2, 18), (2, 19)], [(2, 16), (2, 17)], [(0, 15), (0, 16)]⟩

theorem g011_ok : tagOKF CompactData.T CompactData.F g011 = true := by decide +kernel

def g012 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (11 / 25 : ℚ), (23 / 50 : ℚ), (33 / 800 : ℚ), (9 / 20 : ℚ), (2, 15), (2, 20), (2, 17), (0, 14), [(2, 15), (2, 16)], [(2, 19), (2, 20)], [(2, 17), (2, 18)], [(0, 14), (0, 15)]⟩

theorem g012_ok : tagOKF CompactData.T CompactData.F g012 = true := by decide +kernel

def g013 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (23 / 50 : ℚ), (12 / 25 : ℚ), (33 / 800 : ℚ), (47 / 100 : ℚ), (2, 16), (2, 21), (2, 18), (0, 14), [(2, 16), (2, 17)], [(2, 20), (2, 21)], [(2, 18), (2, 19)], [(0, 14), (0, 15)]⟩

theorem g013_ok : tagOKF CompactData.T CompactData.F g013 = true := by decide +kernel

def g014 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (11 / 25 : ℚ), (23 / 50 : ℚ), (7 / 160 : ℚ), (9 / 20 : ℚ), (2, 15), (2, 20), (2, 18), (0, 16), [(2, 15), (2, 16)], [(2, 19), (2, 20)], [(2, 17), (2, 18)], [(0, 15), (0, 16)]⟩

theorem g014_ok : tagOKF CompactData.T CompactData.F g014 = true := by decide +kernel

def g015 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (23 / 50 : ℚ), (12 / 25 : ℚ), (7 / 160 : ℚ), (47 / 100 : ℚ), (2, 16), (2, 21), (2, 19), (0, 16), [(2, 16), (2, 17)], [(2, 20), (2, 21)], [(2, 18), (2, 19)], [(0, 15), (0, 16)]⟩

theorem g015_ok : tagOKF CompactData.T CompactData.F g015 = true := by decide +kernel

def g016 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (2 / 5 : ℚ), (21 / 50 : ℚ), (37 / 800 : ℚ), (41 / 100 : ℚ), (2, 13), (2, 18), (2, 16), (0, 17), [(2, 13), (2, 14)], [(2, 17), (2, 18), (2, 19)], [(2, 15), (2, 16)], [(0, 16), (0, 17)]⟩

theorem g016_ok : tagOKF CompactData.T CompactData.F g016 = true := by decide +kernel

def g017 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (21 / 50 : ℚ), (11 / 25 : ℚ), (37 / 800 : ℚ), (43 / 100 : ℚ), (2, 14), (2, 19), (2, 17), (0, 17), [(2, 14), (2, 15)], [(2, 18), (2, 19), (2, 20)], [(2, 16), (2, 17)], [(0, 16), (0, 17)]⟩

theorem g017_ok : tagOKF CompactData.T CompactData.F g017 = true := by decide +kernel

def g018 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (2 / 5 : ℚ), (21 / 50 : ℚ), (39 / 800 : ℚ), (41 / 100 : ℚ), (2, 13), (2, 18), (2, 16), (0, 18), [(2, 13), (2, 14)], [(2, 18), (2, 19)], [(2, 15), (2, 16)], [(0, 17), (0, 18)]⟩

theorem g018_ok : tagOKF CompactData.T CompactData.F g018 = true := by decide +kernel

def g019 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (21 / 50 : ℚ), (11 / 25 : ℚ), (39 / 800 : ℚ), (43 / 100 : ℚ), (2, 14), (2, 19), (2, 17), (0, 18), [(2, 14), (2, 15)], [(2, 19), (2, 20)], [(2, 16), (2, 17)], [(0, 17), (0, 18)]⟩

theorem g019_ok : tagOKF CompactData.T CompactData.F g019 = true := by decide +kernel

def g020 : Tag := .inr ⟨(9 / 200 : ℚ), (19 / 400 : ℚ), (11 / 25 : ℚ), (12 / 25 : ℚ), (37 / 800 : ℚ), (23 / 50 : ℚ), (2, 16), (2, 21), (2, 18), (0, 17), [(2, 15), (2, 16), (2, 17)], [(2, 19), (2, 20), (2, 21), (2, 22)], [(2, 17), (2, 18), (2, 19)], [(0, 16), (0, 17)]⟩

theorem g020_ok : tagOKF CompactData.T CompactData.F g020 = true := by decide +kernel

def g021 : Tag := .inr ⟨(19 / 400 : ℚ), (1 / 20 : ℚ), (11 / 25 : ℚ), (12 / 25 : ℚ), (39 / 800 : ℚ), (23 / 50 : ℚ), (2, 16), (2, 21), (2, 18), (0, 18), [(2, 15), (2, 16), (2, 17)], [(2, 20), (2, 21), (2, 22)], [(2, 17), (2, 18), (2, 19)], [(0, 17), (0, 18)]⟩

theorem g021_ok : tagOKF CompactData.T CompactData.F g021 = true := by decide +kernel

def g022 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (8 / 25 : ℚ), (17 / 50 : ℚ), (21 / 400 : ℚ), (33 / 100 : ℚ), (2, 9), (2, 15), (2, 12), (0, 19), [(2, 8), (2, 9), (2, 10)], [(2, 14), (2, 15)], [(2, 11), (2, 12), (2, 13)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g022_ok : tagOKF CompactData.T CompactData.F g022 = true := by decide +kernel

def g023 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (17 / 50 : ℚ), (9 / 25 : ℚ), (21 / 400 : ℚ), (7 / 20 : ℚ), (2, 10), (2, 16), (2, 13), (0, 19), [(2, 10), (2, 11)], [(2, 15), (2, 16)], [(2, 12), (2, 13), (2, 14)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g023_ok : tagOKF CompactData.T CompactData.F g023 = true := by decide +kernel

def g024 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (8 / 25 : ℚ), (17 / 50 : ℚ), (23 / 400 : ℚ), (33 / 100 : ℚ), (2, 9), (2, 15), (2, 12), (0, 21), [(2, 8), (2, 9), (2, 10)], [(2, 14), (2, 15), (2, 16)], [(2, 12), (2, 13)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g024_ok : tagOKF CompactData.T CompactData.F g024 = true := by decide +kernel

def g025 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (17 / 50 : ℚ), (9 / 25 : ℚ), (23 / 400 : ℚ), (7 / 20 : ℚ), (2, 10), (2, 16), (2, 13), (0, 21), [(2, 10), (2, 11)], [(2, 15), (2, 16), (2, 17)], [(2, 13), (2, 14)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g025_ok : tagOKF CompactData.T CompactData.F g025 = true := by decide +kernel

def g026 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (9 / 25 : ℚ), (19 / 50 : ℚ), (21 / 400 : ℚ), (37 / 100 : ℚ), (2, 11), (2, 17), (2, 14), (0, 19), [(2, 11), (2, 12)], [(2, 16), (2, 17)], [(2, 13), (2, 14), (2, 15)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g026_ok : tagOKF CompactData.T CompactData.F g026 = true := by decide +kernel

def g027 : Tag := .inr ⟨(1 / 20 : ℚ), (11 / 200 : ℚ), (19 / 50 : ℚ), (2 / 5 : ℚ), (21 / 400 : ℚ), (39 / 100 : ℚ), (2, 12), (2, 18), (2, 15), (0, 19), [(2, 12), (2, 13)], [(2, 17), (2, 18)], [(2, 14), (2, 15), (2, 16)], [(0, 18), (0, 19), (0, 20)]⟩

theorem g027_ok : tagOKF CompactData.T CompactData.F g027 = true := by decide +kernel

def g028 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (9 / 25 : ℚ), (19 / 50 : ℚ), (23 / 400 : ℚ), (37 / 100 : ℚ), (2, 11), (2, 17), (2, 14), (0, 21), [(2, 11), (2, 12)], [(2, 16), (2, 17), (2, 18)], [(2, 14), (2, 15)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g028_ok : tagOKF CompactData.T CompactData.F g028 = true := by decide +kernel

def g029 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (19 / 50 : ℚ), (2 / 5 : ℚ), (23 / 400 : ℚ), (39 / 100 : ℚ), (2, 12), (2, 18), (2, 15), (0, 21), [(2, 12), (2, 13)], [(2, 17), (2, 18), (2, 19)], [(2, 15), (2, 16)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g029_ok : tagOKF CompactData.T CompactData.F g029 = true := by decide +kernel

def g030 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (2 / 5 : ℚ), (21 / 50 : ℚ), (41 / 800 : ℚ), (41 / 100 : ℚ), (2, 13), (2, 19), (2, 16), (0, 19), [(2, 13), (2, 14)], [(2, 18), (2, 19)], [(2, 15), (2, 16), (2, 17)], [(0, 18), (0, 19)]⟩

theorem g030_ok : tagOKF CompactData.T CompactData.F g030 = true := by decide +kernel

def g031 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (21 / 50 : ℚ), (11 / 25 : ℚ), (41 / 800 : ℚ), (43 / 100 : ℚ), (2, 14), (2, 20), (2, 17), (0, 19), [(2, 14), (2, 15)], [(2, 19), (2, 20)], [(2, 16), (2, 17), (2, 18)], [(0, 18), (0, 19)]⟩

theorem g031_ok : tagOKF CompactData.T CompactData.F g031 = true := by decide +kernel

def g032 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (2 / 5 : ℚ), (11 / 25 : ℚ), (43 / 800 : ℚ), (21 / 50 : ℚ), (2, 14), (2, 19), (2, 17), (0, 20), [(2, 13), (2, 14), (2, 15)], [(2, 18), (2, 19), (2, 20)], [(2, 16), (2, 17), (2, 18)], [(0, 19), (0, 20)]⟩

theorem g032_ok : tagOKF CompactData.T CompactData.F g032 = true := by decide +kernel

def g033 : Tag := .inr ⟨(1 / 20 : ℚ), (21 / 400 : ℚ), (11 / 25 : ℚ), (12 / 25 : ℚ), (41 / 800 : ℚ), (23 / 50 : ℚ), (2, 16), (2, 21), (2, 18), (0, 19), [(2, 15), (2, 16), (2, 17)], [(2, 20), (2, 21), (2, 22)], [(2, 17), (2, 18), (2, 19), (2, 20)], [(0, 18), (0, 19)]⟩

theorem g033_ok : tagOKF CompactData.T CompactData.F g033 = true := by decide +kernel

def g034 : Tag := .inr ⟨(21 / 400 : ℚ), (11 / 200 : ℚ), (11 / 25 : ℚ), (12 / 25 : ℚ), (43 / 800 : ℚ), (23 / 50 : ℚ), (2, 16), (2, 21), (2, 19), (0, 20), [(2, 15), (2, 16), (2, 17)], [(2, 20), (2, 21), (2, 22)], [(2, 18), (2, 19), (2, 20)], [(0, 19), (0, 20)]⟩

theorem g034_ok : tagOKF CompactData.T CompactData.F g034 = true := by decide +kernel

def g035 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (2 / 5 : ℚ), (21 / 50 : ℚ), (23 / 400 : ℚ), (41 / 100 : ℚ), (2, 13), (2, 19), (2, 16), (0, 21), [(2, 13), (2, 14)], [(2, 18), (2, 19), (2, 20)], [(2, 16), (2, 17)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g035_ok : tagOKF CompactData.T CompactData.F g035 = true := by decide +kernel

def g036 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (21 / 50 : ℚ), (11 / 25 : ℚ), (23 / 400 : ℚ), (43 / 100 : ℚ), (2, 14), (2, 20), (2, 17), (0, 21), [(2, 14), (2, 15)], [(2, 19), (2, 20), (2, 21)], [(2, 17), (2, 18)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g036_ok : tagOKF CompactData.T CompactData.F g036 = true := by decide +kernel

def g037 : Tag := .inr ⟨(11 / 200 : ℚ), (3 / 50 : ℚ), (11 / 25 : ℚ), (12 / 25 : ℚ), (23 / 400 : ℚ), (23 / 50 : ℚ), (2, 16), (2, 22), (2, 19), (0, 21), [(2, 15), (2, 16), (2, 17)], [(2, 20), (2, 21), (2, 22), (2, 23)], [(2, 18), (2, 19), (2, 20)], [(0, 20), (0, 21), (0, 22)]⟩

theorem g037_ok : tagOKF CompactData.T CompactData.F g037 = true := by decide +kernel

def g038 : Tag := .inr ⟨(1 / 25 : ℚ), (17 / 400 : ℚ), (12 / 25 : ℚ), (13 / 25 : ℚ), (33 / 800 : ℚ), (1 / 2 : ℚ), (2, 18), (2, 22), (2, 20), (0, 14), [(2, 17), (2, 18), (2, 19)], [(2, 21), (2, 22), (2, 23)], [(2, 19), (2, 20), (2, 21)], [(0, 14), (0, 15)]⟩

theorem g038_ok : tagOKF CompactData.T CompactData.F g038 = true := by decide +kernel

def g039 : Tag := .inr ⟨(17 / 400 : ℚ), (9 / 200 : ℚ), (12 / 25 : ℚ), (13 / 25 : ℚ), (7 / 160 : ℚ), (1 / 2 : ℚ), (2, 18), (2, 22), (2, 20), (0, 16), [(2, 17), (2, 18), (2, 19)], [(2, 21), (2, 22), (2, 23)], [(2, 19), (2, 20), (2, 21)], [(0, 15), (0, 16)]⟩

theorem g039_ok : tagOKF CompactData.T CompactData.F g039 = true := by decide +kernel

end CKLaneC3.CompactBatch22


