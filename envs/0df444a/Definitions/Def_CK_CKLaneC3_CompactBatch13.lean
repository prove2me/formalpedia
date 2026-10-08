-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch13
-- name    : CK_CKLaneC3_CompactBatch13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T05:48:18.926145+00:00
-- url     : https://prove2.me/theorems/e638a7ee-f1a5-4bc4-9ed8-251836773074
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch13` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch13` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch13` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch13 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch13.lean)

import Definitions.Def_CK_CKLaneC3_CompactBatch13_part00

/-! Lane C3 compact cell batch (generated; memoised chains over the data tables). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace CKLaneC3.CompactBatch13
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF

theorem g107_ok : tagOKF CompactData.T CompactData.F g107 = true := by decide +kernel

def g108 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (299 / 50 : ℚ), (1239 / 200 : ℚ), (49 / 1600 : ℚ), (487 / 80 : ℚ), (14, 9), (14, 12), (14, 11), (0, 8), [(14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15)], [(14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15), (14, 16), (14, 17), (14, 18)], [(14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15), (14, 16)], [(0, 8), (0, 9)]⟩

theorem g108_ok : tagOKF CompactData.T CompactData.F g108 = true := by decide +kernel

def g109 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (1239 / 200 : ℚ), (641 / 100 : ℚ), (49 / 1600 : ℚ), (2521 / 400 : ℚ), (14, 20), (14, 23), (14, 22), (0, 8), [(14, 15), (14, 16), (14, 17), (14, 18), (14, 19), (14, 20), (14, 21), (14, 22), (14, 23), (15, 0), (15, 1)], [(14, 18), (14, 19), (14, 20), (14, 21), (14, 22), (14, 23), (15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5)], [(14, 16), (14, 17), (14, 18), (14, 19), (14, 20), (14, 21), (14, 22), (14, 23), (15, 0), (15, 1), (15, 2), (15, 3)], [(0, 8), (0, 9)]⟩

theorem g109_ok : tagOKF CompactData.T CompactData.F g109 = true := by decide +kernel

def g110 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (299 / 50 : ℚ), (1239 / 200 : ℚ), (51 / 1600 : ℚ), (487 / 80 : ℚ), (14, 9), (14, 12), (14, 11), (0, 9), [(14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15)], [(14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15), (14, 16), (14, 17), (14, 18)], [(14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15), (14, 16)], [(0, 9)]⟩

theorem g110_ok : tagOKF CompactData.T CompactData.F g110 = true := by decide +kernel

def g111 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (1239 / 200 : ℚ), (641 / 100 : ℚ), (51 / 1600 : ℚ), (2521 / 400 : ℚ), (14, 20), (14, 23), (14, 22), (0, 9), [(14, 15), (14, 16), (14, 17), (14, 18), (14, 19), (14, 20), (14, 21), (14, 22), (14, 23), (15, 0), (15, 1)], [(14, 18), (14, 19), (14, 20), (14, 21), (14, 22), (14, 23), (15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5)], [(14, 16), (14, 17), (14, 18), (14, 19), (14, 20), (14, 21), (14, 22), (14, 23), (15, 0), (15, 1), (15, 2), (15, 3)], [(0, 9)]⟩

theorem g111_ok : tagOKF CompactData.T CompactData.F g111 = true := by decide +kernel

def g112 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (641 / 100 : ℚ), (53 / 8 : ℚ), (49 / 1600 : ℚ), (2607 / 400 : ℚ), (15, 7), (15, 10), (15, 8), (0, 8), [(15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (15, 12)], [(15, 4), (15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (15, 12), (15, 13), (15, 14), (15, 15)], [(15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (15, 12), (15, 13), (15, 14)], [(0, 8), (0, 9)]⟩

theorem g112_ok : tagOKF CompactData.T CompactData.F g112 = true := by decide +kernel

def g113 : Tag := .inr ⟨(3 / 100 : ℚ), (1 / 32 : ℚ), (53 / 8 : ℚ), (171 / 25 : ℚ), (49 / 1600 : ℚ), (2693 / 400 : ℚ), (15, 18), (15, 21), (15, 19), (0, 8), [(15, 12), (15, 13), (15, 14), (15, 15), (15, 16), (15, 17), (15, 18), (15, 19), (15, 20), (15, 21), (15, 22), (15, 23)], [(15, 15), (15, 16), (15, 17), (15, 18), (15, 19), (15, 20), (15, 21), (15, 22), (15, 23), (16, 0), (16, 1), (16, 2)], [(15, 14), (15, 15), (15, 16), (15, 17), (15, 18), (15, 19), (15, 20), (15, 21), (15, 22), (15, 23), (16, 0)], [(0, 8), (0, 9)]⟩

theorem g113_ok : tagOKF CompactData.T CompactData.F g113 = true := by decide +kernel

def g114 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (641 / 100 : ℚ), (53 / 8 : ℚ), (51 / 1600 : ℚ), (2607 / 400 : ℚ), (15, 7), (15, 10), (15, 8), (0, 9), [(15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (15, 12)], [(15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (15, 12), (15, 13), (15, 14), (15, 15)], [(15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (15, 8), (15, 9), (15, 10), (15, 11), (15, 12), (15, 13), (15, 14)], [(0, 9)]⟩

theorem g114_ok : tagOKF CompactData.T CompactData.F g114 = true := by decide +kernel

def g115 : Tag := .inr ⟨(1 / 32 : ℚ), (13 / 400 : ℚ), (53 / 8 : ℚ), (171 / 25 : ℚ), (51 / 1600 : ℚ), (2693 / 400 : ℚ), (15, 18), (15, 21), (15, 19), (0, 9), [(15, 12), (15, 13), (15, 14), (15, 15), (15, 16), (15, 17), (15, 18), (15, 19), (15, 20), (15, 21), (15, 22), (15, 23)], [(15, 15), (15, 16), (15, 17), (15, 18), (15, 19), (15, 20), (15, 21), (15, 22), (15, 23), (16, 0), (16, 1), (16, 2)], [(15, 14), (15, 15), (15, 16), (15, 17), (15, 18), (15, 19), (15, 20), (15, 21), (15, 22), (15, 23), (16, 0), (16, 1)], [(0, 9)]⟩

theorem g115_ok : tagOKF CompactData.T CompactData.F g115 = true := by decide +kernel

def g116 : Tag := .inr ⟨(13 / 400 : ℚ), (27 / 800 : ℚ), (299 / 50 : ℚ), (1239 / 200 : ℚ), (53 / 1600 : ℚ), (487 / 80 : ℚ), (14, 9), (14, 13), (14, 11), (0, 10), [(14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15)], [(14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15), (14, 16), (14, 17), (14, 18)], [(14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15), (14, 16)], [(0, 9), (0, 10)]⟩

theorem g116_ok : tagOKF CompactData.T CompactData.F g116 = true := by decide +kernel

def g117 : Tag := .inr ⟨(13 / 400 : ℚ), (27 / 800 : ℚ), (1239 / 200 : ℚ), (641 / 100 : ℚ), (53 / 1600 : ℚ), (2521 / 400 : ℚ), (14, 20), (14, 23), (14, 22), (0, 10), [(14, 15), (14, 16), (14, 17), (14, 18), (14, 19), (14, 20), (14, 21), (14, 22), (14, 23), (15, 0), (15, 1)], [(14, 18), (14, 19), (14, 20), (14, 21), (14, 22), (14, 23), (15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5)], [(14, 16), (14, 17), (14, 18), (14, 19), (14, 20), (14, 21), (14, 22), (14, 23), (15, 0), (15, 1), (15, 2), (15, 3)], [(0, 9), (0, 10)]⟩

theorem g117_ok : tagOKF CompactData.T CompactData.F g117 = true := by decide +kernel

def g118 : Tag := .inr ⟨(27 / 800 : ℚ), (7 / 200 : ℚ), (299 / 50 : ℚ), (1239 / 200 : ℚ), (11 / 320 : ℚ), (487 / 80 : ℚ), (14, 9), (14, 13), (14, 11), (0, 11), [(14, 4), (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15)], [(14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15), (14, 16), (14, 17), (14, 18)], [(14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (14, 11), (14, 12), (14, 13), (14, 14), (14, 15), (14, 16)], [(0, 10), (0, 11)]⟩

theorem g118_ok : tagOKF CompactData.T CompactData.F g118 = true := by decide +kernel

def g119 : Tag := .inr ⟨(27 / 800 : ℚ), (7 / 200 : ℚ), (1239 / 200 : ℚ), (641 / 100 : ℚ), (11 / 320 : ℚ), (2521 / 400 : ℚ), (14, 20), (14, 23), (14, 22), (0, 11), [(14, 15), (14, 16), (14, 17), (14, 18), (14, 19), (14, 20), (14, 21), (14, 22), (14, 23), (15, 0), (15, 1)], [(14, 18), (14, 19), (14, 20), (14, 21), (14, 22), (14, 23), (15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5)], [(14, 16), (14, 17), (14, 18), (14, 19), (14, 20), (14, 21), (14, 22), (14, 23), (15, 0), (15, 1), (15, 2), (15, 3)], [(0, 10), (0, 11)]⟩

theorem g119_ok : tagOKF CompactData.T CompactData.F g119 = true := by decide +kernel

def tags : List Tag := [g000, g001, g002, g003, g004, g005, g006, g007, g008, g009, g010, g011, g012, g013, g014, g015, g016, g017, g018, g019, g020, g021, g022, g023, g024, g025, g026, g027, g028, g029, g030, g031, g032, g033, g034, g035, g036, g037, g038, g039, g040, g041, g042, g043, g044, g045, g046, g047, g048, g049, g050, g051, g052, g053, g054, g055, g056, g057, g058, g059, g060, g061, g062, g063, g064, g065, g066, g067, g068, g069, g070, g071, g072, g073, g074, g075, g076, g077, g078, g079, g080, g081, g082, g083, g084, g085, g086, g087, g088, g089, g090, g091, g092, g093, g094, g095, g096, g097, g098, g099, g100, g101, g102, g103, g104, g105, g106, g107, g108, g109, g110, g111, g112, g113, g114, g115, g116, g117, g118, g119]

theorem tags_ok : tags.all (tagOKF CompactData.T CompactData.F) = true := by
  simp only [tags, List.all_cons, List.all_nil, g000_ok, g001_ok, g002_ok, g003_ok, g004_ok, g005_ok, g006_ok, g007_ok, g008_ok, g009_ok, g010_ok, g011_ok, g012_ok, g013_ok, g014_ok, g015_ok, g016_ok, g017_ok, g018_ok, g019_ok, g020_ok, g021_ok, g022_ok, g023_ok, g024_ok, g025_ok, g026_ok, g027_ok, g028_ok, g029_ok, g030_ok, g031_ok, g032_ok, g033_ok, g034_ok, g035_ok, g036_ok, g037_ok, g038_ok, g039_ok, g040_ok, g041_ok, g042_ok, g043_ok, g044_ok, g045_ok, g046_ok, g047_ok, g048_ok, g049_ok, g050_ok, g051_ok, g052_ok, g053_ok, g054_ok, g055_ok, g056_ok, g057_ok, g058_ok, g059_ok, g060_ok, g061_ok, g062_ok, g063_ok, g064_ok, g065_ok, g066_ok, g067_ok, g068_ok, g069_ok, g070_ok, g071_ok, g072_ok, g073_ok, g074_ok, g075_ok, g076_ok, g077_ok, g078_ok, g079_ok, g080_ok, g081_ok, g082_ok, g083_ok, g084_ok, g085_ok, g086_ok, g087_ok, g088_ok, g089_ok, g090_ok, g091_ok, g092_ok, g093_ok, g094_ok, g095_ok, g096_ok, g097_ok, g098_ok, g099_ok, g100_ok, g101_ok, g102_ok, g103_ok, g104_ok, g105_ok, g106_ok, g107_ok, g108_ok, g109_ok, g110_ok, g111_ok, g112_ok, g113_ok, g114_ok, g115_ok, g116_ok, g117_ok, g118_ok, g119_ok, Bool.and_self]

end CKLaneC3.CompactBatch13


