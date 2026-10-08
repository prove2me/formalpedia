-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactBatch47_q02
-- name    : CK_CKLaneC3_CompactBatch47_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T12:10:15.842056+00:00
-- url     : https://prove2.me/theorems/e08417f8-1610-4237-9948-4e92414822c7
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactBatch47 (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactBatch47 (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactBatch47 (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactBatch47 (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactBatch47 (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneC3_CompactBatch47_q01

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace CKLaneC3.CompactBatch47
open CKLaneC3.CompactCover CKLaneC3.CompactCoverF
def g115 : Tag := .inr ⟨(11 / 25 : ℚ), (12 / 25 : ℚ), (899 / 100 : ℚ), (471 / 50 : ℚ), (23 / 50 : ℚ), (1841 / 200 : ℚ), (20, 21), (22, 19), (21, 20), (2, 16), [(20, 10), (20, 11), (20, 12), (20, 13), (20, 14), (20, 15), (20, 16), (20, 17), (20, 18), (20, 19), (20, 20), (20, 21), (20, 22), (20, 23), (21, 0), (21, 1), (21, 2), (21, 3), (21, 4), (21, 5), (21, 6), (21, 7), (21, 8)], [(22, 6), (22, 7), (22, 8), (22, 9), (22, 10), (22, 11), (22, 12), (22, 13), (22, 14), (22, 15), (22, 16), (22, 17), (22, 18), (22, 19), (22, 20), (22, 21), (22, 22), (22, 23), (23, 0), (23, 1), (23, 2), (23, 3), (23, 4), (23, 5), (23, 6), (23, 7), (23, 8)], [(21, 8), (21, 9), (21, 10), (21, 11), (21, 12), (21, 13), (21, 14), (21, 15), (21, 16), (21, 17), (21, 18), (21, 19), (21, 20), (21, 21), (21, 22), (21, 23), (22, 0), (22, 1), (22, 2), (22, 3), (22, 4), (22, 5), (22, 6), (22, 7), (22, 8)], [(2, 15), (2, 16), (2, 17)]⟩

theorem g115_ok : tagOKF CompactData.T CompactData.F g115 = true := by decide +kernel

def g116 : Tag := .inr ⟨(2 / 5 : ℚ), (21 / 50 : ℚ), (471 / 50 : ℚ), (197 / 20 : ℚ), (41 / 100 : ℚ), (1927 / 200 : ℚ), (21, 19), (23, 12), (22, 15), (2, 13), [(21, 8), (21, 9), (21, 10), (21, 11), (21, 12), (21, 13), (21, 14), (21, 15), (21, 16), (21, 17), (21, 18), (21, 19), (21, 20), (21, 21), (21, 22), (21, 23), (22, 0), (22, 1), (22, 2), (22, 3), (22, 4), (22, 5)], [(23, 0), (23, 1), (23, 2), (23, 3), (23, 4), (23, 5), (23, 6), (23, 7), (23, 8), (23, 9), (23, 10), (23, 11), (23, 12), (23, 13), (23, 14), (23, 15), (23, 16), (23, 17), (23, 18), (23, 19), (23, 20), (23, 21), (23, 22), (23, 23)], [(22, 4), (22, 5), (22, 6), (22, 7), (22, 8), (22, 9), (22, 10), (22, 11), (22, 12), (22, 13), (22, 14), (22, 15), (22, 16), (22, 17), (22, 18), (22, 19), (22, 20), (22, 21), (22, 22), (22, 23), (23, 0), (23, 1), (23, 2)], [(2, 13), (2, 14)]⟩

theorem g116_ok : tagOKF CompactData.T CompactData.F g116 = true := by decide +kernel

def g117 : Tag := .inr ⟨(2 / 5 : ℚ), (21 / 50 : ℚ), (197 / 20 : ℚ), (257 / 25 : ℚ), (41 / 100 : ℚ), (2013 / 200 : ℚ), (22, 16), (24, 9), (23, 13), (2, 13), [(22, 5), (22, 6), (22, 7), (22, 8), (22, 9), (22, 10), (22, 11), (22, 12), (22, 13), (22, 14), (22, 15), (22, 16), (22, 17), (22, 18), (22, 19), (22, 20), (22, 21), (22, 22), (22, 23), (23, 0), (23, 1), (23, 2), (23, 3)], [(23, 21), (23, 22), (23, 23), (24, 0), (24, 1), (24, 2), (24, 3), (24, 4), (24, 5), (24, 6), (24, 7), (24, 8), (24, 9), (24, 10), (24, 11), (24, 12), (24, 13), (24, 14), (24, 15), (24, 16), (24, 17), (24, 18), (24, 19), (24, 20), (24, 21)], [(23, 1), (23, 2), (23, 3), (23, 4), (23, 5), (23, 6), (23, 7), (23, 8), (23, 9), (23, 10), (23, 11), (23, 12), (23, 13), (23, 14), (23, 15), (23, 16), (23, 17), (23, 18), (23, 19), (23, 20), (23, 21), (23, 22), (23, 23), (24, 0)], [(2, 13), (2, 14)]⟩

theorem g117_ok : tagOKF CompactData.T CompactData.F g117 = true := by decide +kernel

def g118 : Tag := .inr ⟨(21 / 50 : ℚ), (11 / 25 : ℚ), (471 / 50 : ℚ), (197 / 20 : ℚ), (43 / 100 : ℚ), (1927 / 200 : ℚ), (21, 19), (23, 14), (22, 16), (2, 14), [(21, 8), (21, 9), (21, 10), (21, 11), (21, 12), (21, 13), (21, 14), (21, 15), (21, 16), (21, 17), (21, 18), (21, 19), (21, 20), (21, 21), (21, 22), (21, 23), (22, 0), (22, 1), (22, 2), (22, 3), (22, 4), (22, 5)], [(23, 2), (23, 3), (23, 4), (23, 5), (23, 6), (23, 7), (23, 8), (23, 9), (23, 10), (23, 11), (23, 12), (23, 13), (23, 14), (23, 15), (23, 16), (23, 17), (23, 18), (23, 19), (23, 20), (23, 21), (23, 22), (23, 23), (24, 0), (24, 1)], [(22, 5), (22, 6), (22, 7), (22, 8), (22, 9), (22, 10), (22, 11), (22, 12), (22, 13), (22, 14), (22, 15), (22, 16), (22, 17), (22, 18), (22, 19), (22, 20), (22, 21), (22, 22), (22, 23), (23, 0), (23, 1), (23, 2), (23, 3)], [(2, 14), (2, 15)]⟩

theorem g118_ok : tagOKF CompactData.T CompactData.F g118 = true := by decide +kernel

def g119 : Tag := .inr ⟨(21 / 50 : ℚ), (11 / 25 : ℚ), (197 / 20 : ℚ), (257 / 25 : ℚ), (43 / 100 : ℚ), (2013 / 200 : ℚ), (22, 16), (24, 11), (23, 14), (2, 14), [(22, 5), (22, 6), (22, 7), (22, 8), (22, 9), (22, 10), (22, 11), (22, 12), (22, 13), (22, 14), (22, 15), (22, 16), (22, 17), (22, 18), (22, 19), (22, 20), (22, 21), (22, 22), (22, 23), (23, 0), (23, 1), (23, 2), (23, 3)], [(23, 23), (24, 0), (24, 1), (24, 2), (24, 3), (24, 4), (24, 5), (24, 6), (24, 7), (24, 8), (24, 9), (24, 10), (24, 11), (24, 12), (24, 13), (24, 14), (24, 15), (24, 16), (24, 17), (24, 18), (24, 19), (24, 20), (24, 21), (24, 22), (24, 23)], [(23, 2), (23, 3), (23, 4), (23, 5), (23, 6), (23, 7), (23, 8), (23, 9), (23, 10), (23, 11), (23, 12), (23, 13), (23, 14), (23, 15), (23, 16), (23, 17), (23, 18), (23, 19), (23, 20), (23, 21), (23, 22), (23, 23), (24, 0), (24, 1)], [(2, 14), (2, 15)]⟩

theorem g119_ok : tagOKF CompactData.T CompactData.F g119 = true := by decide +kernel

def tags : List Tag := [g000, g001, g002, g003, g004, g005, g006, g007, g008, g009, g010, g011, g012, g013, g014, g015, g016, g017, g018, g019, g020, g021, g022, g023, g024, g025, g026, g027, g028, g029, g030, g031, g032, g033, g034, g035, g036, g037, g038, g039, g040, g041, g042, g043, g044, g045, g046, g047, g048, g049, g050, g051, g052, g053, g054, g055, g056, g057, g058, g059, g060, g061, g062, g063, g064, g065, g066, g067, g068, g069, g070, g071, g072, g073, g074, g075, g076, g077, g078, g079, g080, g081, g082, g083, g084, g085, g086, g087, g088, g089, g090, g091, g092, g093, g094, g095, g096, g097, g098, g099, g100, g101, g102, g103, g104, g105, g106, g107, g108, g109, g110, g111, g112, g113, g114, g115, g116, g117, g118, g119]

end CKLaneC3.CompactBatch47


