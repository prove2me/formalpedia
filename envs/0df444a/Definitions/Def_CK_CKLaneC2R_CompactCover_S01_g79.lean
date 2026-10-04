-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g79
-- name    : CK_CKLaneC2R_CompactCover_S01_g79
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T07:24:38.957064+00:00
-- url     : https://prove2.me/theorems/3cf71c3a-2e95-4595-9e2f-62e8080a9f69
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B019
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B003

namespace CKLaneC2R.CompactCover

theorem strip1_s115 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : ¬ (a ≤ ((23/80 : ℚ) : ℝ))) (h1106 : z ≤ ((217/400 : ℚ) : ℝ)) (h1107 : a ≤ ((47/160 : ℚ) : ℝ)) (h1108 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1109 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1120 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h1121 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1122 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B019.c388_pos (not_le.mp h998).le h1107 (not_le.mp h1109).le h1122
      · -- right
        exact CKLaneC2R.Cells.S01.B019.c389_pos (not_le.mp h998).le h1107 (not_le.mp h1122).le h1121
    · -- right
      by_cases h1123 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B019.c392_pos (not_le.mp h998).le h1107 (not_le.mp h1121).le h1123
      · -- right
        exact CKLaneC2R.Cells.S01.B019.c393_pos (not_le.mp h998).le h1107 (not_le.mp h1123).le h1120
  · -- right
    by_cases h1124 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B000.c8_pos (not_le.mp h998).le h1107 (not_le.mp h1120).le h1124
    · -- right
      exact CKLaneC2R.Cells.S01.B000.c10_pos (not_le.mp h998).le h1107 (not_le.mp h1124).le h1108

theorem strip1_s116 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : ¬ (a ≤ ((23/80 : ℚ) : ℝ))) (h1106 : z ≤ ((217/400 : ℚ) : ℝ)) (h1107 : a ≤ ((47/160 : ℚ) : ℝ)) (h1108 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1125 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h1126 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1127 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B002.c47_pos (not_le.mp h998).le h1107 (not_le.mp h1108).le h1127
      · -- right
        exact CKLaneC2R.Cells.S01.B002.c49_pos (not_le.mp h998).le h1107 (not_le.mp h1127).le h1126
    · -- right
      by_cases h1128 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B002.c51_pos (not_le.mp h998).le h1107 (not_le.mp h1126).le h1128
      · -- right
        exact CKLaneC2R.Cells.S01.B002.c53_pos (not_le.mp h998).le h1107 (not_le.mp h1128).le h1125
  · -- right
    by_cases h1129 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1130 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B003.c63_pos (not_le.mp h998).le h1107 (not_le.mp h1125).le h1130
      · -- right
        exact CKLaneC2R.Cells.S01.B003.c65_pos (not_le.mp h998).le h1107 (not_le.mp h1130).le h1129
    · -- right
      by_cases h1131 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B003.c67_pos (not_le.mp h998).le h1107 (not_le.mp h1129).le h1131
      · -- right
        exact CKLaneC2R.Cells.S01.B003.c69_pos (not_le.mp h998).le h1107 (not_le.mp h1131).le h1106

end CKLaneC2R.CompactCover


