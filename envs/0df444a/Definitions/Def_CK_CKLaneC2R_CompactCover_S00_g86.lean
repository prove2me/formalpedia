-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g86
-- name    : CK_CKLaneC2R_CompactCover_S00_g86
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T11:07:16.639265+00:00
-- url     : https://prove2.me/theorems/e1a8fd70-8e4b-46e2-8381-53270005e7e0
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S00 (proof part of strip0) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S00 (proof part of strip0).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B000

namespace CKLaneC2R.CompactCover

theorem strip0_s106 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : ¬ (a ≤ ((29/160 : ℚ) : ℝ))) (h1078 : z ≤ ((217/400 : ℚ) : ℝ)) (h1079 : ¬ (a ≤ ((59/320 : ℚ) : ℝ))) (h1124 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1152 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h1153 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1154 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1155 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B013.c275_pos (not_le.mp h1079).le h891 (not_le.mp h1124).le h1155
        · -- right
          exact CKLaneC2R.Cells.S00.B013.c276_pos (not_le.mp h1079).le h891 (not_le.mp h1155).le h1154
      · -- right
        by_cases h1156 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B013.c279_pos (not_le.mp h1079).le h891 (not_le.mp h1154).le h1156
        · -- right
          exact CKLaneC2R.Cells.S00.B014.c280_pos (not_le.mp h1079).le h891 (not_le.mp h1156).le h1153
    · -- right
      by_cases h1157 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        by_cases h1158 : z ≤ ((24677/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B014.c291_pos (not_le.mp h1079).le h891 (not_le.mp h1153).le h1158
        · -- right
          exact CKLaneC2R.Cells.S00.B014.c292_pos (not_le.mp h1079).le h891 (not_le.mp h1158).le h1157
      · -- right
        by_cases h1159 : z ≤ ((26503/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B014.c295_pos (not_le.mp h1079).le h891 (not_le.mp h1157).le h1159
        · -- right
          exact CKLaneC2R.Cells.S00.B014.c296_pos (not_le.mp h1079).le h891 (not_le.mp h1159).le h1152
  · -- right
    by_cases h1160 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1161 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1162 : z ≤ ((28329/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B016.c331_pos (not_le.mp h1079).le h891 (not_le.mp h1152).le h1162
        · -- right
          exact CKLaneC2R.Cells.S00.B016.c332_pos (not_le.mp h1079).le h891 (not_le.mp h1162).le h1161
      · -- right
        exact CKLaneC2R.Cells.S00.B000.c4_pos (not_le.mp h1079).le h891 (not_le.mp h1161).le h1160
    · -- right
      by_cases h1163 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B000.c5_pos (not_le.mp h1079).le h891 (not_le.mp h1160).le h1163
      · -- right
        exact CKLaneC2R.Cells.S00.B000.c7_pos (not_le.mp h1079).le h891 (not_le.mp h1163).le h1078

end CKLaneC2R.CompactCover


