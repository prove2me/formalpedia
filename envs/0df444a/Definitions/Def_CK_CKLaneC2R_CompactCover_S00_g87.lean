-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g87
-- name    : CK_CKLaneC2R_CompactCover_S00_g87
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T15:27:31.285501+00:00
-- url     : https://prove2.me/theorems/87604d27-fd22-4f95-a7c4-4655c6e24e94
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B024
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B025

namespace CKLaneC2R.CompactCover

theorem strip0_s107 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : ¬ (a ≤ ((29/160 : ℚ) : ℝ))) (h1078 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1164 : z ≤ ((3083/4000 : ℚ) : ℝ)) (h1165 : a ≤ ((59/320 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1166 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h1167 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1168 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B001.c24_pos (not_le.mp h892).le h1165 (not_le.mp h1078).le h1168
      · -- right
        exact CKLaneC2R.Cells.S00.B001.c26_pos (not_le.mp h892).le h1165 (not_le.mp h1168).le h1167
    · -- right
      by_cases h1169 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B001.c28_pos (not_le.mp h892).le h1165 (not_le.mp h1167).le h1169
      · -- right
        exact CKLaneC2R.Cells.S00.B001.c30_pos (not_le.mp h892).le h1165 (not_le.mp h1169).le h1166
  · -- right
    by_cases h1170 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1171 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B002.c48_pos (not_le.mp h892).le h1165 (not_le.mp h1166).le h1171
      · -- right
        by_cases h1172 : z ≤ ((44763/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B024.c497_pos (not_le.mp h892).le h1165 (not_le.mp h1171).le h1172
        · -- right
          exact CKLaneC2R.Cells.S00.B024.c498_pos (not_le.mp h892).le h1165 (not_le.mp h1172).le h1170
    · -- right
      by_cases h1173 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1174 : z ≤ ((46589/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B025.c507_pos (not_le.mp h892).le h1165 (not_le.mp h1170).le h1174
        · -- right
          exact CKLaneC2R.Cells.S00.B025.c508_pos (not_le.mp h892).le h1165 (not_le.mp h1174).le h1173
      · -- right
        by_cases h1175 : z ≤ ((9683/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B025.c511_pos (not_le.mp h892).le h1165 (not_le.mp h1173).le h1175
        · -- right
          exact CKLaneC2R.Cells.S00.B025.c512_pos (not_le.mp h892).le h1165 (not_le.mp h1175).le h1164

theorem strip0_s108 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : ¬ (a ≤ ((29/160 : ℚ) : ℝ))) (h1078 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1164 : z ≤ ((3083/4000 : ℚ) : ℝ)) (h1165 : ¬ (a ≤ ((59/320 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1176 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h1177 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1178 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B001.c25_pos (not_le.mp h1165).le h891 (not_le.mp h1078).le h1178
      · -- right
        exact CKLaneC2R.Cells.S00.B001.c27_pos (not_le.mp h1165).le h891 (not_le.mp h1178).le h1177
    · -- right
      by_cases h1179 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B001.c29_pos (not_le.mp h1165).le h891 (not_le.mp h1177).le h1179
      · -- right
        exact CKLaneC2R.Cells.S00.B001.c31_pos (not_le.mp h1165).le h891 (not_le.mp h1179).le h1176
  · -- right
    by_cases h1180 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1181 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B002.c49_pos (not_le.mp h1165).le h891 (not_le.mp h1176).le h1181
      · -- right
        exact CKLaneC2R.Cells.S00.B002.c50_pos (not_le.mp h1165).le h891 (not_le.mp h1181).le h1180
    · -- right
      by_cases h1182 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1183 : z ≤ ((46589/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B025.c509_pos (not_le.mp h1165).le h891 (not_le.mp h1180).le h1183
        · -- right
          exact CKLaneC2R.Cells.S00.B025.c510_pos (not_le.mp h1165).le h891 (not_le.mp h1183).le h1182
      · -- right
        by_cases h1184 : z ≤ ((9683/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B025.c513_pos (not_le.mp h1165).le h891 (not_le.mp h1182).le h1184
        · -- right
          exact CKLaneC2R.Cells.S00.B025.c514_pos (not_le.mp h1165).le h891 (not_le.mp h1184).le h1164

end CKLaneC2R.CompactCover


