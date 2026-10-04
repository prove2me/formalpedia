-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g83
-- name    : CK_CKLaneC2R_CompactCover_S01_g83
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T20:10:20.801055+00:00
-- url     : https://prove2.me/theorems/99a3f076-0d61-4dc8-8301-f8514726c175
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B030
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B047
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B056
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B058

namespace CKLaneC2R.CompactCover

theorem strip1_s122 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : ¬ (a ≤ ((23/80 : ℚ) : ℝ))) (h1106 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1156 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1172 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1180 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1181 : a ≤ ((47/160 : ℚ) : ℝ)
  · -- left
    by_cases h1182 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1183 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B030.c611_pos (not_le.mp h998).le h1181 (not_le.mp h1172).le h1183
      · -- right
        exact CKLaneC2R.Cells.S01.B030.c613_pos (not_le.mp h998).le h1181 (not_le.mp h1183).le h1182
    · -- right
      by_cases h1184 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B030.c619_pos (not_le.mp h998).le h1181 (not_le.mp h1182).le h1184
      · -- right
        exact CKLaneC2R.Cells.S01.B031.c621_pos (not_le.mp h998).le h1181 (not_le.mp h1184).le h1180
  · -- right
    by_cases h1185 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1186 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B030.c612_pos (not_le.mp h1181).le ha2 (not_le.mp h1172).le h1186
      · -- right
        exact CKLaneC2R.Cells.S01.B030.c614_pos (not_le.mp h1181).le ha2 (not_le.mp h1186).le h1185
    · -- right
      by_cases h1187 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B031.c620_pos (not_le.mp h1181).le ha2 (not_le.mp h1185).le h1187
      · -- right
        exact CKLaneC2R.Cells.S01.B031.c622_pos (not_le.mp h1181).le ha2 (not_le.mp h1187).le h1180

theorem strip1_s123 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : ¬ (a ≤ ((23/80 : ℚ) : ℝ))) (h1106 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1156 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1172 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1180 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1188 : z ≤ ((6211/6400 : ℚ) : ℝ)
  · -- left
    by_cases h1189 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1190 : a ≤ ((47/160 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B031.c628_pos (not_le.mp h998).le h1190 (not_le.mp h1180).le h1189
      · -- right
        exact CKLaneC2R.Cells.S01.B031.c629_pos (not_le.mp h1190).le ha2 (not_le.mp h1180).le h1189
    · -- right
      by_cases h1191 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B031.c630_pos (not_le.mp h998).le ha2 (not_le.mp h1189).le h1191
      · -- right
        exact CKLaneC2R.Cells.S01.B031.c631_pos (not_le.mp h998).le ha2 (not_le.mp h1191).le h1188
  · -- right
    by_cases h1192 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1193 : a ≤ ((47/160 : ℚ) : ℝ)
      · -- left
        by_cases h1194 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B047.c945_pos (not_le.mp h998).le h1193 (not_le.mp h1188).le h1194
        · -- right
          exact CKLaneC2R.Cells.S01.B047.c947_pos (not_le.mp h998).le h1193 (not_le.mp h1194).le h1192
      · -- right
        by_cases h1195 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B047.c946_pos (not_le.mp h1193).le ha2 (not_le.mp h1188).le h1195
        · -- right
          exact CKLaneC2R.Cells.S01.B047.c948_pos (not_le.mp h1193).le ha2 (not_le.mp h1195).le h1192
    · -- right
      by_cases h1196 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        by_cases h1197 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B047.c949_pos (not_le.mp h998).le ha2 (not_le.mp h1192).le h1197
        · -- right
          by_cases h1198 : a ≤ ((47/160 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B056.c1120_pos (not_le.mp h998).le h1198 (not_le.mp h1197).le h1196
          · -- right
            exact CKLaneC2R.Cells.S01.B056.c1121_pos (not_le.mp h1198).le ha2 (not_le.mp h1197).le h1196
      · -- right
        by_cases h1199 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          by_cases h1200 : a ≤ ((47/160 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B056.c1126_pos (not_le.mp h998).le h1200 (not_le.mp h1196).le h1199
          · -- right
            exact CKLaneC2R.Cells.S01.B056.c1127_pos (not_le.mp h1200).le ha2 (not_le.mp h1196).le h1199
        · -- right
          by_cases h1201 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B056.c1128_pos (not_le.mp h998).le ha2 (not_le.mp h1199).le h1201
          · -- right
            by_cases h1202 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S01.B058.c1170_pos (not_le.mp h998).le ha2 (not_le.mp h1201).le h1202
            · -- right
              exact CKLaneC2R.Cells.S01.B058.c1171_pos (not_le.mp h998).le ha2 (not_le.mp h1202).le hz2

end CKLaneC2R.CompactCover


