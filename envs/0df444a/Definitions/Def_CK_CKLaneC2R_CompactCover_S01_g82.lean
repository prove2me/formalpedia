-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g82
-- name    : CK_CKLaneC2R_CompactCover_S01_g82
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T11:55:11.615005+00:00
-- url     : https://prove2.me/theorems/8d00d2a7-6a54-4002-b354-dcf446161868
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B009

namespace CKLaneC2R.CompactCover

theorem strip1_s120 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : ¬ (a ≤ ((23/80 : ℚ) : ℝ))) (h1106 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1156 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1157 : a ≤ ((47/160 : ℚ) : ℝ)
  · -- left
    by_cases h1158 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h1159 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1160 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B005.c115_pos (not_le.mp h998).le h1157 (not_le.mp h1106).le h1160
        · -- right
          exact CKLaneC2R.Cells.S01.B005.c117_pos (not_le.mp h998).le h1157 (not_le.mp h1160).le h1159
      · -- right
        by_cases h1161 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B005.c119_pos (not_le.mp h998).le h1157 (not_le.mp h1159).le h1161
        · -- right
          exact CKLaneC2R.Cells.S01.B006.c121_pos (not_le.mp h998).le h1157 (not_le.mp h1161).le h1158
    · -- right
      by_cases h1162 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1163 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B007.c143_pos (not_le.mp h998).le h1157 (not_le.mp h1158).le h1163
        · -- right
          exact CKLaneC2R.Cells.S01.B007.c145_pos (not_le.mp h998).le h1157 (not_le.mp h1163).le h1162
      · -- right
        by_cases h1164 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B007.c151_pos (not_le.mp h998).le h1157 (not_le.mp h1162).le h1164
        · -- right
          exact CKLaneC2R.Cells.S01.B007.c153_pos (not_le.mp h998).le h1157 (not_le.mp h1164).le h1156
  · -- right
    by_cases h1165 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h1166 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1167 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B005.c116_pos (not_le.mp h1157).le ha2 (not_le.mp h1106).le h1167
        · -- right
          exact CKLaneC2R.Cells.S01.B005.c118_pos (not_le.mp h1157).le ha2 (not_le.mp h1167).le h1166
      · -- right
        by_cases h1168 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B006.c120_pos (not_le.mp h1157).le ha2 (not_le.mp h1166).le h1168
        · -- right
          exact CKLaneC2R.Cells.S01.B006.c122_pos (not_le.mp h1157).le ha2 (not_le.mp h1168).le h1165
    · -- right
      by_cases h1169 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1170 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B007.c144_pos (not_le.mp h1157).le ha2 (not_le.mp h1165).le h1170
        · -- right
          exact CKLaneC2R.Cells.S01.B007.c146_pos (not_le.mp h1157).le ha2 (not_le.mp h1170).le h1169
      · -- right
        by_cases h1171 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B007.c152_pos (not_le.mp h1157).le ha2 (not_le.mp h1169).le h1171
        · -- right
          exact CKLaneC2R.Cells.S01.B007.c154_pos (not_le.mp h1157).le ha2 (not_le.mp h1171).le h1156

theorem strip1_s121 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : ¬ (a ≤ ((11/40 : ℚ) : ℝ))) (h998 : ¬ (a ≤ ((23/80 : ℚ) : ℝ))) (h1106 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1156 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1172 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1173 : a ≤ ((47/160 : ℚ) : ℝ)
  · -- left
    by_cases h1174 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h1175 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B008.c170_pos (not_le.mp h998).le h1173 (not_le.mp h1156).le h1175
      · -- right
        exact CKLaneC2R.Cells.S01.B008.c172_pos (not_le.mp h998).le h1173 (not_le.mp h1175).le h1174
    · -- right
      by_cases h1176 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B008.c177_pos (not_le.mp h998).le h1173 (not_le.mp h1174).le h1176
      · -- right
        exact CKLaneC2R.Cells.S01.B008.c179_pos (not_le.mp h998).le h1173 (not_le.mp h1176).le h1172
  · -- right
    by_cases h1177 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h1178 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B008.c171_pos (not_le.mp h1173).le ha2 (not_le.mp h1156).le h1178
      · -- right
        exact CKLaneC2R.Cells.S01.B008.c173_pos (not_le.mp h1173).le ha2 (not_le.mp h1178).le h1177
    · -- right
      by_cases h1179 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B008.c178_pos (not_le.mp h1173).le ha2 (not_le.mp h1177).le h1179
      · -- right
        exact CKLaneC2R.Cells.S01.B009.c180_pos (not_le.mp h1173).le ha2 (not_le.mp h1179).le h1172

end CKLaneC2R.CompactCover


