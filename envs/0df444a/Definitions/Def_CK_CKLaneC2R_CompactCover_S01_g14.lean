-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g14
-- name    : CK_CKLaneC2R_CompactCover_S01_g14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T23:04:17.64303+00:00
-- url     : https://prove2.me/theorems/d10d572c-38f8-426e-abb7-ba06f1535dd4
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B021
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B022
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B025
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B043

namespace CKLaneC2R.CompactCover

theorem strip1_s017 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((33/160 : ℚ) : ℝ))) (h118 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h175 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h176 : a ≤ ((67/320 : ℚ) : ℝ)
  · -- left
    by_cases h177 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h178 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h179 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B020.c414_pos (not_le.mp h3).le h176 (not_le.mp h118).le h179
        · -- right
          exact CKLaneC2R.Cells.S01.B020.c416_pos (not_le.mp h3).le h176 (not_le.mp h179).le h178
      · -- right
        by_cases h180 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B021.c422_pos (not_le.mp h3).le h176 (not_le.mp h178).le h180
        · -- right
          exact CKLaneC2R.Cells.S01.B021.c424_pos (not_le.mp h3).le h176 (not_le.mp h180).le h177
    · -- right
      by_cases h181 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h182 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B022.c446_pos (not_le.mp h3).le h176 (not_le.mp h177).le h182
        · -- right
          exact CKLaneC2R.Cells.S01.B022.c448_pos (not_le.mp h3).le h176 (not_le.mp h182).le h181
      · -- right
        by_cases h183 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B022.c454_pos (not_le.mp h3).le h176 (not_le.mp h181).le h183
        · -- right
          exact CKLaneC2R.Cells.S01.B022.c456_pos (not_le.mp h3).le h176 (not_le.mp h183).le h175
  · -- right
    by_cases h184 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h185 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h186 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B020.c415_pos (not_le.mp h176).le h2 (not_le.mp h118).le h186
        · -- right
          exact CKLaneC2R.Cells.S01.B020.c417_pos (not_le.mp h176).le h2 (not_le.mp h186).le h185
      · -- right
        by_cases h187 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B021.c423_pos (not_le.mp h176).le h2 (not_le.mp h185).le h187
        · -- right
          exact CKLaneC2R.Cells.S01.B021.c425_pos (not_le.mp h176).le h2 (not_le.mp h187).le h184
    · -- right
      by_cases h188 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h189 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B022.c447_pos (not_le.mp h176).le h2 (not_le.mp h184).le h189
        · -- right
          exact CKLaneC2R.Cells.S01.B022.c449_pos (not_le.mp h176).le h2 (not_le.mp h189).le h188
      · -- right
        by_cases h190 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B022.c455_pos (not_le.mp h176).le h2 (not_le.mp h188).le h190
        · -- right
          exact CKLaneC2R.Cells.S01.B022.c457_pos (not_le.mp h176).le h2 (not_le.mp h190).le h175

theorem strip1_s018 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((33/160 : ℚ) : ℝ))) (h118 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h175 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h191 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h192 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h193 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h194 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B025.c500_pos (not_le.mp h3).le h2 (not_le.mp h175).le h194
      · -- right
        exact CKLaneC2R.Cells.S01.B025.c501_pos (not_le.mp h3).le h2 (not_le.mp h194).le h193
    · -- right
      by_cases h195 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B025.c504_pos (not_le.mp h3).le h2 (not_le.mp h193).le h195
      · -- right
        exact CKLaneC2R.Cells.S01.B025.c505_pos (not_le.mp h3).le h2 (not_le.mp h195).le h192
  · -- right
    by_cases h196 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h197 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B025.c516_pos (not_le.mp h3).le h2 (not_le.mp h192).le h197
      · -- right
        exact CKLaneC2R.Cells.S01.B025.c517_pos (not_le.mp h3).le h2 (not_le.mp h197).le h196
    · -- right
      by_cases h198 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B025.c518_pos (not_le.mp h3).le h2 (not_le.mp h196).le h198
      · -- right
        exact CKLaneC2R.Cells.S01.B025.c519_pos (not_le.mp h3).le h2 (not_le.mp h198).le h191

theorem strip1_s019 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((33/160 : ℚ) : ℝ))) (h118 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h175 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h191 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h199 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h200 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h201 : a ≤ ((67/320 : ℚ) : ℝ)
    · -- left
      by_cases h202 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B043.c860_pos (not_le.mp h3).le h201 (not_le.mp h191).le h202
      · -- right
        exact CKLaneC2R.Cells.S01.B043.c862_pos (not_le.mp h3).le h201 (not_le.mp h202).le h200
    · -- right
      by_cases h203 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B043.c861_pos (not_le.mp h201).le h2 (not_le.mp h191).le h203
      · -- right
        exact CKLaneC2R.Cells.S01.B043.c863_pos (not_le.mp h201).le h2 (not_le.mp h203).le h200
  · -- right
    by_cases h204 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      by_cases h205 : a ≤ ((67/320 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B043.c866_pos (not_le.mp h3).le h205 (not_le.mp h200).le h204
      · -- right
        exact CKLaneC2R.Cells.S01.B043.c867_pos (not_le.mp h205).le h2 (not_le.mp h200).le h204
    · -- right
      by_cases h206 : z ≤ ((23931/25600 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B043.c870_pos (not_le.mp h3).le h2 (not_le.mp h204).le h206
      · -- right
        exact CKLaneC2R.Cells.S01.B043.c871_pos (not_le.mp h3).le h2 (not_le.mp h206).le h199

end CKLaneC2R.CompactCover


