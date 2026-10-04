-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g11
-- name    : CK_CKLaneC2R_CompactCover_S02_g11
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T15:24:47.605975+00:00
-- url     : https://prove2.me/theorems/81c427c2-df22-4921-9be3-32eb7846198a
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S02 (proof part of strip2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S02 (proof part of strip2).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B038
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B030
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B015

namespace CKLaneC2R.CompactCover

theorem strip2_s016 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((13/40 : ℚ) : ℝ))) (h179 : a ≤ ((27/80 : ℚ) : ℝ)) (h180 : z ≤ ((217/400 : ℚ) : ℝ)) (h181 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h182 : a ≤ ((53/160 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h183 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h184 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h185 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h186 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          by_cases h187 : z ≤ ((11921/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B038.c771_pos (not_le.mp h2).le h182 hz1 h187
          · -- right
            exact CKLaneC2R.Cells.S02.B038.c772_pos (not_le.mp h2).le h182 (not_le.mp h187).le h186
        · -- right
          exact CKLaneC2R.Cells.S02.B030.c603_pos (not_le.mp h2).le h182 (not_le.mp h186).le h185
      · -- right
        by_cases h188 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B030.c607_pos (not_le.mp h2).le h182 (not_le.mp h185).le h188
        · -- right
          exact CKLaneC2R.Cells.S02.B030.c609_pos (not_le.mp h2).le h182 (not_le.mp h188).le h184
    · -- right
      by_cases h189 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h190 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B030.c615_pos (not_le.mp h2).le h182 (not_le.mp h184).le h190
        · -- right
          exact CKLaneC2R.Cells.S02.B030.c616_pos (not_le.mp h2).le h182 (not_le.mp h190).le h189
      · -- right
        by_cases h191 : z ≤ ((2379/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B030.c619_pos (not_le.mp h2).le h182 (not_le.mp h189).le h191
        · -- right
          exact CKLaneC2R.Cells.S02.B031.c620_pos (not_le.mp h2).le h182 (not_le.mp h191).le h183
  · -- right
    by_cases h192 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h193 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B015.c304_pos (not_le.mp h2).le h182 (not_le.mp h183).le h193
      · -- right
        exact CKLaneC2R.Cells.S02.B015.c306_pos (not_le.mp h2).le h182 (not_le.mp h193).le h192
    · -- right
      by_cases h194 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B015.c312_pos (not_le.mp h2).le h182 (not_le.mp h192).le h194
      · -- right
        exact CKLaneC2R.Cells.S02.B015.c314_pos (not_le.mp h2).le h182 (not_le.mp h194).le h181

theorem strip2_s017 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((13/40 : ℚ) : ℝ))) (h179 : a ≤ ((27/80 : ℚ) : ℝ)) (h180 : z ≤ ((217/400 : ℚ) : ℝ)) (h181 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h182 : ¬ (a ≤ ((53/160 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h195 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h196 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h197 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h198 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          by_cases h199 : z ≤ ((11921/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B038.c773_pos (not_le.mp h182).le h179 hz1 h199
          · -- right
            exact CKLaneC2R.Cells.S02.B038.c774_pos (not_le.mp h182).le h179 (not_le.mp h199).le h198
        · -- right
          exact CKLaneC2R.Cells.S02.B030.c604_pos (not_le.mp h182).le h179 (not_le.mp h198).le h197
      · -- right
        by_cases h200 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B030.c608_pos (not_le.mp h182).le h179 (not_le.mp h197).le h200
        · -- right
          exact CKLaneC2R.Cells.S02.B030.c610_pos (not_le.mp h182).le h179 (not_le.mp h200).le h196
    · -- right
      by_cases h201 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h202 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B030.c617_pos (not_le.mp h182).le h179 (not_le.mp h196).le h202
        · -- right
          exact CKLaneC2R.Cells.S02.B030.c618_pos (not_le.mp h182).le h179 (not_le.mp h202).le h201
      · -- right
        by_cases h203 : z ≤ ((2379/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B031.c621_pos (not_le.mp h182).le h179 (not_le.mp h201).le h203
        · -- right
          exact CKLaneC2R.Cells.S02.B031.c622_pos (not_le.mp h182).le h179 (not_le.mp h203).le h195
  · -- right
    by_cases h204 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h205 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B015.c305_pos (not_le.mp h182).le h179 (not_le.mp h195).le h205
      · -- right
        exact CKLaneC2R.Cells.S02.B015.c307_pos (not_le.mp h182).le h179 (not_le.mp h205).le h204
    · -- right
      by_cases h206 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B015.c313_pos (not_le.mp h182).le h179 (not_le.mp h204).le h206
      · -- right
        exact CKLaneC2R.Cells.S02.B015.c315_pos (not_le.mp h182).le h179 (not_le.mp h206).le h181

end CKLaneC2R.CompactCover


