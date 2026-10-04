-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g10
-- name    : CK_CKLaneC2R_CompactCover_S03_g10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T20:15:41.265294+00:00
-- url     : https://prove2.me/theorems/aedfe843-2cdb-4d84-a7f7-42b4669b5d03
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S03 (proof part of strip3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S03 (proof part of strip3).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B001

namespace CKLaneC2R.CompactCover

theorem strip3_s015 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((11/20 : ℚ) : ℝ))) (h119 : ¬ (a ≤ ((23/40 : ℚ) : ℝ))) (h172 : z ≤ ((217/400 : ℚ) : ℝ)) (h173 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h174 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h175 : a ≤ ((47/80 : ℚ) : ℝ)
    · -- left
      by_cases h176 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h177 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          by_cases h178 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B016.c322_pos (not_le.mp h119).le h175 hz1 h178
          · -- right
            exact CKLaneC2R.Cells.S03.B016.c324_pos (not_le.mp h119).le h175 (not_le.mp h178).le h177
        · -- right
          exact CKLaneC2R.Cells.S03.B009.c182_pos (not_le.mp h119).le h175 (not_le.mp h177).le h176
      · -- right
        by_cases h179 : z ≤ ((5491/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B009.c188_pos (not_le.mp h119).le h175 (not_le.mp h176).le h179
        · -- right
          exact CKLaneC2R.Cells.S03.B009.c190_pos (not_le.mp h119).le h175 (not_le.mp h179).le h174
    · -- right
      by_cases h180 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h181 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          by_cases h182 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B016.c323_pos (not_le.mp h175).le h0 hz1 h182
          · -- right
            exact CKLaneC2R.Cells.S03.B016.c325_pos (not_le.mp h175).le h0 (not_le.mp h182).le h181
        · -- right
          exact CKLaneC2R.Cells.S03.B009.c183_pos (not_le.mp h175).le h0 (not_le.mp h181).le h180
      · -- right
        by_cases h183 : z ≤ ((5491/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B009.c189_pos (not_le.mp h175).le h0 (not_le.mp h180).le h183
        · -- right
          exact CKLaneC2R.Cells.S03.B009.c191_pos (not_le.mp h175).le h0 (not_le.mp h183).le h174
  · -- right
    by_cases h184 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h185 : a ≤ ((47/80 : ℚ) : ℝ)
      · -- left
        by_cases h186 : z ≤ ((7317/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B010.c212_pos (not_le.mp h119).le h185 (not_le.mp h174).le h186
        · -- right
          exact CKLaneC2R.Cells.S03.B010.c214_pos (not_le.mp h119).le h185 (not_le.mp h186).le h184
      · -- right
        by_cases h187 : z ≤ ((7317/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B010.c213_pos (not_le.mp h185).le h0 (not_le.mp h174).le h187
        · -- right
          exact CKLaneC2R.Cells.S03.B010.c215_pos (not_le.mp h185).le h0 (not_le.mp h187).le h184
    · -- right
      by_cases h188 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B000.c1_pos (not_le.mp h119).le h0 (not_le.mp h184).le h188
      · -- right
        exact CKLaneC2R.Cells.S03.B000.c2_pos (not_le.mp h119).le h0 (not_le.mp h188).le h173

theorem strip3_s016 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((11/20 : ℚ) : ℝ))) (h119 : ¬ (a ≤ ((23/40 : ℚ) : ℝ))) (h172 : z ≤ ((217/400 : ℚ) : ℝ)) (h173 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h189 : a ≤ ((47/80 : ℚ) : ℝ)
  · -- left
    by_cases h190 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h191 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B001.c22_pos (not_le.mp h119).le h189 (not_le.mp h173).le h191
      · -- right
        exact CKLaneC2R.Cells.S03.B001.c24_pos (not_le.mp h119).le h189 (not_le.mp h191).le h190
    · -- right
      by_cases h192 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B001.c30_pos (not_le.mp h119).le h189 (not_le.mp h190).le h192
      · -- right
        exact CKLaneC2R.Cells.S03.B001.c32_pos (not_le.mp h119).le h189 (not_le.mp h192).le h172
  · -- right
    by_cases h193 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h194 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B001.c23_pos (not_le.mp h189).le h0 (not_le.mp h173).le h194
      · -- right
        exact CKLaneC2R.Cells.S03.B001.c25_pos (not_le.mp h189).le h0 (not_le.mp h194).le h193
    · -- right
      by_cases h195 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B001.c31_pos (not_le.mp h189).le h0 (not_le.mp h193).le h195
      · -- right
        exact CKLaneC2R.Cells.S03.B001.c33_pos (not_le.mp h189).le h0 (not_le.mp h195).le h172

end CKLaneC2R.CompactCover


