-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g12
-- name    : CK_CKLaneC2R_CompactCover_S05_g12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T11:47:19.865027+00:00
-- url     : https://prove2.me/theorems/9d9d4697-f83d-48bf-903a-716c7073754c
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S05 (proof part of strip5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S05 (proof part of strip5).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B008

namespace CKLaneC2R.CompactCover

theorem strip5_s018 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : a ≤ ((1539/1600 : ℚ) : ℝ)) (h149 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h150 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h151 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h152 : a ≤ ((15291/16000 : ℚ) : ℝ)
      · -- left
        by_cases h153 : z ≤ ((2289/16000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B002.c56_pos (not_le.mp h0).le h152 hz1 h153
        · -- right
          exact CKLaneC2R.Cells.S05.B002.c58_pos (not_le.mp h0).le h152 (not_le.mp h153).le h151
      · -- right
        by_cases h154 : z ≤ ((2289/16000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B002.c57_pos (not_le.mp h152).le h148 hz1 h154
        · -- right
          exact CKLaneC2R.Cells.S05.B002.c59_pos (not_le.mp h152).le h148 (not_le.mp h154).le h151
    · -- right
      by_cases h155 : z ≤ ((823/3200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B001.c28_pos (not_le.mp h0).le h148 (not_le.mp h151).le h155
      · -- right
        exact CKLaneC2R.Cells.S05.B001.c29_pos (not_le.mp h0).le h148 (not_le.mp h155).le h150
  · -- right
    by_cases h156 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h157 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B001.c30_pos (not_le.mp h0).le h148 (not_le.mp h150).le h157
      · -- right
        exact CKLaneC2R.Cells.S05.B001.c31_pos (not_le.mp h0).le h148 (not_le.mp h157).le h156
    · -- right
      by_cases h158 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B001.c32_pos (not_le.mp h0).le h148 (not_le.mp h156).le h158
      · -- right
        exact CKLaneC2R.Cells.S05.B001.c33_pos (not_le.mp h0).le h148 (not_le.mp h158).le h149

theorem strip5_s019 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : a ≤ ((1539/1600 : ℚ) : ℝ)) (h149 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h159 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h160 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h161 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B002.c46_pos (not_le.mp h0).le h148 (not_le.mp h149).le h161
    · -- right
      exact CKLaneC2R.Cells.S05.B002.c47_pos (not_le.mp h0).le h148 (not_le.mp h161).le h160
  · -- right
    by_cases h162 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h163 : a ≤ ((15291/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B005.c103_pos (not_le.mp h0).le h163 (not_le.mp h160).le h162
      · -- right
        exact CKLaneC2R.Cells.S05.B005.c104_pos (not_le.mp h163).le h148 (not_le.mp h160).le h162
    · -- right
      by_cases h164 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B005.c107_pos (not_le.mp h0).le h148 (not_le.mp h162).le h164
      · -- right
        exact CKLaneC2R.Cells.S05.B005.c108_pos (not_le.mp h0).le h148 (not_le.mp h164).le h159

theorem strip5_s020 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : a ≤ ((1539/1600 : ℚ) : ℝ)) (h149 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h159 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h165 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h166 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h167 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B006.c129_pos (not_le.mp h0).le h148 (not_le.mp h159).le h167
    · -- right
      by_cases h168 : a ≤ ((15291/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B008.c168_pos (not_le.mp h0).le h168 (not_le.mp h167).le h166
      · -- right
        exact CKLaneC2R.Cells.S05.B008.c169_pos (not_le.mp h168).le h148 (not_le.mp h167).le h166
  · -- right
    by_cases h169 : a ≤ ((15291/16000 : ℚ) : ℝ)
    · -- left
      by_cases h170 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B008.c174_pos (not_le.mp h0).le h169 (not_le.mp h166).le h170
      · -- right
        exact CKLaneC2R.Cells.S05.B008.c176_pos (not_le.mp h0).le h169 (not_le.mp h170).le h165
    · -- right
      by_cases h171 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B008.c175_pos (not_le.mp h169).le h148 (not_le.mp h166).le h171
      · -- right
        exact CKLaneC2R.Cells.S05.B008.c177_pos (not_le.mp h169).le h148 (not_le.mp h171).le h165

end CKLaneC2R.CompactCover


