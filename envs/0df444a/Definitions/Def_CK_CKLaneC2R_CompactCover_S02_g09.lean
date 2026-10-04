-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g09
-- name    : CK_CKLaneC2R_CompactCover_S02_g09
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T06:12:46.064894+00:00
-- url     : https://prove2.me/theorems/a26cc2cb-acef-432b-a259-c86f07abf000
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B023
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B024
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B025

namespace CKLaneC2R.CompactCover

theorem strip2_s011 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : a ≤ ((13/40 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((5/16 : ℚ) : ℝ))) (h93 : z ≤ ((217/400 : ℚ) : ℝ)) (h94 : ¬ (a ≤ ((51/160 : ℚ) : ℝ))) (h117 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h131 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h132 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h133 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B016.c325_pos (not_le.mp h94).le h2 (not_le.mp h117).le h133
      · -- right
        exact CKLaneC2R.Cells.S02.B016.c327_pos (not_le.mp h94).le h2 (not_le.mp h133).le h132
    · -- right
      by_cases h134 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B016.c333_pos (not_le.mp h94).le h2 (not_le.mp h132).le h134
      · -- right
        exact CKLaneC2R.Cells.S02.B016.c335_pos (not_le.mp h94).le h2 (not_le.mp h134).le h131
  · -- right
    by_cases h135 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h136 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B017.c341_pos (not_le.mp h94).le h2 (not_le.mp h131).le h136
      · -- right
        exact CKLaneC2R.Cells.S02.B017.c343_pos (not_le.mp h94).le h2 (not_le.mp h136).le h135
    · -- right
      by_cases h137 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B017.c349_pos (not_le.mp h94).le h2 (not_le.mp h135).le h137
      · -- right
        exact CKLaneC2R.Cells.S02.B017.c351_pos (not_le.mp h94).le h2 (not_le.mp h137).le h93

theorem strip2_s012 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : a ≤ ((13/40 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((5/16 : ℚ) : ℝ))) (h93 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h138 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h139 : a ≤ ((51/160 : ℚ) : ℝ)
  · -- left
    by_cases h140 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h141 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h142 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B023.c461_pos (not_le.mp h3).le h139 (not_le.mp h93).le h142
        · -- right
          exact CKLaneC2R.Cells.S02.B023.c463_pos (not_le.mp h3).le h139 (not_le.mp h142).le h141
      · -- right
        by_cases h143 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B023.c469_pos (not_le.mp h3).le h139 (not_le.mp h141).le h143
        · -- right
          exact CKLaneC2R.Cells.S02.B023.c471_pos (not_le.mp h3).le h139 (not_le.mp h143).le h140
    · -- right
      by_cases h144 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h145 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B023.c477_pos (not_le.mp h3).le h139 (not_le.mp h140).le h145
        · -- right
          exact CKLaneC2R.Cells.S02.B023.c479_pos (not_le.mp h3).le h139 (not_le.mp h145).le h144
      · -- right
        by_cases h146 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B024.c485_pos (not_le.mp h3).le h139 (not_le.mp h144).le h146
        · -- right
          exact CKLaneC2R.Cells.S02.B024.c487_pos (not_le.mp h3).le h139 (not_le.mp h146).le h138
  · -- right
    by_cases h147 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h148 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h149 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B023.c462_pos (not_le.mp h139).le h2 (not_le.mp h93).le h149
        · -- right
          exact CKLaneC2R.Cells.S02.B023.c464_pos (not_le.mp h139).le h2 (not_le.mp h149).le h148
      · -- right
        by_cases h150 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B023.c470_pos (not_le.mp h139).le h2 (not_le.mp h148).le h150
        · -- right
          exact CKLaneC2R.Cells.S02.B023.c472_pos (not_le.mp h139).le h2 (not_le.mp h150).le h147
    · -- right
      by_cases h151 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h152 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B023.c478_pos (not_le.mp h139).le h2 (not_le.mp h147).le h152
        · -- right
          exact CKLaneC2R.Cells.S02.B024.c480_pos (not_le.mp h139).le h2 (not_le.mp h152).le h151
      · -- right
        by_cases h153 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B024.c486_pos (not_le.mp h139).le h2 (not_le.mp h151).le h153
        · -- right
          exact CKLaneC2R.Cells.S02.B024.c488_pos (not_le.mp h139).le h2 (not_le.mp h153).le h138

theorem strip2_s013 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : a ≤ ((13/40 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((5/16 : ℚ) : ℝ))) (h93 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h138 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h154 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h155 : a ≤ ((51/160 : ℚ) : ℝ)
  · -- left
    by_cases h156 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h157 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B024.c493_pos (not_le.mp h3).le h155 (not_le.mp h138).le h157
      · -- right
        exact CKLaneC2R.Cells.S02.B024.c495_pos (not_le.mp h3).le h155 (not_le.mp h157).le h156
    · -- right
      by_cases h158 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B025.c501_pos (not_le.mp h3).le h155 (not_le.mp h156).le h158
      · -- right
        exact CKLaneC2R.Cells.S02.B025.c503_pos (not_le.mp h3).le h155 (not_le.mp h158).le h154
  · -- right
    by_cases h159 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h160 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B024.c494_pos (not_le.mp h155).le h2 (not_le.mp h138).le h160
      · -- right
        exact CKLaneC2R.Cells.S02.B024.c496_pos (not_le.mp h155).le h2 (not_le.mp h160).le h159
    · -- right
      by_cases h161 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B025.c502_pos (not_le.mp h155).le h2 (not_le.mp h159).le h161
      · -- right
        exact CKLaneC2R.Cells.S02.B025.c504_pos (not_le.mp h155).le h2 (not_le.mp h161).le h154

end CKLaneC2R.CompactCover


