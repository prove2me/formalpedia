-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g07
-- name    : CK_CKLaneC2R_CompactCover_S03_g07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T03:35:36.874586+00:00
-- url     : https://prove2.me/theorems/7a4f4587-cf64-414d-b2bf-f45db7b0ee55
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

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B005

namespace CKLaneC2R.CompactCover

theorem strip3_s011 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((11/20 : ℚ) : ℝ))) (h119 : a ≤ ((23/40 : ℚ) : ℝ)) (h120 : z ≤ ((217/400 : ℚ) : ℝ)) (h121 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h138 : a ≤ ((9/16 : ℚ) : ℝ)
  · -- left
    by_cases h139 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h140 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B000.c18_pos (not_le.mp h1).le h138 (not_le.mp h121).le h140
      · -- right
        exact CKLaneC2R.Cells.S03.B001.c20_pos (not_le.mp h1).le h138 (not_le.mp h140).le h139
    · -- right
      by_cases h141 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B001.c26_pos (not_le.mp h1).le h138 (not_le.mp h139).le h141
      · -- right
        exact CKLaneC2R.Cells.S03.B001.c28_pos (not_le.mp h1).le h138 (not_le.mp h141).le h120
  · -- right
    by_cases h142 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h143 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B000.c19_pos (not_le.mp h138).le h119 (not_le.mp h121).le h143
      · -- right
        exact CKLaneC2R.Cells.S03.B001.c21_pos (not_le.mp h138).le h119 (not_le.mp h143).le h142
    · -- right
      by_cases h144 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B001.c27_pos (not_le.mp h138).le h119 (not_le.mp h142).le h144
      · -- right
        exact CKLaneC2R.Cells.S03.B001.c29_pos (not_le.mp h138).le h119 (not_le.mp h144).le h120

theorem strip3_s012 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((11/20 : ℚ) : ℝ))) (h119 : a ≤ ((23/40 : ℚ) : ℝ)) (h120 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h145 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h146 : a ≤ ((9/16 : ℚ) : ℝ)
  · -- left
    by_cases h147 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h148 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B004.c99_pos (not_le.mp h1).le h146 (not_le.mp h120).le h148
      · -- right
        exact CKLaneC2R.Cells.S03.B005.c101_pos (not_le.mp h1).le h146 (not_le.mp h148).le h147
    · -- right
      by_cases h149 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B005.c107_pos (not_le.mp h1).le h146 (not_le.mp h147).le h149
      · -- right
        exact CKLaneC2R.Cells.S03.B005.c109_pos (not_le.mp h1).le h146 (not_le.mp h149).le h145
  · -- right
    by_cases h150 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h151 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B005.c100_pos (not_le.mp h146).le h119 (not_le.mp h120).le h151
      · -- right
        exact CKLaneC2R.Cells.S03.B005.c102_pos (not_le.mp h146).le h119 (not_le.mp h151).le h150
    · -- right
      by_cases h152 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B005.c108_pos (not_le.mp h146).le h119 (not_le.mp h150).le h152
      · -- right
        exact CKLaneC2R.Cells.S03.B005.c110_pos (not_le.mp h146).le h119 (not_le.mp h152).le h145

end CKLaneC2R.CompactCover


