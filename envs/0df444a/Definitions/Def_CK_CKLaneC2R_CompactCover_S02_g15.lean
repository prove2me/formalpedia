-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g15
-- name    : CK_CKLaneC2R_CompactCover_S02_g15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T05:31:10.969983+00:00
-- url     : https://prove2.me/theorems/24db45be-db83-4ea6-a7cc-f4bb930db3c7
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B008

namespace CKLaneC2R.CompactCover

theorem strip2_s024 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((13/40 : ℚ) : ℝ))) (h179 : ¬ (a ≤ ((27/80 : ℚ) : ℝ))) (h251 : z ≤ ((217/400 : ℚ) : ℝ)) (h252 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h277 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h278 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h279 : a ≤ ((11/32 : ℚ) : ℝ)
      · -- left
        by_cases h280 : z ≤ ((10969/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B017.c356_pos (not_le.mp h179).le h279 (not_le.mp h252).le h280
        · -- right
          exact CKLaneC2R.Cells.S02.B017.c358_pos (not_le.mp h179).le h279 (not_le.mp h280).le h278
      · -- right
        by_cases h281 : z ≤ ((10969/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B017.c357_pos (not_le.mp h279).le h1 (not_le.mp h252).le h281
        · -- right
          exact CKLaneC2R.Cells.S02.B017.c359_pos (not_le.mp h279).le h1 (not_le.mp h281).le h278
    · -- right
      by_cases h282 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        by_cases h283 : a ≤ ((11/32 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B018.c364_pos (not_le.mp h179).le h283 (not_le.mp h278).le h282
        · -- right
          exact CKLaneC2R.Cells.S02.B018.c365_pos (not_le.mp h283).le h1 (not_le.mp h278).le h282
      · -- right
        exact CKLaneC2R.Cells.S02.B001.c24_pos (not_le.mp h179).le h1 (not_le.mp h282).le h277
  · -- right
    by_cases h284 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h285 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B001.c25_pos (not_le.mp h179).le h1 (not_le.mp h277).le h285
      · -- right
        exact CKLaneC2R.Cells.S02.B001.c26_pos (not_le.mp h179).le h1 (not_le.mp h285).le h284
    · -- right
      by_cases h286 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B001.c29_pos (not_le.mp h179).le h1 (not_le.mp h284).le h286
      · -- right
        exact CKLaneC2R.Cells.S02.B001.c30_pos (not_le.mp h179).le h1 (not_le.mp h286).le h251

theorem strip2_s025 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((13/40 : ℚ) : ℝ))) (h179 : ¬ (a ≤ ((27/80 : ℚ) : ℝ))) (h251 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h287 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h288 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h289 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h290 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B007.c148_pos (not_le.mp h179).le h1 (not_le.mp h251).le h290
      · -- right
        exact CKLaneC2R.Cells.S02.B007.c149_pos (not_le.mp h179).le h1 (not_le.mp h290).le h289
    · -- right
      by_cases h291 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B007.c152_pos (not_le.mp h179).le h1 (not_le.mp h289).le h291
      · -- right
        exact CKLaneC2R.Cells.S02.B007.c153_pos (not_le.mp h179).le h1 (not_le.mp h291).le h288
  · -- right
    by_cases h292 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h293 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B007.c156_pos (not_le.mp h179).le h1 (not_le.mp h288).le h293
      · -- right
        exact CKLaneC2R.Cells.S02.B007.c157_pos (not_le.mp h179).le h1 (not_le.mp h293).le h292
    · -- right
      by_cases h294 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B008.c160_pos (not_le.mp h179).le h1 (not_le.mp h292).le h294
      · -- right
        exact CKLaneC2R.Cells.S02.B008.c161_pos (not_le.mp h179).le h1 (not_le.mp h294).le h287

end CKLaneC2R.CompactCover


