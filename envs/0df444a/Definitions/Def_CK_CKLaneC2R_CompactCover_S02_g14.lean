-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g14
-- name    : CK_CKLaneC2R_CompactCover_S02_g14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T07:55:40.591328+00:00
-- url     : https://prove2.me/theorems/42f58c01-0abc-46aa-9025-57891b74576f
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
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B014

namespace CKLaneC2R.CompactCover

theorem strip2_s022 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((13/40 : ℚ) : ℝ))) (h179 : ¬ (a ≤ ((27/80 : ℚ) : ℝ))) (h251 : z ≤ ((217/400 : ℚ) : ℝ)) (h252 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h253 : a ≤ ((11/32 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h254 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h255 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h256 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h257 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          by_cases h258 : z ≤ ((11921/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B038.c775_pos (not_le.mp h179).le h253 hz1 h258
          · -- right
            exact CKLaneC2R.Cells.S02.B038.c776_pos (not_le.mp h179).le h253 (not_le.mp h258).le h257
        · -- right
          exact CKLaneC2R.Cells.S02.B030.c605_pos (not_le.mp h179).le h253 (not_le.mp h257).le h256
      · -- right
        by_cases h259 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B030.c611_pos (not_le.mp h179).le h253 (not_le.mp h256).le h259
        · -- right
          exact CKLaneC2R.Cells.S02.B030.c613_pos (not_le.mp h179).le h253 (not_le.mp h259).le h255
    · -- right
      by_cases h260 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h261 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B031.c623_pos (not_le.mp h179).le h253 (not_le.mp h255).le h261
        · -- right
          exact CKLaneC2R.Cells.S02.B031.c625_pos (not_le.mp h179).le h253 (not_le.mp h261).le h260
      · -- right
        by_cases h262 : z ≤ ((2379/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B031.c627_pos (not_le.mp h179).le h253 (not_le.mp h260).le h262
        · -- right
          exact CKLaneC2R.Cells.S02.B031.c628_pos (not_le.mp h179).le h253 (not_le.mp h262).le h254
  · -- right
    by_cases h263 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h264 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B015.c308_pos (not_le.mp h179).le h253 (not_le.mp h254).le h264
      · -- right
        exact CKLaneC2R.Cells.S02.B015.c310_pos (not_le.mp h179).le h253 (not_le.mp h264).le h263
    · -- right
      by_cases h265 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B015.c316_pos (not_le.mp h179).le h253 (not_le.mp h263).le h265
      · -- right
        exact CKLaneC2R.Cells.S02.B015.c318_pos (not_le.mp h179).le h253 (not_le.mp h265).le h252

theorem strip2_s023 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((13/40 : ℚ) : ℝ))) (h179 : ¬ (a ≤ ((27/80 : ℚ) : ℝ))) (h251 : z ≤ ((217/400 : ℚ) : ℝ)) (h252 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h253 : ¬ (a ≤ ((11/32 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h266 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h267 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h268 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h269 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          by_cases h270 : z ≤ ((11921/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B038.c777_pos (not_le.mp h253).le h1 hz1 h270
          · -- right
            exact CKLaneC2R.Cells.S02.B038.c778_pos (not_le.mp h253).le h1 (not_le.mp h270).le h269
        · -- right
          exact CKLaneC2R.Cells.S02.B030.c606_pos (not_le.mp h253).le h1 (not_le.mp h269).le h268
      · -- right
        by_cases h271 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B030.c612_pos (not_le.mp h253).le h1 (not_le.mp h268).le h271
        · -- right
          exact CKLaneC2R.Cells.S02.B030.c614_pos (not_le.mp h253).le h1 (not_le.mp h271).le h267
    · -- right
      by_cases h272 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h273 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B031.c624_pos (not_le.mp h253).le h1 (not_le.mp h267).le h273
        · -- right
          exact CKLaneC2R.Cells.S02.B031.c626_pos (not_le.mp h253).le h1 (not_le.mp h273).le h272
      · -- right
        exact CKLaneC2R.Cells.S02.B014.c290_pos (not_le.mp h253).le h1 (not_le.mp h272).le h266
  · -- right
    by_cases h274 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h275 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B015.c309_pos (not_le.mp h253).le h1 (not_le.mp h266).le h275
      · -- right
        exact CKLaneC2R.Cells.S02.B015.c311_pos (not_le.mp h253).le h1 (not_le.mp h275).le h274
    · -- right
      by_cases h276 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B015.c317_pos (not_le.mp h253).le h1 (not_le.mp h274).le h276
      · -- right
        exact CKLaneC2R.Cells.S02.B015.c319_pos (not_le.mp h253).le h1 (not_le.mp h276).le h252

end CKLaneC2R.CompactCover


