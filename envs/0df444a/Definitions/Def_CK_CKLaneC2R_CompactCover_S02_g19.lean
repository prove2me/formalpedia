-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g19
-- name    : CK_CKLaneC2R_CompactCover_S02_g19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T14:02:20.746604+00:00
-- url     : https://prove2.me/theorems/492bd6da-bdf7-4c05-82b1-5d8666a8f56e
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B009

namespace CKLaneC2R.CompactCover

theorem strip2_s030 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : a ≤ ((3/8 : ℚ) : ℝ)) (h316 : a ≤ ((29/80 : ℚ) : ℝ)) (h317 : z ≤ ((217/400 : ℚ) : ℝ)) (h318 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h340 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h341 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h342 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h343 : a ≤ ((57/160 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B020.c407_pos (not_le.mp h1).le h343 (not_le.mp h318).le h342
        · -- right
          exact CKLaneC2R.Cells.S02.B020.c408_pos (not_le.mp h343).le h316 (not_le.mp h318).le h342
      · -- right
        exact CKLaneC2R.Cells.S02.B001.c34_pos (not_le.mp h1).le h316 (not_le.mp h342).le h341
    · -- right
      by_cases h344 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B001.c37_pos (not_le.mp h1).le h316 (not_le.mp h341).le h344
      · -- right
        exact CKLaneC2R.Cells.S02.B001.c38_pos (not_le.mp h1).le h316 (not_le.mp h344).le h340
  · -- right
    by_cases h345 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h346 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B002.c49_pos (not_le.mp h1).le h316 (not_le.mp h340).le h346
      · -- right
        exact CKLaneC2R.Cells.S02.B002.c50_pos (not_le.mp h1).le h316 (not_le.mp h346).le h345
    · -- right
      by_cases h347 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B002.c53_pos (not_le.mp h1).le h316 (not_le.mp h345).le h347
      · -- right
        exact CKLaneC2R.Cells.S02.B002.c54_pos (not_le.mp h1).le h316 (not_le.mp h347).le h317

theorem strip2_s031 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : a ≤ ((3/8 : ℚ) : ℝ)) (h316 : a ≤ ((29/80 : ℚ) : ℝ)) (h317 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h348 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h349 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h350 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h351 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B008.c162_pos (not_le.mp h1).le h316 (not_le.mp h317).le h351
      · -- right
        exact CKLaneC2R.Cells.S02.B008.c163_pos (not_le.mp h1).le h316 (not_le.mp h351).le h350
    · -- right
      by_cases h352 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B008.c166_pos (not_le.mp h1).le h316 (not_le.mp h350).le h352
      · -- right
        exact CKLaneC2R.Cells.S02.B008.c167_pos (not_le.mp h1).le h316 (not_le.mp h352).le h349
  · -- right
    by_cases h353 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h354 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B008.c178_pos (not_le.mp h1).le h316 (not_le.mp h349).le h354
      · -- right
        exact CKLaneC2R.Cells.S02.B008.c179_pos (not_le.mp h1).le h316 (not_le.mp h354).le h353
    · -- right
      by_cases h355 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B009.c182_pos (not_le.mp h1).le h316 (not_le.mp h353).le h355
      · -- right
        exact CKLaneC2R.Cells.S02.B009.c183_pos (not_le.mp h1).le h316 (not_le.mp h355).le h348

end CKLaneC2R.CompactCover


