-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g15
-- name    : CK_CKLaneC2R_CompactCover_S03_g15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T14:20:24.81986+00:00
-- url     : https://prove2.me/theorems/4af0c2a9-9bd7-4670-815c-0a6dad8f5fdd
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

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B019

namespace CKLaneC2R.CompactCover

theorem strip3_s022 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((3/5 : ℚ) : ℝ))) (h220 : a ≤ ((13/20 : ℚ) : ℝ)) (h221 : a ≤ ((5/8 : ℚ) : ℝ)) (h222 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h245 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h253 : z ≤ ((7079/8000 : ℚ) : ℝ)
  · -- left
    by_cases h254 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h255 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B007.c156_pos (not_le.mp h0).le h221 (not_le.mp h245).le h255
      · -- right
        exact CKLaneC2R.Cells.S03.B007.c157_pos (not_le.mp h0).le h221 (not_le.mp h255).le h254
    · -- right
      by_cases h256 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B008.c160_pos (not_le.mp h0).le h221 (not_le.mp h254).le h256
      · -- right
        exact CKLaneC2R.Cells.S03.B008.c161_pos (not_le.mp h0).le h221 (not_le.mp h256).le h253
  · -- right
    by_cases h257 : z ≤ ((15071/16000 : ℚ) : ℝ)
    · -- left
      by_cases h258 : a ≤ ((49/80 : ℚ) : ℝ)
      · -- left
        by_cases h259 : z ≤ ((29229/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B013.c274_pos (not_le.mp h0).le h258 (not_le.mp h253).le h259
        · -- right
          exact CKLaneC2R.Cells.S03.B013.c276_pos (not_le.mp h0).le h258 (not_le.mp h259).le h257
      · -- right
        by_cases h260 : z ≤ ((29229/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B013.c275_pos (not_le.mp h258).le h221 (not_le.mp h253).le h260
        · -- right
          exact CKLaneC2R.Cells.S03.B013.c277_pos (not_le.mp h258).le h221 (not_le.mp h260).le h257
    · -- right
      by_cases h261 : z ≤ ((6211/6400 : ℚ) : ℝ)
      · -- left
        by_cases h262 : z ≤ ((61197/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B014.c294_pos (not_le.mp h0).le h221 (not_le.mp h257).le h262
        · -- right
          exact CKLaneC2R.Cells.S03.B014.c295_pos (not_le.mp h0).le h221 (not_le.mp h262).le h261
      · -- right
        by_cases h263 : z ≤ ((63023/64000 : ℚ) : ℝ)
        · -- left
          by_cases h264 : z ≤ ((125133/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B017.c354_pos (not_le.mp h0).le h221 (not_le.mp h261).le h264
          · -- right
            exact CKLaneC2R.Cells.S03.B017.c355_pos (not_le.mp h0).le h221 (not_le.mp h264).le h263
        · -- right
          by_cases h265 : z ≤ ((126959/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B018.c363_pos (not_le.mp h0).le h221 (not_le.mp h263).le h265
          · -- right
            by_cases h266 : z ≤ ((254831/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S03.B018.c377_pos (not_le.mp h0).le h221 (not_le.mp h265).le h266
            · -- right
              by_cases h267 : z ≤ ((20423/20480 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S03.B019.c385_pos (not_le.mp h0).le h221 (not_le.mp h266).le h267
              · -- right
                exact CKLaneC2R.Cells.S03.B019.c387_pos (not_le.mp h0).le h221 (not_le.mp h267).le hz2

end CKLaneC2R.CompactCover


