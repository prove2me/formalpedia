-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g20
-- name    : CK_CKLaneC2R_CompactCover_S00_g20
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T21:53:42.101845+00:00
-- url     : https://prove2.me/theorems/361efac3-55af-433e-924c-47eab3b533b8
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S00 (proof part of strip0) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S00 (proof part of strip0).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B065
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B067
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B070
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B071
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B072
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B073
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B074

namespace CKLaneC2R.CompactCover

theorem strip0_s025 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((49/320 : ℚ) : ℝ))) (h133 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h202 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h218 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h227 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h235 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h240 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h241 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      by_cases h242 : z ≤ ((249353/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B065.c1301_pos (not_le.mp h3).le h2 (not_le.mp h235).le h242
      · -- right
        exact CKLaneC2R.Cells.S00.B065.c1302_pos (not_le.mp h3).le h2 (not_le.mp h242).le h241
    · -- right
      by_cases h243 : z ≤ ((251179/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B065.c1308_pos (not_le.mp h3).le h2 (not_le.mp h241).le h243
      · -- right
        exact CKLaneC2R.Cells.S00.B065.c1310_pos (not_le.mp h3).le h2 (not_le.mp h243).le h240
  · -- right
    by_cases h244 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h245 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B067.c1343_pos (not_le.mp h3).le h2 (not_le.mp h240).le h245
      · -- right
        by_cases h246 : z ≤ ((506923/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B070.c1408_pos (not_le.mp h3).le h2 (not_le.mp h245).le h246
        · -- right
          exact CKLaneC2R.Cells.S00.B070.c1409_pos (not_le.mp h3).le h2 (not_le.mp h246).le h244
    · -- right
      by_cases h247 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        by_cases h248 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B071.c1421_pos (not_le.mp h3).le h2 (not_le.mp h244).le h248
        · -- right
          exact CKLaneC2R.Cells.S00.B071.c1423_pos (not_le.mp h3).le h2 (not_le.mp h248).le h247
      · -- right
        by_cases h249 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          by_cases h250 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B072.c1458_pos (not_le.mp h3).le h2 (not_le.mp h247).le h250
          · -- right
            exact CKLaneC2R.Cells.S00.B072.c1459_pos (not_le.mp h3).le h2 (not_le.mp h250).le h249
        · -- right
          by_cases h251 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B073.c1473_pos (not_le.mp h3).le h2 (not_le.mp h249).le h251
          · -- right
            by_cases h252 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S00.B074.c1492_pos (not_le.mp h3).le h2 (not_le.mp h251).le h252
            · -- right
              exact CKLaneC2R.Cells.S00.B074.c1493_pos (not_le.mp h3).le h2 (not_le.mp h252).le hz2

end CKLaneC2R.CompactCover


