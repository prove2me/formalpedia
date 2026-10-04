-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g21
-- name    : CK_CKLaneC2R_CompactCover_S02_g21
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T21:57:50.345262+00:00
-- url     : https://prove2.me/theorems/771807d4-f0ae-4960-9fd0-900a4d864446
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B035
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B039
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B042

namespace CKLaneC2R.CompactCover

theorem strip2_s033 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : a ≤ ((3/8 : ℚ) : ℝ)) (h316 : a ≤ ((29/80 : ℚ) : ℝ)) (h317 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h348 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h356 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h361 : z ≤ ((15071/16000 : ℚ) : ℝ)
  · -- left
    by_cases h362 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h363 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B026.c533_pos (not_le.mp h1).le h316 (not_le.mp h356).le h363
      · -- right
        exact CKLaneC2R.Cells.S02.B026.c534_pos (not_le.mp h1).le h316 (not_le.mp h363).le h362
    · -- right
      by_cases h364 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B026.c537_pos (not_le.mp h1).le h316 (not_le.mp h362).le h364
      · -- right
        exact CKLaneC2R.Cells.S02.B026.c538_pos (not_le.mp h1).le h316 (not_le.mp h364).le h361
  · -- right
    by_cases h365 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h366 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B027.c556_pos (not_le.mp h1).le h316 (not_le.mp h361).le h366
      · -- right
        by_cases h367 : z ≤ ((123307/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B035.c715_pos (not_le.mp h1).le h316 (not_le.mp h366).le h367
        · -- right
          exact CKLaneC2R.Cells.S02.B035.c716_pos (not_le.mp h1).le h316 (not_le.mp h367).le h365
    · -- right
      by_cases h368 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        by_cases h369 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B036.c723_pos (not_le.mp h1).le h316 (not_le.mp h365).le h369
        · -- right
          exact CKLaneC2R.Cells.S02.B036.c724_pos (not_le.mp h1).le h316 (not_le.mp h369).le h368
      · -- right
        by_cases h370 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          by_cases h371 : z ≤ ((50601/51200 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B039.c791_pos (not_le.mp h1).le h316 (not_le.mp h368).le h371
          · -- right
            exact CKLaneC2R.Cells.S02.B039.c792_pos (not_le.mp h1).le h316 (not_le.mp h371).le h370
        · -- right
          by_cases h372 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B040.c801_pos (not_le.mp h1).le h316 (not_le.mp h370).le h372
          · -- right
            by_cases h373 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S02.B041.c822_pos (not_le.mp h1).le h316 (not_le.mp h372).le h373
            · -- right
              by_cases h374 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S02.B042.c846_pos (not_le.mp h1).le h316 (not_le.mp h373).le h374
              · -- right
                exact CKLaneC2R.Cells.S02.B042.c847_pos (not_le.mp h1).le h316 (not_le.mp h374).le hz2

end CKLaneC2R.CompactCover


