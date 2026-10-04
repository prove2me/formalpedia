-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g29
-- name    : CK_CKLaneC2R_CompactCover_S02_g29
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T03:58:18.649975+00:00
-- url     : https://prove2.me/theorems/e8ef8278-6c05-442f-acdb-4b448321a120
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B039
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B042

namespace CKLaneC2R.CompactCover

theorem strip2_s045 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : ¬ (a ≤ ((3/8 : ℚ) : ℝ))) (h430 : a ≤ ((31/80 : ℚ) : ℝ)) (h431 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h459 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h467 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h471 : z ≤ ((15071/16000 : ℚ) : ℝ)
  · -- left
    by_cases h472 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h473 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B027.c541_pos (not_le.mp h315).le h430 (not_le.mp h467).le h473
      · -- right
        exact CKLaneC2R.Cells.S02.B027.c542_pos (not_le.mp h315).le h430 (not_le.mp h473).le h472
    · -- right
      by_cases h474 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B027.c543_pos (not_le.mp h315).le h430 (not_le.mp h472).le h474
      · -- right
        exact CKLaneC2R.Cells.S02.B027.c544_pos (not_le.mp h315).le h430 (not_le.mp h474).le h471
  · -- right
    by_cases h475 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h476 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B027.c559_pos (not_le.mp h315).le h430 (not_le.mp h471).le h476
      · -- right
        exact CKLaneC2R.Cells.S02.B028.c561_pos (not_le.mp h315).le h430 (not_le.mp h476).le h475
    · -- right
      by_cases h477 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        by_cases h478 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B036.c727_pos (not_le.mp h315).le h430 (not_le.mp h475).le h478
        · -- right
          exact CKLaneC2R.Cells.S02.B036.c728_pos (not_le.mp h315).le h430 (not_le.mp h478).le h477
      · -- right
        by_cases h479 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          by_cases h480 : z ≤ ((50601/51200 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B039.c795_pos (not_le.mp h315).le h430 (not_le.mp h477).le h480
          · -- right
            exact CKLaneC2R.Cells.S02.B039.c796_pos (not_le.mp h315).le h430 (not_le.mp h480).le h479
        · -- right
          by_cases h481 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B040.c803_pos (not_le.mp h315).le h430 (not_le.mp h479).le h481
          · -- right
            by_cases h482 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S02.B041.c824_pos (not_le.mp h315).le h430 (not_le.mp h481).le h482
            · -- right
              by_cases h483 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S02.B042.c850_pos (not_le.mp h315).le h430 (not_le.mp h482).le h483
              · -- right
                exact CKLaneC2R.Cells.S02.B042.c851_pos (not_le.mp h315).le h430 (not_le.mp h483).le hz2

end CKLaneC2R.CompactCover


