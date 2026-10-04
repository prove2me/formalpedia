-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g33
-- name    : CK_CKLaneC2R_CompactCover_S02_g33
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T17:23:58.152734+00:00
-- url     : https://prove2.me/theorems/bce21855-a9bd-4a63-92e4-000294a1cd3f
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B039
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B042

namespace CKLaneC2R.CompactCover

theorem strip2_s051 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : ¬ (a ≤ ((3/8 : ℚ) : ℝ))) (h430 : ¬ (a ≤ ((31/80 : ℚ) : ℝ))) (h484 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h510 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h518 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h522 : z ≤ ((15071/16000 : ℚ) : ℝ)
  · -- left
    by_cases h523 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B013.c277_pos (not_le.mp h430).le h0 (not_le.mp h518).le h523
    · -- right
      by_cases h524 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B027.c545_pos (not_le.mp h430).le h0 (not_le.mp h523).le h524
      · -- right
        exact CKLaneC2R.Cells.S02.B027.c546_pos (not_le.mp h430).le h0 (not_le.mp h524).le h522
  · -- right
    by_cases h525 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h526 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B028.c560_pos (not_le.mp h430).le h0 (not_le.mp h522).le h526
      · -- right
        exact CKLaneC2R.Cells.S02.B028.c562_pos (not_le.mp h430).le h0 (not_le.mp h526).le h525
    · -- right
      by_cases h527 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        by_cases h528 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B036.c729_pos (not_le.mp h430).le h0 (not_le.mp h525).le h528
        · -- right
          exact CKLaneC2R.Cells.S02.B036.c730_pos (not_le.mp h430).le h0 (not_le.mp h528).le h527
      · -- right
        by_cases h529 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          by_cases h530 : z ≤ ((50601/51200 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B039.c797_pos (not_le.mp h430).le h0 (not_le.mp h527).le h530
          · -- right
            exact CKLaneC2R.Cells.S02.B039.c798_pos (not_le.mp h430).le h0 (not_le.mp h530).le h529
        · -- right
          by_cases h531 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B040.c804_pos (not_le.mp h430).le h0 (not_le.mp h529).le h531
          · -- right
            by_cases h532 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S02.B041.c825_pos (not_le.mp h430).le h0 (not_le.mp h531).le h532
            · -- right
              by_cases h533 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S02.B042.c852_pos (not_le.mp h430).le h0 (not_le.mp h532).le h533
              · -- right
                exact CKLaneC2R.Cells.S02.B042.c853_pos (not_le.mp h430).le h0 (not_le.mp h533).le hz2

end CKLaneC2R.CompactCover


