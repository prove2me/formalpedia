-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g42
-- name    : CK_CKLaneC2R_CompactCover_S02_g42
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T18:48:16.658858+00:00
-- url     : https://prove2.me/theorems/c8f108a8-cbc8-4869-8caf-fb21550600f4
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B037
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B041

namespace CKLaneC2R.CompactCover

theorem strip2_s063 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : ¬ (a ≤ ((17/40 : ℚ) : ℝ))) (h630 : a ≤ ((7/16 : ℚ) : ℝ)) (h631 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h653 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h661 : z ≤ ((7079/8000 : ℚ) : ℝ)
  · -- left
    by_cases h662 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h663 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B012.c249_pos (not_le.mp h535).le h630 (not_le.mp h653).le h663
      · -- right
        exact CKLaneC2R.Cells.S02.B012.c250_pos (not_le.mp h535).le h630 (not_le.mp h663).le h662
    · -- right
      by_cases h664 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B012.c257_pos (not_le.mp h535).le h630 (not_le.mp h662).le h664
      · -- right
        exact CKLaneC2R.Cells.S02.B012.c259_pos (not_le.mp h535).le h630 (not_le.mp h664).le h661
  · -- right
    by_cases h665 : z ≤ ((15071/16000 : ℚ) : ℝ)
    · -- left
      by_cases h666 : z ≤ ((29229/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B014.c280_pos (not_le.mp h535).le h630 (not_le.mp h661).le h666
      · -- right
        by_cases h667 : z ≤ ((59371/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B027.c551_pos (not_le.mp h535).le h630 (not_le.mp h666).le h667
        · -- right
          exact CKLaneC2R.Cells.S02.B027.c552_pos (not_le.mp h535).le h630 (not_le.mp h667).le h665
    · -- right
      by_cases h668 : z ≤ ((6211/6400 : ℚ) : ℝ)
      · -- left
        by_cases h669 : z ≤ ((61197/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B028.c567_pos (not_le.mp h535).le h630 (not_le.mp h665).le h669
        · -- right
          exact CKLaneC2R.Cells.S02.B028.c569_pos (not_le.mp h535).le h630 (not_le.mp h669).le h668
      · -- right
        by_cases h670 : z ≤ ((63023/64000 : ℚ) : ℝ)
        · -- left
          by_cases h671 : z ≤ ((125133/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B036.c735_pos (not_le.mp h535).le h630 (not_le.mp h668).le h671
          · -- right
            exact CKLaneC2R.Cells.S02.B036.c737_pos (not_le.mp h535).le h630 (not_le.mp h671).le h670
        · -- right
          by_cases h672 : z ≤ ((126959/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B037.c749_pos (not_le.mp h535).le h630 (not_le.mp h670).le h672
          · -- right
            by_cases h673 : z ≤ ((254831/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S02.B040.c807_pos (not_le.mp h535).le h630 (not_le.mp h672).le h673
            · -- right
              by_cases h674 : z ≤ ((20423/20480 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S02.B041.c828_pos (not_le.mp h535).le h630 (not_le.mp h673).le h674
              · -- right
                exact CKLaneC2R.Cells.S02.B041.c830_pos (not_le.mp h535).le h630 (not_le.mp h674).le hz2

end CKLaneC2R.CompactCover


