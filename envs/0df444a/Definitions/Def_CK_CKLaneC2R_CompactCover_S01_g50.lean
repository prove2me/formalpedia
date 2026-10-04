-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g50
-- name    : CK_CKLaneC2R_CompactCover_S01_g50
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T18:10:20.06861+00:00
-- url     : https://prove2.me/theorems/502f53f0-0a55-4171-ac22-53b5b62121da
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B045
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B046
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B054
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B055
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B057
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B058
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B059

namespace CKLaneC2R.CompactCover

theorem strip1_s067 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : a ≤ ((39/160 : ℚ) : ℝ)) (h599 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h642 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h650 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h658 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h662 : z ≤ ((6211/6400 : ℚ) : ℝ)
  · -- left
    by_cases h663 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      by_cases h664 : z ≤ ((121481/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B045.c905_pos (not_le.mp h419).le h598 (not_le.mp h658).le h664
      · -- right
        exact CKLaneC2R.Cells.S01.B045.c906_pos (not_le.mp h419).le h598 (not_le.mp h664).le h663
    · -- right
      by_cases h665 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B045.c909_pos (not_le.mp h419).le h598 (not_le.mp h663).le h665
      · -- right
        exact CKLaneC2R.Cells.S01.B045.c910_pos (not_le.mp h419).le h598 (not_le.mp h665).le h662
  · -- right
    by_cases h666 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h667 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B046.c930_pos (not_le.mp h419).le h598 (not_le.mp h662).le h667
      · -- right
        by_cases h668 : z ≤ ((251179/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B054.c1092_pos (not_le.mp h419).le h598 (not_le.mp h667).le h668
        · -- right
          exact CKLaneC2R.Cells.S01.B054.c1093_pos (not_le.mp h419).le h598 (not_le.mp h668).le h666
    · -- right
      by_cases h669 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        by_cases h670 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B055.c1104_pos (not_le.mp h419).le h598 (not_le.mp h666).le h670
        · -- right
          exact CKLaneC2R.Cells.S01.B055.c1106_pos (not_le.mp h419).le h598 (not_le.mp h670).le h669
      · -- right
        by_cases h671 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          by_cases h672 : z ≤ ((508749/512000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B057.c1149_pos (not_le.mp h419).le h598 (not_le.mp h669).le h672
          · -- right
            exact CKLaneC2R.Cells.S01.B057.c1150_pos (not_le.mp h419).le h598 (not_le.mp h672).le h671
        · -- right
          by_cases h673 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B058.c1161_pos (not_le.mp h419).le h598 (not_le.mp h671).le h673
          · -- right
            by_cases h674 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S01.B059.c1186_pos (not_le.mp h419).le h598 (not_le.mp h673).le h674
            · -- right
              exact CKLaneC2R.Cells.S01.B059.c1188_pos (not_le.mp h419).le h598 (not_le.mp h674).le hz2

end CKLaneC2R.CompactCover


