-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g45
-- name    : CK_CKLaneC2R_CompactCover_S01_g45
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T20:38:45.363959+00:00
-- url     : https://prove2.me/theorems/749e5935-781a-4443-987a-7f2516944c10
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B044
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B045
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B046
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B054
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B055
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B057
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B058
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B059

namespace CKLaneC2R.CompactCover

theorem strip1_s059 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : ¬ (a ≤ ((37/160 : ℚ) : ℝ))) (h513 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h561 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h573 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h581 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h585 : z ≤ ((6211/6400 : ℚ) : ℝ)
  · -- left
    by_cases h586 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      by_cases h587 : z ≤ ((121481/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B044.c899_pos (not_le.mp h420).le h419 (not_le.mp h581).le h587
      · -- right
        exact CKLaneC2R.Cells.S01.B045.c900_pos (not_le.mp h420).le h419 (not_le.mp h587).le h586
    · -- right
      by_cases h588 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B045.c903_pos (not_le.mp h420).le h419 (not_le.mp h586).le h588
      · -- right
        exact CKLaneC2R.Cells.S01.B045.c904_pos (not_le.mp h420).le h419 (not_le.mp h588).le h585
  · -- right
    by_cases h589 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h590 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B046.c929_pos (not_le.mp h420).le h419 (not_le.mp h585).le h590
      · -- right
        by_cases h591 : z ≤ ((251179/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B054.c1090_pos (not_le.mp h420).le h419 (not_le.mp h590).le h591
        · -- right
          exact CKLaneC2R.Cells.S01.B054.c1091_pos (not_le.mp h420).le h419 (not_le.mp h591).le h589
    · -- right
      by_cases h592 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        by_cases h593 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B055.c1101_pos (not_le.mp h420).le h419 (not_le.mp h589).le h593
        · -- right
          exact CKLaneC2R.Cells.S01.B055.c1103_pos (not_le.mp h420).le h419 (not_le.mp h593).le h592
      · -- right
        by_cases h594 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          by_cases h595 : z ≤ ((508749/512000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B057.c1147_pos (not_le.mp h420).le h419 (not_le.mp h592).le h595
          · -- right
            exact CKLaneC2R.Cells.S01.B057.c1148_pos (not_le.mp h420).le h419 (not_le.mp h595).le h594
        · -- right
          by_cases h596 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B058.c1160_pos (not_le.mp h420).le h419 (not_le.mp h594).le h596
          · -- right
            by_cases h597 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S01.B059.c1183_pos (not_le.mp h420).le h419 (not_le.mp h596).le h597
            · -- right
              exact CKLaneC2R.Cells.S01.B059.c1185_pos (not_le.mp h420).le h419 (not_le.mp h597).le hz2

end CKLaneC2R.CompactCover


