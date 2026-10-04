-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g39
-- name    : CK_CKLaneC2R_CompactCover_S00_g39
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T18:52:09.133957+00:00
-- url     : https://prove2.me/theorems/1bd6b8f4-9e4d-4bac-b58d-fd544bad7044
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B070
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B057
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B058
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B059
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B060
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B061
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B034

namespace CKLaneC2R.CompactCover

theorem strip0_s046 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : a ≤ ((53/320 : ℚ) : ℝ)) (h483 : z ≤ ((217/400 : ℚ) : ℝ)) (h484 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h485 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h486 : a ≤ ((21/128 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h487 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h488 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h489 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h490 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          by_cases h491 : z ≤ ((22929/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B070.c1402_pos (not_le.mp h1).le h486 hz1 h491
          · -- right
            exact CKLaneC2R.Cells.S00.B070.c1403_pos (not_le.mp h1).le h486 (not_le.mp h491).le h490
        · -- right
          exact CKLaneC2R.Cells.S00.B057.c1149_pos (not_le.mp h1).le h486 (not_le.mp h490).le h489
      · -- right
        by_cases h492 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B057.c1155_pos (not_le.mp h1).le h486 (not_le.mp h489).le h492
        · -- right
          exact CKLaneC2R.Cells.S00.B057.c1157_pos (not_le.mp h1).le h486 (not_le.mp h492).le h488
    · -- right
      by_cases h493 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h494 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B058.c1179_pos (not_le.mp h1).le h486 (not_le.mp h488).le h494
        · -- right
          exact CKLaneC2R.Cells.S00.B059.c1181_pos (not_le.mp h1).le h486 (not_le.mp h494).le h493
      · -- right
        by_cases h495 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B059.c1187_pos (not_le.mp h1).le h486 (not_le.mp h493).le h495
        · -- right
          exact CKLaneC2R.Cells.S00.B059.c1189_pos (not_le.mp h1).le h486 (not_le.mp h495).le h487
  · -- right
    by_cases h496 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h497 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        by_cases h498 : z ≤ ((769/5120 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B060.c1211_pos (not_le.mp h1).le h486 (not_le.mp h487).le h498
        · -- right
          exact CKLaneC2R.Cells.S00.B060.c1213_pos (not_le.mp h1).le h486 (not_le.mp h498).le h497
      · -- right
        by_cases h499 : z ≤ ((21051/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B060.c1219_pos (not_le.mp h1).le h486 (not_le.mp h497).le h499
        · -- right
          exact CKLaneC2R.Cells.S00.B061.c1221_pos (not_le.mp h1).le h486 (not_le.mp h499).le h496
    · -- right
      by_cases h500 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B034.c686_pos (not_le.mp h1).le h486 (not_le.mp h496).le h500
      · -- right
        exact CKLaneC2R.Cells.S00.B034.c688_pos (not_le.mp h1).le h486 (not_le.mp h500).le h485

end CKLaneC2R.CompactCover


