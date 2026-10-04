-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g37
-- name    : CK_CKLaneC2R_CompactCover_S02_g37
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T20:57:29.011984+00:00
-- url     : https://prove2.me/theorems/9e602b79-ab53-401b-9c1f-973324ac9dfe
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B034
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B021
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B003

namespace CKLaneC2R.CompactCover

theorem strip2_s056 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : a ≤ ((17/40 : ℚ) : ℝ)) (h536 : ¬ (a ≤ ((33/80 : ℚ) : ℝ))) (h584 : z ≤ ((217/400 : ℚ) : ℝ)) (h585 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h586 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h587 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h588 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h589 : a ≤ ((67/160 : ℚ) : ℝ)
        · -- left
          by_cases h590 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B034.c681_pos (not_le.mp h536).le h589 hz1 h590
          · -- right
            exact CKLaneC2R.Cells.S02.B034.c683_pos (not_le.mp h536).le h589 (not_le.mp h590).le h588
        · -- right
          by_cases h591 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B034.c682_pos (not_le.mp h589).le h535 hz1 h591
          · -- right
            exact CKLaneC2R.Cells.S02.B034.c684_pos (not_le.mp h589).le h535 (not_le.mp h591).le h588
      · -- right
        by_cases h592 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B020.c410_pos (not_le.mp h536).le h535 (not_le.mp h588).le h592
        · -- right
          exact CKLaneC2R.Cells.S02.B020.c411_pos (not_le.mp h536).le h535 (not_le.mp h592).le h587
    · -- right
      by_cases h593 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h594 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B020.c419_pos (not_le.mp h536).le h535 (not_le.mp h587).le h594
        · -- right
          exact CKLaneC2R.Cells.S02.B021.c420_pos (not_le.mp h536).le h535 (not_le.mp h594).le h593
      · -- right
        by_cases h595 : z ≤ ((2379/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B021.c423_pos (not_le.mp h536).le h535 (not_le.mp h593).le h595
        · -- right
          exact CKLaneC2R.Cells.S02.B021.c424_pos (not_le.mp h536).le h535 (not_le.mp h595).le h586
  · -- right
    by_cases h596 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h597 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        by_cases h598 : a ≤ ((67/160 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B021.c435_pos (not_le.mp h536).le h598 (not_le.mp h586).le h597
        · -- right
          exact CKLaneC2R.Cells.S02.B021.c436_pos (not_le.mp h598).le h535 (not_le.mp h586).le h597
      · -- right
        exact CKLaneC2R.Cells.S02.B003.c66_pos (not_le.mp h536).le h535 (not_le.mp h597).le h596
    · -- right
      by_cases h599 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B003.c69_pos (not_le.mp h536).le h535 (not_le.mp h596).le h599
      · -- right
        exact CKLaneC2R.Cells.S02.B003.c70_pos (not_le.mp h536).le h535 (not_le.mp h599).le h585

end CKLaneC2R.CompactCover


