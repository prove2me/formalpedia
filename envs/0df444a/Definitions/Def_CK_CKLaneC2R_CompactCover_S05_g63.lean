-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g63
-- name    : CK_CKLaneC2R_CompactCover_S05_g63
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T09:10:00.003001+00:00
-- url     : https://prove2.me/theorems/af14f4f9-8cd7-416a-87ee-25e3ba247165
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S05 (proof part of strip5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S05 (proof part of strip5).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B033
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B034
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B035
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B036

namespace CKLaneC2R.CompactCover

theorem strip5_s123 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : ¬ (a ≤ ((127773/128000 : ℚ) : ℝ))) (h667 : ¬ (a ≤ ((51129/51200 : ℚ) : ℝ))) (h694 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h703 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h706 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h708 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h710 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h713 : ¬ (z ≤ ((63023/64000 : ℚ) : ℝ))) (h716 : z ≤ ((126959/128000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h717 : z ≤ ((50601/51200 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B032.c647_pos (not_le.mp h667).le ha2 (not_le.mp h713).le h717
  · -- right
    by_cases h718 : a ≤ ((511389/512000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B033.c665_pos (not_le.mp h667).le h718 (not_le.mp h717).le h716
    · -- right
      exact CKLaneC2R.Cells.S05.B033.c666_pos (not_le.mp h718).le ha2 (not_le.mp h717).le h716

theorem strip5_s124 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : ¬ (a ≤ ((127773/128000 : ℚ) : ℝ))) (h667 : ¬ (a ≤ ((51129/51200 : ℚ) : ℝ))) (h694 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h703 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h706 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h708 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h710 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h713 : ¬ (z ≤ ((63023/64000 : ℚ) : ℝ))) (h716 : ¬ (z ≤ ((126959/128000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h719 : z ≤ ((254831/256000 : ℚ) : ℝ)
  · -- left
    by_cases h720 : z ≤ ((508749/512000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B034.c683_pos (not_le.mp h667).le ha2 (not_le.mp h716).le h720
    · -- right
      by_cases h721 : a ≤ ((511389/512000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B034.c690_pos (not_le.mp h667).le h721 (not_le.mp h720).le h719
      · -- right
        exact CKLaneC2R.Cells.S05.B034.c691_pos (not_le.mp h721).le ha2 (not_le.mp h720).le h719
  · -- right
    by_cases h722 : a ≤ ((511389/512000 : ℚ) : ℝ)
    · -- left
      by_cases h723 : z ≤ ((20423/20480 : ℚ) : ℝ)
      · -- left
        by_cases h724 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B035.c710_pos (not_le.mp h667).le h722 (not_le.mp h719).le h724
        · -- right
          exact CKLaneC2R.Cells.S05.B035.c712_pos (not_le.mp h667).le h722 (not_le.mp h724).le h723
      · -- right
        by_cases h725 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B036.c722_pos (not_le.mp h667).le h722 (not_le.mp h723).le h725
        · -- right
          by_cases h726 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B036.c728_pos (not_le.mp h667).le h722 (not_le.mp h725).le h726
          · -- right
            exact CKLaneC2R.Cells.S05.B036.c730_pos (not_le.mp h667).le h722 (not_le.mp h726).le hz2
    · -- right
      by_cases h727 : z ≤ ((20423/20480 : ℚ) : ℝ)
      · -- left
        by_cases h728 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B035.c711_pos (not_le.mp h722).le ha2 (not_le.mp h719).le h728
        · -- right
          exact CKLaneC2R.Cells.S05.B035.c713_pos (not_le.mp h722).le ha2 (not_le.mp h728).le h727
      · -- right
        by_cases h729 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B036.c723_pos (not_le.mp h722).le ha2 (not_le.mp h727).le h729
        · -- right
          by_cases h730 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B036.c729_pos (not_le.mp h722).le ha2 (not_le.mp h729).le h730
          · -- right
            exact CKLaneC2R.Cells.S05.B036.c731_pos (not_le.mp h722).le ha2 (not_le.mp h730).le hz2

end CKLaneC2R.CompactCover


