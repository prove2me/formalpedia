-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g60
-- name    : CK_CKLaneC2R_CompactCover_S05_g60
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T13:06:46.150131+00:00
-- url     : https://prove2.me/theorems/db74d13a-f458-4f83-80d0-708b909171d4
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
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B034
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B035
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B036

namespace CKLaneC2R.CompactCover

theorem strip5_s116 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : ¬ (a ≤ ((127773/128000 : ℚ) : ℝ))) (h667 : a ≤ ((51129/51200 : ℚ) : ℝ)) (h668 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h673 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h675 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h677 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h679 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h681 : ¬ (z ≤ ((63023/64000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h683 : z ≤ ((126959/128000 : ℚ) : ℝ)
  · -- left
    by_cases h684 : z ≤ ((50601/51200 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B032.c646_pos (not_le.mp h616).le h667 (not_le.mp h681).le h684
    · -- right
      exact CKLaneC2R.Cells.S05.B032.c650_pos (not_le.mp h616).le h667 (not_le.mp h684).le h683
  · -- right
    by_cases h685 : z ≤ ((254831/256000 : ℚ) : ℝ)
    · -- left
      by_cases h686 : z ≤ ((508749/512000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B034.c682_pos (not_le.mp h616).le h667 (not_le.mp h683).le h686
      · -- right
        exact CKLaneC2R.Cells.S05.B034.c684_pos (not_le.mp h616).le h667 (not_le.mp h686).le h685
    · -- right
      by_cases h687 : z ≤ ((20423/20480 : ℚ) : ℝ)
      · -- left
        by_cases h688 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B035.c705_pos (not_le.mp h616).le h667 (not_le.mp h685).le h688
        · -- right
          exact CKLaneC2R.Cells.S05.B035.c706_pos (not_le.mp h616).le h667 (not_le.mp h688).le h687
      · -- right
        by_cases h689 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
        · -- left
          by_cases h690 : z ≤ ((2043213/2048000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B036.c720_pos (not_le.mp h616).le h667 (not_le.mp h687).le h690
          · -- right
            exact CKLaneC2R.Cells.S05.B036.c721_pos (not_le.mp h616).le h667 (not_le.mp h690).le h689
        · -- right
          by_cases h691 : a ≤ ((511191/512000 : ℚ) : ℝ)
          · -- left
            by_cases h692 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B036.c724_pos (not_le.mp h616).le h691 (not_le.mp h689).le h692
            · -- right
              exact CKLaneC2R.Cells.S05.B036.c726_pos (not_le.mp h616).le h691 (not_le.mp h692).le hz2
          · -- right
            by_cases h693 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B036.c725_pos (not_le.mp h691).le h667 (not_le.mp h689).le h693
            · -- right
              exact CKLaneC2R.Cells.S05.B036.c727_pos (not_le.mp h691).le h667 (not_le.mp h693).le hz2

end CKLaneC2R.CompactCover


