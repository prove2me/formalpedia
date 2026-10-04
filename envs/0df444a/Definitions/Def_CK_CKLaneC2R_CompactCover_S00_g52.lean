-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g52
-- name    : CK_CKLaneC2R_CompactCover_S00_g52
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T11:01:44.835987+00:00
-- url     : https://prove2.me/theorems/abf89de3-42d9-4396-8bbe-8e735434b639
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B065
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B066
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B067
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B070
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B071
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B073
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B075

namespace CKLaneC2R.CompactCover

theorem strip0_s063 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : ¬ (a ≤ ((53/320 : ℚ) : ℝ))) (h590 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h645 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h661 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h669 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h676 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h680 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h681 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      by_cases h682 : z ≤ ((249353/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B065.c1317_pos (not_le.mp h482).le h481 (not_le.mp h676).le h682
      · -- right
        exact CKLaneC2R.Cells.S00.B065.c1318_pos (not_le.mp h482).le h481 (not_le.mp h682).le h681
    · -- right
      by_cases h683 : z ≤ ((251179/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B066.c1324_pos (not_le.mp h482).le h481 (not_le.mp h681).le h683
      · -- right
        exact CKLaneC2R.Cells.S00.B066.c1326_pos (not_le.mp h482).le h481 (not_le.mp h683).le h680
  · -- right
    by_cases h684 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h685 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B067.c1347_pos (not_le.mp h482).le h481 (not_le.mp h680).le h685
      · -- right
        by_cases h686 : z ≤ ((506923/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B070.c1416_pos (not_le.mp h482).le h481 (not_le.mp h685).le h686
        · -- right
          exact CKLaneC2R.Cells.S00.B070.c1417_pos (not_le.mp h482).le h481 (not_le.mp h686).le h684
    · -- right
      by_cases h687 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        by_cases h688 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B071.c1429_pos (not_le.mp h482).le h481 (not_le.mp h684).le h688
        · -- right
          exact CKLaneC2R.Cells.S00.B071.c1431_pos (not_le.mp h482).le h481 (not_le.mp h688).le h687
      · -- right
        by_cases h689 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          by_cases h690 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B073.c1466_pos (not_le.mp h482).le h481 (not_le.mp h687).le h690
          · -- right
            exact CKLaneC2R.Cells.S00.B073.c1467_pos (not_le.mp h482).le h481 (not_le.mp h690).le h689
        · -- right
          by_cases h691 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B073.c1477_pos (not_le.mp h482).le h481 (not_le.mp h689).le h691
          · -- right
            by_cases h692 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S00.B075.c1500_pos (not_le.mp h482).le h481 (not_le.mp h691).le h692
            · -- right
              exact CKLaneC2R.Cells.S00.B075.c1501_pos (not_le.mp h482).le h481 (not_le.mp h692).le hz2

end CKLaneC2R.CompactCover


