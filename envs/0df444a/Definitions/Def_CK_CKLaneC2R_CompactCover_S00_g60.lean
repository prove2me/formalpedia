-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g60
-- name    : CK_CKLaneC2R_CompactCover_S00_g60
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T09:44:31.477982+00:00
-- url     : https://prove2.me/theorems/d41ca8a0-cae2-426a-8bd5-6bd731afe5b8
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

theorem strip0_s072 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : a ≤ ((11/64 : ℚ) : ℝ)) (h694 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h747 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h763 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h771 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h777 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h781 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h782 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      by_cases h783 : z ≤ ((249353/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B065.c1319_pos (not_le.mp h481).le h693 (not_le.mp h777).le h783
      · -- right
        exact CKLaneC2R.Cells.S00.B066.c1320_pos (not_le.mp h481).le h693 (not_le.mp h783).le h782
    · -- right
      by_cases h784 : z ≤ ((251179/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B066.c1327_pos (not_le.mp h481).le h693 (not_le.mp h782).le h784
      · -- right
        exact CKLaneC2R.Cells.S00.B066.c1329_pos (not_le.mp h481).le h693 (not_le.mp h784).le h781
  · -- right
    by_cases h785 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h786 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B067.c1348_pos (not_le.mp h481).le h693 (not_le.mp h781).le h786
      · -- right
        by_cases h787 : z ≤ ((506923/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B070.c1418_pos (not_le.mp h481).le h693 (not_le.mp h786).le h787
        · -- right
          exact CKLaneC2R.Cells.S00.B070.c1419_pos (not_le.mp h481).le h693 (not_le.mp h787).le h785
    · -- right
      by_cases h788 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        by_cases h789 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B071.c1432_pos (not_le.mp h481).le h693 (not_le.mp h785).le h789
        · -- right
          exact CKLaneC2R.Cells.S00.B071.c1434_pos (not_le.mp h481).le h693 (not_le.mp h789).le h788
      · -- right
        by_cases h790 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          by_cases h791 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B073.c1468_pos (not_le.mp h481).le h693 (not_le.mp h788).le h791
          · -- right
            exact CKLaneC2R.Cells.S00.B073.c1469_pos (not_le.mp h481).le h693 (not_le.mp h791).le h790
        · -- right
          by_cases h792 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B073.c1478_pos (not_le.mp h481).le h693 (not_le.mp h790).le h792
          · -- right
            by_cases h793 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S00.B075.c1502_pos (not_le.mp h481).le h693 (not_le.mp h792).le h793
            · -- right
              exact CKLaneC2R.Cells.S00.B075.c1503_pos (not_le.mp h481).le h693 (not_le.mp h793).le hz2

end CKLaneC2R.CompactCover


