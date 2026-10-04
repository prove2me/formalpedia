-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g45
-- name    : CK_CKLaneC2R_CompactCover_S00_g45
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T15:52:46.63826+00:00
-- url     : https://prove2.me/theorems/ca5f5fbc-1ef8-4493-86e4-a641f3d29f86
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
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B074

namespace CKLaneC2R.CompactCover

theorem strip0_s054 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : a ≤ ((53/320 : ℚ) : ℝ)) (h483 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h542 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h558 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h566 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h573 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h577 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h578 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      by_cases h579 : z ≤ ((249353/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B065.c1315_pos (not_le.mp h1).le h482 (not_le.mp h573).le h579
      · -- right
        exact CKLaneC2R.Cells.S00.B065.c1316_pos (not_le.mp h1).le h482 (not_le.mp h579).le h578
    · -- right
      by_cases h580 : z ≤ ((251179/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B066.c1323_pos (not_le.mp h1).le h482 (not_le.mp h578).le h580
      · -- right
        exact CKLaneC2R.Cells.S00.B066.c1325_pos (not_le.mp h1).le h482 (not_le.mp h580).le h577
  · -- right
    by_cases h581 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h582 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B067.c1346_pos (not_le.mp h1).le h482 (not_le.mp h577).le h582
      · -- right
        by_cases h583 : z ≤ ((506923/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B070.c1414_pos (not_le.mp h1).le h482 (not_le.mp h582).le h583
        · -- right
          exact CKLaneC2R.Cells.S00.B070.c1415_pos (not_le.mp h1).le h482 (not_le.mp h583).le h581
    · -- right
      by_cases h584 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        by_cases h585 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B071.c1428_pos (not_le.mp h1).le h482 (not_le.mp h581).le h585
        · -- right
          exact CKLaneC2R.Cells.S00.B071.c1430_pos (not_le.mp h1).le h482 (not_le.mp h585).le h584
      · -- right
        by_cases h586 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          by_cases h587 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B073.c1464_pos (not_le.mp h1).le h482 (not_le.mp h584).le h587
          · -- right
            exact CKLaneC2R.Cells.S00.B073.c1465_pos (not_le.mp h1).le h482 (not_le.mp h587).le h586
        · -- right
          by_cases h588 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B073.c1476_pos (not_le.mp h1).le h482 (not_le.mp h586).le h588
          · -- right
            by_cases h589 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S00.B074.c1498_pos (not_le.mp h1).le h482 (not_le.mp h588).le h589
            · -- right
              exact CKLaneC2R.Cells.S00.B074.c1499_pos (not_le.mp h1).le h482 (not_le.mp h589).le hz2

end CKLaneC2R.CompactCover


