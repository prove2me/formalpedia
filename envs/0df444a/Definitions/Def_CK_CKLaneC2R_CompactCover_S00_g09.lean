-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g09
-- name    : CK_CKLaneC2R_CompactCover_S00_g09
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T21:29:36.956981+00:00
-- url     : https://prove2.me/theorems/72548acf-390b-4a48-908c-70a20d73d6ac
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B064
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B065
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B070
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B071
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B072
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B073
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B074

namespace CKLaneC2R.CompactCover

theorem strip0_s012 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : a ≤ ((49/320 : ℚ) : ℝ)) (h4 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h78 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h94 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h105 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h113 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h119 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h120 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      by_cases h121 : z ≤ ((249353/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B064.c1299_pos ha1 h3 (not_le.mp h113).le h121
      · -- right
        exact CKLaneC2R.Cells.S00.B065.c1300_pos ha1 h3 (not_le.mp h121).le h120
    · -- right
      by_cases h122 : z ≤ ((251179/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B065.c1307_pos ha1 h3 (not_le.mp h120).le h122
      · -- right
        exact CKLaneC2R.Cells.S00.B065.c1309_pos ha1 h3 (not_le.mp h122).le h119
  · -- right
    by_cases h123 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h124 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        by_cases h125 : z ≤ ((505097/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B070.c1404_pos ha1 h3 (not_le.mp h119).le h125
        · -- right
          exact CKLaneC2R.Cells.S00.B070.c1405_pos ha1 h3 (not_le.mp h125).le h124
      · -- right
        by_cases h126 : z ≤ ((506923/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B070.c1406_pos ha1 h3 (not_le.mp h124).le h126
        · -- right
          exact CKLaneC2R.Cells.S00.B070.c1407_pos ha1 h3 (not_le.mp h126).le h123
    · -- right
      by_cases h127 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        by_cases h128 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B071.c1420_pos ha1 h3 (not_le.mp h123).le h128
        · -- right
          exact CKLaneC2R.Cells.S00.B071.c1422_pos ha1 h3 (not_le.mp h128).le h127
      · -- right
        by_cases h129 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          by_cases h130 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B072.c1456_pos ha1 h3 (not_le.mp h127).le h130
          · -- right
            exact CKLaneC2R.Cells.S00.B072.c1457_pos ha1 h3 (not_le.mp h130).le h129
        · -- right
          by_cases h131 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B073.c1472_pos ha1 h3 (not_le.mp h129).le h131
          · -- right
            by_cases h132 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S00.B074.c1490_pos ha1 h3 (not_le.mp h131).le h132
            · -- right
              exact CKLaneC2R.Cells.S00.B074.c1491_pos ha1 h3 (not_le.mp h132).le hz2

end CKLaneC2R.CompactCover


