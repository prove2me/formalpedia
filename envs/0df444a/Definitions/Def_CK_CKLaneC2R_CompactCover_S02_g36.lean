-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g36
-- name    : CK_CKLaneC2R_CompactCover_S02_g36
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T08:15:17.3695+00:00
-- url     : https://prove2.me/theorems/2557a54e-33ec-40e5-ade8-92ab0217d231
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B037
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B042

namespace CKLaneC2R.CompactCover

theorem strip2_s055 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : a ≤ ((17/40 : ℚ) : ℝ)) (h536 : a ≤ ((33/80 : ℚ) : ℝ)) (h537 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h561 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h569 : z ≤ ((7079/8000 : ℚ) : ℝ)
  · -- left
    by_cases h570 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h571 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B012.c245_pos (not_le.mp h0).le h536 (not_le.mp h561).le h571
      · -- right
        exact CKLaneC2R.Cells.S02.B012.c246_pos (not_le.mp h0).le h536 (not_le.mp h571).le h570
    · -- right
      by_cases h572 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B012.c253_pos (not_le.mp h0).le h536 (not_le.mp h570).le h572
      · -- right
        exact CKLaneC2R.Cells.S02.B012.c255_pos (not_le.mp h0).le h536 (not_le.mp h572).le h569
  · -- right
    by_cases h573 : z ≤ ((15071/16000 : ℚ) : ℝ)
    · -- left
      by_cases h574 : z ≤ ((29229/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B013.c278_pos (not_le.mp h0).le h536 (not_le.mp h569).le h574
      · -- right
        by_cases h575 : z ≤ ((59371/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B027.c547_pos (not_le.mp h0).le h536 (not_le.mp h574).le h575
        · -- right
          exact CKLaneC2R.Cells.S02.B027.c548_pos (not_le.mp h0).le h536 (not_le.mp h575).le h573
    · -- right
      by_cases h576 : z ≤ ((6211/6400 : ℚ) : ℝ)
      · -- left
        by_cases h577 : z ≤ ((61197/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B028.c563_pos (not_le.mp h0).le h536 (not_le.mp h573).le h577
        · -- right
          exact CKLaneC2R.Cells.S02.B028.c565_pos (not_le.mp h0).le h536 (not_le.mp h577).le h576
      · -- right
        by_cases h578 : z ≤ ((63023/64000 : ℚ) : ℝ)
        · -- left
          by_cases h579 : z ≤ ((125133/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B036.c731_pos (not_le.mp h0).le h536 (not_le.mp h576).le h579
          · -- right
            exact CKLaneC2R.Cells.S02.B036.c733_pos (not_le.mp h0).le h536 (not_le.mp h579).le h578
        · -- right
          by_cases h580 : z ≤ ((126959/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B037.c747_pos (not_le.mp h0).le h536 (not_le.mp h578).le h580
          · -- right
            by_cases h581 : z ≤ ((254831/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S02.B040.c805_pos (not_le.mp h0).le h536 (not_le.mp h580).le h581
            · -- right
              by_cases h582 : z ≤ ((20423/20480 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S02.B041.c826_pos (not_le.mp h0).le h536 (not_le.mp h581).le h582
              · -- right
                by_cases h583 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S02.B042.c854_pos (not_le.mp h0).le h536 (not_le.mp h582).le h583
                · -- right
                  exact CKLaneC2R.Cells.S02.B042.c855_pos (not_le.mp h0).le h536 (not_le.mp h583).le hz2

end CKLaneC2R.CompactCover


