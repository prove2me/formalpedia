-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g56
-- name    : CK_CKLaneC2R_CompactCover_S05_g56
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T01:31:20.515987+00:00
-- url     : https://prove2.me/theorems/5620abc0-8564-427e-a280-305c5508680d
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B033
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B034
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B035

namespace CKLaneC2R.CompactCover

theorem strip5_s103 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : a ≤ ((127773/128000 : ℚ) : ℝ)) (h617 : a ≤ ((255447/256000 : ℚ) : ℝ)) (h618 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h623 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h625 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h627 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h629 : z ≤ ((6211/6400 : ℚ) : ℝ)
  · -- left
    by_cases h630 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B027.c540_pos (not_le.mp h550).le h617 (not_le.mp h627).le h630
    · -- right
      exact CKLaneC2R.Cells.S05.B027.c544_pos (not_le.mp h550).le h617 (not_le.mp h630).le h629
  · -- right
    by_cases h631 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h632 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B029.c599_pos (not_le.mp h550).le h617 (not_le.mp h629).le h632
      · -- right
        by_cases h633 : z ≤ ((251179/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B031.c622_pos (not_le.mp h550).le h617 (not_le.mp h632).le h633
        · -- right
          exact CKLaneC2R.Cells.S05.B031.c624_pos (not_le.mp h550).le h617 (not_le.mp h633).le h631
    · -- right
      by_cases h634 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        by_cases h635 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B032.c644_pos (not_le.mp h550).le h617 (not_le.mp h631).le h635
        · -- right
          exact CKLaneC2R.Cells.S05.B032.c648_pos (not_le.mp h550).le h617 (not_le.mp h635).le h634
      · -- right
        by_cases h636 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          by_cases h637 : z ≤ ((508749/512000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B033.c678_pos (not_le.mp h550).le h617 (not_le.mp h634).le h637
          · -- right
            exact CKLaneC2R.Cells.S05.B034.c680_pos (not_le.mp h550).le h617 (not_le.mp h637).le h636
        · -- right
          by_cases h638 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            by_cases h639 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B035.c701_pos (not_le.mp h550).le h617 (not_le.mp h636).le h639
            · -- right
              exact CKLaneC2R.Cells.S05.B035.c703_pos (not_le.mp h550).le h617 (not_le.mp h639).le h638
          · -- right
            by_cases h640 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B035.c707_pos (not_le.mp h550).le h617 (not_le.mp h638).le h640
            · -- right
              by_cases h641 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B035.c716_pos (not_le.mp h550).le h617 (not_le.mp h640).le h641
              · -- right
                exact CKLaneC2R.Cells.S05.B035.c717_pos (not_le.mp h550).le h617 (not_le.mp h641).le hz2

end CKLaneC2R.CompactCover


