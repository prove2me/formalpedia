-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g39
-- name    : CK_CKLaneC2R_CompactCover_S02_g39
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T06:15:58.161832+00:00
-- url     : https://prove2.me/theorems/d45bf670-f074-4fc8-b88e-30ddcbef7c83
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

theorem strip2_s059 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : a ≤ ((17/40 : ℚ) : ℝ)) (h536 : ¬ (a ≤ ((33/80 : ℚ) : ℝ))) (h584 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h607 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h615 : z ≤ ((7079/8000 : ℚ) : ℝ)
  · -- left
    by_cases h616 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h617 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B012.c247_pos (not_le.mp h536).le h535 (not_le.mp h607).le h617
      · -- right
        exact CKLaneC2R.Cells.S02.B012.c248_pos (not_le.mp h536).le h535 (not_le.mp h617).le h616
    · -- right
      by_cases h618 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B012.c254_pos (not_le.mp h536).le h535 (not_le.mp h616).le h618
      · -- right
        exact CKLaneC2R.Cells.S02.B012.c256_pos (not_le.mp h536).le h535 (not_le.mp h618).le h615
  · -- right
    by_cases h619 : z ≤ ((15071/16000 : ℚ) : ℝ)
    · -- left
      by_cases h620 : z ≤ ((29229/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B013.c279_pos (not_le.mp h536).le h535 (not_le.mp h615).le h620
      · -- right
        by_cases h621 : z ≤ ((59371/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B027.c549_pos (not_le.mp h536).le h535 (not_le.mp h620).le h621
        · -- right
          exact CKLaneC2R.Cells.S02.B027.c550_pos (not_le.mp h536).le h535 (not_le.mp h621).le h619
    · -- right
      by_cases h622 : z ≤ ((6211/6400 : ℚ) : ℝ)
      · -- left
        by_cases h623 : z ≤ ((61197/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B028.c564_pos (not_le.mp h536).le h535 (not_le.mp h619).le h623
        · -- right
          exact CKLaneC2R.Cells.S02.B028.c566_pos (not_le.mp h536).le h535 (not_le.mp h623).le h622
      · -- right
        by_cases h624 : z ≤ ((63023/64000 : ℚ) : ℝ)
        · -- left
          by_cases h625 : z ≤ ((125133/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B036.c732_pos (not_le.mp h536).le h535 (not_le.mp h622).le h625
          · -- right
            exact CKLaneC2R.Cells.S02.B036.c734_pos (not_le.mp h536).le h535 (not_le.mp h625).le h624
        · -- right
          by_cases h626 : z ≤ ((126959/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B037.c748_pos (not_le.mp h536).le h535 (not_le.mp h624).le h626
          · -- right
            by_cases h627 : z ≤ ((254831/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S02.B040.c806_pos (not_le.mp h536).le h535 (not_le.mp h626).le h627
            · -- right
              by_cases h628 : z ≤ ((20423/20480 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S02.B041.c827_pos (not_le.mp h536).le h535 (not_le.mp h627).le h628
              · -- right
                by_cases h629 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S02.B042.c856_pos (not_le.mp h536).le h535 (not_le.mp h628).le h629
                · -- right
                  exact CKLaneC2R.Cells.S02.B042.c857_pos (not_le.mp h536).le h535 (not_le.mp h629).le hz2

end CKLaneC2R.CompactCover


