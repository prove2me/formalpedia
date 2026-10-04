-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g48
-- name    : CK_CKLaneC2R_CompactCover_S02_g48
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T03:37:02.560989+00:00
-- url     : https://prove2.me/theorems/0adafb81-8811-4892-ad90-6a95999040fb
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B037
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B041

namespace CKLaneC2R.CompactCover

theorem strip2_s071 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : ¬ (a ≤ ((9/20 : ℚ) : ℝ))) (h717 : a ≤ ((19/40 : ℚ) : ℝ)) (h718 : a ≤ ((37/80 : ℚ) : ℝ)) (h719 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h738 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h743 : z ≤ ((7079/8000 : ℚ) : ℝ)
  · -- left
    by_cases h744 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h745 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B013.c261_pos (not_le.mp h534).le h718 (not_le.mp h738).le h745
      · -- right
        exact CKLaneC2R.Cells.S02.B013.c262_pos (not_le.mp h534).le h718 (not_le.mp h745).le h744
    · -- right
      by_cases h746 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B013.c269_pos (not_le.mp h534).le h718 (not_le.mp h744).le h746
      · -- right
        exact CKLaneC2R.Cells.S02.B013.c271_pos (not_le.mp h534).le h718 (not_le.mp h746).le h743
  · -- right
    by_cases h747 : z ≤ ((15071/16000 : ℚ) : ℝ)
    · -- left
      by_cases h748 : z ≤ ((29229/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B014.c282_pos (not_le.mp h534).le h718 (not_le.mp h743).le h748
      · -- right
        exact CKLaneC2R.Cells.S02.B014.c284_pos (not_le.mp h534).le h718 (not_le.mp h748).le h747
    · -- right
      by_cases h749 : z ≤ ((6211/6400 : ℚ) : ℝ)
      · -- left
        by_cases h750 : z ≤ ((61197/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B028.c571_pos (not_le.mp h534).le h718 (not_le.mp h747).le h750
        · -- right
          exact CKLaneC2R.Cells.S02.B028.c573_pos (not_le.mp h534).le h718 (not_le.mp h750).le h749
      · -- right
        by_cases h751 : z ≤ ((63023/64000 : ℚ) : ℝ)
        · -- left
          by_cases h752 : z ≤ ((125133/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B036.c739_pos (not_le.mp h534).le h718 (not_le.mp h749).le h752
          · -- right
            exact CKLaneC2R.Cells.S02.B037.c741_pos (not_le.mp h534).le h718 (not_le.mp h752).le h751
        · -- right
          by_cases h753 : z ≤ ((126959/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B037.c751_pos (not_le.mp h534).le h718 (not_le.mp h751).le h753
          · -- right
            by_cases h754 : z ≤ ((254831/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S02.B040.c809_pos (not_le.mp h534).le h718 (not_le.mp h753).le h754
            · -- right
              by_cases h755 : z ≤ ((20423/20480 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S02.B041.c832_pos (not_le.mp h534).le h718 (not_le.mp h754).le h755
              · -- right
                exact CKLaneC2R.Cells.S02.B041.c834_pos (not_le.mp h534).le h718 (not_le.mp h755).le hz2

end CKLaneC2R.CompactCover


