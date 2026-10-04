-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g51
-- name    : CK_CKLaneC2R_CompactCover_S02_g51
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T14:24:32.238728+00:00
-- url     : https://prove2.me/theorems/766d6205-c816-411c-8219-9b685421524a
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
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B037
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B041

namespace CKLaneC2R.CompactCover

theorem strip2_s075 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : ¬ (a ≤ ((9/20 : ℚ) : ℝ))) (h717 : a ≤ ((19/40 : ℚ) : ℝ)) (h718 : ¬ (a ≤ ((37/80 : ℚ) : ℝ))) (h756 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h774 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h779 : z ≤ ((7079/8000 : ℚ) : ℝ)
  · -- left
    by_cases h780 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h781 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B013.c263_pos (not_le.mp h718).le h717 (not_le.mp h774).le h781
      · -- right
        exact CKLaneC2R.Cells.S02.B013.c264_pos (not_le.mp h718).le h717 (not_le.mp h781).le h780
    · -- right
      by_cases h782 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B013.c270_pos (not_le.mp h718).le h717 (not_le.mp h780).le h782
      · -- right
        exact CKLaneC2R.Cells.S02.B013.c272_pos (not_le.mp h718).le h717 (not_le.mp h782).le h779
  · -- right
    by_cases h783 : z ≤ ((15071/16000 : ℚ) : ℝ)
    · -- left
      by_cases h784 : z ≤ ((29229/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B014.c283_pos (not_le.mp h718).le h717 (not_le.mp h779).le h784
      · -- right
        exact CKLaneC2R.Cells.S02.B014.c285_pos (not_le.mp h718).le h717 (not_le.mp h784).le h783
    · -- right
      by_cases h785 : z ≤ ((6211/6400 : ℚ) : ℝ)
      · -- left
        by_cases h786 : z ≤ ((61197/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B028.c572_pos (not_le.mp h718).le h717 (not_le.mp h783).le h786
        · -- right
          exact CKLaneC2R.Cells.S02.B028.c574_pos (not_le.mp h718).le h717 (not_le.mp h786).le h785
      · -- right
        by_cases h787 : z ≤ ((63023/64000 : ℚ) : ℝ)
        · -- left
          by_cases h788 : z ≤ ((125133/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B037.c740_pos (not_le.mp h718).le h717 (not_le.mp h785).le h788
          · -- right
            exact CKLaneC2R.Cells.S02.B037.c742_pos (not_le.mp h718).le h717 (not_le.mp h788).le h787
        · -- right
          by_cases h789 : z ≤ ((126959/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B037.c752_pos (not_le.mp h718).le h717 (not_le.mp h787).le h789
          · -- right
            by_cases h790 : z ≤ ((254831/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S02.B040.c810_pos (not_le.mp h718).le h717 (not_le.mp h789).le h790
            · -- right
              by_cases h791 : z ≤ ((20423/20480 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S02.B041.c833_pos (not_le.mp h718).le h717 (not_le.mp h790).le h791
              · -- right
                exact CKLaneC2R.Cells.S02.B041.c835_pos (not_le.mp h718).le h717 (not_le.mp h791).le hz2

end CKLaneC2R.CompactCover


