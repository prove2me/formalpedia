-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g63
-- name    : CK_CKLaneC2R_CompactCover_S01_g63
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T22:56:23.315956+00:00
-- url     : https://prove2.me/theorems/c3d1573e-6dcf-4358-b03a-67b8e59f30e0
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B030
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B045
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B046
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B055
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B057
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B058
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B059

namespace CKLaneC2R.CompactCover

theorem strip1_s090 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) (h748 : ¬ (a ≤ ((41/160 : ℚ) : ℝ))) (h817 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h851 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h859 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h865 : z ≤ ((15071/16000 : ℚ) : ℝ)
  · -- left
    by_cases h866 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h867 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B029.c593_pos (not_le.mp h748).le h747 (not_le.mp h859).le h867
      · -- right
        exact CKLaneC2R.Cells.S01.B029.c594_pos (not_le.mp h748).le h747 (not_le.mp h867).le h866
    · -- right
      by_cases h868 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B030.c600_pos (not_le.mp h748).le h747 (not_le.mp h866).le h868
      · -- right
        exact CKLaneC2R.Cells.S01.B030.c602_pos (not_le.mp h748).le h747 (not_le.mp h868).le h865
  · -- right
    by_cases h869 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h870 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B031.c623_pos (not_le.mp h748).le h747 (not_le.mp h865).le h870
      · -- right
        by_cases h871 : z ≤ ((123307/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B045.c917_pos (not_le.mp h748).le h747 (not_le.mp h870).le h871
        · -- right
          exact CKLaneC2R.Cells.S01.B045.c918_pos (not_le.mp h748).le h747 (not_le.mp h871).le h869
    · -- right
      by_cases h872 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        by_cases h873 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B046.c934_pos (not_le.mp h748).le h747 (not_le.mp h869).le h873
        · -- right
          exact CKLaneC2R.Cells.S01.B046.c936_pos (not_le.mp h748).le h747 (not_le.mp h873).le h872
      · -- right
        by_cases h874 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          by_cases h875 : z ≤ ((50601/51200 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B055.c1109_pos (not_le.mp h748).le h747 (not_le.mp h872).le h875
          · -- right
            exact CKLaneC2R.Cells.S01.B055.c1111_pos (not_le.mp h748).le h747 (not_le.mp h875).le h874
        · -- right
          by_cases h876 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            by_cases h877 : z ≤ ((508749/512000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S01.B057.c1155_pos (not_le.mp h748).le h747 (not_le.mp h874).le h877
            · -- right
              exact CKLaneC2R.Cells.S01.B057.c1156_pos (not_le.mp h748).le h747 (not_le.mp h877).le h876
          · -- right
            by_cases h878 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S01.B058.c1164_pos (not_le.mp h748).le h747 (not_le.mp h876).le h878
            · -- right
              by_cases h879 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S01.B059.c1191_pos (not_le.mp h748).le h747 (not_le.mp h878).le h879
              · -- right
                exact CKLaneC2R.Cells.S01.B059.c1193_pos (not_le.mp h748).le h747 (not_le.mp h879).le hz2

end CKLaneC2R.CompactCover


