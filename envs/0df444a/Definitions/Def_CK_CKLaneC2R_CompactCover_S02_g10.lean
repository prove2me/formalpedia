-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g10
-- name    : CK_CKLaneC2R_CompactCover_S02_g10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T23:50:31.114259+00:00
-- url     : https://prove2.me/theorems/52aca45a-c459-4fda-9100-bd73366cde54
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B035
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B039
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B042

namespace CKLaneC2R.CompactCover

theorem strip2_s014 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : a ≤ ((13/40 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((5/16 : ℚ) : ℝ))) (h93 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h138 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h154 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h162 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h163 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h164 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B026.c521_pos (not_le.mp h3).le h2 (not_le.mp h154).le h164
    · -- right
      exact CKLaneC2R.Cells.S02.B026.c522_pos (not_le.mp h3).le h2 (not_le.mp h164).le h163
  · -- right
    by_cases h165 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B026.c523_pos (not_le.mp h3).le h2 (not_le.mp h163).le h165
    · -- right
      exact CKLaneC2R.Cells.S02.B026.c524_pos (not_le.mp h3).le h2 (not_le.mp h165).le h162

theorem strip2_s015 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : a ≤ ((13/40 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((5/16 : ℚ) : ℝ))) (h93 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h138 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h154 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h162 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h166 : z ≤ ((6211/6400 : ℚ) : ℝ)
  · -- left
    by_cases h167 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      by_cases h168 : a ≤ ((51/160 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B035.c703_pos (not_le.mp h3).le h168 (not_le.mp h162).le h167
      · -- right
        exact CKLaneC2R.Cells.S02.B035.c704_pos (not_le.mp h168).le h2 (not_le.mp h162).le h167
    · -- right
      by_cases h169 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B035.c707_pos (not_le.mp h3).le h2 (not_le.mp h167).le h169
      · -- right
        exact CKLaneC2R.Cells.S02.B035.c708_pos (not_le.mp h3).le h2 (not_le.mp h169).le h166
  · -- right
    by_cases h170 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h171 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B035.c718_pos (not_le.mp h3).le h2 (not_le.mp h166).le h171
      · -- right
        by_cases h172 : a ≤ ((51/160 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B039.c781_pos (not_le.mp h3).le h172 (not_le.mp h171).le h170
        · -- right
          exact CKLaneC2R.Cells.S02.B039.c782_pos (not_le.mp h172).le h2 (not_le.mp h171).le h170
    · -- right
      by_cases h173 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        by_cases h174 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B039.c785_pos (not_le.mp h3).le h2 (not_le.mp h170).le h174
        · -- right
          exact CKLaneC2R.Cells.S02.B039.c786_pos (not_le.mp h3).le h2 (not_le.mp h174).le h173
      · -- right
        by_cases h175 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          by_cases h176 : z ≤ ((508749/512000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B040.c816_pos (not_le.mp h3).le h2 (not_le.mp h173).le h176
          · -- right
            exact CKLaneC2R.Cells.S02.B040.c817_pos (not_le.mp h3).le h2 (not_le.mp h176).le h175
        · -- right
          by_cases h177 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B040.c819_pos (not_le.mp h3).le h2 (not_le.mp h175).le h177
          · -- right
            by_cases h178 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S02.B042.c840_pos (not_le.mp h3).le h2 (not_le.mp h177).le h178
            · -- right
              exact CKLaneC2R.Cells.S02.B042.c841_pos (not_le.mp h3).le h2 (not_le.mp h178).le hz2

end CKLaneC2R.CompactCover


