-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g09
-- name    : CK_CKLaneC2R_CompactCover_S03_g09
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T03:36:42.4799+00:00
-- url     : https://prove2.me/theorems/5631e43e-cbb9-4ff8-bdd1-a8e0175850ae
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S03 (proof part of strip3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S03 (proof part of strip3).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B019

namespace CKLaneC2R.CompactCover

theorem strip3_s014 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((11/20 : ℚ) : ℝ))) (h119 : a ≤ ((23/40 : ℚ) : ℝ)) (h120 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h145 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h153 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h158 : z ≤ ((15071/16000 : ℚ) : ℝ)
  · -- left
    by_cases h159 : a ≤ ((9/16 : ℚ) : ℝ)
    · -- left
      by_cases h160 : z ≤ ((29229/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B013.c266_pos (not_le.mp h1).le h159 (not_le.mp h153).le h160
      · -- right
        exact CKLaneC2R.Cells.S03.B013.c268_pos (not_le.mp h1).le h159 (not_le.mp h160).le h158
    · -- right
      by_cases h161 : z ≤ ((29229/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B013.c267_pos (not_le.mp h159).le h119 (not_le.mp h153).le h161
      · -- right
        exact CKLaneC2R.Cells.S03.B013.c269_pos (not_le.mp h159).le h119 (not_le.mp h161).le h158
  · -- right
    by_cases h162 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h163 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B014.c291_pos (not_le.mp h1).le h119 (not_le.mp h158).le h163
      · -- right
        by_cases h164 : a ≤ ((9/16 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B017.c344_pos (not_le.mp h1).le h164 (not_le.mp h163).le h162
        · -- right
          exact CKLaneC2R.Cells.S03.B017.c345_pos (not_le.mp h164).le h119 (not_le.mp h163).le h162
    · -- right
      by_cases h165 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        by_cases h166 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B017.c350_pos (not_le.mp h1).le h119 (not_le.mp h162).le h166
        · -- right
          exact CKLaneC2R.Cells.S03.B017.c351_pos (not_le.mp h1).le h119 (not_le.mp h166).le h165
      · -- right
        by_cases h167 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          by_cases h168 : a ≤ ((9/16 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B018.c371_pos (not_le.mp h1).le h168 (not_le.mp h165).le h167
          · -- right
            exact CKLaneC2R.Cells.S03.B018.c372_pos (not_le.mp h168).le h119 (not_le.mp h165).le h167
        · -- right
          by_cases h169 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B018.c375_pos (not_le.mp h1).le h119 (not_le.mp h167).le h169
          · -- right
            by_cases h170 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S03.B019.c383_pos (not_le.mp h1).le h119 (not_le.mp h169).le h170
            · -- right
              by_cases h171 : a ≤ ((9/16 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S03.B019.c397_pos (not_le.mp h1).le h171 (not_le.mp h170).le hz2
              · -- right
                exact CKLaneC2R.Cells.S03.B019.c398_pos (not_le.mp h171).le h119 (not_le.mp h170).le hz2

end CKLaneC2R.CompactCover


