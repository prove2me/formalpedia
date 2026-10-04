-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g14
-- name    : CK_CKLaneC2R_CompactCover_S05_g14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T21:59:35.883914+00:00
-- url     : https://prove2.me/theorems/d0b053f6-2281-4f43-b018-edd24758f08d
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B021
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B024

namespace CKLaneC2R.CompactCover

theorem strip5_s022 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : a ≤ ((1539/1600 : ℚ) : ℝ)) (h149 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h159 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h165 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h172 : ¬ (a ≤ ((15291/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h185 : z ≤ ((15071/16000 : ℚ) : ℝ)
  · -- left
    by_cases h186 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B010.c202_pos (not_le.mp h172).le h148 (not_le.mp h165).le h186
    · -- right
      by_cases h187 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B013.c279_pos (not_le.mp h172).le h148 (not_le.mp h186).le h187
      · -- right
        exact CKLaneC2R.Cells.S05.B014.c280_pos (not_le.mp h172).le h148 (not_le.mp h187).le h185
  · -- right
    by_cases h188 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h189 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B014.c291_pos (not_le.mp h172).le h148 (not_le.mp h185).le h189
      · -- right
        by_cases h190 : z ≤ ((123307/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B017.c359_pos (not_le.mp h172).le h148 (not_le.mp h189).le h190
        · -- right
          exact CKLaneC2R.Cells.S05.B018.c360_pos (not_le.mp h172).le h148 (not_le.mp h190).le h188
    · -- right
      by_cases h191 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        by_cases h192 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B018.c370_pos (not_le.mp h172).le h148 (not_le.mp h188).le h192
        · -- right
          by_cases h193 : a ≤ ((30681/32000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B021.c421_pos (not_le.mp h172).le h193 (not_le.mp h192).le h191
          · -- right
            exact CKLaneC2R.Cells.S05.B021.c422_pos (not_le.mp h193).le h148 (not_le.mp h192).le h191
      · -- right
        by_cases h194 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          by_cases h195 : a ≤ ((30681/32000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B021.c433_pos (not_le.mp h172).le h195 (not_le.mp h191).le h194
          · -- right
            exact CKLaneC2R.Cells.S05.B021.c434_pos (not_le.mp h195).le h148 (not_le.mp h191).le h194
        · -- right
          by_cases h196 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            by_cases h197 : a ≤ ((30681/32000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B024.c489_pos (not_le.mp h172).le h197 (not_le.mp h194).le h196
            · -- right
              exact CKLaneC2R.Cells.S05.B024.c490_pos (not_le.mp h197).le h148 (not_le.mp h194).le h196
          · -- right
            by_cases h198 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B024.c493_pos (not_le.mp h172).le h148 (not_le.mp h196).le h198
            · -- right
              exact CKLaneC2R.Cells.S05.B024.c494_pos (not_le.mp h172).le h148 (not_le.mp h198).le hz2

end CKLaneC2R.CompactCover


