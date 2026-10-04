-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g16
-- name    : CK_CKLaneC2R_CompactCover_S01_g16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T15:35:59.895724+00:00
-- url     : https://prove2.me/theorems/72cace57-bb17-463a-aa76-cee97af2a5a9
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B053
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B054
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B056
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B057
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B058
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B060

namespace CKLaneC2R.CompactCover

theorem strip1_s021 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((33/160 : ℚ) : ℝ))) (h118 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h175 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h191 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h199 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h207 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h211 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h212 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      by_cases h213 : z ≤ ((249353/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B053.c1076_pos (not_le.mp h3).le h2 (not_le.mp h207).le h213
      · -- right
        exact CKLaneC2R.Cells.S01.B053.c1077_pos (not_le.mp h3).le h2 (not_le.mp h213).le h212
    · -- right
      by_cases h214 : z ≤ ((251179/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B054.c1080_pos (not_le.mp h3).le h2 (not_le.mp h212).le h214
      · -- right
        exact CKLaneC2R.Cells.S01.B054.c1081_pos (not_le.mp h3).le h2 (not_le.mp h214).le h211
  · -- right
    by_cases h215 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h216 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B054.c1095_pos (not_le.mp h3).le h2 (not_le.mp h211).le h216
      · -- right
        by_cases h217 : z ≤ ((506923/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B056.c1135_pos (not_le.mp h3).le h2 (not_le.mp h216).le h217
        · -- right
          exact CKLaneC2R.Cells.S01.B056.c1136_pos (not_le.mp h3).le h2 (not_le.mp h217).le h215
    · -- right
      by_cases h218 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        by_cases h219 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B056.c1139_pos (not_le.mp h3).le h2 (not_le.mp h215).le h219
        · -- right
          exact CKLaneC2R.Cells.S01.B057.c1140_pos (not_le.mp h3).le h2 (not_le.mp h219).le h218
      · -- right
        by_cases h220 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          by_cases h221 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B058.c1174_pos (not_le.mp h3).le h2 (not_le.mp h218).le h221
          · -- right
            exact CKLaneC2R.Cells.S01.B058.c1175_pos (not_le.mp h3).le h2 (not_le.mp h221).le h220
        · -- right
          by_cases h222 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B058.c1177_pos (not_le.mp h3).le h2 (not_le.mp h220).le h222
          · -- right
            by_cases h223 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S01.B060.c1202_pos (not_le.mp h3).le h2 (not_le.mp h222).le h223
            · -- right
              exact CKLaneC2R.Cells.S01.B060.c1203_pos (not_le.mp h3).le h2 (not_le.mp h223).le hz2

end CKLaneC2R.CompactCover


