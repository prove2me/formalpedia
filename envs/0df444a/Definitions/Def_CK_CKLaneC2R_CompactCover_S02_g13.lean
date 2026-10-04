-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g13
-- name    : CK_CKLaneC2R_CompactCover_S02_g13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T10:56:08.041442+00:00
-- url     : https://prove2.me/theorems/4710626b-b185-40ef-99be-2449097937d4
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
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B039
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B042

namespace CKLaneC2R.CompactCover

theorem strip2_s021 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((13/40 : ℚ) : ℝ))) (h179 : a ≤ ((27/80 : ℚ) : ℝ)) (h180 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h220 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h228 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h236 : z ≤ ((15071/16000 : ℚ) : ℝ)
  · -- left
    by_cases h237 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h238 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B026.c525_pos (not_le.mp h2).le h179 (not_le.mp h228).le h238
      · -- right
        exact CKLaneC2R.Cells.S02.B026.c526_pos (not_le.mp h2).le h179 (not_le.mp h238).le h237
    · -- right
      by_cases h239 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B026.c529_pos (not_le.mp h2).le h179 (not_le.mp h237).le h239
      · -- right
        exact CKLaneC2R.Cells.S02.B026.c530_pos (not_le.mp h2).le h179 (not_le.mp h239).le h236
  · -- right
    by_cases h240 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h241 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        by_cases h242 : a ≤ ((53/160 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B035.c709_pos (not_le.mp h2).le h242 (not_le.mp h236).le h241
        · -- right
          exact CKLaneC2R.Cells.S02.B035.c710_pos (not_le.mp h242).le h179 (not_le.mp h236).le h241
      · -- right
        by_cases h243 : z ≤ ((123307/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B035.c711_pos (not_le.mp h2).le h179 (not_le.mp h241).le h243
        · -- right
          exact CKLaneC2R.Cells.S02.B035.c712_pos (not_le.mp h2).le h179 (not_le.mp h243).le h240
    · -- right
      by_cases h244 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        by_cases h245 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B035.c719_pos (not_le.mp h2).le h179 (not_le.mp h240).le h245
        · -- right
          exact CKLaneC2R.Cells.S02.B036.c720_pos (not_le.mp h2).le h179 (not_le.mp h245).le h244
      · -- right
        by_cases h246 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          by_cases h247 : z ≤ ((50601/51200 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B039.c787_pos (not_le.mp h2).le h179 (not_le.mp h244).le h247
          · -- right
            exact CKLaneC2R.Cells.S02.B039.c788_pos (not_le.mp h2).le h179 (not_le.mp h247).le h246
        · -- right
          by_cases h248 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B039.c799_pos (not_le.mp h2).le h179 (not_le.mp h246).le h248
          · -- right
            by_cases h249 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S02.B041.c820_pos (not_le.mp h2).le h179 (not_le.mp h248).le h249
            · -- right
              by_cases h250 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S02.B042.c842_pos (not_le.mp h2).le h179 (not_le.mp h249).le h250
              · -- right
                exact CKLaneC2R.Cells.S02.B042.c843_pos (not_le.mp h2).le h179 (not_le.mp h250).le hz2

end CKLaneC2R.CompactCover


