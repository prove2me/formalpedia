-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g17
-- name    : CK_CKLaneC2R_CompactCover_S02_g17
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T17:59:15.69399+00:00
-- url     : https://prove2.me/theorems/ebb1af74-e449-43f9-937f-a85a2fe720d2
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
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B035
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B039
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B042

namespace CKLaneC2R.CompactCover

theorem strip2_s027 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((13/40 : ℚ) : ℝ))) (h179 : ¬ (a ≤ ((27/80 : ℚ) : ℝ))) (h251 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h287 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h295 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h301 : z ≤ ((15071/16000 : ℚ) : ℝ)
  · -- left
    by_cases h302 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h303 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B026.c527_pos (not_le.mp h179).le h1 (not_le.mp h295).le h303
      · -- right
        exact CKLaneC2R.Cells.S02.B026.c528_pos (not_le.mp h179).le h1 (not_le.mp h303).le h302
    · -- right
      by_cases h304 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B026.c531_pos (not_le.mp h179).le h1 (not_le.mp h302).le h304
      · -- right
        exact CKLaneC2R.Cells.S02.B026.c532_pos (not_le.mp h179).le h1 (not_le.mp h304).le h301
  · -- right
    by_cases h305 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h306 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B027.c555_pos (not_le.mp h179).le h1 (not_le.mp h301).le h306
      · -- right
        by_cases h307 : z ≤ ((123307/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B035.c713_pos (not_le.mp h179).le h1 (not_le.mp h306).le h307
        · -- right
          exact CKLaneC2R.Cells.S02.B035.c714_pos (not_le.mp h179).le h1 (not_le.mp h307).le h305
    · -- right
      by_cases h308 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        by_cases h309 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B036.c721_pos (not_le.mp h179).le h1 (not_le.mp h305).le h309
        · -- right
          exact CKLaneC2R.Cells.S02.B036.c722_pos (not_le.mp h179).le h1 (not_le.mp h309).le h308
      · -- right
        by_cases h310 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          by_cases h311 : z ≤ ((50601/51200 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B039.c789_pos (not_le.mp h179).le h1 (not_le.mp h308).le h311
          · -- right
            exact CKLaneC2R.Cells.S02.B039.c790_pos (not_le.mp h179).le h1 (not_le.mp h311).le h310
        · -- right
          by_cases h312 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B040.c800_pos (not_le.mp h179).le h1 (not_le.mp h310).le h312
          · -- right
            by_cases h313 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S02.B041.c821_pos (not_le.mp h179).le h1 (not_le.mp h312).le h313
            · -- right
              by_cases h314 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S02.B042.c844_pos (not_le.mp h179).le h1 (not_le.mp h313).le h314
              · -- right
                exact CKLaneC2R.Cells.S02.B042.c845_pos (not_le.mp h179).le h1 (not_le.mp h314).le hz2

end CKLaneC2R.CompactCover


