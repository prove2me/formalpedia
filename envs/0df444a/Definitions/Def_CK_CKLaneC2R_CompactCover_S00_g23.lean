-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g23
-- name    : CK_CKLaneC2R_CompactCover_S00_g23
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T18:28:58.449668+00:00
-- url     : https://prove2.me/theorems/1862e1a9-03fc-48be-a8c1-ea04e7f44d0c
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S00 (proof part of strip0) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S00 (proof part of strip0).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B069
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B053
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B054
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B055
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B056
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B033

namespace CKLaneC2R.CompactCover

theorem strip0_s028 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : a ≤ ((51/320 : ℚ) : ℝ)) (h254 : z ≤ ((217/400 : ℚ) : ℝ)) (h255 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h256 : ¬ (a ≤ ((101/640 : ℚ) : ℝ))) (h280 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h281 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h282 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h283 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h284 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          by_cases h285 : z ≤ ((22929/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B069.c1392_pos (not_le.mp h256).le h253 hz1 h285
          · -- right
            exact CKLaneC2R.Cells.S00.B069.c1393_pos (not_le.mp h256).le h253 (not_le.mp h285).le h284
        · -- right
          by_cases h286 : z ≤ ((4951/51200 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B069.c1396_pos (not_le.mp h256).le h253 (not_le.mp h284).le h286
          · -- right
            exact CKLaneC2R.Cells.S00.B069.c1397_pos (not_le.mp h256).le h253 (not_le.mp h286).le h283
      · -- right
        by_cases h287 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B053.c1069_pos (not_le.mp h256).le h253 (not_le.mp h283).le h287
        · -- right
          exact CKLaneC2R.Cells.S00.B053.c1071_pos (not_le.mp h256).le h253 (not_le.mp h287).le h282
    · -- right
      by_cases h288 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h289 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B054.c1093_pos (not_le.mp h256).le h253 (not_le.mp h282).le h289
        · -- right
          exact CKLaneC2R.Cells.S00.B054.c1095_pos (not_le.mp h256).le h253 (not_le.mp h289).le h288
      · -- right
        by_cases h290 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B055.c1101_pos (not_le.mp h256).le h253 (not_le.mp h288).le h290
        · -- right
          exact CKLaneC2R.Cells.S00.B055.c1103_pos (not_le.mp h256).le h253 (not_le.mp h290).le h281
  · -- right
    by_cases h291 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h292 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        by_cases h293 : z ≤ ((769/5120 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B056.c1133_pos (not_le.mp h256).le h253 (not_le.mp h281).le h293
        · -- right
          exact CKLaneC2R.Cells.S00.B056.c1135_pos (not_le.mp h256).le h253 (not_le.mp h293).le h292
      · -- right
        by_cases h294 : z ≤ ((21051/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B056.c1138_pos (not_le.mp h256).le h253 (not_le.mp h292).le h294
        · -- right
          exact CKLaneC2R.Cells.S00.B056.c1139_pos (not_le.mp h256).le h253 (not_le.mp h294).le h291
    · -- right
      by_cases h295 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B033.c677_pos (not_le.mp h256).le h253 (not_le.mp h291).le h295
      · -- right
        exact CKLaneC2R.Cells.S00.B033.c679_pos (not_le.mp h256).le h253 (not_le.mp h295).le h280

end CKLaneC2R.CompactCover


