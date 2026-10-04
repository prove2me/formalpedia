-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g95
-- name    : CK_CKLaneC2R_CompactCover_S00_g95
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T04:56:47.399983+00:00
-- url     : https://prove2.me/theorems/d17bdf7b-06bd-4a4e-b0c6-920e2956ef5e
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B044
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B045
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B011
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B012

namespace CKLaneC2R.CompactCover

theorem strip0_s119 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : a ≤ ((31/160 : ℚ) : ℝ)) (h1239 : z ≤ ((217/400 : ℚ) : ℝ)) (h1240 : ¬ (a ≤ ((61/320 : ℚ) : ℝ))) (h1278 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1279 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h1280 : ¬ (z ≤ ((2289/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1291 : z ≤ ((5491/32000 : ℚ) : ℝ)
  · -- left
    by_cases h1292 : z ≤ ((10069/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1293 : z ≤ ((769/5120 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B044.c895_pos (not_le.mp h1240).le h1238 (not_le.mp h1280).le h1293
      · -- right
        exact CKLaneC2R.Cells.S00.B044.c896_pos (not_le.mp h1240).le h1238 (not_le.mp h1293).le h1292
    · -- right
      by_cases h1294 : z ≤ ((21051/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B044.c899_pos (not_le.mp h1240).le h1238 (not_le.mp h1292).le h1294
      · -- right
        exact CKLaneC2R.Cells.S00.B045.c900_pos (not_le.mp h1240).le h1238 (not_le.mp h1294).le h1291
  · -- right
    by_cases h1295 : z ≤ ((2379/12800 : ℚ) : ℝ)
    · -- left
      by_cases h1296 : z ≤ ((22877/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B045.c911_pos (not_le.mp h1240).le h1238 (not_le.mp h1291).le h1296
      · -- right
        exact CKLaneC2R.Cells.S00.B045.c912_pos (not_le.mp h1240).le h1238 (not_le.mp h1296).le h1295
    · -- right
      exact CKLaneC2R.Cells.S00.B010.c200_pos (not_le.mp h1240).le h1238 (not_le.mp h1295).le h1279

theorem strip0_s120 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : a ≤ ((31/160 : ℚ) : ℝ)) (h1239 : z ≤ ((217/400 : ℚ) : ℝ)) (h1240 : ¬ (a ≤ ((61/320 : ℚ) : ℝ))) (h1278 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1279 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1297 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h1298 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1299 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B011.c235_pos (not_le.mp h1240).le h1238 (not_le.mp h1279).le h1299
      · -- right
        exact CKLaneC2R.Cells.S00.B011.c236_pos (not_le.mp h1240).le h1238 (not_le.mp h1299).le h1298
    · -- right
      by_cases h1300 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B011.c239_pos (not_le.mp h1240).le h1238 (not_le.mp h1298).le h1300
      · -- right
        exact CKLaneC2R.Cells.S00.B012.c240_pos (not_le.mp h1240).le h1238 (not_le.mp h1300).le h1297
  · -- right
    by_cases h1301 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1302 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B012.c251_pos (not_le.mp h1240).le h1238 (not_le.mp h1297).le h1302
      · -- right
        exact CKLaneC2R.Cells.S00.B012.c252_pos (not_le.mp h1240).le h1238 (not_le.mp h1302).le h1301
    · -- right
      by_cases h1303 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B012.c255_pos (not_le.mp h1240).le h1238 (not_le.mp h1301).le h1303
      · -- right
        exact CKLaneC2R.Cells.S00.B012.c256_pos (not_le.mp h1240).le h1238 (not_le.mp h1303).le h1278

end CKLaneC2R.CompactCover


