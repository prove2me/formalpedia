-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g97
-- name    : CK_CKLaneC2R_CompactCover_S00_g97
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T11:43:50.444997+00:00
-- url     : https://prove2.me/theorems/7da8415a-8873-40b1-bfbb-9c846332dd13
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B025
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B003

namespace CKLaneC2R.CompactCover

theorem strip0_s122 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : a ≤ ((31/160 : ℚ) : ℝ)) (h1239 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1314 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1315 : a ≤ ((61/320 : ℚ) : ℝ)
  · -- left
    by_cases h1316 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h1317 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1318 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B001.c32_pos (not_le.mp h891).le h1315 (not_le.mp h1239).le h1318
        · -- right
          exact CKLaneC2R.Cells.S00.B001.c34_pos (not_le.mp h891).le h1315 (not_le.mp h1318).le h1317
      · -- right
        by_cases h1319 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B002.c40_pos (not_le.mp h891).le h1315 (not_le.mp h1317).le h1319
        · -- right
          exact CKLaneC2R.Cells.S00.B002.c42_pos (not_le.mp h891).le h1315 (not_le.mp h1319).le h1316
    · -- right
      by_cases h1320 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1321 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B002.c51_pos (not_le.mp h891).le h1315 (not_le.mp h1316).le h1321
        · -- right
          exact CKLaneC2R.Cells.S00.B002.c53_pos (not_le.mp h891).le h1315 (not_le.mp h1321).le h1320
      · -- right
        by_cases h1322 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B002.c59_pos (not_le.mp h891).le h1315 (not_le.mp h1320).le h1322
        · -- right
          by_cases h1323 : z ≤ ((9683/12800 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B025.c515_pos (not_le.mp h891).le h1315 (not_le.mp h1322).le h1323
          · -- right
            exact CKLaneC2R.Cells.S00.B025.c516_pos (not_le.mp h891).le h1315 (not_le.mp h1323).le h1314
  · -- right
    by_cases h1324 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h1325 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1326 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B001.c33_pos (not_le.mp h1315).le h1238 (not_le.mp h1239).le h1326
        · -- right
          exact CKLaneC2R.Cells.S00.B001.c35_pos (not_le.mp h1315).le h1238 (not_le.mp h1326).le h1325
      · -- right
        by_cases h1327 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B002.c41_pos (not_le.mp h1315).le h1238 (not_le.mp h1325).le h1327
        · -- right
          exact CKLaneC2R.Cells.S00.B002.c43_pos (not_le.mp h1315).le h1238 (not_le.mp h1327).le h1324
    · -- right
      by_cases h1328 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h1329 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B002.c52_pos (not_le.mp h1315).le h1238 (not_le.mp h1324).le h1329
        · -- right
          exact CKLaneC2R.Cells.S00.B002.c54_pos (not_le.mp h1315).le h1238 (not_le.mp h1329).le h1328
      · -- right
        by_cases h1330 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B003.c60_pos (not_le.mp h1315).le h1238 (not_le.mp h1328).le h1330
        · -- right
          exact CKLaneC2R.Cells.S00.B003.c61_pos (not_le.mp h1315).le h1238 (not_le.mp h1330).le h1314

end CKLaneC2R.CompactCover


