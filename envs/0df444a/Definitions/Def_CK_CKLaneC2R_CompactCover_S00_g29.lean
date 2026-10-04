-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g29
-- name    : CK_CKLaneC2R_CompactCover_S00_g29
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T22:07:07.913138+00:00
-- url     : https://prove2.me/theorems/df81629a-3a4b-454b-9e3c-251e2d7bda1f
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B065
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B067
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B070
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B071
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B073
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B074

namespace CKLaneC2R.CompactCover

theorem strip0_s035 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : a ≤ ((51/320 : ℚ) : ℝ)) (h254 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h319 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h335 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h343 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h351 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h356 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h357 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      by_cases h358 : z ≤ ((249353/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B065.c1303_pos (not_le.mp h2).le h253 (not_le.mp h351).le h358
      · -- right
        exact CKLaneC2R.Cells.S00.B065.c1304_pos (not_le.mp h2).le h253 (not_le.mp h358).le h357
    · -- right
      by_cases h359 : z ≤ ((251179/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B065.c1311_pos (not_le.mp h2).le h253 (not_le.mp h357).le h359
      · -- right
        exact CKLaneC2R.Cells.S00.B065.c1313_pos (not_le.mp h2).le h253 (not_le.mp h359).le h356
  · -- right
    by_cases h360 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h361 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B067.c1344_pos (not_le.mp h2).le h253 (not_le.mp h356).le h361
      · -- right
        by_cases h362 : z ≤ ((506923/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B070.c1410_pos (not_le.mp h2).le h253 (not_le.mp h361).le h362
        · -- right
          exact CKLaneC2R.Cells.S00.B070.c1411_pos (not_le.mp h2).le h253 (not_le.mp h362).le h360
    · -- right
      by_cases h363 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        by_cases h364 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B071.c1424_pos (not_le.mp h2).le h253 (not_le.mp h360).le h364
        · -- right
          exact CKLaneC2R.Cells.S00.B071.c1426_pos (not_le.mp h2).le h253 (not_le.mp h364).le h363
      · -- right
        by_cases h365 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          by_cases h366 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B073.c1460_pos (not_le.mp h2).le h253 (not_le.mp h363).le h366
          · -- right
            exact CKLaneC2R.Cells.S00.B073.c1461_pos (not_le.mp h2).le h253 (not_le.mp h366).le h365
        · -- right
          by_cases h367 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B073.c1474_pos (not_le.mp h2).le h253 (not_le.mp h365).le h367
          · -- right
            by_cases h368 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S00.B074.c1494_pos (not_le.mp h2).le h253 (not_le.mp h367).le h368
            · -- right
              exact CKLaneC2R.Cells.S00.B074.c1495_pos (not_le.mp h2).le h253 (not_le.mp h368).le hz2

end CKLaneC2R.CompactCover


