-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g32
-- name    : CK_CKLaneC2R_CompactCover_S00_g32
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T12:39:54.457452+00:00
-- url     : https://prove2.me/theorems/4102e497-2f11-433e-bd84-4458955fba79
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B070
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B053
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B054
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B055
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B057
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B034

namespace CKLaneC2R.CompactCover

theorem strip0_s038 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : ¬ (a ≤ ((51/320 : ℚ) : ℝ))) (h369 : z ≤ ((217/400 : ℚ) : ℝ)) (h370 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h371 : ¬ (a ≤ ((103/640 : ℚ) : ℝ))) (h394 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h395 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h396 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h397 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h398 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          by_cases h399 : z ≤ ((22929/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B070.c1400_pos (not_le.mp h371).le h1 hz1 h399
          · -- right
            exact CKLaneC2R.Cells.S00.B070.c1401_pos (not_le.mp h371).le h1 (not_le.mp h399).le h398
        · -- right
          exact CKLaneC2R.Cells.S00.B053.c1067_pos (not_le.mp h371).le h1 (not_le.mp h398).le h397
      · -- right
        by_cases h400 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B053.c1073_pos (not_le.mp h371).le h1 (not_le.mp h397).le h400
        · -- right
          exact CKLaneC2R.Cells.S00.B053.c1075_pos (not_le.mp h371).le h1 (not_le.mp h400).le h396
    · -- right
      by_cases h401 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h402 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B054.c1097_pos (not_le.mp h371).le h1 (not_le.mp h396).le h402
        · -- right
          exact CKLaneC2R.Cells.S00.B054.c1099_pos (not_le.mp h371).le h1 (not_le.mp h402).le h401
      · -- right
        by_cases h403 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B055.c1105_pos (not_le.mp h371).le h1 (not_le.mp h401).le h403
        · -- right
          exact CKLaneC2R.Cells.S00.B055.c1107_pos (not_le.mp h371).le h1 (not_le.mp h403).le h395
  · -- right
    by_cases h404 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h405 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        by_cases h406 : z ≤ ((769/5120 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B057.c1141_pos (not_le.mp h371).le h1 (not_le.mp h395).le h406
        · -- right
          exact CKLaneC2R.Cells.S00.B057.c1143_pos (not_le.mp h371).le h1 (not_le.mp h406).le h405
      · -- right
        by_cases h407 : z ≤ ((21051/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B057.c1146_pos (not_le.mp h371).le h1 (not_le.mp h405).le h407
        · -- right
          exact CKLaneC2R.Cells.S00.B057.c1147_pos (not_le.mp h371).le h1 (not_le.mp h407).le h404
    · -- right
      by_cases h408 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B034.c681_pos (not_le.mp h371).le h1 (not_le.mp h404).le h408
      · -- right
        exact CKLaneC2R.Cells.S00.B034.c683_pos (not_le.mp h371).le h1 (not_le.mp h408).le h394

end CKLaneC2R.CompactCover


