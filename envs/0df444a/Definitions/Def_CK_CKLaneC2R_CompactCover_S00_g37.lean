-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g37
-- name    : CK_CKLaneC2R_CompactCover_S00_g37
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T17:57:05.263276+00:00
-- url     : https://prove2.me/theorems/88005f1a-0dfd-4989-8641-5506f882ecba
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B046
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B047
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B048
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B050
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B064

namespace CKLaneC2R.CompactCover

theorem strip0_s043 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : ¬ (a ≤ ((51/320 : ℚ) : ℝ))) (h369 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h431 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h447 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h455 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h456 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h457 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      by_cases h458 : z ≤ ((114177/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B046.c939_pos (not_le.mp h253).le h1 (not_le.mp h447).le h458
      · -- right
        exact CKLaneC2R.Cells.S00.B047.c940_pos (not_le.mp h253).le h1 (not_le.mp h458).le h457
    · -- right
      by_cases h459 : z ≤ ((116003/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B047.c943_pos (not_le.mp h253).le h1 (not_le.mp h457).le h459
      · -- right
        exact CKLaneC2R.Cells.S00.B047.c944_pos (not_le.mp h253).le h1 (not_le.mp h459).le h456
  · -- right
    by_cases h460 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      by_cases h461 : z ≤ ((117829/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B047.c955_pos (not_le.mp h253).le h1 (not_le.mp h456).le h461
      · -- right
        exact CKLaneC2R.Cells.S00.B047.c956_pos (not_le.mp h253).le h1 (not_le.mp h461).le h460
    · -- right
      by_cases h462 : z ≤ ((23931/25600 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B047.c959_pos (not_le.mp h253).le h1 (not_le.mp h460).le h462
      · -- right
        exact CKLaneC2R.Cells.S00.B048.c960_pos (not_le.mp h253).le h1 (not_le.mp h462).le h455

theorem strip0_s044 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : ¬ (a ≤ ((51/320 : ℚ) : ℝ))) (h369 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h431 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h447 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h455 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h463 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h464 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    by_cases h465 : z ≤ ((121481/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B050.c1000_pos (not_le.mp h253).le h1 (not_le.mp h455).le h465
    · -- right
      exact CKLaneC2R.Cells.S00.B050.c1002_pos (not_le.mp h253).le h1 (not_le.mp h465).le h464
  · -- right
    by_cases h466 : z ≤ ((123307/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B050.c1005_pos (not_le.mp h253).le h1 (not_le.mp h464).le h466
    · -- right
      by_cases h467 : z ≤ ((247527/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B064.c1297_pos (not_le.mp h253).le h1 (not_le.mp h466).le h467
      · -- right
        exact CKLaneC2R.Cells.S00.B064.c1298_pos (not_le.mp h253).le h1 (not_le.mp h467).le h463

end CKLaneC2R.CompactCover


