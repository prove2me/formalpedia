-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g26
-- name    : CK_CKLaneC2R_CompactCover_S05_g26
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T01:58:41.348987+00:00
-- url     : https://prove2.me/theorems/ff7c707a-5cac-42c1-a3cc-00b0d3f4a84e
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B011

namespace CKLaneC2R.CompactCover

theorem strip5_s046 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : a ≤ ((7893/8000 : ℚ) : ℝ)) (h272 : ¬ (a ≤ ((15687/16000 : ℚ) : ℝ))) (h316 : ¬ (a ≤ ((31473/32000 : ℚ) : ℝ))) (h346 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h347 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h348 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h349 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B006.c133_pos (not_le.mp h316).le h271 hz1 h349
      · -- right
        exact CKLaneC2R.Cells.S05.B006.c135_pos (not_le.mp h316).le h271 (not_le.mp h349).le h348
    · -- right
      exact CKLaneC2R.Cells.S05.B004.c80_pos (not_le.mp h316).le h271 (not_le.mp h348).le h347
  · -- right
    by_cases h350 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B004.c84_pos (not_le.mp h316).le h271 (not_le.mp h347).le h350
    · -- right
      exact CKLaneC2R.Cells.S05.B004.c88_pos (not_le.mp h316).le h271 (not_le.mp h350).le h346

theorem strip5_s047 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : a ≤ ((7893/8000 : ℚ) : ℝ)) (h272 : ¬ (a ≤ ((15687/16000 : ℚ) : ℝ))) (h316 : ¬ (a ≤ ((31473/32000 : ℚ) : ℝ))) (h346 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h351 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h352 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h353 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B007.c150_pos (not_le.mp h316).le h271 (not_le.mp h346).le h353
    · -- right
      exact CKLaneC2R.Cells.S05.B007.c152_pos (not_le.mp h316).le h271 (not_le.mp h353).le h352
  · -- right
    by_cases h354 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B007.c154_pos (not_le.mp h316).le h271 (not_le.mp h352).le h354
    · -- right
      exact CKLaneC2R.Cells.S05.B007.c156_pos (not_le.mp h316).le h271 (not_le.mp h354).le h351

theorem strip5_s048 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : a ≤ ((7893/8000 : ℚ) : ℝ)) (h272 : ¬ (a ≤ ((15687/16000 : ℚ) : ℝ))) (h316 : ¬ (a ≤ ((31473/32000 : ℚ) : ℝ))) (h346 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h351 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h355 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h356 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B009.c185_pos (not_le.mp h316).le h271 (not_le.mp h351).le h356
  · -- right
    by_cases h357 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B011.c234_pos (not_le.mp h316).le h271 (not_le.mp h356).le h357
    · -- right
      exact CKLaneC2R.Cells.S05.B011.c238_pos (not_le.mp h316).le h271 (not_le.mp h357).le h355

end CKLaneC2R.CompactCover


