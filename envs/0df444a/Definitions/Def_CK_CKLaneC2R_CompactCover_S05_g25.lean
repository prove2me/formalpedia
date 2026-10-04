-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g25
-- name    : CK_CKLaneC2R_CompactCover_S05_g25
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T19:42:22.124081+00:00
-- url     : https://prove2.me/theorems/51da1499-24bf-4143-ae4d-12e8ada63d47
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B022
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B025
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B028

namespace CKLaneC2R.CompactCover

theorem strip5_s045 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : a ≤ ((7893/8000 : ℚ) : ℝ)) (h272 : ¬ (a ≤ ((15687/16000 : ℚ) : ℝ))) (h316 : a ≤ ((31473/32000 : ℚ) : ℝ)) (h317 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h322 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h326 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h329 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h332 : z ≤ ((6211/6400 : ℚ) : ℝ)
  · -- left
    by_cases h333 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B018.c373_pos (not_le.mp h272).le h316 (not_le.mp h329).le h333
    · -- right
      by_cases h334 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B022.c444_pos (not_le.mp h272).le h316 (not_le.mp h333).le h334
      · -- right
        exact CKLaneC2R.Cells.S05.B022.c445_pos (not_le.mp h272).le h316 (not_le.mp h334).le h332
  · -- right
    by_cases h335 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h336 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B022.c459_pos (not_le.mp h272).le h316 (not_le.mp h332).le h336
      · -- right
        by_cases h337 : z ≤ ((251179/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B025.c511_pos (not_le.mp h272).le h316 (not_le.mp h336).le h337
        · -- right
          exact CKLaneC2R.Cells.S05.B025.c512_pos (not_le.mp h272).le h316 (not_le.mp h337).le h335
    · -- right
      by_cases h338 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        by_cases h339 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B026.c520_pos (not_le.mp h272).le h316 (not_le.mp h335).le h339
        · -- right
          by_cases h340 : a ≤ ((62847/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B027.c553_pos (not_le.mp h272).le h340 (not_le.mp h339).le h338
          · -- right
            exact CKLaneC2R.Cells.S05.B027.c554_pos (not_le.mp h340).le h316 (not_le.mp h339).le h338
      · -- right
        by_cases h341 : a ≤ ((62847/64000 : ℚ) : ℝ)
        · -- left
          by_cases h342 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B027.c559_pos (not_le.mp h272).le h341 (not_le.mp h338).le h342
          · -- right
            by_cases h343 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B029.c585_pos (not_le.mp h272).le h341 (not_le.mp h342).le h343
            · -- right
              exact CKLaneC2R.Cells.S05.B029.c587_pos (not_le.mp h272).le h341 (not_le.mp h343).le hz2
        · -- right
          by_cases h344 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B028.c560_pos (not_le.mp h341).le h316 (not_le.mp h338).le h344
          · -- right
            by_cases h345 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B029.c586_pos (not_le.mp h341).le h316 (not_le.mp h344).le h345
            · -- right
              exact CKLaneC2R.Cells.S05.B029.c588_pos (not_le.mp h341).le h316 (not_le.mp h345).le hz2

end CKLaneC2R.CompactCover


