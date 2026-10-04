-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g34
-- name    : CK_CKLaneC2R_CompactCover_S05_g34
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T03:19:22.390305+00:00
-- url     : https://prove2.me/theorems/cc135424-137a-42fa-8d7f-cfa6538ca366
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B022
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B024
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B025
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B030
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B031

namespace CKLaneC2R.CompactCover

theorem strip5_s063 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : a ≤ ((3177/3200 : ℚ) : ℝ)) (h377 : ¬ (a ≤ ((31671/32000 : ℚ) : ℝ))) (h416 : a ≤ ((63441/64000 : ℚ) : ℝ)) (h417 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h422 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h425 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h428 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h431 : z ≤ ((6211/6400 : ℚ) : ℝ)
  · -- left
    by_cases h432 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B022.c450_pos (not_le.mp h377).le h416 (not_le.mp h428).le h432
    · -- right
      by_cases h433 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B024.c499_pos (not_le.mp h377).le h416 (not_le.mp h432).le h433
      · -- right
        exact CKLaneC2R.Cells.S05.B025.c501_pos (not_le.mp h377).le h416 (not_le.mp h433).le h431
  · -- right
    by_cases h434 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h435 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B026.c523_pos (not_le.mp h377).le h416 (not_le.mp h431).le h435
      · -- right
        by_cases h436 : z ≤ ((251179/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B028.c563_pos (not_le.mp h377).le h416 (not_le.mp h435).le h436
        · -- right
          exact CKLaneC2R.Cells.S05.B028.c564_pos (not_le.mp h377).le h416 (not_le.mp h436).le h434
    · -- right
      by_cases h437 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        by_cases h438 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B028.c578_pos (not_le.mp h377).le h416 (not_le.mp h434).le h438
        · -- right
          exact CKLaneC2R.Cells.S05.B029.c580_pos (not_le.mp h377).le h416 (not_le.mp h438).le h437
      · -- right
        by_cases h439 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          by_cases h440 : z ≤ ((508749/512000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B030.c611_pos (not_le.mp h377).le h416 (not_le.mp h437).le h440
          · -- right
            exact CKLaneC2R.Cells.S05.B030.c612_pos (not_le.mp h377).le h416 (not_le.mp h440).le h439
        · -- right
          by_cases h441 : a ≤ ((126783/128000 : ℚ) : ℝ)
          · -- left
            by_cases h442 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B031.c632_pos (not_le.mp h377).le h441 (not_le.mp h439).le h442
            · -- right
              exact CKLaneC2R.Cells.S05.B031.c634_pos (not_le.mp h377).le h441 (not_le.mp h442).le hz2
          · -- right
            by_cases h443 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B031.c633_pos (not_le.mp h441).le h416 (not_le.mp h439).le h443
            · -- right
              exact CKLaneC2R.Cells.S05.B031.c635_pos (not_le.mp h441).le h416 (not_le.mp h443).le hz2

end CKLaneC2R.CompactCover


