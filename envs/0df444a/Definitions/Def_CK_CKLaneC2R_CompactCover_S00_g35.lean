-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g35
-- name    : CK_CKLaneC2R_CompactCover_S00_g35
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T02:18:50.127265+00:00
-- url     : https://prove2.me/theorems/1cac3582-261b-474d-b6a5-fa92d489ca59
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B021
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B022

namespace CKLaneC2R.CompactCover

theorem strip0_s041 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : ¬ (a ≤ ((51/320 : ℚ) : ℝ))) (h369 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h431 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h432 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h433 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h434 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        by_cases h435 : z ≤ ((35633/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B017.c355_pos (not_le.mp h253).le h1 (not_le.mp h369).le h435
        · -- right
          exact CKLaneC2R.Cells.S00.B017.c356_pos (not_le.mp h253).le h1 (not_le.mp h435).le h434
      · -- right
        by_cases h436 : z ≤ ((37459/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B017.c359_pos (not_le.mp h253).le h1 (not_le.mp h434).le h436
        · -- right
          exact CKLaneC2R.Cells.S00.B018.c360_pos (not_le.mp h253).le h1 (not_le.mp h436).le h433
    · -- right
      by_cases h437 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        by_cases h438 : z ≤ ((7857/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B018.c371_pos (not_le.mp h253).le h1 (not_le.mp h433).le h438
        · -- right
          exact CKLaneC2R.Cells.S00.B018.c372_pos (not_le.mp h253).le h1 (not_le.mp h438).le h437
      · -- right
        by_cases h439 : z ≤ ((41111/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B018.c375_pos (not_le.mp h253).le h1 (not_le.mp h437).le h439
        · -- right
          exact CKLaneC2R.Cells.S00.B018.c376_pos (not_le.mp h253).le h1 (not_le.mp h439).le h432
  · -- right
    by_cases h440 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h441 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        by_cases h442 : z ≤ ((42937/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B020.c419_pos (not_le.mp h253).le h1 (not_le.mp h432).le h442
        · -- right
          exact CKLaneC2R.Cells.S00.B021.c420_pos (not_le.mp h253).le h1 (not_le.mp h442).le h441
      · -- right
        by_cases h443 : z ≤ ((44763/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B021.c423_pos (not_le.mp h253).le h1 (not_le.mp h441).le h443
        · -- right
          exact CKLaneC2R.Cells.S00.B021.c424_pos (not_le.mp h253).le h1 (not_le.mp h443).le h440
    · -- right
      by_cases h444 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        by_cases h445 : z ≤ ((46589/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B021.c435_pos (not_le.mp h253).le h1 (not_le.mp h440).le h445
        · -- right
          exact CKLaneC2R.Cells.S00.B021.c436_pos (not_le.mp h253).le h1 (not_le.mp h445).le h444
      · -- right
        by_cases h446 : z ≤ ((9683/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B021.c439_pos (not_le.mp h253).le h1 (not_le.mp h444).le h446
        · -- right
          exact CKLaneC2R.Cells.S00.B022.c440_pos (not_le.mp h253).le h1 (not_le.mp h446).le h431

end CKLaneC2R.CompactCover


