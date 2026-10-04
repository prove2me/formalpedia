-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g43
-- name    : CK_CKLaneC2R_CompactCover_S00_g43
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T07:40:32.694146+00:00
-- url     : https://prove2.me/theorems/4dad719e-b653-4091-8dac-c01a135979d1
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B019
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B022
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B023

namespace CKLaneC2R.CompactCover

theorem strip0_s050 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : a ≤ ((53/320 : ℚ) : ℝ)) (h483 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h542 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h543 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h544 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h545 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        by_cases h546 : z ≤ ((35633/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B018.c377_pos (not_le.mp h1).le h482 (not_le.mp h483).le h546
        · -- right
          exact CKLaneC2R.Cells.S00.B018.c378_pos (not_le.mp h1).le h482 (not_le.mp h546).le h545
      · -- right
        by_cases h547 : z ≤ ((37459/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B019.c381_pos (not_le.mp h1).le h482 (not_le.mp h545).le h547
        · -- right
          exact CKLaneC2R.Cells.S00.B019.c382_pos (not_le.mp h1).le h482 (not_le.mp h547).le h544
    · -- right
      by_cases h548 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        by_cases h549 : z ≤ ((7857/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B019.c393_pos (not_le.mp h1).le h482 (not_le.mp h544).le h549
        · -- right
          exact CKLaneC2R.Cells.S00.B019.c394_pos (not_le.mp h1).le h482 (not_le.mp h549).le h548
      · -- right
        by_cases h550 : z ≤ ((41111/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B019.c397_pos (not_le.mp h1).le h482 (not_le.mp h548).le h550
        · -- right
          exact CKLaneC2R.Cells.S00.B019.c398_pos (not_le.mp h1).le h482 (not_le.mp h550).le h543
  · -- right
    by_cases h551 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h552 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        by_cases h553 : z ≤ ((42937/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B022.c441_pos (not_le.mp h1).le h482 (not_le.mp h543).le h553
        · -- right
          exact CKLaneC2R.Cells.S00.B022.c442_pos (not_le.mp h1).le h482 (not_le.mp h553).le h552
      · -- right
        by_cases h554 : z ≤ ((44763/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B022.c445_pos (not_le.mp h1).le h482 (not_le.mp h552).le h554
        · -- right
          exact CKLaneC2R.Cells.S00.B022.c446_pos (not_le.mp h1).le h482 (not_le.mp h554).le h551
    · -- right
      by_cases h555 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        by_cases h556 : z ≤ ((46589/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B022.c457_pos (not_le.mp h1).le h482 (not_le.mp h551).le h556
        · -- right
          exact CKLaneC2R.Cells.S00.B022.c458_pos (not_le.mp h1).le h482 (not_le.mp h556).le h555
      · -- right
        by_cases h557 : z ≤ ((9683/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B023.c461_pos (not_le.mp h1).le h482 (not_le.mp h555).le h557
        · -- right
          exact CKLaneC2R.Cells.S00.B023.c462_pos (not_le.mp h1).le h482 (not_le.mp h557).le h542

end CKLaneC2R.CompactCover


