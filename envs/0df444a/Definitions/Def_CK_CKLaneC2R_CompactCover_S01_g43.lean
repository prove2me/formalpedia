-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g43
-- name    : CK_CKLaneC2R_CompactCover_S01_g43
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T21:34:57.973003+00:00
-- url     : https://prove2.me/theorems/8edfde03-e878-4f13-ae11-0debbe47c3d9
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B023
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B003
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B024

namespace CKLaneC2R.CompactCover

theorem strip1_s056 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : a ≤ ((19/80 : ℚ) : ℝ)) (h420 : ¬ (a ≤ ((37/160 : ℚ) : ℝ))) (h513 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h561 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h562 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h563 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h564 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        by_cases h565 : a ≤ ((15/64 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B023.c478_pos (not_le.mp h420).le h565 (not_le.mp h513).le h564
        · -- right
          exact CKLaneC2R.Cells.S01.B023.c479_pos (not_le.mp h565).le h419 (not_le.mp h513).le h564
      · -- right
        exact CKLaneC2R.Cells.S01.B003.c71_pos (not_le.mp h420).le h419 (not_le.mp h564).le h563
    · -- right
      by_cases h566 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B003.c72_pos (not_le.mp h420).le h419 (not_le.mp h563).le h566
      · -- right
        exact CKLaneC2R.Cells.S01.B003.c73_pos (not_le.mp h420).le h419 (not_le.mp h566).le h562
  · -- right
    by_cases h567 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h568 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B004.c82_pos (not_le.mp h420).le h419 (not_le.mp h562).le h568
      · -- right
        by_cases h569 : a ≤ ((15/64 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B024.c488_pos (not_le.mp h420).le h569 (not_le.mp h568).le h567
        · -- right
          exact CKLaneC2R.Cells.S01.B024.c489_pos (not_le.mp h569).le h419 (not_le.mp h568).le h567
    · -- right
      by_cases h570 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        by_cases h571 : a ≤ ((15/64 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B024.c494_pos (not_le.mp h420).le h571 (not_le.mp h567).le h570
        · -- right
          exact CKLaneC2R.Cells.S01.B024.c495_pos (not_le.mp h571).le h419 (not_le.mp h567).le h570
      · -- right
        by_cases h572 : z ≤ ((9683/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B024.c496_pos (not_le.mp h420).le h419 (not_le.mp h570).le h572
        · -- right
          exact CKLaneC2R.Cells.S01.B024.c497_pos (not_le.mp h420).le h419 (not_le.mp h572).le h561

end CKLaneC2R.CompactCover


