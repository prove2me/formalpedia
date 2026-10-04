-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g49
-- name    : CK_CKLaneC2R_CompactCover_S01_g49
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T11:05:27.544694+00:00
-- url     : https://prove2.me/theorems/fff61b7a-4cbb-4020-9203-d05bbecf716b
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B003
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B029

namespace CKLaneC2R.CompactCover

theorem strip1_s064 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : a ≤ ((39/160 : ℚ) : ℝ)) (h599 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h642 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h643 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h644 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h645 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B003.c74_pos (not_le.mp h419).le h598 (not_le.mp h599).le h645
      · -- right
        exact CKLaneC2R.Cells.S01.B003.c75_pos (not_le.mp h419).le h598 (not_le.mp h645).le h644
    · -- right
      by_cases h646 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B003.c78_pos (not_le.mp h419).le h598 (not_le.mp h644).le h646
      · -- right
        exact CKLaneC2R.Cells.S01.B003.c79_pos (not_le.mp h419).le h598 (not_le.mp h646).le h643
  · -- right
    by_cases h647 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h648 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B004.c83_pos (not_le.mp h419).le h598 (not_le.mp h643).le h648
      · -- right
        exact CKLaneC2R.Cells.S01.B004.c84_pos (not_le.mp h419).le h598 (not_le.mp h648).le h647
    · -- right
      by_cases h649 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B004.c87_pos (not_le.mp h419).le h598 (not_le.mp h647).le h649
      · -- right
        exact CKLaneC2R.Cells.S01.B004.c89_pos (not_le.mp h419).le h598 (not_le.mp h649).le h642

theorem strip1_s065 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : a ≤ ((39/160 : ℚ) : ℝ)) (h599 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h642 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h650 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h651 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h652 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h653 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B026.c536_pos (not_le.mp h419).le h598 (not_le.mp h642).le h653
      · -- right
        exact CKLaneC2R.Cells.S01.B026.c537_pos (not_le.mp h419).le h598 (not_le.mp h653).le h652
    · -- right
      by_cases h654 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B026.c538_pos (not_le.mp h419).le h598 (not_le.mp h652).le h654
      · -- right
        exact CKLaneC2R.Cells.S01.B026.c539_pos (not_le.mp h419).le h598 (not_le.mp h654).le h651
  · -- right
    by_cases h655 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h656 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B027.c550_pos (not_le.mp h419).le h598 (not_le.mp h651).le h656
      · -- right
        exact CKLaneC2R.Cells.S01.B027.c551_pos (not_le.mp h419).le h598 (not_le.mp h656).le h655
    · -- right
      by_cases h657 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B027.c554_pos (not_le.mp h419).le h598 (not_le.mp h655).le h657
      · -- right
        exact CKLaneC2R.Cells.S01.B027.c555_pos (not_le.mp h419).le h598 (not_le.mp h657).le h650

theorem strip1_s066 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : a ≤ ((39/160 : ℚ) : ℝ)) (h599 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h642 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h650 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h658 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h659 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h660 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B029.c580_pos (not_le.mp h419).le h598 (not_le.mp h650).le h660
    · -- right
      exact CKLaneC2R.Cells.S01.B029.c581_pos (not_le.mp h419).le h598 (not_le.mp h660).le h659
  · -- right
    by_cases h661 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B029.c587_pos (not_le.mp h419).le h598 (not_le.mp h659).le h661
    · -- right
      exact CKLaneC2R.Cells.S01.B029.c589_pos (not_le.mp h419).le h598 (not_le.mp h661).le h658

end CKLaneC2R.CompactCover


