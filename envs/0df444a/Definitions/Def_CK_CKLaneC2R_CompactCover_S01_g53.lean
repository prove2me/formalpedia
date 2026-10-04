-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g53
-- name    : CK_CKLaneC2R_CompactCover_S01_g53
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T22:38:02.083776+00:00
-- url     : https://prove2.me/theorems/c85dbd39-8f4d-46fe-8704-2adf80bd300b
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
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B029

namespace CKLaneC2R.CompactCover

theorem strip1_s072 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : ¬ (a ≤ ((39/160 : ℚ) : ℝ))) (h675 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h715 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h716 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h717 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h718 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B003.c76_pos (not_le.mp h598).le h0 (not_le.mp h675).le h718
      · -- right
        exact CKLaneC2R.Cells.S01.B003.c77_pos (not_le.mp h598).le h0 (not_le.mp h718).le h717
    · -- right
      by_cases h719 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B004.c80_pos (not_le.mp h598).le h0 (not_le.mp h717).le h719
      · -- right
        exact CKLaneC2R.Cells.S01.B004.c81_pos (not_le.mp h598).le h0 (not_le.mp h719).le h716
  · -- right
    by_cases h720 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h721 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B004.c85_pos (not_le.mp h598).le h0 (not_le.mp h716).le h721
      · -- right
        exact CKLaneC2R.Cells.S01.B004.c86_pos (not_le.mp h598).le h0 (not_le.mp h721).le h720
    · -- right
      by_cases h722 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B004.c88_pos (not_le.mp h598).le h0 (not_le.mp h720).le h722
      · -- right
        exact CKLaneC2R.Cells.S01.B004.c90_pos (not_le.mp h598).le h0 (not_le.mp h722).le h715

theorem strip1_s073 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : ¬ (a ≤ ((39/160 : ℚ) : ℝ))) (h675 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h715 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h723 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h724 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h725 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B007.c155_pos (not_le.mp h598).le h0 (not_le.mp h715).le h725
    · -- right
      by_cases h726 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B027.c540_pos (not_le.mp h598).le h0 (not_le.mp h725).le h726
      · -- right
        exact CKLaneC2R.Cells.S01.B027.c541_pos (not_le.mp h598).le h0 (not_le.mp h726).le h724
  · -- right
    by_cases h727 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h728 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B027.c552_pos (not_le.mp h598).le h0 (not_le.mp h724).le h728
      · -- right
        exact CKLaneC2R.Cells.S01.B027.c553_pos (not_le.mp h598).le h0 (not_le.mp h728).le h727
    · -- right
      by_cases h729 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B027.c556_pos (not_le.mp h598).le h0 (not_le.mp h727).le h729
      · -- right
        exact CKLaneC2R.Cells.S01.B027.c557_pos (not_le.mp h598).le h0 (not_le.mp h729).le h723

theorem strip1_s074 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : ¬ (a ≤ ((39/160 : ℚ) : ℝ))) (h675 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h715 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h723 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h730 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h731 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h732 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B029.c582_pos (not_le.mp h598).le h0 (not_le.mp h723).le h732
    · -- right
      exact CKLaneC2R.Cells.S01.B029.c583_pos (not_le.mp h598).le h0 (not_le.mp h732).le h731
  · -- right
    by_cases h733 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B029.c588_pos (not_le.mp h598).le h0 (not_le.mp h731).le h733
    · -- right
      exact CKLaneC2R.Cells.S01.B029.c590_pos (not_le.mp h598).le h0 (not_le.mp h733).le h730

end CKLaneC2R.CompactCover


