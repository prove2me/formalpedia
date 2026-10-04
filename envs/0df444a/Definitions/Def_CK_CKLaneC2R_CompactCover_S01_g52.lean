-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g52
-- name    : CK_CKLaneC2R_CompactCover_S01_g52
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T00:47:36.581978+00:00
-- url     : https://prove2.me/theorems/16be6bd5-872d-407e-8145-4f0bfda1eaed
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B015
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B000

namespace CKLaneC2R.CompactCover

theorem strip1_s070 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : ¬ (a ≤ ((39/160 : ℚ) : ℝ))) (h675 : z ≤ ((217/400 : ℚ) : ℝ)) (h676 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h677 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h697 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h698 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h699 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B009.c194_pos (not_le.mp h598).le h0 (not_le.mp h677).le h699
      · -- right
        exact CKLaneC2R.Cells.S01.B009.c195_pos (not_le.mp h598).le h0 (not_le.mp h699).le h698
    · -- right
      by_cases h700 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B009.c198_pos (not_le.mp h598).le h0 (not_le.mp h698).le h700
      · -- right
        exact CKLaneC2R.Cells.S01.B009.c199_pos (not_le.mp h598).le h0 (not_le.mp h700).le h697
  · -- right
    by_cases h701 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h702 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B010.c204_pos (not_le.mp h598).le h0 (not_le.mp h697).le h702
      · -- right
        exact CKLaneC2R.Cells.S01.B010.c205_pos (not_le.mp h598).le h0 (not_le.mp h702).le h701
    · -- right
      by_cases h703 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B010.c206_pos (not_le.mp h598).le h0 (not_le.mp h701).le h703
      · -- right
        exact CKLaneC2R.Cells.S01.B010.c207_pos (not_le.mp h598).le h0 (not_le.mp h703).le h676

theorem strip1_s071 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((9/40 : ℚ) : ℝ))) (h419 : ¬ (a ≤ ((19/80 : ℚ) : ℝ))) (h598 : ¬ (a ≤ ((39/160 : ℚ) : ℝ))) (h675 : z ≤ ((217/400 : ℚ) : ℝ)) (h676 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h704 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h705 : a ≤ ((79/320 : ℚ) : ℝ)
    · -- left
      by_cases h706 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        by_cases h707 : z ≤ ((10969/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B014.c290_pos (not_le.mp h598).le h705 (not_le.mp h676).le h707
        · -- right
          exact CKLaneC2R.Cells.S01.B014.c292_pos (not_le.mp h598).le h705 (not_le.mp h707).le h706
      · -- right
        by_cases h708 : z ≤ ((2559/6400 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B014.c298_pos (not_le.mp h598).le h705 (not_le.mp h706).le h708
        · -- right
          exact CKLaneC2R.Cells.S01.B015.c300_pos (not_le.mp h598).le h705 (not_le.mp h708).le h704
    · -- right
      by_cases h709 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        by_cases h710 : z ≤ ((10969/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B014.c291_pos (not_le.mp h705).le h0 (not_le.mp h676).le h710
        · -- right
          exact CKLaneC2R.Cells.S01.B014.c293_pos (not_le.mp h705).le h0 (not_le.mp h710).le h709
      · -- right
        by_cases h711 : z ≤ ((2559/6400 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B014.c299_pos (not_le.mp h705).le h0 (not_le.mp h709).le h711
        · -- right
          exact CKLaneC2R.Cells.S01.B015.c301_pos (not_le.mp h705).le h0 (not_le.mp h711).le h704
  · -- right
    by_cases h712 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h713 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B000.c0_pos (not_le.mp h598).le h0 (not_le.mp h704).le h713
      · -- right
        exact CKLaneC2R.Cells.S01.B000.c1_pos (not_le.mp h598).le h0 (not_le.mp h713).le h712
    · -- right
      by_cases h714 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B000.c4_pos (not_le.mp h598).le h0 (not_le.mp h712).le h714
      · -- right
        exact CKLaneC2R.Cells.S01.B000.c5_pos (not_le.mp h598).le h0 (not_le.mp h714).le h675

end CKLaneC2R.CompactCover


