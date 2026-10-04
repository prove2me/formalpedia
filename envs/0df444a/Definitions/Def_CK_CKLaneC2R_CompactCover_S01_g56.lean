-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g56
-- name    : CK_CKLaneC2R_CompactCover_S01_g56
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T19:52:45.492205+00:00
-- url     : https://prove2.me/theorems/7fd53553-8ffc-493a-ab62-712b2b85dfa5
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B001

namespace CKLaneC2R.CompactCover

theorem strip1_s078 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) (h748 : a ≤ ((41/160 : ℚ) : ℝ)) (h749 : z ≤ ((217/400 : ℚ) : ℝ)) (h750 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h751 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h770 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h771 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h772 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B017.c348_pos (not_le.mp h0).le h748 (not_le.mp h751).le h772
      · -- right
        exact CKLaneC2R.Cells.S01.B017.c349_pos (not_le.mp h0).le h748 (not_le.mp h772).le h771
    · -- right
      by_cases h773 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B017.c352_pos (not_le.mp h0).le h748 (not_le.mp h771).le h773
      · -- right
        exact CKLaneC2R.Cells.S01.B017.c353_pos (not_le.mp h0).le h748 (not_le.mp h773).le h770
  · -- right
    by_cases h774 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h775 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B018.c364_pos (not_le.mp h0).le h748 (not_le.mp h770).le h775
      · -- right
        exact CKLaneC2R.Cells.S01.B018.c365_pos (not_le.mp h0).le h748 (not_le.mp h775).le h774
    · -- right
      by_cases h776 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B018.c368_pos (not_le.mp h0).le h748 (not_le.mp h774).le h776
      · -- right
        exact CKLaneC2R.Cells.S01.B018.c369_pos (not_le.mp h0).le h748 (not_le.mp h776).le h750

theorem strip1_s079 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) (h748 : a ≤ ((41/160 : ℚ) : ℝ)) (h749 : z ≤ ((217/400 : ℚ) : ℝ)) (h750 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h777 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h778 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h779 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h780 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B020.c400_pos (not_le.mp h0).le h748 (not_le.mp h750).le h780
        · -- right
          exact CKLaneC2R.Cells.S01.B020.c401_pos (not_le.mp h0).le h748 (not_le.mp h780).le h779
      · -- right
        by_cases h781 : a ≤ ((81/320 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B020.c402_pos (not_le.mp h0).le h781 (not_le.mp h779).le h778
        · -- right
          exact CKLaneC2R.Cells.S01.B020.c403_pos (not_le.mp h781).le h748 (not_le.mp h779).le h778
    · -- right
      by_cases h782 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        by_cases h783 : a ≤ ((81/320 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B020.c406_pos (not_le.mp h0).le h783 (not_le.mp h778).le h782
        · -- right
          exact CKLaneC2R.Cells.S01.B020.c407_pos (not_le.mp h783).le h748 (not_le.mp h778).le h782
      · -- right
        exact CKLaneC2R.Cells.S01.B000.c13_pos (not_le.mp h0).le h748 (not_le.mp h782).le h777
  · -- right
    by_cases h784 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h785 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B001.c23_pos (not_le.mp h0).le h748 (not_le.mp h777).le h785
      · -- right
        exact CKLaneC2R.Cells.S01.B001.c24_pos (not_le.mp h0).le h748 (not_le.mp h785).le h784
    · -- right
      by_cases h786 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B001.c27_pos (not_le.mp h0).le h748 (not_le.mp h784).le h786
      · -- right
        exact CKLaneC2R.Cells.S01.B001.c28_pos (not_le.mp h0).le h748 (not_le.mp h786).le h749

end CKLaneC2R.CompactCover


