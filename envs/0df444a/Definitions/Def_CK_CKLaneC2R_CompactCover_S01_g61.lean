-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g61
-- name    : CK_CKLaneC2R_CompactCover_S01_g61
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T14:17:55.464984+00:00
-- url     : https://prove2.me/theorems/e419fab2-1201-4b80-a634-f0d02503b564
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

theorem strip1_s086 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) (h748 : ¬ (a ≤ ((41/160 : ℚ) : ℝ))) (h817 : z ≤ ((217/400 : ℚ) : ℝ)) (h818 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h819 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h836 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h837 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h838 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B017.c350_pos (not_le.mp h748).le h747 (not_le.mp h819).le h838
      · -- right
        exact CKLaneC2R.Cells.S01.B017.c351_pos (not_le.mp h748).le h747 (not_le.mp h838).le h837
    · -- right
      by_cases h839 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B017.c354_pos (not_le.mp h748).le h747 (not_le.mp h837).le h839
      · -- right
        exact CKLaneC2R.Cells.S01.B017.c355_pos (not_le.mp h748).le h747 (not_le.mp h839).le h836
  · -- right
    by_cases h840 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h841 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B018.c366_pos (not_le.mp h748).le h747 (not_le.mp h836).le h841
      · -- right
        exact CKLaneC2R.Cells.S01.B018.c367_pos (not_le.mp h748).le h747 (not_le.mp h841).le h840
    · -- right
      by_cases h842 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B018.c370_pos (not_le.mp h748).le h747 (not_le.mp h840).le h842
      · -- right
        exact CKLaneC2R.Cells.S01.B018.c371_pos (not_le.mp h748).le h747 (not_le.mp h842).le h818

theorem strip1_s087 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) (h748 : ¬ (a ≤ ((41/160 : ℚ) : ℝ))) (h817 : z ≤ ((217/400 : ℚ) : ℝ)) (h818 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h843 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h844 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h845 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h846 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B020.c404_pos (not_le.mp h748).le h747 (not_le.mp h818).le h846
        · -- right
          exact CKLaneC2R.Cells.S01.B020.c405_pos (not_le.mp h748).le h747 (not_le.mp h846).le h845
      · -- right
        exact CKLaneC2R.Cells.S01.B000.c12_pos (not_le.mp h748).le h747 (not_le.mp h845).le h844
    · -- right
      by_cases h847 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B000.c14_pos (not_le.mp h748).le h747 (not_le.mp h844).le h847
      · -- right
        exact CKLaneC2R.Cells.S01.B000.c15_pos (not_le.mp h748).le h747 (not_le.mp h847).le h843
  · -- right
    by_cases h848 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h849 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B001.c25_pos (not_le.mp h748).le h747 (not_le.mp h843).le h849
      · -- right
        exact CKLaneC2R.Cells.S01.B001.c26_pos (not_le.mp h748).le h747 (not_le.mp h849).le h848
    · -- right
      by_cases h850 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B001.c29_pos (not_le.mp h748).le h747 (not_le.mp h848).le h850
      · -- right
        exact CKLaneC2R.Cells.S01.B001.c30_pos (not_le.mp h748).le h747 (not_le.mp h850).le h817

end CKLaneC2R.CompactCover


