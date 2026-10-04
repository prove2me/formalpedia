-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g57
-- name    : CK_CKLaneC2R_CompactCover_S01_g57
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T06:33:23.687509+00:00
-- url     : https://prove2.me/theorems/049d0525-06ba-49d8-b9bc-3bdd51444103
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B028

namespace CKLaneC2R.CompactCover

theorem strip1_s080 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) (h748 : a ≤ ((41/160 : ℚ) : ℝ)) (h749 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h787 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h788 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h789 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h790 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B004.c91_pos (not_le.mp h0).le h748 (not_le.mp h749).le h790
      · -- right
        exact CKLaneC2R.Cells.S01.B004.c92_pos (not_le.mp h0).le h748 (not_le.mp h790).le h789
    · -- right
      by_cases h791 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B004.c95_pos (not_le.mp h0).le h748 (not_le.mp h789).le h791
      · -- right
        exact CKLaneC2R.Cells.S01.B004.c96_pos (not_le.mp h0).le h748 (not_le.mp h791).le h788
  · -- right
    by_cases h792 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h793 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B006.c123_pos (not_le.mp h0).le h748 (not_le.mp h788).le h793
      · -- right
        exact CKLaneC2R.Cells.S01.B006.c124_pos (not_le.mp h0).le h748 (not_le.mp h793).le h792
    · -- right
      by_cases h794 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B006.c131_pos (not_le.mp h0).le h748 (not_le.mp h792).le h794
      · -- right
        exact CKLaneC2R.Cells.S01.B006.c133_pos (not_le.mp h0).le h748 (not_le.mp h794).le h787

theorem strip1_s081 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : a ≤ ((21/80 : ℚ) : ℝ)) (h748 : a ≤ ((41/160 : ℚ) : ℝ)) (h749 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h787 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h795 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h796 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h797 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B007.c156_pos (not_le.mp h0).le h748 (not_le.mp h787).le h797
    · -- right
      exact CKLaneC2R.Cells.S01.B007.c158_pos (not_le.mp h0).le h748 (not_le.mp h797).le h796
  · -- right
    by_cases h798 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h799 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B027.c558_pos (not_le.mp h0).le h748 (not_le.mp h796).le h799
      · -- right
        exact CKLaneC2R.Cells.S01.B027.c559_pos (not_le.mp h0).le h748 (not_le.mp h799).le h798
    · -- right
      by_cases h800 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B028.c562_pos (not_le.mp h0).le h748 (not_le.mp h798).le h800
      · -- right
        exact CKLaneC2R.Cells.S01.B028.c563_pos (not_le.mp h0).le h748 (not_le.mp h800).le h795

end CKLaneC2R.CompactCover


