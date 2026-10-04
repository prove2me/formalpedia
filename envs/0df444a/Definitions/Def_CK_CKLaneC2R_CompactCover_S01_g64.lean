-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g64
-- name    : CK_CKLaneC2R_CompactCover_S01_g64
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T01:35:00.445224+00:00
-- url     : https://prove2.me/theorems/ac4d7cdf-1852-4452-acbe-429455c3a644
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B053
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B039
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B016

namespace CKLaneC2R.CompactCover

theorem strip1_s091 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : ¬ (a ≤ ((21/80 : ℚ) : ℝ))) (h880 : a ≤ ((43/160 : ℚ) : ℝ)) (h881 : z ≤ ((217/400 : ℚ) : ℝ)) (h882 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h883 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h884 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h885 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h886 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h887 : a ≤ ((17/64 : ℚ) : ℝ)
        · -- left
          by_cases h888 : z ≤ ((11921/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B053.c1066_pos (not_le.mp h747).le h887 hz1 h888
          · -- right
            exact CKLaneC2R.Cells.S01.B053.c1068_pos (not_le.mp h747).le h887 (not_le.mp h888).le h886
        · -- right
          by_cases h889 : z ≤ ((11921/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B053.c1067_pos (not_le.mp h887).le h880 hz1 h889
          · -- right
            exact CKLaneC2R.Cells.S01.B053.c1069_pos (not_le.mp h887).le h880 (not_le.mp h889).le h886
      · -- right
        by_cases h890 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B039.c796_pos (not_le.mp h747).le h880 (not_le.mp h886).le h890
        · -- right
          exact CKLaneC2R.Cells.S01.B039.c797_pos (not_le.mp h747).le h880 (not_le.mp h890).le h885
    · -- right
      by_cases h891 : a ≤ ((17/64 : ℚ) : ℝ)
      · -- left
        by_cases h892 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B040.c800_pos (not_le.mp h747).le h891 (not_le.mp h885).le h892
        · -- right
          exact CKLaneC2R.Cells.S01.B040.c802_pos (not_le.mp h747).le h891 (not_le.mp h892).le h884
      · -- right
        by_cases h893 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B040.c801_pos (not_le.mp h891).le h880 (not_le.mp h885).le h893
        · -- right
          exact CKLaneC2R.Cells.S01.B040.c803_pos (not_le.mp h891).le h880 (not_le.mp h893).le h884
  · -- right
    by_cases h894 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h895 : a ≤ ((17/64 : ℚ) : ℝ)
      · -- left
        by_cases h896 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B040.c818_pos (not_le.mp h747).le h895 (not_le.mp h884).le h896
        · -- right
          exact CKLaneC2R.Cells.S01.B041.c820_pos (not_le.mp h747).le h895 (not_le.mp h896).le h894
      · -- right
        by_cases h897 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B040.c819_pos (not_le.mp h895).le h880 (not_le.mp h884).le h897
        · -- right
          exact CKLaneC2R.Cells.S01.B041.c821_pos (not_le.mp h895).le h880 (not_le.mp h897).le h894
    · -- right
      by_cases h898 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B016.c326_pos (not_le.mp h747).le h880 (not_le.mp h894).le h898
      · -- right
        exact CKLaneC2R.Cells.S01.B016.c327_pos (not_le.mp h747).le h880 (not_le.mp h898).le h883

end CKLaneC2R.CompactCover


