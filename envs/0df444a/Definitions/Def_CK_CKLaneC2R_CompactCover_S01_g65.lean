-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g65
-- name    : CK_CKLaneC2R_CompactCover_S01_g65
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T01:38:48.648454+00:00
-- url     : https://prove2.me/theorems/55dc598d-f48c-4b39-971a-2c5e78db6ad8
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

theorem strip1_s092 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : ¬ (a ≤ ((21/80 : ℚ) : ℝ))) (h880 : a ≤ ((43/160 : ℚ) : ℝ)) (h881 : z ≤ ((217/400 : ℚ) : ℝ)) (h882 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h883 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h899 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h900 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h901 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B017.c356_pos (not_le.mp h747).le h880 (not_le.mp h883).le h901
      · -- right
        exact CKLaneC2R.Cells.S01.B017.c357_pos (not_le.mp h747).le h880 (not_le.mp h901).le h900
    · -- right
      by_cases h902 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B018.c360_pos (not_le.mp h747).le h880 (not_le.mp h900).le h902
      · -- right
        exact CKLaneC2R.Cells.S01.B018.c361_pos (not_le.mp h747).le h880 (not_le.mp h902).le h899
  · -- right
    by_cases h903 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h904 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B018.c372_pos (not_le.mp h747).le h880 (not_le.mp h899).le h904
      · -- right
        exact CKLaneC2R.Cells.S01.B018.c373_pos (not_le.mp h747).le h880 (not_le.mp h904).le h903
    · -- right
      by_cases h905 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B018.c376_pos (not_le.mp h747).le h880 (not_le.mp h903).le h905
      · -- right
        exact CKLaneC2R.Cells.S01.B018.c377_pos (not_le.mp h747).le h880 (not_le.mp h905).le h882

theorem strip1_s093 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : ¬ (a ≤ ((21/80 : ℚ) : ℝ))) (h880 : a ≤ ((43/160 : ℚ) : ℝ)) (h881 : z ≤ ((217/400 : ℚ) : ℝ)) (h882 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h906 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h907 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h908 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h909 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B020.c408_pos (not_le.mp h747).le h880 (not_le.mp h882).le h909
        · -- right
          exact CKLaneC2R.Cells.S01.B020.c409_pos (not_le.mp h747).le h880 (not_le.mp h909).le h908
      · -- right
        exact CKLaneC2R.Cells.S01.B000.c17_pos (not_le.mp h747).le h880 (not_le.mp h908).le h907
    · -- right
      by_cases h910 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B000.c19_pos (not_le.mp h747).le h880 (not_le.mp h907).le h910
      · -- right
        exact CKLaneC2R.Cells.S01.B001.c20_pos (not_le.mp h747).le h880 (not_le.mp h910).le h906
  · -- right
    by_cases h911 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h912 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B001.c31_pos (not_le.mp h747).le h880 (not_le.mp h906).le h912
      · -- right
        exact CKLaneC2R.Cells.S01.B001.c32_pos (not_le.mp h747).le h880 (not_le.mp h912).le h911
    · -- right
      by_cases h913 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B001.c35_pos (not_le.mp h747).le h880 (not_le.mp h911).le h913
      · -- right
        exact CKLaneC2R.Cells.S01.B001.c36_pos (not_le.mp h747).le h880 (not_le.mp h913).le h881

end CKLaneC2R.CompactCover


