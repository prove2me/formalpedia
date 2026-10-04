-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g05
-- name    : CK_CKLaneC2R_CompactCover_S05_g05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T08:21:34.594022+00:00
-- url     : https://prove2.me/theorems/7ce4a7a7-c38d-47c9-b499-3783986ace32
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S05 (proof part of strip5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S05 (proof part of strip5).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B004

namespace CKLaneC2R.CompactCover

theorem strip5_s008 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((3699/4000 : ℚ) : ℝ))) (h69 : a ≤ ((7497/8000 : ℚ) : ℝ)) (h70 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h71 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h72 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h73 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h74 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B002.c52_pos (not_le.mp h1).le h69 hz1 h74
        · -- right
          exact CKLaneC2R.Cells.S05.B002.c53_pos (not_le.mp h1).le h69 (not_le.mp h74).le h73
      · -- right
        exact CKLaneC2R.Cells.S05.B000.c2_pos (not_le.mp h1).le h69 (not_le.mp h73).le h72
    · -- right
      by_cases h75 : z ≤ ((823/3200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B000.c8_pos (not_le.mp h1).le h69 (not_le.mp h72).le h75
      · -- right
        exact CKLaneC2R.Cells.S05.B000.c9_pos (not_le.mp h1).le h69 (not_le.mp h75).le h71
  · -- right
    by_cases h76 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h77 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B000.c16_pos (not_le.mp h1).le h69 (not_le.mp h71).le h77
      · -- right
        exact CKLaneC2R.Cells.S05.B000.c18_pos (not_le.mp h1).le h69 (not_le.mp h77).le h76
    · -- right
      by_cases h78 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B001.c24_pos (not_le.mp h1).le h69 (not_le.mp h76).le h78
      · -- right
        exact CKLaneC2R.Cells.S05.B001.c26_pos (not_le.mp h1).le h69 (not_le.mp h78).le h70

theorem strip5_s009 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((3699/4000 : ℚ) : ℝ))) (h69 : a ≤ ((7497/8000 : ℚ) : ℝ)) (h70 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h79 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h80 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h81 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B001.c38_pos (not_le.mp h1).le h69 (not_le.mp h70).le h81
    · -- right
      exact CKLaneC2R.Cells.S05.B002.c40_pos (not_le.mp h1).le h69 (not_le.mp h81).le h80
  · -- right
    by_cases h82 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B002.c44_pos (not_le.mp h1).le h69 (not_le.mp h80).le h82
    · -- right
      by_cases h83 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B004.c95_pos (not_le.mp h1).le h69 (not_le.mp h82).le h83
      · -- right
        exact CKLaneC2R.Cells.S05.B004.c96_pos (not_le.mp h1).le h69 (not_le.mp h83).le h79

end CKLaneC2R.CompactCover


